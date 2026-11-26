import CoreGeisha.Syntax

/-!
# Core Geisha: 40-Bit Exact Object Pointer Masks & Sticky-Mark Generational GC Soundness

Machine-checked formalization (zero `sorry`, zero external dependencies beyond
Lean 4 core) of Geisha's runtime memory manager and compiler GC layout emission:

1. **40-Bit Exact Header Pointer Masks & Compiler ADT Layout Soundness**
   (`src/codegen.gsa`: `accumPtrMaskType` / `accumPtrMaskFields`,
    `runtime/include/gsvalue.h`: `HEADER_HAS_MASK_BIT`, `HEADER_MASK_SHIFT = 24`):
   - Exact LP64 word-flattening (`flattenTyWords`, `flattenTyListWords`) for Core
     Geisha types (`Ty`), inline tuple flattening, and `≤ 40`-word bitmask synthesis
     (`computePtrMask`, `adtVariantPtrMask`) with conservative fallback (`none`)
     above 40 payload words.
   - Soundness and no-false-pointer precision (`computePtrMask_sound`,
     `adtVariantPtrMask_sound`, `checkProgramGcLayouts_sound`): every pointer word
     is covered by the mask (`ObjMaskSound`), while unboxed scalar words (including
     word `0` ADT variant tags) never set mask bits (`mask.testBit idx = false`).

2. **Sticky-Mark Generational GC State, Write Barrier & Invariant**
   (`runtime/runtime/gc_bitmap.c`: `mark_bits`, `HEADER_REMEMBERED_BIT`, `remset`,
    `gc_write_barrier`):
   - True semantic object-graph reachability (`Reachable`) independent of masks and
     generations.
   - Generational heap invariant (`GenHeapInv`) coupling pointer validity, exact mask
     soundness, deduplicated `remset` synchronization, and the Old-to-Young
     remembered-set invariant.

3. **Mutator Operations & Write-Barrier Necessity**
   - Lock-free nursery allocations (`gcAllocImmutable`, `gcAllocCell`) without write
     barriers preserve `GenHeapInv`.
   - Mutating stores with sticky write barrier (`gcWriteBarrierStore`) preserve
     `GenHeapInv`.
   - Concrete counterexample (`missing_write_barrier_unsound`): mutating an Old
     `Cell` to reference a Young object via `rawStoreNoBarrier` causes `minorGcCollect`
     to sweep a live `Reachable` object (**Use-After-Free**).

4. **Executable Sticky Minor GC & Full Major GC Soundness and Completeness**
   - `minorGcCollect` (scanning only Young roots, `remset` children, and newly marked
     Young objects, then promoting survivors via sticky `markBits`):
     `minorGc_sound`, `minorGc_preserves_inv`, and `minorGc_reachable_iff`.
   - `majorGcCollect` (full mark-sweep from roots across all generations):
     `majorGc_sound`, `majorGc_complete` (exact `↔` characterization with `Reachable`),
     `majorGc_preserves_inv`, and `majorGc_reachable_iff`.
-/

namespace CoreGeisha

/-! ## Part 1: Exact 40-Bit Word Pointer Masks & Compiler ADT Layout Soundness -/

/-- Heap object identifier (abstracting 8-byte-aligned payload addresses). -/
abbrev ObjId := Nat

/-- Maximum payload words representable in the inline 40-bit header pointer mask
    (`HEADER_MASK_SHIFT = 24` in `runtime/include/gsvalue.h`, bits `[24..63]`). -/
abbrev maxMaskWords : Nat := 40

/-- A 64-bit machine word inside a heap object payload: either raw unboxed scalar
    bits (`Int`, `Bool`, `Void`, ADT tag) or a nullable heap object pointer. -/
inductive Word where
  | scalar (bits : UInt64) : Word
  | ptr (target : Option ObjId) : Word
  deriving Repr, BEq, DecidableEq

/-- Runtime heap object with optional 40-bit exact pointer mask (`some mask` when
    `HEADER_HAS_MASK_BIT` is set for `≤ 40` payload words; `none` for conservative
    full-payload word scanning on `> 40` words) and mutability flag (`true` for
    `Cell` / `MutArray`, `false` for immutable ADTs, tuples, strings, closures). -/
structure HeapObj where
  hdrMask : Option Nat
  mutable : Bool
  words   : List Word
  deriving Repr, BEq, DecidableEq

/-- Whether payload word `idx` is scanned as a pointer candidate according to
    `hdrMask`: conservative fallback (`none`) scans all words; an exact mask
    (`some mask`) scans `idx < 40` iff bit `idx` of `mask` is `1`. -/
def maskCoversWord (hdrMask : Option Nat) (idx : Nat) : Bool :=
  match hdrMask with
  | none => true
  | some mask => decide (idx < maxMaskWords) && mask.testBit idx

/-- Exact pointer-mask soundness for a heap object:
    1. An inline mask `some m` is only attached to objects of `≤ 40` words;
    2. Every non-null pointer word at index `idx` is covered by `hdrMask`. -/
def ObjMaskSound (obj : HeapObj) : Prop :=
  (∀ (m : Nat), obj.hdrMask = some m → obj.words.length ≤ maxMaskWords) ∧
  ∀ (idx : Nat) (oid : ObjId), obj.words[idx]? = some (.ptr (some oid)) →
    maskCoversWord obj.hdrMask idx = true

/-! ### Compiler LP64 Type Flattening & 40-Bit Mask Synthesis (`src/codegen.gsa`) -/

mutual
/-- Flatten a monomorphic Core Geisha type into its LP64 word-level pointer flags
    (`true` = GC-traced boxed heap pointer, `false` = unboxed scalar word).
    Tuples are flattened inline; scalars (`void`, `int`, `bool`) are unboxed;
    strings, closures, ADTs, `Cell`, and concurrency handles are boxed pointers. -/
def flattenTyWords : Ty → List Bool
  | .void => [false]
  | .int => [false]
  | .bool => [false]
  | .tuple ts => flattenTyListWords ts
  | .str => [true]
  | .fn _ _ _ => [true]
  | .adt _ => [true]
  | .cell _ => [true]
  | .task _ => [true]
  | .mvar _ => [true]
  | .chan _ => [true]
  | .actor _ => [true]

/-- Flatten a list of field types into their LP64 word-level pointer flags. -/
def flattenTyListWords : List Ty → List Bool
  | [] => []
  | t :: ts => flattenTyWords t ++ flattenTyListWords ts
end

/-- Accumulate pointer bit positions starting at word offset `startWord`. -/
def buildPtrMaskAux (startWord : Nat) : List Bool → Nat
  | [] => 0
  | b :: bs =>
    let rest := buildPtrMaskAux (startWord + 1) bs
    if b then (1 <<< startWord) ||| rest else rest

/-- Synthesize an exact 40-bit header pointer mask starting at `startWord`
    (mirroring `accumPtrMaskFields` in `src/codegen.gsa`), falling back to `none`
    (conservative scan) when total words exceed `maxMaskWords = 40`. -/
def computePtrMask (startWord : Nat) (isPtrWords : List Bool) : Option Nat :=
  if startWord + isPtrWords.length > maxMaskWords then
    none
  else
    some (buildPtrMaskAux startWord isPtrWords)

/-- Synthesize the header pointer mask for a heap-allocated ADT constructor cell:
    word `0` stores the integer constructor tag (`v.tag`), and payload fields start
    at word `1`. -/
def adtVariantPtrMask (v : VariantDef) : Option Nat :=
  computePtrMask 1 (flattenTyListWords v.fields)

/-- Agreement between a runtime `Word` and a static pointer-vs-scalar layout flag. -/
def WordMatchesFlag : Word → Bool → Prop
  | .scalar _, false => True
  | .ptr _, true => True
  | _, _ => False

/-- Pointwise agreement between a payload word list and a flattened layout list. -/
inductive WordsMatchLayout : List Word → List Bool → Prop where
  | nil : WordsMatchLayout [] []
  | cons {w : Word} {b : Bool} {ws : List Word} {bs : List Bool} :
      WordMatchesFlag w b →
      WordsMatchLayout ws bs →
      WordsMatchLayout (w :: ws) (b :: bs)

/-! ### Bit-Level Algebra & Layout Soundness Proofs -/

private theorem testBit_one_shiftLeft_eq (k idx : Nat) :
    (1 <<< k).testBit idx = decide (k = idx) := by
  rw [Nat.shiftLeft_eq, Nat.one_mul]
  exact Nat.testBit_two_pow

/-- Exact closed-form characterization of every bit produced by `buildPtrMaskAux`. -/
theorem testBit_buildPtrMaskAux (startWord : Nat) (bs : List Bool) (idx : Nat) :
    (buildPtrMaskAux startWord bs).testBit idx =
      if idx < startWord then false else (bs[idx - startWord]?).getD false := by
  induction bs generalizing startWord with
  | nil =>
    simp [buildPtrMaskAux]
  | cons b bs ih =>
    simp only [buildPtrMaskAux]
    by_cases hlt : idx < startWord
    · have hlt1 : idx < startWord + 1 := by omega
      have hne : startWord ≠ idx := by omega
      cases b
      · simp only [Bool.false_eq_true, ↓reduceIte, ih (startWord + 1), hlt, hlt1]
      · simp only [↓reduceIte, Nat.testBit_or, testBit_one_shiftLeft_eq,
          ih (startWord + 1), hlt, hlt1, hne, decide_false, Bool.or_self]
    · by_cases heq : idx = startWord
      · subst heq
        have hlt1 : idx < idx + 1 := by omega
        cases b
        · simp only [Bool.false_eq_true, ↓reduceIte, ih (idx + 1), hlt1, hlt,
            Nat.sub_self, List.getElem?_cons_zero, Option.getD_some]
        · simp only [↓reduceIte, Nat.testBit_or, testBit_one_shiftLeft_eq,
            ih (idx + 1), hlt1, hlt, decide_true, Bool.true_or,
            Nat.sub_self, List.getElem?_cons_zero, Option.getD_some]
      · have hnl1 : ¬ (idx < startWord + 1) := by omega
        have hne : startWord ≠ idx := by omega
        have hsub : idx - startWord = (idx - (startWord + 1)) + 1 := by omega
        cases b
        · simp only [Bool.false_eq_true, ↓reduceIte, ih (startWord + 1),
            hlt, hnl1, hsub, List.getElem?_cons_succ]
        · simp only [↓reduceIte, Nat.testBit_or, testBit_one_shiftLeft_eq,
            ih (startWord + 1), hlt, hnl1, hne, decide_false, Bool.false_or,
            hsub, List.getElem?_cons_succ]

theorem buildPtrMaskAux_lt_two_pow (startWord : Nat) (bs : List Bool) :
    buildPtrMaskAux startWord bs < 2 ^ (startWord + bs.length) := by
  induction bs generalizing startWord with
  | nil =>
    simp only [buildPtrMaskAux, List.length_nil, Nat.add_zero]
    exact Nat.two_pow_pos startWord
  | cons b bs ih =>
    simp only [buildPtrMaskAux, List.length_cons]
    have hExp : startWord + 1 + bs.length = startWord + (bs.length + 1) := by omega
    have hRest : buildPtrMaskAux (startWord + 1) bs < 2 ^ (startWord + (bs.length + 1)) :=
      hExp ▸ ih (startWord + 1)
    cases b with
    | false => exact hRest
    | true =>
      simp only [↓reduceIte]
      apply Nat.or_lt_two_pow
      · rw [Nat.shiftLeft_eq, Nat.one_mul]
        exact Nat.pow_lt_pow_right (by omega) (by omega)
      · exact hRest

theorem computePtrMask_lt_two_pow_40 {startWord : Nat} {isPtrWords : List Bool} {m : Nat}
    (h : computePtrMask startWord isPtrWords = some m) :
    m < 2 ^ maxMaskWords := by
  unfold computePtrMask at h
  by_cases hgt : startWord + isPtrWords.length > maxMaskWords
  · simp [hgt] at h
  · simp only [hgt, ↓reduceIte, Option.some.injEq] at h
    subst h
    have h1 := buildPtrMaskAux_lt_two_pow startWord isPtrWords
    have h2 : 2 ^ (startWord + isPtrWords.length) ≤ 2 ^ maxMaskWords :=
      Nat.pow_le_pow_right (by omega) (by omega)
    exact Nat.lt_of_lt_of_le h1 h2

theorem WordsMatchLayout.length_eq {ws : List Word} {bs : List Bool}
    (h : WordsMatchLayout ws bs) : ws.length = bs.length := by
  induction h with
  | nil => rfl
  | cons _ _ ih => simp [ih]

theorem WordsMatchLayout.getElem?_some {ws : List Word} {bs : List Bool}
    (h : WordsMatchLayout ws bs) {i : Nat} {w : Word}
    (hw : ws[i]? = some w) :
    ∃ b, bs[i]? = some b ∧ WordMatchesFlag w b := by
  induction h generalizing i with
  | nil => simp at hw
  | cons hwf hrest ih =>
    cases i with
    | zero =>
      simp only [List.getElem?_cons_zero, Option.some.injEq] at hw
      subst hw
      exact ⟨_, rfl, hwf⟩
    | succ j =>
      simp only [List.getElem?_cons_succ] at hw
      exact ih hw

/-- **Compiler Pointer-Mask Soundness & Scalar Precision (`computePtrMask_sound`)**:
    For an object with `prefixScalars.length` leading scalar header/tag words followed
    by `payload` matching `isPtrWords`:
    1. `ObjMaskSound` holds (every pointer word is scanned, and exact masks only
       occur for `≤ 40` total words);
    2. When `computePtrMask` returns `some m`, NO scalar word (neither in the scalar
       prefix nor in scalar payload slots) ever sets its mask bit (`m.testBit idx = false`). -/
theorem computePtrMask_sound (prefixScalars : List UInt64) (payload : List Word)
    (isPtrWords : List Bool) (hLayout : WordsMatchLayout payload isPtrWords) :
    let hdrMask := computePtrMask prefixScalars.length isPtrWords
    let obj : HeapObj := {
      hdrMask := hdrMask
      mutable := false
      words   := prefixScalars.map Word.scalar ++ payload
    }
    ObjMaskSound obj ∧
    (∀ (m idx : Nat) (bits : UInt64),
      hdrMask = some m →
      obj.words[idx]? = some (.scalar bits) →
      m.testBit idx = false) := by
  have hLenEq : payload.length = isPtrWords.length := hLayout.length_eq
  dsimp only
  refine ⟨⟨?_, ?_⟩, ?_⟩
  · intro m hm
    unfold computePtrMask at hm
    by_cases hgt : prefixScalars.length + isPtrWords.length > maxMaskWords
    · simp [hgt] at hm
    · simp only [List.length_append, List.length_map, hLenEq]
      omega
  · intro idx oid hGet
    simp only [List.getElem?_append, List.length_map] at hGet
    split at hGet
    · rename_i hlt
      rw [List.getElem?_map, List.getElem?_eq_getElem hlt] at hGet
      cases hGet
    · rename_i hge
      rcases hLayout.getElem?_some hGet with ⟨b, hb, hwf⟩
      cases b with
      | false => simp [WordMatchesFlag] at hwf
      | true =>
        have hiLt : idx - prefixScalars.length < isPtrWords.length := by
          cases Nat.lt_or_ge (idx - prefixScalars.length) isPtrWords.length with
          | inl h => exact h
          | inr h => rw [List.getElem?_eq_none h] at hb; cases hb
        unfold computePtrMask
        by_cases hgt : prefixScalars.length + isPtrWords.length > maxMaskWords
        · simp [hgt, maskCoversWord]
        · have hIdxLt : idx < maxMaskWords := by omega
          simp [hgt, maskCoversWord, hIdxLt, testBit_buildPtrMaskAux, hge, hb]
  · intro m idx bits hm hScalar
    unfold computePtrMask at hm
    by_cases hgt : prefixScalars.length + isPtrWords.length > maxMaskWords
    · simp [hgt] at hm
    · simp only [hgt, ↓reduceIte, Option.some.injEq] at hm
      subst hm
      rw [testBit_buildPtrMaskAux]
      simp only [List.getElem?_append, List.length_map] at hScalar
      split at hScalar
      · rename_i hlt
        simp [hlt]
      · rename_i hge
        rcases hLayout.getElem?_some hScalar with ⟨b, hb, hwf⟩
        cases b with
        | false => simp [hge, hb]
        | true => simp [WordMatchesFlag] at hwf

/-- **ADT Variant Pointer-Mask Soundness (`adtVariantPtrMask_sound`)**:
    Every ADT constructor object `{ hdrMask := adtVariantPtrMask v, mutable := false,
    words := .scalar tagBits :: words }` whose payload matches `flattenTyListWords v.fields`:
    1. Satisfies `ObjMaskSound`;
    2. Never marks word `0` (the constructor tag) when `adtVariantPtrMask v = some m`;
    3. Never marks any unboxed scalar word (`Int`, `Bool`, `Void`, or scalar tuple field)
       as a candidate GC pointer when `adtVariantPtrMask v = some m`. -/
theorem adtVariantPtrMask_sound (v : VariantDef) (tagBits : UInt64) (words : List Word)
    (hLayout : WordsMatchLayout words (flattenTyListWords v.fields)) :
    let obj : HeapObj := {
      hdrMask := adtVariantPtrMask v
      mutable := false
      words   := .scalar tagBits :: words
    }
    ObjMaskSound obj ∧
    (∀ (m : Nat), adtVariantPtrMask v = some m → m.testBit 0 = false) ∧
    (∀ (m idx : Nat) (bits : UInt64),
      adtVariantPtrMask v = some m →
      obj.words[idx]? = some (.scalar bits) →
      m.testBit idx = false) := by
  have hBase := computePtrMask_sound [tagBits] words (flattenTyListWords v.fields) hLayout
  simp only [List.length_singleton, List.map_cons, List.map_nil, List.singleton_append] at hBase
  rcases hBase with ⟨hSound, hNoFalsePtr⟩
  exact ⟨hSound, fun m hm => hNoFalsePtr m 0 tagBits hm rfl, hNoFalsePtr⟩

/-- Executable per-variant GC mask layout validator. -/
def checkVariantGcLayout (v : VariantDef) : Bool :=
  let flags := flattenTyListWords v.fields
  match adtVariantPtrMask v with
  | none => decide (1 + flags.length > maxMaskWords)
  | some m =>
    decide (1 + flags.length ≤ maxMaskWords) &&
    !m.testBit 0 &&
    (List.range flags.length).all fun i =>
      m.testBit (1 + i) == (flags[i]?).getD false

/-- Executable whole-program ADT GC pointer-mask layout validator. -/
def checkProgramGcLayouts (adts : List AdtDef) : Bool :=
  adts.all fun adt => adt.variants.all checkVariantGcLayout

theorem checkVariantGcLayout_true (v : VariantDef) :
    checkVariantGcLayout v = true := by
  unfold checkVariantGcLayout adtVariantPtrMask computePtrMask
  dsimp only
  by_cases hgt : 1 + (flattenTyListWords v.fields).length > maxMaskWords
  · simp [hgt]
  · have hle' : 1 + (flattenTyListWords v.fields).length ≤ maxMaskWords := by omega
    simp only [hgt, ↓reduceIte, hle', decide_true, Bool.true_and, Bool.and_eq_true,
      Bool.not_eq_true', List.all_eq_true, List.mem_range, beq_iff_eq]
    refine ⟨?_, ?_⟩
    · rw [testBit_buildPtrMaskAux]
      simp
    · intro i _
      rw [testBit_buildPtrMaskAux]
      have hnl : ¬ (1 + i < 1) := by omega
      have hsub : 1 + i - 1 = i := by omega
      simp [hnl, hsub]

/-- Every monomorphic Core Geisha ADT table passes `checkProgramGcLayouts`. -/
theorem checkProgramGcLayouts_complete (adts : List AdtDef) :
    checkProgramGcLayouts adts = true := by
  unfold checkProgramGcLayouts
  rw [List.all_eq_true]
  intro adt _
  rw [List.all_eq_true]
  intro v _
  exact checkVariantGcLayout_true v

/-- **Whole-Program GC Layout Checker Soundness (`checkProgramGcLayouts_sound`)**:
    Whenever `checkProgramGcLayouts adts = true`, every variant `v` of every `adt ∈ adts`
    produces exact, `ObjMaskSound`, false-pointer-free heap objects. -/
theorem checkProgramGcLayouts_sound {adts : List AdtDef}
    (_hCheck : checkProgramGcLayouts adts = true)
    {adt : AdtDef} (_hAdt : adt ∈ adts)
    {v : VariantDef} (_hVar : v ∈ adt.variants)
    (tagBits : UInt64) (words : List Word)
    (hLayout : WordsMatchLayout words (flattenTyListWords v.fields)) :
    let obj : HeapObj := {
      hdrMask := adtVariantPtrMask v
      mutable := false
      words   := .scalar tagBits :: words
    }
    ObjMaskSound obj ∧
    (∀ (m idx : Nat) (bits : UInt64),
      adtVariantPtrMask v = some m →
      obj.words[idx]? = some (.scalar bits) →
      m.testBit idx = false) := by
  rcases adtVariantPtrMask_sound v tagBits words hLayout with ⟨hSound, _, hScalar⟩
  exact ⟨hSound, hScalar⟩

/-! ## Part 2: Sticky-Mark Generational GC State, Reachability & Invariant -/

/-- Abstract generational GC state modeling `runtime/runtime/gc_bitmap.c`:
    - `heap`: slot-indexed table of live/allocated (`some obj`) or swept (`none`) slots;
    - `markBits`: sticky mark bitmap (`true` = Old generation, `false` = Young nursery);
    - `rememberedBit`: per-object `HEADER_REMEMBERED_BIT` deduplication flag;
    - `remset`: remembered set of Old containers mutated since the previous collection. -/
structure GcState where
  heap          : List (Option HeapObj)
  markBits      : List Bool
  rememberedBit : List Bool
  remset        : List ObjId
  deriving Repr, BEq, DecidableEq

/-- Initial empty GC heap state. -/
def emptyGcState : GcState :=
  { heap := [], markBits := [], rememberedBit := [], remset := [] }

/-- True semantic object-graph reachability from `roots` over `heap`.
    Crucially, `Reachable` inspects ALL `.ptr (some v) ∈ objU.words` without
    consulting `hdrMask`, `markBits`, or `remset`, serving as the ground-truth
    liveness oracle against which both exact pointer masks and sticky generational
    collection are verified. -/
inductive Reachable (heap : List (Option HeapObj)) (roots : List ObjId) : ObjId → Prop where
  | root {r : ObjId} {obj : HeapObj} :
      r ∈ roots →
      heap[r]? = some (some obj) →
      Reachable heap roots r
  | step {u v : ObjId} {objU objV : HeapObj} :
      Reachable heap roots u →
      heap[u]? = some (some objU) →
      Word.ptr (some v) ∈ objU.words →
      heap[v]? = some (some objV) →
      Reachable heap roots v

theorem Reachable.allocated {heap : List (Option HeapObj)} {roots : List ObjId} {oid : ObjId}
    (h : Reachable heap roots oid) :
    ∃ obj, heap[oid]? = some (some obj) := by
  cases h with
  | root _ hObj => exact ⟨_, hObj⟩
  | step _ _ _ hObjV => exact ⟨_, hObjV⟩

/-- **Sticky-Mark Generational Heap Invariant (`GenHeapInv`)**:
    1. Bitmap arrays `markBits` and `rememberedBit` match `heap.length`;
    2. Closed heap pointers (`validPtrs`): live objects never point to swept/OOB slots;
    3. Exact mask soundness (`maskSound`): every live object satisfies `ObjMaskSound`;
    4. Deduplicated valid `remset` (`remsetSync`, `remsetValid`, `remsetNodup`);
    5. **Old-to-Young Remembered-Set Invariant (`oldToYoung`)**: every Old object
       (`markBits[u] = true`) holding a pointer to a Young object (`markBits[v] = false`)
       is recorded in `remset`. -/
structure GenHeapInv (s : GcState) : Prop where
  markLen     : s.markBits.length = s.heap.length
  remBitLen   : s.rememberedBit.length = s.heap.length
  validPtrs   : ∀ (u : ObjId) (objU : HeapObj) (v : ObjId),
    s.heap[u]? = some (some objU) →
    Word.ptr (some v) ∈ objU.words →
    ∃ objV, s.heap[v]? = some (some objV)
  maskSound   : ∀ (u : ObjId) (objU : HeapObj),
    s.heap[u]? = some (some objU) →
    ObjMaskSound objU
  remsetSync  : ∀ (u : ObjId), u ∈ s.remset ↔ s.rememberedBit[u]? = some true
  remsetValid : ∀ (u : ObjId), u ∈ s.remset → ∃ objU, s.heap[u]? = some (some objU)
  remsetNodup : s.remset.Nodup
  oldToYoung  : ∀ (u : ObjId) (objU : HeapObj) (v : ObjId),
    s.heap[u]? = some (some objU) →
    s.markBits[u]? = some true →
    Word.ptr (some v) ∈ objU.words →
    s.markBits[v]? = some false →
    u ∈ s.remset

theorem emptyGcState_inv : GenHeapInv emptyGcState :=
  { markLen     := rfl
    remBitLen   := rfl
    validPtrs   := fun _ _ _ h => by simp [emptyGcState] at h
    maskSound   := fun _ _ h => by simp [emptyGcState] at h
    remsetSync  := fun _ => by simp [emptyGcState]
    remsetValid := fun _ h => by simp [emptyGcState] at h
    remsetNodup := List.Pairwise.nil
    oldToYoung  := fun _ _ _ h => by simp [emptyGcState] at h }

private theorem lt_len_of_getElem?_some {α : Type} {xs : List α} {i : Nat} {x : α}
    (h : xs[i]? = some x) : i < xs.length := by
  cases Nat.lt_or_ge i xs.length with
  | inl hlt => exact hlt
  | inr hge =>
    rw [List.getElem?_eq_none hge] at h
    cases h

/-! ## Part 3: Mutator Allocations, Sticky Write Barrier & Counterexample -/

/-- Lock-free Young-generation allocation of an immutable object (`mutable = false`),
    e.g., ADT value, tuple, closure, or string. Emits NO write barrier. -/
def gcAllocImmutable (s : GcState) (hdrMask : Option Nat) (words : List Word) :
    GcState × ObjId :=
  let oid := s.heap.length
  let obj : HeapObj := { hdrMask := hdrMask, mutable := false, words := words }
  let s' : GcState :=
    { heap          := s.heap ++ [some obj]
      markBits      := s.markBits ++ [false]
      rememberedBit := s.rememberedBit ++ [false]
      remset        := s.remset }
  (s', oid)

/-- Exact 1-word header mask for a mutable `Cell` (`some 1` if holding a pointer,
    `some 0` if holding an unboxed scalar). -/
def cellHdrMask (w : Word) : Option Nat :=
  match w with
  | .scalar _ => some 0
  | .ptr _    => some 1

/-- Lock-free Young-generation allocation of a 1-word mutable `Cell` (`cellNew`).
    Emits NO write barrier at allocation time because the new `Cell` itself resides
    in the Young nursery (`markBit = false`). -/
def gcAllocCell (s : GcState) (initWord : Word) : GcState × ObjId :=
  let oid := s.heap.length
  let obj : HeapObj := { hdrMask := cellHdrMask initWord, mutable := true, words := [initWord] }
  let s' : GcState :=
    { heap          := s.heap ++ [some obj]
      markBits      := s.markBits ++ [false]
      rememberedBit := s.rememberedBit ++ [false]
      remset        := s.remset }
  (s', oid)

/-- Shared preservation lemma for fresh Young-generation (`markBit = false`) object
    allocation without a write barrier. -/
private theorem gcAllocYoungObj_preserves_inv (s : GcState) (obj : HeapObj)
    (hInv : GenHeapInv s)
    (hMask : ObjMaskSound obj)
    (hPtrs : ∀ (v : ObjId), Word.ptr (some v) ∈ obj.words → ∃ objV, s.heap[v]? = some (some objV)) :
    GenHeapInv
      { heap          := s.heap ++ [some obj]
        markBits      := s.markBits ++ [false]
        rememberedBit := s.rememberedBit ++ [false]
        remset        := s.remset } := by
  refine
    { markLen     := by simp [hInv.markLen]
      remBitLen   := by simp [hInv.remBitLen]
      validPtrs   := ?_
      maskSound   := ?_
      remsetSync  := ?_
      remsetValid := ?_
      remsetNodup := hInv.remsetNodup
      oldToYoung  := ?_ }
  · intro u objU v hu hvMem
    simp only [List.getElem?_append] at hu
    split at hu
    · rcases hInv.validPtrs u objU v hu hvMem with ⟨objV, hv⟩
      have hvLt : v < s.heap.length := lt_len_of_getElem?_some hv
      exact ⟨objV, by rw [List.getElem?_append_left hvLt]; exact hv⟩
    · have huEq : u - s.heap.length = 0 := by
        cases hsub : u - s.heap.length with
        | zero => rfl
        | succ k => simp [hsub] at hu
      rw [huEq] at hu
      simp only [List.getElem?_cons_zero, Option.some.injEq] at hu
      subst hu
      rcases hPtrs v hvMem with ⟨objV, hv⟩
      have hvLt : v < s.heap.length := lt_len_of_getElem?_some hv
      exact ⟨objV, by rw [List.getElem?_append_left hvLt]; exact hv⟩
  · intro u objU hu
    simp only [List.getElem?_append] at hu
    split at hu
    · exact hInv.maskSound u objU hu
    · have huEq : u - s.heap.length = 0 := by
        cases hsub : u - s.heap.length with
        | zero => rfl
        | succ k => simp [hsub] at hu
      rw [huEq] at hu
      simp only [List.getElem?_cons_zero, Option.some.injEq] at hu
      subst hu
      exact hMask
  · intro u
    constructor
    · intro hMem
      have hRem := (hInv.remsetSync u).mp hMem
      have huLt : u < s.rememberedBit.length := lt_len_of_getElem?_some hRem
      dsimp only
      rw [List.getElem?_append_left huLt]
      exact hRem
    · intro hRem'
      simp only [List.getElem?_append] at hRem'
      split at hRem'
      · exact (hInv.remsetSync u).mpr hRem'
      · cases hsub : u - s.rememberedBit.length <;> simp [hsub] at hRem'
  · intro u hMem
    rcases hInv.remsetValid u hMem with ⟨objU, hu⟩
    have huLt : u < s.heap.length := lt_len_of_getElem?_some hu
    exact ⟨objU, by dsimp only; rw [List.getElem?_append_left huLt]; exact hu⟩
  · intro u objU v hu hOld hvMem hYoung
    simp only [List.getElem?_append, hInv.markLen] at hOld
    have huLt : u < s.heap.length := by
      split at hOld
      · assumption
      · cases hsub : u - s.heap.length <;> simp [hsub] at hOld
    simp only [List.getElem?_append, huLt, ↓reduceIte] at hu
    have hOldOrig : s.markBits[u]? = some true := by
      simpa [List.getElem?_append, hInv.markLen, huLt] using hOld
    rcases hInv.validPtrs u objU v hu hvMem with ⟨_, hvOrig⟩
    have hvLt : v < s.heap.length := lt_len_of_getElem?_some hvOrig
    have hYoungOrig : s.markBits[v]? = some false := by
      simpa [List.getElem?_append, hInv.markLen, hvLt] using hYoung
    exact hInv.oldToYoung u objU v hu hOldOrig hvMem hYoungOrig

/-- **Immutable Allocation Preserves `GenHeapInv` (`gcAllocImmutable_preserves_inv`)**:
    Allocating a Young immutable object with valid target pointers and a sound mask
    preserves `GenHeapInv` with zero write-barrier overhead. -/
theorem gcAllocImmutable_preserves_inv (s : GcState) (hdrMask : Option Nat) (words : List Word)
    (hInv : GenHeapInv s)
    (hMask : ObjMaskSound { hdrMask := hdrMask, mutable := false, words := words })
    (hPtrs : ∀ (v : ObjId), Word.ptr (some v) ∈ words → ∃ objV, s.heap[v]? = some (some objV)) :
    GenHeapInv (gcAllocImmutable s hdrMask words).1 :=
  gcAllocYoungObj_preserves_inv s _ hInv hMask hPtrs

/-- **Mutable Cell Allocation Preserves `GenHeapInv` (`gcAllocCell_preserves_inv`)**:
    Allocating a Young 1-word mutable `Cell` preserves `GenHeapInv` with zero
    write-barrier overhead. -/
theorem gcAllocCell_preserves_inv (s : GcState) (initWord : Word)
    (hInv : GenHeapInv s)
    (hPtr : ∀ (v : ObjId), initWord = .ptr (some v) → ∃ objV, s.heap[v]? = some (some objV)) :
    GenHeapInv (gcAllocCell s initWord).1 := by
  unfold gcAllocCell
  apply gcAllocYoungObj_preserves_inv s _ hInv
  · refine ⟨fun _ _ => by show 1 ≤ 40; omega, ?_⟩
    intro idx oid hGet
    cases idx with
    | zero =>
      simp only [List.getElem?_cons_zero, Option.some.injEq] at hGet
      subst hGet
      simp [cellHdrMask, maskCoversWord]
    | succ k => simp at hGet
  · intro v hvMem
    simp only [List.mem_singleton] at hvMem
    exact hPtr v hvMem.symm

/-- Sticky generational write barrier (`gc_write_barrier` in `gc_bitmap.c`):
    if mutated container `u` is in the Old generation (`markBits[u] = true`) and not
    yet remembered (`rememberedBit[u] = false`), sets `HEADER_REMEMBERED_BIT` and
    pushes `u` onto `remset`. -/
def gcWriteBarrier (s : GcState) (u : ObjId) : GcState :=
  if s.markBits[u]? == some true && s.rememberedBit[u]? == some false then
    { s with
      rememberedBit := s.rememberedBit.set u true
      remset        := u :: s.remset }
  else
    s

/-- Mutating word store with sticky generational write barrier
    (`cellSet` / `arraySet` + `gc_write_barrier(u)` in `gc_bitmap.c`). -/
def gcWriteBarrierStore (s : GcState) (u : ObjId) (idx : Nat) (newWord : Word) : GcState :=
  match s.heap[u]? with
  | some (some objU) =>
    if objU.mutable && idx < objU.words.length then
      let objU' : HeapObj := { objU with words := objU.words.set idx newWord }
      gcWriteBarrier { s with heap := s.heap.set u (some objU') } u
    else
      s
  | _ => s

/-- Raw mutating word store OMITTING the generational write barrier (used below in
    `missing_write_barrier_unsound` to prove necessity of `gc_write_barrier`). -/
def rawStoreNoBarrier (s : GcState) (u : ObjId) (idx : Nat) (newWord : Word) : GcState :=
  match s.heap[u]? with
  | some (some objU) =>
    if objU.mutable && idx < objU.words.length then
      let objU' : HeapObj := { objU with words := objU.words.set idx newWord }
      { s with heap := s.heap.set u (some objU') }
    else
      s
  | _ => s

private theorem mem_set_or_mem {α : Type} {xs : List α} {idx : Nat} {x y : α}
    (h : y ∈ xs.set idx x) : y = x ∨ y ∈ xs := by
  induction xs generalizing idx with
  | nil => simp at h
  | cons a as ih =>
    cases idx with
    | zero =>
      simp only [List.set_cons_zero, List.mem_cons] at h
      rcases h with rfl | hMem
      · exact Or.inl rfl
      · exact Or.inr (List.mem_cons_of_mem a hMem)
    | succ k =>
      simp only [List.set_cons_succ, List.mem_cons] at h
      rcases h with rfl | hMem
      · exact Or.inr (List.mem_cons_self ..)
      · rcases ih hMem with rfl | hMem'
        · exact Or.inl rfl
        · exact Or.inr (List.mem_cons_of_mem a hMem')

/-- **Write-Barrier Store Preserves `GenHeapInv` (`gcWriteBarrierStore_preserves_inv`)**:
    Mutating slot `idx` of mutable container `u` with `gcWriteBarrierStore` preserves
    all clauses of `GenHeapInv`, including deduplicated `remset` and `oldToYoung`. -/
theorem gcWriteBarrierStore_preserves_inv (s : GcState) (u : ObjId) (idx : Nat) (newWord : Word)
    (hInv : GenHeapInv s)
    (hValidTarget : ∀ (v : ObjId), newWord = .ptr (some v) → ∃ objV, s.heap[v]? = some (some objV))
    (hMaskIdx : ∀ (objU : HeapObj) (v : ObjId),
      s.heap[u]? = some (some objU) →
      newWord = .ptr (some v) →
      maskCoversWord objU.hdrMask idx = true) :
    GenHeapInv (gcWriteBarrierStore s u idx newWord) := by
  unfold gcWriteBarrierStore
  cases hu : s.heap[u]? with
  | none => exact hInv
  | some optObj =>
    cases optObj with
    | none => exact hInv
    | some objU =>
      dsimp only
      by_cases hMutIdx : (objU.mutable && decide (idx < objU.words.length)) = true
      · simp only [hMutIdx, ↓reduceIte]
        have huLtHeap : u < s.heap.length := lt_len_of_getElem?_some hu
        have huLtRem : u < s.rememberedBit.length := hInv.remBitLen ▸ huLtHeap
        let objU' : HeapObj := { objU with words := objU.words.set idx newWord }
        have hAllocIff : ∀ (w : ObjId),
            (∃ objW, (s.heap.set u (some objU'))[w]? = some (some objW)) ↔
            (∃ objW, s.heap[w]? = some (some objW)) := by
          intro w
          by_cases hwu : w = u
          · subst hwu
            simp [List.getElem?_set_self huLtHeap, hu]
          · simp [List.getElem?_set_ne (Ne.symm hwu)]
        have hObjU'Mask : ObjMaskSound objU' := by
          rcases hInv.maskSound u objU hu with ⟨hLen40, hCover⟩
          refine ⟨?_, ?_⟩
          · intro m hm
            simpa [objU', List.length_set] using hLen40 m hm
          · intro i oid hGet
            by_cases hi : i = idx
            · subst hi
              have hIdxLt : i < objU.words.length := by
                simp only [Bool.and_eq_true, decide_eq_true_eq] at hMutIdx
                exact hMutIdx.2
              have hEqWord : newWord = .ptr (some oid) := by
                simpa [objU', List.getElem?_set_self hIdxLt] using hGet
              exact hMaskIdx objU oid hu hEqWord
            · simp only [objU', List.getElem?_set_ne (Ne.symm hi)] at hGet
              exact hCover i oid hGet
        have hValidPtrs' : ∀ (w : ObjId) (objW : HeapObj) (v : ObjId),
            (s.heap.set u (some objU'))[w]? = some (some objW) →
            Word.ptr (some v) ∈ objW.words →
            ∃ objV, (s.heap.set u (some objU'))[v]? = some (some objV) := by
          intro w objW v hw hvMem
          rw [hAllocIff v]
          by_cases hwu : w = u
          · subst hwu
            simp only [List.getElem?_set_self huLtHeap, Option.some.injEq] at hw
            subst hw
            rcases mem_set_or_mem hvMem with hEq | hOldMem
            · exact hValidTarget v hEq.symm
            · exact hInv.validPtrs w objU v hu hOldMem
          · simp only [List.getElem?_set_ne (Ne.symm hwu)] at hw
            exact hInv.validPtrs w objW v hw hvMem
        have hMaskSound' : ∀ (w : ObjId) (objW : HeapObj),
            (s.heap.set u (some objU'))[w]? = some (some objW) →
            ObjMaskSound objW := by
          intro w objW hw
          by_cases hwu : w = u
          · subst hwu
            simp only [List.getElem?_set_self huLtHeap, Option.some.injEq] at hw
            subst hw
            exact hObjU'Mask
          · simp only [List.getElem?_set_ne (Ne.symm hwu)] at hw
            exact hInv.maskSound w objW hw
        unfold gcWriteBarrier
        dsimp only
        by_cases hCond : (s.markBits[u]? == some true && s.rememberedBit[u]? == some false) = true
        · simp only [hCond, ↓reduceIte]
          simp only [Bool.and_eq_true, beq_iff_eq] at hCond
          rcases hCond with ⟨_, hRemFalse⟩
          have huNotInRem : u ∉ s.remset := by
            intro hIn
            have hTrue := (hInv.remsetSync u).mp hIn
            rw [hRemFalse] at hTrue
            cases hTrue
          refine
            { markLen     := by simp [hInv.markLen]
              remBitLen   := by simp [hInv.remBitLen]
              validPtrs   := hValidPtrs'
              maskSound   := hMaskSound'
              remsetSync  := ?_
              remsetValid := ?_
              remsetNodup := List.Pairwise.cons (fun x hx hEq => huNotInRem (hEq ▸ hx)) hInv.remsetNodup
              oldToYoung  := ?_ }
          · intro w
            by_cases hwu : w = u
            · subst hwu
              simp [List.getElem?_set_self huLtRem]
            · simp [List.getElem?_set_ne (Ne.symm hwu), hwu, hInv.remsetSync w]
          · intro w hwMem
            dsimp only at hwMem ⊢
            rw [hAllocIff w]
            simp only [List.mem_cons] at hwMem
            rcases hwMem with rfl | hwOld
            · exact ⟨objU, hu⟩
            · exact hInv.remsetValid w hwOld
          · intro w objW v hw hOld hvMem hYoung
            by_cases hwu : w = u
            · subst hwu
              exact List.mem_cons_self ..
            · dsimp only at hw hOld hYoung ⊢
              simp only [List.getElem?_set_ne (Ne.symm hwu)] at hw
              exact List.mem_cons_of_mem u (hInv.oldToYoung w objW v hw hOld hvMem hYoung)
        · simp only [hCond, Bool.false_eq_true, ↓reduceIte]
          refine
            { markLen     := by simp [hInv.markLen]
              remBitLen   := by simp [hInv.remBitLen]
              validPtrs   := hValidPtrs'
              maskSound   := hMaskSound'
              remsetSync  := hInv.remsetSync
              remsetValid := fun w hw => (hAllocIff w).mpr (hInv.remsetValid w hw)
              remsetNodup := hInv.remsetNodup
              oldToYoung  := ?_ }
          intro w objW v hw hOld hvMem hYoung
          dsimp only at hw hOld hYoung ⊢
          by_cases hwu : w = u
          · subst hwu
            have hRemSome : s.rememberedBit[w]? = some (s.rememberedBit[w]) :=
              List.getElem?_eq_getElem huLtRem
            cases hb : s.rememberedBit[w]
            · rw [hb] at hRemSome
              have hBoth : (s.markBits[w]? == some true && s.rememberedBit[w]? == some false) = true := by
                simp [hOld, hRemSome]
              exact False.elim (hCond hBoth)
            · rw [hb] at hRemSome
              exact (hInv.remsetSync w).mpr hRemSome
          · simp only [List.getElem?_set_ne (Ne.symm hwu)] at hw
            exact hInv.oldToYoung w objW v hw hOld hvMem hYoung
      · simp only [hMutIdx, Bool.false_eq_true, ↓reduceIte]
        exact hInv

/-! ## Part 4: Executable Minor & Major GC Collectors and Soundness/Completeness -/

/-! ### Exact Mask-Guided Child Scanning (`scannedChildren`) -/

/-- Scan payload words starting at `idx`, collecting target `ObjId`s at positions
    covered by `hdrMask` (`drain_mark_stack` / `scan_object_children_only` in `gc_bitmap.c`). -/
def scannedChildrenAux (hdrMask : Option Nat) (idx : Nat) : List Word → List ObjId
  | [] => []
  | w :: ws =>
    let rest := scannedChildrenAux hdrMask (idx + 1) ws
    match w with
    | .ptr (some oid) =>
      if maskCoversWord hdrMask idx then oid :: rest else rest
    | _ => rest

/-- Extract all child `ObjId`s scanned by the collector on `obj` under `obj.hdrMask`. -/
def scannedChildren (obj : HeapObj) : List ObjId :=
  scannedChildrenAux obj.hdrMask 0 obj.words

private theorem mem_scannedChildrenAux_iff (hdrMask : Option Nat) (startIdx : Nat)
    (ws : List Word) (v : ObjId) :
    v ∈ scannedChildrenAux hdrMask startIdx ws ↔
      ∃ (i : Nat), ws[i]? = some (.ptr (some v)) ∧ maskCoversWord hdrMask (startIdx + i) = true := by
  induction ws generalizing startIdx with
  | nil =>
    simp [scannedChildrenAux]
  | cons w ws ih =>
    constructor
    · intro hMem
      cases w with
      | scalar _ =>
        simp only [scannedChildrenAux] at hMem
        rcases (ih (startIdx + 1)).mp hMem with ⟨j, hj, hCov⟩
        exact ⟨j + 1, hj, by simpa [Nat.add_assoc, Nat.add_comm 1 j] using hCov⟩
      | ptr opt =>
        cases opt with
        | none =>
          simp only [scannedChildrenAux] at hMem
          rcases (ih (startIdx + 1)).mp hMem with ⟨j, hj, hCov⟩
          exact ⟨j + 1, hj, by simpa [Nat.add_assoc, Nat.add_comm 1 j] using hCov⟩
        | some oid =>
          by_cases hCov0 : maskCoversWord hdrMask startIdx = true
          · simp only [scannedChildrenAux, hCov0, ↓reduceIte, List.mem_cons] at hMem
            rcases hMem with rfl | hRest
            · exact ⟨0, rfl, by simpa using hCov0⟩
            · rcases (ih (startIdx + 1)).mp hRest with ⟨j, hj, hCov⟩
              exact ⟨j + 1, hj, by simpa [Nat.add_assoc, Nat.add_comm 1 j] using hCov⟩
          · simp only [scannedChildrenAux, hCov0, Bool.false_eq_true, ↓reduceIte] at hMem
            rcases (ih (startIdx + 1)).mp hMem with ⟨j, hj, hCov⟩
            exact ⟨j + 1, hj, by simpa [Nat.add_assoc, Nat.add_comm 1 j] using hCov⟩
    · rintro ⟨i, hi, hCov⟩
      cases i with
      | zero =>
        simp only [List.getElem?_cons_zero, Option.some.injEq] at hi
        subst hi
        simp only [Nat.add_zero] at hCov
        simp [scannedChildrenAux, hCov]
      | succ j =>
        simp only [List.getElem?_cons_succ] at hi
        have hCov' : maskCoversWord hdrMask ((startIdx + 1) + j) = true := by
          simpa [Nat.add_assoc, Nat.add_comm 1 j] using hCov
        have hRest := (ih (startIdx + 1)).mpr ⟨j, hi, hCov'⟩
        cases w with
        | scalar _ =>
          simpa [scannedChildrenAux] using hRest
        | ptr opt =>
          cases opt with
          | none =>
            simpa [scannedChildrenAux] using hRest
          | some oid =>
            by_cases hCov0 : maskCoversWord hdrMask startIdx = true
            · simp [scannedChildrenAux, hCov0, hRest]
            · simp [scannedChildrenAux, hCov0, hRest]

/-- Exact membership characterization for `scannedChildren`. -/
theorem mem_scannedChildren_iff (obj : HeapObj) (v : ObjId) :
    v ∈ scannedChildren obj ↔
      ∃ (idx : Nat), obj.words[idx]? = some (.ptr (some v)) ∧ maskCoversWord obj.hdrMask idx = true := by
  simpa [scannedChildren] using mem_scannedChildrenAux_iff obj.hdrMask 0 obj.words v

private theorem mem_iff_exists_getElem? {α : Type} (x : α) (xs : List α) :
    x ∈ xs ↔ ∃ (idx : Nat), xs[idx]? = some x := by
  induction xs with
  | nil => simp
  | cons a as ih =>
    constructor
    · intro h
      simp only [List.mem_cons] at h
      rcases h with rfl | hRest
      · exact ⟨0, rfl⟩
      · rcases ih.mp hRest with ⟨j, hj⟩
        exact ⟨j + 1, hj⟩
    · rintro ⟨idx, hIdx⟩
      cases idx with
      | zero =>
        simp only [List.getElem?_cons_zero, Option.some.injEq] at hIdx
        exact hIdx ▸ List.mem_cons_self ..
      | succ j =>
        simp only [List.getElem?_cons_succ] at hIdx
        exact List.mem_cons_of_mem a (ih.mpr ⟨j, hIdx⟩)

/-- **Pointer-Mask Scanning Completeness (`mem_scannedChildren_of_maskSound`)**:
    Whenever `ObjMaskSound obj` holds, every pointer `Word.ptr (some v) ∈ obj.words`
    is guaranteed to be visited by `scannedChildren obj`. -/
theorem mem_scannedChildren_of_maskSound {obj : HeapObj} {v : ObjId}
    (hMask : ObjMaskSound obj) (hMem : Word.ptr (some v) ∈ obj.words) :
    v ∈ scannedChildren obj := by
  rcases (mem_iff_exists_getElem? _ _).mp hMem with ⟨idx, hIdx⟩
  exact (mem_scannedChildren_iff obj v).mpr ⟨idx, hIdx, hMask.2 idx v hIdx⟩

theorem mem_words_of_mem_scannedChildren {obj : HeapObj} {v : ObjId}
    (hMem : v ∈ scannedChildren obj) :
    Word.ptr (some v) ∈ obj.words := by
  rcases (mem_scannedChildren_iff obj v).mp hMem with ⟨idx, hIdx, _⟩
  exact (mem_iff_exists_getElem? _ _).mpr ⟨idx, hIdx⟩

/-! ### Reusable Monotone Boolean-Vector Fixed-Point Engine -/

/-- Count the number of `true` bits in a mark vector. -/
def countTrue : List Bool → Nat
  | [] => 0
  | b :: bs => (if b then 1 else 0) + countTrue bs

/-- Iterate a monotone mark-propagation pass `fuel` times. -/
def iterStep (step : List Bool → List Bool) : Nat → List Bool → List Bool
  | 0, m => m
  | k + 1, m => iterStep step k (step m)

private theorem countTrue_le_length (bs : List Bool) :
    countTrue bs ≤ bs.length := by
  induction bs with
  | nil => simp [countTrue]
  | cons b bs ih =>
    cases b <;> simp [countTrue] <;> omega

private theorem countTrue_mono_and_strict {as bs : List Bool}
    (hLen : as.length = bs.length)
    (hImp : ∀ (i : Nat), as[i]? = some true → bs[i]? = some true) :
    countTrue as ≤ countTrue bs ∧ (as ≠ bs → countTrue as < countTrue bs) := by
  induction as generalizing bs with
  | nil =>
    cases bs with
    | nil => simp [countTrue]
    | cons _ _ => simp at hLen
  | cons a as ih =>
    cases bs with
    | nil => simp at hLen
    | cons b bs =>
      simp only [List.length_cons, Nat.add_right_cancel_iff] at hLen
      have hHead : a = true → b = true := by
        intro ha
        have h0 := hImp 0 (by simp [ha])
        simpa using h0
      have hTail : ∀ (j : Nat), as[j]? = some true → bs[j]? = some true := by
        intro j hj
        exact hImp (j + 1) hj
      rcases ih hLen hTail with ⟨hLe, hStrict⟩
      cases a <;> cases b
      · refine ⟨by simp [countTrue]; omega, ?_⟩
        intro hNe
        have hTailNe : as ≠ bs := fun hEq => hNe (hEq ▸ rfl)
        have hLt := hStrict hTailNe
        simp [countTrue]; omega
      · refine ⟨by simp [countTrue]; omega, ?_⟩
        intro _
        simp [countTrue]; omega
      · exact False.elim (Bool.noConfusion (hHead rfl))
      · refine ⟨by simp [countTrue]; omega, ?_⟩
        intro hNe
        have hTailNe : as ≠ bs := fun hEq => hNe (hEq ▸ rfl)
        have hLt := hStrict hTailNe
        simp [countTrue]; omega

private theorem iterStep_of_fixpoint {step : List Bool → List Bool} {m : List Bool}
    (hFix : step m = m) (fuel : Nat) :
    iterStep step fuel m = m := by
  induction fuel with
  | zero => rfl
  | succ k ih => simp [iterStep, hFix, ih]

private theorem iterStep_length {step : List Bool → List Bool} {n : Nat}
    (hStepLen : ∀ (m : List Bool), m.length = n → (step m).length = n)
    (fuel : Nat) {m : List Bool} (hm : m.length = n) :
    (iterStep step fuel m).length = n := by
  induction fuel generalizing m with
  | zero => exact hm
  | succ k ih => exact ih (hStepLen m hm)

private theorem iterStep_mono {step : List Bool → List Bool} {n : Nat}
    (hStepLen : ∀ (m : List Bool), m.length = n → (step m).length = n)
    (hStepMono : ∀ (m : List Bool), m.length = n → ∀ (i : Nat), m[i]? = some true → (step m)[i]? = some true)
    (fuel : Nat) {m : List Bool} (hm : m.length = n) {i : Nat}
    (hi : m[i]? = some true) :
    (iterStep step fuel m)[i]? = some true := by
  induction fuel generalizing m with
  | zero => exact hi
  | succ k ih => exact ih (hStepLen m hm) (hStepMono m hm i hi)

private theorem iterStep_inv {step : List Bool → List Bool} {n : Nat} {P : ObjId → Prop}
    (hStepLen : ∀ (m : List Bool), m.length = n → (step m).length = n)
    (hStepInv : ∀ (m : List Bool), m.length = n → (∀ (i : ObjId), m[i]? = some true → P i) →
      ∀ (i : ObjId), (step m)[i]? = some true → P i)
    (fuel : Nat) {m : List Bool} (hm : m.length = n)
    (hInit : ∀ (i : ObjId), m[i]? = some true → P i) :
    ∀ (i : ObjId), (iterStep step fuel m)[i]? = some true → P i := by
  induction fuel generalizing m with
  | zero => exact hInit
  | succ k ih => exact ih (hStepLen m hm) (hStepInv m hm hInit)

private theorem iterStep_fixpoint_aux {step : List Bool → List Bool} {n : Nat}
    (hStepLen : ∀ (m : List Bool), m.length = n → (step m).length = n)
    (hStepMono : ∀ (m : List Bool), m.length = n → ∀ (i : Nat), m[i]? = some true → (step m)[i]? = some true)
    (fuel : Nat) {m : List Bool} (hm : m.length = n)
    (hBudget : n - countTrue m ≤ fuel) :
    step (iterStep step fuel m) = iterStep step fuel m := by
  induction fuel generalizing m with
  | zero =>
    simp only [iterStep]
    by_cases hEq : m = step m
    · exact hEq.symm
    · have hLenStep : (step m).length = n := hStepLen m hm
      have hLt := (countTrue_mono_and_strict (hm.trans hLenStep.symm) (hStepMono m hm)).2 hEq
      have hBoundStep : countTrue (step m) ≤ n := hLenStep ▸ countTrue_le_length (step m)
      omega
  | succ k ih =>
    by_cases hEq : step m = m
    · rw [iterStep_of_fixpoint hEq (k + 1), hEq]
    · have hNe : m ≠ step m := fun h => hEq h.symm
      have hLenStep : (step m).length = n := hStepLen m hm
      have hLt := (countTrue_mono_and_strict (hm.trans hLenStep.symm) (hStepMono m hm)).2 hNe
      exact ih hLenStep (by omega)

/-- Any monotone boolean operator on `List Bool` of length `n` reaches an exact
    fixed point after `n` iterations (`iterStep step n init`). -/
theorem iterStep_fixpoint {step : List Bool → List Bool} {n : Nat}
    (hStepLen : ∀ (m : List Bool), m.length = n → (step m).length = n)
    (hStepMono : ∀ (m : List Bool), m.length = n → ∀ (i : Nat), m[i]? = some true → (step m)[i]? = some true)
    {init : List Bool} (hInitLen : init.length = n) :
    step (iterStep step n init) = iterStep step n init :=
  iterStep_fixpoint_aux hStepLen hStepMono n hInitLen (by omega)

/-! ### Heap Predicates, Sweep, Sticky Minor GC, and Full Major GC -/

/-- Whether slot `oid` currently holds a live allocated `HeapObj`. -/
def isAllocated (heap : List (Option HeapObj)) (oid : ObjId) : Bool :=
  match heap[oid]? with
  | some (some _) => true
  | _ => false

/-- Whether live object `u` scans `v` under `u`'s exact/conservative header mask. -/
def hasScannedEdge (heap : List (Option HeapObj)) (u v : ObjId) : Bool :=
  match heap[u]? with
  | some (some objU) => decide (v ∈ scannedChildren objU)
  | _ => false

/-- Sweep unmarked heap slots to `none` while preserving surviving objects in-place. -/
def sweepHeap (heap : List (Option HeapObj)) (keepBits : List Bool) : List (Option HeapObj) :=
  (List.range heap.length).map fun oid =>
    if decide (keepBits[oid]? = some true) then
      (heap[oid]?).join
    else
      none

/-- Whether `oid` is an allocated Young-generation object (`markBits[oid] = false`). -/
def isYoungObj (s : GcState) (oid : ObjId) : Bool :=
  isAllocated s.heap oid && decide (s.markBits[oid]? = some false)

/-- Whether `oid` is an allocated Old-generation object (`markBits[oid] = true`). -/
def isOldObj (s : GcState) (oid : ObjId) : Bool :=
  isAllocated s.heap oid && decide (s.markBits[oid]? = some true)

/-- Initial Young-generation mark seeds in Sticky Minor GC (`gc_bitmap.c`):
    ONLY Young roots (`try_mark_ptr_push` skips Old roots whose `mark_bit` is already `1`)
    and Young children of remembered Old containers (`scan_object_children_only` on `remset`). -/
def minorInitYoungMarks (s : GcState) (roots : List ObjId) : List Bool :=
  (List.range s.heap.length).map fun v =>
    isYoungObj s v &&
      (decide (v ∈ roots) || s.remset.any fun u => hasScannedEdge s.heap u v)

/-- One Young-only mark-stack propagation step in Sticky Minor GC (`drain_mark_stack`):
    ONLY newly marked Young objects (`isYoungObj s u`) propagate marks to their
    Young children (`isYoungObj s v`); Old objects outside `remset` are never rescanned! -/
def minorYoungMarkStep (s : GcState) (youngMarks : List Bool) : List Bool :=
  let n := s.heap.length
  (List.range n).map fun v =>
    decide (youngMarks[v]? = some true) ||
      (isYoungObj s v &&
        (List.range n).any fun u =>
          decide (youngMarks[u]? = some true) && isYoungObj s u && hasScannedEdge s.heap u v)

/-- Fixed-point Young mark closure in Sticky Minor GC. -/
def minorYoungMarkClosure (s : GcState) (roots : List ObjId) : List Bool :=
  iterStep (minorYoungMarkStep s) s.heap.length (minorInitYoungMarks s roots)

/-- Final survival/sticky-mark bitmap after Minor GC: Old objects keep their sticky
    `markBit = true`, and marked Young objects survive and promote to Old (`true`). -/
def minorSurvives (s : GcState) (roots : List ObjId) : List Bool :=
  let youngMarked := minorYoungMarkClosure s roots
  (List.range s.heap.length).map fun oid =>
    isOldObj s oid || decide (youngMarked[oid]? = some true)

/-- **Executable Sticky Minor GC (`minorGcCollect`)**, faithfully modeling
    `gc_collect_locked(..., is_major = false)` in `runtime/runtime/gc_bitmap.c`. -/
def minorGcCollect (s : GcState) (roots : List ObjId) : GcState :=
  let n := s.heap.length
  let survived := minorSurvives s roots
  { heap          := sweepHeap s.heap survived
    markBits      := survived
    rememberedBit := List.replicate n false
    remset        := [] }

/-- Initial root marks in Full Major GC (`is_major = true`: all `mark_bits` cleared first). -/
def majorInitMarks (heap : List (Option HeapObj)) (roots : List ObjId) : List Bool :=
  (List.range heap.length).map fun oid =>
    decide (oid ∈ roots) && isAllocated heap oid

/-- One full-heap mark-stack propagation step in Major GC. -/
def majorMarkStep (heap : List (Option HeapObj)) (marks : List Bool) : List Bool :=
  let n := heap.length
  (List.range n).map fun v =>
    decide (marks[v]? = some true) ||
      (isAllocated heap v &&
        (List.range n).any fun u =>
          decide (marks[u]? = some true) && hasScannedEdge heap u v)

/-- Fixed-point full-heap mark closure in Major GC. -/
def majorMarkClosure (heap : List (Option HeapObj)) (roots : List ObjId) : List Bool :=
  iterStep (majorMarkStep heap) heap.length (majorInitMarks heap roots)

/-- **Executable Full Major GC (`majorGcCollect`)**, faithfully modeling
    `gc_collect_locked(..., is_major = true)` in `runtime/runtime/gc_bitmap.c`. -/
def majorGcCollect (s : GcState) (roots : List ObjId) : GcState :=
  let n := s.heap.length
  let survived := majorMarkClosure s.heap roots
  { heap          := sweepHeap s.heap survived
    markBits      := survived
    rememberedBit := List.replicate n false
    remset        := [] }

/-! ### Helper Lemmas on `List.range`, `isAllocated`, and `sweepHeap` -/

private theorem getElem?_map_range {α : Type} (n : Nat) (f : Nat → α) {i : Nat} (hi : i < n) :
    ((List.range n).map f)[i]? = some (f i) := by
  rw [List.getElem?_map, List.getElem?_range hi]
  rfl

private theorem isAllocated_iff (heap : List (Option HeapObj)) (oid : ObjId) :
    isAllocated heap oid = true ↔ ∃ obj, heap[oid]? = some (some obj) := by
  unfold isAllocated
  cases h : heap[oid]? with
  | none => simp
  | some opt =>
    cases opt with
    | none => simp
    | some obj => simp

private theorem hasScannedEdge_iff (heap : List (Option HeapObj)) (u v : ObjId) :
    hasScannedEdge heap u v = true ↔
      ∃ objU, heap[u]? = some (some objU) ∧ v ∈ scannedChildren objU := by
  unfold hasScannedEdge
  cases h : heap[u]? with
  | none => simp
  | some opt =>
    cases opt with
    | none => simp
    | some objU => simp

private theorem sweepHeap_length (heap : List (Option HeapObj)) (keepBits : List Bool) :
    (sweepHeap heap keepBits).length = heap.length := by
  simp [sweepHeap]

private theorem sweepHeap_eq_of_keep {heap : List (Option HeapObj)} {keepBits : List Bool}
    {oid : ObjId} {obj : HeapObj}
    (hObj : heap[oid]? = some (some obj))
    (hKeep : keepBits[oid]? = some true) :
    (sweepHeap heap keepBits)[oid]? = heap[oid]? := by
  have hLt : oid < heap.length := lt_len_of_getElem?_some hObj
  unfold sweepHeap
  rw [getElem?_map_range heap.length _ hLt]
  simp [hKeep, hObj]

private theorem sweepHeap_some_some_iff {heap : List (Option HeapObj)} {keepBits : List Bool}
    {oid : ObjId} {obj : HeapObj} :
    (sweepHeap heap keepBits)[oid]? = some (some obj) ↔
      keepBits[oid]? = some true ∧ heap[oid]? = some (some obj) := by
  constructor
  · intro hSweep
    have hLt : oid < heap.length := by
      have h := lt_len_of_getElem?_some hSweep
      simpa [sweepHeap] using h
    unfold sweepHeap at hSweep
    rw [getElem?_map_range heap.length _ hLt] at hSweep
    simp only [Option.some.injEq] at hSweep
    split at hSweep
    · rename_i hKeep
      have hKeep' : keepBits[oid]? = some true := of_decide_eq_true hKeep
      cases hOrig : heap[oid]? with
      | none => rw [hOrig] at hSweep; cases hSweep
      | some opt =>
        cases opt with
        | none => rw [hOrig] at hSweep; cases hSweep
        | some o =>
          rw [hOrig] at hSweep
          injection hSweep with hEq
          subst hEq
          exact ⟨hKeep', rfl⟩
    · cases hSweep
  · rintro ⟨hKeep, hOrig⟩
    rw [sweepHeap_eq_of_keep hOrig hKeep, hOrig]

private theorem getElem?_replicate_false_ne_true (n u : Nat) :
    (List.replicate n false)[u]? ≠ some true := by
  rw [List.getElem?_replicate]
  split <;> simp

private theorem reachable_of_sweepHeap {heap : List (Option HeapObj)} {keepBits : List Bool}
    {roots : List ObjId} {oid : ObjId}
    (hReach : Reachable (sweepHeap heap keepBits) roots oid) :
    Reachable heap roots oid := by
  induction hReach with
  | root hr hObj =>
    exact Reachable.root hr (sweepHeap_some_some_iff.mp hObj).2
  | step _ hObjU hEdge hObjV ih =>
    exact Reachable.step ih
      (sweepHeap_some_some_iff.mp hObjU).2
      hEdge
      (sweepHeap_some_some_iff.mp hObjV).2

/-! ### Sticky Minor GC Soundness & Invariant Preservation -/

private theorem minorInitYoungMarks_length (s : GcState) (roots : List ObjId) :
    (minorInitYoungMarks s roots).length = s.heap.length := by
  simp [minorInitYoungMarks]

private theorem minorYoungMarkStep_length (s : GcState) (m : List Bool) :
    (minorYoungMarkStep s m).length = s.heap.length := by
  simp [minorYoungMarkStep]

private theorem minorYoungMarkStep_mono (s : GcState) (m : List Bool)
    (hm : m.length = s.heap.length) (i : Nat) (hi : m[i]? = some true) :
    (minorYoungMarkStep s m)[i]? = some true := by
  have hiLt : i < s.heap.length := hm ▸ lt_len_of_getElem?_some hi
  unfold minorYoungMarkStep
  rw [getElem?_map_range s.heap.length _ hiLt]
  simp [hi]

private theorem minorYoungMarkClosure_length (s : GcState) (roots : List ObjId) :
    (minorYoungMarkClosure s roots).length = s.heap.length :=
  iterStep_length (fun m _ => minorYoungMarkStep_length s m)
    s.heap.length (minorInitYoungMarks_length s roots)

private theorem minorYoungMarkClosure_fixpoint (s : GcState) (roots : List ObjId) :
    minorYoungMarkStep s (minorYoungMarkClosure s roots) = minorYoungMarkClosure s roots :=
  iterStep_fixpoint
    (fun m _ => minorYoungMarkStep_length s m)
    (fun m hm i hi => minorYoungMarkStep_mono s m hm i hi)
    (minorInitYoungMarks_length s roots)

private theorem minorYoungMarkClosure_isYoung (s : GcState) (roots : List ObjId) :
    ∀ (i : ObjId), (minorYoungMarkClosure s roots)[i]? = some true → isYoungObj s i = true := by
  unfold minorYoungMarkClosure
  apply iterStep_inv
    (n := s.heap.length)
    (P := fun i => isYoungObj s i = true)
    (hStepLen := fun m _ => minorYoungMarkStep_length s m)
  · intro m _ hPrev i hi
    have hiLt : i < s.heap.length := by
      have h := lt_len_of_getElem?_some hi
      simpa [minorYoungMarkStep] using h
    unfold minorYoungMarkStep at hi
    rw [getElem?_map_range s.heap.length _ hiLt] at hi
    simp only [Option.some.injEq, Bool.or_eq_true, decide_eq_true_eq, Bool.and_eq_true] at hi
    rcases hi with hOldMark | ⟨hYoung, _⟩
    · exact hPrev i hOldMark
    · exact hYoung
  · exact minorInitYoungMarks_length s roots
  · intro i hi
    have hiLt : i < s.heap.length := by
      have h := lt_len_of_getElem?_some hi
      simpa [minorInitYoungMarks] using h
    unfold minorInitYoungMarks at hi
    rw [getElem?_map_range s.heap.length _ hiLt] at hi
    simp only [Option.some.injEq, Bool.and_eq_true] at hi
    exact hi.1

private theorem minorSurvives_length (s : GcState) (roots : List ObjId) :
    (minorSurvives s roots).length = s.heap.length := by
  simp [minorSurvives]

/-- Core edge-closure lemma for Sticky Minor GC: under `GenHeapInv s`, the survival
    set `minorSurvives s roots` is closed under ALL heap pointer edges!
    - Old -> Old & Young -> Old edges hold because Old objects keep their sticky mark;
    - Old -> Young edges hold because `GenHeapInv.oldToYoung` guarantees `u ∈ s.remset`;
    - Young -> Young edges hold by fixed-point closure of `minorYoungMarkClosure`. -/
theorem minorSurvives_edge_closed (s : GcState) (roots : List ObjId)
    (hInv : GenHeapInv s) {u v : ObjId} {objU : HeapObj}
    (huSurv : (minorSurvives s roots)[u]? = some true)
    (huObj : s.heap[u]? = some (some objU))
    (hEdge : Word.ptr (some v) ∈ objU.words) :
    (minorSurvives s roots)[v]? = some true := by
  rcases hInv.validPtrs u objU v huObj hEdge with ⟨objV, hvObj⟩
  have hvLt : v < s.heap.length := lt_len_of_getElem?_some hvObj
  have hvMarkLt : v < s.markBits.length := hInv.markLen ▸ hvLt
  have hvAlloc : isAllocated s.heap v = true := (isAllocated_iff s.heap v).mpr ⟨objV, hvObj⟩
  have huLt : u < s.heap.length := lt_len_of_getElem?_some huObj
  unfold minorSurvives
  rw [getElem?_map_range s.heap.length _ hvLt]
  simp only [Option.some.injEq]
  have hvMarkSome : s.markBits[v]? = some (s.markBits[v]) :=
    List.getElem?_eq_getElem hvMarkLt
  cases hvb : s.markBits[v]
  · rw [hvb] at hvMarkSome
    have hvYoung : isYoungObj s v = true := by
      simp [isYoungObj, hvAlloc, hvMarkSome]
    have hScanned : hasScannedEdge s.heap u v = true :=
      (hasScannedEdge_iff s.heap u v).mpr
        ⟨objU, huObj, mem_scannedChildren_of_maskSound (hInv.maskSound u objU huObj) hEdge⟩
    unfold minorSurvives at huSurv
    rw [getElem?_map_range s.heap.length _ huLt] at huSurv
    simp only [Option.some.injEq, Bool.or_eq_true, decide_eq_true_eq] at huSurv
    rcases huSurv with huOld | huYoungMarked
    · simp only [isOldObj, Bool.and_eq_true, decide_eq_true_eq] at huOld
      have huInRem : u ∈ s.remset :=
        hInv.oldToYoung u objU v huObj huOld.2 hEdge hvMarkSome
      have hvInit : (minorInitYoungMarks s roots)[v]? = some true := by
        unfold minorInitYoungMarks
        rw [getElem?_map_range s.heap.length _ hvLt]
        simp only [Option.some.injEq, Bool.and_eq_true, Bool.or_eq_true, List.any_eq_true]
        exact ⟨hvYoung, Or.inr ⟨u, huInRem, hScanned⟩⟩
      have hvMarked : (minorYoungMarkClosure s roots)[v]? = some true :=
        iterStep_mono
          (fun m _ => minorYoungMarkStep_length s m)
          (fun m hm i hi => minorYoungMarkStep_mono s m hm i hi)
          s.heap.length
          (minorInitYoungMarks_length s roots)
          hvInit
      simp [hvMarked]
    · have huYoung : isYoungObj s u = true :=
        minorYoungMarkClosure_isYoung s roots u huYoungMarked
      have hStepV : (minorYoungMarkStep s (minorYoungMarkClosure s roots))[v]? = some true := by
        unfold minorYoungMarkStep
        rw [getElem?_map_range s.heap.length _ hvLt]
        simp only [Option.some.injEq, Bool.or_eq_true, Bool.and_eq_true,
          List.any_eq_true, List.mem_range, decide_eq_true_eq]
        exact Or.inr ⟨hvYoung, u, huLt, ⟨huYoungMarked, huYoung⟩, hScanned⟩
      rw [minorYoungMarkClosure_fixpoint s roots] at hStepV
      simp [hStepV]
  · rw [hvb] at hvMarkSome
    have hvOld : isOldObj s v = true := by
      simp [isOldObj, hvAlloc, hvMarkSome]
    simp [hvOld]

private theorem minorSurvives_of_reachable (s : GcState) (roots : List ObjId)
    (hInv : GenHeapInv s) {oid : ObjId} (hReach : Reachable s.heap roots oid) :
    (minorSurvives s roots)[oid]? = some true := by
  induction hReach with
  | root hr hObj =>
    rename_i r obj
    have hrLt : r < s.heap.length := lt_len_of_getElem?_some hObj
    have hrMarkLt : r < s.markBits.length := hInv.markLen ▸ hrLt
    have hrAlloc : isAllocated s.heap r = true := (isAllocated_iff s.heap r).mpr ⟨obj, hObj⟩
    have hrMarkSome : s.markBits[r]? = some (s.markBits[r]) :=
      List.getElem?_eq_getElem hrMarkLt
    unfold minorSurvives
    rw [getElem?_map_range s.heap.length _ hrLt]
    simp only [Option.some.injEq]
    cases hrb : s.markBits[r]
    · rw [hrb] at hrMarkSome
      have hrYoung : isYoungObj s r = true := by simp [isYoungObj, hrAlloc, hrMarkSome]
      have hrInit : (minorInitYoungMarks s roots)[r]? = some true := by
        unfold minorInitYoungMarks
        rw [getElem?_map_range s.heap.length _ hrLt]
        simp [hrYoung, hr]
      have hrMarked : (minorYoungMarkClosure s roots)[r]? = some true :=
        iterStep_mono
          (fun m _ => minorYoungMarkStep_length s m)
          (fun m hm i hi => minorYoungMarkStep_mono s m hm i hi)
          s.heap.length
          (minorInitYoungMarks_length s roots)
          hrInit
      simp [hrMarked]
    · rw [hrb] at hrMarkSome
      have hrOld : isOldObj s r = true := by simp [isOldObj, hrAlloc, hrMarkSome]
      simp [hrOld]
  | step _ hObjU hEdge _ ih =>
    exact minorSurvives_edge_closed s roots hInv ih hObjU hEdge

/-- **Sticky Minor GC Soundness (`minorGc_sound`)**:
    Under `GenHeapInv s`, `minorGcCollect` NEVER sweeps or corrupts any object
    `Reachable` from `roots`, even though Old objects outside `remset` are never
    rescanned and objects `≤ 40` words are scanned strictly via their 40-bit masks. -/
theorem minorGc_sound (s : GcState) (roots : List ObjId) (oid : ObjId)
    (hInv : GenHeapInv s) (hReach : Reachable s.heap roots oid) :
    (minorGcCollect s roots).heap[oid]? = s.heap[oid]? := by
  rcases hReach.allocated with ⟨obj, hObj⟩
  exact sweepHeap_eq_of_keep hObj (minorSurvives_of_reachable s roots hInv hReach)

/-- **Sticky Minor GC Preserves `GenHeapInv` (`minorGc_preserves_inv`)**:
    After `minorGcCollect`, all surviving objects are promoted to the Old generation
    (`markBits = true`), `remset` is emptied, and `GenHeapInv` holds unconditionally. -/
theorem minorGc_preserves_inv (s : GcState) (roots : List ObjId)
    (hInv : GenHeapInv s) :
    GenHeapInv (minorGcCollect s roots) := by
  refine
    { markLen     := by simp [minorGcCollect, minorSurvives_length, sweepHeap_length]
      remBitLen   := by simp [minorGcCollect, sweepHeap_length]
      validPtrs   := ?_
      maskSound   := ?_
      remsetSync  := fun u => by simp [minorGcCollect, getElem?_replicate_false_ne_true]
      remsetValid := fun _ h => by simp [minorGcCollect] at h
      remsetNodup := List.Pairwise.nil
      oldToYoung  := ?_ }
  · intro u objU v hu hEdge
    rcases sweepHeap_some_some_iff.mp hu with ⟨huSurv, huOrig⟩
    have hvSurv := minorSurvives_edge_closed s roots hInv huSurv huOrig hEdge
    rcases hInv.validPtrs u objU v huOrig hEdge with ⟨objV, hvOrig⟩
    exact ⟨objV, sweepHeap_some_some_iff.mpr ⟨hvSurv, hvOrig⟩⟩
  · intro u objU hu
    exact hInv.maskSound u objU (sweepHeap_some_some_iff.mp hu).2
  · intro u objU v hu _ hEdge hYoung
    rcases sweepHeap_some_some_iff.mp hu with ⟨huSurv, huOrig⟩
    have hvSurv := minorSurvives_edge_closed s roots hInv huSurv huOrig hEdge
    simp only [minorGcCollect] at hYoung
    rw [hvSurv] at hYoung
    cases hYoung

/-- **Sticky Minor GC Preserves Exact Graph Reachability (`minorGc_reachable_iff`)**. -/
theorem minorGc_reachable_iff (s : GcState) (roots : List ObjId) (oid : ObjId)
    (hInv : GenHeapInv s) :
    Reachable (minorGcCollect s roots).heap roots oid ↔ Reachable s.heap roots oid := by
  constructor
  · exact reachable_of_sweepHeap
  · intro hReach
    induction hReach with
    | root hr hObj =>
      have hEq := minorGc_sound s roots _ hInv (Reachable.root hr hObj)
      exact Reachable.root hr (hEq.trans hObj)
    | step hReachU hObjU hEdge hObjV ih =>
      have hEqU := minorGc_sound s roots _ hInv hReachU
      have hEqV := minorGc_sound s roots _ hInv (Reachable.step hReachU hObjU hEdge hObjV)
      exact Reachable.step ih (hEqU.trans hObjU) hEdge (hEqV.trans hObjV)

/-! ### Missing Write-Barrier Unsoundness Counterexample (`missing_write_barrier_unsound`) -/

/-- Pre-mutation 2-object generational heap:
    - `oid 0`: Old-generation mutable `Cell` (`markBit = true`), promoted by a prior Minor GC;
    - `oid 1`: Newly allocated Young immutable scalar box (`markBit = false`). -/
def wbCounterexamplePreState : GcState :=
  let (s1, _) := gcAllocCell emptyGcState (.ptr none)
  let sOld    := minorGcCollect s1 [0]
  (gcAllocImmutable sOld (some 0) [.scalar 42]).1

/-- State after mutating Old `Cell` `0` to point to Young object `1` WITHOUT `gc_write_barrier`. -/
def wbCounterexampleBadState : GcState :=
  rawStoreNoBarrier wbCounterexamplePreState 0 0 (.ptr (some 1))

/-- State after mutating Old `Cell` `0` to point to Young object `1` WITH `gcWriteBarrierStore`. -/
def wbCounterexampleGoodState : GcState :=
  gcWriteBarrierStore wbCounterexamplePreState 0 0 (.ptr (some 1))

/-- **Necessity of the Generational Write Barrier (`missing_write_barrier_unsound`)**:
    1. Before the raw mutation, `wbCounterexamplePreState` satisfies `GenHeapInv`;
    2. After `rawStoreNoBarrier`, Young object `1` IS live (`Reachable ... [0] 1`) from root `0`;
    3. Yet `minorGcCollect` erroneously sweeps live Young object `1` to `none`
       (**Use-After-Free**), whereas `gcWriteBarrierStore` preserves object `1` intact! -/
theorem missing_write_barrier_unsound :
    GenHeapInv wbCounterexamplePreState ∧
    Reachable wbCounterexampleBadState.heap [0] 1 ∧
    (minorGcCollect wbCounterexampleBadState [0]).heap[1]? = some none ∧
    (minorGcCollect wbCounterexampleGoodState [0]).heap[1]? = wbCounterexampleGoodState.heap[1]? := by
  refine ⟨?_, ?_, rfl, rfl⟩
  · have hCellInv : GenHeapInv (gcAllocCell emptyGcState (.ptr none)).1 :=
      gcAllocCell_preserves_inv emptyGcState (.ptr none) emptyGcState_inv (fun _ h => by cases h)
    have hOldInv : GenHeapInv (minorGcCollect (gcAllocCell emptyGcState (.ptr none)).1 [0]) :=
      minorGc_preserves_inv _ [0] hCellInv
    exact gcAllocImmutable_preserves_inv _ (some 0) [.scalar 42] hOldInv
      ⟨fun _ _ => by decide, fun idx _ hGet => by cases idx <;> simp at hGet⟩
      (fun _ hv => by simp at hv)
  · have hRoot0 : Reachable wbCounterexampleBadState.heap [0] 0 :=
      Reachable.root
        (r := 0)
        (obj := { hdrMask := some 1, mutable := true, words := [.ptr (some 1)] })
        (List.mem_cons_self ..)
        rfl
    exact Reachable.step
      (u := 0) (v := 1)
      (objU := { hdrMask := some 1, mutable := true, words := [.ptr (some 1)] })
      (objV := { hdrMask := some 0, mutable := false, words := [.scalar 42] })
      hRoot0
      rfl
      (List.mem_cons_self ..)
      rfl

/-! ### Full Major GC Soundness, Completeness & Invariant Preservation -/

private theorem majorInitMarks_length (heap : List (Option HeapObj)) (roots : List ObjId) :
    (majorInitMarks heap roots).length = heap.length := by
  simp [majorInitMarks]

private theorem majorMarkStep_length (heap : List (Option HeapObj)) (m : List Bool) :
    (majorMarkStep heap m).length = heap.length := by
  simp [majorMarkStep]

private theorem majorMarkStep_mono (heap : List (Option HeapObj)) (m : List Bool)
    (hm : m.length = heap.length) (i : Nat) (hi : m[i]? = some true) :
    (majorMarkStep heap m)[i]? = some true := by
  have hiLt : i < heap.length := hm ▸ lt_len_of_getElem?_some hi
  unfold majorMarkStep
  rw [getElem?_map_range heap.length _ hiLt]
  simp [hi]

private theorem majorMarkClosure_length (heap : List (Option HeapObj)) (roots : List ObjId) :
    (majorMarkClosure heap roots).length = heap.length :=
  iterStep_length (fun m _ => majorMarkStep_length heap m)
    heap.length (majorInitMarks_length heap roots)

private theorem majorMarkClosure_fixpoint (heap : List (Option HeapObj)) (roots : List ObjId) :
    majorMarkStep heap (majorMarkClosure heap roots) = majorMarkClosure heap roots :=
  iterStep_fixpoint
    (fun m _ => majorMarkStep_length heap m)
    (fun m hm i hi => majorMarkStep_mono heap m hm i hi)
    (majorInitMarks_length heap roots)

private theorem majorMarkClosure_edge_closed (s : GcState) (roots : List ObjId)
    (hInv : GenHeapInv s) {u v : ObjId} {objU : HeapObj}
    (huMark : (majorMarkClosure s.heap roots)[u]? = some true)
    (huObj : s.heap[u]? = some (some objU))
    (hEdge : Word.ptr (some v) ∈ objU.words) :
    (majorMarkClosure s.heap roots)[v]? = some true := by
  rcases hInv.validPtrs u objU v huObj hEdge with ⟨objV, hvObj⟩
  have hvLt : v < s.heap.length := lt_len_of_getElem?_some hvObj
  have huLt : u < s.heap.length := lt_len_of_getElem?_some huObj
  have hvAlloc : isAllocated s.heap v = true := (isAllocated_iff s.heap v).mpr ⟨objV, hvObj⟩
  have hScanned : hasScannedEdge s.heap u v = true :=
    (hasScannedEdge_iff s.heap u v).mpr
      ⟨objU, huObj, mem_scannedChildren_of_maskSound (hInv.maskSound u objU huObj) hEdge⟩
  have hStepV : (majorMarkStep s.heap (majorMarkClosure s.heap roots))[v]? = some true := by
    unfold majorMarkStep
    rw [getElem?_map_range s.heap.length _ hvLt]
    simp only [Option.some.injEq, Bool.or_eq_true, Bool.and_eq_true,
      List.any_eq_true, List.mem_range, decide_eq_true_eq]
    exact Or.inr ⟨hvAlloc, u, huLt, huMark, hScanned⟩
  rwa [majorMarkClosure_fixpoint s.heap roots] at hStepV

private theorem majorMarkClosure_of_reachable (s : GcState) (roots : List ObjId)
    (hInv : GenHeapInv s) {oid : ObjId} (hReach : Reachable s.heap roots oid) :
    (majorMarkClosure s.heap roots)[oid]? = some true := by
  induction hReach with
  | root hr hObj =>
    rename_i r obj
    have hrLt : r < s.heap.length := lt_len_of_getElem?_some hObj
    have hrAlloc : isAllocated s.heap r = true := (isAllocated_iff s.heap r).mpr ⟨obj, hObj⟩
    have hrInit : (majorInitMarks s.heap roots)[r]? = some true := by
      unfold majorInitMarks
      rw [getElem?_map_range s.heap.length _ hrLt]
      simp [hr, hrAlloc]
    exact iterStep_mono
      (fun m _ => majorMarkStep_length s.heap m)
      (fun m hm i hi => majorMarkStep_mono s.heap m hm i hi)
      s.heap.length
      (majorInitMarks_length s.heap roots)
      hrInit
  | step _ hObjU hEdge _ ih =>
    exact majorMarkClosure_edge_closed s roots hInv ih hObjU hEdge

private theorem reachable_of_majorMarkClosure (heap : List (Option HeapObj)) (roots : List ObjId) :
    ∀ (oid : ObjId), (majorMarkClosure heap roots)[oid]? = some true → Reachable heap roots oid := by
  unfold majorMarkClosure
  apply iterStep_inv
    (n := heap.length)
    (P := fun oid => Reachable heap roots oid)
    (hStepLen := fun m _ => majorMarkStep_length heap m)
  · intro m _ hPrev v hv
    have hvLt : v < heap.length := by
      have h := lt_len_of_getElem?_some hv
      simpa [majorMarkStep] using h
    unfold majorMarkStep at hv
    rw [getElem?_map_range heap.length _ hvLt] at hv
    simp only [Option.some.injEq, Bool.or_eq_true, Bool.and_eq_true,
      List.any_eq_true, List.mem_range, decide_eq_true_eq] at hv
    rcases hv with hAlready | ⟨hvAlloc, u, _, huMark, hScanned⟩
    · exact hPrev v hAlready
    · rcases (isAllocated_iff heap v).mp hvAlloc with ⟨objV, hvObj⟩
      rcases (hasScannedEdge_iff heap u v).mp hScanned with ⟨objU, huObj, hvChild⟩
      exact Reachable.step (hPrev u huMark) huObj (mem_words_of_mem_scannedChildren hvChild) hvObj
  · exact majorInitMarks_length heap roots
  · intro r hr
    have hrLt : r < heap.length := by
      have h := lt_len_of_getElem?_some hr
      simpa [majorInitMarks] using h
    unfold majorInitMarks at hr
    rw [getElem?_map_range heap.length _ hrLt] at hr
    simp only [Option.some.injEq, Bool.and_eq_true, decide_eq_true_eq] at hr
    rcases (isAllocated_iff heap r).mp hr.2 with ⟨obj, hObj⟩
    exact Reachable.root hr.1 hObj

/-- **Full Major GC Soundness (`majorGc_sound`)**:
    Under `GenHeapInv s`, `majorGcCollect` preserves every `Reachable` object
    identically at its `ObjId`. -/
theorem majorGc_sound (s : GcState) (roots : List ObjId) (oid : ObjId)
    (hInv : GenHeapInv s) (hReach : Reachable s.heap roots oid) :
    (majorGcCollect s roots).heap[oid]? = s.heap[oid]? := by
  rcases hReach.allocated with ⟨obj, hObj⟩
  exact sweepHeap_eq_of_keep hObj (majorMarkClosure_of_reachable s roots hInv hReach)

/-- **Full Major GC Exact Completeness (`majorGc_complete`)**:
    Under `GenHeapInv s`, an object slot remains live after `majorGcCollect`
    if and only if it was `Reachable` from `roots` (zero memory leaks of
    unreachable cycles or floating Old-generation garbage). -/
theorem majorGc_complete (s : GcState) (roots : List ObjId) (oid : ObjId)
    (hInv : GenHeapInv s) :
    (∃ obj, (majorGcCollect s roots).heap[oid]? = some (some obj)) ↔
      Reachable s.heap roots oid := by
  constructor
  · rintro ⟨obj, hSweep⟩
    rcases sweepHeap_some_some_iff.mp hSweep with ⟨hMarked, _⟩
    exact reachable_of_majorMarkClosure s.heap roots oid hMarked
  · intro hReach
    rcases hReach.allocated with ⟨obj, hObj⟩
    exact ⟨obj, (majorGc_sound s roots oid hInv hReach).trans hObj⟩

/-- **Full Major GC Preserves `GenHeapInv` (`majorGc_preserves_inv`)**. -/
theorem majorGc_preserves_inv (s : GcState) (roots : List ObjId)
    (hInv : GenHeapInv s) :
    GenHeapInv (majorGcCollect s roots) := by
  refine
    { markLen     := by simp [majorGcCollect, majorMarkClosure_length, sweepHeap_length]
      remBitLen   := by simp [majorGcCollect, sweepHeap_length]
      validPtrs   := ?_
      maskSound   := ?_
      remsetSync  := fun u => by simp [majorGcCollect, getElem?_replicate_false_ne_true]
      remsetValid := fun _ h => by simp [majorGcCollect] at h
      remsetNodup := List.Pairwise.nil
      oldToYoung  := ?_ }
  · intro u objU v hu hEdge
    rcases sweepHeap_some_some_iff.mp hu with ⟨huMark, huOrig⟩
    have hvMark := majorMarkClosure_edge_closed s roots hInv huMark huOrig hEdge
    rcases hInv.validPtrs u objU v huOrig hEdge with ⟨objV, hvOrig⟩
    exact ⟨objV, sweepHeap_some_some_iff.mpr ⟨hvMark, hvOrig⟩⟩
  · intro u objU hu
    exact hInv.maskSound u objU (sweepHeap_some_some_iff.mp hu).2
  · intro u objU v hu _ hEdge hYoung
    rcases sweepHeap_some_some_iff.mp hu with ⟨huMark, huOrig⟩
    have hvMark := majorMarkClosure_edge_closed s roots hInv huMark huOrig hEdge
    simp only [majorGcCollect] at hYoung
    rw [hvMark] at hYoung
    cases hYoung

/-- **Full Major GC Preserves Exact Graph Reachability (`majorGc_reachable_iff`)**. -/
theorem majorGc_reachable_iff (s : GcState) (roots : List ObjId) (oid : ObjId)
    (hInv : GenHeapInv s) :
    Reachable (majorGcCollect s roots).heap roots oid ↔ Reachable s.heap roots oid := by
  constructor
  · exact reachable_of_sweepHeap
  · intro hReach
    induction hReach with
    | root hr hObj =>
      have hEq := majorGc_sound s roots _ hInv (Reachable.root hr hObj)
      exact Reachable.root hr (hEq.trans hObj)
    | step hReachU hObjU hEdge hObjV ih =>
      have hEqU := majorGc_sound s roots _ hInv hReachU
      have hEqV := majorGc_sound s roots _ hInv (Reachable.step hReachU hObjU hEdge hObjV)
      exact Reachable.step ih (hEqU.trans hObjU) hEdge (hEqV.trans hObjV)

end CoreGeisha

