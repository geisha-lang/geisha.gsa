import CoreGeisha.Syntax
import CoreGeisha.Typing
import CoreGeisha.Semantics
import CoreGeisha.Soundness
import CoreGeisha.Concurrency
import CoreGeisha.Exhaustive
import CoreGeisha.Escape
import CoreGeisha.GC

/-!
# Core Geisha: Unified Verified Executable Checker

An executable whole-program verifier `checkProgram` combining all 4 formal pillars
with machine-checked soundness proofs linking concrete `.gscore` Core IR programs
directly to:
1. `verified_program_safety` & `verified_concurrent_program_safety` (`¬ IsStuck` across `Task`s & `Actor`s)
2. `verified_program_no_match_failure` & `verified_concurrent_no_match_failure` (Maranget exhaustiveness eliminating `Trap.matchFailure`)
3. `verified_program_data_race_freedom` (`¬ HasDataRace pool` across `Task` / `MVar` / `Chan` / `!Send`-state `Actor`)
4. `verified_program_gc_mask_sound` (40-bit exact object pointer masks & scalar false-pointer immunity)
5. `verified_program_no_dangling_stack` & `verified_program_stack_simulates_heap` (stack-frame region safety & heap simulation)
-/

namespace CoreGeisha

/-! ## Decidable Mode/Type Equality & Subtyping with Soundness Proofs -/

def modeEq : Mode → Mode → Bool
  | .local, .local => true
  | .shared, .shared => true
  | _, _ => false

theorem modeEq_sound {m1 m2 : Mode} (h : modeEq m1 m2 = true) : m1 = m2 := by
  cases m1 <;> cases m2 <;> simp [modeEq] at h <;> rfl

def modeSub : Mode → Mode → Bool
  | .local, .local => true
  | .shared, .shared => true
  | .shared, .local => true
  | .local, .shared => false

theorem modeSub_sound {m1 m2 : Mode} (h : modeSub m1 m2 = true) : ModeSub m1 m2 := by
  cases m1 <;> cases m2 <;> simp [modeSub] at h <;> constructor

mutual
def tyEq : Ty → Ty → Bool
  | .void, .void => true
  | .int, .int => true
  | .int64, .int64 => true
  | .float, .float => true
  | .float32, .float32 => true
  | .bool, .bool => true
  | .char, .char => true
  | .str, .str => true
  | .ptr, .ptr => true
  | .scopedPtr, .scopedPtr => true
  | .arena, .arena => true
  | .foreignPtr, .foreignPtr => true
  | .atomicInt, .atomicInt => true
  | .tuple ts1, .tuple ts2 => tyListEq ts1 ts2
  | .fn m1 ps1 r1, .fn m2 ps2 r2 => modeEq m1 m2 && tyListEq ps1 ps2 && tyEq r1 r2
  | .adt n1, .adt n2 => n1 == n2
  | .simd128 s1, .simd128 s2 => s1 == s2
  | .simd256 s1, .simd256 s2 => s1 == s2
  | .cell t1, .cell t2 => tyEq t1 t2
  | .mutArray t1, .mutArray t2 => tyEq t1 t2
  | .immArray t1, .immArray t2 => tyEq t1 t2
  | .task t1, .task t2 => tyEq t1 t2
  | .mvar t1, .mvar t2 => tyEq t1 t2
  | .chan t1, .chan t2 => tyEq t1 t2
  | .actor t1, .actor t2 => tyEq t1 t2
  | _, _ => false

def tyListEq : List Ty → List Ty → Bool
  | [], [] => true
  | t1 :: ts1, t2 :: ts2 => tyEq t1 t2 && tyListEq ts1 ts2
  | _, _ => false
end

mutual
theorem tyEq_sound {t1 t2 : Ty} (h : tyEq t1 t2 = true) : t1 = t2 := by
  cases t1 <;> cases t2 <;> try cases h
  all_goals
    first
    | rfl
    | (simp only [tyEq, Bool.and_eq_true, beq_iff_eq] at h
       first
       | rw [h]
       | rw [tyEq_sound h]
       | rw [tyListEq_sound h]
       | rw [modeEq_sound h.1.1, tyListEq_sound h.1.2, tyEq_sound h.2])

theorem tyListEq_sound {ts1 ts2 : List Ty} (h : tyListEq ts1 ts2 = true) : ts1 = ts2 := by
  cases ts1 <;> cases ts2 <;> simp only [tyListEq] at h <;> try cases h
  · rfl
  · simp only [Bool.and_eq_true] at h
    rw [tyEq_sound h.1, tyListEq_sound h.2]
end

mutual
def tySub : Ty → Ty → Bool
  | .void, .void => true
  | .int, .int => true
  | .int64, .int64 => true
  | .float, .float => true
  | .float32, .float32 => true
  | .bool, .bool => true
  | .char, .char => true
  | .str, .str => true
  | .ptr, .ptr => true
  | .scopedPtr, .scopedPtr => true
  | .arena, .arena => true
  | .foreignPtr, .foreignPtr => true
  | .atomicInt, .atomicInt => true
  | .tuple ts1, .tuple ts2 => tyListSub ts1 ts2
  | .fn m1 ps1 r1, .fn m2 ps2 r2 =>
    modeSub m1 m2 && tyListSub ps2 ps1 && tySub r1 r2
  | .adt n1, .adt n2 => n1 == n2
  | .simd128 s1, .simd128 s2 => s1 == s2
  | .simd256 s1, .simd256 s2 => s1 == s2
  | .cell t1, .cell t2 => tyEq t1 t2
  | .mutArray t1, .mutArray t2 => tyEq t1 t2
  | .immArray t1, .immArray t2 => tySub t1 t2
  | .task t1, .task t2 => tySub t1 t2
  | .mvar t1, .mvar t2 => tyEq t1 t2
  | .chan t1, .chan t2 => tyEq t1 t2
  | .actor t1, .actor t2 => tyEq t1 t2
  | _, _ => false
termination_by t1 t2 => sizeOf t1 + sizeOf t2

def tyListSub : List Ty → List Ty → Bool
  | [], [] => true
  | t1 :: ts1, t2 :: ts2 => tySub t1 t2 && tyListSub ts1 ts2
  | _, _ => false
termination_by ts1 ts2 => sizeOf ts1 + sizeOf ts2
end

mutual
theorem tySub_sound {t1 t2 : Ty} (h : tySub t1 t2 = true) : TySub t1 t2 := by
  cases t1 <;> cases t2 <;> simp only [tySub] at h <;> try cases h
  · exact .void
  · exact .int
  · exact .int64
  · exact .float
  · exact .float32
  · exact .bool
  · exact .char
  · exact .str
  · exact .ptr
  · exact .scopedPtr
  · exact .arena
  · exact .foreignPtr
  · exact .atomicInt
  · exact .tuple (tyListSub_sound h)
  · simp only [Bool.and_eq_true] at h
    exact .fn (modeSub_sound h.1.1) (tyListSub_sound h.1.2) (tySub_sound h.2)
  · simp only [beq_iff_eq] at h; subst h; exact .adt _
  · simp only [beq_iff_eq] at h; subst h; exact .simd128 _
  · simp only [beq_iff_eq] at h; subst h; exact .simd256 _
  · rw [tyEq_sound h]; exact .cell _
  · rw [tyEq_sound h]; exact .mutArray _
  · exact .immArray (tySub_sound h)
  · exact .task (tySub_sound h)
  · rw [tyEq_sound h]; exact .mvar _
  · rw [tyEq_sound h]; exact .chan _
  · rw [tyEq_sound h]; exact .actor _
termination_by sizeOf t1 + sizeOf t2

theorem tyListSub_sound {ts1 ts2 : List Ty} (h : tyListSub ts1 ts2 = true) : TyListSub ts1 ts2 := by
  cases ts1 <;> cases ts2 <;> simp only [tyListSub] at h <;> try cases h
  · exact .nil
  · simp only [Bool.and_eq_true] at h
    exact .cons (tySub_sound h.1) (tyListSub_sound h.2)
termination_by sizeOf ts1 + sizeOf ts2
end

/-! ## Greatest-Fixed-Point `IsSend` Checker & Soundness Proof -/

mutual
def tySendInList (sendAdts : List Ident) : Ty → Bool
  | .void => true
  | .int => true
  | .int64 => true
  | .float => true
  | .float32 => true
  | .bool => true
  | .char => true
  | .str => true
  | .ptr => false
  | .scopedPtr => false
  | .arena => false
  | .foreignPtr => false
  | .atomicInt => true
  | .tuple ts => tyListSendInList sendAdts ts
  | .fn .shared _ _ => true
  | .fn .local _ _ => false
  | .adt n => sendAdts.contains n
  | .simd128 _ => true
  | .simd256 _ => true
  | .cell _ => false
  | .mutArray _ => false
  | .immArray t => tySendInList sendAdts t
  | .task t => tySendInList sendAdts t
  | .mvar t => tySendInList sendAdts t
  | .chan t => tySendInList sendAdts t
  | .actor _ => true

def tyListSendInList (sendAdts : List Ident) : List Ty → Bool
  | [] => true
  | t :: ts => tySendInList sendAdts t && tyListSendInList sendAdts ts
end

/-- Iterative pruning computing the greatest fixed point of `Send` ADTs. -/
def computeSendAdts (adts : List AdtDef) : List Ident :=
  let rec loop : Nat → List Ident → List Ident
    | 0, _ => []
    | n + 1, cand =>
      let cand' := cand.filter fun name =>
        match adts.find? (fun a => a.name == name) with
        | none => false
        | some defn => defn.variants.all (fun v => tyListSendInList cand v.fields)
      if cand'.length == cand.length then cand' else loop n cand'
  loop (adts.length + 1) (adts.map AdtDef.name)

/-- Certificate check verifying that `sendAdts` is a `Δ`-closed post-fixed point. -/
def checkSendAdtsClosed (Δ : AdtEnv) (sendAdts : List Ident) : Bool :=
  sendAdts.all fun name =>
    match Δ name with
    | none => false
    | some defn => defn.variants.all (fun v => tyListSendInList sendAdts v.fields)

mutual
theorem tySendInList_sound {sendAdts : List Ident} {τ : Ty}
    (h : tySendInList sendAdts τ = true) :
    TySendIn (fun n => n ∈ sendAdts) τ := by
  cases τ with
  | void => exact .void
  | int => exact .int
  | int64 => exact .int64
  | float => exact .float
  | float32 => exact .float32
  | bool => exact .bool
  | char => exact .char
  | str => exact .str
  | ptr => simp [tySendInList] at h
  | scopedPtr => simp [tySendInList] at h
  | arena => simp [tySendInList] at h
  | foreignPtr => simp [tySendInList] at h
  | atomicInt => exact .atomicInt
  | tuple ts => exact .tuple (tyListSendInList_sound h)
  | fn m ps r =>
    cases m
    · simp [tySendInList] at h
    · exact .fnShared ps r
  | adt n =>
    simp only [tySendInList] at h
    exact .adt (List.contains_iff_mem.mp h)
  | simd128 s => exact .simd128 s
  | simd256 s => exact .simd256 s
  | cell _ => simp [tySendInList] at h
  | mutArray _ => simp [tySendInList] at h
  | immArray t => exact .immArray (tySendInList_sound h)
  | task t => exact .task (tySendInList_sound h)
  | mvar t => exact .mvar (tySendInList_sound h)
  | chan t => exact .chan (tySendInList_sound h)
  | actor s => exact .actor s

theorem tyListSendInList_sound {sendAdts : List Ident} {ts : List Ty}
    (h : tyListSendInList sendAdts ts = true) :
    TyListSendIn (fun n => n ∈ sendAdts) ts := by
  cases ts with
  | nil => exact .nil
  | cons t ts =>
    simp only [tyListSendInList, Bool.and_eq_true] at h
    exact .cons (tySendInList_sound h.1) (tyListSendInList_sound h.2)
end

theorem checkSendAdtsClosed_sound {Δ : AdtEnv} {sendAdts : List Ident}
    (h : checkSendAdtsClosed Δ sendAdts = true) :
    AdtSendClosed Δ (fun n => n ∈ sendAdts) := by
  intro name hmem
  simp only [checkSendAdtsClosed, List.all_eq_true] at h
  have hn := h name hmem
  cases hΔ : Δ name with
  | none => simp [hΔ] at hn
  | some defn =>
    simp only [hΔ, List.all_eq_true] at hn
    exact ⟨defn, rfl, fun v hv => tyListSendInList_sound (hn v hv)⟩

theorem checkIsSend_sound {Δ : AdtEnv} {sendAdts : List Ident} {τ : Ty}
    (hcl : checkSendAdtsClosed Δ sendAdts = true)
    (ht : tySendInList sendAdts τ = true) :
    IsSend Δ τ :=
  ⟨fun n => n ∈ sendAdts, checkSendAdtsClosed_sound hcl, tySendInList_sound ht⟩

def checkSharedFvs (sendAdts : List Ident) (Γ : Ctx) : List Ident → Except String Unit
  | [] => .ok ()
  | x :: xs =>
    match Γ x with
    | none => .error s!"shared closure captures unbound variable '{x}'"
    | some τx =>
      if tySendInList sendAdts τx then
        checkSharedFvs sendAdts Γ xs
      else
        .error s!"shared closure captures non-Send variable '{x}' of type {repr τx}"

theorem checkSharedFvs_sound {Δ : AdtEnv} {sendAdts : List Ident} {Γ : Ctx} {fvs : List Ident}
    (hcl : checkSendAdtsClosed Δ sendAdts = true)
    (h : checkSharedFvs sendAdts Γ fvs = .ok ()) :
    ∀ x ∈ fvs, ∃ τx, Γ x = some τx ∧ IsSend Δ τx := by
  induction fvs with
  | nil => intro _ hm; cases hm
  | cons y ys ih =>
    simp only [checkSharedFvs] at h
    cases hy : Γ y with
    | none => simp [hy] at h
    | some τy =>
      simp only [hy] at h
      split at h
      · rename_i hsend
        intro x hx
        rcases List.mem_cons.mp hx with rfl | hrest
        · exact ⟨τy, hy, checkIsSend_sound hcl hsend⟩
        · exact ih h x hrest
      · cases h

/-! ## Concurrency Primitive (`MVar` / `Chan` / `Actor`) Checker & Soundness -/

def checkConcPrim (Δ : AdtEnv) (sendAdts : List Ident) (op : ConcPrim) (argTys : List Ty) :
    Except String (List Ty × Ty) :=
  match op, argTys with
  | .mvarNew, [τ] =>
    if tySendInList sendAdts τ then .ok ([τ], .mvar τ)
    else .error s!"mvarNew payload type {repr τ} is not Send"
  | .mvarEmpty τ, [] =>
    if tySendInList sendAdts τ then .ok ([], .mvar τ)
    else .error s!"mvarEmpty payload type {repr τ} is not Send"
  | .mvarTake, [.mvar τ] =>
    if tySendInList sendAdts τ then .ok ([.mvar τ], τ)
    else .error s!"mvarTake payload type {repr τ} is not Send"
  | .mvarPut, [.mvar τ, τv] =>
    if tySendInList sendAdts τ && tySub τv τ then .ok ([.mvar τ, τ], .void)
    else .error s!"mvarPut ill-typed for ({repr τ}, {repr τv})"
  | .chanNew τ, [.int] =>
    if tySendInList sendAdts τ then .ok ([.int], .chan τ)
    else .error s!"chanNew payload type {repr τ} is not Send"
  | .chanSend, [.chan τ, τv] =>
    if tySendInList sendAdts τ && tySub τv τ then .ok ([.chan τ, τ], .bool)
    else .error s!"chanSend ill-typed for ({repr τ}, {repr τv})"
  | .chanRecv optAdt, [.chan τ] =>
    match lookupVariant Δ optAdt 0, lookupVariant Δ optAdt 1 with
    | some [], some [τopt] =>
      if tyEq τ τopt && tySendInList sendAdts τ then
        .ok ([.chan τ], .adt optAdt)
      else .error s!"chanRecv Option type mismatch for {optAdt} vs {repr τ}"
    | _, _ => .error s!"chanRecv target ADT '{optAdt}' is not Option-shaped"
  | .chanClose, [.chan τ] =>
    .ok ([.chan τ], .void)
  | .actorSpawn, [.fn .shared [] σ_ty] =>
    .ok ([.fn .shared [] σ_ty], .actor σ_ty)
  | .actorCall, [.actor σ_ty, .fn .shared [p_ty] r_ty] =>
    if tySub σ_ty p_ty && tySendInList sendAdts r_ty then
      .ok ([.actor σ_ty, .fn .shared [σ_ty] r_ty], .task r_ty)
    else .error s!"actorCall ill-typed or non-Send reply {repr r_ty}"
  | .actorSend, [.actor σ_ty, .fn .shared [p_ty] .void] =>
    if tySub σ_ty p_ty then
      .ok ([.actor σ_ty, .fn .shared [σ_ty] .void], .void)
    else .error s!"actorSend handler parameter mismatch for actor state {repr σ_ty}"
  | _, _ => .error s!"concurrency primitive {repr op} ill-typed for arguments {repr argTys}"

theorem checkConcPrim_sound {Δ : AdtEnv} {sendAdts : List Ident}
    {op : ConcPrim} {argTys expectedTys : List Ty} {retTy : Ty}
    (hcl : checkSendAdtsClosed Δ sendAdts = true)
    (h : checkConcPrim Δ sendAdts op argTys = .ok (expectedTys, retTy)) :
    TyListSub argTys expectedTys ∧ ConcPrimHasType Δ op expectedTys retTy := by
  cases op with
  | mvarNew =>
    cases argTys with
    | nil => simp [checkConcPrim] at h
    | cons τ rest =>
      cases rest with
      | cons _ _ => simp [checkConcPrim] at h
      | nil =>
        simp only [checkConcPrim] at h
        split at h
        · rename_i hsend
          cases h
          exact ⟨TyListSub.refl _, .mvarNew (checkIsSend_sound hcl hsend)⟩
        · cases h
  | mvarEmpty τ =>
    cases argTys with
    | cons _ _ => simp [checkConcPrim] at h
    | nil =>
      simp only [checkConcPrim] at h
      split at h
      · rename_i hsend
        cases h
        exact ⟨.nil, .mvarEmpty (checkIsSend_sound hcl hsend)⟩
      · cases h
  | mvarTake =>
    cases argTys with
    | nil => simp [checkConcPrim] at h
    | cons a0 rest =>
      cases rest with
      | cons _ _ => simp [checkConcPrim] at h
      | nil =>
        cases a0 <;> simp only [checkConcPrim] at h <;> try cases h
        rename_i τ
        split at h
        · rename_i hsend
          cases h
          exact ⟨TyListSub.refl _, .mvarTake (checkIsSend_sound hcl hsend)⟩
        · cases h
  | mvarPut =>
    cases argTys with
    | nil => simp [checkConcPrim] at h
    | cons a0 r1 =>
      cases r1 with
      | nil => simp [checkConcPrim] at h
      | cons τv r2 =>
        cases r2 with
        | cons _ _ => simp [checkConcPrim] at h
        | nil =>
          cases a0 <;> simp only [checkConcPrim] at h <;> try cases h
          rename_i τ
          split at h
          · rename_i hcond
            simp only [Bool.and_eq_true] at hcond
            cases h
            exact ⟨.cons (.refl _) (.cons (tySub_sound hcond.2) .nil),
              .mvarPut (checkIsSend_sound hcl hcond.1)⟩
          · cases h
  | chanNew τ =>
    cases argTys with
    | nil => simp [checkConcPrim] at h
    | cons a0 rest =>
      cases rest with
      | cons _ _ => simp [checkConcPrim] at h
      | nil =>
        cases a0 <;> simp only [checkConcPrim] at h <;> try cases h
        split at h
        · rename_i hsend
          cases h
          exact ⟨TyListSub.refl _, .chanNew (checkIsSend_sound hcl hsend)⟩
        · cases h
  | chanSend =>
    cases argTys with
    | nil => simp [checkConcPrim] at h
    | cons a0 r1 =>
      cases r1 with
      | nil => simp [checkConcPrim] at h
      | cons τv r2 =>
        cases r2 with
        | cons _ _ => simp [checkConcPrim] at h
        | nil =>
          cases a0 <;> simp only [checkConcPrim] at h <;> try cases h
          rename_i τ
          split at h
          · rename_i hcond
            simp only [Bool.and_eq_true] at hcond
            cases h
            exact ⟨.cons (.refl _) (.cons (tySub_sound hcond.2) .nil),
              .chanSend (checkIsSend_sound hcl hcond.1)⟩
          · cases h
  | chanRecv optAdt =>
    cases argTys with
    | nil => simp [checkConcPrim] at h
    | cons a0 rest =>
      cases rest with
      | cons _ _ => simp [checkConcPrim] at h
      | nil =>
        cases a0 <;> simp only [checkConcPrim] at h <;> try cases h
        rename_i τ
        cases hv0 : lookupVariant Δ optAdt 0 with
        | none => simp [hv0] at h
        | some f0 =>
          cases f0 with
          | cons _ _ => simp [hv0] at h
          | nil =>
            cases hv1 : lookupVariant Δ optAdt 1 with
            | none => simp [hv0, hv1] at h
            | some f1 =>
              cases f1 with
              | nil => simp [hv0, hv1] at h
              | cons τopt f1rest =>
                cases f1rest with
                | cons _ _ => simp [hv0, hv1] at h
                | nil =>
                  simp only [hv0, hv1] at h
                  split at h
                  · rename_i hcond
                    simp only [Bool.and_eq_true] at hcond
                    have heq := tyEq_sound hcond.1
                    subst heq
                    cases h
                    exact ⟨TyListSub.refl _, .chanRecv (checkIsSend_sound hcl hcond.2) hv0 hv1⟩
                  · cases h
  | chanClose =>
    cases argTys with
    | nil => simp [checkConcPrim] at h
    | cons a0 rest =>
      cases rest with
      | cons _ _ => simp [checkConcPrim] at h
      | nil =>
        cases a0 <;> simp only [checkConcPrim] at h <;> try cases h
        exact ⟨TyListSub.refl _, .chanClose⟩
  | actorSpawn =>
    cases argTys with
    | nil => simp [checkConcPrim] at h
    | cons a0 rest =>
      cases rest with
      | cons _ _ => simp [checkConcPrim] at h
      | nil =>
        cases a0 <;> simp only [checkConcPrim] at h <;> try cases h
        rename_i m ps σ_ty
        cases m <;> cases ps <;> simp at h
        rcases h with ⟨rfl, rfl⟩
        exact ⟨TyListSub.refl _, .actorSpawn⟩
  | actorCall =>
    cases argTys with
    | nil => simp [checkConcPrim] at h
    | cons a0 r1 =>
      cases r1 with
      | nil => simp [checkConcPrim] at h
      | cons a1 r2 =>
        cases r2 with
        | cons _ _ => simp [checkConcPrim] at h
        | nil =>
          cases a0 <;> simp only [checkConcPrim] at h <;> try cases h
          rename_i σ_ty
          cases a1 <;> try cases h
          rename_i m ps r_ty
          cases m
          · cases h
          · cases ps with
            | nil => cases h
            | cons p_ty psRest =>
              cases psRest with
              | cons _ _ => cases h
              | nil =>
                dsimp only at h
                split at h
                · rename_i hcond
                  simp only [Bool.and_eq_true] at hcond
                  cases h
                  refine ⟨.cons (.refl _) (.cons (.fn (.refl .shared) (.cons (tySub_sound hcond.1) .nil) (.refl _)) .nil),
                    .actorCall (checkIsSend_sound hcl hcond.2)⟩
                · cases h
  | actorSend =>
    cases argTys with
    | nil => simp [checkConcPrim] at h
    | cons a0 r1 =>
      cases r1 with
      | nil => simp [checkConcPrim] at h
      | cons a1 r2 =>
        cases r2 with
        | cons _ _ => simp [checkConcPrim] at h
        | nil =>
          cases a0 <;> simp only [checkConcPrim] at h <;> try cases h
          rename_i σ_ty
          cases a1 <;> try cases h
          rename_i m ps r_ty
          cases m
          · cases h
          · cases ps with
            | nil => cases h
            | cons p_ty psRest =>
              cases psRest with
              | cons _ _ => cases h
              | nil =>
                cases r_ty <;> try cases h
                dsimp only at h
                split at h
                · rename_i hsub
                  cases h
                  exact ⟨.cons (.refl _) (.cons (.fn (.refl .shared) (.cons (tySub_sound hsub) .nil) .void) .nil),
                    .actorSend⟩
                · cases h

/-! ## Literal & Operator Checkers -/

def checkLit : Lit → Ty
  | .int _ => .int
  | .int64 _ => .int64
  | .floatBits _ => .float
  | .float32Bits _ => .float32
  | .bool _ => .bool
  | .char _ => .char
  | .str _ => .str
  | .unit => .void

theorem checkLit_sound (l : Lit) : LitHasType l (checkLit l) := by
  cases l <;> constructor

def unOpSig : UnOp → Ty × Ty
  | .not => (.bool, .bool)
  | .neg => (.int, .int)
  | .bitNot => (.int, .int)
  | .neg64 => (.int64, .int64)
  | .bitNot64 => (.int64, .int64)
  | .negFloat => (.float, .float)
  | .negFloat32 => (.float32, .float32)
  | .intToI64 => (.int, .int64)
  | .i64ToInt => (.int64, .int)

def checkUnOp (op : UnOp) (τ : Ty) : Except String Ty :=
  let (e1, τr) := unOpSig op
  if tyEq τ e1 then .ok τr
  else .error s!"unary operator {repr op} ill-typed for {repr τ}"

theorem checkUnOp_sound {op : UnOp} {τ1 τr : Ty} (h : checkUnOp op τ1 = .ok τr) :
    UnOpHasType op τ1 τr := by
  unfold checkUnOp at h
  dsimp only at h
  split at h
  · rename_i heq
    rw [tyEq_sound heq]
    cases h
    cases op <;> constructor
  · cases h

def binOpSig : BinOp → Ty × Ty × Ty
  | .add => (.int, .int, .int)
  | .sub => (.int, .int, .int)
  | .mul => (.int, .int, .int)
  | .div => (.int, .int, .int)
  | .rem => (.int, .int, .int)
  | .bitAnd => (.int, .int, .int)
  | .bitOr => (.int, .int, .int)
  | .bitXor => (.int, .int, .int)
  | .shlInt => (.int, .int, .int)
  | .shrInt => (.int, .int, .int)
  | .ushrInt => (.int, .int, .int)
  | .eqInt => (.int, .int, .bool)
  | .neInt => (.int, .int, .bool)
  | .ltInt => (.int, .int, .bool)
  | .leInt => (.int, .int, .bool)
  | .gtInt => (.int, .int, .bool)
  | .geInt => (.int, .int, .bool)
  | .add64 => (.int64, .int64, .int64)
  | .sub64 => (.int64, .int64, .int64)
  | .mul64 => (.int64, .int64, .int64)
  | .div64 => (.int64, .int64, .int64)
  | .rem64 => (.int64, .int64, .int64)
  | .bitAnd64 => (.int64, .int64, .int64)
  | .bitOr64 => (.int64, .int64, .int64)
  | .bitXor64 => (.int64, .int64, .int64)
  | .shl64 => (.int64, .int, .int64)
  | .shr64 => (.int64, .int, .int64)
  | .ushr64 => (.int64, .int, .int64)
  | .eq64 => (.int64, .int64, .bool)
  | .ne64 => (.int64, .int64, .bool)
  | .lt64 => (.int64, .int64, .bool)
  | .le64 => (.int64, .int64, .bool)
  | .gt64 => (.int64, .int64, .bool)
  | .ge64 => (.int64, .int64, .bool)
  | .addFloat => (.float, .float, .float)
  | .subFloat => (.float, .float, .float)
  | .mulFloat => (.float, .float, .float)
  | .divFloat => (.float, .float, .float)
  | .eqFloat => (.float, .float, .bool)
  | .neFloat => (.float, .float, .bool)
  | .ltFloat => (.float, .float, .bool)
  | .leFloat => (.float, .float, .bool)
  | .gtFloat => (.float, .float, .bool)
  | .geFloat => (.float, .float, .bool)
  | .addF32 => (.float32, .float32, .float32)
  | .subF32 => (.float32, .float32, .float32)
  | .mulF32 => (.float32, .float32, .float32)
  | .divF32 => (.float32, .float32, .float32)
  | .eqF32 => (.float32, .float32, .bool)
  | .neF32 => (.float32, .float32, .bool)
  | .ltF32 => (.float32, .float32, .bool)
  | .leF32 => (.float32, .float32, .bool)
  | .gtF32 => (.float32, .float32, .bool)
  | .geF32 => (.float32, .float32, .bool)
  | .eqBool => (.bool, .bool, .bool)
  | .neBool => (.bool, .bool, .bool)
  | .bitAndBool => (.bool, .bool, .bool)
  | .bitOrBool => (.bool, .bool, .bool)
  | .bitXorBool => (.bool, .bool, .bool)
  | .eqChar => (.char, .char, .bool)
  | .neChar => (.char, .char, .bool)
  | .ltChar => (.char, .char, .bool)
  | .leChar => (.char, .char, .bool)
  | .gtChar => (.char, .char, .bool)
  | .geChar => (.char, .char, .bool)
  | .eqStr => (.str, .str, .bool)
  | .neStr => (.str, .str, .bool)
  | .ltStr => (.str, .str, .bool)
  | .leStr => (.str, .str, .bool)
  | .gtStr => (.str, .str, .bool)
  | .geStr => (.str, .str, .bool)
  | .strConcat => (.str, .str, .str)
  | .and => (.bool, .bool, .bool)
  | .or => (.bool, .bool, .bool)

def checkBinOp (op : BinOp) (τ1 τ2 : Ty) : Except String Ty :=
  let (e1, e2, τr) := binOpSig op
  if tyEq τ1 e1 && tyEq τ2 e2 then .ok τr
  else .error s!"binary operator {repr op} ill-typed for ({repr τ1}, {repr τ2})"

theorem checkBinOp_sound {op : BinOp} {τ1 τ2 τr : Ty} (h : checkBinOp op τ1 τ2 = .ok τr) :
    BinOpHasType op τ1 τ2 τr := by
  unfold checkBinOp at h
  dsimp only at h
  split at h
  · rename_i hcond
    simp only [Bool.and_eq_true] at hcond
    rw [tyEq_sound hcond.1, tyEq_sound hcond.2]
    cases h
    cases op <;> constructor
  · cases h

/-! ## Pattern Type Checker -/

mutual
def checkPat (Δ : AdtEnv) : Pat → Ty → Except String (List (Ident × Ty))
  | .wild, _ => .ok []
  | .var x, τ => .ok [(x, τ)]
  | .lit l, τ =>
    if tyEq (checkLit l) τ then .ok []
    else .error s!"literal pattern type mismatch: expected {repr τ}"
  | .tuple ps, .tuple τs => checkPats Δ ps τs
  | .tuple _, τ => .error s!"tuple pattern against non-tuple type {repr τ}"
  | .ctor adt tag ps, .adt adt' =>
    if adt == adt' then
      match lookupVariant Δ adt tag with
      | some flds => checkPats Δ ps flds
      | none => .error s!"unknown variant tag {tag} for ADT {adt}"
    else .error s!"constructor ADT mismatch: {adt} vs {adt'}"
  | .ctor adt _ _, τ => .error s!"constructor {adt} against non-ADT type {repr τ}"

def checkPats (Δ : AdtEnv) : List Pat → List Ty → Except String (List (Ident × Ty))
  | [], [] => .ok []
  | p :: ps, τ :: τs =>
    match checkPat Δ p τ with
    | .error e => .error e
    | .ok b1 =>
      match checkPats Δ ps τs with
      | .error e => .error e
      | .ok b2 => .ok (b1 ++ b2)
  | _, _ => .error "pattern arity mismatch"
end

mutual
theorem checkPat_sound {Δ : AdtEnv} {p : Pat} {τ : Ty} {bs : List (Ident × Ty)}
    (h : checkPat Δ p τ = .ok bs) : PatHasType Δ p τ bs := by
  cases p with
  | wild => simp [checkPat] at h; subst h; exact .wild τ
  | var x => simp [checkPat] at h; subst h; exact .var x τ
  | lit l =>
    simp only [checkPat] at h
    split at h
    · rename_i heq
      cases h
      rw [← tyEq_sound heq]
      exact .lit (checkLit_sound l)
    · cases h
  | tuple ps =>
    cases τ <;> simp only [checkPat] at h <;> try cases h
    exact .tuple (checkPats_sound h)
  | ctor adt tag ps =>
    cases τ <;> simp only [checkPat] at h <;> try cases h
    rename_i adt'
    split at h
    · rename_i heq
      simp only [beq_iff_eq] at heq
      subst heq
      cases hlv : lookupVariant Δ adt tag with
      | none => simp only [hlv] at h; cases h
      | some flds =>
        simp only [hlv] at h
        exact .ctor hlv (checkPats_sound h)
    · cases h

theorem checkPats_sound {Δ : AdtEnv} {ps : List Pat} {τs : List Ty} {bs : List (Ident × Ty)}
    (h : checkPats Δ ps τs = .ok bs) : PatsHaveType Δ ps τs bs := by
  cases ps <;> cases τs <;> simp only [checkPats] at h <;> try cases h
  · exact .nil
  · rename_i p ps τ τs
    cases h1 : checkPat Δ p τ with
    | error e => simp only [h1] at h; cases h
    | ok b1 =>
      simp only [h1] at h
      cases h2 : checkPats Δ ps τs with
      | error e => simp only [h2] at h; cases h
      | ok b2 =>
        simp only [h2] at h
        cases h
        exact .cons (checkPat_sound h1) (checkPats_sound h2)
end

/-! ## Expression Type Checker -/

mutual
def checkExpr (Δ : AdtEnv) (Φ : FunEnv) (sendAdts : List Ident) (Γ : Ctx) :
    Expr → Except String Ty
  | .lit l => .ok (checkLit l)
  | .var x =>
    match Γ x with
    | some τ => .ok τ
    | none => .error s!"unbound variable '{x}'"
  | .loc l => .error s!"runtime location #{l} not allowed in static Core IR"
  | .taskRef tid => .error s!"runtime taskRef #{tid} not allowed in static Core IR"
  | .syncRef k id => .error s!"runtime syncRef {repr k}#{id} not allowed in static Core IR"
  | .tuple es =>
    match checkExprList Δ Φ sendAdts Γ es with
    | .ok τs => .ok (.tuple τs)
    | .error e => .error e
  | .block [] => .ok .void
  | .block [e] => checkExpr Δ Φ sendAdts Γ e
  | .block (e1 :: e2 :: es) =>
    match checkExpr Δ Φ sendAdts Γ e1 with
    | .error err => .error err
    | .ok _ => checkExpr Δ Φ sendAdts Γ (.block (e2 :: es))
  | .lam m ps ret body =>
    match checkExpr Δ Φ sendAdts (extendMany Γ ps) body with
    | .error err => .error err
    | .ok τb =>
      if tySub τb ret then
        match m with
        | .local => .ok (.fn .local (ps.map Prod.snd) ret)
        | .shared =>
          match checkSharedFvs sendAdts Γ (freeVars (.lam .shared ps ret body)) with
          | .error err => .error err
          | .ok () => .ok (.fn .shared (ps.map Prod.snd) ret)
      else .error s!"lambda return type mismatch: expected {repr ret}, got {repr τb}"
  | .apply fn args =>
    match checkExpr Δ Φ sendAdts Γ fn with
    | .error err => .error err
    | .ok (.fn _ paramTys ret) =>
      match checkExprList Δ Φ sendAdts Γ args with
      | .error err => .error err
      | .ok argTys =>
        if tyListSub argTys paramTys then .ok ret
        else .error s!"closure call argument mismatch: expected {repr paramTys}, got {repr argTys}"
    | .ok other => .error s!"calling non-function value of type {repr other}"
  | .applyDir name args =>
    match Φ name with
    | none => .error s!"unknown direct-call function '{name}'"
    | some fd =>
      match checkExprList Δ Φ sendAdts Γ args with
      | .error err => .error err
      | .ok argTys =>
        if tyListSub argTys (fd.params.map Prod.snd) then .ok fd.retTy
        else .error s!"direct call '{name}' argument mismatch: expected {repr (fd.params.map Prod.snd)}, got {repr argTys}"
  | .bin op e1 e2 =>
    match checkExpr Δ Φ sendAdts Γ e1 with
    | .error err => .error err
    | .ok τ1 =>
      match checkExpr Δ Φ sendAdts Γ e2 with
      | .error err => .error err
      | .ok τ2 => checkBinOp op τ1 τ2
  | .un op e =>
    match checkExpr Δ Φ sendAdts Γ e with
    | .error err => .error err
    | .ok τ1 => checkUnOp op τ1
  | .let_ x e1 e2 =>
    match checkExpr Δ Φ sendAdts Γ e1 with
    | .error err => .error err
    | .ok τ1 => checkExpr Δ Φ sendAdts (extendCtx Γ x τ1) e2
  | .if_ c t e =>
    match checkExpr Δ Φ sendAdts Γ c with
    | .error err => .error err
    | .ok .bool =>
      match checkExpr Δ Φ sendAdts Γ t with
      | .error err => .error err
      | .ok τt =>
        match checkExpr Δ Φ sendAdts Γ e with
        | .error err => .error err
        | .ok τe =>
          if tySub τt τe then .ok τe
          else if tySub τe τt then .ok τt
          else .error s!"if branch mismatch: {repr τt} vs {repr τe}"
    | .ok other => .error s!"if condition must be Bool, got {repr other}"
  | .while_ c b =>
    match checkExpr Δ Φ sendAdts Γ c with
    | .error err => .error err
    | .ok .bool =>
      match checkExpr Δ Φ sendAdts Γ b with
      | .error err => .error err
      | .ok _ => .ok .void
    | .ok other => .error s!"while condition must be Bool, got {repr other}"
  | .match_ scrut arms =>
    match checkExpr Δ Φ sendAdts Γ scrut with
    | .error err => .error err
    | .ok τs =>
      match arms with
      | [] => .error "empty match expression"
      | (p, body) :: rest =>
        match checkPat Δ p τs with
        | .error err => .error err
        | .ok bs =>
          match checkExpr Δ Φ sendAdts (extendMany Γ bs) body with
          | .error err => .error err
          | .ok τr =>
            match checkArms Δ Φ sendAdts Γ τs τr rest with
            | .error err => .error err
            | .ok () => .ok τr
  | .makeData adt tag es =>
    match lookupVariant Δ adt tag with
    | none => .error s!"unknown variant {adt}#{tag}"
    | some flds =>
      match checkExprList Δ Φ sendAdts Γ es with
      | .error err => .error err
      | .ok argTys =>
        if tyListSub argTys flds then .ok (.adt adt)
        else .error s!"constructor {adt}#{tag} field mismatch: expected {repr flds}, got {repr argTys}"
  | .getTag e =>
    match checkExpr Δ Φ sendAdts Γ e with
    | .error err => .error err
    | .ok (.adt _) => .ok .int
    | .ok other => .error s!"getTag expects ADT, got {repr other}"
  | .cellNew e =>
    match checkExpr Δ Φ sendAdts Γ e with
    | .error err => .error err
    | .ok τ => .ok (.cell τ)
  | .cellGet e =>
    match checkExpr Δ Φ sendAdts Γ e with
    | .error err => .error err
    | .ok (.cell τ) => .ok τ
    | .ok other => .error s!"cellGet expects Cell, got {repr other}"
  | .cellSet e1 e2 =>
    match checkExpr Δ Φ sendAdts Γ e1 with
    | .error err => .error err
    | .ok (.cell τ) =>
      match checkExpr Δ Φ sendAdts Γ e2 with
      | .error err => .error err
      | .ok τ2 =>
        if tySub τ2 τ then .ok .void
        else .error s!"cellSet type mismatch: expected {repr τ}, got {repr τ2}"
    | .ok other => .error s!"cellSet expects Cell, got {repr other}"
  | .spawn fn =>
    match checkExpr Δ Φ sendAdts Γ fn with
    | .error err => .error err
    | .ok (.fn .shared [] τ) =>
      if tySendInList sendAdts τ then .ok (.task τ)
      else .error s!"spawn return type {repr τ} is not Send"
    | .ok (.fn .local _ _) =>
      .error "cannot spawn a 'local' closure (captures non-Send thread-local state)"
    | .ok other => .error s!"spawn expects 0-arg shared function, got {repr other}"
  | .await e =>
    match checkExpr Δ Φ sendAdts Γ e with
    | .error err => .error err
    | .ok (.task τ) =>
      if tySendInList sendAdts τ then .ok τ
      else .error s!"await task payload type {repr τ} is not Send"
    | .ok other => .error s!"await expects Task, got {repr other}"
  | .concPrim op args =>
    match checkExprList Δ Φ sendAdts Γ args with
    | .error err => .error err
    | .ok argTys =>
      match checkConcPrim Δ sendAdts op argTys with
      | .error err => .error err
      | .ok (_, retTy) => .ok retTy
  | .trap t => .error s!"runtime trap {repr t} not allowed in static Core IR"

def checkExprList (Δ : AdtEnv) (Φ : FunEnv) (sendAdts : List Ident) (Γ : Ctx) :
    List Expr → Except String (List Ty)
  | [] => .ok []
  | e :: es =>
    match checkExpr Δ Φ sendAdts Γ e with
    | .error err => .error err
    | .ok τ =>
      match checkExprList Δ Φ sendAdts Γ es with
      | .error err => .error err
      | .ok τs => .ok (τ :: τs)

def checkArms (Δ : AdtEnv) (Φ : FunEnv) (sendAdts : List Ident) (Γ : Ctx) (τs τr : Ty) :
    List (Pat × Expr) → Except String Unit
  | [] => .ok ()
  | (p, body) :: rest =>
    match checkPat Δ p τs with
    | .error err => .error err
    | .ok bs =>
      match checkExpr Δ Φ sendAdts (extendMany Γ bs) body with
      | .error err => .error err
      | .ok τb =>
        if tySub τb τr then checkArms Δ Φ sendAdts Γ τs τr rest
        else .error s!"match arm type mismatch: expected {repr τr}, got {repr τb}"
end

/-! ## Soundness Proof of Executable Type Checker -/

mutual
theorem checkExpr_sound {Δ : AdtEnv} {Φ : FunEnv} {sendAdts : List Ident} {Γ : Ctx}
    {e : Expr} {τ : Ty}
    (hcl : checkSendAdtsClosed Δ sendAdts = true)
    (h : checkExpr Δ Φ sendAdts Γ e = .ok τ) : HasType Δ Φ [] emptyTaskTy Γ e τ := by
  cases e with
  | lit l =>
    simp only [checkExpr, Except.ok.injEq] at h
    subst h; exact .lit (checkLit_sound l)
  | var x =>
    simp only [checkExpr] at h
    cases hx : Γ x with
    | none => simp only [hx] at h; cases h
    | some τ0 => simp only [hx] at h; cases h; exact .var hx (TySub.refl _)
  | loc _ => simp [checkExpr] at h
  | taskRef _ => simp [checkExpr] at h
  | syncRef _ _ => simp [checkExpr] at h
  | tuple es =>
    simp only [checkExpr] at h
    cases hts : checkExprList Δ Φ sendAdts Γ es with
    | error _ => simp only [hts] at h; cases h
    | ok τs => simp only [hts] at h; cases h; exact .tuple (checkExprList_sound hcl hts)
  | block es =>
    cases es with
    | nil => simp only [checkExpr, Except.ok.injEq] at h; subst h; exact .blockEmpty
    | cons e1 rest =>
      cases rest with
      | nil =>
        simp only [checkExpr] at h
        exact .blockSingle (checkExpr_sound hcl h)
      | cons e2 tail =>
        simp only [checkExpr] at h
        cases h1 : checkExpr Δ Φ sendAdts Γ e1 with
        | error _ => simp only [h1] at h; cases h
        | ok τ1 =>
          simp only [h1] at h
          exact .blockCons (checkExpr_sound hcl h1) (checkExpr_sound hcl h)
  | lam m ps ret body =>
    unfold checkExpr at h
    cases hb : checkExpr Δ Φ sendAdts (extendMany Γ ps) body with
    | error _ => rw [hb] at h; cases h
    | ok τb =>
      rw [hb] at h
      dsimp only at h
      split at h
      · rename_i hsub
        have hbody0 := checkExpr_sound hcl hb
        have hbody : HasType Δ Φ [] emptyTaskTy (extendMany Γ ps) body ret :=
          typing_sub (tySub_sound hsub) hbody0
        cases m
        · dsimp only at h
          cases h
          exact .lam (.refl .local) (TyListSub.refl _) (TySub.refl _) hbody (fun hm => by cases hm)
        · dsimp only at h
          cases hfv : checkSharedFvs sendAdts Γ (freeVars (.lam .shared ps ret body)) with
          | error _ => rw [hfv] at h; cases h
          | ok u =>
            cases u
            rw [hfv] at h
            dsimp only at h
            cases h
            exact .lam (.refl .shared) (TyListSub.refl _) (TySub.refl _) hbody
              (fun _ => ⟨checkSharedFvs_sound hcl hfv, exprLocs_empty_of_empty_store hbody⟩)
      · cases h
  | apply fn args =>
    simp only [checkExpr] at h
    cases hfn : checkExpr Δ Φ sendAdts Γ fn with
    | error _ => simp only [hfn] at h; cases h
    | ok τfn =>
      simp only [hfn] at h
      cases τfn <;> try cases h
      rename_i m paramTys ret
      cases hargs : checkExprList Δ Φ sendAdts Γ args with
      | error _ => simp only [hargs] at h; cases h
      | ok argTys =>
        simp only [hargs] at h
        split at h
        · rename_i hsub
          cases h
          exact .apply (checkExpr_sound hcl hfn)
            (typingList_sub (tyListSub_sound hsub) (checkExprList_sound hcl hargs))
            (TySub.refl _)
        · cases h
  | applyDir name args =>
    simp only [checkExpr] at h
    cases hf : Φ name with
    | none => simp only [hf] at h; cases h
    | some fd =>
      simp only [hf] at h
      cases hargs : checkExprList Δ Φ sendAdts Γ args with
      | error _ => simp only [hargs] at h; cases h
      | ok argTys =>
        simp only [hargs] at h
        split at h
        · rename_i hsub
          cases h
          exact .applyDir hf
            (typingList_sub (tyListSub_sound hsub) (checkExprList_sound hcl hargs))
            (TySub.refl _)
        · cases h
  | bin op e1 e2 =>
    simp only [checkExpr] at h
    cases h1 : checkExpr Δ Φ sendAdts Γ e1 with
    | error _ => simp only [h1] at h; cases h
    | ok τ1 =>
      simp only [h1] at h
      cases h2 : checkExpr Δ Φ sendAdts Γ e2 with
      | error _ => simp only [h2] at h; cases h
      | ok τ2 =>
        simp only [h2] at h
        exact .bin (checkBinOp_sound h) (checkExpr_sound hcl h1) (checkExpr_sound hcl h2)
  | un op e1 =>
    simp only [checkExpr] at h
    cases h1 : checkExpr Δ Φ sendAdts Γ e1 with
    | error _ => simp only [h1] at h; cases h
    | ok τ1 =>
      simp only [h1] at h
      exact .un (checkUnOp_sound h) (checkExpr_sound hcl h1)
  | let_ x e1 e2 =>
    simp only [checkExpr] at h
    cases h1 : checkExpr Δ Φ sendAdts Γ e1 with
    | error _ => simp only [h1] at h; cases h
    | ok τ1 =>
      simp only [h1] at h
      exact .let_ (checkExpr_sound hcl h1) (checkExpr_sound hcl h)
  | if_ c t e2 =>
    simp only [checkExpr] at h
    cases hc : checkExpr Δ Φ sendAdts Γ c with
    | error _ => simp only [hc] at h; cases h
    | ok τc =>
      simp only [hc] at h
      cases τc <;> try cases h
      cases ht : checkExpr Δ Φ sendAdts Γ t with
      | error _ => simp only [ht] at h; cases h
      | ok τt =>
        simp only [ht] at h
        cases he : checkExpr Δ Φ sendAdts Γ e2 with
        | error _ => simp only [he] at h; cases h
        | ok τe =>
          simp only [he] at h
          split at h
          · rename_i hsub1
            cases h
            exact .if_ (checkExpr_sound hcl hc)
              (typing_sub (tySub_sound hsub1) (checkExpr_sound hcl ht))
              (checkExpr_sound hcl he)
          · split at h
            · rename_i hsub2
              cases h
              exact .if_ (checkExpr_sound hcl hc)
                (checkExpr_sound hcl ht)
                (typing_sub (tySub_sound hsub2) (checkExpr_sound hcl he))
            · cases h
  | while_ c b =>
    simp only [checkExpr] at h
    cases hc : checkExpr Δ Φ sendAdts Γ c with
    | error _ => simp only [hc] at h; cases h
    | ok τc =>
      simp only [hc] at h
      cases τc <;> try cases h
      cases hb : checkExpr Δ Φ sendAdts Γ b with
      | error _ => simp only [hb] at h; cases h
      | ok τb =>
        simp only [hb] at h; cases h
        exact .while_ (checkExpr_sound hcl hc) (checkExpr_sound hcl hb)
  | match_ scrut arms =>
    simp only [checkExpr] at h
    cases hs : checkExpr Δ Φ sendAdts Γ scrut with
    | error _ => simp only [hs] at h; cases h
    | ok τs =>
      simp only [hs] at h
      cases arms with
      | nil => cases h
      | cons arm rest =>
        cases arm with
        | mk p body =>
          cases hp : checkPat Δ p τs with
          | error _ => simp only [hp] at h; cases h
          | ok bs =>
            simp only [hp] at h
            cases hb : checkExpr Δ Φ sendAdts (extendMany Γ bs) body with
            | error _ => simp only [hb] at h; cases h
            | ok τr =>
              simp only [hb] at h
              cases hr : checkArms Δ Φ sendAdts Γ τs τr rest with
              | error _ => simp only [hr] at h; cases h
              | ok u =>
                simp only [hr] at h; cases h
                exact .match_ (checkExpr_sound hcl hs)
                  (.cons (checkPat_sound hp) (checkExpr_sound hcl hb) (checkArms_sound hcl hr))
  | makeData adt tag es =>
    simp only [checkExpr] at h
    cases hlv : lookupVariant Δ adt tag with
    | none => simp only [hlv] at h; cases h
    | some flds =>
      simp only [hlv] at h
      cases hes : checkExprList Δ Φ sendAdts Γ es with
      | error _ => simp only [hes] at h; cases h
      | ok argTys =>
        simp only [hes] at h
        split at h
        · rename_i hsub
          cases h
          exact .makeData hlv (typingList_sub (tyListSub_sound hsub) (checkExprList_sound hcl hes))
        · cases h
  | getTag e1 =>
    simp only [checkExpr] at h
    cases h1 : checkExpr Δ Φ sendAdts Γ e1 with
    | error _ => simp only [h1] at h; cases h
    | ok τ1 =>
      simp only [h1] at h
      cases τ1 <;> try cases h
      exact .getTag (checkExpr_sound hcl h1)
  | cellNew e1 =>
    simp only [checkExpr] at h
    cases h1 : checkExpr Δ Φ sendAdts Γ e1 with
    | error _ => simp only [h1] at h; cases h
    | ok τ1 => simp only [h1] at h; cases h; exact .cellNew (checkExpr_sound hcl h1)
  | cellGet e1 =>
    simp only [checkExpr] at h
    cases h1 : checkExpr Δ Φ sendAdts Γ e1 with
    | error _ => simp only [h1] at h; cases h
    | ok τ1 =>
      simp only [h1] at h
      cases τ1 <;> try cases h
      exact .cellGet (checkExpr_sound hcl h1) (TySub.refl _)
  | cellSet e1 e2 =>
    simp only [checkExpr] at h
    cases h1 : checkExpr Δ Φ sendAdts Γ e1 with
    | error _ => simp only [h1] at h; cases h
    | ok τ1 =>
      simp only [h1] at h
      cases τ1 <;> try cases h
      rename_i τelem
      cases h2 : checkExpr Δ Φ sendAdts Γ e2 with
      | error _ => simp only [h2] at h; cases h
      | ok τ2 =>
        simp only [h2] at h
        split at h
        · rename_i hsub
          cases h
          exact .cellSet (checkExpr_sound hcl h1) (typing_sub (tySub_sound hsub) (checkExpr_sound hcl h2))
        · cases h
  | spawn fn =>
    unfold checkExpr at h
    cases hfn : checkExpr Δ Φ sendAdts Γ fn with
    | error _ => rw [hfn] at h; cases h
    | ok τfn =>
      cases τfn <;> (try rw [hfn] at h; cases h)
      rename_i m ps τret
      cases m
      · rw [hfn] at h; cases h
      · cases ps
        · rw [hfn] at h
          dsimp only at h
          split at h
          · rename_i hsend
            cases h
            exact .spawn (checkExpr_sound hcl hfn) (checkIsSend_sound hcl hsend) (TySub.refl _)
          · cases h
        · rw [hfn] at h; cases h
  | await e1 =>
    unfold checkExpr at h
    cases h1 : checkExpr Δ Φ sendAdts Γ e1 with
    | error _ => rw [h1] at h; cases h
    | ok τ1 =>
      cases τ1 <;> (try rw [h1] at h; cases h)
      rename_i τret
      rw [h1] at h
      dsimp only at h
      split at h
      · rename_i hsend
        cases h
        exact .await (checkExpr_sound hcl h1) (checkIsSend_sound hcl hsend) (TySub.refl _)
      · cases h
  | concPrim op args =>
    unfold checkExpr at h
    cases hargs : checkExprList Δ Φ sendAdts Γ args with
    | error _ => rw [hargs] at h; cases h
    | ok argTys =>
      rw [hargs] at h
      dsimp only at h
      cases hcp : checkConcPrim Δ sendAdts op argTys with
      | error _ => rw [hcp] at h; cases h
      | ok pair =>
        rcases pair with ⟨expectedTys, retTy⟩
        rw [hcp] at h
        dsimp only at h
        cases h
        rcases checkConcPrim_sound hcl hcp with ⟨hsub, hprim⟩
        exact .concPrim hprim (typingList_sub hsub (checkExprList_sound hcl hargs)) (TySub.refl _)
  | trap _ => simp [checkExpr] at h
termination_by sizeOf e

theorem checkExprList_sound {Δ : AdtEnv} {Φ : FunEnv} {sendAdts : List Ident} {Γ : Ctx}
    {es : List Expr} {τs : List Ty}
    (hcl : checkSendAdtsClosed Δ sendAdts = true)
    (h : checkExprList Δ Φ sendAdts Γ es = .ok τs) : HasTypes Δ Φ [] emptyTaskTy Γ es τs := by
  cases es with
  | nil => simp only [checkExprList, Except.ok.injEq] at h; subst h; exact .nil
  | cons e rest =>
    simp only [checkExprList] at h
    cases h1 : checkExpr Δ Φ sendAdts Γ e with
    | error _ => simp only [h1] at h; cases h
    | ok τ =>
      simp only [h1] at h
      cases h2 : checkExprList Δ Φ sendAdts Γ rest with
      | error _ => simp only [h2] at h; cases h
      | ok τs' =>
        simp only [h2] at h; cases h
        exact .cons (checkExpr_sound hcl h1) (checkExprList_sound hcl h2)
termination_by sizeOf es

theorem checkArms_sound {Δ : AdtEnv} {Φ : FunEnv} {sendAdts : List Ident} {Γ : Ctx} {τs τr : Ty}
    {arms : List (Pat × Expr)}
    (hcl : checkSendAdtsClosed Δ sendAdts = true)
    (h : checkArms Δ Φ sendAdts Γ τs τr arms = .ok ()) : ArmsHaveType Δ Φ [] emptyTaskTy Γ τs arms τr := by
  cases arms with
  | nil => exact .nil
  | cons arm rest =>
    cases arm with
    | mk p body =>
      simp only [checkArms] at h
      cases hp : checkPat Δ p τs with
      | error _ => simp only [hp] at h; cases h
      | ok bs =>
        simp only [hp] at h
        cases hb : checkExpr Δ Φ sendAdts (extendMany Γ bs) body with
        | error _ => simp only [hb] at h; cases h
        | ok τb =>
          simp only [hb] at h
          split at h
          · rename_i hsub
            exact .cons (checkPat_sound hp)
              (typing_sub (tySub_sound hsub) (checkExpr_sound hcl hb))
              (checkArms_sound hcl h)
          · cases h
termination_by sizeOf arms
end

/-! ## Whole-Program Verifier & Unified Safety Theorems -/

/-- A concrete Core Geisha program as exported by `geisha.gsa --dump-core`. -/
structure Program where
  adts        : List AdtDef
  funs        : List FunDef
  externs     : List ExternDecl := []
  stackAllocs : List FnStackSpec := []
  gcMasks     : List AdtGcMaskSpec := []
  hasGcMasks  : Bool := false
  deriving Repr

def Program.allFuns (p : Program) : List FunDef :=
  p.funs ++ p.externs.map ExternDecl.toFunDef

def Program.toAdtEnv (p : Program) : AdtEnv :=
  fun name => p.adts.find? (fun a => a.name == name)

def Program.toFunEnv (p : Program) : FunEnv :=
  fun name => p.allFuns.find? (fun f => f.name == name)

def checkFunDef (Δ : AdtEnv) (Φ : FunEnv) (sendAdts : List Ident) (fd : FunDef) :
    Except String Unit :=
  match checkExpr Δ Φ sendAdts (extendMany emptyCtx fd.params) fd.body with
  | .error err => .error s!"in function '{fd.name}': {err}"
  | .ok τb =>
    if tySub τb fd.retTy then .ok ()
    else .error s!"in function '{fd.name}': body type {repr τb} </: declared return type {repr fd.retTy}"

def checkFunList (Δ : AdtEnv) (Φ : FunEnv) (sendAdts : List Ident) :
    List FunDef → Except String Unit
  | [] => .ok ()
  | fd :: rest =>
    match checkFunDef Δ Φ sendAdts fd with
    | .error err => .error err
    | .ok () => checkFunList Δ Φ sendAdts rest

/-- Whole-program verifier checking:
    1. Types, closure capture modes (`local`/`shared`), host `extern` boundaries, and `Task`/`MVar`/`Chan`/`Actor` concurrency
    2. Maranget pattern-matrix exhaustiveness (`checkProgramExhaustive`)
    3. Intraprocedural & frame stack-allocation escape safety (`checkProgramEscape`)
    4. Exact 40-bit GC pointer-mask layouts (`checkProgramGcLayouts`) -/
def checkProgram (prog : Program) : Except String Unit :=
  let Δ := prog.toAdtEnv
  let Φ := prog.toFunEnv
  let sendAdts := computeSendAdts prog.adts
  if checkSendAdtsClosed Δ sendAdts then
    match checkFunList Δ Φ sendAdts prog.funs with
    | .error err => .error err
    | .ok () =>
      match checkProgramExhaustive Δ prog.allFuns with
      | .error err => .error err
      | .ok () =>
        match checkProgramEscape prog.allFuns prog.stackAllocs with
        | .error err => .error err
        | .ok () =>
          match checkEmittedGcMasks prog.adts prog.hasGcMasks prog.gcMasks with
          | .error err => .error err
          | .ok () =>
            if checkProgramGcLayouts prog.adts then .ok ()
            else .error "GC pointer-mask layout verification failed"
  else
    .error "internal error: computed Send ADT set is not closed"

theorem checkFunDef_sound {Δ : AdtEnv} {Φ : FunEnv} {sendAdts : List Ident} {fd : FunDef}
    (hcl : checkSendAdtsClosed Δ sendAdts = true)
    (h : checkFunDef Δ Φ sendAdts fd = .ok ()) :
    HasType Δ Φ [] emptyTaskTy (extendMany emptyCtx fd.params) fd.body fd.retTy := by
  simp only [checkFunDef] at h
  cases hb : checkExpr Δ Φ sendAdts (extendMany emptyCtx fd.params) fd.body with
  | error _ => simp only [hb] at h; cases h
  | ok τb =>
    simp only [hb] at h
    split at h
    · rename_i hsub
      exact typing_sub (tySub_sound hsub) (checkExpr_sound hcl hb)
    · cases h

theorem checkFunList_mem {Δ : AdtEnv} {Φ : FunEnv} {sendAdts : List Ident}
    {fds : List FunDef} {fd : FunDef}
    (hcl : checkSendAdtsClosed Δ sendAdts = true)
    (h : checkFunList Δ Φ sendAdts fds = .ok ()) (hmem : fd ∈ fds) :
    HasType Δ Φ [] emptyTaskTy (extendMany emptyCtx fd.params) fd.body fd.retTy := by
  induction fds with
  | nil => cases hmem
  | cons f rest ih =>
    simp only [checkFunList] at h
    cases hf : checkFunDef Δ Φ sendAdts f with
    | error _ => simp only [hf] at h; cases h
    | ok u =>
      simp only [hf] at h
      rcases List.mem_cons.mp hmem with rfl | hrest
      · exact checkFunDef_sound hcl hf
      · exact ih h hrest

theorem checkProgram_components {prog : Program} (h : checkProgram prog = .ok ()) :
    FunEnvTyped prog.toAdtEnv prog.toFunEnv ∧
    FunEnvExhSafe prog.toAdtEnv prog.toFunEnv ∧
    checkProgramEscape prog.allFuns prog.stackAllocs = .ok () ∧
    checkProgramGcLayouts prog.adts = true := by
  unfold checkProgram at h
  dsimp only at h
  split at h
  · rename_i hcl
    cases hfl : checkFunList prog.toAdtEnv prog.toFunEnv (computeSendAdts prog.adts) prog.funs with
    | error _ => rw [hfl] at h; cases h
    | ok u1 =>
      rw [hfl] at h; dsimp only at h
      cases hexh : checkProgramExhaustive prog.toAdtEnv prog.allFuns with
      | error _ => rw [hexh] at h; cases h
      | ok u2 =>
        rw [hexh] at h; dsimp only at h
        cases hesc : checkProgramEscape prog.allFuns prog.stackAllocs with
        | error _ => rw [hesc] at h; cases h
        | ok u3 =>
          rw [hesc] at h; dsimp only at h
          cases hgcm : checkEmittedGcMasks prog.adts prog.hasGcMasks prog.gcMasks with
          | error _ => rw [hgcm] at h; cases h
          | ok u4 =>
            rw [hgcm] at h; dsimp only at h
            split at h
            · rename_i hgc
              cases u3; cases u4
              refine ⟨?_, ?_, rfl, hgc⟩
              · intro name fd hfd
                have hmem := List.mem_of_find?_eq_some hfd
                rcases List.mem_append.mp hmem with hfun | hext
                · exact checkFunList_mem hcl hfl hfun
                · rcases List.mem_map.mp hext with ⟨ed, _, rfl⟩
                  exact .trap .hostTrap ed.retTy
              · exact checkProgramExhaustive_sound
                  (fun _ _ hfd => List.mem_of_find?_eq_some hfd) hexh
            · cases h
  · cases h

theorem checkProgram_sound {prog : Program} (h : checkProgram prog = .ok ()) :
    FunEnvTyped prog.toAdtEnv prog.toFunEnv :=
  (checkProgram_components h).1

/-- End-to-end Sequential Type Safety Theorem:
    Any Core Geisha program accepted by `checkProgram` never gets stuck in
    single-thread execution. -/
theorem verified_program_safety (prog : Program) (hchk : checkProgram prog = .ok ())
    (entry : Ident) (fd : FunDef) (hfd : prog.toFunEnv entry = some fd)
    (hnoargs : fd.params = [])
    (e' : Expr) (σ' : Store)
    (hsteps : Steps prog.toAdtEnv prog.toFunEnv fd.body [] e' σ') :
    ¬ IsStuck prog.toAdtEnv prog.toFunEnv emptyPool e' σ' := by
  have hΦ := checkProgram_sound hchk
  have hbody : HasType prog.toAdtEnv prog.toFunEnv [] emptyTaskTy emptyCtx fd.body fd.retTy := by
    have h1 := hΦ entry fd hfd
    rw [hnoargs] at h1
    exact h1
  have hσ0 : StoreTyped prog.toAdtEnv prog.toFunEnv [] emptyTaskTy [] :=
    ⟨rfl, fun _ _ h => by simp at h⟩
  exact type_safety hΦ hbody hσ0 hsteps

/-- End-to-end Sequential Exhaustiveness Theorem:
    Any Core Geisha program accepted by `checkProgram` never terminates with
    `Trap.matchFailure` in sequential execution. -/
theorem verified_program_no_match_failure (prog : Program) (hchk : checkProgram prog = .ok ())
    (entry : Ident) (fd : FunDef) (hfd : prog.toFunEnv entry = some fd)
    (hnoargs : fd.params = [])
    (e' : Expr) (σ' : Store)
    (hsteps : Steps prog.toAdtEnv prog.toFunEnv fd.body [] e' σ') :
    e' ≠ .trap .matchFailure := by
  rcases checkProgram_components hchk with ⟨hΦ, hΦ_exh, _, _⟩
  have hbody : HasType prog.toAdtEnv prog.toFunEnv [] emptyTaskTy emptyCtx fd.body fd.retTy := by
    have h1 := hΦ entry fd hfd
    rw [hnoargs] at h1
    exact h1
  exact exhaustive_no_match_failure hΦ hΦ_exh hbody (hΦ_exh entry fd hfd) hsteps

/-- End-to-end Concurrent Type Safety Theorem (`Task` + `MVar` + `Chan` + `Actor`):
    Across arbitrary interleavings (`ConcSteps`), no active `Task` or `Actor`
    thread ever enters an undefined/stuck state (`¬ IsStuck`). -/
theorem verified_concurrent_program_safety (prog : Program) (hchk : checkProgram prog = .ok ())
    (entry : Ident) (fd : FunDef) (hfd : prog.toFunEnv entry = some fd)
    (hnoargs : fd.params = []) (hret : fd.retTy = .void)
    (pool : ConcPool) (σ : Store)
    (hsteps : ConcSteps prog.toAdtEnv prog.toFunEnv (initPool fd.body) [] pool σ) :
    ∀ (th : ThreadId) (e : Expr),
      activeThreadExpr pool th = some e → ¬ IsStuck prog.toAdtEnv prog.toFunEnv pool e σ := by
  have hΦ := checkProgram_sound hchk
  have hbody : HasType prog.toAdtEnv prog.toFunEnv [] emptyTaskTy emptyCtx fd.body .void := by
    have h1 := hΦ entry fd hfd
    rw [hnoargs, hret] at h1
    exact h1
  exact conc_type_safety hΦ hbody hsteps

/-- End-to-end Verified Data-Race Freedom Theorem (`Task` + `MVar` + `Chan` + `Actor`):
    Any Core Geisha program accepted by `checkProgram` is completely free of
    `Cell` data races (`¬ HasDataRace pool`) across all Task-Task, Task-Actor,
    and Actor-Actor interleavings. -/
theorem verified_program_data_race_freedom (prog : Program) (hchk : checkProgram prog = .ok ())
    (entry : Ident) (fd : FunDef) (hfd : prog.toFunEnv entry = some fd)
    (hnoargs : fd.params = []) (hret : fd.retTy = .void)
    (pool : ConcPool) (σ : Store)
    (hsteps : ConcSteps prog.toAdtEnv prog.toFunEnv (initPool fd.body) [] pool σ) :
    ¬ HasDataRace pool := by
  have hΦ := checkProgram_sound hchk
  have hbody : HasType prog.toAdtEnv prog.toFunEnv [] emptyTaskTy emptyCtx fd.body .void := by
    have h1 := hΦ entry fd hfd
    rw [hnoargs, hret] at h1
    exact h1
  exact conc_data_race_freedom hΦ hbody hsteps

/-- End-to-end Concurrent Exhaustiveness Theorem:
    Across arbitrary concurrent `Task` and `Actor` interleavings, no running
    `Task` and no `Actor` ever fails with `Trap.matchFailure`. -/
theorem verified_concurrent_no_match_failure (prog : Program) (hchk : checkProgram prog = .ok ())
    (entry : Ident) (fd : FunDef) (hfd : prog.toFunEnv entry = some fd)
    (hnoargs : fd.params = []) (hret : fd.retTy = .void)
    (pool : ConcPool) (σ : Store)
    (hsteps : ConcSteps prog.toAdtEnv prog.toFunEnv (initPool fd.body) [] pool σ) :
    (∀ (tid : TaskId) (e : Expr), pool.tasks[tid]? = some (.running e) → e ≠ .trap .matchFailure) ∧
    (∀ (aid : Nat) (act : ActorState), pool.actors[aid]? = some act → act.phase ≠ .failed .matchFailure) := by
  rcases checkProgram_components hchk with ⟨hΦ, hΦ_exh, _, _⟩
  have hbody : HasType prog.toAdtEnv prog.toFunEnv [] emptyTaskTy emptyCtx fd.body .void := by
    have h1 := hΦ entry fd hfd
    rw [hnoargs, hret] at h1
    exact h1
  exact conc_exhaustive_no_match_failure hΦ hΦ_exh hbody (hΦ_exh entry fd hfd) hsteps

/-- End-to-end Verified GC Pointer-Mask Soundness Theorem:
    Every ADT variant in any Core Geisha program accepted by `checkProgram` has a
    sound 40-bit pointer word mask (`ObjMaskSound`) that scans every pointer word
    and never misidentifies scalar fields as heap pointers. -/
theorem verified_program_gc_mask_sound (prog : Program) (hchk : checkProgram prog = .ok ())
    {adt : AdtDef} (hAdt : adt ∈ prog.adts) {v : VariantDef} (hVar : v ∈ adt.variants)
    (tagBits : UInt64) (words : List Word)
    (hLayout : WordsMatchLayout words (flattenTyListWords v.fields)) :
    let obj : HeapObj := { hdrMask := adtVariantPtrMask v, mutable := false, words := .scalar tagBits :: words }
    ObjMaskSound obj ∧
    (∀ (m idx : Nat) (bits : UInt64), adtVariantPtrMask v = some m → obj.words[idx]? = some (.scalar bits) → m.testBit idx = false) :=
  checkProgramGcLayouts_sound (checkProgram_components hchk).2.2.2 hAdt hVar tagBits words hLayout

/-- End-to-end Verified Stack-Region Memory Safety Theorem:
    Any Core Geisha program accepted by `checkProgram` never dereferences a
    popped/deallocated stack-frame slot (`¬ IsDanglingAccess`) across arbitrarily
    nested and recursive calls. -/
theorem verified_program_no_dangling_stack (prog : Program) (hchk : checkProgram prog = .ok ())
    (entry : Ident) (fd : FunDef) (hfd : prog.toFunEnv entry = some fd)
    (hnoargs : fd.params = [])
    {re' : RExpr} {ρ' : RStore} {n' : RegionId}
    (hsteps : RSteps prog.toFunEnv prog.stackAllocs
      (.frame 0 (compileExpr (lookupStackVars prog.stackAllocs entry) 0 fd.body)) [] 1 re' ρ' n') :
    ¬ IsDanglingAccess re' ρ' :=
  escape_no_dangling_pointers_gen (fun _ => rfl) (checkProgram_components hchk).2.2.1 hfd hnoargs hsteps

/-- End-to-end Verified Stack-vs-Heap Observational Simulation Theorem:
    Stack-promoted execution of `main` in any program accepted by `checkProgram`
    is simulated step-for-step by standard heap semantics (`Steps`). -/
theorem verified_program_stack_simulates_heap (prog : Program) (hchk : checkProgram prog = .ok ())
    (fdMain : FunDef) (hmain : prog.toFunEnv "main" = some fdMain)
    (hnoargs : fdMain.params = [])
    {re' : RExpr} {ρ' : RStore} {n' : RegionId}
    (hsteps : RSteps prog.toFunEnv prog.stackAllocs
      (.frame 0 (compileExpr (lookupStackVars prog.stackAllocs "main") 0 fdMain.body)) [] 1 re' ρ' n') :
    ∃ σ' : Store,
      Steps prog.toAdtEnv prog.toFunEnv fdMain.body [] (eraseRExpr re') σ' ∧ RStoreMatches ρ' σ' :=
  stack_alloc_simulates_heap prog.toAdtEnv (fun _ => rfl) (checkProgram_components hchk).2.2.1
    hmain hnoargs hsteps

end CoreGeisha
