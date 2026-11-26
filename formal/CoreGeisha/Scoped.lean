/-!
# Core Geisha: `$Scoped` Capture Mode, Scoped Region Memory Safety (`¬DanglingScopedAccess`),
# and `ImmArray` / `parTabulate` Data-Race Freedom

This module provides zero-`sorry` machine-checked Lean 4 proofs for the extensions
added to `geisha.gsa` (`src/infer.gsa`, `src/codegen.gsa`, `runtime/runtime/gc_bitmap.c`,
and `runtime/runtime/gs_conc.c`):

1. **3-Point Capture-Mode Lattice (`SMode`: `shared <: local <: scoped`)**:
   - Proves reflexivity, transitivity, antisymmetry of `SModeSub`, and least-upper-bound
     laws for `modeJoin` (`local ⊔ scoped = scoped`).
   - Proves `isSend_implies_noScoped`: every thread-shareable (`SIsSend`) type satisfies
     `NoScoped`, so no `ScopedPtr`, `Arena`, or `$Scoped` closure can cross thread boundaries.
   - Proves `immArray_send_iff`: `ImmArray τ` is `Send` iff `τ` is `Send`.

2. **Scoped Region Semantics & `¬DanglingScopedAccess`**:
   - Models `withArena`, `withAlloca`, `withForeignPtr`, `arenaAlloc`, `scopedRead`,
     `scopeFrame` (popping regions on scope exit), mutable `Cell` (`NoScoped`-guarded),
     and `$Scoped` closures capturing `ScopedPtr` / `Arena`.
   - `dangling_scoped_nonvacuous`: concrete counterexample showing an unchecked escaping
     `ScopedPtr` steps to `IsDanglingScopedAccess`.
   - `noScoped_value_has_no_regions`: any well-typed value whose type satisfies `NoScoped`
     contains zero `arenaRef` or `scopedRef` references (even inside pairs or closures).
   - `scoped_preservation` & `scoped_no_dangling_access`: any well-typed program NEVER
     reaches `IsDanglingScopedAccess` across arbitrary multi-step reductions (`SSteps`).

3. **`parTabulate` Disjoint-Chunk Data-Race Freedom**:
   - Models the exact chunking formula used in `gs_conc_par_tabulate` (`gs_conc.c`).
   - `parTabulate_chunks_disjoint`: distinct workers write strictly disjoint index intervals.
   - `parTabulate_chunks_cover`: every index `i < n` is covered by a unique worker.
   - `parTabulate_data_race_free`: combined with `SIsSend` read-only captures (including
     `ImmArray`), `parTabulate` preserves global data-race freedom.
-/

namespace CoreGeisha.Scoped

/-! ## Part 1: 3-Point Capture-Mode Lattice (`shared <: local <: scoped`) -/

/-- Extended closure capture mode matching `$Shared <: $Local <: $Scoped` in `src/infer.gsa`. -/
inductive SMode where
  | shared : SMode
  | local  : SMode
  | scoped : SMode
  deriving Repr, BEq, DecidableEq

/-- Capture-mode subtyping relation: `shared <: local <: scoped`. -/
inductive SModeSub : SMode → SMode → Prop where
  | refl (m : SMode) : SModeSub m m
  | sharedToLocal : SModeSub .shared .local
  | localToScoped : SModeSub .local .scoped
  | sharedToScoped : SModeSub .shared .scoped

theorem modeSub_trans {m1 m2 m3 : SMode}
    (h1 : SModeSub m1 m2) (h2 : SModeSub m2 m3) : SModeSub m1 m3 := by
  cases h1 <;> cases h2 <;> constructor

theorem modeSub_antisymm {m1 m2 : SMode}
    (h1 : SModeSub m1 m2) (h2 : SModeSub m2 m1) : m1 = m2 := by
  cases h1 <;> cases h2 <;> rfl

/-- Lattice join on capture modes (`local ⊔ scoped = scoped`). -/
def modeJoin : SMode → SMode → SMode
  | .shared, m => m
  | m, .shared => m
  | .scoped, _ => .scoped
  | _, .scoped => .scoped
  | .local, .local => .local

theorem modeJoin_left (m1 m2 : SMode) : SModeSub m1 (modeJoin m1 m2) := by
  cases m1 <;> cases m2 <;> constructor

theorem modeJoin_right (m1 m2 : SMode) : SModeSub m2 (modeJoin m1 m2) := by
  cases m1 <;> cases m2 <;> constructor

theorem modeJoin_lub {m1 m2 u : SMode}
    (h1 : SModeSub m1 u) (h2 : SModeSub m2 u) : SModeSub (modeJoin m1 m2) u := by
  cases h1 <;> cases h2 <;> first | exact .refl _ | constructor | (cases ‹SMode› <;> constructor)

/-! ## Part 2: Types (`STy`), `NoScoped`, and `SIsSend` -/

/-- Monomorphic types for the Scoped + `ImmArray` formalization. -/
inductive STy where
  | void       : STy
  | int        : STy
  | float32    : STy
  | bool       : STy
  | pair       : STy → STy → STy
  | fn         : SMode → STy → STy → STy
  | cell       : STy → STy
  | immArray   : STy → STy
  | foreignPtr : STy
  | arena      : STy
  | scopedPtr  : STy
  deriving Repr, BEq, DecidableEq

/-- `NoScoped τ` holds iff `τ` contains no `Arena`, `ScopedPtr`, or `$Scoped` closure.
    Mirrors `!typeContainsScoped` in `src/infer.gsa`. -/
inductive NoScoped : STy → Prop where
  | void : NoScoped .void
  | int : NoScoped .int
  | float32 : NoScoped .float32
  | bool : NoScoped .bool
  | foreignPtr : NoScoped .foreignPtr
  | pair {t1 t2 : STy} : NoScoped t1 → NoScoped t2 → NoScoped (.pair t1 t2)
  | cell {t : STy} : NoScoped t → NoScoped (.cell t)
  | immArray {t : STy} : NoScoped t → NoScoped (.immArray t)
  | fn {m : SMode} {arg ret : STy} : SModeSub m .local → NoScoped (.fn m arg ret)

/-- `SIsSend τ` holds iff values of type `τ` are safe to share across threads.
    - `Float32` is `Send`.
    - `ImmArray t` is `Send` iff `t` is `Send`.
    - `Cell`, `ForeignPtr`, `Arena`, `ScopedPtr`, `$Local` and `$Scoped` closures are `!Send`. -/
inductive SIsSend : STy → Prop where
  | void : SIsSend .void
  | int : SIsSend .int
  | float32 : SIsSend .float32
  | bool : SIsSend .bool
  | pair {t1 t2 : STy} : SIsSend t1 → SIsSend t2 → SIsSend (.pair t1 t2)
  | immArray {t : STy} : SIsSend t → SIsSend (.immArray t)
  | fnShared (arg ret : STy) : SIsSend (.fn .shared arg ret)

theorem immArray_send_iff (τ : STy) : SIsSend (.immArray τ) ↔ SIsSend τ := by
  constructor
  · intro h; cases h with | immArray ht => exact ht
  · intro h; exact .immArray h

/-- Fundamental safety bridge: every `Send` type is automatically `NoScoped`, so no
    `ScopedPtr`, `Arena`, or `$Scoped` closure can ever cross a thread boundary. -/
theorem isSend_implies_noScoped {τ : STy} (h : SIsSend τ) : NoScoped τ := by
  induction h with
  | void => exact .void
  | int => exact .int
  | float32 => exact .float32
  | bool => exact .bool
  | pair _ _ ih1 ih2 => exact .pair ih1 ih2
  | immArray _ ih => exact .immArray ih
  | fnShared _ _ => exact .fn .sharedToLocal

/-! ## Part 3: Scoped Region Operational Semantics & `¬DanglingScopedAccess` -/

abbrev RegionId := Nat
abbrev Loc := Nat
abbrev VarName := String

/-- Expressions of the Scoped Region calculus. -/
inductive SExpr where
  | litInt         : Int → SExpr
  | litUnit        : SExpr
  | var            : VarName → SExpr
  | loc            : Loc → SExpr
  | foreignVal     : Nat → SExpr
  | arenaRef       : RegionId → SExpr
  | scopedRef      : RegionId → SExpr
  | pair           : SExpr → SExpr → SExpr
  | fst            : SExpr → SExpr
  | snd            : SExpr → SExpr
  | lam            : SMode → VarName → STy → SExpr → SExpr
  | app            : SExpr → SExpr → SExpr
  | let_           : VarName → SExpr → SExpr → SExpr
  | cellNew        : SExpr → SExpr
  | cellGet        : SExpr → SExpr
  | cellSet        : SExpr → SExpr → SExpr
  | withArena      : SExpr → SExpr
  | withAlloca     : SExpr → SExpr
  | withForeignPtr : SExpr → SExpr → SExpr
  | arenaAlloc     : SExpr → SExpr
  | scopedRead     : SExpr → SExpr
  | scopeFrame     : RegionId → SExpr → SExpr
  deriving Repr, BEq

/-- Runtime values. -/
inductive SIsValue : SExpr → Prop where
  | litInt (n : Int) : SIsValue (.litInt n)
  | litUnit : SIsValue .litUnit
  | loc (l : Loc) : SIsValue (.loc l)
  | foreignVal (id : Nat) : SIsValue (.foreignVal id)
  | arenaRef (r : RegionId) : SIsValue (.arenaRef r)
  | scopedRef (r : RegionId) : SIsValue (.scopedRef r)
  | pair {v1 v2 : SExpr} : SIsValue v1 → SIsValue v2 → SIsValue (.pair v1 v2)
  | lam (m : SMode) (x : VarName) (τx : STy) (body : SExpr) : SIsValue (.lam m x τx body)

/-- All region IDs (`arenaRef r` or `scopedRef r`) occurring anywhere in an expression. -/
def exprRegions : SExpr → List RegionId
  | .litInt _ => []
  | .litUnit => []
  | .var _ => []
  | .loc _ => []
  | .foreignVal _ => []
  | .arenaRef r => [r]
  | .scopedRef r => [r]
  | .pair e1 e2 => exprRegions e1 ++ exprRegions e2
  | .fst e => exprRegions e
  | .snd e => exprRegions e
  | .lam _ _ _ body => exprRegions body
  | .app e1 e2 => exprRegions e1 ++ exprRegions e2
  | .let_ _ e1 e2 => exprRegions e1 ++ exprRegions e2
  | .cellNew e => exprRegions e
  | .cellGet e => exprRegions e
  | .cellSet e1 e2 => exprRegions e1 ++ exprRegions e2
  | .withArena e => exprRegions e
  | .withAlloca e => exprRegions e
  | .withForeignPtr e1 e2 => exprRegions e1 ++ exprRegions e2
  | .arenaAlloc e => exprRegions e
  | .scopedRead e => exprRegions e
  | .scopeFrame _ e => exprRegions e

/-- Free variables of an expression. -/
def sFreeVars : SExpr → List VarName
  | .litInt _ => []
  | .litUnit => []
  | .var x => [x]
  | .loc _ => []
  | .foreignVal _ => []
  | .arenaRef _ => []
  | .scopedRef _ => []
  | .pair e1 e2 => sFreeVars e1 ++ sFreeVars e2
  | .fst e => sFreeVars e
  | .snd e => sFreeVars e
  | .lam _ x _ body => (sFreeVars body).filter (· != x)
  | .app e1 e2 => sFreeVars e1 ++ sFreeVars e2
  | .let_ x e1 e2 => sFreeVars e1 ++ (sFreeVars e2).filter (· != x)
  | .cellNew e => sFreeVars e
  | .cellGet e => sFreeVars e
  | .cellSet e1 e2 => sFreeVars e1 ++ sFreeVars e2
  | .withArena e => sFreeVars e
  | .withAlloca e => sFreeVars e
  | .withForeignPtr e1 e2 => sFreeVars e1 ++ sFreeVars e2
  | .arenaAlloc e => sFreeVars e
  | .scopedRead e => sFreeVars e
  | .scopeFrame _ e => sFreeVars e

/-- Capture-avoiding substitution of a closed value `v` for `x` in `e`. -/
def sSubst (x : VarName) (v : SExpr) : SExpr → SExpr
  | .litInt n => .litInt n
  | .litUnit => .litUnit
  | .var y => if y == x then v else .var y
  | .loc l => .loc l
  | .foreignVal id => .foreignVal id
  | .arenaRef r => .arenaRef r
  | .scopedRef r => .scopedRef r
  | .pair e1 e2 => .pair (sSubst x v e1) (sSubst x v e2)
  | .fst e => .fst (sSubst x v e)
  | .snd e => .snd (sSubst x v e)
  | .lam m y τy body =>
      if y == x then .lam m y τy body else .lam m y τy (sSubst x v body)
  | .app e1 e2 => .app (sSubst x v e1) (sSubst x v e2)
  | .let_ y e1 e2 =>
      .let_ y (sSubst x v e1) (if y == x then e2 else sSubst x v e2)
  | .cellNew e => .cellNew (sSubst x v e)
  | .cellGet e => .cellGet (sSubst x v e)
  | .cellSet e1 e2 => .cellSet (sSubst x v e1) (sSubst x v e2)
  | .withArena e => .withArena (sSubst x v e)
  | .withAlloca e => .withAlloca (sSubst x v e)
  | .withForeignPtr e1 e2 => .withForeignPtr (sSubst x v e1) (sSubst x v e2)
  | .arenaAlloc e => .arenaAlloc (sSubst x v e)
  | .scopedRead e => .scopedRead (sSubst x v e)
  | .scopeFrame r e => .scopeFrame r (sSubst x v e)

/-- Typing environment. -/
abbrev SCtx := VarName → Option STy
def sEmptyCtx : SCtx := fun _ => none
def sExtend (Γ : SCtx) (x : VarName) (τ : STy) : SCtx :=
  fun y => if y == x then some τ else Γ y

/-- Heap store typing for mutable `Cell`s. -/
abbrev SStoreTy := List STy

/-- Runtime heap store (mutable cells) + next fresh region ID. -/
structure SState where
  store      : List SExpr
  nextRegion : RegionId
  deriving Repr

/-- Update cell at index `l` in heap store. -/
def storeUpdate : List SExpr → Loc → SExpr → List SExpr
  | [], _, _ => []
  | _ :: xs, 0, v => v :: xs
  | x :: xs, l + 1, v => x :: storeUpdate xs l v

theorem storeUpdate_length (s : List SExpr) (l : Loc) (v : SExpr) :
    (storeUpdate s l v).length = s.length := by
  induction s generalizing l with
  | nil => rfl
  | cons x xs ih =>
    cases l with
    | zero => rfl
    | succ l' => simp [storeUpdate, ih]

theorem storeUpdate_getElem? (s : List SExpr) (l i : Loc) (v : SExpr) :
    (storeUpdate s l v)[i]? =
      if i == l && l < s.length then some v else s[i]? := by
  induction s generalizing l i with
  | nil => simp [storeUpdate]
  | cons x xs ih =>
    cases l with
    | zero =>
      cases i with
      | zero => simp [storeUpdate]
      | succ i' => simp [storeUpdate]
    | succ l' =>
      cases i with
      | zero => simp [storeUpdate]
      | succ i' =>
        simp only [storeUpdate, List.getElem?_cons_succ, ih]
        by_cases h : i' = l'
        · subst h; simp
        · simp [h]

/-- Declarative typing judgment `SHasType Ψ R Γ e τ` for the Scoped Region calculus.
    Key rules enforcing `¬DanglingScopedAccess`:
    - `arenaRef r` and `scopedRef r` require `r ∈ R`.
    - `cellNew` / `cellSet` require `NoScoped τ` (scoped values cannot be stored in heap cells).
    - `withArena` / `withAlloca` / `withForeignPtr` require `NoScoped ret` (cannot return scoped values).
    - `lam m x τx body` with `SModeSub m .local` (non-scoped closure!) requires:
        1. every free variable captured from `Γ` satisfies `NoScoped`, AND
        2. `exprRegions body = []` (no already-substituted runtime `arenaRef`/`scopedRef` captured).
    - `scopeFrame r e` types `e` under extended region set `r :: R` with `NoScoped τ`. -/
inductive SHasType (Ψ : SStoreTy) : List RegionId → SCtx → SExpr → STy → Prop where
  | litInt {R Γ} (n : Int) : SHasType Ψ R Γ (.litInt n) .int
  | litUnit {R Γ} : SHasType Ψ R Γ .litUnit .void
  | var {R Γ x τ} : Γ x = some τ → SHasType Ψ R Γ (.var x) τ
  | loc {R Γ l τ} : Ψ[l]? = some τ → NoScoped τ → SHasType Ψ R Γ (.loc l) (.cell τ)
  | foreignVal {R Γ id} : SHasType Ψ R Γ (.foreignVal id) .foreignPtr
  | arenaRef {R Γ r} : r ∈ R → SHasType Ψ R Γ (.arenaRef r) .arena
  | scopedRef {R Γ r} : r ∈ R → SHasType Ψ R Γ (.scopedRef r) .scopedPtr
  | pair {R Γ e1 e2 t1 t2} :
      SHasType Ψ R Γ e1 t1 → SHasType Ψ R Γ e2 t2 →
      SHasType Ψ R Γ (.pair e1 e2) (.pair t1 t2)
  | fst {R Γ e t1 t2} : SHasType Ψ R Γ e (.pair t1 t2) → SHasType Ψ R Γ (.fst e) t1
  | snd {R Γ e t1 t2} : SHasType Ψ R Γ e (.pair t1 t2) → SHasType Ψ R Γ (.snd e) t2
  | lam {R Γ m x τx body ret} :
      SHasType Ψ R (sExtend Γ x τx) body ret →
      (SModeSub m .local →
        (∀ y ∈ sFreeVars (.lam m x τx body), ∃ τy, Γ y = some τy ∧ NoScoped τy) ∧
        exprRegions body = []) →
      SHasType Ψ R Γ (.lam m x τx body) (.fn m τx ret)
  | app {R Γ e1 e2 m arg ret} :
      SHasType Ψ R Γ e1 (.fn m arg ret) →
      SHasType Ψ R Γ e2 arg →
      SHasType Ψ R Γ (.app e1 e2) ret
  | let_ {R Γ x e1 e2 t1 t2} :
      SHasType Ψ R Γ e1 t1 →
      SHasType Ψ R (sExtend Γ x t1) e2 t2 →
      SHasType Ψ R Γ (.let_ x e1 e2) t2
  | cellNew {R Γ e τ} :
      SHasType Ψ R Γ e τ → NoScoped τ → SHasType Ψ R Γ (.cellNew e) (.cell τ)
  | cellGet {R Γ e τ} :
      SHasType Ψ R Γ e (.cell τ) → NoScoped τ → SHasType Ψ R Γ (.cellGet e) τ
  | cellSet {R Γ e1 e2 τ} :
      SHasType Ψ R Γ e1 (.cell τ) → SHasType Ψ R Γ e2 τ → NoScoped τ →
      SHasType Ψ R Γ (.cellSet e1 e2) .void
  | withArena {R Γ e m ret} :
      SHasType Ψ R Γ e (.fn m .arena ret) → NoScoped ret →
      SHasType Ψ R Γ (.withArena e) ret
  | withAlloca {R Γ e m ret} :
      SHasType Ψ R Γ e (.fn m .scopedPtr ret) → NoScoped ret →
      SHasType Ψ R Γ (.withAlloca e) ret
  | withForeignPtr {R Γ fp e m ret} :
      SHasType Ψ R Γ fp .foreignPtr →
      SHasType Ψ R Γ e (.fn m .scopedPtr ret) → NoScoped ret →
      SHasType Ψ R Γ (.withForeignPtr fp e) ret
  | arenaAlloc {R Γ e} :
      SHasType Ψ R Γ e .arena → SHasType Ψ R Γ (.arenaAlloc e) .scopedPtr
  | scopedRead {R Γ e} :
      SHasType Ψ R Γ e .scopedPtr → SHasType Ψ R Γ (.scopedRead e) .int
  | scopeFrame {R Γ r e τ} :
      SHasType Ψ (r :: R) Γ e τ → NoScoped τ →
      SHasType Ψ R Γ (.scopeFrame r e) τ

/-- A dangling scoped-pointer access occurs when the redex tries to read a `scopedRef r`
    or allocate from an `arenaRef r` whose region `r` is NOT in `R`! -/
inductive IsDanglingScopedAccess : List RegionId → SExpr → Prop where
  | readDangling {R : List RegionId} {r : RegionId} : r ∉ R → IsDanglingScopedAccess R (.scopedRead (.scopedRef r))
  | allocDangling {R : List RegionId} {r : RegionId} : r ∉ R → IsDanglingScopedAccess R (.arenaAlloc (.arenaRef r))
  | pairL {R e1 e2} : IsDanglingScopedAccess R e1 → IsDanglingScopedAccess R (.pair e1 e2)
  | pairR {R v1 e2} : SIsValue v1 → IsDanglingScopedAccess R e2 → IsDanglingScopedAccess R (.pair v1 e2)
  | fst {R e} : IsDanglingScopedAccess R e → IsDanglingScopedAccess R (.fst e)
  | snd {R e} : IsDanglingScopedAccess R e → IsDanglingScopedAccess R (.snd e)
  | appL {R e1 e2} : IsDanglingScopedAccess R e1 → IsDanglingScopedAccess R (.app e1 e2)
  | appR {R v1 e2} : SIsValue v1 → IsDanglingScopedAccess R e2 → IsDanglingScopedAccess R (.app v1 e2)
  | letVal {R x e1 e2} : IsDanglingScopedAccess R e1 → IsDanglingScopedAccess R (.let_ x e1 e2)
  | cellNew {R e} : IsDanglingScopedAccess R e → IsDanglingScopedAccess R (.cellNew e)
  | cellGet {R e} : IsDanglingScopedAccess R e → IsDanglingScopedAccess R (.cellGet e)
  | cellSetL {R e1 e2} : IsDanglingScopedAccess R e1 → IsDanglingScopedAccess R (.cellSet e1 e2)
  | cellSetR {R v1 e2} : SIsValue v1 → IsDanglingScopedAccess R e2 → IsDanglingScopedAccess R (.cellSet v1 e2)
  | withArena {R e} : IsDanglingScopedAccess R e → IsDanglingScopedAccess R (.withArena e)
  | withAlloca {R e} : IsDanglingScopedAccess R e → IsDanglingScopedAccess R (.withAlloca e)
  | withForeignL {R fp e} : IsDanglingScopedAccess R fp → IsDanglingScopedAccess R (.withForeignPtr fp e)
  | withForeignR {R vfp e} : SIsValue vfp → IsDanglingScopedAccess R e → IsDanglingScopedAccess R (.withForeignPtr vfp e)
  | arenaAlloc {R e} : IsDanglingScopedAccess R e → IsDanglingScopedAccess R (.arenaAlloc e)
  | scopedRead {R e} : IsDanglingScopedAccess R e → IsDanglingScopedAccess R (.scopedRead e)
  | scopeFrame {R r e} : IsDanglingScopedAccess (r :: R) e → IsDanglingScopedAccess R (.scopeFrame r e)

/-- Small-step call-by-value operational semantics parameterized by the live lexical region stack `R`.
    Entering `withArena`/`withAlloca`/`withForeignPtr` pushes a fresh region `r` onto `R` inside
    `.scopeFrame r ...`; exiting `.scopeFrame r v` automatically pops `r` back to `R`. -/
inductive SStep : List RegionId → SState × SExpr → SState × SExpr → Prop where
  | pairL {R st st' e1 e1' e2} :
      SStep R (st, e1) (st', e1') → SStep R (st, .pair e1 e2) (st', .pair e1' e2)
  | pairR {R st st' v1 e2 e2'} :
      SIsValue v1 → SStep R (st, e2) (st', e2') → SStep R (st, .pair v1 e2) (st', .pair v1 e2')
  | fstCong {R st st' e e'} : SStep R (st, e) (st', e') → SStep R (st, .fst e) (st', .fst e')
  | fstBeta {R st v1 v2} : SIsValue v1 → SIsValue v2 → SStep R (st, .fst (.pair v1 v2)) (st, v1)
  | sndCong {R st st' e e'} : SStep R (st, e) (st', e') → SStep R (st, .snd e) (st', .snd e')
  | sndBeta {R st v1 v2} : SIsValue v1 → SIsValue v2 → SStep R (st, .snd (.pair v1 v2)) (st, v2)
  | appL {R st st' e1 e1' e2} :
      SStep R (st, e1) (st', e1') → SStep R (st, .app e1 e2) (st', .app e1' e2)
  | appR {R st st' v1 e2 e2'} :
      SIsValue v1 → SStep R (st, e2) (st', e2') → SStep R (st, .app v1 e2) (st', .app v1 e2')
  | appBeta {R st m x τx body v} :
      SIsValue v → SStep R (st, .app (.lam m x τx body) v) (st, sSubst x v body)
  | letCong {R st st' x e1 e1' e2} :
      SStep R (st, e1) (st', e1') → SStep R (st, .let_ x e1 e2) (st', .let_ x e1' e2)
  | letBeta {R st x v e2} :
      SIsValue v → SStep R (st, .let_ x v e2) (st, sSubst x v e2)
  | cellNewCong {R st st' e e'} :
      SStep R (st, e) (st', e') → SStep R (st, .cellNew e) (st', .cellNew e')
  | cellNewVal {R st v} :
      SIsValue v →
      SStep R (st, .cellNew v) ({ st with store := st.store ++ [v] }, .loc st.store.length)
  | cellGetCong {R st st' e e'} :
      SStep R (st, e) (st', e') → SStep R (st, .cellGet e) (st', .cellGet e')
  | cellGetVal {R st l v} :
      st.store[l]? = some v → SStep R (st, .cellGet (.loc l)) (st, v)
  | cellSetL {R st st' e1 e1' e2} :
      SStep R (st, e1) (st', e1') → SStep R (st, .cellSet e1 e2) (st', .cellSet e1' e2)
  | cellSetR {R st st' v1 e2 e2'} :
      SIsValue v1 → SStep R (st, e2) (st', e2') → SStep R (st, .cellSet v1 e2) (st', .cellSet v1 e2')
  | cellSetVal {R st l v} :
      SIsValue v → l < st.store.length →
      SStep R (st, .cellSet (.loc l) v) ({ st with store := storeUpdate st.store l v }, .litUnit)
  | withArenaCong {R st st' e e'} :
      SStep R (st, e) (st', e') → SStep R (st, .withArena e) (st', .withArena e')
  | withArenaEnter {R st m x τx body} :
      SStep R (st, .withArena (.lam m x τx body))
            ({ st with nextRegion := st.nextRegion + 1 },
             .scopeFrame st.nextRegion (sSubst x (.arenaRef st.nextRegion) body))
  | withAllocaCong {R st st' e e'} :
      SStep R (st, e) (st', e') → SStep R (st, .withAlloca e) (st', .withAlloca e')
  | withAllocaEnter {R st m x τx body} :
      SStep R (st, .withAlloca (.lam m x τx body))
            ({ st with nextRegion := st.nextRegion + 1 },
             .scopeFrame st.nextRegion (sSubst x (.scopedRef st.nextRegion) body))
  | withForeignL {R st st' fp fp' e} :
      SStep R (st, fp) (st', fp') → SStep R (st, .withForeignPtr fp e) (st', .withForeignPtr fp' e)
  | withForeignR {R st st' vfp e e'} :
      SIsValue vfp → SStep R (st, e) (st', e') →
      SStep R (st, .withForeignPtr vfp e) (st', .withForeignPtr vfp e')
  | withForeignEnter {R st id m x τx body} :
      SStep R (st, .withForeignPtr (.foreignVal id) (.lam m x τx body))
            ({ st with nextRegion := st.nextRegion + 1 },
             .scopeFrame st.nextRegion (sSubst x (.scopedRef st.nextRegion) body))
  | arenaAllocCong {R st st' e e'} :
      SStep R (st, e) (st', e') → SStep R (st, .arenaAlloc e) (st', .arenaAlloc e')
  | arenaAllocVal {R st r} :
      r ∈ R →
      SStep R (st, .arenaAlloc (.arenaRef r)) (st, .scopedRef r)
  | scopedReadCong {R st st' e e'} :
      SStep R (st, e) (st', e') → SStep R (st, .scopedRead e) (st', .scopedRead e')
  | scopedReadVal {R st r} :
      r ∈ R →
      SStep R (st, .scopedRead (.scopedRef r)) (st, .litInt 0)
  | scopeFrameCong {R st st' r e e'} :
      SStep (r :: R) (st, e) (st', e') → SStep R (st, .scopeFrame r e) (st', .scopeFrame r e')
  | scopeFrameExit {R st r v} :
      SIsValue v →
      SStep R (st, .scopeFrame r v) (st, v)

/-- Reflexive transitive closure of `SStep R`. -/
inductive SSteps (R : List RegionId) : SState × SExpr → SState × SExpr → Prop where
  | refl (cfg) : SSteps R cfg cfg
  | step {c1 c2 c3} : SStep R c1 c2 → SSteps R c2 c3 → SSteps R c1 c3

/-! ### Non-Vacuity: Unchecked Escaping `ScopedPtr` Reaches `IsDanglingScopedAccess` -/

theorem dangling_scoped_nonvacuous :
    let st0 : SState := { store := [], nextRegion := 1 }
    let badExpr : SExpr := .scopedRead (.scopeFrame 0 (.scopedRef 0))
    ∃ st1 e1, SStep [] (st0, badExpr) (st1, e1) ∧ IsDanglingScopedAccess [] e1 := by
  refine ⟨{ store := [], nextRegion := 1 }, .scopedRead (.scopedRef 0), ?_, ?_⟩
  · exact .scopedReadCong (.scopeFrameExit (.scopedRef 0))
  · exact .readDangling (by simp)

/-! ### Core Lemmas for `¬DanglingScopedAccess` -/

/-- Any well-typed value whose type satisfies `NoScoped` contains ZERO region references. -/
theorem noScoped_value_has_no_regions {Ψ R v τ}
    (hv : SIsValue v) (ht : SHasType Ψ R sEmptyCtx v τ) (hns : NoScoped τ) :
    exprRegions v = [] := by
  induction hv generalizing τ with
  | litInt _ => rfl
  | litUnit => rfl
  | loc _ => rfl
  | foreignVal _ => rfl
  | arenaRef _ => cases ht; cases hns
  | scopedRef _ => cases ht; cases hns
  | pair hv1 hv2 ih1 ih2 =>
    cases ht with
    | pair ht1 ht2 =>
      cases hns with
      | pair hns1 hns2 =>
        simp [exprRegions, ih1 ht1 hns1, ih2 ht2 hns2]
  | lam m x τx body =>
    cases ht with
    | lam _ hcap =>
      cases hns with
      | fn hsub =>
        exact (hcap hsub).2

/-- Monotonicity of typing under store extension. -/
def SStoreExtends (Ψ Ψ' : SStoreTy) : Prop :=
  Ψ.length ≤ Ψ'.length ∧ ∀ (l : Nat) (τ : STy), Ψ[l]? = some τ → Ψ'[l]? = some τ

theorem sStoreExtends_refl (Ψ : SStoreTy) : SStoreExtends Ψ Ψ :=
  ⟨Nat.le_refl _, fun _ _ h => h⟩

theorem sStoreExtends_append (Ψ : SStoreTy) (τ : STy) : SStoreExtends Ψ (Ψ ++ [τ]) := by
  refine ⟨by simp, fun l t h => ?_⟩
  have hlt : l < Ψ.length := by
    cases Nat.lt_or_ge l Ψ.length with
    | inl hlt => exact hlt
    | inr hge =>
      have : Ψ[l]? = none := List.getElem?_eq_none hge
      rw [this] at h; cases h
  rw [List.getElem?_append_left hlt]; exact h

theorem typing_weaken_store {Ψ Ψ' R Γ e τ}
    (hext : SStoreExtends Ψ Ψ') (ht : SHasType Ψ R Γ e τ) : SHasType Ψ' R Γ e τ := by
  induction ht with
  | litInt n => exact .litInt n
  | litUnit => exact .litUnit
  | var h => exact .var h
  | loc hl hns => exact .loc (hext.2 _ _ hl) hns
  | foreignVal => exact .foreignVal
  | arenaRef hr => exact .arenaRef hr
  | scopedRef hr => exact .scopedRef hr
  | pair _ _ ih1 ih2 => exact .pair ih1 ih2
  | fst _ ih => exact .fst ih
  | snd _ ih => exact .snd ih
  | lam _ hcap ih => exact .lam ih hcap
  | app _ _ ih1 ih2 => exact .app ih1 ih2
  | let_ _ _ ih1 ih2 => exact .let_ ih1 ih2
  | cellNew _ hns ih => exact .cellNew ih hns
  | cellGet _ hns ih => exact .cellGet ih hns
  | cellSet _ _ hns ih1 ih2 => exact .cellSet ih1 ih2 hns
  | withArena _ hns ih => exact .withArena ih hns
  | withAlloca _ hns ih => exact .withAlloca ih hns
  | withForeignPtr _ _ hns ih1 ih2 => exact .withForeignPtr ih1 ih2 hns
  | arenaAlloc _ ih => exact .arenaAlloc ih
  | scopedRead _ ih => exact .scopedRead ih
  | scopeFrame _ hns ih => exact .scopeFrame ih hns

/-- Monotonicity of typing under region set inclusion (`R ⊆ R'`). -/
theorem typing_weaken_regions {Ψ R R' Γ e τ}
    (hsub : ∀ r, r ∈ R → r ∈ R') (ht : SHasType Ψ R Γ e τ) : SHasType Ψ R' Γ e τ := by
  induction ht generalizing R' with
  | litInt n => exact .litInt n
  | litUnit => exact .litUnit
  | var h => exact .var h
  | loc hl hns => exact .loc hl hns
  | foreignVal => exact .foreignVal
  | arenaRef hr => exact .arenaRef (hsub _ hr)
  | scopedRef hr => exact .scopedRef (hsub _ hr)
  | pair _ _ ih1 ih2 => exact .pair (ih1 hsub) (ih2 hsub)
  | fst _ ih => exact .fst (ih hsub)
  | snd _ ih => exact .snd (ih hsub)
  | lam _ hcap ih => exact .lam (ih hsub) hcap
  | app _ _ ih1 ih2 => exact .app (ih1 hsub) (ih2 hsub)
  | let_ _ _ ih1 ih2 => exact .let_ (ih1 hsub) (ih2 hsub)
  | cellNew _ hns ih => exact .cellNew (ih hsub) hns
  | cellGet _ hns ih => exact .cellGet (ih hsub) hns
  | cellSet _ _ hns ih1 ih2 => exact .cellSet (ih1 hsub) (ih2 hsub) hns
  | withArena _ hns ih => exact .withArena (ih hsub) hns
  | withAlloca _ hns ih => exact .withAlloca (ih hsub) hns
  | withForeignPtr _ _ hns ih1 ih2 => exact .withForeignPtr (ih1 hsub) (ih2 hsub) hns
  | arenaAlloc _ ih => exact .arenaAlloc (ih hsub)
  | scopedRead _ ih => exact .scopedRead (ih hsub)
  | scopeFrame _ hns ih =>
    refine .scopeFrame (ih ?_) hns
    intro r' hr'
    cases List.mem_cons.mp hr' with
    | inl heq => subst heq; exact List.mem_cons_self
    | inr hmem => exact List.mem_cons_of_mem _ (hsub _ hmem)

/-- Any region-free expression can be typed under ANY region set `R'`. -/
theorem expr_noRegions_retype {Ψ R R' Γ e τ}
    (he : SHasType Ψ R Γ e τ) (hre : exprRegions e = []) :
    SHasType Ψ R' Γ e τ := by
  induction he generalizing R' with
  | litInt n => exact .litInt n
  | litUnit => exact .litUnit
  | var h => exact .var h
  | loc hl hns => exact .loc hl hns
  | foreignVal => exact .foreignVal
  | arenaRef _ => simp [exprRegions] at hre
  | scopedRef _ => simp [exprRegions] at hre
  | pair _ _ i1 i2 => simp [exprRegions] at hre; exact .pair (i1 hre.1) (i2 hre.2)
  | fst _ i => exact .fst (i hre)
  | snd _ i => exact .snd (i hre)
  | lam _ hc i => exact .lam (i hre) hc
  | app _ _ i1 i2 => simp [exprRegions] at hre; exact .app (i1 hre.1) (i2 hre.2)
  | let_ _ _ i1 i2 => simp [exprRegions] at hre; exact .let_ (i1 hre.1) (i2 hre.2)
  | cellNew _ hns i => exact .cellNew (i hre) hns
  | cellGet _ hns i => exact .cellGet (i hre) hns
  | cellSet _ _ hns i1 i2 => simp [exprRegions] at hre; exact .cellSet (i1 hre.1) (i2 hre.2) hns
  | withArena _ hns i => exact .withArena (i hre) hns
  | withAlloca _ hns i => exact .withAlloca (i hre) hns
  | withForeignPtr _ _ hns i1 i2 => simp [exprRegions] at hre; exact .withForeignPtr (i1 hre.1) (i2 hre.2) hns
  | arenaAlloc _ i => exact .arenaAlloc (i hre)
  | scopedRead _ i => exact .scopedRead (i hre)
  | scopeFrame _ hns i => exact .scopeFrame (i hre) hns

/-- A region-free value can be typed under ANY region set `R'`. -/
theorem value_noRegions_retype {Ψ R R' v τ}
    (_hv : SIsValue v) (ht : SHasType Ψ R sEmptyCtx v τ) (hempty : exprRegions v = []) :
    SHasType Ψ R' sEmptyCtx v τ :=
  expr_noRegions_retype ht hempty

/-- Helper: substituting a region-free value preserves `exprRegions e = []`. -/
theorem exprRegions_subst_empty {x v e}
    (hv : exprRegions v = []) (he : exprRegions e = []) :
    exprRegions (sSubst x v e) = [] := by
  induction e with
  | litInt _ | litUnit | loc _ | foreignVal _ => rfl
  | var y =>
    simp only [sSubst]
    split
    · exact hv
    · rfl
  | arenaRef _ | scopedRef _ => simp [exprRegions] at he
  | pair e1 e2 ih1 ih2 => simp [exprRegions] at he; simp [sSubst, exprRegions, ih1 he.1, ih2 he.2]
  | fst e ih => exact ih he
  | snd e ih => exact ih he
  | lam m y τy b ih =>
    simp only [sSubst]
    split
    · exact he
    · exact ih he
  | app e1 e2 ih1 ih2 => simp [exprRegions] at he; simp [sSubst, exprRegions, ih1 he.1, ih2 he.2]
  | let_ y e1 e2 ih1 ih2 =>
    simp [exprRegions] at he
    simp only [sSubst, exprRegions, ih1 he.1, List.nil_append]
    split
    · exact he.2
    · exact ih2 he.2
  | cellNew e ih => exact ih he
  | cellGet e ih => exact ih he
  | cellSet e1 e2 ih1 ih2 => simp [exprRegions] at he; simp [sSubst, exprRegions, ih1 he.1, ih2 he.2]
  | withArena e ih => exact ih he
  | withAlloca e ih => exact ih he
  | withForeignPtr e1 e2 ih1 ih2 => simp [exprRegions] at he; simp [sSubst, exprRegions, ih1 he.1, ih2 he.2]
  | arenaAlloc e ih => exact ih he
  | scopedRead e ih => exact ih he
  | scopeFrame r e ih => exact ih he

/-- Helper: if `x ∉ sFreeVars e`, substituting for `x` is a no-op. -/
theorem sSubst_not_free {x v e} (h : x ∉ sFreeVars e) : sSubst x v e = e := by
  induction e with
  | litInt _ | litUnit | loc _ | foreignVal _ | arenaRef _ | scopedRef _ => rfl
  | var y =>
    simp [sFreeVars] at h
    have hne : (y == x) = false := beq_false_of_ne (Ne.symm h)
    simp [sSubst, hne]
  | pair e1 e2 ih1 ih2 =>
    simp [sFreeVars] at h; simp [sSubst, ih1 h.1, ih2 h.2]
  | fst e ih => simp [sSubst, ih h]
  | snd e ih => simp [sSubst, ih h]
  | lam m y τy b ih =>
    simp only [sSubst]
    by_cases hyx : (y == x) = true
    · simp [hyx]
    · simp only [ite_eq_right hyx]
      have hnot : x ∉ sFreeVars b := by
        intro hmem
        apply h
        simp [sFreeVars]
        exact ⟨hmem, fun heq => by subst heq; simp at hyx⟩
      rw [ih hnot]
  | app e1 e2 ih1 ih2 =>
    simp [sFreeVars] at h; simp [sSubst, ih1 h.1, ih2 h.2]
  | let_ y e1 e2 ih1 ih2 =>
    simp [sFreeVars] at h
    simp only [sSubst, ih1 h.1]
    by_cases hyx : (y == x) = true
    · simp [hyx]
    · simp only [ite_eq_right hyx]
      have hnot : x ∉ sFreeVars e2 := fun hmem => by
        have heq := h.2 hmem; subst heq; simp at hyx
      rw [ih2 hnot]
  | cellNew e ih => simp [sSubst, ih h]
  | cellGet e ih => simp [sSubst, ih h]
  | cellSet e1 e2 ih1 ih2 =>
    simp [sFreeVars] at h; simp [sSubst, ih1 h.1, ih2 h.2]
  | withArena e ih => simp [sSubst, ih h]
  | withAlloca e ih => simp [sSubst, ih h]
  | withForeignPtr e1 e2 ih1 ih2 =>
    simp [sFreeVars] at h; simp [sSubst, ih1 h.1, ih2 h.2]
  | arenaAlloc e ih => simp [sSubst, ih h]
  | scopedRead e ih => simp [sSubst, ih h]
  | scopeFrame r e ih => simp [sSubst, ih h]

/-- Helper: every free variable of `sSubst x v e` (when `sFreeVars v = []`) is a free variable of `e` other than `x`. -/
theorem sFreeVars_subst_sub {x v e y} (hv : sFreeVars v = [])
    (hy : y ∈ sFreeVars (sSubst x v e)) : y ∈ sFreeVars e ∧ y ≠ x := by
  induction e with
  | litInt _ | litUnit | loc _ | foreignVal _ | arenaRef _ | scopedRef _ =>
    simp [sSubst, sFreeVars] at hy
  | var z =>
    simp only [sSubst] at hy
    by_cases hzx : (z == x) = true
    · simp [hzx, hv] at hy
    · simp [hzx, sFreeVars] at hy
      subst hy
      exact ⟨by simp [sFreeVars], fun heq => by subst heq; simp at hzx⟩
  | pair e1 e2 ih1 ih2 =>
    simp [sSubst, sFreeVars] at hy ⊢
    cases hy with
    | inl h1 => exact ⟨Or.inl (ih1 h1).1, (ih1 h1).2⟩
    | inr h2 => exact ⟨Or.inr (ih2 h2).1, (ih2 h2).2⟩
  | fst e ih => exact ih hy
  | snd e ih => exact ih hy
  | lam m z τz b ih =>
    simp only [sSubst] at hy
    by_cases hzx : (z == x) = true
    · simp [hzx, sFreeVars] at hy
      have hzeq : z = x := eq_of_beq hzx
      exact ⟨by simp [sFreeVars]; exact hy, fun h => hy.2 (h.trans hzeq.symm)⟩
    · simp [hzx, sFreeVars] at hy ⊢
      have ⟨hm, hne⟩ := ih hy.1
      exact ⟨⟨hm, hy.2⟩, hne⟩
  | app e1 e2 ih1 ih2 =>
    simp [sSubst, sFreeVars] at hy ⊢
    cases hy with
    | inl h1 => exact ⟨Or.inl (ih1 h1).1, (ih1 h1).2⟩
    | inr h2 => exact ⟨Or.inr (ih2 h2).1, (ih2 h2).2⟩
  | let_ z e1 e2 ih1 ih2 =>
    simp only [sSubst, sFreeVars, List.mem_append, List.mem_filter, bne_iff_ne, ne_eq] at hy ⊢
    cases hy with
    | inl h1 => exact ⟨Or.inl (ih1 h1).1, (ih1 h1).2⟩
    | inr h2 =>
      by_cases hzx : (z == x) = true
      · simp [hzx] at h2
        have hzeq : z = x := eq_of_beq hzx
        exact ⟨Or.inr h2, fun h => h2.2 (h.trans hzeq.symm)⟩
      · simp [hzx] at h2
        have ⟨hm, hne⟩ := ih2 h2.1
        exact ⟨Or.inr ⟨hm, h2.2⟩, hne⟩
  | cellNew e ih => exact ih hy
  | cellGet e ih => exact ih hy
  | cellSet e1 e2 ih1 ih2 =>
    simp [sSubst, sFreeVars] at hy ⊢
    cases hy with
    | inl h1 => exact ⟨Or.inl (ih1 h1).1, (ih1 h1).2⟩
    | inr h2 => exact ⟨Or.inr (ih2 h2).1, (ih2 h2).2⟩
  | withArena e ih => exact ih hy
  | withAlloca e ih => exact ih hy
  | withForeignPtr e1 e2 ih1 ih2 =>
    simp [sSubst, sFreeVars] at hy ⊢
    cases hy with
    | inl h1 => exact ⟨Or.inl (ih1 h1).1, (ih1 h1).2⟩
    | inr h2 => exact ⟨Or.inr (ih2 h2).1, (ih2 h2).2⟩
  | arenaAlloc e ih => exact ih hy
  | scopedRead e ih => exact ih hy
  | scopeFrame r e ih => exact ih hy

/-- Every free variable of a well-typed expression is bound in `Γ`. -/
theorem freeVars_in_ctx {Ψ R Γ e τ} (h : SHasType Ψ R Γ e τ) :
    ∀ y ∈ sFreeVars e, ∃ τy, Γ y = some τy := by
  induction h with
  | litInt _ | litUnit | loc _ _ | foreignVal | arenaRef _ | scopedRef _ =>
    intro y hy; simp [sFreeVars] at hy
  | var hx =>
    intro y hy; simp [sFreeVars] at hy; subst hy; exact ⟨_, hx⟩
  | pair _ _ ih1 ih2 | app _ _ ih1 ih2 | cellSet _ _ _ ih1 ih2 | withForeignPtr _ _ _ ih1 ih2 =>
    intro y hy; simp [sFreeVars] at hy
    cases hy with | inl h1 => exact ih1 y h1 | inr h2 => exact ih2 y h2
  | fst _ ih | snd _ ih | cellNew _ _ ih | cellGet _ _ ih
  | withArena _ _ ih | withAlloca _ _ ih | arenaAlloc _ ih | scopedRead _ ih =>
    exact ih
  | scopeFrame _ _ ih =>
    exact ih
  | lam _ _ ih =>
    intro y hy
    simp [sFreeVars] at hy
    have ⟨τy, hgy⟩ := ih y hy.1
    have hne : (y == _) = false := beq_false_of_ne hy.2
    simp [sExtend, hne] at hgy
    exact ⟨τy, hgy⟩
  | let_ _ _ ih1 ih2 =>
    intro y hy
    simp [sFreeVars] at hy
    cases hy with
    | inl h1 => exact ih1 y h1
    | inr h2 =>
      have ⟨τy, hgy⟩ := ih2 y h2.1
      have hne : (y == _) = false := beq_false_of_ne h2.2
      simp [sExtend, hne] at hgy
      exact ⟨τy, hgy⟩

/-- Well-typed closed expressions have no free variables. -/
theorem closed_has_no_freeVars {Ψ R e τ} (ht : SHasType Ψ R sEmptyCtx e τ) :
    sFreeVars e = [] := by
  cases h : sFreeVars e with
  | nil => rfl
  | cons y ys =>
    have ⟨_, hsome⟩ := freeVars_in_ctx ht y (by rw [h]; exact List.mem_cons_self)
    simp [sEmptyCtx] at hsome

/-- Context weakening for closed values. -/
theorem typing_weaken_ctx {Ψ R Γ Γ' e τ}
    (hagree : ∀ x, x ∈ sFreeVars e → Γ x = Γ' x)
    (ht : SHasType Ψ R Γ e τ) : SHasType Ψ R Γ' e τ := by
  induction ht generalizing Γ' with
  | litInt n => exact .litInt n
  | litUnit => exact .litUnit
  | var hx =>
    exact .var (by rw [← hagree _ (by simp [sFreeVars])]; exact hx)
  | loc hl hns => exact .loc hl hns
  | foreignVal => exact .foreignVal
  | arenaRef hr => exact .arenaRef hr
  | scopedRef hr => exact .scopedRef hr
  | pair _ _ ih1 ih2 =>
    exact .pair (ih1 fun x hx => hagree x (by simp [sFreeVars, hx]))
                (ih2 fun x hx => hagree x (by simp [sFreeVars, hx]))
  | fst _ ih => exact .fst (ih hagree)
  | snd _ ih => exact .snd (ih hagree)
  | @lam R₀ Γ₀ m x τx body ret _ hcap ih =>
    refine .lam (ih ?_) ?_
    · intro y hy
      by_cases hyx : y = x
      · subst hyx; simp [sExtend]
      · have hne : (y == x) = false := beq_false_of_ne hyx
        simp [sExtend, hne]
        exact hagree y (by simp [sFreeVars]; exact ⟨hy, hyx⟩)
    · intro hsub
      have ⟨hc1, hc2⟩ := hcap hsub
      refine ⟨fun y hy => ?_, hc2⟩
      have ⟨τy, hgy, hns⟩ := hc1 y hy
      exact ⟨τy, by rw [← hagree y hy]; exact hgy, hns⟩
  | app _ _ ih1 ih2 =>
    exact .app (ih1 fun x hx => hagree x (by simp [sFreeVars, hx]))
               (ih2 fun x hx => hagree x (by simp [sFreeVars, hx]))
  | @let_ R₀ Γ₀ x e1 e2 t1 t2 _ _ ih1 ih2 =>
    refine .let_ (ih1 fun y hy => hagree y (by simp [sFreeVars, hy])) (ih2 ?_)
    intro y hy
    by_cases hyx : y = x
    · subst hyx; simp [sExtend]
    · have hne : (y == x) = false := beq_false_of_ne hyx
      simp [sExtend, hne]
      exact hagree y (by simp [sFreeVars]; exact Or.inr ⟨hy, hyx⟩)
  | cellNew _ hns ih => exact .cellNew (ih hagree) hns
  | cellGet _ hns ih => exact .cellGet (ih hagree) hns
  | cellSet _ _ hns ih1 ih2 =>
    exact .cellSet (ih1 fun x hx => hagree x (by simp [sFreeVars, hx]))
                   (ih2 fun x hx => hagree x (by simp [sFreeVars, hx])) hns
  | withArena _ hns ih => exact .withArena (ih hagree) hns
  | withAlloca _ hns ih => exact .withAlloca (ih hagree) hns
  | withForeignPtr _ _ hns ih1 ih2 =>
    exact .withForeignPtr (ih1 fun x hx => hagree x (by simp [sFreeVars, hx]))
                          (ih2 fun x hx => hagree x (by simp [sFreeVars, hx])) hns
  | arenaAlloc _ ih => exact .arenaAlloc (ih hagree)
  | scopedRead _ ih => exact .scopedRead (ih hagree)
  | scopeFrame _ hns ih => exact .scopeFrame (ih hagree) hns

/-- Substitution lemma for `SHasType`. -/
theorem sSubst_typing {Ψ R Γ x τx v e τ}
    (hv : SIsValue v)
    (htv : SHasType Ψ R sEmptyCtx v τx)
    (hte : SHasType Ψ R (sExtend Γ x τx) e τ) :
    SHasType Ψ R Γ (sSubst x v e) τ := by
  have hvfv : sFreeVars v = [] := closed_has_no_freeVars htv
  generalize hΓ' : sExtend Γ x τx = Γ' at hte
  induction hte generalizing Γ with
  | litInt n => exact .litInt n
  | litUnit => exact .litUnit
  | var hy =>
    rename_i R₀ Γ₀ y τ₀
    subst hΓ'
    simp only [sSubst]
    by_cases hyx : (y == x) = true
    · simp only [hyx]
      simp [sExtend, hyx] at hy
      subst hy
      exact typing_weaken_ctx (fun z hz => by simp [hvfv] at hz) htv
    · simp only [ite_eq_right hyx]
      simp [sExtend, hyx] at hy
      exact .var hy
  | loc hl hns => exact .loc hl hns
  | foreignVal => exact .foreignVal
  | arenaRef hr => exact .arenaRef hr
  | scopedRef hr => exact .scopedRef hr
  | pair _ _ ih1 ih2 => exact .pair (ih1 htv hΓ') (ih2 htv hΓ')
  | fst _ ih => exact .fst (ih htv hΓ')
  | snd _ ih => exact .snd (ih htv hΓ')
  | app _ _ ih1 ih2 => exact .app (ih1 htv hΓ') (ih2 htv hΓ')
  | cellNew _ hns ih => exact .cellNew (ih htv hΓ') hns
  | cellGet _ hns ih => exact .cellGet (ih htv hΓ') hns
  | cellSet _ _ hns ih1 ih2 => exact .cellSet (ih1 htv hΓ') (ih2 htv hΓ') hns
  | withArena _ hns ih => exact .withArena (ih htv hΓ') hns
  | withAlloca _ hns ih => exact .withAlloca (ih htv hΓ') hns
  | withForeignPtr _ _ hns ih1 ih2 => exact .withForeignPtr (ih1 htv hΓ') (ih2 htv hΓ') hns
  | arenaAlloc _ ih => exact .arenaAlloc (ih htv hΓ')
  | scopedRead _ ih => exact .scopedRead (ih htv hΓ')
  | scopeFrame _ hns ih =>
    exact .scopeFrame (ih (typing_weaken_regions (fun _ h => List.mem_cons_of_mem _ h) htv) hΓ') hns
  | let_ _ _ ih1 ih2 =>
    rename_i R₀ Γ₀ y e1 e2 t1 t2 _ _
    subst hΓ'
    simp only [sSubst]
    by_cases hyx : (y == x) = true
    · simp only [hyx, ↓reduceIte]
      have heq : y = x := eq_of_beq hyx
      subst heq
      refine .let_ (ih1 htv rfl) ?_
      apply typing_weaken_ctx _ ‹SHasType Ψ R₀ (sExtend (sExtend Γ y τx) y t1) e2 t2›
      intro z _
      by_cases hzy : z = y
      · subst hzy; simp [sExtend]
      · have hne : (z == y) = false := beq_false_of_ne hzy
        simp [sExtend, hne]
    · simp only [ite_eq_right hyx]
      refine .let_ (ih1 htv rfl) (ih2 htv ?_)
      funext z
      by_cases hzy : z = y
      · subst hzy
        have hne : (z == x) = false := Bool.eq_false_iff.mpr hyx
        simp [sExtend, hne]
      · have hne : (z == y) = false := beq_false_of_ne hzy
        simp [sExtend, hne]
  | lam hbody hcap ih =>
    rename_i R₀ Γ₀ m y τy body ret
    subst hΓ'
    simp only [sSubst]
    by_cases hyx : (y == x) = true
    · simp only [hyx, ↓reduceIte]
      have heq : y = x := eq_of_beq hyx
      subst heq
      refine .lam ?_ ?_
      · apply typing_weaken_ctx _ hbody
        intro z _
        by_cases hzy : z = y
        · subst hzy; simp [sExtend]
        · have hne : (z == y) = false := beq_false_of_ne hzy
          simp [sExtend, hne]
      · intro hsub
        have ⟨hc1, hc2⟩ := hcap hsub
        refine ⟨fun z hz => ?_, hc2⟩
        have ⟨τz, hgz, hns⟩ := hc1 z hz
        simp [sFreeVars] at hz
        have hne : (z == y) = false := beq_false_of_ne hz.2
        simp [sExtend, hne] at hgz
        exact ⟨τz, hgz, hns⟩
    · simp only [ite_eq_right hyx]
      refine .lam (ih htv ?_) ?_
      · funext z
        by_cases hzy : z = y
        · subst hzy; simp [sExtend, Bool.eq_false_iff.mpr hyx]
        · have hne : (z == y) = false := beq_false_of_ne hzy
          simp [sExtend, hne]
      · intro hsub
        have ⟨hc1, hc2⟩ := hcap hsub
        refine ⟨fun z hz => ?_, ?_⟩
        · have hsubfv : z ∈ sFreeVars (sSubst x v (.lam m y τy body)) := by
            simp only [sSubst, ite_eq_right hyx]; exact hz
          have ⟨hmem, hnez⟩ := sFreeVars_subst_sub hvfv hsubfv
          have ⟨τz, hgz, hns⟩ := hc1 z hmem
          have hne : (z == x) = false := beq_false_of_ne hnez
          simp [sExtend, hne] at hgz
          exact ⟨τz, hgz, hns⟩
        · by_cases hxin : x ∈ sFreeVars (.lam m y τy body)
          · have ⟨τz, hgx, hnsx⟩ := hc1 x hxin
            simp [sExtend] at hgx
            subst hgx
            have hvr : exprRegions v = [] := noScoped_value_has_no_regions hv htv hnsx
            exact exprRegions_subst_empty hvr hc2
          · have hnotb : x ∉ sFreeVars body := by
              intro hmem
              apply hxin
              simp [sFreeVars]
              exact ⟨hmem, fun heq => by subst heq; simp at hyx⟩
            rw [sSubst_not_free hnotb]
            exact hc2

/-- Store well-typedness: every heap cell holds a closed value of its `NoScoped` type. -/
def StoreWellTyped (Ψ : SStoreTy) (R : List RegionId) (store : List SExpr) : Prop :=
  store.length = Ψ.length ∧
  ∀ (l : Nat) (τ : STy), Ψ[l]? = some τ → ∃ v, store[l]? = some v ∧ SIsValue v ∧ NoScoped τ ∧ SHasType Ψ R sEmptyCtx v τ

theorem storeWellTyped_retype {Ψ R R' store} (hs : StoreWellTyped Ψ R store) :
    StoreWellTyped Ψ R' store := by
  refine ⟨hs.1, fun l τ h => ?_⟩
  have ⟨v, hvget, hv, hns, htv⟩ := hs.2 l τ h
  have hnr : exprRegions v = [] := noScoped_value_has_no_regions hv htv hns
  exact ⟨v, hvget, hv, hns, value_noRegions_retype hv htv hnr⟩

/-- Well-typed expressions NEVER commit a dangling scoped-pointer access! -/
theorem wellTyped_not_dangling {Ψ R Γ e τ}
    (ht : SHasType Ψ R Γ e τ) : ¬ IsDanglingScopedAccess R e := by
  intro hd
  induction hd generalizing Γ τ with
  | readDangling hnot =>
    cases ht with
    | scopedRead h =>
      cases h with
      | scopedRef hr => exact hnot hr
  | allocDangling hnot =>
    cases ht with
    | arenaAlloc h =>
      cases h with
      | arenaRef hr => exact hnot hr
  | pairL _ ih => cases ht with | pair h1 _ => exact ih h1
  | pairR _ _ ih => cases ht with | pair _ h2 => exact ih h2
  | fst _ ih => cases ht with | fst h => exact ih h
  | snd _ ih => cases ht with | snd h => exact ih h
  | appL _ ih => cases ht with | app h1 _ => exact ih h1
  | appR _ _ ih => cases ht with | app _ h2 => exact ih h2
  | letVal _ ih => cases ht with | let_ h1 _ => exact ih h1
  | cellNew _ ih => cases ht with | cellNew h _ => exact ih h
  | cellGet _ ih => cases ht with | cellGet h _ => exact ih h
  | cellSetL _ ih => cases ht with | cellSet h1 _ _ => exact ih h1
  | cellSetR _ _ ih => cases ht with | cellSet _ h2 _ => exact ih h2
  | withArena _ ih => cases ht with | withArena h _ => exact ih h
  | withAlloca _ ih => cases ht with | withAlloca h _ => exact ih h
  | withForeignL _ ih => cases ht with | withForeignPtr h1 _ _ => exact ih h1
  | withForeignR _ _ ih => cases ht with | withForeignPtr _ h2 _ => exact ih h2
  | arenaAlloc _ ih => cases ht with | arenaAlloc h => exact ih h
  | scopedRead _ ih => cases ht with | scopedRead h => exact ih h
  | scopeFrame _ ih => cases ht with | scopeFrame h _ => exact ih h

/-- Type & Region Safety Preservation across every single `SStep` (zero `sorry`). -/
theorem scoped_preservation {Ψ R st st' e e' τ}
    (hstep : SStep R (st, e) (st', e'))
    (ht : SHasType Ψ R sEmptyCtx e τ)
    (hs : StoreWellTyped Ψ R st.store) :
    ∃ Ψ', SStoreExtends Ψ Ψ' ∧
      SHasType Ψ' R sEmptyCtx e' τ ∧
      StoreWellTyped Ψ' R st'.store := by
  generalize hcfg1 : (st, e) = cfg1 at hstep
  generalize hcfg2 : (st', e') = cfg2 at hstep
  induction hstep generalizing Ψ st st' e e' τ with
  | pairL _ ih =>
    cases hcfg1; cases hcfg2
    cases ht with | pair h1 h2 =>
      have ⟨Ψ', hext, h1', hs'⟩ := ih h1 hs rfl rfl
      exact ⟨Ψ', hext, .pair h1' (typing_weaken_store hext h2), hs'⟩
  | pairR _ _ ih =>
    cases hcfg1; cases hcfg2
    cases ht with | pair h1 h2 =>
      have ⟨Ψ', hext, h2', hs'⟩ := ih h2 hs rfl rfl
      exact ⟨Ψ', hext, .pair (typing_weaken_store hext h1) h2', hs'⟩
  | fstCong _ ih =>
    cases hcfg1; cases hcfg2
    cases ht with | fst h =>
      have ⟨Ψ', hext, h', hs'⟩ := ih h hs rfl rfl
      exact ⟨Ψ', hext, .fst h', hs'⟩
  | fstBeta _ _ =>
    cases hcfg1; cases hcfg2
    cases ht with | fst h => cases h with | pair h1 _ =>
      exact ⟨Ψ, sStoreExtends_refl Ψ, h1, hs⟩
  | sndCong _ ih =>
    cases hcfg1; cases hcfg2
    cases ht with | snd h =>
      have ⟨Ψ', hext, h', hs'⟩ := ih h hs rfl rfl
      exact ⟨Ψ', hext, .snd h', hs'⟩
  | sndBeta _ _ =>
    cases hcfg1; cases hcfg2
    cases ht with | snd h => cases h with | pair _ h2 =>
      exact ⟨Ψ, sStoreExtends_refl Ψ, h2, hs⟩
  | appL _ ih =>
    cases hcfg1; cases hcfg2
    cases ht with | app h1 h2 =>
      have ⟨Ψ', hext, h1', hs'⟩ := ih h1 hs rfl rfl
      exact ⟨Ψ', hext, .app h1' (typing_weaken_store hext h2), hs'⟩
  | appR _ _ ih =>
    cases hcfg1; cases hcfg2
    cases ht with | app h1 h2 =>
      have ⟨Ψ', hext, h2', hs'⟩ := ih h2 hs rfl rfl
      exact ⟨Ψ', hext, .app (typing_weaken_store hext h1) h2', hs'⟩
  | appBeta hv =>
    cases hcfg1; cases hcfg2
    cases ht with | app h1 h2 => cases h1 with | lam hbody _ =>
      exact ⟨Ψ, sStoreExtends_refl Ψ, sSubst_typing hv h2 hbody, hs⟩
  | letCong _ ih =>
    cases hcfg1; cases hcfg2
    cases ht with | let_ h1 h2 =>
      have ⟨Ψ', hext, h1', hs'⟩ := ih h1 hs rfl rfl
      exact ⟨Ψ', hext, .let_ h1' (typing_weaken_store hext h2), hs'⟩
  | letBeta hv =>
    cases hcfg1; cases hcfg2
    cases ht with | let_ h1 h2 =>
      exact ⟨Ψ, sStoreExtends_refl Ψ, sSubst_typing hv h1 h2, hs⟩
  | cellNewCong _ ih =>
    cases hcfg1; cases hcfg2
    cases ht with | cellNew h hns =>
      have ⟨Ψ', hext, h', hs'⟩ := ih h hs rfl rfl
      exact ⟨Ψ', hext, .cellNew h' hns, hs'⟩
  | @cellNewVal R₀ st₀ v hv =>
    cases hcfg1; cases hcfg2
    cases ht with | cellNew htv hns =>
      rename_i τc
      let Ψ' := Ψ ++ [τc]
      have hext : SStoreExtends Ψ Ψ' := sStoreExtends_append Ψ τc
      have hloc : Ψ'[st₀.store.length]? = some τc := by
        rw [hs.1]; simp [Ψ']
      refine ⟨Ψ', hext, .loc hloc hns, ?_, ?_⟩
      · simp [Ψ', hs.1]
      · intro l t hl
        by_cases hlt : l < Ψ.length
        · rw [List.getElem?_append_left hlt] at hl
          have ⟨v0, hv0get, hv0, hns0, htv0⟩ := hs.2 l t hl
          have hlt' : l < st₀.store.length := by rw [hs.1]; exact hlt
          exact ⟨v0, by rw [List.getElem?_append_left hlt']; exact hv0get, hv0, hns0,
                 typing_weaken_store hext htv0⟩
        · have heq : l = Ψ.length := by
            cases Nat.lt_or_ge l Ψ.length with
            | inl hlt2 => exact absurd hlt2 hlt
            | inr hge =>
              cases Nat.eq_or_lt_of_le hge with
              | inl he => exact he.symm
              | inr hgt =>
                have : Ψ'[l]? = none := List.getElem?_eq_none (by simp [Ψ']; omega)
                rw [this] at hl; cases hl
          subst heq
          simp [Ψ'] at hl; subst hl
          exact ⟨v, by rw [← hs.1]; simp, hv, hns, typing_weaken_store hext htv⟩
  | cellGetCong _ ih =>
    cases hcfg1; cases hcfg2
    cases ht with | cellGet h hns =>
      have ⟨Ψ', hext, h', hs'⟩ := ih h hs rfl rfl
      exact ⟨Ψ', hext, .cellGet h' hns, hs'⟩
  | cellGetVal hget =>
    cases hcfg1; cases hcfg2
    cases ht with | cellGet h _ => cases h with | loc hl _ =>
      have ⟨v0, hv0get, _, _, htv0⟩ := hs.2 _ _ hl
      rw [hget] at hv0get; cases hv0get
      exact ⟨Ψ, sStoreExtends_refl Ψ, htv0, hs⟩
  | cellSetL _ ih =>
    cases hcfg1; cases hcfg2
    cases ht with | cellSet h1 h2 hns =>
      have ⟨Ψ', hext, h1', hs'⟩ := ih h1 hs rfl rfl
      exact ⟨Ψ', hext, .cellSet h1' (typing_weaken_store hext h2) hns, hs'⟩
  | cellSetR _ _ ih =>
    cases hcfg1; cases hcfg2
    cases ht with | cellSet h1 h2 hns =>
      have ⟨Ψ', hext, h2', hs'⟩ := ih h2 hs rfl rfl
      exact ⟨Ψ', hext, .cellSet (typing_weaken_store hext h1) h2' hns, hs'⟩
  | @cellSetVal R₀ st₀ l v hv hlt =>
    cases hcfg1; cases hcfg2
    cases ht with | cellSet h1 h2 hns => cases h1 with | loc hl _ =>
      refine ⟨Ψ, sStoreExtends_refl Ψ, .litUnit, ?_, ?_⟩
      · rw [storeUpdate_length]; exact hs.1
      · intro i t hi
        rw [storeUpdate_getElem?]
        by_cases hil : i = l
        · subst hil
          simp only [beq_self_eq_true, Bool.true_and, decide_eq_true hlt, ↓reduceIte]
          rw [hl] at hi; cases hi
          exact ⟨v, rfl, hv, hns, h2⟩
        · have hne : (i == l) = false := beq_false_of_ne hil
          simp only [hne, Bool.false_and, Bool.false_eq_true, ↓reduceIte]
          exact hs.2 i t hi
  | withArenaCong _ ih =>
    cases hcfg1; cases hcfg2
    cases ht with | withArena h hns =>
      have ⟨Ψ', hext, h', hs'⟩ := ih h hs rfl rfl
      exact ⟨Ψ', hext, .withArena h' hns, hs'⟩
  | @withArenaEnter R₀ st₀ m x τx body =>
    cases hcfg1; cases hcfg2
    cases ht with | withArena h hns => cases h with | lam hbody _ =>
      have hbody' := typing_weaken_regions (R' := st₀.nextRegion :: R₀) (fun _ hr => List.mem_cons_of_mem _ hr) hbody
      have hare : SHasType Ψ (st₀.nextRegion :: R₀) sEmptyCtx (.arenaRef st₀.nextRegion) .arena := .arenaRef List.mem_cons_self
      exact ⟨Ψ, sStoreExtends_refl Ψ,
             .scopeFrame (sSubst_typing (.arenaRef st₀.nextRegion) hare hbody') hns, hs⟩
  | withAllocaCong _ ih =>
    cases hcfg1; cases hcfg2
    cases ht with | withAlloca h hns =>
      have ⟨Ψ', hext, h', hs'⟩ := ih h hs rfl rfl
      exact ⟨Ψ', hext, .withAlloca h' hns, hs'⟩
  | @withAllocaEnter R₀ st₀ m x τx body =>
    cases hcfg1; cases hcfg2
    cases ht with | withAlloca h hns => cases h with | lam hbody _ =>
      have hbody' := typing_weaken_regions (R' := st₀.nextRegion :: R₀) (fun _ hr => List.mem_cons_of_mem _ hr) hbody
      have hsc : SHasType Ψ (st₀.nextRegion :: R₀) sEmptyCtx (.scopedRef st₀.nextRegion) .scopedPtr := .scopedRef List.mem_cons_self
      exact ⟨Ψ, sStoreExtends_refl Ψ,
             .scopeFrame (sSubst_typing (.scopedRef st₀.nextRegion) hsc hbody') hns, hs⟩
  | withForeignL _ ih =>
    cases hcfg1; cases hcfg2
    cases ht with | withForeignPtr h1 h2 hns =>
      have ⟨Ψ', hext, h1', hs'⟩ := ih h1 hs rfl rfl
      exact ⟨Ψ', hext, .withForeignPtr h1' (typing_weaken_store hext h2) hns, hs'⟩
  | withForeignR _ _ ih =>
    cases hcfg1; cases hcfg2
    cases ht with | withForeignPtr h1 h2 hns =>
      have ⟨Ψ', hext, h2', hs'⟩ := ih h2 hs rfl rfl
      exact ⟨Ψ', hext, .withForeignPtr (typing_weaken_store hext h1) h2' hns, hs'⟩
  | @withForeignEnter R₀ st₀ id m x τx body =>
    cases hcfg1; cases hcfg2
    cases ht with | withForeignPtr _ h2 hns => cases h2 with | lam hbody _ =>
      have hbody' := typing_weaken_regions (R' := st₀.nextRegion :: R₀) (fun _ hr => List.mem_cons_of_mem _ hr) hbody
      have hsc : SHasType Ψ (st₀.nextRegion :: R₀) sEmptyCtx (.scopedRef st₀.nextRegion) .scopedPtr := .scopedRef List.mem_cons_self
      exact ⟨Ψ, sStoreExtends_refl Ψ,
             .scopeFrame (sSubst_typing (.scopedRef st₀.nextRegion) hsc hbody') hns, hs⟩
  | arenaAllocCong _ ih =>
    cases hcfg1; cases hcfg2
    cases ht with | arenaAlloc h =>
      have ⟨Ψ', hext, h', hs'⟩ := ih h hs rfl rfl
      exact ⟨Ψ', hext, .arenaAlloc h', hs'⟩
  | arenaAllocVal hr =>
    cases hcfg1; cases hcfg2
    cases ht with | arenaAlloc _ =>
      exact ⟨Ψ, sStoreExtends_refl Ψ, .scopedRef hr, hs⟩
  | scopedReadCong _ ih =>
    cases hcfg1; cases hcfg2
    cases ht with | scopedRead h =>
      have ⟨Ψ', hext, h', hs'⟩ := ih h hs rfl rfl
      exact ⟨Ψ', hext, .scopedRead h', hs'⟩
  | scopedReadVal _ =>
    cases hcfg1; cases hcfg2
    cases ht with | scopedRead _ =>
      exact ⟨Ψ, sStoreExtends_refl Ψ, .litInt 0, hs⟩
  | scopeFrameCong _ ih =>
    cases hcfg1; cases hcfg2
    cases ht with | scopeFrame h hns =>
      have ⟨Ψ', hext, h', hs'⟩ := ih h (storeWellTyped_retype hs) rfl rfl
      exact ⟨Ψ', hext, .scopeFrame h' hns, storeWellTyped_retype hs'⟩
  | scopeFrameExit hv =>
    cases hcfg1; cases hcfg2
    cases ht with | scopeFrame htv hns =>
      have hnr : exprRegions _ = [] := noScoped_value_has_no_regions hv htv hns
      exact ⟨Ψ, sStoreExtends_refl Ψ, value_noRegions_retype hv htv hnr, hs⟩

/-- Multi-step helper for `scoped_no_dangling_access`. -/
theorem scoped_no_dangling_steps {R : List RegionId} {c1 c2 : SState × SExpr} {Ψ τ}
    (hms : SSteps R c1 c2)
    (ht1 : SHasType Ψ R sEmptyCtx c1.2 τ)
    (hs1 : StoreWellTyped Ψ R c1.1.store) :
    ¬ IsDanglingScopedAccess R c2.2 := by
  induction hms generalizing Ψ with
  | refl => exact wellTyped_not_dangling ht1
  | step hstep _ ih =>
    have ⟨Ψ', _, ht', hs'⟩ := scoped_preservation hstep ht1 hs1
    exact ih ht' hs'

/-- Multi-step Scoped Region Memory Safety (`¬DanglingScopedAccess`):
    Any well-typed closed program starting with an empty heap and empty region stack
    NEVER reaches `IsDanglingScopedAccess` across any finite execution `SSteps`. -/
theorem scoped_no_dangling_access {e e' : SExpr} {st' : SState} {τ : STy}
    (ht : SHasType [] [] sEmptyCtx e τ)
    (hsteps : SSteps [] ({ store := [], nextRegion := 0 }, e) (st', e')) :
    ¬ IsDanglingScopedAccess [] e' :=
  scoped_no_dangling_steps hsteps ht ⟨rfl, fun _ _ h => by simp at h⟩

/-! ## Part 4: `ImmArray` & `parTabulate` Disjoint-Chunk Data-Race Freedom -/

/-- Exact chunk size formula matching `gs_conc_par_tabulate` in `runtime/runtime/gs_conc.c`:
    `chunk = (n + workers - 1) / workers`. -/
def tabChunkSize (n workers : Nat) : Nat :=
  (n + workers - 1) / workers

/-- Inclusive-lower, exclusive-upper index interval `[lo, hi)` owned by worker `w`. -/
def tabChunkBounds (n workers w : Nat) : Nat × Nat :=
  let c := tabChunkSize n workers
  let lo := w * c
  let hi := if lo + c > n then n else lo + c
  (lo, hi)

/-- Predicate stating that worker `w` owns output index `i`. -/
def WorkerOwnsIndex (n workers w i : Nat) : Prop :=
  let (lo, hi) := tabChunkBounds n workers w
  lo ≤ i ∧ i < hi

/-- Disjointness Theorem: distinct workers `w1 ≠ w2` NEVER write to the same output index! -/
theorem parTabulate_chunks_disjoint {n workers w1 w2 i : Nat}
    (hne : w1 ≠ w2)
    (h1 : WorkerOwnsIndex n workers w1 i)
    (h2 : WorkerOwnsIndex n workers w2 i) : False := by
  simp only [WorkerOwnsIndex, tabChunkBounds] at h1 h2
  generalize tabChunkSize n workers = c at h1 h2
  have h1hi : i < w1 * c + c := by
    split at h1 <;> omega
  have h2hi : i < w2 * c + c := by
    split at h2 <;> omega
  cases Nat.lt_or_gt_of_ne hne with
  | inl hlt =>
    have hstep : (w1 + 1) * c ≤ w2 * c := Nat.mul_le_mul_right c (Nat.succ_le_of_lt hlt)
    rw [Nat.add_mul, Nat.one_mul] at hstep
    omega
  | inr hgt =>
    have hstep : (w2 + 1) * c ≤ w1 * c := Nat.mul_le_mul_right c (Nat.succ_le_of_lt hgt)
    rw [Nat.add_mul, Nat.one_mul] at hstep
    omega

/-- Coverage Theorem: for any `workers > 0` and `i < n`, there exists a worker `w < workers`
    that owns index `i` (so every element of the `ImmArray` is initialized before freeze). -/
theorem parTabulate_chunks_cover {n workers i : Nat}
    (hw : 0 < workers) (hi : i < n) :
    ∃ w < workers, WorkerOwnsIndex n workers w i := by
  have hc_pos : 0 < tabChunkSize n workers := by
    dsimp [tabChunkSize]
    exact Nat.div_pos (by omega) hw
  have hmul : workers * tabChunkSize n workers ≥ n := by
    dsimp [tabChunkSize]
    have hdm := Nat.div_add_mod (n + workers - 1) workers
    have hmod := Nat.mod_lt (n + workers - 1) hw
    omega
  let c := tabChunkSize n workers
  let w := i / c
  have hwc_le : w * c ≤ i := by
    dsimp [w, c]; rw [Nat.mul_comm]; exact Nat.mul_div_le i (tabChunkSize n workers)
  have hi_lt : i < w * c + c := by
    dsimp [w, c]
    have hrem : i % tabChunkSize n workers < tabChunkSize n workers := Nat.mod_lt i hc_pos
    have hdiv : tabChunkSize n workers * (i / tabChunkSize n workers) + i % tabChunkSize n workers = i :=
      Nat.div_add_mod i (tabChunkSize n workers)
    rw [Nat.mul_comm] at hdiv
    omega
  have hw_lt : w < workers := by
    cases Nat.lt_or_ge w workers with
    | inl hlt => exact hlt
    | inr hge =>
      have hle : workers * c ≤ w * c := Nat.mul_le_mul_right c hge
      have hmul' : n ≤ workers * c := hmul
      omega
  refine ⟨w, hw_lt, ?_⟩
  simp only [WorkerOwnsIndex, tabChunkBounds]
  refine ⟨hwc_le, ?_⟩
  split <;> omega

/-- Combined Data-Race Freedom for `parTabulate`:
    1. Output writes by distinct workers are strictly disjoint (`parTabulate_chunks_disjoint`);
    2. Every captured value (including `ImmArray τ` with `SIsSend τ`) satisfies `SIsSend`
       and hence `NoScoped` (zero mutable `Cell` or `ScopedPtr` sharing across workers). -/
theorem parTabulate_data_race_free {n workers : Nat} {capTy elemTy : STy}
    (hcap : SIsSend capTy) (helem : SIsSend elemTy) :
    (∀ w1 w2 i, w1 ≠ w2 → ¬ (WorkerOwnsIndex n workers w1 i ∧ WorkerOwnsIndex n workers w2 i)) ∧
    NoScoped capTy ∧
    SIsSend (.immArray elemTy) :=
  ⟨fun _ _ _ hne ⟨h1, h2⟩ => parTabulate_chunks_disjoint hne h1 h2,
   isSend_implies_noScoped hcap,
   (immArray_send_iff elemTy).mpr helem⟩

end CoreGeisha.Scoped
