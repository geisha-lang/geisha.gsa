import CoreGeisha.Syntax
import CoreGeisha.Typing
import CoreGeisha.Semantics
import CoreGeisha.Soundness
import CoreGeisha.Concurrency

/-!
# Core Geisha: Verified Maranget Pattern-Matrix Exhaustiveness Checker

Machine-checked executable exhaustiveness checker (`checkPatsExhaustive`,
`checkArmsExhaustive`, `checkExprExhaustive`, `checkProgramExhaustive`) mirroring
`findMissingPattern` in `src/infer.gsa`, together with end-to-end soundness proofs
guaranteeing complete elimination of `Trap.matchFailure`:

1. **Matrix & Arm Exhaustiveness Soundness** (`checkPatsExhaustive_sound`,
   `checkArmsExhaustive_sound`): Any pattern matrix / `match` arm list accepted by
   Maranget specialization matches every closed well-typed value of the scrutinee
   type(s).
2. **Dynamic Match-Safety Invariant** (`ExprExhSafe`, `PoolExhSafe`,
   `step_preserves_exhSafe`, `concStep_preserves_exhSafe`): Preserved across
   capture-avoiding substitution, `Step.matchMiss` arm peeling, mutable `Cell`
   heap operations, and concurrent `Task` / `MVar` / `Chan` / `Actor` transitions.
3. **End-to-End `Trap.matchFailure` Elimination** (`exhaustive_no_match_failure`,
   `conc_exhaustive_no_match_failure`): Well-typed exhaustive Core Geisha programs
   never evaluate to `.trap .matchFailure` or fail an actor with `.matchFailure`.
-/

namespace CoreGeisha

/-! ## Part 1: Executable Maranget Pattern-Matrix Exhaustiveness Checker -/

/-- Default recursion fuel for Maranget pattern-matrix specialization. -/
def defaultExhFuel : Nat := 256

/-- Whether a pattern is an irrefutable wildcard (`.`wild` or `.var _`). -/
def isWildPat : Pat → Bool
  | .wild | .var _ => true
  | _ => false

/-- Default-matrix specialization: retain rows whose head column is wildcard. -/
def specializeWild : List (List Pat) → List (List Pat)
  | [] => []
  | [] :: rows => specializeWild rows
  | (p :: rest) :: rows =>
    if isWildPat p then rest :: specializeWild rows
    else specializeWild rows

/-- Literal specialization for `l : Lit` in column 0. -/
def specializeLit (l : Lit) : List (List Pat) → List (List Pat)
  | [] => []
  | [] :: rows => specializeLit l rows
  | (p :: rest) :: rows =>
    match p with
    | .lit l' =>
      if l' == l then rest :: specializeLit l rows
      else specializeLit l rows
    | _ =>
      if isWildPat p then rest :: specializeLit l rows
      else specializeLit l rows

/-- Tuple specialization for `arity`-element tuples in column 0. -/
def specializeTuple (arity : Nat) : List (List Pat) → List (List Pat)
  | [] => []
  | [] :: rows => specializeTuple arity rows
  | (p :: rest) :: rows =>
    match p with
    | .tuple ps =>
      if ps.length == arity then (ps ++ rest) :: specializeTuple arity rows
      else specializeTuple arity rows
    | _ =>
      if isWildPat p then (List.replicate arity Pat.wild ++ rest) :: specializeTuple arity rows
      else specializeTuple arity rows

/-- Constructor specialization for `adt` variant `tag` of `arity` fields in column 0. -/
def specializeCtor (adt : Ident) (tag : Nat) (arity : Nat) : List (List Pat) → List (List Pat)
  | [] => []
  | [] :: rows => specializeCtor adt tag arity rows
  | (p :: rest) :: rows =>
    match p with
    | .ctor adt' tag' ps =>
      if adt' == adt && tag' == tag && ps.length == arity then
        (ps ++ rest) :: specializeCtor adt tag arity rows
      else
        specializeCtor adt tag arity rows
    | _ =>
      if isWildPat p then
        (List.replicate arity Pat.wild ++ rest) :: specializeCtor adt tag arity rows
      else
        specializeCtor adt tag arity rows

/-- Check whether a pattern matrix contains at least one non-empty (`p :: rest`) row. -/
def hasNonEmptyRow : List (List Pat) → Bool
  | [] => false
  | [] :: rows => hasNonEmptyRow rows
  | (_ :: _) :: _ => true

/-- Find the first non-wildcard head pattern among non-empty rows of `matrix`. -/
def firstNonWildHead : List (List Pat) → Option Pat
  | [] => none
  | [] :: rows => firstNonWildHead rows
  | (p :: _) :: rows =>
    if isWildPat p then firstNonWildHead rows else some p

/-- Type-free Maranget pattern-matrix exhaustiveness checker (mirroring
    `findMissingPattern` in `src/infer.gsa`). -/
def checkPatsExhaustive : Nat → AdtEnv → Nat → List (List Pat) → Bool
  | 0, _, 0, matrix => matrix.any List.isEmpty
  | 0, _, _ + 1, _ => false
  | _ + 1, _, 0, matrix => matrix.any List.isEmpty
  | fuel' + 1, Δ, k + 1, matrix =>
    if !hasNonEmptyRow matrix then
      false
    else
      match firstNonWildHead matrix with
      | none =>
        checkPatsExhaustive fuel' Δ k (specializeWild matrix)
      | some .wild | some (.var _) =>
        false
      | some (.lit .unit) =>
        checkPatsExhaustive fuel' Δ k (specializeLit .unit matrix)
      | some (.lit (.bool _)) =>
        checkPatsExhaustive fuel' Δ k (specializeLit (.bool true) matrix) &&
        checkPatsExhaustive fuel' Δ k (specializeLit (.bool false) matrix)
      | some (.lit (.int _)) | some (.lit (.int64 _))
      | some (.lit (.floatBits _)) | some (.lit (.float32Bits _))
      | some (.lit (.char _)) | some (.lit (.str _)) =>
        checkPatsExhaustive fuel' Δ k (specializeWild matrix)
      | some (.tuple ps) =>
        checkPatsExhaustive fuel' Δ (ps.length + k) (specializeTuple ps.length matrix)
      | some (.ctor adt _ _) =>
        match Δ adt with
        | none => false
        | some defn =>
          defn.variants.all fun v =>
            checkPatsExhaustive fuel' Δ (v.fields.length + k)
              (specializeCtor adt v.tag v.fields.length matrix)

/-- Check that a list of `match` arms is exhaustive under `Δ`. -/
def checkArmsExhaustive (Δ : AdtEnv) (arms : List (Pat × Expr)) : Bool :=
  checkPatsExhaustive defaultExhFuel Δ 1 (arms.map fun a => [a.1])

/- Syntactic expression exhaustiveness checker:
   rejects `.trap .matchFailure` and requires every `.match_` to be non-empty
   and accepted by `checkArmsExhaustive Δ`. -/
mutual
def checkExprExhaustive (Δ : AdtEnv) : Expr → Bool
  | .lit _ => true
  | .var _ => true
  | .loc _ => true
  | .taskRef _ => true
  | .syncRef _ _ => true
  | .tuple es => checkExprListExhaustive Δ es
  | .block es => checkExprListExhaustive Δ es
  | .lam _ _ _ body => checkExprExhaustive Δ body
  | .apply fn args => checkExprExhaustive Δ fn && checkExprListExhaustive Δ args
  | .applyDir _ args => checkExprListExhaustive Δ args
  | .bin _ e1 e2 => checkExprExhaustive Δ e1 && checkExprExhaustive Δ e2
  | .un _ e => checkExprExhaustive Δ e
  | .let_ _ e1 e2 => checkExprExhaustive Δ e1 && checkExprExhaustive Δ e2
  | .if_ c t e => checkExprExhaustive Δ c && checkExprExhaustive Δ t && checkExprExhaustive Δ e
  | .while_ c b => checkExprExhaustive Δ c && checkExprExhaustive Δ b
  | .match_ scrut arms =>
    !arms.isEmpty &&
    checkArmsExhaustive Δ arms &&
    checkExprExhaustive Δ scrut &&
    checkArmsBodyExhaustive Δ arms
  | .makeData _ _ es => checkExprListExhaustive Δ es
  | .getTag e => checkExprExhaustive Δ e
  | .cellNew e => checkExprExhaustive Δ e
  | .cellGet e => checkExprExhaustive Δ e
  | .cellSet e1 e2 => checkExprExhaustive Δ e1 && checkExprExhaustive Δ e2
  | .spawn e => checkExprExhaustive Δ e
  | .await e => checkExprExhaustive Δ e
  | .concPrim _ args => checkExprListExhaustive Δ args
  | .trap .divByZero => true
  | .trap .hostTrap => true
  | .trap .matchFailure => false

def checkExprListExhaustive (Δ : AdtEnv) : List Expr → Bool
  | [] => true
  | e :: es => checkExprExhaustive Δ e && checkExprListExhaustive Δ es

def checkArmsBodyExhaustive (Δ : AdtEnv) : List (Pat × Expr) → Bool
  | [] => true
  | (_, body) :: rest => checkExprExhaustive Δ body && checkArmsBodyExhaustive Δ rest
end

/-- Check that every top-level function definition in `funs` has exhaustive `match` expressions. -/
def checkProgramExhaustive (Δ : AdtEnv) (funs : List FunDef) : Except String Unit :=
  match funs with
  | [] => .ok ()
  | fd :: rest =>
    if checkExprExhaustive Δ fd.body then
      checkProgramExhaustive Δ rest
    else
      .error s!"non-exhaustive pattern match in function '{fd.name}'"

/-! ## Part 2: Matrix Soundness Proof (`checkPatsExhaustive_sound` & `checkArmsExhaustive_sound`) -/

private theorem lit_beq_self (l : Lit) : (l == l) = true := by
  cases l with
  | int a => exact beq_self_eq_true a
  | int64 a => exact beq_self_eq_true a
  | floatBits a => exact beq_self_eq_true a
  | float32Bits a => exact beq_self_eq_true a
  | bool b => exact beq_self_eq_true b
  | char c => exact beq_self_eq_true c
  | str s => exact beq_self_eq_true s
  | unit => rfl

private theorem lit_eq_of_beq {l1 l2 : Lit} (h : (l1 == l2) = true) : l1 = l2 := by
  cases l1 <;> cases l2 <;> try cases h
  · rename_i a1 a2; have heq : (a1 == a2) = true := h; rw [beq_iff_eq.mp heq]
  · rename_i a1 a2; have heq : (a1 == a2) = true := h; rw [beq_iff_eq.mp heq]
  · rename_i a1 a2; have heq : (a1 == a2) = true := h; rw [beq_iff_eq.mp heq]
  · rename_i a1 a2; have heq : (a1 == a2) = true := h; rw [beq_iff_eq.mp heq]
  · rename_i a1 a2; have heq : (a1 == a2) = true := h; rw [beq_iff_eq.mp heq]
  · rename_i a1 a2; have heq : (a1 == a2) = true := h; rw [beq_iff_eq.mp heq]
  · rename_i a1 a2; have heq : (a1 == a2) = true := h; rw [beq_iff_eq.mp heq]
  · rfl

private theorem find?_pred_of_some {α : Type} {p : α → Bool} {xs : List α} {a : α}
    (h : xs.find? p = some a) : a ∈ xs ∧ p a = true := by
  induction xs with
  | nil => simp at h
  | cons x rest ih =>
    simp only [List.find?] at h
    cases hp : p x with
    | true =>
      rw [hp] at h
      cases h
      exact ⟨List.mem_cons_self .., hp⟩
    | false =>
      rw [hp] at h
      rcases ih h with ⟨hm, hpa⟩
      exact ⟨List.mem_cons_of_mem _ hm, hpa⟩

theorem lookupVariant_mem_variants {Δ : AdtEnv} {adt : Ident} {defn : AdtDef}
    {tag : Nat} {flds : List Ty}
    (hΔ : Δ adt = some defn) (hlv : lookupVariant Δ adt tag = some flds) :
    ∃ vi ∈ defn.variants, vi.tag = tag ∧ vi.fields = flds := by
  simp only [lookupVariant, hΔ] at hlv
  cases hfind : defn.variants.find? (fun v => v.tag == tag) with
  | none => rw [hfind] at hlv; cases hlv
  | some vi =>
    rw [hfind] at hlv
    cases hlv
    rcases find?_pred_of_some hfind with ⟨hmem, htag⟩
    exact ⟨vi, hmem, beq_iff_eq.mp htag, rfl⟩

theorem canonical_void {Δ : AdtEnv} {Φ : FunEnv} {Ψ : StoreTy} {Θ : TaskTy} {v : Expr}
    (ht : HasType Δ Φ Ψ Θ emptyCtx v .void) (hv : IsValue v) :
    v = .lit .unit := by
  cases hv with
  | lit l => cases ht with | lit hl => cases hl; rfl
  | loc _ => cases ht
  | taskRef _ => cases ht
  | syncRef _ _ => cases ht with | syncRef hsr => cases hsr
  | lam _ _ _ _ => cases ht
  | tuple _ => cases ht
  | makeData _ _ _ => cases ht

theorem canonical_tuple {Δ : AdtEnv} {Φ : FunEnv} {Ψ : StoreTy} {Θ : TaskTy}
    {v : Expr} {τs : List Ty}
    (ht : HasType Δ Φ Ψ Θ emptyCtx v (.tuple τs)) (hv : IsValue v) :
    ∃ vs, v = .tuple vs ∧ HasTypes Δ Φ Ψ Θ emptyCtx vs τs ∧ (∀ u ∈ vs, IsValue u) := by
  cases hv with
  | lit _ => cases ht with | lit hl => cases hl
  | loc _ => cases ht
  | taskRef _ => cases ht
  | syncRef _ _ => cases ht with | syncRef hsr => cases hsr
  | lam _ _ _ _ => cases ht
  | tuple hvs =>
    cases ht with
    | tuple hts => exact ⟨_, rfl, hts, hvs⟩
  | makeData _ _ _ => cases ht

theorem canonical_adt_typed {Δ : AdtEnv} {Φ : FunEnv} {Ψ : StoreTy} {Θ : TaskTy}
    {v : Expr} {adt : Ident}
    (ht : HasType Δ Φ Ψ Θ emptyCtx v (.adt adt)) (hv : IsValue v) :
    ∃ tag flds vs,
      v = .makeData adt tag vs ∧
      lookupVariant Δ adt tag = some flds ∧
      HasTypes Δ Φ Ψ Θ emptyCtx vs flds ∧
      (∀ u ∈ vs, IsValue u) := by
  rcases canonical_adt ht hv with ⟨tag, vs, rfl, hvs⟩
  cases ht with
  | makeData hlv hts => exact ⟨tag, _, vs, rfl, hlv, hts, hvs⟩

theorem hasTypes_append {Δ : AdtEnv} {Φ : FunEnv} {Ψ : StoreTy} {Θ : TaskTy} {Γ : Ctx}
    {es1 es2 : List Expr} {τs1 τs2 : List Ty}
    (h1 : HasTypes Δ Φ Ψ Θ Γ es1 τs1) (h2 : HasTypes Δ Φ Ψ Θ Γ es2 τs2) :
    HasTypes Δ Φ Ψ Θ Γ (es1 ++ es2) (τs1 ++ τs2) := by
  induction es1 generalizing τs1 with
  | nil => cases h1; exact h2
  | cons _ _ ih =>
    cases h1 with
    | cons he hrest => exact .cons he (ih hrest)

theorem patsHaveType_length {Δ : AdtEnv} {ps : List Pat} {τs : List Ty} {bs : List (Ident × Ty)}
    (h : PatsHaveType Δ ps τs bs) : ps.length = τs.length := by
  induction ps generalizing τs bs with
  | nil => cases h; rfl
  | cons _ _ ih =>
    cases h with
    | cons _ hrest => simp [ih hrest]

theorem patsHaveType_append {Δ : AdtEnv} {ps1 ps2 : List Pat} {τs1 τs2 : List Ty}
    {bs1 bs2 : List (Ident × Ty)}
    (h1 : PatsHaveType Δ ps1 τs1 bs1) (h2 : PatsHaveType Δ ps2 τs2 bs2) :
    PatsHaveType Δ (ps1 ++ ps2) (τs1 ++ τs2) (bs1 ++ bs2) := by
  induction ps1 generalizing τs1 bs1 with
  | nil => cases h1; simpa using h2
  | cons p ps ih =>
    cases h1 with
    | @cons _ _ τ τs b1 bRest hp hrest =>
      have hcons : PatsHaveType Δ (p :: (ps ++ ps2)) (τ :: (τs ++ τs2)) (b1 ++ (bRest ++ bs2)) :=
        .cons hp (ih hrest)
      simpa [List.append_assoc] using hcons

theorem patsHaveType_replicate_wild (Δ : AdtEnv) :
    (τs : List Ty) → PatsHaveType Δ (List.replicate τs.length Pat.wild) τs []
  | [] => .nil
  | τ :: τs => by
    simp only [List.length_cons, List.replicate_succ]
    exact .cons (.wild τ) (patsHaveType_replicate_wild Δ τs)

theorem firstNonWildHead_some {matrix : List (List Pat)} {p : Pat}
    (h : firstNonWildHead matrix = some p) :
    isWildPat p = false ∧ ∃ rest, (p :: rest) ∈ matrix := by
  induction matrix with
  | nil => simp [firstNonWildHead] at h
  | cons row rows ih =>
    cases row with
    | nil =>
      simp only [firstNonWildHead] at h
      rcases ih h with ⟨hnw, rest, hmem⟩
      exact ⟨hnw, rest, List.mem_cons_of_mem _ hmem⟩
    | cons q qs =>
      simp only [firstNonWildHead] at h
      cases hq : isWildPat q with
      | true =>
        rw [hq] at h
        simp only [↓reduceIte] at h
        rcases ih h with ⟨hnw, rest, hmem⟩
        exact ⟨hnw, rest, List.mem_cons_of_mem _ hmem⟩
      | false =>
        rw [hq] at h
        simp only [Bool.false_eq_true, ↓reduceIte, Option.some.injEq] at h
        subst h
        exact ⟨hq, qs, List.mem_cons_self ..⟩

theorem isWildPat_matchPat {p : Pat} (hw : isWildPat p = true) (v : Expr) :
    ∃ b, matchPat p v = some b := by
  cases p <;> simp [isWildPat] at hw
  · exact ⟨[], rfl⟩
  · exact ⟨[(_, v)], rfl⟩

theorem matchPats_replicate_wild :
    (vs : List Expr) → matchPats (List.replicate vs.length Pat.wild) vs = some []
  | [] => rfl
  | v :: vs => by
    simp only [List.length_cons, List.replicate_succ, matchPats, matchPat,
      matchPats_replicate_wild vs]
    rfl

theorem matchPats_append_split {ps1 ps2 : List Pat} {vs1 vs2 : List Expr}
    (hlen : ps1.length = vs1.length)
    (hm : (matchPats (ps1 ++ ps2) (vs1 ++ vs2)).isSome = true) :
    ∃ b1 b2, matchPats ps1 vs1 = some b1 ∧ matchPats ps2 vs2 = some b2 := by
  induction ps1 generalizing vs1 with
  | nil =>
    cases vs1 with
    | nil =>
      simp only [List.nil_append] at hm
      cases h2 : matchPats ps2 vs2 with
      | none => rw [h2] at hm; simp at hm
      | some b2 => exact ⟨[], b2, rfl, rfl⟩
    | cons _ _ => simp at hlen
  | cons p rest ih =>
    cases vs1 with
    | nil => simp at hlen
    | cons v vrest =>
      simp only [List.length_cons, Nat.add_right_cancel_iff] at hlen
      simp only [List.cons_append, matchPats] at hm
      cases h1 : matchPat p v with
      | none => rw [h1] at hm; simp at hm
      | some b1 =>
        rw [h1] at hm
        cases h2 : matchPats (rest ++ ps2) (vrest ++ vs2) with
        | none => rw [h2] at hm; simp at hm
        | some bRest =>
          rcases ih hlen (by simp [h2]) with ⟨b1', b2, hb1', hb2⟩
          exact ⟨b1 ++ b1', b2, by simp [matchPats, h1, hb1'], hb2⟩

/-! ### Specialization Membership Characterizations -/

theorem mem_specializeWild {matrix : List (List Pat)} {row' : List Pat}
    (h : row' ∈ specializeWild matrix) :
    ∃ p, isWildPat p = true ∧ (p :: row') ∈ matrix := by
  induction matrix with
  | nil => simp [specializeWild] at h
  | cons row rows ih =>
    cases row with
    | nil =>
      rcases ih h with ⟨p, hw, hm⟩
      exact ⟨p, hw, List.mem_cons_of_mem _ hm⟩
    | cons p rest =>
      simp only [specializeWild] at h
      split at h
      · rename_i hw
        rcases List.mem_cons.mp h with rfl | htail
        · exact ⟨p, hw, List.mem_cons_self ..⟩
        · rcases ih htail with ⟨q, hqw, hm⟩
          exact ⟨q, hqw, List.mem_cons_of_mem _ hm⟩
      · rcases ih h with ⟨q, hqw, hm⟩
        exact ⟨q, hqw, List.mem_cons_of_mem _ hm⟩

theorem mem_specializeLit {l : Lit} {matrix : List (List Pat)} {row' : List Pat}
    (h : row' ∈ specializeLit l matrix) :
    ∃ p, (p :: row') ∈ matrix ∧ (p = .lit l ∨ isWildPat p = true) := by
  induction matrix with
  | nil => simp [specializeLit] at h
  | cons row rows ih =>
    cases row with
    | nil =>
      rcases ih h with ⟨p, hm, hp⟩
      exact ⟨p, List.mem_cons_of_mem _ hm, hp⟩
    | cons p rest =>
      simp only [specializeLit] at h
      cases p with
      | lit l' =>
        dsimp only at h
        split at h
        · rename_i heq
          rcases List.mem_cons.mp h with rfl | htail
          · exact ⟨.lit l', List.mem_cons_self .., Or.inl (by rw [lit_eq_of_beq heq])⟩
          · rcases ih htail with ⟨q, hm, hq⟩
            exact ⟨q, List.mem_cons_of_mem _ hm, hq⟩
        · rcases ih h with ⟨q, hm, hq⟩
          exact ⟨q, List.mem_cons_of_mem _ hm, hq⟩
      | wild =>
        simp only [isWildPat, ↓reduceIte] at h
        rcases List.mem_cons.mp h with rfl | htail
        · exact ⟨.wild, List.mem_cons_self .., Or.inr rfl⟩
        · rcases ih htail with ⟨q, hm, hq⟩
          exact ⟨q, List.mem_cons_of_mem _ hm, hq⟩
      | var x =>
        simp only [isWildPat, ↓reduceIte] at h
        rcases List.mem_cons.mp h with rfl | htail
        · exact ⟨.var x, List.mem_cons_self .., Or.inr rfl⟩
        · rcases ih htail with ⟨q, hm, hq⟩
          exact ⟨q, List.mem_cons_of_mem _ hm, hq⟩
      | tuple _ =>
        simp only [isWildPat, Bool.false_eq_true, ↓reduceIte] at h
        rcases ih h with ⟨q, hm, hq⟩
        exact ⟨q, List.mem_cons_of_mem _ hm, hq⟩
      | ctor _ _ _ =>
        simp only [isWildPat, Bool.false_eq_true, ↓reduceIte] at h
        rcases ih h with ⟨q, hm, hq⟩
        exact ⟨q, List.mem_cons_of_mem _ hm, hq⟩

theorem mem_specializeTuple {arity : Nat} {matrix : List (List Pat)} {row' : List Pat}
    (h : row' ∈ specializeTuple arity matrix) :
    (∃ ps rest, (.tuple ps :: rest) ∈ matrix ∧ ps.length = arity ∧ row' = ps ++ rest) ∨
    (∃ p rest, (p :: rest) ∈ matrix ∧ isWildPat p = true ∧ row' = List.replicate arity Pat.wild ++ rest) := by
  induction matrix with
  | nil => simp [specializeTuple] at h
  | cons row rows ih =>
    cases row with
    | nil =>
      rcases ih h with ⟨ps, rest, hm, hlen, rfl⟩ | ⟨p, rest, hm, hw, rfl⟩
      · exact Or.inl ⟨ps, rest, List.mem_cons_of_mem _ hm, hlen, rfl⟩
      · exact Or.inr ⟨p, rest, List.mem_cons_of_mem _ hm, hw, rfl⟩
    | cons p rest =>
      simp only [specializeTuple] at h
      cases p with
      | tuple ps =>
        dsimp only at h
        split at h
        · rename_i heq
          rcases List.mem_cons.mp h with rfl | htail
          · exact Or.inl ⟨ps, rest, List.mem_cons_self .., beq_iff_eq.mp heq, rfl⟩
          · rcases ih htail with ⟨ps', r', hm, hl, rfl⟩ | ⟨q, r', hm, hw, rfl⟩
            · exact Or.inl ⟨ps', r', List.mem_cons_of_mem _ hm, hl, rfl⟩
            · exact Or.inr ⟨q, r', List.mem_cons_of_mem _ hm, hw, rfl⟩
        · rcases ih h with ⟨ps', r', hm, hl, rfl⟩ | ⟨q, r', hm, hw, rfl⟩
          · exact Or.inl ⟨ps', r', List.mem_cons_of_mem _ hm, hl, rfl⟩
          · exact Or.inr ⟨q, r', List.mem_cons_of_mem _ hm, hw, rfl⟩
      | wild =>
        simp only [isWildPat, ↓reduceIte] at h
        rcases List.mem_cons.mp h with rfl | htail
        · exact Or.inr ⟨.wild, rest, List.mem_cons_self .., rfl, rfl⟩
        · rcases ih htail with ⟨ps', r', hm, hl, rfl⟩ | ⟨q, r', hm, hw, rfl⟩
          · exact Or.inl ⟨ps', r', List.mem_cons_of_mem _ hm, hl, rfl⟩
          · exact Or.inr ⟨q, r', List.mem_cons_of_mem _ hm, hw, rfl⟩
      | var x =>
        simp only [isWildPat, ↓reduceIte] at h
        rcases List.mem_cons.mp h with rfl | htail
        · exact Or.inr ⟨.var x, rest, List.mem_cons_self .., rfl, rfl⟩
        · rcases ih htail with ⟨ps', r', hm, hl, rfl⟩ | ⟨q, r', hm, hw, rfl⟩
          · exact Or.inl ⟨ps', r', List.mem_cons_of_mem _ hm, hl, rfl⟩
          · exact Or.inr ⟨q, r', List.mem_cons_of_mem _ hm, hw, rfl⟩
      | lit _ =>
        simp only [isWildPat, Bool.false_eq_true, ↓reduceIte] at h
        rcases ih h with ⟨ps', r', hm, hl, rfl⟩ | ⟨q, r', hm, hw, rfl⟩
        · exact Or.inl ⟨ps', r', List.mem_cons_of_mem _ hm, hl, rfl⟩
        · exact Or.inr ⟨q, r', List.mem_cons_of_mem _ hm, hw, rfl⟩
      | ctor _ _ _ =>
        simp only [isWildPat, Bool.false_eq_true, ↓reduceIte] at h
        rcases ih h with ⟨ps', r', hm, hl, rfl⟩ | ⟨q, r', hm, hw, rfl⟩
        · exact Or.inl ⟨ps', r', List.mem_cons_of_mem _ hm, hl, rfl⟩
        · exact Or.inr ⟨q, r', List.mem_cons_of_mem _ hm, hw, rfl⟩

theorem mem_specializeCtor {adt : Ident} {tag arity : Nat} {matrix : List (List Pat)} {row' : List Pat}
    (h : row' ∈ specializeCtor adt tag arity matrix) :
    (∃ ps rest, (.ctor adt tag ps :: rest) ∈ matrix ∧ ps.length = arity ∧ row' = ps ++ rest) ∨
    (∃ p rest, (p :: rest) ∈ matrix ∧ isWildPat p = true ∧ row' = List.replicate arity Pat.wild ++ rest) := by
  induction matrix with
  | nil => simp [specializeCtor] at h
  | cons row rows ih =>
    cases row with
    | nil =>
      rcases ih h with ⟨ps, rest, hm, hlen, rfl⟩ | ⟨p, rest, hm, hw, rfl⟩
      · exact Or.inl ⟨ps, rest, List.mem_cons_of_mem _ hm, hlen, rfl⟩
      · exact Or.inr ⟨p, rest, List.mem_cons_of_mem _ hm, hw, rfl⟩
    | cons p rest =>
      simp only [specializeCtor] at h
      cases p with
      | ctor adt' tag' ps =>
        dsimp only at h
        split at h
        · rename_i hcond
          simp only [Bool.and_eq_true, beq_iff_eq] at hcond
          rcases hcond with ⟨⟨rfl, rfl⟩, hlen⟩
          rcases List.mem_cons.mp h with rfl | htail
          · exact Or.inl ⟨ps, rest, List.mem_cons_self .., hlen, rfl⟩
          · rcases ih htail with ⟨ps', r', hm, hl, rfl⟩ | ⟨q, r', hm, hw, rfl⟩
            · exact Or.inl ⟨ps', r', List.mem_cons_of_mem _ hm, hl, rfl⟩
            · exact Or.inr ⟨q, r', List.mem_cons_of_mem _ hm, hw, rfl⟩
        · rcases ih h with ⟨ps', r', hm, hl, rfl⟩ | ⟨q, r', hm, hw, rfl⟩
          · exact Or.inl ⟨ps', r', List.mem_cons_of_mem _ hm, hl, rfl⟩
          · exact Or.inr ⟨q, r', List.mem_cons_of_mem _ hm, hw, rfl⟩
      | wild =>
        simp only [isWildPat, ↓reduceIte] at h
        rcases List.mem_cons.mp h with rfl | htail
        · exact Or.inr ⟨.wild, rest, List.mem_cons_self .., rfl, rfl⟩
        · rcases ih htail with ⟨ps', r', hm, hl, rfl⟩ | ⟨q, r', hm, hw, rfl⟩
          · exact Or.inl ⟨ps', r', List.mem_cons_of_mem _ hm, hl, rfl⟩
          · exact Or.inr ⟨q, r', List.mem_cons_of_mem _ hm, hw, rfl⟩
      | var x =>
        simp only [isWildPat, ↓reduceIte] at h
        rcases List.mem_cons.mp h with rfl | htail
        · exact Or.inr ⟨.var x, rest, List.mem_cons_self .., rfl, rfl⟩
        · rcases ih htail with ⟨ps', r', hm, hl, rfl⟩ | ⟨q, r', hm, hw, rfl⟩
          · exact Or.inl ⟨ps', r', List.mem_cons_of_mem _ hm, hl, rfl⟩
          · exact Or.inr ⟨q, r', List.mem_cons_of_mem _ hm, hw, rfl⟩
      | lit _ =>
        simp only [isWildPat, Bool.false_eq_true, ↓reduceIte] at h
        rcases ih h with ⟨ps', r', hm, hl, rfl⟩ | ⟨q, r', hm, hw, rfl⟩
        · exact Or.inl ⟨ps', r', List.mem_cons_of_mem _ hm, hl, rfl⟩
        · exact Or.inr ⟨q, r', List.mem_cons_of_mem _ hm, hw, rfl⟩
      | tuple _ =>
        simp only [isWildPat, Bool.false_eq_true, ↓reduceIte] at h
        rcases ih h with ⟨ps', r', hm, hl, rfl⟩ | ⟨q, r', hm, hw, rfl⟩
        · exact Or.inl ⟨ps', r', List.mem_cons_of_mem _ hm, hl, rfl⟩
        · exact Or.inr ⟨q, r', List.mem_cons_of_mem _ hm, hw, rfl⟩

/-! ### Main Matrix & Arm Exhaustiveness Soundness Theorems -/

/-- **Maranget Pattern-Matrix Soundness**: If `checkPatsExhaustive` accepts `matrix`
    at arity `τs.length`, every row in `matrix` is well-typed against `τs`, and `vs`
    is a list of closed values of types `τs`, then at least one row of `matrix`
    matches `vs`. -/
theorem checkPatsExhaustive_sound {fuel : Nat} {Δ : AdtEnv} {Φ : FunEnv} {Ψ : StoreTy} {Θ : TaskTy}
    {τs : List Ty} {matrix : List (List Pat)} {vs : List Expr}
    (hexh : checkPatsExhaustive fuel Δ τs.length matrix = true)
    (hmat : ∀ row ∈ matrix, ∃ bs, PatsHaveType Δ row τs bs)
    (hvs_ty : HasTypes Δ Φ Ψ Θ emptyCtx vs τs)
    (hvs_val : ∀ v ∈ vs, IsValue v) :
    ∃ row ∈ matrix, (matchPats row vs).isSome = true := by
  induction fuel generalizing τs matrix vs with
  | zero =>
    cases τs with
    | nil =>
      cases hvs_ty
      unfold checkPatsExhaustive at hexh
      simp only [List.length_nil, List.any_eq_true] at hexh
      rcases hexh with ⟨row, hmem, hempty⟩
      have hnil : row = [] := List.isEmpty_iff.mp hempty
      subst hnil
      exact ⟨[], hmem, rfl⟩
    | cons _ _ =>
      unfold checkPatsExhaustive at hexh
      simp at hexh
  | succ fuel' ih =>
    cases τs with
    | nil =>
      cases hvs_ty
      unfold checkPatsExhaustive at hexh
      simp only [List.length_nil, List.any_eq_true] at hexh
      rcases hexh with ⟨row, hmem, hempty⟩
      have hnil : row = [] := List.isEmpty_iff.mp hempty
      subst hnil
      exact ⟨[], hmem, rfl⟩
    | cons τ0 restTys =>
      cases hvs_ty with
      | @cons _ v0 restVs _ _ hv0_ty hrest_ty =>
        have hv0_val : IsValue v0 := hvs_val v0 (List.mem_cons_self ..)
        have hrest_val : ∀ u ∈ restVs, IsValue u :=
          fun u hu => hvs_val u (List.mem_cons_of_mem _ hu)
        unfold checkPatsExhaustive at hexh
        simp only [List.length_cons] at hexh
        cases hne : hasNonEmptyRow matrix with
        | false => simp [hne] at hexh
        | true =>
          simp only [hne, Bool.not_true, Bool.false_eq_true, ↓reduceIte] at hexh
          -- Helper for wildcard specialization (`none`, `.int`, `.str`)
          have wildCase :
              checkPatsExhaustive fuel' Δ restTys.length (specializeWild matrix) = true →
              ∃ row ∈ matrix, (matchPats row (v0 :: restVs)).isSome = true := by
            intro hexhW
            have hmatW : ∀ row' ∈ specializeWild matrix, ∃ bs', PatsHaveType Δ row' restTys bs' := by
              intro row' hmem'
              rcases mem_specializeWild hmem' with ⟨p, _, hp_mem⟩
              rcases hmat (p :: row') hp_mem with ⟨_, hps⟩
              cases hps with
              | cons _ hrest_ps => exact ⟨_, hrest_ps⟩
            rcases ih hexhW hmatW hrest_ty hrest_val with ⟨row', hmem', hmatch'⟩
            rcases mem_specializeWild hmem' with ⟨p, hpw, hp_mem⟩
            rcases isWildPat_matchPat hpw v0 with ⟨b1, hb1⟩
            cases hmp : matchPats row' restVs with
            | none => rw [hmp] at hmatch'; simp at hmatch'
            | some b2 =>
              exact ⟨p :: row', hp_mem, by simp [matchPats, hb1, hmp]⟩
          -- Helper for literal specialization (`.unit`, `.bool b`)
          have litCase : ∀ (l : Lit),
              v0 = .lit l →
              checkPatsExhaustive fuel' Δ restTys.length (specializeLit l matrix) = true →
              ∃ row ∈ matrix, (matchPats row (v0 :: restVs)).isSome = true := by
            intro l hv0_eq hexhL
            subst hv0_eq
            have hmatL : ∀ row' ∈ specializeLit l matrix, ∃ bs', PatsHaveType Δ row' restTys bs' := by
              intro row' hmem'
              rcases mem_specializeLit hmem' with ⟨p, hp_mem, _⟩
              rcases hmat (p :: row') hp_mem with ⟨_, hps⟩
              cases hps with
              | cons _ hrest_ps => exact ⟨_, hrest_ps⟩
            rcases ih hexhL hmatL hrest_ty hrest_val with ⟨row', hmem', hmatch'⟩
            rcases mem_specializeLit hmem' with ⟨p, hp_mem, hp_kind⟩
            cases hmp : matchPats row' restVs with
            | none => rw [hmp] at hmatch'; simp at hmatch'
            | some b2 =>
              rcases hp_kind with rfl | hpw
              · exact ⟨.lit l :: row', hp_mem, by simp [matchPats, matchPat, lit_beq_self, hmp]⟩
              · rcases isWildPat_matchPat hpw (.lit l) with ⟨b1, hb1⟩
                exact ⟨p :: row', hp_mem, by simp [matchPats, hb1, hmp]⟩
          cases hhead : firstNonWildHead matrix with
          | none =>
            rw [hhead] at hexh
            exact wildCase hexh
          | some p0 =>
            rw [hhead] at hexh
            rcases firstNonWildHead_some hhead with ⟨hp0_nw, rest0, hp0_mem⟩
            cases p0 with
            | wild => simp [isWildPat] at hp0_nw
            | var _ => simp [isWildPat] at hp0_nw
            | lit l0 =>
              cases l0 with
              | unit =>
                rcases hmat (.lit .unit :: rest0) hp0_mem with ⟨_, hps0⟩
                cases hps0 with
                | cons hp0 _ =>
                  cases hp0 with
                  | lit hl0 =>
                    cases hl0
                    exact litCase .unit (canonical_void hv0_ty hv0_val) hexh
              | bool b0 =>
                simp only [Bool.and_eq_true] at hexh
                rcases hmat (.lit (.bool b0) :: rest0) hp0_mem with ⟨_, hps0⟩
                cases hps0 with
                | cons hp0 _ =>
                  cases hp0 with
                  | lit hl0 =>
                    cases hl0
                    rcases canonical_bool hv0_ty hv0_val with ⟨b, hv0_eq⟩
                    cases b
                    · exact litCase (.bool false) hv0_eq hexh.2
                    · exact litCase (.bool true) hv0_eq hexh.1
              | int _ => exact wildCase hexh
              | int64 _ => exact wildCase hexh
              | floatBits _ => exact wildCase hexh
              | float32Bits _ => exact wildCase hexh
              | char _ => exact wildCase hexh
              | str _ => exact wildCase hexh
            | tuple ps0 =>
              rcases hmat (.tuple ps0 :: rest0) hp0_mem with ⟨_, hps0⟩
              cases hps0 with
              | cons hp0 _ =>
                cases hp0 with
                | @tuple _ elemTys _ hps0_ty =>
                  have hlen_ps0 : ps0.length = elemTys.length := patsHaveType_length hps0_ty
                  rcases canonical_tuple hv0_ty hv0_val with ⟨elemVs, rfl, helem_ty, helem_val⟩
                  have hlen_vs : elemVs.length = elemTys.length := hasTypes_length helem_ty
                  have hexhT :
                      checkPatsExhaustive fuel' Δ (elemTys ++ restTys).length
                        (specializeTuple elemTys.length matrix) = true := by
                    simpa [List.length_append, hlen_ps0] using hexh
                  have hmatT :
                      ∀ row' ∈ specializeTuple elemTys.length matrix,
                        ∃ bs', PatsHaveType Δ row' (elemTys ++ restTys) bs' := by
                    intro row' hmem'
                    rcases mem_specializeTuple hmem' with
                      ⟨ps, rest, hm, _, rfl⟩ | ⟨p, rest, hm, _, rfl⟩
                    · rcases hmat (.tuple ps :: rest) hm with ⟨_, hcons⟩
                      cases hcons with
                      | cons hp hrest_ps =>
                        cases hp with
                        | tuple hps => exact ⟨_, patsHaveType_append hps hrest_ps⟩
                    · rcases hmat (p :: rest) hm with ⟨_, hcons⟩
                      cases hcons with
                      | cons _ hrest_ps =>
                        exact ⟨_, patsHaveType_append (patsHaveType_replicate_wild Δ elemTys) hrest_ps⟩
                  have hvsT_ty : HasTypes Δ Φ Ψ Θ emptyCtx (elemVs ++ restVs) (elemTys ++ restTys) :=
                    hasTypes_append helem_ty hrest_ty
                  have hvsT_val : ∀ u ∈ elemVs ++ restVs, IsValue u := by
                    intro u hu
                    rcases List.mem_append.mp hu with h1 | h2
                    · exact helem_val u h1
                    · exact hrest_val u h2
                  rcases ih hexhT hmatT hvsT_ty hvsT_val with ⟨row', hmem', hmatch'⟩
                  rcases mem_specializeTuple hmem' with
                    ⟨ps, rest, hm, hlen_ps, rfl⟩ | ⟨p, rest, hm, hpw, rfl⟩
                  · rcases matchPats_append_split (hlen_ps.trans hlen_vs.symm) hmatch' with
                      ⟨b1, b2, hb1, hb2⟩
                    exact ⟨.tuple ps :: rest, hm, by simp [matchPats, matchPat, hb1, hb2]⟩
                  · have hlen_rep : (List.replicate elemTys.length Pat.wild).length = elemVs.length := by
                      simp [hlen_vs]
                    rcases matchPats_append_split hlen_rep hmatch' with ⟨_, b2, _, hb2⟩
                    rcases isWildPat_matchPat hpw (.tuple elemVs) with ⟨b1, hb1⟩
                    exact ⟨p :: rest, hm, by simp [matchPats, hb1, hb2]⟩
            | ctor adt0 tag0 ps0 =>
              rcases hmat (.ctor adt0 tag0 ps0 :: rest0) hp0_mem with ⟨_, hps0⟩
              cases hps0 with
              | cons hp0 _ =>
                cases hp0 with
                | ctor _ _ =>
                  cases hΔ : Δ adt0 with
                  | none => simp [hΔ] at hexh
                  | some defn =>
                    simp only [hΔ, List.all_eq_true] at hexh
                    rcases canonical_adt_typed hv0_ty hv0_val with
                      ⟨tag, flds, fldVs, rfl, hlv, hfld_ty, hfld_val⟩
                    rcases lookupVariant_mem_variants hΔ hlv with ⟨vi, hvi_mem, hvi_tag, hvi_flds⟩
                    have hexh_vi := hexh vi hvi_mem
                    rw [hvi_tag, hvi_flds] at hexh_vi
                    have hexhC :
                        checkPatsExhaustive fuel' Δ (flds ++ restTys).length
                          (specializeCtor adt0 tag flds.length matrix) = true := by
                      simpa [List.length_append] using hexh_vi
                    have hmatC :
                        ∀ row' ∈ specializeCtor adt0 tag flds.length matrix,
                          ∃ bs', PatsHaveType Δ row' (flds ++ restTys) bs' := by
                      intro row' hmem'
                      rcases mem_specializeCtor hmem' with
                        ⟨ps, rest, hm, _, rfl⟩ | ⟨p, rest, hm, _, rfl⟩
                      · rcases hmat (.ctor adt0 tag ps :: rest) hm with ⟨_, hcons⟩
                        cases hcons with
                        | cons hp hrest_ps =>
                          cases hp with
                          | ctor hlv' hps =>
                            rw [hlv] at hlv'
                            cases hlv'
                            exact ⟨_, patsHaveType_append hps hrest_ps⟩
                      · rcases hmat (p :: rest) hm with ⟨_, hcons⟩
                        cases hcons with
                        | cons _ hrest_ps =>
                          exact ⟨_, patsHaveType_append (patsHaveType_replicate_wild Δ flds) hrest_ps⟩
                    have hlen_flds : fldVs.length = flds.length := hasTypes_length hfld_ty
                    have hvsC_ty : HasTypes Δ Φ Ψ Θ emptyCtx (fldVs ++ restVs) (flds ++ restTys) :=
                      hasTypes_append hfld_ty hrest_ty
                    have hvsC_val : ∀ u ∈ fldVs ++ restVs, IsValue u := by
                      intro u hu
                      rcases List.mem_append.mp hu with h1 | h2
                      · exact hfld_val u h1
                      · exact hrest_val u h2
                    rcases ih hexhC hmatC hvsC_ty hvsC_val with ⟨row', hmem', hmatch'⟩
                    rcases mem_specializeCtor hmem' with
                      ⟨ps, rest, hm, hlen_ps, rfl⟩ | ⟨p, rest, hm, hpw, rfl⟩
                    · rcases matchPats_append_split (hlen_ps.trans hlen_flds.symm) hmatch' with
                        ⟨b1, b2, hb1, hb2⟩
                      exact ⟨.ctor adt0 tag ps :: rest, hm, by simp [matchPats, matchPat, hb1, hb2]⟩
                    · have hlen_rep : (List.replicate flds.length Pat.wild).length = fldVs.length := by
                        simp [hlen_flds]
                      rcases matchPats_append_split hlen_rep hmatch' with ⟨_, b2, _, hb2⟩
                      rcases isWildPat_matchPat hpw (.makeData adt0 tag fldVs) with ⟨b1, hb1⟩
                      exact ⟨p :: rest, hm, by simp [matchPats, hb1, hb2]⟩

private theorem armsHaveType_mem_pat {Δ : AdtEnv} {Φ : FunEnv} {Ψ : StoreTy} {Θ : TaskTy}
    {Γ : Ctx} {τs τr : Ty} {arms : List (Pat × Expr)} {arm : Pat × Expr}
    (harms : ArmsHaveType Δ Φ Ψ Θ Γ τs arms τr) (hmem : arm ∈ arms) :
    ∃ bs, PatHasType Δ arm.1 τs bs := by
  induction arms with
  | nil => cases hmem
  | cons _ _ ih =>
    cases harms with
    | cons hp _ hrest =>
      rcases List.mem_cons.mp hmem with rfl | hm
      · exact ⟨_, hp⟩
      · exact ih hrest hm

/-- **Arm Exhaustiveness Soundness**: If `checkArmsExhaustive Δ arms = true`, then
    every closed well-typed scrutinee value `v : τs` matches at least one arm in `arms`. -/
theorem checkArmsExhaustive_sound {Δ : AdtEnv} {Φ : FunEnv} {Ψ : StoreTy} {Θ : TaskTy}
    {τs τr : Ty} {arms : List (Pat × Expr)} {v : Expr}
    (hexh : checkArmsExhaustive Δ arms = true)
    (hval : IsValue v)
    (hv : HasType Δ Φ Ψ Θ emptyCtx v τs)
    (harms : ArmsHaveType Δ Φ Ψ Θ emptyCtx τs arms τr) :
    ∃ arm ∈ arms, (matchPat arm.1 v).isSome = true := by
  have hmat : ∀ row ∈ arms.map (fun a => [a.1]), ∃ bs, PatsHaveType Δ row [τs] bs := by
    intro row hmem
    rcases List.mem_map.mp hmem with ⟨arm, harm_mem, rfl⟩
    rcases armsHaveType_mem_pat harms harm_mem with ⟨bs, hp⟩
    exact ⟨bs ++ [], .cons hp .nil⟩
  have hvs_ty : HasTypes Δ Φ Ψ Θ emptyCtx [v] [τs] := .cons hv .nil
  have hvs_val : ∀ u ∈ [v], IsValue u := by
    intro u hu
    simp only [List.mem_singleton] at hu
    subst hu
    exact hval
  rcases checkPatsExhaustive_sound (τs := [τs]) hexh hmat hvs_ty hvs_val with ⟨row, hmem, hmatch⟩
  rcases List.mem_map.mp hmem with ⟨arm, harm_mem, rfl⟩
  simp only [matchPats] at hmatch
  cases hm : matchPat arm.1 v with
  | none => rw [hm] at hmatch; simp at hmatch
  | some _ => exact ⟨arm, harm_mem, by simp [hm]⟩

/-! ## Part 3: Dynamic Invariant & End-to-End Elimination of `Trap.matchFailure` -/

/- Dynamic expression match-safety invariant `ExprExhSafe Δ e`:
   - Forbids `.trap .matchFailure` while allowing `.trap .divByZero`.
   - Allows `.match_ scrut arms` when either `checkArmsExhaustive Δ arms = true`
     (before `scrut` finishes evaluating or before peeling arms) OR `scrut` is
     already a value with a remaining matching arm in `arms` (across `Step.matchMiss`). -/
mutual
def ExprExhSafe (Δ : AdtEnv) : Expr → Prop
  | .lit _ => True
  | .var _ => True
  | .loc _ => True
  | .taskRef _ => True
  | .syncRef _ _ => True
  | .tuple es => ExprListExhSafe Δ es
  | .block es => ExprListExhSafe Δ es
  | .lam _ _ _ body => ExprExhSafe Δ body
  | .apply fn args => ExprExhSafe Δ fn ∧ ExprListExhSafe Δ args
  | .applyDir _ args => ExprListExhSafe Δ args
  | .bin _ e1 e2 => ExprExhSafe Δ e1 ∧ ExprExhSafe Δ e2
  | .un _ e => ExprExhSafe Δ e
  | .let_ _ e1 e2 => ExprExhSafe Δ e1 ∧ ExprExhSafe Δ e2
  | .if_ c t e => ExprExhSafe Δ c ∧ ExprExhSafe Δ t ∧ ExprExhSafe Δ e
  | .while_ c b => ExprExhSafe Δ c ∧ ExprExhSafe Δ b
  | .match_ scrut arms =>
    ExprExhSafe Δ scrut ∧
    ArmsExhSafe Δ arms ∧
    (checkArmsExhaustive Δ arms = true ∨
      (IsValue scrut ∧ ∃ arm ∈ arms, (matchPat arm.1 scrut).isSome = true))
  | .makeData _ _ es => ExprListExhSafe Δ es
  | .getTag e => ExprExhSafe Δ e
  | .cellNew e => ExprExhSafe Δ e
  | .cellGet e => ExprExhSafe Δ e
  | .cellSet e1 e2 => ExprExhSafe Δ e1 ∧ ExprExhSafe Δ e2
  | .spawn e => ExprExhSafe Δ e
  | .await e => ExprExhSafe Δ e
  | .concPrim _ args => ExprListExhSafe Δ args
  | .trap .divByZero => True
  | .trap .hostTrap => True
  | .trap .matchFailure => False

def ExprListExhSafe (Δ : AdtEnv) : List Expr → Prop
  | [] => True
  | e :: es => ExprExhSafe Δ e ∧ ExprListExhSafe Δ es

def ArmsExhSafe (Δ : AdtEnv) : List (Pat × Expr) → Prop
  | [] => True
  | (_, body) :: rest => ExprExhSafe Δ body ∧ ArmsExhSafe Δ rest
end

theorem exprListExhSafe_iff {Δ : AdtEnv} {es : List Expr} :
    ExprListExhSafe Δ es ↔ ∀ e ∈ es, ExprExhSafe Δ e := by
  induction es with
  | nil => simp [ExprListExhSafe]
  | cons e rest ih =>
    simp only [ExprListExhSafe, ih, List.mem_cons, forall_eq_or_imp]

theorem armsExhSafe_iff {Δ : AdtEnv} {arms : List (Pat × Expr)} :
    ArmsExhSafe Δ arms ↔ ∀ arm ∈ arms, ExprExhSafe Δ arm.2 := by
  induction arms with
  | nil => simp [ArmsExhSafe]
  | cons arm rest ih =>
    cases arm with
    | mk p body =>
      simp only [ArmsExhSafe, ih, List.mem_cons, forall_eq_or_imp]

theorem ne_matchFailure_of_exhSafe {Δ : AdtEnv} {e : Expr}
    (h : ExprExhSafe Δ e) : e ≠ .trap .matchFailure := by
  intro rfl
  exact h

/-- Top-level function table exhaustiveness invariant. -/
def FunEnvExhSafe (Δ : AdtEnv) (Φ : FunEnv) : Prop :=
  ∀ name fd, Φ name = some fd → ExprExhSafe Δ fd.body

/-! ### Soundness of Static `checkExprExhaustive` & `checkProgramExhaustive` -/

mutual
theorem checkExprExhaustive_sound {Δ : AdtEnv} {e : Expr}
    (h : checkExprExhaustive Δ e = true) : ExprExhSafe Δ e := by
  cases e with
  | lit _ => trivial
  | var _ => trivial
  | loc _ => trivial
  | taskRef _ => trivial
  | syncRef _ _ => trivial
  | tuple es =>
    simp only [checkExprExhaustive] at h
    exact checkExprListExhaustive_sound h
  | block es =>
    simp only [checkExprExhaustive] at h
    exact checkExprListExhaustive_sound h
  | lam _ _ _ body =>
    exact checkExprExhaustive_sound (e := body) h
  | apply fn args =>
    simp only [checkExprExhaustive, Bool.and_eq_true] at h
    exact ⟨checkExprExhaustive_sound (e := fn) h.1, checkExprListExhaustive_sound h.2⟩
  | applyDir _ args =>
    exact checkExprListExhaustive_sound h
  | bin _ e1 e2 =>
    simp only [checkExprExhaustive, Bool.and_eq_true] at h
    exact ⟨checkExprExhaustive_sound (e := e1) h.1, checkExprExhaustive_sound (e := e2) h.2⟩
  | un _ e1 =>
    exact checkExprExhaustive_sound (e := e1) h
  | let_ _ e1 e2 =>
    simp only [checkExprExhaustive, Bool.and_eq_true] at h
    exact ⟨checkExprExhaustive_sound (e := e1) h.1, checkExprExhaustive_sound (e := e2) h.2⟩
  | if_ c t e2 =>
    simp only [checkExprExhaustive, Bool.and_eq_true] at h
    exact ⟨checkExprExhaustive_sound (e := c) h.1.1,
      checkExprExhaustive_sound (e := t) h.1.2,
      checkExprExhaustive_sound (e := e2) h.2⟩
  | while_ c b =>
    simp only [checkExprExhaustive, Bool.and_eq_true] at h
    exact ⟨checkExprExhaustive_sound (e := c) h.1, checkExprExhaustive_sound (e := b) h.2⟩
  | match_ scrut arms =>
    simp only [checkExprExhaustive, Bool.and_eq_true] at h
    exact ⟨checkExprExhaustive_sound (e := scrut) h.1.2, checkArmsBodyExhaustive_sound h.2, Or.inl h.1.1.2⟩
  | makeData _ _ es =>
    exact checkExprListExhaustive_sound h
  | getTag e1 =>
    exact checkExprExhaustive_sound (e := e1) h
  | cellNew e1 =>
    exact checkExprExhaustive_sound (e := e1) h
  | cellGet e1 =>
    exact checkExprExhaustive_sound (e := e1) h
  | cellSet e1 e2 =>
    simp only [checkExprExhaustive, Bool.and_eq_true] at h
    exact ⟨checkExprExhaustive_sound (e := e1) h.1, checkExprExhaustive_sound (e := e2) h.2⟩
  | spawn e1 =>
    exact checkExprExhaustive_sound (e := e1) h
  | await e1 =>
    exact checkExprExhaustive_sound (e := e1) h
  | concPrim _ args =>
    exact checkExprListExhaustive_sound h
  | trap t =>
    cases t
    · trivial
    · simp [checkExprExhaustive] at h
    · trivial
termination_by sizeOf e

theorem checkExprListExhaustive_sound {Δ : AdtEnv} {es : List Expr}
    (h : checkExprListExhaustive Δ es = true) : ExprListExhSafe Δ es := by
  cases es with
  | nil => trivial
  | cons e rest =>
    simp only [checkExprListExhaustive, Bool.and_eq_true] at h
    exact ⟨checkExprExhaustive_sound h.1, checkExprListExhaustive_sound h.2⟩
termination_by sizeOf es

theorem checkArmsBodyExhaustive_sound {Δ : AdtEnv} {arms : List (Pat × Expr)}
    (h : checkArmsBodyExhaustive Δ arms = true) : ArmsExhSafe Δ arms := by
  cases arms with
  | nil => trivial
  | cons arm rest =>
    cases arm with
    | mk p body =>
      simp only [checkArmsBodyExhaustive, Bool.and_eq_true] at h
      exact ⟨checkExprExhaustive_sound h.1, checkArmsBodyExhaustive_sound h.2⟩
termination_by sizeOf arms
end

theorem checkProgramExhaustive_mem {Δ : AdtEnv} {funs : List FunDef} {fd : FunDef}
    (h : checkProgramExhaustive Δ funs = .ok ()) (hmem : fd ∈ funs) :
    ExprExhSafe Δ fd.body := by
  induction funs with
  | nil => cases hmem
  | cons f rest ih =>
    simp only [checkProgramExhaustive] at h
    split at h
    · rename_i hf
      rcases List.mem_cons.mp hmem with rfl | hrest
      · exact checkExprExhaustive_sound hf
      · exact ih h hrest
    · cases h

theorem checkProgramExhaustive_sound {Δ : AdtEnv} {funs : List FunDef} {Φ : FunEnv}
    (hΦ_mem : ∀ name fd, Φ name = some fd → fd ∈ funs)
    (h : checkProgramExhaustive Δ funs = .ok ()) :
    FunEnvExhSafe Δ Φ :=
  fun name fd hfd => checkProgramExhaustive_mem h (hΦ_mem name fd hfd)

/-! ### Value, Pattern-Matching & Substitution Preservation of `ExprExhSafe` -/

mutual
theorem subst_isValue (x : Ident) (val : Expr) :
    {u : Expr} → IsValue u → IsValue (subst x val u)
  | _, .lit l => .lit l
  | _, .loc l => .loc l
  | _, .taskRef tid => .taskRef tid
  | _, .syncRef k id => .syncRef k id
  | _, .lam m ps ret body => by
    simp only [subst]
    split <;> exact .lam _ _ _ _
  | _, .tuple hvs => .tuple (substList_isValue x val hvs)
  | _, .makeData adt tag hvs => .makeData adt tag (substList_isValue x val hvs)
termination_by u => sizeOf u

theorem substList_isValue (x : Ident) (val : Expr) :
    {es : List Expr} → (∀ e ∈ es, IsValue e) → ∀ w ∈ substList x val es, IsValue w
  | [], _, _, hm => nomatch hm
  | e :: rest, hvs, w, hm => by
    rcases List.mem_cons.mp hm with rfl | hrest
    · exact subst_isValue x val (hvs e (List.mem_cons_self ..))
    · exact substList_isValue x val (fun a ha => hvs a (List.mem_cons_of_mem _ ha)) w hrest
termination_by es => sizeOf es
end

mutual
theorem matchPat_subst_isSome (x : Ident) (val : Expr) :
    (p : Pat) → {u : Expr} → IsValue u → (matchPat p u).isSome = true →
    (matchPat p (subst x val u)).isSome = true
  | .wild, _, _, _ => rfl
  | .var _, _, _, _ => rfl
  | .lit l1, u, hu, hm => by
    cases hu with
    | lit l2 => exact hm
    | loc _ => simp [matchPat] at hm
    | taskRef _ => simp [matchPat] at hm
    | syncRef _ _ => simp [matchPat] at hm
    | lam _ _ _ _ => simp [matchPat] at hm
    | tuple _ => simp [matchPat] at hm
    | makeData _ _ _ => simp [matchPat] at hm
  | .tuple ps, u, hu, hm => by
    cases hu with
    | lit _ => simp [matchPat] at hm
    | loc _ => simp [matchPat] at hm
    | taskRef _ => simp [matchPat] at hm
    | syncRef _ _ => simp [matchPat] at hm
    | lam _ _ _ _ => simp [matchPat] at hm
    | tuple hvs =>
      simp only [subst, matchPat] at hm ⊢
      exact matchPats_subst_isSome x val ps hvs hm
    | makeData _ _ _ => simp [matchPat] at hm
  | .ctor adt1 tag1 ps, u, hu, hm => by
    cases hu with
    | lit _ => simp [matchPat] at hm
    | loc _ => simp [matchPat] at hm
    | taskRef _ => simp [matchPat] at hm
    | syncRef _ _ => simp [matchPat] at hm
    | lam _ _ _ _ => simp [matchPat] at hm
    | tuple _ => simp [matchPat] at hm
    | makeData adt2 tag2 hvs =>
      simp only [subst, matchPat] at hm ⊢
      by_cases hc : (adt1 == adt2 && tag1 == tag2) = true
      · simp only [hc, ↓reduceIte] at hm ⊢
        exact matchPats_subst_isSome x val ps hvs hm
      · simp only [hc] at hm
        cases hm

theorem matchPats_subst_isSome (x : Ident) (val : Expr) :
    (ps : List Pat) → {us : List Expr} → (∀ u ∈ us, IsValue u) → (matchPats ps us).isSome = true →
    (matchPats ps (substList x val us)).isSome = true
  | [], [], _, _ => rfl
  | [], _ :: _, _, hm => by simp [matchPats] at hm
  | _ :: _, [], _, hm => by simp [matchPats] at hm
  | p :: ps, u :: us, hus, hm => by
    simp only [substList, matchPats] at hm ⊢
    cases h1 : matchPat p u with
    | none => rw [h1] at hm; simp at hm
    | some _ =>
      rw [h1] at hm
      cases h2 : matchPats ps us with
      | none => rw [h2] at hm; simp at hm
      | some _ =>
        have hs1 := matchPat_subst_isSome x val p (hus u (List.mem_cons_self ..)) (by simp [h1])
        have hs2 := matchPats_subst_isSome x val ps
          (fun w hw => hus w (List.mem_cons_of_mem _ hw)) (by simp [h2])
        cases hm1 : matchPat p (subst x val u) with
        | none => rw [hm1] at hs1; simp at hs1
        | some _ =>
          cases hm2 : matchPats ps (substList x val us) with
          | none => rw [hm2] at hs2; simp at hs2
          | some _ => rfl
end

theorem substArms_pats (x : Ident) (val : Expr) (arms : List (Pat × Expr)) :
    (substArms x val arms).map (fun a => [a.1]) = arms.map (fun a => [a.1]) := by
  induction arms with
  | nil => rfl
  | cons arm rest ih =>
    cases arm with
    | mk p body => simp [substArms, ih]

theorem checkArmsExhaustive_substArms (Δ : AdtEnv) (x : Ident) (val : Expr)
    (arms : List (Pat × Expr)) :
    checkArmsExhaustive Δ (substArms x val arms) = checkArmsExhaustive Δ arms := by
  simp [checkArmsExhaustive, substArms_pats]

theorem mem_substArms_of_mem (x : Ident) (val : Expr) {arms : List (Pat × Expr)} {arm : Pat × Expr}
    (hmem : arm ∈ arms) :
    ∃ arm' ∈ substArms x val arms, arm'.1 = arm.1 := by
  induction arms with
  | nil => cases hmem
  | cons hd rest ih =>
    cases hd with
    | mk p body =>
      rcases List.mem_cons.mp hmem with rfl | hrest
      · exact ⟨_, List.mem_cons_self .., rfl⟩
      · rcases ih hrest with ⟨arm', hm', hp'⟩
        exact ⟨arm', List.mem_cons_of_mem _ hm', hp'⟩

mutual
theorem subst_preserves_exhSafe {Δ : AdtEnv} {x : Ident} {val : Expr}
    (hval_exh : ExprExhSafe Δ val) :
    (e : Expr) → ExprExhSafe Δ e → ExprExhSafe Δ (subst x val e)
  | .lit _, _ => trivial
  | .var y, _ => by
    simp only [subst]
    split
    · exact hval_exh
    · trivial
  | .loc _, _ => trivial
  | .taskRef _, _ => trivial
  | .syncRef _ _, _ => trivial
  | .tuple es, h => substList_preserves_exhSafe hval_exh es h
  | .block es, h => substList_preserves_exhSafe hval_exh es h
  | .lam m ps ret body, h => by
    simp only [subst]
    split
    · exact h
    · exact subst_preserves_exhSafe hval_exh body h
  | .apply fn args, h =>
    ⟨subst_preserves_exhSafe hval_exh fn h.1, substList_preserves_exhSafe hval_exh args h.2⟩
  | .applyDir _ args, h => substList_preserves_exhSafe hval_exh args h
  | .bin _ e1 e2, h =>
    ⟨subst_preserves_exhSafe hval_exh e1 h.1, subst_preserves_exhSafe hval_exh e2 h.2⟩
  | .un _ e1, h => subst_preserves_exhSafe hval_exh e1 h
  | .let_ y e1 e2, h => by
    simp only [subst]
    split
    · exact ⟨subst_preserves_exhSafe hval_exh e1 h.1, h.2⟩
    · exact ⟨subst_preserves_exhSafe hval_exh e1 h.1, subst_preserves_exhSafe hval_exh e2 h.2⟩
  | .if_ c t e2, h =>
    ⟨subst_preserves_exhSafe hval_exh c h.1,
     subst_preserves_exhSafe hval_exh t h.2.1,
     subst_preserves_exhSafe hval_exh e2 h.2.2⟩
  | .while_ c b, h =>
    ⟨subst_preserves_exhSafe hval_exh c h.1, subst_preserves_exhSafe hval_exh b h.2⟩
  | .match_ scrut arms, h => by
    rcases h with ⟨hs, harms, hdisj⟩
    refine ⟨subst_preserves_exhSafe hval_exh scrut hs,
      substArms_preserves_exhSafe hval_exh arms harms, ?_⟩
    rcases hdisj with hexh | ⟨hval_s, arm, harm_mem, harm_match⟩
    · exact Or.inl (by rw [checkArmsExhaustive_substArms]; exact hexh)
    · rcases mem_substArms_of_mem x val harm_mem with ⟨arm', harm'_mem, harm'_pat⟩
      refine Or.inr ⟨subst_isValue x val hval_s, arm', harm'_mem, ?_⟩
      rw [harm'_pat]
      exact matchPat_subst_isSome x val arm.1 hval_s harm_match
  | .makeData _ _ es, h => substList_preserves_exhSafe hval_exh es h
  | .getTag e1, h => subst_preserves_exhSafe hval_exh e1 h
  | .cellNew e1, h => subst_preserves_exhSafe hval_exh e1 h
  | .cellGet e1, h => subst_preserves_exhSafe hval_exh e1 h
  | .cellSet e1 e2, h =>
    ⟨subst_preserves_exhSafe hval_exh e1 h.1, subst_preserves_exhSafe hval_exh e2 h.2⟩
  | .spawn e1, h => subst_preserves_exhSafe hval_exh e1 h
  | .await e1, h => subst_preserves_exhSafe hval_exh e1 h
  | .concPrim _ args, h => substList_preserves_exhSafe hval_exh args h
  | .trap .divByZero, _ => trivial
  | .trap .hostTrap, _ => trivial
  | .trap .matchFailure, h => False.elim h
termination_by e => sizeOf e

theorem substList_preserves_exhSafe {Δ : AdtEnv} {x : Ident} {val : Expr}
    (hval_exh : ExprExhSafe Δ val) :
    (es : List Expr) → ExprListExhSafe Δ es → ExprListExhSafe Δ (substList x val es)
  | [], _ => trivial
  | e :: rest, h =>
    ⟨subst_preserves_exhSafe hval_exh e h.1, substList_preserves_exhSafe hval_exh rest h.2⟩
termination_by es => sizeOf es

theorem substArms_preserves_exhSafe {Δ : AdtEnv} {x : Ident} {val : Expr}
    (hval_exh : ExprExhSafe Δ val) :
    (arms : List (Pat × Expr)) → ArmsExhSafe Δ arms → ArmsExhSafe Δ (substArms x val arms)
  | [], _ => trivial
  | (p, body) :: rest, h => by
    simp only [substArms, ArmsExhSafe]
    refine ⟨?_, substArms_preserves_exhSafe hval_exh rest h.2⟩
    split
    · exact h.1
    · exact subst_preserves_exhSafe hval_exh body h.1
termination_by arms => sizeOf arms
end

theorem substMany_preserves_exhSafe {Δ : AdtEnv} {env : List (Ident × Expr)} {e : Expr}
    (henv : ∀ x u, (x, u) ∈ env → ExprExhSafe Δ u)
    (he : ExprExhSafe Δ e) :
    ExprExhSafe Δ (substMany env e) := by
  induction env generalizing e with
  | nil => exact he
  | cons kv rest ih =>
    cases kv with
    | mk x v =>
      exact ih
        (fun y u hm => henv y u (List.mem_cons_of_mem _ hm))
        (subst_preserves_exhSafe (henv x v (List.mem_cons_self ..)) e he)

mutual
theorem matchPat_exhSafe {Δ : AdtEnv} :
    {p : Pat} → {v : Expr} → {env : List (Ident × Expr)} →
    ExprExhSafe Δ v → matchPat p v = some env →
    ∀ x u, (x, u) ∈ env → ExprExhSafe Δ u
  | .wild, _, _, _, hm => by
    simp only [matchPat, Option.some.injEq] at hm
    subst hm; intro _ _ h; cases h
  | .var _, _, _, hv, hm => by
    simp only [matchPat, Option.some.injEq] at hm
    subst hm
    intro _ u hu
    simp only [List.mem_singleton, Prod.mk.injEq] at hu
    rcases hu with ⟨_, rfl⟩
    exact hv
  | .lit _, v, _, _, hm => by
    cases v <;> simp only [matchPat] at hm <;> try cases hm
    split at hm
    · cases hm; intro _ _ h; cases h
    · cases hm
  | .tuple _, v, _, hv, hm => by
    cases v <;> simp only [matchPat] at hm <;> try cases hm
    exact matchPats_exhSafe hv hm
  | .ctor _ _ _, v, _, hv, hm => by
    cases v <;> simp only [matchPat] at hm <;> try cases hm
    split at hm
    · exact matchPats_exhSafe hv hm
    · cases hm

theorem matchPats_exhSafe {Δ : AdtEnv} :
    {ps : List Pat} → {vs : List Expr} → {env : List (Ident × Expr)} →
    ExprListExhSafe Δ vs → matchPats ps vs = some env →
    ∀ x u, (x, u) ∈ env → ExprExhSafe Δ u
  | [], vs, _, _, hm => by
    cases vs <;> simp only [matchPats] at hm <;> try cases hm
    intro _ _ h; cases h
  | _ :: _, [], _, _, hm => by simp [matchPats] at hm
  | p :: rest, v :: vrest, _, hvs, hm => by
    simp only [matchPats] at hm
    cases h1 : matchPat p v with
    | none => rw [h1] at hm; cases hm
    | some b1 =>
      rw [h1] at hm
      cases h2 : matchPats rest vrest with
      | none => rw [h2] at hm; cases hm
      | some b2 =>
        rw [h2] at hm; cases hm
        intro x u hmem
        rcases List.mem_append.mp hmem with hm1 | hm2
        · exact matchPat_exhSafe hvs.1 h1 x u hm1
        · exact matchPats_exhSafe hvs.2 h2 x u hm2
end

theorem zipParams_exhSafe {Δ : AdtEnv} {ps : List (Ident × Ty)} {args : List Expr}
    (hargs : ExprListExhSafe Δ args) :
    ∀ x u, (x, u) ∈ zipParams ps args → ExprExhSafe Δ u := by
  induction ps generalizing args with
  | nil => intro _ _ h; simp [zipParams] at h
  | cons p prest ih =>
    cases args with
    | nil => intro _ _ h; simp [zipParams] at h
    | cons a arest =>
      intro x u hmem
      simp only [zipParams, List.map_cons, List.zip_cons_cons, List.mem_cons, Prod.mk.injEq] at hmem
      rcases hmem with ⟨_, rfl⟩ | hrest
      · exact hargs.1
      · exact ih hargs.2 x u hrest

/-! ### Step Helpers: Irreducibility of Values, Trap Extraction & Pool Invariants -/

theorem no_trap_of_isValues {vs : List Expr} {t : Trap}
    (hvs : ∀ v ∈ vs, IsValue v) (htr : ListFirstTrap vs t) : False := by
  induction htr with
  | head _ _ =>
    have h := hvs _ (List.mem_cons_self ..)
    cases h
  | tail _ _ ih =>
    exact ih (fun u hu => hvs u (List.mem_cons_of_mem _ hu))

mutual
theorem no_step_of_isValue {Δ : AdtEnv} {Φ : FunEnv} {pool : ConcPool}
    {v e' : Expr} {σ σ' : Store} {eff : ConcEff}
    (hv : IsValue v) (hs : Step Δ Φ pool v σ e' σ' eff) : False := by
  cases hv with
  | lit _ => cases hs
  | loc _ => cases hs
  | taskRef _ => cases hs
  | syncRef _ _ => cases hs
  | lam _ _ _ _ => cases hs
  | tuple hvs =>
    cases hs with
    | tupleStep hsl => exact no_stepList_of_isValues hvs hsl
    | tupleTrap htr => exact no_trap_of_isValues hvs htr
  | makeData _ _ hvs =>
    cases hs with
    | makeDataStep hsl => exact no_stepList_of_isValues hvs hsl
    | makeDataTrap htr => exact no_trap_of_isValues hvs htr
termination_by sizeOf v

theorem no_stepList_of_isValues {Δ : AdtEnv} {Φ : FunEnv} {pool : ConcPool}
    {vs es' : List Expr} {σ σ' : Store} {eff : ConcEff}
    (hvs : ∀ v ∈ vs, IsValue v) (hsl : StepList Δ Φ pool vs σ es' σ' eff) : False := by
  cases hsl with
  | head hs => exact no_step_of_isValue (hvs _ (List.mem_cons_self ..)) hs
  | tail _ hsl' =>
    exact no_stepList_of_isValues (fun u hu => hvs u (List.mem_cons_of_mem _ hu)) hsl'
termination_by sizeOf vs
end

theorem listFirstTrap_exhSafe {Δ : AdtEnv} {es : List Expr} {t : Trap}
    (hes : ExprListExhSafe Δ es) (htr : ListFirstTrap es t) :
    ExprExhSafe Δ (.trap t) := by
  induction htr with
  | head _ _ => exact hes.1
  | tail _ _ ih => exact ih hes.2

theorem evalBinOp_trap_exhSafe {Δ : AdtEnv} {op : BinOp} {l1 l2 : Lit} {t : Trap}
    (he : evalBinOp op l1 l2 = some (.trap t)) :
    ExprExhSafe Δ (.trap t) := by
  cases op with
  | div | rem | div64 | rem64 =>
    cases l1 <;> cases l2 <;> simp [evalBinOp] at he
    all_goals
      split at he <;> simp at he
      subst he
      trivial
  | _ =>
    cases l1 <;> cases l2 <;> cases he

/-- Match-safety invariant for an `Actor`'s lifecycle phase (excluding `.failed .matchFailure`). -/
def ActorPhaseExhSafe (Δ : AdtEnv) : ActorPhase → Prop
  | .init e => ExprExhSafe Δ e
  | .idle sv => ExprExhSafe Δ sv
  | .busy sv e _ => ExprExhSafe Δ sv ∧ ExprExhSafe Δ e
  | .failed .divByZero => True
  | .failed .hostTrap => True
  | .failed .matchFailure => False

/-- Match-safety invariant across the mutable store `σ` and concurrent `ConcPool`. -/
structure PoolExhSafe (Δ : AdtEnv) (pool : ConcPool) (σ : Store) : Prop where
  store_safe : ∀ (l : Loc) (v : Expr), σ[l]? = some v → ExprExhSafe Δ v
  task_safe  : ∀ (tid : TaskId) (e : Expr),
    pool.tasks[tid]? = some (.running e) → ExprExhSafe Δ e
  mvar_safe  : ∀ (mid : Nat) (v : Expr),
    pool.mvars[mid]? = some (some v) → ExprExhSafe Δ v
  chan_safe  : ∀ (cid : Nat) (ch : ChanState) (v : Expr),
    pool.chans[cid]? = some ch → v ∈ ch.buf → ExprExhSafe Δ v
  actor_safe : ∀ (aid : Nat) (act : ActorState),
    pool.actors[aid]? = some act →
    ActorPhaseExhSafe Δ act.phase ∧
    (∀ msg ∈ act.mailbox, ExprExhSafe Δ msg.handler)

/-- Match-safety invariant on an emitted `ConcEff`. -/
def EffExhSafe (Δ : AdtEnv) : ConcEff → Prop
  | .none => True
  | .spawnTask body => ExprExhSafe Δ body
  | .allocMVar init => ∀ v, init = some v → ExprExhSafe Δ v
  | .takeMVar _ => True
  | .putMVar _ val => ExprExhSafe Δ val
  | .allocChan _ => True
  | .sendChan _ val => ExprExhSafe Δ val
  | .recvChan _ => True
  | .closeChan _ => True
  | .spawnActor initExpr => ExprExhSafe Δ initExpr
  | .callActor _ handler => ExprExhSafe Δ handler
  | .sendActor _ handler => ExprExhSafe Δ handler

/-! ### Single-Thread Preservation of `ExprExhSafe` (`step_preserves_exhSafe`) -/

mutual
theorem step_preserves_exhSafe {Δ : AdtEnv} {Φ : FunEnv} (hΦ_exh : FunEnvExhSafe Δ Φ)
    {Ψ : StoreTy} {Θ : TaskTy} {pool : ConcPool}
    {e : Expr} {σ : Store} {e' : Expr} {σ' : Store} {eff : ConcEff} {τ : Ty}
    (ht : HasType Δ Φ Ψ Θ emptyCtx e τ)
    (hexh : ExprExhSafe Δ e)
    (hpool_exh : PoolExhSafe Δ pool σ)
    (hstep : Step Δ Φ pool e σ e' σ' eff) :
    ExprExhSafe Δ e' ∧ PoolExhSafe Δ pool σ' ∧ EffExhSafe Δ eff := by
  cases hstep with
  | tupleStep hsl =>
    cases ht with
    | tuple hts =>
      exact stepList_preserves_exhSafe hΦ_exh hts hexh hpool_exh hsl
  | tupleTrap htr =>
    exact ⟨listFirstTrap_exhSafe hexh htr, hpool_exh, trivial⟩
  | blockEmpty =>
    exact ⟨trivial, hpool_exh, trivial⟩
  | blockSingle =>
    exact ⟨hexh.1, hpool_exh, trivial⟩
  | blockConsStep hs =>
    cases ht with
    | blockCons h1 _ =>
      rcases step_preserves_exhSafe hΦ_exh h1 hexh.1 hpool_exh hs with ⟨he1', hp', heff'⟩
      exact ⟨⟨he1', hexh.2⟩, hp', heff'⟩
  | blockConsVal _ =>
    exact ⟨hexh.2, hpool_exh, trivial⟩
  | blockConsTrap =>
    exact ⟨hexh.1, hpool_exh, trivial⟩
  | applyFn hs =>
    cases ht with
    | apply hfn _ _ =>
      rcases step_preserves_exhSafe hΦ_exh hfn hexh.1 hpool_exh hs with ⟨hfn', hp', heff'⟩
      exact ⟨⟨hfn', hexh.2⟩, hp', heff'⟩
  | applyFnTrap =>
    exact ⟨hexh.1, hpool_exh, trivial⟩
  | applyArgs _ hsl =>
    cases ht with
    | apply _ hargs _ =>
      rcases stepList_preserves_exhSafe hΦ_exh hargs hexh.2 hpool_exh hsl with ⟨hargs', hp', heff'⟩
      exact ⟨⟨hexh.1, hargs'⟩, hp', heff'⟩
  | applyArgsTrap _ htr =>
    exact ⟨listFirstTrap_exhSafe hexh.2 htr, hpool_exh, trivial⟩
  | applyBeta _ _ =>
    exact ⟨substMany_preserves_exhSafe (zipParams_exhSafe hexh.2) hexh.1, hpool_exh, trivial⟩
  | applyDirArgs hsl =>
    cases ht with
    | applyDir _ hargs _ =>
      exact stepList_preserves_exhSafe hΦ_exh hargs hexh hpool_exh hsl
  | applyDirTrap htr =>
    exact ⟨listFirstTrap_exhSafe hexh htr, hpool_exh, trivial⟩
  | applyDirBeta hf _ _ =>
    exact ⟨substMany_preserves_exhSafe (zipParams_exhSafe hexh) (hΦ_exh _ _ hf), hpool_exh, trivial⟩
  | unStep hs =>
    cases ht with
    | un _ h1 =>
      rcases step_preserves_exhSafe hΦ_exh h1 hexh hpool_exh hs with ⟨he', hp', heff'⟩
      exact ⟨he', hp', heff'⟩
  | unTrap =>
    exact ⟨hexh, hpool_exh, trivial⟩
  | unVal _ =>
    exact ⟨trivial, hpool_exh, trivial⟩
  | binLeft hs =>
    cases ht with
    | bin _ h1 _ =>
      rcases step_preserves_exhSafe hΦ_exh h1 hexh.1 hpool_exh hs with ⟨he1', hp', heff'⟩
      exact ⟨⟨he1', hexh.2⟩, hp', heff'⟩
  | binLeftTrap =>
    exact ⟨hexh.1, hpool_exh, trivial⟩
  | binAndFalse =>
    exact ⟨trivial, hpool_exh, trivial⟩
  | binAndTrue =>
    exact ⟨hexh.2, hpool_exh, trivial⟩
  | binOrTrue =>
    exact ⟨trivial, hpool_exh, trivial⟩
  | binOrFalse =>
    exact ⟨hexh.2, hpool_exh, trivial⟩
  | binRight _ _ _ hs =>
    cases ht with
    | bin _ _ h2 =>
      rcases step_preserves_exhSafe hΦ_exh h2 hexh.2 hpool_exh hs with ⟨he2', hp', heff'⟩
      exact ⟨⟨hexh.1, he2'⟩, hp', heff'⟩
  | binRightTrap _ _ _ =>
    exact ⟨hexh.2, hpool_exh, trivial⟩
  | binVal _ =>
    exact ⟨trivial, hpool_exh, trivial⟩
  | binTrap he =>
    exact ⟨evalBinOp_trap_exhSafe he, hpool_exh, trivial⟩
  | letStep hs =>
    cases ht with
    | let_ h1 _ =>
      rcases step_preserves_exhSafe hΦ_exh h1 hexh.1 hpool_exh hs with ⟨he1', hp', heff'⟩
      exact ⟨⟨he1', hexh.2⟩, hp', heff'⟩
  | letTrap =>
    exact ⟨hexh.1, hpool_exh, trivial⟩
  | letVal _ =>
    exact ⟨subst_preserves_exhSafe hexh.1 _ hexh.2, hpool_exh, trivial⟩
  | ifStep hs =>
    cases ht with
    | if_ hc _ _ =>
      rcases step_preserves_exhSafe hΦ_exh hc hexh.1 hpool_exh hs with ⟨hc', hp', heff'⟩
      exact ⟨⟨hc', hexh.2.1, hexh.2.2⟩, hp', heff'⟩
  | ifTrap =>
    exact ⟨hexh.1, hpool_exh, trivial⟩
  | ifTrue =>
    exact ⟨hexh.2.1, hpool_exh, trivial⟩
  | ifFalse =>
    exact ⟨hexh.2.2, hpool_exh, trivial⟩
  | whileUnfold =>
    exact ⟨⟨hexh.1, ⟨hexh.2, ⟨hexh.1, hexh.2⟩, trivial⟩, trivial⟩, hpool_exh, trivial⟩
  | matchScrut hs =>
    cases ht with
    | match_ hscr _ =>
      rcases hexh with ⟨hscr_exh, harms_exh, hdisj⟩
      rcases step_preserves_exhSafe hΦ_exh hscr hscr_exh hpool_exh hs with ⟨hscr', hp', heff'⟩
      rcases hdisj with hexh_arms | ⟨hval_s, _⟩
      · exact ⟨⟨hscr', harms_exh, Or.inl hexh_arms⟩, hp', heff'⟩
      · exact False.elim (no_step_of_isValue hval_s hs)
  | matchScrutTrap =>
    exact ⟨hexh.1, hpool_exh, trivial⟩
  | matchEmpty _ =>
    rcases hexh with ⟨_, _, hdisj⟩
    rcases hdisj with hexh_nil | ⟨_, _, hmem, _⟩
    · unfold checkArmsExhaustive defaultExhFuel checkPatsExhaustive hasNonEmptyRow at hexh_nil
      simp at hexh_nil
    · cases hmem
  | matchHit _ hm =>
    rcases hexh with ⟨hv_exh, harms_exh, _⟩
    exact ⟨substMany_preserves_exhSafe (matchPat_exhSafe hv_exh hm) harms_exh.1, hpool_exh, trivial⟩
  | @matchMiss v p body rest _ hv_val hm_none =>
    cases ht with
    | match_ hv_ty harms_ty =>
      rcases hexh with ⟨hv_exh, harms_exh, hdisj⟩
      have hexists : ∃ arm ∈ (p, body) :: rest, (matchPat arm.1 v).isSome = true := by
        rcases hdisj with hexh_arms | ⟨_, hex⟩
        · exact checkArmsExhaustive_sound hexh_arms hv_val hv_ty harms_ty
        · exact hex
      rcases hexists with ⟨arm, harm_mem, harm_match⟩
      rcases List.mem_cons.mp harm_mem with rfl | harm_rest
      · rw [hm_none] at harm_match
        simp at harm_match
      · exact ⟨⟨hv_exh, harms_exh.2, Or.inr ⟨hv_val, arm, harm_rest, harm_match⟩⟩, hpool_exh, trivial⟩
  | makeDataStep hsl =>
    cases ht with
    | makeData _ hts =>
      exact stepList_preserves_exhSafe hΦ_exh hts hexh hpool_exh hsl
  | makeDataTrap htr =>
    exact ⟨listFirstTrap_exhSafe hexh htr, hpool_exh, trivial⟩
  | getTagStep hs =>
    cases ht with
    | getTag h1 =>
      rcases step_preserves_exhSafe hΦ_exh h1 hexh hpool_exh hs with ⟨he', hp', heff'⟩
      exact ⟨he', hp', heff'⟩
  | getTagTrap =>
    exact ⟨hexh, hpool_exh, trivial⟩
  | getTagVal _ =>
    exact ⟨trivial, hpool_exh, trivial⟩
  | cellNewStep hs =>
    cases ht with
    | cellNew h1 =>
      rcases step_preserves_exhSafe hΦ_exh h1 hexh hpool_exh hs with ⟨he', hp', heff'⟩
      exact ⟨he', hp', heff'⟩
  | cellNewTrap =>
    exact ⟨hexh, hpool_exh, trivial⟩
  | @cellNewVal v _ =>
    refine ⟨trivial, { hpool_exh with store_safe := ?_ }, trivial⟩
    intro l u hlu
    cases Nat.lt_or_ge l σ.length with
    | inl hlt =>
      rw [List.getElem?_append_left hlt] at hlu
      exact hpool_exh.store_safe l u hlu
    | inr hge =>
      rw [List.getElem?_append_right hge] at hlu
      have hlt1 : l - σ.length < 1 := by simpa using lt_length_of_getElem?_eq_some hlu
      have heql : l = σ.length := Nat.le_antisymm (Nat.le_of_sub_eq_zero (Nat.lt_one_iff.mp hlt1)) hge
      subst heql
      simp at hlu
      subst hlu
      exact hexh
  | cellGetStep hs =>
    cases ht with
    | cellGet h1 _ =>
      rcases step_preserves_exhSafe hΦ_exh h1 hexh hpool_exh hs with ⟨he', hp', heff'⟩
      exact ⟨he', hp', heff'⟩
  | cellGetTrap =>
    exact ⟨hexh, hpool_exh, trivial⟩
  | cellGetVal hvσ =>
    exact ⟨hpool_exh.store_safe _ _ hvσ, hpool_exh, trivial⟩
  | cellSetLeft hs =>
    cases ht with
    | cellSet h1 _ =>
      rcases step_preserves_exhSafe hΦ_exh h1 hexh.1 hpool_exh hs with ⟨he1', hp', heff'⟩
      exact ⟨⟨he1', hexh.2⟩, hp', heff'⟩
  | cellSetLeftTrap =>
    exact ⟨hexh.1, hpool_exh, trivial⟩
  | cellSetRight _ hs =>
    cases ht with
    | cellSet _ h2 =>
      rcases step_preserves_exhSafe hΦ_exh h2 hexh.2 hpool_exh hs with ⟨he2', hp', heff'⟩
      exact ⟨⟨hexh.1, he2'⟩, hp', heff'⟩
  | cellSetRightTrap _ =>
    exact ⟨hexh.2, hpool_exh, trivial⟩
  | @cellSetVal l v _ hlt _ =>
    refine ⟨trivial, { hpool_exh with store_safe := ?_ }, trivial⟩
    intro k u hku
    by_cases hkl : k = l
    · subst hkl
      simp only [List.getElem?_set_self hlt, Option.some.injEq] at hku
      subst hku
      exact hexh.2
    · rw [List.getElem?_set_ne (Ne.symm hkl)] at hku
      exact hpool_exh.store_safe k u hku
  | spawnStep hs =>
    cases ht with
    | spawn h1 _ _ =>
      rcases step_preserves_exhSafe hΦ_exh h1 hexh hpool_exh hs with ⟨he', hp', heff'⟩
      exact ⟨he', hp', heff'⟩
  | spawnTrap =>
    exact ⟨hexh, hpool_exh, trivial⟩
  | spawnBeta =>
    exact ⟨trivial, hpool_exh, hexh⟩
  | awaitStep hs =>
    cases ht with
    | await h1 _ _ =>
      rcases step_preserves_exhSafe hΦ_exh h1 hexh hpool_exh hs with ⟨he', hp', heff'⟩
      exact ⟨he', hp', heff'⟩
  | awaitTrap =>
    exact ⟨hexh, hpool_exh, trivial⟩
  | awaitVal hte _ =>
    exact ⟨hpool_exh.task_safe _ _ hte, hpool_exh, trivial⟩
  | awaitTaskTrap hte =>
    exact ⟨hpool_exh.task_safe _ _ hte, hpool_exh, trivial⟩
  | concPrimArgs hsl =>
    cases ht with
    | concPrim _ hargs _ =>
      exact stepList_preserves_exhSafe hΦ_exh hargs hexh hpool_exh hsl
  | concPrimTrap htr =>
    exact ⟨listFirstTrap_exhSafe hexh htr, hpool_exh, trivial⟩
  | concPrimVal hprim =>
    cases hprim with
    | mvarNew _ =>
      refine ⟨trivial, hpool_exh, ?_⟩
      intro u hu; cases hu; exact hexh.1
    | mvarEmpty _ =>
      exact ⟨trivial, hpool_exh, fun _ hu => nomatch hu⟩
    | mvarTake hslot =>
      exact ⟨hpool_exh.mvar_safe _ _ hslot, hpool_exh, trivial⟩
    | mvarPut _ _ =>
      exact ⟨trivial, hpool_exh, hexh.2.1⟩
    | chanNew _ _ =>
      exact ⟨trivial, hpool_exh, trivial⟩
    | chanSendClosed _ _ _ =>
      exact ⟨trivial, hpool_exh, trivial⟩
    | chanSendOpen _ _ _ _ =>
      exact ⟨trivial, hpool_exh, hexh.2.1⟩
    | chanRecvVal hch hbuf =>
      have hv_safe : ExprExhSafe Δ _ :=
        hpool_exh.chan_safe _ _ _ hch (by rw [hbuf]; exact List.mem_cons_self ..)
      exact ⟨⟨hv_safe, trivial⟩, hpool_exh, trivial⟩
    | chanRecvClosed _ _ _ =>
      exact ⟨trivial, hpool_exh, trivial⟩
    | chanClose _ =>
      exact ⟨trivial, hpool_exh, trivial⟩
    | actorSpawn _ =>
      exact ⟨trivial, hpool_exh, ⟨hexh.1, trivial⟩⟩
    | actorCall _ _ =>
      exact ⟨trivial, hpool_exh, hexh.2.1⟩
    | actorSend _ _ =>
      exact ⟨trivial, hpool_exh, hexh.2.1⟩
termination_by sizeOf e

theorem stepList_preserves_exhSafe {Δ : AdtEnv} {Φ : FunEnv} (hΦ_exh : FunEnvExhSafe Δ Φ)
    {Ψ : StoreTy} {Θ : TaskTy} {pool : ConcPool}
    {es : List Expr} {σ : Store} {es' : List Expr} {σ' : Store} {eff : ConcEff} {τs : List Ty}
    (hts : HasTypes Δ Φ Ψ Θ emptyCtx es τs)
    (hexh : ExprListExhSafe Δ es)
    (hpool_exh : PoolExhSafe Δ pool σ)
    (hstep : StepList Δ Φ pool es σ es' σ' eff) :
    ExprListExhSafe Δ es' ∧ PoolExhSafe Δ pool σ' ∧ EffExhSafe Δ eff := by
  cases hstep with
  | head hs =>
    cases hts with
    | cons h1 _ =>
      rcases step_preserves_exhSafe hΦ_exh h1 hexh.1 hpool_exh hs with ⟨he1', hp', heff'⟩
      exact ⟨⟨he1', hexh.2⟩, hp', heff'⟩
  | tail _ hsl =>
    cases hts with
    | cons _ hrest =>
      rcases stepList_preserves_exhSafe hΦ_exh hrest hexh.2 hpool_exh hsl with ⟨hrest', hp', heff'⟩
      exact ⟨⟨hexh.1, hrest'⟩, hp', heff'⟩
termination_by sizeOf es
end

/-! ### Sequential Multi-Step Elimination of `Trap.matchFailure` -/

theorem emptyPool_exhSafe (Δ : AdtEnv) : PoolExhSafe Δ emptyPool [] :=
  { store_safe := fun _ _ h => by simp at h
    task_safe  := fun _ _ h => by simp [emptyPool] at h
    mvar_safe  := fun _ _ h => by simp [emptyPool] at h
    chan_safe  := fun _ _ _ h => by simp [emptyPool] at h
    actor_safe := fun _ _ h => by simp [emptyPool] at h }

theorem steps_preserves_exhSafe {Δ : AdtEnv} {Φ : FunEnv} {Ψ : StoreTy}
    (hΦ_ty : FunEnvTyped Δ Φ) (hΦ_exh : FunEnvExhSafe Δ Φ)
    {e e' : Expr} {σ σ' : Store} {τ : Ty}
    (ht : HasType Δ Φ Ψ emptyTaskTy emptyCtx e τ)
    (hσ : StoreTyped Δ Φ Ψ emptyTaskTy σ)
    (hexh : ExprExhSafe Δ e)
    (hp : PoolExhSafe Δ emptyPool σ)
    (hsteps : Steps Δ Φ e σ e' σ') :
    ExprExhSafe Δ e' := by
  induction hsteps generalizing Ψ with
  | refl => exact hexh
  | trans hstep _ ih =>
    rcases preservation hΦ_ty ht hstep hσ emptyPool_typed with
      ⟨Ψ', Θ', _, heff_ty, ht2, hσ2⟩
    simp only [EffTyped] at heff_ty
    subst heff_ty
    rcases step_preserves_exhSafe hΦ_exh ht hexh hp hstep with ⟨hexh2, hp2, _⟩
    exact ih ht2 hσ2 hexh2 hp2

/-- **Sequential Match-Failure Freedom**: Any closed well-typed expression `e`
    satisfying `ExprExhSafe Δ e` under an exhaustive, well-typed `FunEnv` never
    steps to `.trap .matchFailure` across any sequence of `Steps`. -/
theorem exhaustive_no_match_failure {Δ : AdtEnv} {Φ : FunEnv}
    (hΦ_ty : FunEnvTyped Δ Φ) (hΦ_exh : FunEnvExhSafe Δ Φ)
    {e e' : Expr} {σ' : Store} {τ : Ty}
    (ht : HasType Δ Φ [] emptyTaskTy emptyCtx e τ)
    (hexh : ExprExhSafe Δ e)
    (hsteps : Steps Δ Φ e [] e' σ') :
    e' ≠ .trap .matchFailure := by
  have hσ0 : StoreTyped Δ Φ [] emptyTaskTy [] := ⟨rfl, fun _ _ h => by simp at h⟩
  exact ne_matchFailure_of_exhSafe
    (steps_preserves_exhSafe hΦ_ty hΦ_exh ht hσ0 hexh (emptyPool_exhSafe Δ) hsteps)

/-! ### Concurrent Pool Preservation & Match-Failure Freedom (`Task` + `MVar` + `Chan` + `Actor`) -/

theorem applyConcEff_preserves_exhSafe {Δ : AdtEnv} {p1 : ConcPool} {σ : Store} {eff : ConcEff}
    (hp : PoolExhSafe Δ p1 σ) (heff : EffExhSafe Δ eff) :
    PoolExhSafe Δ (applyConcEff p1 eff) σ := by
  cases eff with
  | none => exact hp
  | spawnTask body =>
    simp only [applyConcEff]
    refine { hp with task_safe := fun k ek hk => ?_ }
    cases Nat.lt_or_ge k p1.tasks.length with
    | inl hlt =>
      rw [List.getElem?_append_left hlt] at hk
      exact hp.task_safe k ek hk
    | inr hge =>
      rw [List.getElem?_append_right hge] at hk
      have hlt1 : k - p1.tasks.length < 1 := by simpa using lt_length_of_getElem?_eq_some hk
      have heqk : k = p1.tasks.length := Nat.le_antisymm (Nat.le_of_sub_eq_zero (Nat.lt_one_iff.mp hlt1)) hge
      subst heqk; simp at hk; subst hk
      exact heff
  | allocMVar init =>
    simp only [applyConcEff]
    refine { hp with mvar_safe := fun k v hk => ?_ }
    cases Nat.lt_or_ge k p1.mvars.length with
    | inl hlt =>
      rw [List.getElem?_append_left hlt] at hk
      exact hp.mvar_safe k v hk
    | inr hge =>
      rw [List.getElem?_append_right hge] at hk
      have hlt1 : k - p1.mvars.length < 1 := by simpa using lt_length_of_getElem?_eq_some hk
      have heqk : k = p1.mvars.length := Nat.le_antisymm (Nat.le_of_sub_eq_zero (Nat.lt_one_iff.mp hlt1)) hge
      subst heqk; simp at hk
      exact heff v hk
  | takeMVar mid =>
    simp only [applyConcEff]
    refine { hp with mvar_safe := fun k v hk => ?_ }
    by_cases hkm : k = mid
    · subst hkm
      cases Nat.lt_or_ge k p1.mvars.length with
      | inl hlt =>
        rw [List.getElem?_set_self hlt] at hk
        cases hk
      | inr hge =>
        have hge' : (p1.mvars.set k none).length ≤ k := by simp [hge]
        rw [List.getElem?_eq_none hge'] at hk
        cases hk
    · rw [List.getElem?_set_ne (Ne.symm hkm)] at hk
      exact hp.mvar_safe k v hk
  | putMVar mid val =>
    simp only [applyConcEff]
    refine { hp with mvar_safe := fun k v hk => ?_ }
    by_cases hkm : k = mid
    · subst hkm
      cases Nat.lt_or_ge k p1.mvars.length with
      | inl hlt =>
        rw [List.getElem?_set_self hlt] at hk
        simp only [Option.some.injEq] at hk
        subst hk
        exact heff
      | inr hge =>
        have hge' : (p1.mvars.set k (some val)).length ≤ k := by simp [hge]
        rw [List.getElem?_eq_none hge'] at hk
        cases hk
    · rw [List.getElem?_set_ne (Ne.symm hkm)] at hk
      exact hp.mvar_safe k v hk
  | allocChan cap =>
    simp only [applyConcEff]
    refine { hp with chan_safe := fun k ch v hk hv => ?_ }
    cases Nat.lt_or_ge k p1.chans.length with
    | inl hlt =>
      rw [List.getElem?_append_left hlt] at hk
      exact hp.chan_safe k ch v hk hv
    | inr hge =>
      rw [List.getElem?_append_right hge] at hk
      have hlt1 : k - p1.chans.length < 1 := by simpa using lt_length_of_getElem?_eq_some hk
      have heqk : k = p1.chans.length := Nat.le_antisymm (Nat.le_of_sub_eq_zero (Nat.lt_one_iff.mp hlt1)) hge
      subst heqk; simp at hk; subst hk
      simp at hv
  | sendChan cid val =>
    cases hch0 : p1.chans[cid]? with
    | none => simpa [applyConcEff, hch0] using hp
    | some ch0 =>
      have hlt_c : cid < p1.chans.length := lt_length_of_getElem?_eq_some hch0
      simp only [applyConcEff, hch0]
      refine { hp with chan_safe := fun k ch v hk hv => ?_ }
      by_cases hkc : k = cid
      · subst hkc
        simp only [List.getElem?_set_self hlt_c, Option.some.injEq] at hk
        subst hk
        rcases List.mem_append.mp hv with hold | hnew
        · exact hp.chan_safe k ch0 v hch0 hold
        · simp only [List.mem_singleton] at hnew; subst hnew; exact heff
      · rw [List.getElem?_set_ne (Ne.symm hkc)] at hk
        exact hp.chan_safe k ch v hk hv
  | recvChan cid =>
    cases hch0 : p1.chans[cid]? with
    | none => simpa [applyConcEff, hch0] using hp
    | some ch0 =>
      have hlt_c : cid < p1.chans.length := lt_length_of_getElem?_eq_some hch0
      simp only [applyConcEff, hch0]
      refine { hp with chan_safe := fun k ch v hk hv => ?_ }
      by_cases hkc : k = cid
      · subst hkc
        simp only [List.getElem?_set_self hlt_c, Option.some.injEq] at hk
        subst hk
        exact hp.chan_safe k ch0 v hch0 (List.mem_of_mem_tail hv)
      · rw [List.getElem?_set_ne (Ne.symm hkc)] at hk
        exact hp.chan_safe k ch v hk hv
  | closeChan cid =>
    cases hch0 : p1.chans[cid]? with
    | none => simpa [applyConcEff, hch0] using hp
    | some ch0 =>
      have hlt_c : cid < p1.chans.length := lt_length_of_getElem?_eq_some hch0
      simp only [applyConcEff, hch0]
      refine { hp with chan_safe := fun k ch v hk hv => ?_ }
      by_cases hkc : k = cid
      · subst hkc
        simp only [List.getElem?_set_self hlt_c, Option.some.injEq] at hk
        subst hk
        exact hp.chan_safe k ch0 v hch0 hv
      · rw [List.getElem?_set_ne (Ne.symm hkc)] at hk
        exact hp.chan_safe k ch v hk hv
  | spawnActor initExpr =>
    simp only [applyConcEff]
    refine { hp with actor_safe := fun k act hk => ?_ }
    cases Nat.lt_or_ge k p1.actors.length with
    | inl hlt =>
      rw [List.getElem?_append_left hlt] at hk
      exact hp.actor_safe k act hk
    | inr hge =>
      rw [List.getElem?_append_right hge] at hk
      have hlt1 : k - p1.actors.length < 1 := by simpa using lt_length_of_getElem?_eq_some hk
      have heqk : k = p1.actors.length := Nat.le_antisymm (Nat.le_of_sub_eq_zero (Nat.lt_one_iff.mp hlt1)) hge
      subst heqk; simp at hk; subst hk
      exact ⟨heff, fun _ hm => nomatch hm⟩
  | callActor aid handler =>
    cases hact0 : p1.actors[aid]? with
    | none => simpa [applyConcEff, hact0] using hp
    | some act0 =>
      have hlt_a : aid < p1.actors.length := lt_length_of_getElem?_eq_some hact0
      simp only [applyConcEff, hact0]
      refine { hp with
        task_safe  := fun k ek hk => ?_
        actor_safe := fun k act hk => ?_ }
      · cases Nat.lt_or_ge k p1.tasks.length with
        | inl hlt =>
          rw [List.getElem?_append_left hlt] at hk
          exact hp.task_safe k ek hk
        | inr hge =>
          rw [List.getElem?_append_right hge] at hk
          have hlt1 : k - p1.tasks.length < 1 := by simpa using lt_length_of_getElem?_eq_some hk
          have heqk : k = p1.tasks.length := Nat.le_antisymm (Nat.le_of_sub_eq_zero (Nat.lt_one_iff.mp hlt1)) hge
          subst heqk; simp at hk
      · by_cases hka : k = aid
        · subst hka
          simp only [List.getElem?_set_self hlt_a, Option.some.injEq] at hk
          subst hk
          rcases hp.actor_safe k act0 hact0 with ⟨hph, hmb⟩
          refine ⟨hph, fun msg hm => ?_⟩
          rcases List.mem_append.mp hm with hold | hnew
          · exact hmb msg hold
          · simp only [List.mem_singleton] at hnew; subst hnew; exact heff
        · rw [List.getElem?_set_ne (Ne.symm hka)] at hk
          exact hp.actor_safe k act hk
  | sendActor aid handler =>
    cases hact0 : p1.actors[aid]? with
    | none => simpa [applyConcEff, hact0] using hp
    | some act0 =>
      have hlt_a : aid < p1.actors.length := lt_length_of_getElem?_eq_some hact0
      simp only [applyConcEff, hact0]
      refine { hp with actor_safe := fun k act hk => ?_ }
      by_cases hka : k = aid
      · subst hka
        simp only [List.getElem?_set_self hlt_a, Option.some.injEq] at hk
        subst hk
        rcases hp.actor_safe k act0 hact0 with ⟨hph, hmb⟩
        refine ⟨hph, fun msg hm => ?_⟩
        rcases List.mem_append.mp hm with hold | hnew
        · exact hmb msg hold
        · simp only [List.mem_singleton] at hnew; subst hnew; exact heff
      · rw [List.getElem?_set_ne (Ne.symm hka)] at hk
        exact hp.actor_safe k act hk

theorem setPoolTask_preserves_exhSafe {Δ : AdtEnv} {pool : ConcPool} {σ : Store}
    (tid : TaskId) {e' : Expr}
    (hp : PoolExhSafe Δ pool σ) (he' : ExprExhSafe Δ e') :
    PoolExhSafe Δ (setPoolTask pool tid (.running e')) σ := by
  simp only [setPoolTask]
  refine { hp with task_safe := fun k ek hk => ?_ }
  by_cases hkt : k = tid
  · subst hkt
    cases Nat.lt_or_ge k pool.tasks.length with
    | inl hlt =>
      rw [List.getElem?_set_self hlt] at hk
      simp only [Option.some.injEq, TaskEntry.running.injEq] at hk
      subst hk; exact he'
    | inr hge =>
      have hge' : (pool.tasks.set k (.running e')).length ≤ k := by simp [hge]
      rw [List.getElem?_eq_none hge'] at hk
      cases hk
  · rw [List.getElem?_set_ne (Ne.symm hkt)] at hk
    exact hp.task_safe k ek hk

theorem setPoolActorPhase_preserves_exhSafe {Δ : AdtEnv} {pool : ConcPool} {σ : Store}
    (aid : Nat) {ph' : ActorPhase}
    (hp : PoolExhSafe Δ pool σ) (hph' : ActorPhaseExhSafe Δ ph') :
    PoolExhSafe Δ (setPoolActorPhase pool aid ph') σ := by
  cases hact0 : pool.actors[aid]? with
  | none => simpa [setPoolActorPhase, hact0] using hp
  | some act0 =>
    have hlt_a : aid < pool.actors.length := lt_length_of_getElem?_eq_some hact0
    simp only [setPoolActorPhase, hact0, setPoolActor]
    refine { hp with actor_safe := fun k act hk => ?_ }
    by_cases hka : k = aid
    · subst hka
      simp only [List.getElem?_set_self hlt_a, Option.some.injEq] at hk
      subst hk
      exact ⟨hph', (hp.actor_safe k act0 hact0).2⟩
    · rw [List.getElem?_set_ne (Ne.symm hka)] at hk
      exact hp.actor_safe k act hk

private theorem trap_exhSafe_iff_phase (Δ : AdtEnv) (t : Trap) :
    ExprExhSafe Δ (.trap t) ↔ ActorPhaseExhSafe Δ (.failed t) := by
  cases t <;> rfl

theorem concStep_preserves_exhSafe {Δ : AdtEnv} {Φ : FunEnv}
    (hΦ_exh : FunEnvExhSafe Δ Φ)
    {pool pool' : ConcPool} {σ σ' : Store}
    (hinv : ConcInv Δ Φ pool σ)
    (hexh : PoolExhSafe Δ pool σ)
    (hstep : ConcStep Δ Φ pool σ pool' σ') :
    PoolExhSafe Δ pool' σ' := by
  rcases hinv with ⟨Ψ, Θ, _, _, hpool_ty, _⟩
  match hstep with
  | .taskStep (tid := tid) (e := e) (e' := e') (eff := eff) het hs =>
    have hlt_t : tid < pool.tasks.length := lt_length_of_getElem?_eq_some het
    have hlt_Θ : tid < Θ.tasks.length := hpool_ty.tasks_len ▸ hlt_t
    rcases hpool_ty.tasks_ty tid Θ.tasks[tid] (List.getElem?_eq_getElem hlt_Θ) with
      ⟨_, te0, hte0, hrun0⟩
    rw [het] at hte0; cases hte0
    rcases step_preserves_exhSafe hΦ_exh (hrun0 e rfl) (hexh.task_safe tid e het) hexh hs with
      ⟨he', hp', heff'⟩
    exact applyConcEff_preserves_exhSafe (setPoolTask_preserves_exhSafe tid hp' he') heff'
  | .actorInitStep (aid := aid) (act := act) (e := e) (e' := e') (eff := eff) hact hph hs =>
    have hlt_a : aid < pool.actors.length := lt_length_of_getElem?_eq_some hact
    have hlt_Θ : aid < Θ.actors.length := hpool_ty.actors_len ▸ hlt_a
    rcases hpool_ty.actors_ty aid Θ.actors[aid] (List.getElem?_eq_getElem hlt_Θ) with
      ⟨act0, hact0, hphTy, _⟩
    rw [hact] at hact0; cases hact0
    rw [hph] at hphTy
    have hphSafe := (hexh.actor_safe aid act hact).1
    rw [hph] at hphSafe
    rcases step_preserves_exhSafe hΦ_exh hphTy hphSafe hexh hs with ⟨he', hp', heff'⟩
    exact applyConcEff_preserves_exhSafe (setPoolActorPhase_preserves_exhSafe aid hp' (ph' := .init e') he') heff'
  | .actorInitDone (aid := aid) (act := act) (sv := sv) hact hph _ =>
    have hphSafe := (hexh.actor_safe aid act hact).1
    rw [hph] at hphSafe
    exact setPoolActorPhase_preserves_exhSafe aid hexh (ph' := .idle sv) hphSafe
  | .actorInitTrap (aid := aid) (act := act) (t := t) hact hph =>
    have hphSafe := (hexh.actor_safe aid act hact).1
    rw [hph] at hphSafe
    exact setPoolActorPhase_preserves_exhSafe aid hexh ((trap_exhSafe_iff_phase Δ t).mp hphSafe)
  | .actorDequeue (aid := aid) (sv := sv) (msg := msg) (rest := rest) hact =>
    have hlt_a : aid < pool.actors.length := lt_length_of_getElem?_eq_some hact
    rcases hexh.actor_safe aid _ hact with ⟨hsv_safe, hmb_safe⟩
    have hmsg_safe : ExprExhSafe Δ msg.handler := hmb_safe msg (List.mem_cons_self ..)
    simp only [setPoolActor]
    refine { hexh with actor_safe := fun k actk hk => ?_ }
    by_cases hka : k = aid
    · subst hka
      simp only [List.getElem?_set_self hlt_a, Option.some.injEq] at hk
      subst hk
      exact ⟨⟨hsv_safe, hmsg_safe, hsv_safe, trivial⟩,
        fun m hm => hmb_safe m (List.mem_cons_of_mem _ hm)⟩
    · rw [List.getElem?_set_ne (Ne.symm hka)] at hk
      exact hexh.actor_safe k actk hk
  | .actorBusyStep (aid := aid) (act := act) (sv := sv) (e := e) (e' := e') (reply := reply) (eff := eff) hact hph hs =>
    have hlt_a : aid < pool.actors.length := lt_length_of_getElem?_eq_some hact
    have hlt_Θ : aid < Θ.actors.length := hpool_ty.actors_len ▸ hlt_a
    rcases hpool_ty.actors_ty aid Θ.actors[aid] (List.getElem?_eq_getElem hlt_Θ) with
      ⟨act0, hact0, hphTy, _⟩
    rw [hact] at hact0; cases hact0
    rw [hph] at hphTy
    have hphSafe := (hexh.actor_safe aid act hact).1
    rw [hph] at hphSafe
    rcases hphSafe with ⟨hsv_safe, he_safe⟩
    cases reply with
    | none =>
      rcases step_preserves_exhSafe hΦ_exh hphTy.2.2 he_safe hexh hs with ⟨he', hp', heff'⟩
      exact applyConcEff_preserves_exhSafe
        (setPoolActorPhase_preserves_exhSafe aid hp' (ph' := .busy sv e' none) ⟨hsv_safe, he'⟩) heff'
    | some tid =>
      rcases hphTy.2.2 with ⟨_, _, _, heTy⟩
      rcases step_preserves_exhSafe hΦ_exh heTy he_safe hexh hs with ⟨he', hp', heff'⟩
      exact applyConcEff_preserves_exhSafe
        (setPoolActorPhase_preserves_exhSafe aid hp' (ph' := .busy sv e' (some tid)) ⟨hsv_safe, he'⟩) heff'
  | .actorBusyDone (aid := aid) (act := act) (sv := sv) (v := v) (reply := reply) hact hph _ =>
    have hphSafe := (hexh.actor_safe aid act hact).1
    rw [hph] at hphSafe
    rcases hphSafe with ⟨hsv_safe, hv_safe⟩
    have hp1 := setPoolActorPhase_preserves_exhSafe aid hexh (ph' := .idle sv) hsv_safe
    cases reply with
    | none => exact hp1
    | some tid => exact setPoolTask_preserves_exhSafe tid hp1 hv_safe
  | .actorBusyTrap (aid := aid) (act := act) (t := t) (reply := reply) hact hph =>
    have hphSafe := (hexh.actor_safe aid act hact).1
    rw [hph] at hphSafe
    rcases hphSafe with ⟨_, ht_safe⟩
    have hp1 := setPoolActorPhase_preserves_exhSafe aid hexh ((trap_exhSafe_iff_phase Δ t).mp ht_safe)
    cases reply with
    | none => exact hp1
    | some tid => exact setPoolTask_preserves_exhSafe tid hp1 ht_safe
  | .actorFailedReply (aid := aid) (t := t) (msg := msg) (rest := rest) hact =>
    have hlt_a : aid < pool.actors.length := lt_length_of_getElem?_eq_some hact
    rcases hexh.actor_safe aid _ hact with ⟨hfail_safe, hmb_safe⟩
    have ht_safe : ExprExhSafe Δ (.trap t) := (trap_exhSafe_iff_phase Δ t).mpr hfail_safe
    have hp1 : PoolExhSafe Δ (setPoolActor pool aid { phase := .failed t, mailbox := rest }) σ := by
      simp only [setPoolActor]
      refine { hexh with actor_safe := fun k actk hk => ?_ }
      by_cases hka : k = aid
      · subst hka
        simp only [List.getElem?_set_self hlt_a, Option.some.injEq] at hk
        subst hk
        exact ⟨hfail_safe, fun m hm => hmb_safe m (List.mem_cons_of_mem _ hm)⟩
      · rw [List.getElem?_set_ne (Ne.symm hka)] at hk
        exact hexh.actor_safe k actk hk
    cases msg.replyTask with
    | none => exact hp1
    | some tid => exact setPoolTask_preserves_exhSafe tid hp1 ht_safe

theorem concSteps_preserves_exhSafe {Δ : AdtEnv} {Φ : FunEnv}
    (hΦ_ty : FunEnvTyped Δ Φ) (hΦ_exh : FunEnvExhSafe Δ Φ)
    {p0 pool : ConcPool} {σ0 σ : Store}
    (hinv0 : ConcInv Δ Φ p0 σ0)
    (hexh0 : PoolExhSafe Δ p0 σ0)
    (hsteps : ConcSteps Δ Φ p0 σ0 pool σ) :
    PoolExhSafe Δ pool σ := by
  induction hsteps with
  | refl => exact hexh0
  | trans hs _ ih =>
    exact ih (concStep_preserves_inv hΦ_ty hinv0 hs) (concStep_preserves_exhSafe hΦ_exh hinv0 hexh0 hs)

theorem poolExhSafe_init {Δ : AdtEnv} {e0 : Expr} (hexh0 : ExprExhSafe Δ e0) :
    PoolExhSafe Δ (initPool e0) [] := by
  refine
    { store_safe := fun _ _ h => by simp at h
      task_safe  := fun tid e het => ?_
      mvar_safe  := fun _ _ h => by simp [initPool] at h
      chan_safe  := fun _ _ _ h => by simp [initPool] at h
      actor_safe := fun _ _ h => by simp [initPool] at h }
  cases tid with
  | zero =>
    simp [initPool] at het
    subst het
    exact hexh0
  | succ _ =>
    simp [initPool] at het

/-- **Concurrent Match-Failure Freedom (`Task` + `MVar` + `Chan` + `Actor`)**:
    Across arbitrary concurrent task and actor interleavings (`ConcSteps`) from
    `initPool e0`, no `Task` ever evaluates to `.trap .matchFailure` and no
    `Actor` ever enters `.failed .matchFailure`. -/
theorem conc_exhaustive_no_match_failure {Δ : AdtEnv} {Φ : FunEnv}
    (hΦ_ty : FunEnvTyped Δ Φ) (hΦ_exh : FunEnvExhSafe Δ Φ)
    {e0 : Expr} {pool : ConcPool} {σ : Store}
    (ht0 : HasType Δ Φ [] emptyTaskTy emptyCtx e0 .void)
    (hexh0 : ExprExhSafe Δ e0)
    (hsteps : ConcSteps Δ Φ (initPool e0) [] pool σ) :
    (∀ (tid : TaskId) (e : Expr), pool.tasks[tid]? = some (.running e) → e ≠ .trap .matchFailure) ∧
    (∀ (aid : Nat) (act : ActorState), pool.actors[aid]? = some act → act.phase ≠ .failed .matchFailure) := by
  have hp := concSteps_preserves_exhSafe hΦ_ty hΦ_exh (concInv_init ht0) (poolExhSafe_init hexh0) hsteps
  refine ⟨fun tid e het => ne_matchFailure_of_exhSafe (hp.task_safe tid e het),
    fun aid act hact hfail => ?_⟩
  have hph := (hp.actor_safe aid act hact).1
  rw [hfail] at hph
  exact hph

/-! ### Non-Vacuity & Kernel-Evaluated Exhaustiveness Examples -/

private def sampleOptAdtEnv : AdtEnv
  | "OptionInt" => some {
      name := "OptionInt"
      variants := [
        { tag := 0, fields := [] },
        { tag := 1, fields := [.int] }
      ]
    }
  | _ => none

/-- Non-vacuity witness: nested `(OptionInt × Bool)` pattern matrix covering
    `(None, _)`, `(Some(_), true)`, `(Some(_), false)` is accepted by kernel evaluation. -/
theorem sample_nested_exhaustive :
    checkArmsExhaustive sampleOptAdtEnv
      [ (.tuple [.ctor "OptionInt" 0 [], .wild], .lit (.int 0)),
        (.tuple [.ctor "OptionInt" 1 [.var "x"], .lit (.bool true)], .var "x"),
        (.tuple [.ctor "OptionInt" 1 [.wild], .lit (.bool false)], .lit (.int 1)) ] = true := by
  decide

/-- Non-vacuity witness: omitting `(Some(_), false)` is rejected by kernel evaluation. -/
theorem sample_nested_nonexhaustive :
    checkArmsExhaustive sampleOptAdtEnv
      [ (.tuple [.ctor "OptionInt" 0 [], .wild], .lit (.int 0)),
        (.tuple [.ctor "OptionInt" 1 [.var "x"], .lit (.bool true)], .var "x") ] = false := by
  decide

end CoreGeisha
