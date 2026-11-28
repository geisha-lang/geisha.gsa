import CoreGeisha.Syntax
import CoreGeisha.Semantics

/-!
# Core Geisha: Machine-Checked Soundness of Verification Condition Generation (`VCG`)

This module formalizes and machine-proves the soundness of `geisha verify`'s
symbolic verification condition generator (`src/verify.gsa`) directly against the
small-step operational semantics `CoreGeisha.Semantics` (`Step`, `Steps`,
`evalUnOp`, `evalBinOp`, `matchPat`):

1. **Exact Symbolic Semantics (`SVal`, `SForm`, `evalSVal`, `evalSForm`)**:
   - Models `Int32` and `Int64` wrapping two's-complement arithmetic, truncating
     division/remainder (`div`/`rem`/`div64`/`rem64`), masked shifts (`&&& 31` /
     `&&& 63`), `Bool`, `Char` (`UInt32` unsigned comparison), `Unit`, `Loc`,
     and `ADT` tag inspection (`getTag`) by delegating directly to
     `CoreGeisha.evalUnOp` and `CoreGeisha.evalBinOp`.
   - **Fail-Closed**: Unmodeled types/operators (`Float`, `Float32`, `String`,
     closures, concurrency primitives, unannotated loops, aliased mutable calls)
     return `none` rather than vacuously succeeding.
2. **Executable VCG (`vcgenPure`, `vcgen`, `verifyFn`)**:
   - Handles `let_` (with lexical shadowing and `Loc` aliasing), `block`,
     `cellNew`/`cellGet`/`cellSet`, short-circuit `&&`/`||`, `if_` merging,
     `while_` with `invariant` + conservative cell havoc, `assert`/`assume`,
     and modular `applyDir` calls with `requires`, **pairwise non-aliasing of
     mutable `Loc` arguments**, cell havoc, and `ensures`.
3. **Machine-Checked Theorems (Zero `sorry`, Zero custom `axiom`)**:
   - `vcgen_sound`: Valid VCs guarantee `¬ Steps ... (.trap .divByZero) _` and
     post-state & symbolic return value preservation for all terminating runs.
   - `verifyFn_sound`: Function-level contract soundness under `requires` and
     pairwise distinct mutable `Loc` arguments.
   - `while_decreases_terminates`: Well-founded termination of `while_` loops
     under a non-negative strictly decreasing `decreases` variant.
   - Four non-vacuity counterexamples:
     - `int32_overflow_counterexample`
     - `truncating_rem_and_masked_shift_counterexample`
     - `missing_loop_havoc_counterexample`
     - `mutable_alias_call_counterexample`
-/

namespace CoreGeisha

/-! ## Part 1: Step-Indexed Sequential Execution (`StepsN`) & Decomposition Lemmas -/

/-- Step-indexed reflexive-transitive closure of sequential `Step Δ Φ emptyPool`. -/
inductive StepsN (Δ : AdtEnv) (Φ : FunEnv) : Nat → Expr → Store → Expr → Store → Prop where
  | refl (e : Expr) (σ : Store) : StepsN Δ Φ 0 e σ e σ
  | step {n : Nat} {e1 e2 e3 : Expr} {σ1 σ2 σ3 : Store} :
      Step Δ Φ emptyPool e1 σ1 e2 σ2 .none →
      StepsN Δ Φ n e2 σ2 e3 σ3 →
      StepsN Δ Φ (n + 1) e1 σ1 e3 σ3

theorem stepsN_to_steps {Δ : AdtEnv} {Φ : FunEnv} {n : Nat} {e1 e2 : Expr} {σ1 σ2 : Store}
    (h : StepsN Δ Φ n e1 σ1 e2 σ2) : Steps Δ Φ e1 σ1 e2 σ2 := by
  induction h with
  | refl e σ => exact .refl e σ
  | step hs _ ih => exact .trans hs ih

theorem steps_to_stepsN {Δ : AdtEnv} {Φ : FunEnv} {e1 e2 : Expr} {σ1 σ2 : Store}
    (h : Steps Δ Φ e1 σ1 e2 σ2) : ∃ n, StepsN Δ Φ n e1 σ1 e2 σ2 := by
  induction h with
  | refl e σ => exact ⟨0, .refl e σ⟩
  | trans hs _ ih =>
    rcases ih with ⟨n, hn⟩
    exact ⟨n + 1, .step hs hn⟩

theorem steps_trans {Δ : AdtEnv} {Φ : FunEnv} {e1 e2 e3 : Expr} {σ1 σ2 σ3 : Store}
    (h1 : Steps Δ Φ e1 σ1 e2 σ2) (h2 : Steps Δ Φ e2 σ2 e3 σ3) :
    Steps Δ Φ e1 σ1 e3 σ3 := by
  induction h1 with
  | refl => exact h2
  | trans hs _ ih => exact .trans hs (ih h2)

theorem valueList_no_firstTrap {vs : List Expr} {t : Trap}
    (hvs : ∀ v ∈ vs, IsValue v) (hft : ListFirstTrap vs t) : False := by
  induction hft with
  | head t rest =>
    have hv : IsValue (.trap t) := hvs (.trap t) (List.mem_cons_self ..)
    cases hv
  | tail _ _ ih =>
    exact ih (fun v hv => hvs v (List.mem_cons_of_mem _ hv))

mutual
theorem value_no_step {Δ : AdtEnv} {Φ : FunEnv} {pool : ConcPool} {v e' : Expr}
    {σ σ' : Store} {eff : ConcEff}
    (hv : IsValue v) (hs : Step Δ Φ pool v σ e' σ' eff) : False := by
  cases hv with
  | lit => cases hs
  | loc => cases hs
  | taskRef => cases hs
  | syncRef => cases hs
  | lam => cases hs
  | tuple hvs =>
    cases hs with
    | tupleStep hsl => exact valueList_no_stepList hvs hsl
    | tupleTrap hft => exact valueList_no_firstTrap hvs hft
  | makeData _ _ hvs =>
    cases hs with
    | makeDataStep hsl => exact valueList_no_stepList hvs hsl
    | makeDataTrap hft => exact valueList_no_firstTrap hvs hft
termination_by sizeOf v

theorem valueList_no_stepList {Δ : AdtEnv} {Φ : FunEnv} {pool : ConcPool} {vs es' : List Expr}
    {σ σ' : Store} {eff : ConcEff}
    (hvs : ∀ v ∈ vs, IsValue v) (hs : StepList Δ Φ pool vs σ es' σ' eff) : False := by
  cases hs with
  | head h1 => exact value_no_step (hvs _ (List.mem_cons_self ..)) h1
  | tail _ h2 => exact valueList_no_stepList (fun x hx => hvs x (List.mem_cons_of_mem _ hx)) h2
termination_by sizeOf vs
end

theorem trap_no_step {Δ : AdtEnv} {Φ : FunEnv} {pool : ConcPool} {t : Trap} {e' : Expr}
    {σ σ' : Store} {eff : ConcEff}
    (hs : Step Δ Φ pool (.trap t) σ e' σ' eff) : False := by
  cases hs

theorem stepsN_of_value {Δ : AdtEnv} {Φ : FunEnv} {n : Nat} {v e' : Expr} {σ σ' : Store}
    (hv : IsValue v) (h : StepsN Δ Φ n v σ e' σ') : n = 0 ∧ e' = v ∧ σ' = σ := by
  cases h with
  | refl => exact ⟨rfl, rfl, rfl⟩
  | step hs _ => exact False.elim (value_no_step hv hs)

theorem stepsN_of_trap {Δ : AdtEnv} {Φ : FunEnv} {n : Nat} {t : Trap} {e' : Expr} {σ σ' : Store}
    (h : StepsN Δ Φ n (.trap t) σ e' σ') : n = 0 ∧ e' = .trap t ∧ σ' = σ := by
  cases h with
  | refl => exact ⟨rfl, rfl, rfl⟩
  | step hs _ => exact False.elim (trap_no_step hs)

/-- Step-indexed decomposition of `.un op e` reaching a terminal expression. -/
theorem stepsN_un_terminal {Δ : AdtEnv} {Φ : FunEnv} {n : Nat} {op : UnOp} {e res : Expr}
    {σ σ' : Store} (ht : IsTerminal res) (h : StepsN Δ Φ n (.un op e) σ res σ') :
    (∃ k < n, ∃ t, StepsN Δ Φ k e σ (.trap t) σ' ∧ res = .trap t) ∨
    (∃ k < n, ∃ l l', StepsN Δ Φ k e σ (.lit l) σ' ∧ evalUnOp op l = some l' ∧ res = .lit l') := by
  induction n generalizing e σ with
  | zero =>
    cases h
    rcases ht with hv | ⟨_, hEq⟩
    · cases hv
    · cases hEq
  | succ m ih =>
    cases h with
    | step hs hrest =>
      cases hs with
      | unStep hs1 =>
        rcases ih hrest with ⟨k, hk, t, h1, hres⟩ | ⟨k, hk, l, l', h1, hev, hres⟩
        · exact Or.inl ⟨k + 1, Nat.succ_lt_succ hk, t, .step hs1 h1, hres⟩
        · exact Or.inr ⟨k + 1, Nat.succ_lt_succ hk, l, l', .step hs1 h1, hev, hres⟩
      | unTrap =>
        rcases stepsN_of_trap hrest with ⟨_, rfl, rfl⟩
        exact Or.inl ⟨0, Nat.zero_lt_succ m, _, .refl _ _, rfl⟩
      | unVal hev =>
        rcases stepsN_of_value (.lit _) hrest with ⟨_, rfl, rfl⟩
        exact Or.inr ⟨0, Nat.zero_lt_succ m, _, _, .refl _ _, hev, rfl⟩

/-- Step-indexed decomposition of `.bin op e1 e2` for strict binary operators. -/
theorem stepsN_bin_strict_terminal {Δ : AdtEnv} {Φ : FunEnv} {n : Nat} {op : BinOp}
    (hNotAnd : op ≠ .and) (hNotOr : op ≠ .or)
    {e1 e2 res : Expr} {σ σ' : Store} (ht : IsTerminal res)
    (h : StepsN Δ Φ n (.bin op e1 e2) σ res σ') :
    (∃ k < n, ∃ t, StepsN Δ Φ k e1 σ (.trap t) σ' ∧ res = .trap t) ∨
    (∃ k1 k2, k1 + k2 < n ∧ ∃ v1 σ1 t, IsValue v1 ∧
      StepsN Δ Φ k1 e1 σ v1 σ1 ∧ StepsN Δ Φ k2 e2 σ1 (.trap t) σ' ∧ res = .trap t) ∨
    (∃ k1 k2, k1 + k2 < n ∧ ∃ l1 l2 σ1 r,
      StepsN Δ Φ k1 e1 σ (.lit l1) σ1 ∧ StepsN Δ Φ k2 e2 σ1 (.lit l2) σ' ∧
      evalBinOp op l1 l2 = some r ∧
      match r with
      | .val l' => res = .lit l'
      | .trap t => res = .trap t) := by
  induction n generalizing e1 e2 σ with
  | zero =>
    cases h
    rcases ht with hv | ⟨_, hEq⟩
    · cases hv
    · cases hEq
  | succ m ih =>
    cases h with
    | step hs hrest =>
      cases hs with
      | binLeft hs1 =>
        rcases ih hrest with
          ⟨k, hk, t, h1, hres⟩ |
          ⟨k1, k2, hlt, v1, σ1, t, hv1, h1, h2, hres⟩ |
          ⟨k1, k2, hlt, l1, l2, σ1, r, h1, h2, hev, hres⟩
        · exact Or.inl ⟨k + 1, Nat.succ_lt_succ hk, t, .step hs1 h1, hres⟩
        · exact Or.inr (Or.inl ⟨k1 + 1, k2, by omega, v1, σ1, t, hv1, .step hs1 h1, h2, hres⟩)
        · exact Or.inr (Or.inr ⟨k1 + 1, k2, by omega, l1, l2, σ1, r, .step hs1 h1, h2, hev, hres⟩)
      | binLeftTrap =>
        rcases stepsN_of_trap hrest with ⟨_, rfl, rfl⟩
        exact Or.inl ⟨0, Nat.zero_lt_succ m, _, .refl _ _, rfl⟩
      | binAndFalse => exact False.elim (hNotAnd rfl)
      | binAndTrue => exact False.elim (hNotAnd rfl)
      | binOrTrue => exact False.elim (hNotOr rfl)
      | binOrFalse => exact False.elim (hNotOr rfl)
      | binRight _ _ hv1 hs2 =>
        rcases ih hrest with
          ⟨k, hk, t, h1, hres⟩ |
          ⟨k1, k2, hlt, v1', σ1, t, hv1', h1, h2, hres⟩ |
          ⟨k1, k2, hlt, l1, l2, σ1, r, h1, h2, hev, hres⟩
        · rcases stepsN_of_value hv1 h1 with ⟨_, hEq, _⟩
          subst hEq; cases hv1
        · rcases stepsN_of_value hv1 h1 with ⟨rfl, rfl, hσ⟩
          subst hσ
          exact Or.inr (Or.inl ⟨0, k2 + 1, by omega, v1', σ, t, hv1', .refl _ _, .step hs2 h2, hres⟩)
        · rcases stepsN_of_value hv1 h1 with ⟨rfl, rfl, hσ⟩
          subst hσ
          exact Or.inr (Or.inr ⟨0, k2 + 1, by omega, l1, l2, σ, r, .refl _ _, .step hs2 h2, hev, hres⟩)
      | binRightTrap _ _ hv1 =>
        rcases stepsN_of_trap hrest with ⟨_, rfl, rfl⟩
        exact Or.inr (Or.inl ⟨0, 0, Nat.zero_lt_succ m, _, _, _, hv1, .refl _ _, .refl _ _, rfl⟩)
      | binVal hev =>
        rcases stepsN_of_value (.lit _) hrest with ⟨_, rfl, rfl⟩
        exact Or.inr (Or.inr ⟨0, 0, Nat.zero_lt_succ m, _, _, _, .val _, .refl _ _, .refl _ _, hev, rfl⟩)
      | binTrap hev =>
        rcases stepsN_of_trap hrest with ⟨_, rfl, rfl⟩
        exact Or.inr (Or.inr ⟨0, 0, Nat.zero_lt_succ m, _, _, _, .trap _, .refl _ _, .refl _ _, hev, rfl⟩)

/-- Step-indexed decomposition of short-circuit `.bin .and e1 e2`. -/
theorem stepsN_and_terminal {Δ : AdtEnv} {Φ : FunEnv} {n : Nat} {e1 e2 res : Expr}
    {σ σ' : Store} (ht : IsTerminal res)
    (h : StepsN Δ Φ n (.bin .and e1 e2) σ res σ') :
    (∃ k < n, ∃ t, StepsN Δ Φ k e1 σ (.trap t) σ' ∧ res = .trap t) ∨
    (∃ k < n, StepsN Δ Φ k e1 σ (.lit (.bool false)) σ' ∧ res = .lit (.bool false)) ∨
    (∃ k1 k2, k1 + k2 < n ∧ ∃ σ1,
      StepsN Δ Φ k1 e1 σ (.lit (.bool true)) σ1 ∧ StepsN Δ Φ k2 e2 σ1 res σ') := by
  induction n generalizing e1 σ with
  | zero =>
    cases h
    rcases ht with hv | ⟨_, hEq⟩
    · cases hv
    · cases hEq
  | succ m ih =>
    cases h with
    | step hs hrest =>
      cases hs with
      | binLeft hs1 =>
        rcases ih hrest with
          ⟨k, hk, t, h1, hres⟩ |
          ⟨k, hk, h1, hres⟩ |
          ⟨k1, k2, hlt, σ1, h1, h2⟩
        · exact Or.inl ⟨k + 1, Nat.succ_lt_succ hk, t, .step hs1 h1, hres⟩
        · exact Or.inr (Or.inl ⟨k + 1, Nat.succ_lt_succ hk, .step hs1 h1, hres⟩)
        · exact Or.inr (Or.inr ⟨k1 + 1, k2, by omega, σ1, .step hs1 h1, h2⟩)
      | binLeftTrap =>
        rcases stepsN_of_trap hrest with ⟨_, rfl, rfl⟩
        exact Or.inl ⟨0, Nat.zero_lt_succ m, _, .refl _ _, rfl⟩
      | binAndFalse =>
        rcases stepsN_of_value (.lit _) hrest with ⟨_, rfl, rfl⟩
        exact Or.inr (Or.inl ⟨0, Nat.zero_lt_succ m, .refl _ _, rfl⟩)
      | binAndTrue =>
        exact Or.inr (Or.inr ⟨0, m, by omega, σ, .refl _ _, hrest⟩)
      | binRight hna => exact False.elim (hna rfl)
      | binRightTrap hna => exact False.elim (hna rfl)
      | binVal hev => cases hev
      | binTrap hev => cases hev

/-- Step-indexed decomposition of short-circuit `.bin .or e1 e2`. -/
theorem stepsN_or_terminal {Δ : AdtEnv} {Φ : FunEnv} {n : Nat} {e1 e2 res : Expr}
    {σ σ' : Store} (ht : IsTerminal res)
    (h : StepsN Δ Φ n (.bin .or e1 e2) σ res σ') :
    (∃ k < n, ∃ t, StepsN Δ Φ k e1 σ (.trap t) σ' ∧ res = .trap t) ∨
    (∃ k < n, StepsN Δ Φ k e1 σ (.lit (.bool true)) σ' ∧ res = .lit (.bool true)) ∨
    (∃ k1 k2, k1 + k2 < n ∧ ∃ σ1,
      StepsN Δ Φ k1 e1 σ (.lit (.bool false)) σ1 ∧ StepsN Δ Φ k2 e2 σ1 res σ') := by
  induction n generalizing e1 σ with
  | zero =>
    cases h
    rcases ht with hv | ⟨_, hEq⟩
    · cases hv
    · cases hEq
  | succ m ih =>
    cases h with
    | step hs hrest =>
      cases hs with
      | binLeft hs1 =>
        rcases ih hrest with
          ⟨k, hk, t, h1, hres⟩ |
          ⟨k, hk, h1, hres⟩ |
          ⟨k1, k2, hlt, σ1, h1, h2⟩
        · exact Or.inl ⟨k + 1, Nat.succ_lt_succ hk, t, .step hs1 h1, hres⟩
        · exact Or.inr (Or.inl ⟨k + 1, Nat.succ_lt_succ hk, .step hs1 h1, hres⟩)
        · exact Or.inr (Or.inr ⟨k1 + 1, k2, by omega, σ1, .step hs1 h1, h2⟩)
      | binLeftTrap =>
        rcases stepsN_of_trap hrest with ⟨_, rfl, rfl⟩
        exact Or.inl ⟨0, Nat.zero_lt_succ m, _, .refl _ _, rfl⟩
      | binOrTrue =>
        rcases stepsN_of_value (.lit _) hrest with ⟨_, rfl, rfl⟩
        exact Or.inr (Or.inl ⟨0, Nat.zero_lt_succ m, .refl _ _, rfl⟩)
      | binOrFalse =>
        exact Or.inr (Or.inr ⟨0, m, by omega, σ, .refl _ _, hrest⟩)
      | binRight _ hno => exact False.elim (hno rfl)
      | binRightTrap _ hno => exact False.elim (hno rfl)
      | binVal hev => cases hev
      | binTrap hev => cases hev

/-- Step-indexed decomposition of `.let_ x e1 e2`. -/
theorem stepsN_let_terminal {Δ : AdtEnv} {Φ : FunEnv} {n : Nat} {x : Ident} {e1 e2 res : Expr}
    {σ σ' : Store} (ht : IsTerminal res)
    (h : StepsN Δ Φ n (.let_ x e1 e2) σ res σ') :
    (∃ k < n, ∃ t, StepsN Δ Φ k e1 σ (.trap t) σ' ∧ res = .trap t) ∨
    (∃ k1 k2, k1 + k2 < n ∧ ∃ v1 σ1, IsValue v1 ∧
      StepsN Δ Φ k1 e1 σ v1 σ1 ∧ StepsN Δ Φ k2 (subst x v1 e2) σ1 res σ') := by
  induction n generalizing e1 σ with
  | zero =>
    cases h
    rcases ht with hv | ⟨_, hEq⟩
    · cases hv
    · cases hEq
  | succ m ih =>
    cases h with
    | step hs hrest =>
      cases hs with
      | letStep hs1 =>
        rcases ih hrest with ⟨k, hk, t, h1, hres⟩ | ⟨k1, k2, hlt, v1, σ1, hv1, h1, h2⟩
        · exact Or.inl ⟨k + 1, Nat.succ_lt_succ hk, t, .step hs1 h1, hres⟩
        · exact Or.inr ⟨k1 + 1, k2, by omega, v1, σ1, hv1, .step hs1 h1, h2⟩
      | letTrap =>
        rcases stepsN_of_trap hrest with ⟨_, rfl, rfl⟩
        exact Or.inl ⟨0, Nat.zero_lt_succ m, _, .refl _ _, rfl⟩
      | letVal hv1 =>
        exact Or.inr ⟨0, m, by omega, _, σ, hv1, .refl _ _, hrest⟩

/-- Step-indexed decomposition of `.if_ c t e`. -/
theorem stepsN_if_terminal {Δ : AdtEnv} {Φ : FunEnv} {n : Nat} {c t e res : Expr}
    {σ σ' : Store} (ht : IsTerminal res)
    (h : StepsN Δ Φ n (.if_ c t e) σ res σ') :
    (∃ k < n, ∃ tr, StepsN Δ Φ k c σ (.trap tr) σ' ∧ res = .trap tr) ∨
    (∃ k1 k2, k1 + k2 < n ∧ ∃ σ1,
      StepsN Δ Φ k1 c σ (.lit (.bool true)) σ1 ∧ StepsN Δ Φ k2 t σ1 res σ') ∨
    (∃ k1 k2, k1 + k2 < n ∧ ∃ σ1,
      StepsN Δ Φ k1 c σ (.lit (.bool false)) σ1 ∧ StepsN Δ Φ k2 e σ1 res σ') := by
  induction n generalizing c σ with
  | zero =>
    cases h
    rcases ht with hv | ⟨_, hEq⟩
    · cases hv
    · cases hEq
  | succ m ih =>
    cases h with
    | step hs hrest =>
      cases hs with
      | ifStep hs1 =>
        rcases ih hrest with
          ⟨k, hk, tr, h1, hres⟩ |
          ⟨k1, k2, hlt, σ1, h1, h2⟩ |
          ⟨k1, k2, hlt, σ1, h1, h2⟩
        · exact Or.inl ⟨k + 1, Nat.succ_lt_succ hk, tr, .step hs1 h1, hres⟩
        · exact Or.inr (Or.inl ⟨k1 + 1, k2, by omega, σ1, .step hs1 h1, h2⟩)
        · exact Or.inr (Or.inr ⟨k1 + 1, k2, by omega, σ1, .step hs1 h1, h2⟩)
      | ifTrap =>
        rcases stepsN_of_trap hrest with ⟨_, rfl, rfl⟩
        exact Or.inl ⟨0, Nat.zero_lt_succ m, _, .refl _ _, rfl⟩
      | ifTrue =>
        exact Or.inr (Or.inl ⟨0, m, by omega, σ, .refl _ _, hrest⟩)
      | ifFalse =>
        exact Or.inr (Or.inr ⟨0, m, by omega, σ, .refl _ _, hrest⟩)

/-- Step-indexed decomposition of `.block (e1 :: e2 :: es)`. -/
theorem stepsN_blockCons_terminal {Δ : AdtEnv} {Φ : FunEnv} {n : Nat} {e1 e2 : Expr}
    {es : List Expr} {res : Expr} {σ σ' : Store} (ht : IsTerminal res)
    (h : StepsN Δ Φ n (.block (e1 :: e2 :: es)) σ res σ') :
    (∃ k < n, ∃ tr, StepsN Δ Φ k e1 σ (.trap tr) σ' ∧ res = .trap tr) ∨
    (∃ k1 k2, k1 + k2 < n ∧ ∃ v1 σ1, IsValue v1 ∧
      StepsN Δ Φ k1 e1 σ v1 σ1 ∧ StepsN Δ Φ k2 (.block (e2 :: es)) σ1 res σ') := by
  induction n generalizing e1 σ with
  | zero =>
    cases h
    rcases ht with hv | ⟨_, hEq⟩
    · cases hv
    · cases hEq
  | succ m ih =>
    cases h with
    | step hs hrest =>
      cases hs with
      | blockConsStep hs1 =>
        rcases ih hrest with ⟨k, hk, tr, h1, hres⟩ | ⟨k1, k2, hlt, v1, σ1, hv1, h1, h2⟩
        · exact Or.inl ⟨k + 1, Nat.succ_lt_succ hk, tr, .step hs1 h1, hres⟩
        · exact Or.inr ⟨k1 + 1, k2, by omega, v1, σ1, hv1, .step hs1 h1, h2⟩
      | blockConsVal hv1 =>
        exact Or.inr ⟨0, m, by omega, _, σ, hv1, .refl _ _, hrest⟩
      | blockConsTrap =>
        rcases stepsN_of_trap hrest with ⟨_, rfl, rfl⟩
        exact Or.inl ⟨0, Nat.zero_lt_succ m, _, .refl _ _, rfl⟩

/-- Step-indexed decomposition of `.cellNew e`. -/
theorem stepsN_cellNew_terminal {Δ : AdtEnv} {Φ : FunEnv} {n : Nat} {e res : Expr}
    {σ σ' : Store} (ht : IsTerminal res)
    (h : StepsN Δ Φ n (.cellNew e) σ res σ') :
    (∃ k < n, ∃ tr, StepsN Δ Φ k e σ (.trap tr) σ' ∧ res = .trap tr) ∨
    (∃ k < n, ∃ v σ1, IsValue v ∧ StepsN Δ Φ k e σ v σ1 ∧
      res = .loc σ1.length ∧ σ' = σ1 ++ [v]) := by
  induction n generalizing e σ with
  | zero =>
    cases h
    rcases ht with hv | ⟨_, hEq⟩
    · cases hv
    · cases hEq
  | succ m ih =>
    cases h with
    | step hs hrest =>
      cases hs with
      | cellNewStep hs1 =>
        rcases ih hrest with ⟨k, hk, tr, h1, hres⟩ | ⟨k, hk, v, σ1, hv, h1, hres, hσ⟩
        · exact Or.inl ⟨k + 1, Nat.succ_lt_succ hk, tr, .step hs1 h1, hres⟩
        · exact Or.inr ⟨k + 1, Nat.succ_lt_succ hk, v, σ1, hv, .step hs1 h1, hres, hσ⟩
      | cellNewTrap =>
        rcases stepsN_of_trap hrest with ⟨_, rfl, rfl⟩
        exact Or.inl ⟨0, Nat.zero_lt_succ m, _, .refl _ _, rfl⟩
      | cellNewVal hv =>
        rcases stepsN_of_value (.loc _) hrest with ⟨_, rfl, rfl⟩
        exact Or.inr ⟨0, Nat.zero_lt_succ m, _, σ, hv, .refl _ _, rfl, rfl⟩

/-- Step-indexed decomposition of `.cellGet e`. -/
theorem stepsN_cellGet_terminal {Δ : AdtEnv} {Φ : FunEnv} {n : Nat} {e res : Expr}
    {σ σ' : Store} (ht : IsTerminal res)
    (h : StepsN Δ Φ n (.cellGet e) σ res σ') :
    (∃ k < n, ∃ tr, StepsN Δ Φ k e σ (.trap tr) σ' ∧ res = .trap tr) ∨
    (∃ k < n, ∃ l σ1 v, StepsN Δ Φ k e σ (.loc l) σ1 ∧ σ1[l]? = some v ∧
      StepsN Δ Φ (n - 1 - k) v σ1 res σ') := by
  induction n generalizing e σ with
  | zero =>
    cases h
    rcases ht with hv | ⟨_, hEq⟩
    · cases hv
    · cases hEq
  | succ m ih =>
    cases h with
    | step hs hrest =>
      cases hs with
      | cellGetStep hs1 =>
        rcases ih hrest with ⟨k, hk, tr, h1, hres⟩ | ⟨k, hk, l, σ1, v, h1, hget, h2⟩
        · exact Or.inl ⟨k + 1, Nat.succ_lt_succ hk, tr, .step hs1 h1, hres⟩
        · refine Or.inr ⟨k + 1, Nat.succ_lt_succ hk, l, σ1, v, .step hs1 h1, hget, ?_⟩
          have : m + 1 - 1 - (k + 1) = m - 1 - k := by omega
          rw [this]; exact h2
      | cellGetTrap =>
        rcases stepsN_of_trap hrest with ⟨_, rfl, rfl⟩
        exact Or.inl ⟨0, Nat.zero_lt_succ m, _, .refl _ _, rfl⟩
      | cellGetVal hget =>
        refine Or.inr ⟨0, Nat.zero_lt_succ m, _, σ, _, .refl _ _, hget, ?_⟩
        simpa using hrest

/-- Step-indexed decomposition of `.cellSet e1 e2`. -/
theorem stepsN_cellSet_terminal {Δ : AdtEnv} {Φ : FunEnv} {n : Nat} {e1 e2 res : Expr}
    {σ σ' : Store} (ht : IsTerminal res)
    (h : StepsN Δ Φ n (.cellSet e1 e2) σ res σ') :
    (∃ k < n, ∃ tr, StepsN Δ Φ k e1 σ (.trap tr) σ' ∧ res = .trap tr) ∨
    (∃ k1 k2, k1 + k2 < n ∧ ∃ v1 σ1 tr, IsValue v1 ∧
      StepsN Δ Φ k1 e1 σ v1 σ1 ∧ StepsN Δ Φ k2 e2 σ1 (.trap tr) σ' ∧ res = .trap tr) ∨
    (∃ k1 k2, k1 + k2 < n ∧ ∃ l v2 σ1 σ2, IsValue v2 ∧ l < σ2.length ∧
      StepsN Δ Φ k1 e1 σ (.loc l) σ1 ∧ StepsN Δ Φ k2 e2 σ1 v2 σ2 ∧
      res = .lit .unit ∧ σ' = σ2.set l v2) := by
  induction n generalizing e1 e2 σ with
  | zero =>
    cases h
    rcases ht with hv | ⟨_, hEq⟩
    · cases hv
    · cases hEq
  | succ m ih =>
    cases h with
    | step hs hrest =>
      cases hs with
      | cellSetLeft hs1 =>
        rcases ih hrest with
          ⟨k, hk, tr, h1, hres⟩ |
          ⟨k1, k2, hlt, v1, σ1, tr, hv1, h1, h2, hres⟩ |
          ⟨k1, k2, hlt, l, v2, σ1, σ2, hv2, hlen, h1, h2, hres, hσ⟩
        · exact Or.inl ⟨k + 1, Nat.succ_lt_succ hk, tr, .step hs1 h1, hres⟩
        · exact Or.inr (Or.inl ⟨k1 + 1, k2, by omega, v1, σ1, tr, hv1, .step hs1 h1, h2, hres⟩)
        · exact Or.inr (Or.inr ⟨k1 + 1, k2, by omega, l, v2, σ1, σ2, hv2, hlen, .step hs1 h1, h2, hres, hσ⟩)
      | cellSetLeftTrap =>
        rcases stepsN_of_trap hrest with ⟨_, rfl, rfl⟩
        exact Or.inl ⟨0, Nat.zero_lt_succ m, _, .refl _ _, rfl⟩
      | cellSetRight hv1 hs2 =>
        rcases ih hrest with
          ⟨k, hk, tr, h1, hres⟩ |
          ⟨k1, k2, hlt, v1', σ1, tr, hv1', h1, h2, hres⟩ |
          ⟨k1, k2, hlt, l, v2, σ1, σ2, hv2, hlen, h1, h2, hres, hσ⟩
        · rcases stepsN_of_value hv1 h1 with ⟨_, hEq, _⟩; subst hEq; cases hv1
        · rcases stepsN_of_value hv1 h1 with ⟨rfl, rfl, hσ1⟩
          subst hσ1
          exact Or.inr (Or.inl ⟨0, k2 + 1, by omega, v1', σ, tr, hv1', .refl _ _, .step hs2 h2, hres⟩)
        · rcases stepsN_of_value hv1 h1 with ⟨rfl, rfl, hσ1⟩
          subst hσ1
          exact Or.inr (Or.inr ⟨0, k2 + 1, by omega, l, v2, σ, σ2, hv2, hlen, .refl _ _, .step hs2 h2, hres, hσ⟩)
      | cellSetRightTrap hv1 =>
        rcases stepsN_of_trap hrest with ⟨_, rfl, rfl⟩
        exact Or.inr (Or.inl ⟨0, 0, Nat.zero_lt_succ m, _, _, _, hv1, .refl _ _, .refl _ _, rfl⟩)
      | cellSetVal hlen hv2 =>
        rcases stepsN_of_value (.lit _) hrest with ⟨_, rfl, rfl⟩
        exact Or.inr (Or.inr ⟨0, 0, Nat.zero_lt_succ m, _, _, σ, σ, hv2, hlen, .refl _ _, .refl _ _, rfl, rfl⟩)

/-- Step-indexed decomposition of `.getTag e`. -/
theorem stepsN_getTag_terminal {Δ : AdtEnv} {Φ : FunEnv} {n : Nat} {e res : Expr}
    {σ σ' : Store} (ht : IsTerminal res)
    (h : StepsN Δ Φ n (.getTag e) σ res σ') :
    (∃ k < n, ∃ tr, StepsN Δ Φ k e σ (.trap tr) σ' ∧ res = .trap tr) ∨
    (∃ k < n, ∃ adt tag vs, (∀ v ∈ vs, IsValue v) ∧
      StepsN Δ Φ k e σ (.makeData adt tag vs) σ' ∧ res = .lit (.int (Int32.ofNat tag))) := by
  induction n generalizing e σ with
  | zero =>
    cases h
    rcases ht with hv | ⟨_, hEq⟩
    · cases hv
    · cases hEq
  | succ m ih =>
    cases h with
    | step hs hrest =>
      cases hs with
      | getTagStep hs1 =>
        rcases ih hrest with ⟨k, hk, tr, h1, hres⟩ | ⟨k, hk, adt, tag, vs, hvs, h1, hres⟩
        · exact Or.inl ⟨k + 1, Nat.succ_lt_succ hk, tr, .step hs1 h1, hres⟩
        · exact Or.inr ⟨k + 1, Nat.succ_lt_succ hk, adt, tag, vs, hvs, .step hs1 h1, hres⟩
      | getTagTrap =>
        rcases stepsN_of_trap hrest with ⟨_, rfl, rfl⟩
        exact Or.inl ⟨0, Nat.zero_lt_succ m, _, .refl _ _, rfl⟩
      | getTagVal hvs =>
        rcases stepsN_of_value (.lit _) hrest with ⟨_, rfl, rfl⟩
        exact Or.inr ⟨0, Nat.zero_lt_succ m, _, _, _, hvs, .refl _ _, rfl⟩

/-- Step-indexed unfolding of `.while_ c b` reaching a terminal expression. -/
theorem stepsN_while_terminal {Δ : AdtEnv} {Φ : FunEnv} {n : Nat} {c b res : Expr}
    {σ σ' : Store} (ht : IsTerminal res)
    (h : StepsN Δ Φ n (.while_ c b) σ res σ') :
    ∃ m < n, StepsN Δ Φ m (.if_ c (.block [b, .while_ c b]) (.lit .unit)) σ res σ' := by
  cases h with
  | refl =>
    rcases ht with hv | ⟨_, hEq⟩
    · cases hv
    · cases hEq
  | step hs hrest =>
    cases hs with
    | whileUnfold => exact ⟨_, Nat.lt_succ_self _, hrest⟩

/-- Step-indexed decomposition of `.applyDir name [e1]` reaching a terminal expression. -/
theorem stepsN_applyDir_one_terminal {Δ : AdtEnv} {Φ : FunEnv} {n : Nat} {name : Ident}
    {e1 res : Expr} {σ σ' : Store} (ht : IsTerminal res)
    (h : StepsN Δ Φ n (.applyDir name [e1]) σ res σ') :
    (∃ k < n, ∃ tr, StepsN Δ Φ k e1 σ (.trap tr) σ' ∧ res = .trap tr) ∨
    (∃ k1 k2, k1 + k2 < n ∧ ∃ v1 σ1 fd, IsValue v1 ∧
      StepsN Δ Φ k1 e1 σ v1 σ1 ∧
      Φ name = some fd ∧ fd.params.length = 1 ∧
      StepsN Δ Φ k2 (substMany (zipParams fd.params [v1]) fd.body) σ1 res σ') := by
  induction n generalizing e1 σ with
  | zero =>
    cases h; rcases ht with hv | ⟨_, hEq⟩
    · cases hv
    · cases hEq
  | succ m ih =>
    cases h with
    | step hs hrest =>
      cases hs with
      | applyDirArgs hsl =>
        cases hsl with
        | head hs1 =>
          rcases ih hrest with ⟨k, hk, tr, h1, hres⟩ | ⟨k1, k2, hlt, v1, σ1, fd, hv1, h1, hfd, hlen, h2⟩
          · exact Or.inl ⟨k + 1, Nat.succ_lt_succ hk, tr, .step hs1 h1, hres⟩
          · exact Or.inr ⟨k1 + 1, k2, by omega, v1, σ1, fd, hv1, .step hs1 h1, hfd, hlen, h2⟩
        | tail _ h2 => cases h2
      | applyDirTrap hft =>
        cases hft with
        | head =>
          rcases stepsN_of_trap hrest with ⟨_, rfl, rfl⟩
          exact Or.inl ⟨0, Nat.zero_lt_succ m, _, .refl _ _, rfl⟩
        | tail _ h2 => cases h2
      | applyDirBeta hfd hvs hlen =>
        exact Or.inr ⟨0, m, by omega, e1, σ, _, hvs e1 (List.mem_cons_self ..), .refl _ _, hfd, hlen.symm, hrest⟩

/-- Step-indexed decomposition of `.applyDir name args` when `args` are already values. -/
theorem stepsN_applyDir_vals_terminal {Δ : AdtEnv} {Φ : FunEnv} {n : Nat} {name : Ident}
    {vs : List Expr} {res : Expr} {σ σ' : Store}
    (hvs : ∀ v ∈ vs, IsValue v) (ht : IsTerminal res)
    (h : StepsN Δ Φ n (.applyDir name vs) σ res σ') :
    ∃ m < n, ∃ fd, Φ name = some fd ∧ vs.length = fd.params.length ∧
      StepsN Δ Φ m (substMany (zipParams fd.params vs) fd.body) σ res σ' := by
  cases h with
  | refl =>
    rcases ht with hv | ⟨_, hEq⟩
    · cases hv
    · cases hEq
  | step hs hrest =>
    cases hs with
    | applyDirArgs hsl =>
      exact False.elim (valueList_no_stepList hvs hsl)
    | applyDirTrap hft =>
      exact False.elim (valueList_no_firstTrap hvs hft)
    | applyDirBeta hfd _ hlen =>
      exact ⟨_, Nat.lt_succ_self _, _, hfd, hlen, hrest⟩

/-- Prefix decomposition of `StepList` when `pre` are all values: the step occurs in `e1`
    (if `e1` is not a value) or in `rest` (if `e1` is a value). -/
private theorem stepList_append_values {Δ : AdtEnv} {Φ : FunEnv} {pool : ConcPool}
    {pre : List Expr} {e1 : Expr} {rest es' : List Expr} {σ σ' : Store} {eff : ConcEff}
    (hpre : ∀ v ∈ pre, IsValue v)
    (h : StepList Δ Φ pool (pre ++ e1 :: rest) σ es' σ' eff) :
    (∃ e1', Step Δ Φ pool e1 σ e1' σ' eff ∧ es' = pre ++ e1' :: rest) ∨
    (IsValue e1 ∧ ∃ rest', StepList Δ Φ pool rest σ rest' σ' eff ∧ es' = (pre ++ [e1]) ++ rest') := by
  induction pre generalizing es' with
  | nil =>
    simp only [List.nil_append] at h ⊢
    cases h with
    | head hs => exact Or.inl ⟨_, hs, rfl⟩
    | tail hv hsl => exact Or.inr ⟨hv, _, hsl, rfl⟩
  | cons p ps ih =>
    have hp : IsValue p := hpre p (List.mem_cons_self ..)
    have hps : ∀ v ∈ ps, IsValue v := fun v hv => hpre v (List.mem_cons_of_mem _ hv)
    simp only [List.cons_append] at h ⊢
    cases h with
    | head hs => exact False.elim (value_no_step hp hs)
    | tail _ hsl =>
      rcases ih hps hsl with ⟨e1', hs1, rfl⟩ | ⟨hv1, rest', hsl', rfl⟩
      · exact Or.inl ⟨e1', hs1, rfl⟩
      · exact Or.inr ⟨hv1, rest', hsl', by simp [List.cons_append]⟩

/-- Prefix decomposition of `ListFirstTrap` when `pre` are all values. -/
private theorem firstTrap_append_values {pre : List Expr} {e1 : Expr} {rest : List Expr} {t : Trap}
    (hpre : ∀ v ∈ pre, IsValue v) (h : ListFirstTrap (pre ++ e1 :: rest) t) :
    e1 = .trap t ∨ (IsValue e1 ∧ ListFirstTrap rest t) := by
  induction pre with
  | nil =>
    simp only [List.nil_append] at h
    cases h with
    | head => exact Or.inl rfl
    | tail hv hft => exact Or.inr ⟨hv, hft⟩
  | cons p ps ih =>
    have hp : IsValue p := hpre p (List.mem_cons_self ..)
    have hps : ∀ v ∈ ps, IsValue v := fun v hv => hpre v (List.mem_cons_of_mem _ hv)
    simp only [List.cons_append] at h
    cases h with
    | head => cases hp
    | tail _ hft => exact ih hps hft

/-- Step-indexed decomposition of `.applyDir name (pre ++ e1 :: rest)` when `pre` are already
    values: either `e1` traps, or `e1` evaluates to a value `v1` and `.applyDir name ((pre ++ [v1]) ++ rest)`
    continues to `res`. -/
theorem stepsN_applyDir_cons_terminal {Δ : AdtEnv} {Φ : FunEnv} {n : Nat} {name : Ident}
    {pre : List Expr} {e1 : Expr} {rest : List Expr} {res : Expr} {σ σ' : Store}
    (hpre : ∀ v ∈ pre, IsValue v) (ht : IsTerminal res)
    (h : StepsN Δ Φ n (.applyDir name (pre ++ e1 :: rest)) σ res σ') :
    (∃ k1 ≤ n, ∃ t, StepsN Δ Φ k1 e1 σ (.trap t) σ' ∧ res = .trap t) ∨
    (∃ k1 k2, k1 + k2 ≤ n ∧ ∃ v1 σ1, IsValue v1 ∧
      StepsN Δ Φ k1 e1 σ v1 σ1 ∧ StepsN Δ Φ k2 (.applyDir name ((pre ++ [v1]) ++ rest)) σ1 res σ') := by
  induction n generalizing e1 σ with
  | zero =>
    cases h
    rcases ht with hv | ⟨_, hEq⟩
    · cases hv
    · cases hEq
  | succ m ih =>
    cases h with
    | step hs hrest =>
      cases hs with
      | applyDirArgs hsl =>
        rcases stepList_append_values hpre hsl with ⟨e1', hs1, rfl⟩ | ⟨hv1, rest', hsl', rfl⟩
        · rcases ih hrest with ⟨k1, hk1, t, hst1, hEq⟩ | ⟨k1, k2, hsum, v1, σ1, hv1, hst1, hst2⟩
          · exact Or.inl ⟨k1 + 1, by omega, t, .step hs1 hst1, hEq⟩
          · exact Or.inr ⟨k1 + 1, k2, by omega, v1, σ1, hv1, .step hs1 hst1, hst2⟩
        · rename_i σ2
          exact Or.inr ⟨0, m + 1, by omega, e1, σ, hv1, .refl _ _,
            .step (.applyDirArgs (by
              have hLiftS : ∀ (ps : List Expr), (∀ v ∈ ps, IsValue v) →
                  StepList Δ Φ emptyPool rest σ rest' σ2 ConcEff.none →
                  StepList Δ Φ emptyPool (ps ++ rest) σ (ps ++ rest') σ2 ConcEff.none := by
                intro ps hps hs
                induction ps with
                | nil => exact hs
                | cons q qs ihq =>
                  simp only [List.cons_append]
                  exact .tail (hps q (List.mem_cons_self ..)) (ihq (fun v hv => hps v (List.mem_cons_of_mem _ hv)))
              exact hLiftS (pre ++ [e1]) (fun v hv => by
                rcases List.mem_append.mp hv with h1 | h2
                · exact hpre v h1
                · simp at h2; subst h2; exact hv1) hsl')) hrest⟩
      | applyDirTrap hft =>
        rcases firstTrap_append_values hpre hft with rfl | ⟨hv1, hft'⟩
        · rcases stepsN_of_trap hrest with ⟨_, rfl, rfl⟩
          exact Or.inl ⟨0, by omega, _, .refl _ _, rfl⟩
        · rename_i t
          exact Or.inr ⟨0, m + 1, by omega, e1, σ, hv1, .refl _ _,
            .step (.applyDirTrap (by
              have hLift : ∀ (ps : List Expr), (∀ v ∈ ps, IsValue v) → ListFirstTrap rest t → ListFirstTrap (ps ++ rest) t := by
                intro ps hps hf
                induction ps with
                | nil => exact hf
                | cons q qs ihq =>
                  simp only [List.cons_append]
                  exact .tail (hps q (List.mem_cons_self ..)) (ihq (fun v hv => hps v (List.mem_cons_of_mem _ hv)))
              exact hLift (pre ++ [e1]) (fun v hv => by
                rcases List.mem_append.mp hv with h1 | h2
                · exact hpre v h1
                · simp at h2; subst h2; exact hv1) hft')) hrest⟩
      | applyDirBeta hfd hvs hlen =>
        have hv1 : IsValue e1 := hvs e1 (List.mem_append_right pre (List.mem_cons_self ..))
        have hEqArgs : pre ++ e1 :: rest = (pre ++ [e1]) ++ rest := by simp [List.append_assoc]
        exact Or.inr ⟨0, m + 1, by omega, e1, σ, hv1, .refl _ _,
          .step (.applyDirBeta hfd (by rw [← hEqArgs]; exact hvs) (by rw [← hEqArgs]; exact hlen))
            (by rw [← hEqArgs]; exact hrest)⟩

/-- Map symbolic location indices `.loc k` to concrete physical locations `.loc (L k)`,
    leaving all non-location values (literals, ADTs, etc.) unchanged. -/
def mapExprLoc (L : Loc → Loc) : Expr → Expr
  | .loc k => .loc (L k)
  | e => e

theorem mapExprLoc_lit (L : Loc → Loc) (c : Lit) : mapExprLoc L (.lit c) = .lit c := rfl
theorem mapExprLoc_loc (L : Loc → Loc) (k : Loc) : mapExprLoc L (.loc k) = .loc (L k) := rfl

theorem mapExprLoc_eq_lit {L : Loc → Loc} {e : Expr} {c : Lit}
    (h : mapExprLoc L e = .lit c) : e = .lit c := by
  cases e <;> simp [mapExprLoc] at h; subst h; rfl

theorem mapExprLoc_eq_loc {L : Loc → Loc} {e : Expr} {l : Loc}
    (h : mapExprLoc L e = .loc l) : ∃ k, e = .loc k ∧ L k = l := by
  cases e <;> simp [mapExprLoc] at h; exact ⟨_, rfl, h⟩

theorem mapExprLoc_closed {L : Loc → Loc} {e : Expr}
    (hv : IsValue e) (hcl : freeVars e = []) :
    IsValue (mapExprLoc L e) ∧ freeVars (mapExprLoc L e) = [] := by
  cases e with
  | loc k => exact ⟨.loc (L k), rfl⟩
  | _ => exact ⟨hv, hcl⟩

/-- Modeled scalar types whose values are constrained by `SForm.hasTy`. -/
def isModeledScalarTy : Ty → Bool
  | .int | .int64 | .bool | .char | .void => true
  | _ => false

/-- Runtime value typing predicate for modeled scalar types (including `Char < 256`
    matching Geisha's unsigned 8-bit `i8` codegen representation). -/
def valHasTy (v : Expr) : Ty → Prop
  | .int   => ∃ n : Int32, v = .lit (.int n)
  | .int64 => ∃ n : Int64, v = .lit (.int64 n)
  | .bool  => ∃ b : Bool, v = .lit (.bool b)
  | .char  => ∃ c : UInt32, v = .lit (.char c) ∧ c.toNat < 256
  | .void  => v = .lit .unit
  | _      => False

theorem valHasTy_eq_lit {v : Expr} {ty : Ty} (h : valHasTy v ty) :
    ∃ c : Lit, v = .lit c := by
  cases ty with
  | int => rcases h with ⟨n, rfl⟩; exact ⟨.int n, rfl⟩
  | int64 => rcases h with ⟨n, rfl⟩; exact ⟨.int64 n, rfl⟩
  | bool => rcases h with ⟨b, rfl⟩; exact ⟨.bool b, rfl⟩
  | char => rcases h with ⟨c, rfl, _⟩; exact ⟨.char c, rfl⟩
  | void => exact ⟨.unit, h⟩
  | _ => exact False.elim h

theorem valHasTy_not_loc {v : Expr} {ty : Ty} (h : valHasTy v ty) (l : Loc) :
    v ≠ .loc l := by
  rcases valHasTy_eq_lit h with ⟨_, rfl⟩; simp

theorem valHasTy_mapExprLoc {L : Loc → Loc} {v : Expr} {ty : Ty} (h : valHasTy v ty) :
    mapExprLoc L v = v := by
  rcases valHasTy_eq_lit h with ⟨_, rfl⟩; rfl

/-! ## Part 2: Closed Environments & `substMany` Commutation Lemmas -/

/-- Lookup the first binding for `x` in an association list. -/
def assocLookup {α : Type} (xs : List (Ident × α)) (x : Ident) : Option α :=
  match xs with
  | [] => none
  | (k, v) :: rest => if k == x then some v else assocLookup rest x

/-- Remove all bindings for `x` from an association list. -/
def assocRemove {α : Type} (x : Ident) (xs : List (Ident × α)) : List (Ident × α) :=
  xs.filter (fun p => p.1 != x)

/-- Lookup the first binding for `l : Loc` in a symbolic cell map. -/
def locLookup {α : Type} (xs : List (Loc × α)) (l : Loc) : Option α :=
  match xs with
  | [] => none
  | (k, v) :: rest => if k == l then some v else locLookup rest l

theorem assocLookup_mem {α : Type} {xs : List (Ident × α)} {x : Ident} {v : α}
    (h : assocLookup xs x = some v) : (x, v) ∈ xs := by
  induction xs with
  | nil => simp [assocLookup] at h
  | cons p rest ih =>
    rcases p with ⟨k, w⟩
    simp only [assocLookup] at h
    by_cases hkx : (k == x) = true
    · simp [hkx] at h
      have hk : k = x := eq_of_beq hkx
      subst hk; subst h; exact List.mem_cons_self ..
    · simp [hkx] at h
      exact List.mem_cons_of_mem _ (ih h)

theorem locLookup_mem {α : Type} {xs : List (Loc × α)} {l : Loc} {v : α}
    (h : locLookup xs l = some v) : (l, v) ∈ xs := by
  induction xs with
  | nil => simp [locLookup] at h
  | cons p rest ih =>
    rcases p with ⟨k, w⟩
    simp only [locLookup] at h
    by_cases hkl : (k == l) = true
    · simp [hkl] at h
      have hk : k = l := eq_of_beq hkl
      subst hk; subst h; exact List.mem_cons_self ..
    · simp [hkl] at h
      exact List.mem_cons_of_mem _ (ih h)

/-- An environment of closed values (no free variables). -/
def ClosedEnv (ρ : List (Ident × Expr)) : Prop :=
  ∀ p ∈ ρ, IsValue p.2 ∧ freeVars p.2 = []

mutual
theorem subst_not_free {x : Ident} {v e : Expr} (h : x ∉ freeVars e) :
    subst x v e = e := by
  cases e with
  | lit _ | loc _ | taskRef _ | syncRef _ _ | trap _ => rfl
  | var y =>
    simp only [freeVars, List.mem_singleton] at h
    have hne : (y == x) = false := beq_false_of_ne (Ne.symm h)
    simp [subst, hne]
  | tuple es => simp [subst, substList_not_free (by simpa [freeVars] using h)]
  | block es => simp [subst, substList_not_free (by simpa [freeVars] using h)]
  | lam m ps ret body =>
    simp only [subst]
    by_cases hmem : ps.any (fun p => p.1 == x) = true
    · simp [hmem]
    · have hnb : x ∉ freeVars body := by
        intro hb; apply h; simp [freeVars, hb, hmem]
      simp [hmem, subst_not_free hnb]
  | apply fn args =>
    simp only [freeVars, List.mem_append, not_or] at h
    simp [subst, subst_not_free h.1, substList_not_free h.2]
  | applyDir fn args =>
    simp [subst, substList_not_free (by simpa [freeVars] using h)]
  | bin op e1 e2 =>
    simp only [freeVars, List.mem_append, not_or] at h
    simp [subst, subst_not_free h.1, subst_not_free h.2]
  | un op e1 =>
    simp [subst, subst_not_free (by simpa [freeVars] using h)]
  | let_ y e1 e2 =>
    simp only [freeVars, List.mem_append, not_or] at h
    simp only [subst, subst_not_free h.1]
    by_cases hyx : (y == x) = true
    · simp [hyx]
    · have hne : (x != y) = true := by
        simp only [bne_iff_ne]; intro heq; subst heq; simp at hyx
      have hnb : x ∉ freeVars e2 := by
        intro hb; exact h.2 (List.mem_filter.mpr ⟨hb, hne⟩)
      simp [hyx, subst_not_free hnb]
  | if_ c t e =>
    simp only [freeVars, List.mem_append, not_or] at h
    simp [subst, subst_not_free h.1.1, subst_not_free h.1.2, subst_not_free h.2]
  | while_ c b =>
    simp only [freeVars, List.mem_append, not_or] at h
    simp [subst, subst_not_free h.1, subst_not_free h.2]
  | match_ s arms =>
    simp only [freeVars, List.mem_append, not_or] at h
    simp [subst, subst_not_free h.1, substArms_not_free h.2]
  | makeData adt tag es =>
    simp [subst, substList_not_free (by simpa [freeVars] using h)]
  | getTag e1 => simp [subst, subst_not_free (by simpa [freeVars] using h)]
  | cellNew e1 => simp [subst, subst_not_free (by simpa [freeVars] using h)]
  | cellGet e1 => simp [subst, subst_not_free (by simpa [freeVars] using h)]
  | cellSet e1 e2 =>
    simp only [freeVars, List.mem_append, not_or] at h
    simp [subst, subst_not_free h.1, subst_not_free h.2]
  | spawn e1 => simp [subst, subst_not_free (by simpa [freeVars] using h)]
  | await e1 => simp [subst, subst_not_free (by simpa [freeVars] using h)]
  | concPrim op args =>
    simp [subst, substList_not_free (by simpa [freeVars] using h)]
termination_by sizeOf e

theorem substList_not_free {x : Ident} {v : Expr} {es : List Expr} (h : x ∉ freeVarsList es) :
    substList x v es = es := by
  cases es with
  | nil => rfl
  | cons a rest =>
    simp only [freeVarsList, List.mem_append, not_or] at h
    simp [substList, subst_not_free h.1, substList_not_free h.2]
termination_by sizeOf es

theorem substArms_not_free {x : Ident} {v : Expr} {arms : List (Pat × Expr)}
    (h : x ∉ freeVarsArms arms) : substArms x v arms = arms := by
  match arms with
  | [] => rfl
  | (p, body) :: rest =>
    simp only [freeVarsArms, List.mem_append, not_or] at h
    simp only [substArms, substArms_not_free h.2]
    by_cases hmem : x ∈ patBoundNames p
    · simp [hmem]
    · have hnb : x ∉ freeVars body := by
        intro hb; exact h.1 (List.mem_filter.mpr ⟨hb, by simp [hmem]⟩)
      simp [hmem, subst_not_free hnb]
termination_by sizeOf arms
end

theorem substMany_of_closed {ρ : List (Ident × Expr)} {v : Expr} (h : freeVars v = []) :
    substMany ρ v = v := by
  induction ρ with
  | nil => rfl
  | cons p rest ih =>
    rcases p with ⟨x, w⟩
    simp only [substMany]
    rw [subst_not_free (by simp [h])]
    exact ih

theorem substMany_lit (ρ : List (Ident × Expr)) (l : Lit) :
    substMany ρ (.lit l) = .lit l := by
  induction ρ with | nil => rfl | cons p rest ih => exact ih

theorem substMany_loc (ρ : List (Ident × Expr)) (l : Loc) :
    substMany ρ (.loc l) = .loc l := by
  induction ρ with | nil => rfl | cons p rest ih => exact ih

theorem substMany_var {ρ : List (Ident × Expr)} (hρ : ClosedEnv ρ) (x : Ident) :
    substMany ρ (.var x) = match assocLookup ρ x with | some v => v | none => .var x := by
  induction ρ with
  | nil => rfl
  | cons p rest ih =>
    rcases p with ⟨y, w⟩
    have hrest : ClosedEnv rest := fun q hq => hρ q (List.mem_cons_of_mem _ hq)
    have hw : freeVars w = [] := (hρ (y, w) (List.mem_cons_self ..)).2
    simp only [substMany, subst, assocLookup]
    by_cases hxy : (x == y) = true
    · have hyx : (y == x) = true := by
        have := eq_of_beq hxy; subst this; exact beq_self_eq_true _
      simp [hxy, hyx, substMany_of_closed hw]
    · have hyx : (y == x) = false := by
        cases h : (y == x)
        · rfl
        · have := eq_of_beq h; subst this; simp at hxy
      simp [hxy, hyx, ih hrest]

theorem substMany_un (ρ : List (Ident × Expr)) (op : UnOp) (e : Expr) :
    substMany ρ (.un op e) = .un op (substMany ρ e) := by
  induction ρ generalizing e with | nil => rfl | cons p rest ih => exact ih _

theorem substMany_bin (ρ : List (Ident × Expr)) (op : BinOp) (e1 e2 : Expr) :
    substMany ρ (.bin op e1 e2) = .bin op (substMany ρ e1) (substMany ρ e2) := by
  induction ρ generalizing e1 e2 with | nil => rfl | cons p rest ih => exact ih _ _

theorem substMany_if (ρ : List (Ident × Expr)) (c t e : Expr) :
    substMany ρ (.if_ c t e) = .if_ (substMany ρ c) (substMany ρ t) (substMany ρ e) := by
  induction ρ generalizing c t e with | nil => rfl | cons p rest ih => exact ih _ _ _

theorem substMany_while (ρ : List (Ident × Expr)) (c b : Expr) :
    substMany ρ (.while_ c b) = .while_ (substMany ρ c) (substMany ρ b) := by
  induction ρ generalizing c b with | nil => rfl | cons p rest ih => exact ih _ _

theorem substMany_cellNew (ρ : List (Ident × Expr)) (e : Expr) :
    substMany ρ (.cellNew e) = .cellNew (substMany ρ e) := by
  induction ρ generalizing e with | nil => rfl | cons p rest ih => exact ih _

theorem substMany_cellGet (ρ : List (Ident × Expr)) (e : Expr) :
    substMany ρ (.cellGet e) = .cellGet (substMany ρ e) := by
  induction ρ generalizing e with | nil => rfl | cons p rest ih => exact ih _

theorem substMany_cellSet (ρ : List (Ident × Expr)) (e1 e2 : Expr) :
    substMany ρ (.cellSet e1 e2) = .cellSet (substMany ρ e1) (substMany ρ e2) := by
  induction ρ generalizing e1 e2 with | nil => rfl | cons p rest ih => exact ih _ _

theorem substMany_getTag (ρ : List (Ident × Expr)) (e : Expr) :
    substMany ρ (.getTag e) = .getTag (substMany ρ e) := by
  induction ρ generalizing e with | nil => rfl | cons p rest ih => exact ih _

theorem substList_eq_map (x : Ident) (v : Expr) (es : List Expr) :
    substList x v es = es.map (subst x v) := by
  induction es with | nil => rfl | cons a rest ih => simp [substList, ih]

theorem substMany_block (ρ : List (Ident × Expr)) (es : List Expr) :
    substMany ρ (.block es) = .block (es.map (substMany ρ)) := by
  induction ρ generalizing es with
  | nil => simp [substMany]
  | cons p rest ih =>
    rcases p with ⟨x, w⟩
    simp only [substMany, subst, substList_eq_map]
    rw [ih, List.map_map]; rfl

theorem substMany_applyDir (ρ : List (Ident × Expr)) (name : Ident) (args : List Expr) :
    substMany ρ (.applyDir name args) = .applyDir name (args.map (substMany ρ)) := by
  induction ρ generalizing args with
  | nil => simp [substMany]
  | cons p rest ih =>
    rcases p with ⟨x, w⟩
    simp only [substMany, subst, substList_eq_map]
    rw [ih, List.map_map]; rfl

theorem substMany_let (ρ : List (Ident × Expr)) (x : Ident) (e1 e2 : Expr) :
    substMany ρ (.let_ x e1 e2) =
      .let_ x (substMany ρ e1) (substMany (assocRemove x ρ) e2) := by
  induction ρ generalizing e1 e2 with
  | nil => rfl
  | cons p rest ih =>
    rcases p with ⟨y, w⟩
    simp only [substMany, subst, assocRemove, List.filter]
    by_cases hxy : (x == y) = true
    · have hEq : x = y := eq_of_beq hxy
      subst hEq
      simp [assocRemove, ih]
    · have hyne : (y != x) = true := by
        simp only [bne_iff_ne]; intro h; subst h; simp at hxy
      simp [hxy, hyne, assocRemove, substMany, ih]

mutual
theorem subst_comm_closed {x y : Ident} {v w : Expr} (hne : x ≠ y)
    (hv : freeVars v = []) (hw : freeVars w = []) (e : Expr) :
    subst x v (subst y w e) = subst y w (subst x v e) := by
  cases e with
  | lit _ | loc _ | taskRef _ | syncRef _ _ | trap _ => rfl
  | var z =>
    simp only [subst]
    cases hzy : (z == y)
    · cases hzx : (z == x)
      · simp [subst, hzy, hzx]
      · simp only [subst, hzx, Bool.false_eq_true, ↓reduceIte]
        exact (subst_not_free (by simp [hv])).symm
    · have hzx : (z == x) = false := by
        have := eq_of_beq hzy; subst this; exact beq_false_of_ne (Ne.symm hne)
      simp only [subst, hzy, hzx, Bool.false_eq_true, ↓reduceIte]
      exact subst_not_free (by simp [hw])
  | tuple es => simp [subst, substList_comm_closed hne hv hw es]
  | block es => simp [subst, substList_comm_closed hne hv hw es]
  | lam m ps ret body =>
    simp only [subst]
    cases hmy : ps.any (fun p => p.1 == y) <;> cases hmx : ps.any (fun p => p.1 == x) <;>
      simp [subst, hmy, hmx, subst_comm_closed hne hv hw body]
  | apply fn args =>
    simp [subst, subst_comm_closed hne hv hw fn, substList_comm_closed hne hv hw args]
  | applyDir fn args =>
    simp [subst, substList_comm_closed hne hv hw args]
  | bin op e1 e2 =>
    simp [subst, subst_comm_closed hne hv hw e1, subst_comm_closed hne hv hw e2]
  | un op e1 => simp [subst, subst_comm_closed hne hv hw e1]
  | let_ z e1 e2 =>
    simp only [subst]
    cases hzy : (z == y) <;> cases hzx : (z == x) <;>
      simp [subst, hzy, hzx, subst_comm_closed hne hv hw e1, subst_comm_closed hne hv hw e2]
  | if_ c t e =>
    simp [subst, subst_comm_closed hne hv hw c, subst_comm_closed hne hv hw t,
      subst_comm_closed hne hv hw e]
  | while_ c b =>
    simp [subst, subst_comm_closed hne hv hw c, subst_comm_closed hne hv hw b]
  | match_ s arms =>
    simp [subst, subst_comm_closed hne hv hw s, substArms_comm_closed hne hv hw arms]
  | makeData adt tag es => simp [subst, substList_comm_closed hne hv hw es]
  | getTag e1 => simp [subst, subst_comm_closed hne hv hw e1]
  | cellNew e1 => simp [subst, subst_comm_closed hne hv hw e1]
  | cellGet e1 => simp [subst, subst_comm_closed hne hv hw e1]
  | cellSet e1 e2 =>
    simp [subst, subst_comm_closed hne hv hw e1, subst_comm_closed hne hv hw e2]
  | spawn e1 => simp [subst, subst_comm_closed hne hv hw e1]
  | await e1 => simp [subst, subst_comm_closed hne hv hw e1]
  | concPrim op args => simp [subst, substList_comm_closed hne hv hw args]
termination_by sizeOf e

theorem substList_comm_closed {x y : Ident} {v w : Expr} (hne : x ≠ y)
    (hv : freeVars v = []) (hw : freeVars w = []) (es : List Expr) :
    substList x v (substList y w es) = substList y w (substList x v es) := by
  cases es with
  | nil => rfl
  | cons a rest =>
    simp [substList, subst_comm_closed hne hv hw a, substList_comm_closed hne hv hw rest]
termination_by sizeOf es

theorem substArms_comm_closed {x y : Ident} {v w : Expr} (hne : x ≠ y)
    (hv : freeVars v = []) (hw : freeVars w = []) (arms : List (Pat × Expr)) :
    substArms x v (substArms y w arms) = substArms y w (substArms x v arms) := by
  match arms with
  | [] => rfl
  | (p, body) :: rest =>
    simp only [substArms, substArms_comm_closed hne hv hw rest]
    cases hmy : (patBoundNames p).contains y <;> cases hmx : (patBoundNames p).contains x <;>
      simp [hmy, hmx, subst_comm_closed hne hv hw body]
termination_by sizeOf arms
end

mutual
theorem subst_same_closed {x : Ident} {v w : Expr} (hv : freeVars v = []) (e : Expr) :
    subst x w (subst x v e) = subst x v e := by
  cases e with
  | lit _ | loc _ | taskRef _ | syncRef _ _ | trap _ => rfl
  | var z =>
    simp only [subst]
    cases hzx : (z == x)
    · simp [subst, hzx]
    · simp only [↓reduceIte]; exact subst_not_free (by simp [hv])
  | tuple es => simp [subst, substList_same_closed hv es]
  | block es => simp [subst, substList_same_closed hv es]
  | lam m ps ret body =>
    simp only [subst]
    cases hm : ps.any (fun p => p.1 == x) <;> simp [subst, hm, subst_same_closed hv body]
  | apply fn args => simp [subst, subst_same_closed hv fn, substList_same_closed hv args]
  | applyDir fn args => simp [subst, substList_same_closed hv args]
  | bin op e1 e2 => simp [subst, subst_same_closed hv e1, subst_same_closed hv e2]
  | un op e1 => simp [subst, subst_same_closed hv e1]
  | let_ z e1 e2 =>
    simp only [subst]
    cases hzx : (z == x) <;> simp [subst, hzx, subst_same_closed hv e1, subst_same_closed hv e2]
  | if_ c t e => simp [subst, subst_same_closed hv c, subst_same_closed hv t, subst_same_closed hv e]
  | while_ c b => simp [subst, subst_same_closed hv c, subst_same_closed hv b]
  | match_ s arms => simp [subst, subst_same_closed hv s, substArms_same_closed hv arms]
  | makeData adt tag es => simp [subst, substList_same_closed hv es]
  | getTag e1 => simp [subst, subst_same_closed hv e1]
  | cellNew e1 => simp [subst, subst_same_closed hv e1]
  | cellGet e1 => simp [subst, subst_same_closed hv e1]
  | cellSet e1 e2 => simp [subst, subst_same_closed hv e1, subst_same_closed hv e2]
  | spawn e1 => simp [subst, subst_same_closed hv e1]
  | await e1 => simp [subst, subst_same_closed hv e1]
  | concPrim op args => simp [subst, substList_same_closed hv args]
termination_by sizeOf e

theorem substList_same_closed {x : Ident} {v w : Expr} (hv : freeVars v = []) (es : List Expr) :
    substList x w (substList x v es) = substList x v es := by
  cases es with
  | nil => rfl
  | cons a rest => simp [substList, subst_same_closed hv a, substList_same_closed hv rest]
termination_by sizeOf es

theorem substArms_same_closed {x : Ident} {v w : Expr} (hv : freeVars v = [])
    (arms : List (Pat × Expr)) :
    substArms x w (substArms x v arms) = substArms x v arms := by
  match arms with
  | [] => rfl
  | (p, body) :: rest =>
    simp only [substArms, substArms_same_closed hv rest]
    cases hm : (patBoundNames p).contains x <;> simp [hm, subst_same_closed hv body]
termination_by sizeOf arms
end

theorem subst_substMany_remove {ρ : List (Ident × Expr)} (hρ : ClosedEnv ρ)
    {x : Ident} {v : Expr} (hv : freeVars v = []) (e : Expr) :
    subst x v (substMany (assocRemove x ρ) e) = substMany ((x, v) :: ρ) e := by
  induction ρ generalizing e with
  | nil => rfl
  | cons p rest ih =>
    rcases p with ⟨y, w⟩
    have hrest : ClosedEnv rest := fun q hq => hρ q (List.mem_cons_of_mem _ hq)
    have hw : freeVars w = [] := (hρ (y, w) (List.mem_cons_self ..)).2
    simp only [assocRemove, List.filter, substMany]
    cases hyx : (y != x)
    · have heq : y = x := by
        simp only [bne_eq_false_iff_eq] at hyx; exact hyx
      subst heq
      simp only [Bool.false_eq_true, ↓reduceIte]
      change subst y v (substMany (assocRemove y rest) e) = _
      rw [ih hrest e]
      simp only [substMany, subst_same_closed hv e]
    · have hne : x ≠ y := by
        simp only [bne_iff_ne] at hyx; exact Ne.symm hyx
      simp only [↓reduceIte, substMany]
      change subst x v (substMany (assocRemove x rest) (subst y w e)) = _
      rw [ih hrest (subst y w e)]
      simp only [substMany]
      rw [subst_comm_closed hne hv hw e]

/-! ## Part 3: Symbolic Values, Formulas, Valuation Models & Freshness -/

abbrev SymId := Nat

/-- Concrete valuation of symbolic variables to closed Core Geisha values. -/
abbrev Model := SymId → Expr

/-- A valid model maps every symbolic variable to a closed value. -/
def ValidModel (M : Model) : Prop :=
  ∀ id, IsValue (M id) ∧ freeVars (M id) = []

/-- Update a valuation model at a single symbolic variable `id`. -/
def updateModel (M : Model) (id : SymId) (v : Expr) : Model :=
  fun k => if k == id then v else M k

theorem validModel_update {M : Model} {id : SymId} {v : Expr}
    (hM : ValidModel M) (hv : IsValue v) (hclosed : freeVars v = []) :
    ValidModel (updateModel M id v) := by
  intro k
  simp only [updateModel]
  by_cases h : (k == id) = true
  · simp [h, hv, hclosed]
  · simp [h, hM k]

/-- Modeled literal predicate (matches `src/verify.gsa` S1/S3: rejects Float/Float32/Str). -/
def isModeledLit : Lit → Bool
  | .int _ => true
  | .int64 _ => true
  | .bool _ => true
  | .char _ => true
  | .unit => true
  | .floatBits _ => false
  | .float32Bits _ => false
  | .str _ => false

/-- Modeled unary operators (rejects Float/Float32 negation, matching S3). -/
def isModeledUnOp : UnOp → Bool
  | .not => true
  | .neg => true
  | .bitNot => true
  | .neg64 => true
  | .bitNot64 => true
  | .intToI64 => true
  | .i64ToInt => true
  | .negFloat => false
  | .negFloat32 => false

/-- Modeled strict binary operators (Int32, Int64, Bool, Char; rejects Float/Float32/Str). -/
def isModeledStrictBinOp : BinOp → Bool
  | .add | .sub | .mul | .div | .rem
  | .bitAnd | .bitOr | .bitXor | .shlInt | .shrInt | .ushrInt
  | .eqInt | .neInt | .ltInt | .leInt | .gtInt | .geInt
  | .add64 | .sub64 | .mul64 | .div64 | .rem64
  | .bitAnd64 | .bitOr64 | .bitXor64 | .shl64 | .shr64 | .ushr64
  | .eq64 | .ne64 | .lt64 | .le64 | .gt64 | .ge64
  | .eqBool | .neBool | .bitAndBool | .bitOrBool | .bitXorBool
  | .eqChar | .neChar | .ltChar | .leChar | .gtChar | .geChar => true
  | _ => false

/-- Division and remainder operators that trap with `Trap.divByZero` on zero divisor. -/
def isDivOp : BinOp → Bool
  | .div | .rem | .div64 | .rem64 => true
  | _ => false

/-- Symbolic value expressions generated by `vcgen`. -/
inductive SVal where
  | lit (l : Lit)
  | sym (id : SymId)
  | loc (l : Loc)
  | un (op : UnOp) (e : SVal)
  | bin (op : BinOp) (e1 e2 : SVal)
  | ite (c t e : SVal)
  | getTag (v : SVal)
  deriving Repr, BEq

/-- Symbolic verification formulas generated by `vcgen`. -/
inductive SForm where
  | tt
  | ff
  | isTrue (v : SVal)
  | isFalse (v : SVal)
  | neZero (op : BinOp) (v : SVal)
  | hasTy (v : SVal) (ty : Ty)
  | not (p : SForm)
  | and (p q : SForm)
  | imp (p q : SForm)
  deriving Repr, BEq

/-- Evaluate a symbolic value under model `M` and symbolic-to-physical location map `L`
    using the EXACT `CoreGeisha.evalUnOp` and `CoreGeisha.evalBinOp` from `Semantics.lean`.
    Note: `L` defaults to `id`; scalar results (`.lit c`) are provably independent of `L`
    (`evalSVal_lit_iff_id`). -/
def evalSVal (M : Model) (L : Loc → Loc := id) : SVal → Option Expr
  | .lit l => some (.lit l)
  | .sym id => some (M id)
  | .loc k => some (.loc (L k))
  | .un op e =>
    match evalSVal M L e with
    | some (.lit l) =>
      match evalUnOp op l with
      | some l' => some (.lit l')
      | none => none
    | _ => none
  | .bin op e1 e2 =>
    match evalSVal M L e1, evalSVal M L e2 with
    | some (.lit l1), some (.lit l2) =>
      match evalBinOp op l1 l2 with
      | some (.val l') => some (.lit l')
      | _ => none
    | _, _ => none
  | .ite c t e =>
    match evalSVal M L c with
    | some (.lit (.bool true)) => evalSVal M L t
    | some (.lit (.bool false)) => evalSVal M L e
    | _ => none
  | .getTag v =>
    match evalSVal M L v with
    | some (.makeData _ tag _) => some (.lit (.int (Int32.ofNat tag)))
    | _ => none

/-- Evaluating `SVal` to a literal or ADT value is independent of the location map `L`. -/
private theorem evalSVal_nonloc_iff_id {M : Model} {L : Loc → Loc} (sv : SVal) :
    (∀ c, evalSVal M L sv = some (.lit c) ↔ evalSVal M id sv = some (.lit c)) ∧
    (∀ tn tag fs, evalSVal M L sv = some (.makeData tn tag fs) ↔ evalSVal M id sv = some (.makeData tn tag fs)) := by
  induction sv with
  | lit _ | sym _ =>
    exact ⟨fun _ => Iff.rfl, fun _ _ _ => Iff.rfl⟩
  | loc _ =>
    exact ⟨fun _ => by simp [evalSVal], fun _ _ _ => by simp [evalSVal]⟩
  | un op e ih =>
    constructor
    · intro c; simp only [evalSVal]
      constructor
      · intro h
        cases h1 : evalSVal M L e with
        | none => simp [h1] at h
        | some v1 =>
          rw [h1] at h; cases v1 with
          | lit l1 => rw [(ih.1 l1).mp h1]; exact h
          | _ => simp at h
      · intro h
        cases h1 : evalSVal M id e with
        | none => simp [h1] at h
        | some v1 =>
          rw [h1] at h; cases v1 with
          | lit l1 => rw [(ih.1 l1).mpr h1]; exact h
          | _ => simp at h
    · intro tn tag fs; simp only [evalSVal]
      constructor
      · intro h; cases h1 : evalSVal M L e with
        | none => simp [h1] at h
        | some v1 => rw [h1] at h; cases v1 with | lit l1 => cases h2 : evalUnOp op l1 <;> simp [h2] at h | _ => simp at h
      · intro h; cases h1 : evalSVal M id e with
        | none => simp [h1] at h
        | some v1 => rw [h1] at h; cases v1 with | lit l1 => cases h2 : evalUnOp op l1 <;> simp [h2] at h | _ => simp at h
  | bin op e1 e2 ih1 ih2 =>
    constructor
    · intro c; simp only [evalSVal]
      constructor
      · intro h
        cases h1 : evalSVal M L e1 with
        | none => simp [h1] at h
        | some v1 =>
          cases h2 : evalSVal M L e2 with
          | none => simp [h1, h2] at h
          | some v2 =>
            rw [h1, h2] at h; cases v1 with
            | lit l1 =>
              cases v2 with
              | lit l2 => rw [(ih1.1 l1).mp h1, (ih2.1 l2).mp h2]; exact h
              | _ => simp at h
            | _ => simp at h
      · intro h
        cases h1 : evalSVal M id e1 with
        | none => simp [h1] at h
        | some v1 =>
          cases h2 : evalSVal M id e2 with
          | none => simp [h1, h2] at h
          | some v2 =>
            rw [h1, h2] at h; cases v1 with
            | lit l1 =>
              cases v2 with
              | lit l2 => rw [(ih1.1 l1).mpr h1, (ih2.1 l2).mpr h2]; exact h
              | _ => simp at h
            | _ => simp at h
    · intro tn tag fs; simp only [evalSVal]
      constructor
      · intro h
        cases h1 : evalSVal M L e1 with
        | none => simp [h1] at h
        | some v1 =>
          cases h2 : evalSVal M L e2 with
          | none => simp [h1, h2] at h
          | some v2 =>
            rw [h1, h2] at h
            cases v1 with
            | lit l1 =>
              cases v2 with
              | lit l2 => cases h3 : evalBinOp op l1 l2 <;> simp [h3] at h; rename_i r; cases r <;> simp at h
              | _ => simp at h
            | _ => simp at h
      · intro h
        cases h1 : evalSVal M id e1 with
        | none => simp [h1] at h
        | some v1 =>
          cases h2 : evalSVal M id e2 with
          | none => simp [h1, h2] at h
          | some v2 =>
            rw [h1, h2] at h
            cases v1 with
            | lit l1 =>
              cases v2 with
              | lit l2 => cases h3 : evalBinOp op l1 l2 <;> simp [h3] at h; rename_i r; cases r <;> simp at h
              | _ => simp at h
            | _ => simp at h
  | ite cond t e ihc iht ihe =>
    constructor
    · intro c; simp only [evalSVal]
      constructor
      · intro h
        cases hc : evalSVal M L cond with
        | none => simp [hc] at h
        | some vc =>
          rw [hc] at h; cases vc with
          | lit lc =>
            cases lc with
            | bool b =>
              rw [(ihc.1 (.bool b)).mp hc]; cases b
              · exact (ihe.1 c).mp h
              · exact (iht.1 c).mp h
            | _ => simp at h
          | _ => simp at h
      · intro h
        cases hc : evalSVal M id cond with
        | none => simp [hc] at h
        | some vc =>
          rw [hc] at h; cases vc with
          | lit lc =>
            cases lc with
            | bool b =>
              rw [(ihc.1 (.bool b)).mpr hc]; cases b
              · exact (ihe.1 c).mpr h
              · exact (iht.1 c).mpr h
            | _ => simp at h
          | _ => simp at h
    · intro tn tag fs; simp only [evalSVal]
      constructor
      · intro h
        cases hc : evalSVal M L cond with
        | none => simp [hc] at h
        | some vc =>
          rw [hc] at h; cases vc with
          | lit lc =>
            cases lc with
            | bool b =>
              rw [(ihc.1 (.bool b)).mp hc]; cases b
              · exact (ihe.2 tn tag fs).mp h
              · exact (iht.2 tn tag fs).mp h
            | _ => simp at h
          | _ => simp at h
      · intro h
        cases hc : evalSVal M id cond with
        | none => simp [hc] at h
        | some vc =>
          rw [hc] at h; cases vc with
          | lit lc =>
            cases lc with
            | bool b =>
              rw [(ihc.1 (.bool b)).mpr hc]; cases b
              · exact (ihe.2 tn tag fs).mpr h
              · exact (iht.2 tn tag fs).mpr h
            | _ => simp at h
          | _ => simp at h
  | getTag v ih =>
    constructor
    · intro c; simp only [evalSVal]
      constructor
      · intro h
        cases h1 : evalSVal M L v with
        | none => simp [h1] at h
        | some v1 =>
          rw [h1] at h; cases v1 with
          | makeData tn tag fs => rw [(ih.2 tn tag fs).mp h1]; exact h
          | _ => simp at h
      · intro h
        cases h1 : evalSVal M id v with
        | none => simp [h1] at h
        | some v1 =>
          rw [h1] at h; cases v1 with
          | makeData tn tag fs => rw [(ih.2 tn tag fs).mpr h1]; exact h
          | _ => simp at h
    · intro tn tag fs; simp only [evalSVal]
      constructor
      · intro h; cases h1 : evalSVal M L v with | none => simp [h1] at h | some v1 => rw [h1] at h; cases v1 <;> simp at h
      · intro h; cases h1 : evalSVal M id v with | none => simp [h1] at h | some v1 => rw [h1] at h; cases v1 <;> simp at h

theorem evalSVal_lit_iff_id {M : Model} {L : Loc → Loc} {sv : SVal} {c : Lit} :
    evalSVal M L sv = some (.lit c) ↔ evalSVal M id sv = some (.lit c) :=
  (evalSVal_nonloc_iff_id sv).1 c

theorem evalSVal_closed {M : Model} {L : Loc → Loc} (hM : ValidModel M) {sv : SVal} {v : Expr}
    (h : evalSVal M L sv = some v) : IsValue v ∧ freeVars v = [] := by
  induction sv generalizing v with
  | lit l => simp [evalSVal] at h; subst h; exact ⟨.lit l, rfl⟩
  | sym id => simp [evalSVal] at h; subst h; exact hM id
  | loc l => simp [evalSVal] at h; subst h; exact ⟨.loc (L l), rfl⟩
  | un op e _ =>
    simp only [evalSVal] at h
    cases h1 : evalSVal M L e with
    | none => simp [h1] at h
    | some v1 =>
      rw [h1] at h; cases v1 <;> simp at h
      rename_i l
      cases h2 : evalUnOp op l with
      | none => simp [h2] at h
      | some l' => simp [h2] at h; subst h; exact ⟨.lit l', rfl⟩
  | bin op e1 e2 _ _ =>
    simp only [evalSVal] at h
    cases h1 : evalSVal M L e1 with
    | none => simp [h1] at h
    | some v1 =>
      cases h2 : evalSVal M L e2 with
      | none => simp [h1, h2] at h
      | some v2 =>
        rw [h1, h2] at h; cases v1 <;> cases v2 <;> simp at h
        rename_i l1 l2
        cases h3 : evalBinOp op l1 l2 with
        | none => simp [h3] at h
        | some r =>
          cases r with
          | val l' => simp [h3] at h; subst h; exact ⟨.lit l', rfl⟩
          | trap _ => simp [h3] at h
  | ite c t e _ iht ihe =>
    simp only [evalSVal] at h
    cases hc : evalSVal M L c with
    | none => simp [hc] at h
    | some vc =>
      rw [hc] at h
      cases vc with
      | lit lc =>
        cases lc with
        | bool b =>
          cases b
          · exact ihe (by simpa using h)
          · exact iht (by simpa using h)
        | _ => simp at h
      | _ => simp at h
  | getTag e _ =>
    simp only [evalSVal] at h
    cases h1 : evalSVal M L e with
    | none => simp [h1] at h
    | some v1 =>
      rw [h1] at h; cases v1 <;> simp at h
      subst h; exact ⟨.lit _, rfl⟩

/-- Evaluate a symbolic formula under model `M`. -/
def evalSForm (M : Model) : SForm → Prop
  | .tt => True
  | .ff => False
  | .isTrue v => evalSVal M id v = some (.lit (.bool true))
  | .isFalse v => evalSVal M id v = some (.lit (.bool false))
  | .neZero op v =>
    match op with
    | .div | .rem => ∃ n : Int32, evalSVal M id v = some (.lit (.int n)) ∧ n ≠ 0
    | .div64 | .rem64 => ∃ n : Int64, evalSVal M id v = some (.lit (.int64 n)) ∧ n ≠ 0
    | _ => True
  | .hasTy v ty => ∃ val, evalSVal M id v = some val ∧ valHasTy val ty
  | .not p => ¬ evalSForm M p
  | .and p q => evalSForm M p ∧ evalSForm M q
  | .imp p q => evalSForm M p → evalSForm M q

/-- A verification obligation is valid iff it holds under every valid model `M`. -/
def ValidForm (f : SForm) : Prop :=
  ∀ M, ValidModel M → evalSForm M f

/-- All verification obligations in a list are valid. -/
def ValidObs (obs : List SForm) : Prop :=
  ∀ f ∈ obs, ValidForm f

/-- Upper bound on symbolic variable IDs occurring in `SVal`. -/
def svalBound (n : Nat) : SVal → Prop
  | .lit _ => True
  | .sym id => id < n
  | .loc _ => True
  | .un _ e => svalBound n e
  | .bin _ e1 e2 => svalBound n e1 ∧ svalBound n e2
  | .ite c t e => svalBound n c ∧ svalBound n t ∧ svalBound n e
  | .getTag v => svalBound n v

/-- Upper bound on symbolic variable IDs occurring in `SForm`. -/
def sformBound (n : Nat) : SForm → Prop
  | .tt | .ff => True
  | .isTrue v | .isFalse v | .neZero _ v | .hasTy v _ => svalBound n v
  | .not p => sformBound n p
  | .and p q | .imp p q => sformBound n p ∧ sformBound n q

theorem svalBound_mono {n m : Nat} (hle : n ≤ m) {sv : SVal} (h : svalBound n sv) :
    svalBound m sv := by
  induction sv with
  | lit _ | loc _ => trivial
  | sym id => exact Nat.lt_of_lt_of_le h hle
  | un _ _ ih => exact ih h
  | bin _ _ _ ih1 ih2 => exact ⟨ih1 h.1, ih2 h.2⟩
  | ite _ _ _ ih1 ih2 ih3 => exact ⟨ih1 h.1, ih2 h.2.1, ih3 h.2.2⟩
  | getTag _ ih => exact ih h

theorem sformBound_mono {n m : Nat} (hle : n ≤ m) {f : SForm} (h : sformBound n f) :
    sformBound m f := by
  induction f with
  | tt | ff => trivial
  | isTrue _ | isFalse _ | neZero _ _ | hasTy _ _ => exact svalBound_mono hle h
  | not _ ih => exact ih h
  | and _ _ ih1 ih2 => exact ⟨ih1 h.1, ih2 h.2⟩
  | imp _ _ ih1 ih2 => exact ⟨ih1 h.1, ih2 h.2⟩

theorem evalSVal_updateModel_ge {M : Model} {L : Loc → Loc} {n id : Nat} {v : Expr} {sv : SVal}
    (hb : svalBound n sv) (hge : n ≤ id) :
    evalSVal (updateModel M id v) L sv = evalSVal M L sv := by
  induction sv with
  | lit _ | loc _ => rfl
  | sym k =>
    have hlt : k < id := Nat.lt_of_lt_of_le hb hge
    have hne : (k == id) = false := beq_false_of_ne (Nat.ne_of_lt hlt)
    simp [evalSVal, updateModel, hne]
  | un op e ih => simp [evalSVal, ih hb]
  | bin op e1 e2 ih1 ih2 => simp [evalSVal, ih1 hb.1, ih2 hb.2]
  | ite c t e ihc iht ihe => simp [evalSVal, ihc hb.1, iht hb.2.1, ihe hb.2.2]
  | getTag e ih => simp [evalSVal, ih hb]

theorem evalSForm_updateModel_ge {M : Model} {n id : Nat} {v : Expr} {f : SForm}
    (hb : sformBound n f) (hge : n ≤ id) :
    evalSForm (updateModel M id v) f ↔ evalSForm M f := by
  induction f with
  | tt | ff => exact Iff.rfl
  | isTrue sv | isFalse sv => simp [evalSForm, evalSVal_updateModel_ge hb hge]
  | neZero op sv => cases op <;> simp [evalSForm, evalSVal_updateModel_ge hb hge]
  | hasTy sv ty => simp [evalSForm, evalSVal_updateModel_ge hb hge]
  | not p ih => simp [evalSForm, ih hb]
  | and p q ih1 ih2 => simp [evalSForm, ih1 hb.1, ih2 hb.2]
  | imp p q ih1 ih2 => simp [evalSForm, ih1 hb.1, ih2 hb.2]

/-- Evaluating a strict `BinOp` on two literals never traps with `divByZero`
    when `isDivOp op = false` or `evalSForm M (.neZero op sv2)` holds. -/
theorem evalBinOp_no_divByZero {op : BinOp} {l1 l2 : Lit} {M : Model} {sv2 : SVal}
    (h2 : evalSVal M id sv2 = some (.lit l2))
    (hguard : isDivOp op = true → evalSForm M (.neZero op sv2))
    (htrap : evalBinOp op l1 l2 = some (.trap .divByZero)) : False := by
  unfold evalBinOp at htrap
  split at htrap <;> simp at htrap
  · rcases hguard rfl with ⟨n, hn, hne⟩
    rw [h2] at hn; cases hn; exact hne htrap
  · rcases hguard rfl with ⟨n, hn, hne⟩
    rw [h2] at hn; cases hn; exact hne htrap
  · rcases hguard rfl with ⟨n, hn, hne⟩
    rw [h2] at hn; cases hn; exact hne htrap
  · rcases hguard rfl with ⟨n, hn, hne⟩
    rw [h2] at hn; cases hn; exact hne htrap

/-! ## Part 4: Symbolic State, Contracts, and Executable Fail-Closed `vcgen` -/

/-- Symbolic execution state mirroring `SymState` in `src/verify.gsa`. -/
structure SymState where
  nextSym : Nat := 0
  nextLoc : Nat := 0
  vars    : List (Ident × SVal) := []
  cells   : List (Loc × SVal) := []
  cellTys : List (Loc × Ty) := []
  path    : SForm := .tt
  obs     : List SForm := []
  deriving Repr

/-- Function contract specification (`requires` / `ensures` / optional `decreases`). -/
structure FnContract where
  params : List (Ident × Ty)
  req    : Expr
  ens    : Expr
  retVar : Ident := "__res"
  retTy  : Ty := .int
  dec    : Option Expr := none
  deriving Repr

/-- Loop contract specification (`invariant` + optional `decreases`). -/
structure LoopContract where
  inv : Expr
  dec : Option Expr := none
  deriving Repr

/-- Verification environment providing callee contracts, loop invariants, and SCC decreases context. -/
structure VcgEnv where
  contracts : Ident → Option FnContract := fun _ => none
  loops     : Expr → Expr → Option LoopContract := fun _ _ => none
  curFn     : Ident := ""
  curDec    : Option (Ty × SVal) := none
  isSameScc : Ident → Ident → Bool := fun a b => a == b

/-- Check that a list of heap locations contains no duplicates (pairwise non-aliasing). -/
def noDupLocs : List Loc → Bool
  | [] => true
  | l :: ls => !(ls.contains l) && noDupLocs ls

/-- Extract all `.loc l` handles from symbolic arguments. -/
def collectLocArgs : List SVal → List Loc
  | [] => []
  | .loc l :: rest => l :: collectLocArgs rest
  | _ :: rest => collectLocArgs rest

/-- Extract all `.loc l` handles from concrete runtime value arguments. -/
def collectConcreteLocs : List Expr → List Loc
  | [] => []
  | .loc l :: rest => l :: collectConcreteLocs rest
  | _ :: rest => collectConcreteLocs rest

/-- Emit a verification obligation guarded by the current path condition. -/
def emitOb (st : SymState) (goal : SForm) : SymState :=
  { st with obs := .imp st.path goal :: st.obs }

/-- Add a path assumption. -/
def withPath (st : SymState) (cond : SForm) : SymState :=
  { st with path := .and st.path cond }

@[simp] theorem emitOb_nextSym (st : SymState) (g : SForm) : (emitOb st g).nextSym = st.nextSym := rfl
@[simp] theorem emitOb_nextLoc (st : SymState) (g : SForm) : (emitOb st g).nextLoc = st.nextLoc := rfl
@[simp] theorem emitOb_vars (st : SymState) (g : SForm) : (emitOb st g).vars = st.vars := rfl
@[simp] theorem emitOb_cells (st : SymState) (g : SForm) : (emitOb st g).cells = st.cells := rfl
@[simp] theorem emitOb_cellTys (st : SymState) (g : SForm) : (emitOb st g).cellTys = st.cellTys := rfl
@[simp] theorem emitOb_path (st : SymState) (g : SForm) : (emitOb st g).path = st.path := rfl
@[simp] theorem emitOb_obs (st : SymState) (g : SForm) : (emitOb st g).obs = .imp st.path g :: st.obs := rfl
@[simp] theorem withPath_nextSym (st : SymState) (c : SForm) : (withPath st c).nextSym = st.nextSym := rfl
@[simp] theorem withPath_nextLoc (st : SymState) (c : SForm) : (withPath st c).nextLoc = st.nextLoc := rfl
@[simp] theorem withPath_vars (st : SymState) (c : SForm) : (withPath st c).vars = st.vars := rfl
@[simp] theorem withPath_cells (st : SymState) (c : SForm) : (withPath st c).cells = st.cells := rfl
@[simp] theorem withPath_cellTys (st : SymState) (c : SForm) : (withPath st c).cellTys = st.cellTys := rfl
@[simp] theorem withPath_path (st : SymState) (c : SForm) : (withPath st c).path = .and st.path c := rfl
@[simp] theorem withPath_obs (st : SymState) (c : SForm) : (withPath st c).obs = st.obs := rfl

/-- Merge symbolic cell maps from two branches guarded by boolean `svc`. -/
def mergeCells (svc : SVal) (baseCells cellsT cellsE : List (Loc × SVal)) :
    List (Loc × SVal) :=
  baseCells.map fun (l, svBase) =>
    let svT := (locLookup cellsT l).getD svBase
    let svE := (locLookup cellsE l).getD svBase
    (l, .ite svc svT svE)

/-- Havoc all tracked locations in `locs` by assigning fresh symbolic variables,
    and conjoining `.hasTy (.sym id) ty` into `path` for typed cells. -/
def havocCells (st : SymState) (locs : List Loc) : SymState :=
  locs.foldl (fun s l =>
    let id := s.nextSym
    let p' := match locLookup s.cellTys l with
      | some ty => .and s.path (.hasTy (.sym id) ty)
      | none => s.path
    { s with nextSym := id + 1, cells := (l, .sym id) :: s.cells, path := p' }) st

/-- Decidable equality on modeled scalar types (avoids needing `LawfulBEq Ty`). -/
def scalarTyEq : Ty → Ty → Bool
  | .int, .int => true
  | .int64, .int64 => true
  | .bool, .bool => true
  | .char, .char => true
  | .void, .void => true
  | _, _ => false

theorem scalarTyEq_true {t1 t2 : Ty} (h : scalarTyEq t1 t2 = true) : t1 = t2 := by
  cases t1 <;> cases t2 <;> simp [scalarTyEq] at h <;> rfl

/-- Collect `(symId, ty)` pairs from `.hasTy (.sym id) ty` atoms in a formula. -/
def collectSymTys : SForm → List (SymId × Ty)
  | .hasTy (.sym id) ty => [(id, ty)]
  | .not p => collectSymTys p
  | .and p q | .imp p q => collectSymTys p ++ collectSymTys q
  | _ => []

/-- Infer the modeled scalar type of a symbolic value `SVal` using `st.path` type facts.
    Fail-closed (`none`) on `.loc`, unmodeled literals/ops, or untyped symbols. -/
def inferSValTy (st : SymState) : SVal → Option Ty
  | .lit (.int _) => some .int
  | .lit (.int64 _) => some .int64
  | .lit (.bool _) => some .bool
  | .lit (.char _) => some .char
  | .lit .unit => some .void
  | .lit _ => none
  | .sym id =>
    match (collectSymTys st.path).find? (·.1 == id) with
    | some (_, ty) => if isModeledScalarTy ty then some ty else none
    | none => none
  | .loc _ => none
  | .un op e =>
    match inferSValTy st e with
    | none => none
    | some _ =>
      match op with
      | .not => some .bool
      | .neg | .bitNot | .i64ToInt => some .int
      | .neg64 | .bitNot64 | .intToI64 => some .int64
      | _ => none
  | .bin op e1 e2 =>
    match inferSValTy st e1, inferSValTy st e2 with
    | some _, some _ =>
      match op with
      | .add | .sub | .mul | .div | .rem
      | .bitAnd | .bitOr | .bitXor | .shlInt | .shrInt | .ushrInt => some .int
      | .add64 | .sub64 | .mul64 | .div64 | .rem64
      | .bitAnd64 | .bitOr64 | .bitXor64 | .shl64 | .shr64 | .ushr64 => some .int64
      | .eqInt | .neInt | .ltInt | .leInt | .gtInt | .geInt
      | .eq64 | .ne64 | .lt64 | .le64 | .gt64 | .ge64
      | .eqBool | .neBool | .and | .or | .bitAndBool | .bitOrBool | .bitXorBool
      | .eqChar | .neChar | .ltChar | .leChar | .gtChar | .geChar => some .bool
      | _ => none
    | _, _ => none
  | .ite c t e =>
    match inferSValTy st c, inferSValTy st t, inferSValTy st e with
    | some .bool, some t1, some t2 => if scalarTyEq t1 t2 then some t1 else none
    | _, _, _ => none
  | .getTag e =>
    match inferSValTy st e with
    | some _ => some .int
    | none => none

/-- Comparison operators and zero literal for `decreases` measures (`.int` and `.int64`). -/
def decOpsForTy : Ty → Option (BinOp × BinOp × SVal)
  | .int => some (.geInt, .ltInt, .lit (.int 0))
  | .int64 => some (.ge64, .lt64, .lit (.int64 0))
  | _ => none

theorem valHasTy_lit_of_modeled {v : Expr} {ty : Ty}
    (hm : isModeledScalarTy ty = true) (hvt : valHasTy v ty) :
    ∃ l, v = .lit l := by
  cases ty with
  | int => rcases hvt with ⟨n, rfl⟩; exact ⟨.int n, rfl⟩
  | int64 => rcases hvt with ⟨n, rfl⟩; exact ⟨.int64 n, rfl⟩
  | bool => rcases hvt with ⟨b, rfl⟩; exact ⟨.bool b, rfl⟩
  | char => rcases hvt with ⟨c, rfl, _⟩; exact ⟨.char c, rfl⟩
  | void => exact ⟨.unit, hvt⟩
  | _ => simp [isModeledScalarTy] at hm

/-- Check argument-to-parameter type compatibility for modular calls:
    - `Cell elemTy` parameters must receive `.loc l` (no symbolic/scalar confusion);
    - Modeled scalar parameters emit `.hasTy sv ty` so `evalSVal` is guaranteed non-loc and well-typed. -/
def checkCallArgTys (st : SymState) : List (Ident × Ty) → List SVal → Option SymState
  | [], [] => some st
  | (_, .cell elemTy) :: ps, (.loc l) :: svs =>
    match locLookup st.cellTys l with
    | some ty => if scalarTyEq ty elemTy then checkCallArgTys st ps svs else none
    | none => checkCallArgTys st ps svs
  | (_, ty) :: ps, sv :: svs =>
    if isModeledScalarTy ty then
      checkCallArgTys (emitOb st (.hasTy sv ty)) ps svs
    else none
  | _, _ => none

/-- All tracked cell locations in `st`. -/
def trackedLocs (st : SymState) : List Loc :=
  st.cells.map Prod.fst

/-- Pure expression VCG for contract expressions (`requires`, `ensures`, `invariant`, `decreases`).
    Never mutates `nextSym`, `nextLoc`, `vars`, `cells`, or `path`; only emits `divByZero` VCs.
    Fail-closed: rejects unmodeled literals/ops, mutation, loops, and function calls. -/
def vcgenPure (st : SymState) (e : Expr) : Option (SymState × SVal) :=
  match e with
  | .lit l =>
    if isModeledLit l then some (st, .lit l) else none
  | .var x =>
    match assocLookup st.vars x with
    | some sv => some (st, sv)
    | none => none
  | .loc _ => none
  | .un op e1 =>
    if !isModeledUnOp op then none
    else
      match vcgenPure st e1 with
      | some (st1, sv1) => some (st1, .un op sv1)
      | none => none
  | .bin op e1 e2 =>
    if op = .and then
      match vcgenPure st e1 with
      | none => none
      | some (st1, sv1) =>
        match vcgenPure (withPath st1 (.isTrue sv1)) e2 with
        | none => none
        | some (st2, sv2) =>
          some ({ st1 with obs := st2.obs }, .ite sv1 sv2 (.lit (.bool false)))
    else if op = .or then
      match vcgenPure st e1 with
      | none => none
      | some (st1, sv1) =>
        match vcgenPure (withPath st1 (.isFalse sv1)) e2 with
        | none => none
        | some (st2, sv2) =>
          some ({ st1 with obs := st2.obs }, .ite sv1 (.lit (.bool true)) sv2)
    else if !isModeledStrictBinOp op then none
    else
      match vcgenPure st e1 with
      | none => none
      | some (st1, sv1) =>
        match vcgenPure st1 e2 with
        | none => none
        | some (st2, sv2) =>
          let st3 := if isDivOp op then emitOb st2 (.neZero op sv2) else st2
          some (st3, .bin op sv1 sv2)
  | .if_ c t e =>
    match vcgenPure st c with
    | none => none
    | some (st1, svc) =>
      match vcgenPure (withPath st1 (.isTrue svc)) t with
      | none => none
      | some (stT, svT) =>
        match vcgenPure { st1 with path := .and st1.path (.isFalse svc), obs := stT.obs } e with
        | none => none
        | some (stE, svE) =>
          some ({ st1 with obs := stE.obs }, .ite svc svT svE)
  | .cellGet e1 =>
    match vcgenPure st e1 with
    | none => none
    | some (st1, .loc l) =>
      match locLookup st1.cells l with
      | some sv => some (st1, sv)
      | none => none
    | some _ => none
  | .getTag e1 =>
    match vcgenPure st e1 with
    | none => none
    | some (st1, sv1) => some (st1, .getTag sv1)
  | _ => none
termination_by sizeOf e

/-- Emit pre-iteration loop `decreases >= 0` obligation (supports `.int` and `.int64`). -/
def checkLoopPreDec (stBodyIn0 : SymState) (decOpt : Option Expr) :
    Option (SymState × Option (Ty × SVal)) :=
  match decOpt with
  | none => some (stBodyIn0, none)
  | some decE =>
    match vcgenPure stBodyIn0 decE with
    | none => none
    | some (stD0, svD0) =>
      match inferSValTy stD0 svD0 with
      | none => none
      | some decTy =>
        match decOpsForTy decTy with
        | none => none
        | some (geOp, _, zeroLit) =>
          some (emitOb stD0 (.isTrue (.bin geOp svD0 zeroLit)), some (decTy, svD0))

/-- Emit post-iteration loop `decreases' < decreases` obligation. -/
def checkLoopPostDec (stB : SymState) (decOpt : Option Expr) (svD0Opt : Option (Ty × SVal)) :
    Option SymState :=
  match decOpt, svD0Opt with
  | some decE, some (decTy, svD0) =>
    match vcgenPure stB decE with
    | none => none
    | some (stD1, svD1) =>
      match inferSValTy stD1 svD1, decOpsForTy decTy with
      | some decTy1, some (_, ltOp, _) =>
        if scalarTyEq decTy1 decTy then
          some (emitOb stD1 (.isTrue (.bin ltOp svD1 svD0)))
        else none
      | _, _ => none
  | _, _ => some stB

/-- Emit self- or mutual-recursive SCC call-edge `decreases` obligation (fail-closed if callee lacks `decreases`). -/
def checkCallDecreases (env : VcgEnv) (calleeName : Ident) (fc : FnContract)
    (stChecked0 : SymState) : Option SymState :=
  match env.curDec with
  | some (curTy, curSv) =>
    if env.isSameScc env.curFn calleeName then
      match fc.dec with
      | none => none
      | some calleeDecE =>
        match vcgenPure stChecked0 calleeDecE with
        | none => none
        | some (stDec, nextSv) =>
          match inferSValTy stDec nextSv, decOpsForTy curTy with
          | some nextTy, some (geOp, ltOp, zeroLit) =>
            if scalarTyEq nextTy curTy then
              some (emitOb stDec (.isTrue (.bin .and (.bin geOp curSv zeroLit) (.bin ltOp nextSv curSv))))
            else none
          | _, _ => none
    else some stChecked0
  | none => some stChecked0

mutual
/-- Executable, fail-closed Verification Condition Generator mirroring `src/verify.gsa`.
    Returns `none` on any unmodeled construct (Floats, Strings, closures, concurrency,
    unannotated loops, aliased mutable call arguments, out-of-scope vars/cells). -/
def vcgen (env : VcgEnv) (st : SymState) (e : Expr) : Option (SymState × SVal) :=
  match e with
  | .lit l =>
    if isModeledLit l then some (st, .lit l) else none
  | .var x =>
    match assocLookup st.vars x with
    | some sv => some (st, sv)
    | none => none
  | .loc _ => none
  | .un op e1 =>
    if !isModeledUnOp op then none
    else
      match vcgen env st e1 with
      | some (st1, sv1) => some (st1, .un op sv1)
      | none => none
  | .bin op e1 e2 =>
    if op = .and then
      -- Short-circuit `&&` (S2): right-hand side only evaluated when `e1` is `true`
      match vcgen env st e1 with
      | none => none
      | some (st1, sv1) =>
        match vcgen env (withPath st1 (.isTrue sv1)) e2 with
        | none => none
        | some (st2, sv2) =>
          if st2.nextLoc != st1.nextLoc then none
          else
            let mergedCells := mergeCells sv1 st1.cells st2.cells st1.cells
            some ({ nextSym := st2.nextSym, nextLoc := st1.nextLoc,
                    vars := st1.vars, cells := mergedCells, cellTys := st1.cellTys,
                    path := st1.path, obs := st2.obs },
                  .ite sv1 sv2 (.lit (.bool false)))
    else if op = .or then
      -- Short-circuit `||` (S2): right-hand side only evaluated when `e1` is `false`
      match vcgen env st e1 with
      | none => none
      | some (st1, sv1) =>
        match vcgen env (withPath st1 (.isFalse sv1)) e2 with
        | none => none
        | some (st2, sv2) =>
          if st2.nextLoc != st1.nextLoc then none
          else
            let mergedCells := mergeCells sv1 st1.cells st1.cells st2.cells
            some ({ nextSym := st2.nextSym, nextLoc := st1.nextLoc,
                    vars := st1.vars, cells := mergedCells, cellTys := st1.cellTys,
                    path := st1.path, obs := st2.obs },
                  .ite sv1 (.lit (.bool true)) sv2)
    else if !isModeledStrictBinOp op then none
    else
      match vcgen env st e1 with
      | none => none
      | some (st1, sv1) =>
        match vcgen env st1 e2 with
        | none => none
        | some (st2, sv2) =>
          let st3 := if isDivOp op then emitOb st2 (.neZero op sv2) else st2
          some (st3, .bin op sv1 sv2)
  | .let_ x e1 e2 =>
    match vcgen env st e1 with
    | none => none
    | some (st1, sv1) =>
      match vcgen env { st1 with vars := (x, sv1) :: st1.vars } e2 with
      | none => none
      | some (st2, sv2) => some ({ st2 with vars := st1.vars }, sv2)
  | .block es => vcgenBlock env st es
  | .if_ c t e =>
    match vcgen env st c with
    | none => none
    | some (st1, svc) =>
      match vcgen env (withPath st1 (.isTrue svc)) t with
      | none => none
      | some (stT, svT) =>
        let stEIn : SymState :=
          { nextSym := stT.nextSym, nextLoc := st1.nextLoc,
            vars := st1.vars, cells := st1.cells, cellTys := st1.cellTys,
            path := .and st1.path (.isFalse svc), obs := stT.obs }
        match vcgen env stEIn e with
        | none => none
        | some (stE, svE) =>
          if stT.nextLoc != st1.nextLoc || stE.nextLoc != st1.nextLoc then none
          else
            let mergedCells := mergeCells svc st1.cells stT.cells stE.cells
            some ({ nextSym := stE.nextSym, nextLoc := st1.nextLoc,
                    vars := st1.vars, cells := mergedCells, cellTys := st1.cellTys,
                    path := st1.path, obs := stE.obs },
                  .ite svc svT svE)
  | .cellNew e1 =>
    match vcgen env st e1 with
    | none => none
    | some (st1, sv1) =>
      match inferSValTy st1 sv1 with
      | none => none
      | some elemTy =>
        if !isModeledScalarTy elemTy then none
        else
          let st1' := emitOb st1 (.hasTy sv1 elemTy)
          let l := st1'.nextLoc
          some ({ st1' with
                  nextLoc := l + 1
                  cells := (l, sv1) :: st1'.cells
                  cellTys := (l, elemTy) :: st1'.cellTys }, .loc l)
  | .cellGet e1 =>
    match vcgen env st e1 with
    | none => none
    | some (st1, .loc l) =>
      match locLookup st1.cells l with
      | some sv => some (st1, sv)
      | none => none
    | some _ => none
  | .cellSet e1 e2 =>
    match vcgen env st e1 with
    | none => none
    | some (st1, .loc l) =>
      match vcgen env st1 e2 with
      | none => none
      | some (st2, sv2) =>
        match locLookup st2.cells l with
        | some _ =>
          let st2' := match locLookup st2.cellTys l with
            | some ty => emitOb st2 (.hasTy sv2 ty)
            | none => st2
          some ({ st2' with cells := (l, sv2) :: st2'.cells }, .lit .unit)
        | none => none
    | some _ => none
  | .getTag e1 =>
    match vcgen env st e1 with
    | none => none
    | some (st1, sv1) => some (st1, .getTag sv1)
  | .while_ c b =>
    match env.loops c b with
    | none => none
    | some lc =>
      -- 1. Check entry invariant (pure)
      match vcgenPure st lc.inv with
      | none => none
      | some (stI0, svI0) =>
        let st1 := emitOb stI0 (.isTrue svI0)
        -- 2. Conservative havoc of all tracked cells
        let stH := havocCells st1 (trackedLocs st1)
        -- 3. Assume invariant in havocked state
        match vcgenPure stH lc.inv with
        | none => none
        | some (stIH, svIH) =>
          let stLoopEntry := withPath stIH (.isTrue svIH)
          -- 4. Evaluate loop condition (must not allocate cells)
          match vcgen env stLoopEntry c with
          | none => none
          | some (stC, svC) =>
            if stC.nextLoc != stLoopEntry.nextLoc then none
            else
              -- 5. Optional pre-iteration `decreases >= 0` check, then body, then `decreases' < decreases` & `inv`
              let stBodyIn0 := withPath stC (.isTrue svC)
              match checkLoopPreDec stBodyIn0 lc.dec with
              | none => none
              | some (stBodyIn, svD0Opt) =>
                match vcgen env stBodyIn b with
                | none => none
                | some (stB, _) =>
                  if stB.nextLoc != stC.nextLoc then none
                  else
                    match checkLoopPostDec stB lc.dec svD0Opt with
                    | none => none
                    | some stBDec =>
                      match vcgenPure stBDec lc.inv with
                      | none => none
                      | some (stBInv, svBInv) =>
                        let stObs := emitOb stBInv (.isTrue svBInv)
                        -- 6. Post-loop state: `I ∧ ¬c` in havocked post-cond state
                        let stExit : SymState :=
                          { nextSym := stObs.nextSym, nextLoc := stC.nextLoc,
                            vars := st.vars, cells := stC.cells, cellTys := st.cellTys,
                            path := .and stC.path (.isFalse svC), obs := stObs.obs }
                        some (stExit, .lit .unit)
  | .applyDir name args =>
    -- Special `assert(e)` / `assume(e)` intrinsics
    if name == "assert" then
      match args with
      | [e1] =>
        match vcgen env st e1 with
        | none => none
        | some (st1, sv1) => some (emitOb st1 (.isTrue sv1), .lit .unit)
      | _ => none
    else if name == "assume" then
      match args with
      | [e1] =>
        match vcgen env st e1 with
        | none => none
        | some (st1, sv1) => some (withPath st1 (.isTrue sv1), .lit .unit)
      | _ => none
    else
      -- Modular function call with pairwise mutable-argument non-aliasing & scalar type checks
      match env.contracts name with
      | none => none
      | some fc =>
        if args.length != fc.params.length || !isModeledScalarTy fc.retTy then none
        else
          match vcgenList env st args with
          | none => none
          | some (stA, svArgs) =>
            let locArgs := collectLocArgs svArgs
            -- Fail-closed if any two mutable `Loc` arguments alias or are out of bounds!
            if !noDupLocs locArgs || !(locArgs.all (· < stA.nextLoc)) then none
            else
              match checkCallArgTys stA fc.params svArgs with
              | none => none
              | some stTyped =>
                let paramBindings := (fc.params.map Prod.fst).zip svArgs
                match vcgenPure { stTyped with vars := paramBindings } fc.req with
                | none => none
                | some (stReq, svReq) =>
                  let stChecked0 := emitOb stReq (.isTrue svReq)
                  match checkCallDecreases env name fc stChecked0 with
                  | none => none
                  | some stChecked =>
                    -- Havoc mutable `Loc` arguments and allocate fresh typed return symbol
                    let stHav := havocCells stChecked locArgs
                    let retId := stHav.nextSym
                    let stRet : SymState :=
                      { stHav with
                        nextSym := retId + 1
                        vars := (fc.retVar, .sym retId) :: paramBindings
                        path := .and stHav.path (.hasTy (.sym retId) fc.retTy) }
                    match vcgenPure stRet fc.ens with
                    | none => none
                    | some (stEns, svEns) =>
                      let stPost : SymState :=
                        { nextSym := stEns.nextSym, nextLoc := stA.nextLoc,
                          vars := stA.vars, cells := stHav.cells, cellTys := stA.cellTys,
                          path := .and (.and stHav.path (.hasTy (.sym retId) fc.retTy)) (.isTrue svEns),
                          obs := stEns.obs }
                      some (stPost, .sym retId)
  | _ => none
termination_by sizeOf e

def vcgenBlock (env : VcgEnv) (st : SymState) (es : List Expr) : Option (SymState × SVal) :=
  match es with
  | [] => some (st, .lit .unit)
  | [e1] => vcgen env st e1
  | e1 :: e2 :: rest =>
    match vcgen env st e1 with
    | none => none
    | some (st1, _) => vcgenBlock env st1 (e2 :: rest)
termination_by sizeOf es

def vcgenList (env : VcgEnv) (st : SymState) (es : List Expr) : Option (SymState × List SVal) :=
  match es with
  | [] => some (st, [])
  | e1 :: rest =>
    match vcgen env st e1 with
    | none => none
    | some (st1, sv1) =>
      match vcgenList env st1 rest with
      | none => none
      | some (st2, svs) => some (st2, sv1 :: svs)
termination_by sizeOf es
end

/-- Build initial symbolic state for a function's parameters: fresh typed symbols for
    modeled scalar params and fresh distinct `Loc`s for typed `Cell` params.
    Fail-closed (`none`) on unmodeled parameter types (e.g. `Float`, `Str`, `Arr`, ADTs). -/
def initFnSymState (params : List (Ident × Ty)) : Option SymState :=
  params.foldlM (fun (s : SymState) (p : Ident × Ty) =>
    match p.2 with
    | .cell elemTy =>
      if isModeledScalarTy elemTy then
        let l := s.nextLoc
        let id := s.nextSym
        some { s with
          nextSym := id + 1
          nextLoc := l + 1
          vars := (p.1, .loc l) :: s.vars
          cells := (l, .sym id) :: s.cells
          cellTys := (l, elemTy) :: s.cellTys
          path := .and s.path (.hasTy (.sym id) elemTy) }
      else none
    | ty =>
      if isModeledScalarTy ty then
        let id := s.nextSym
        some { s with
          nextSym := id + 1
          vars := (p.1, .sym id) :: s.vars
          path := .and s.path (.hasTy (.sym id) ty) }
      else none) ({} : SymState)

/-- Function-level VCG entry point mirroring `verifySingleFn` in `src/verify.gsa`.
    Checks `requires` well-formedness, optional entry `decreases >= 0`, body VCs,
    and postcondition `ensures`. -/
def verifyFn (env : VcgEnv) (fd : FunDef) (fc : FnContract) : Option (List SForm) :=
  if fd.params.length != fc.params.length then none
  else
    match initFnSymState fd.params with
    | none => none
    | some initSt =>
      match vcgenPure initSt fc.req with
      | none => none
      | some (stReq, svReq) =>
        let stAssumed0 := withPath stReq (.isTrue svReq)
        match checkLoopPreDec stAssumed0 fc.dec with
        | none => none
        | some (stAssumed, curDecOpt) =>
          let bodyEnv : VcgEnv := { env with curFn := fd.name, curDec := curDecOpt }
          match vcgen bodyEnv stAssumed fd.body with
          | none => none
          | some (stBody, svRet) =>
            match vcgenPure { stBody with vars := (fc.retVar, svRet) :: stBody.vars } fc.ens with
            | none => none
            | some (stEns, svEns) =>
              let stFinal := emitOb stEns (.isTrue svEns)
              some stFinal.obs

/-! ## Part 5: Well-Formedness & Soundness Proofs (`vcgen_sound`, `verifyFn_sound`) -/

/-- Well-formedness of symbolic state: all symbols in `vars`, `cells`, `path` are `< nextSym`,
    and all tracked `Loc`s in `cells` are `< nextLoc`. -/
structure SymWf (st : SymState) : Prop where
  vars_bound  : ∀ p ∈ st.vars, svalBound st.nextSym p.2
  cells_bound : ∀ p ∈ st.cells, p.1 < st.nextLoc ∧ svalBound st.nextSym p.2
  path_bound  : sformBound st.nextSym st.path

/-- Upper bound on symbolic location IDs `.loc k` occurring in `SVal`. -/
def svalLocBound (m : Nat) : SVal → Prop
  | .lit _ | .sym _ => True
  | .loc k => k < m
  | .un _ e => svalLocBound m e
  | .bin _ e1 e2 => svalLocBound m e1 ∧ svalLocBound m e2
  | .ite c t e => svalLocBound m c ∧ svalLocBound m t ∧ svalLocBound m e
  | .getTag v => svalLocBound m v

theorem svalLocBound_mono {m1 m2 : Nat} (hle : m1 ≤ m2) {sv : SVal} (h : svalLocBound m1 sv) :
    svalLocBound m2 sv := by
  induction sv with
  | lit _ | sym _ => trivial
  | loc k => exact Nat.lt_of_lt_of_le h hle
  | un _ _ ih => exact ih h
  | bin _ _ _ ih1 ih2 => exact ⟨ih1 h.1, ih2 h.2⟩
  | ite _ _ _ ih1 ih2 ih3 => exact ⟨ih1 h.1, ih2 h.2.1, ih3 h.2.2⟩
  | getTag _ ih => exact ih h

theorem evalSVal_loc_agree_lt {M : Model} {L1 L2 : Loc → Loc} {m : Nat} {sv : SVal}
    (hb : svalLocBound m sv) (hagree : ∀ k < m, L2 k = L1 k) :
    evalSVal M L2 sv = evalSVal M L1 sv := by
  induction sv with
  | lit _ | sym _ => rfl
  | loc k => simp [evalSVal, hagree k hb]
  | un op e ih => simp [evalSVal, ih hb]
  | bin op e1 e2 ih1 ih2 => simp [evalSVal, ih1 hb.1, ih2 hb.2]
  | ite c t e ihc iht ihe => simp [evalSVal, ihc hb.1, iht hb.2.1, ihe hb.2.2]
  | getTag e ih => simp [evalSVal, ih hb]

/-- Concrete state `(ρ, σ)` matches symbolic state `st` under model `M` and
    injective symbolic-to-physical location map `L : Loc → Loc`.
    Supports arbitrary pre-existing heaps `σ` of any size (`∀ k < st.nextLoc, L k < σ.length`)
    and tracks typed `Cell` invariants (`cells_ty`). -/
structure StateMatches (M : Model) (L : Loc → Loc) (st : SymState) (ρ : List (Ident × Expr)) (σ : Store) : Prop where
  closed_env  : ClosedEnv ρ
  wf          : SymWf st
  loc_bound   : ∀ k < st.nextLoc, L k < σ.length
  loc_inj     : ∀ k1 k2, k1 < st.nextLoc → k2 < st.nextLoc → L k1 = L k2 → k1 = k2
  path_holds  : evalSForm M st.path
  vars_match  : ∀ x sv, assocLookup st.vars x = some sv →
    ∃ v, assocLookup ρ x = some v ∧ evalSVal M L sv = some v ∧ svalLocBound st.nextLoc sv
  cells_match : ∀ l sv, locLookup st.cells l = some sv →
    ∃ v, σ[L l]? = some v ∧ evalSVal M L sv = some v ∧ svalLocBound st.nextLoc sv
  cells_ty    : ∀ l ty, locLookup st.cellTys l = some ty →
    l < st.nextLoc ∧ ∃ v, σ[L l]? = some v ∧ valHasTy v ty

theorem StateMatches.of_eq {M : Model} {L : Loc → Loc} {st1 st2 : SymState}
    {ρ : List (Ident × Expr)} {σ : Store} (h : StateMatches M L st1 ρ σ)
    (hwf : SymWf st2) (hloc : st2.nextLoc = st1.nextLoc)
    (hv : st2.vars = st1.vars) (hc : st2.cells = st1.cells) (hct : st2.cellTys = st1.cellTys)
    (hp : evalSForm M st2.path) : StateMatches M L st2 ρ σ :=
  ⟨h.closed_env, hwf, hloc ▸ h.loc_bound, hloc ▸ h.loc_inj, hp,
   by rw [hv, hloc]; exact h.vars_match,
   by rw [hc, hloc]; exact h.cells_match,
   by rw [hct, hloc]; exact h.cells_ty⟩

/-- Step-bounded execution safety + postcondition preservation. -/
def SafeExecN (Δ : AdtEnv) (Φ : FunEnv) (bound : Nat) (e : Expr) (σ : Store)
    (Post : Expr → Store → Prop) : Prop :=
  (∀ k ≤ bound, ∀ σ', ¬ StepsN Δ Φ k e σ (.trap .divByZero) σ') ∧
  (∀ k ≤ bound, ∀ v σ', IsValue v → StepsN Δ Φ k e σ v σ' → Post v σ')

/-- Unbounded execution safety + postcondition preservation. -/
def SafeExec (Δ : AdtEnv) (Φ : FunEnv) (e : Expr) (σ : Store)
    (Post : Expr → Store → Prop) : Prop :=
  (∀ σ', ¬ Steps Δ Φ e σ (.trap .divByZero) σ') ∧
  (∀ v σ', IsValue v → Steps Δ Φ e σ v σ' → Post v σ')

theorem safeExec_of_forall_safeExecN {Δ : AdtEnv} {Φ : FunEnv} {e : Expr} {σ : Store}
    {Post : Expr → Store → Prop}
    (h : ∀ bound, SafeExecN Δ Φ bound e σ Post) : SafeExec Δ Φ e σ Post := by
  constructor
  · intro σ' hsteps
    rcases steps_to_stepsN hsteps with ⟨k, hk⟩
    exact (h k).1 k (Nat.le_refl k) σ' hk
  · intro v σ' hv hsteps
    rcases steps_to_stepsN hsteps with ⟨k, hk⟩
    exact (h k).2 k (Nat.le_refl k) v σ' hv hk

theorem validObs_mono {obs1 obs2 : List SForm} (hsub : ∀ f ∈ obs1, f ∈ obs2)
    (hv : ValidObs obs2) : ValidObs obs1 :=
  fun f hf => hv f (hsub f hf)

theorem locLookup_mergeCells {svc : SVal} {base cellsT cellsE : List (Loc × SVal)}
    {l : Loc} {sv : SVal} (h : locLookup (mergeCells svc base cellsT cellsE) l = some sv) :
    ∃ svBase, locLookup base l = some svBase ∧
      sv = .ite svc ((locLookup cellsT l).getD svBase) ((locLookup cellsE l).getD svBase) := by
  induction base with
  | nil => simp [mergeCells, locLookup] at h
  | cons p rest ih =>
    rcases p with ⟨k, svB⟩
    simp only [mergeCells, List.map, locLookup] at h ⊢
    by_cases hkl : (k == l) = true
    · have hk : k = l := eq_of_beq hkl
      subst hk
      simp [hkl] at h ⊢
      exact h.symm
    · simp [hkl] at h ⊢
      exact ih h

theorem symWf_withPath {st : SymState} {c : SForm} (hwf : SymWf st)
    (hc : sformBound st.nextSym c) : SymWf (withPath st c) :=
  { vars_bound := hwf.vars_bound
    cells_bound := hwf.cells_bound
    path_bound := ⟨hwf.path_bound, hc⟩ }

/-- `vcgenPure` preserves `nextSym`, `nextLoc`, `vars`, `cells`, `path`, grows `obs`
    monotonically, and produces a bounded `SVal`. -/
theorem vcgenPure_wf {st st' : SymState} {e : Expr} {sv : SVal}
    (hwf : SymWf st) (hvc : vcgenPure st e = some (st', sv)) :
    st'.nextSym = st.nextSym ∧
    st'.nextLoc = st.nextLoc ∧
    st'.vars = st.vars ∧
    st'.cells = st.cells ∧
    st'.path = st.path ∧
    (∀ f ∈ st.obs, f ∈ st'.obs) ∧
    svalBound st.nextSym sv := by
  cases e with
  | lit l =>
    simp only [vcgenPure] at hvc
    split at hvc
    · cases hvc; exact ⟨rfl, rfl, rfl, rfl, rfl, fun _ h => h, trivial⟩
    · cases hvc
  | var x =>
    simp only [vcgenPure] at hvc
    cases hlu : assocLookup st.vars x with
    | none => simp [hlu] at hvc
    | some sv0 =>
      simp [hlu] at hvc; rcases hvc with ⟨rfl, rfl⟩
      exact ⟨rfl, rfl, rfl, rfl, rfl, fun _ h => h, hwf.vars_bound _ (assocLookup_mem hlu)⟩
  | loc _ => simp [vcgenPure] at hvc
  | un op e1 =>
    simp only [vcgenPure] at hvc
    split at hvc
    · cases hvc
    · cases h1 : vcgenPure st e1 with
      | none => simp [h1] at hvc
      | some r1 =>
        rcases r1 with ⟨st1, sv1⟩; simp [h1] at hvc; rcases hvc with ⟨rfl, rfl⟩
        simpa [svalBound] using vcgenPure_wf hwf h1
  | bin op e1 e2 =>
    by_cases hAnd : op = .and
    · subst hAnd
      simp only [vcgenPure] at hvc
      cases h1 : vcgenPure st e1 with
      | none => simp [h1] at hvc
      | some r1 =>
        rcases r1 with ⟨st1, sv1⟩; simp only [h1] at hvc
        rcases vcgenPure_wf hwf h1 with ⟨hs1, hl1, hv1, hc1, hp1, ho1, hb1⟩
        have hwf1 : SymWf (withPath st1 (.isTrue sv1)) := by
          refine ⟨?_, ?_, ?_⟩
          · simp only [withPath, hs1, hv1]; exact hwf.vars_bound
          · simp only [withPath, hs1, hl1, hc1]; exact hwf.cells_bound
          · simp only [withPath, sformBound, hs1, hp1]; exact ⟨hwf.path_bound, hb1⟩
        cases h2 : vcgenPure (withPath st1 (.isTrue sv1)) e2 with
        | none => simp [h2] at hvc
        | some r2 =>
          rcases r2 with ⟨st2, sv2⟩; simp [h2] at hvc; rcases hvc with ⟨rfl, rfl⟩
          rcases vcgenPure_wf hwf1 h2 with ⟨_, _, _, _, _, ho2, hb2⟩
          simp only [withPath, hs1] at hb2
          exact ⟨hs1, hl1, hv1, hc1, hp1, fun f hf => ho2 f (ho1 f hf), ⟨hb1, hb2, trivial⟩⟩
    · by_cases hOr : op = .or
      · subst hOr
        simp only [vcgenPure, reduceCtorEq, ↓reduceIte] at hvc
        cases h1 : vcgenPure st e1 with
        | none => simp [h1] at hvc
        | some r1 =>
          rcases r1 with ⟨st1, sv1⟩; simp only [h1] at hvc
          rcases vcgenPure_wf hwf h1 with ⟨hs1, hl1, hv1, hc1, hp1, ho1, hb1⟩
          have hwf1 : SymWf (withPath st1 (.isFalse sv1)) := by
            refine ⟨?_, ?_, ?_⟩
            · simp only [withPath, hs1, hv1]; exact hwf.vars_bound
            · simp only [withPath, hs1, hl1, hc1]; exact hwf.cells_bound
            · simp only [withPath, sformBound, hs1, hp1]; exact ⟨hwf.path_bound, hb1⟩
          cases h2 : vcgenPure (withPath st1 (.isFalse sv1)) e2 with
          | none => simp [h2] at hvc
          | some r2 =>
            rcases r2 with ⟨st2, sv2⟩; simp [h2] at hvc; rcases hvc with ⟨rfl, rfl⟩
            rcases vcgenPure_wf hwf1 h2 with ⟨_, _, _, _, _, ho2, hb2⟩
            simp only [withPath, hs1] at hb2
            exact ⟨hs1, hl1, hv1, hc1, hp1, fun f hf => ho2 f (ho1 f hf), ⟨hb1, trivial, hb2⟩⟩
      · simp only [vcgenPure, hAnd, hOr, ↓reduceIte] at hvc
        split at hvc
        · cases hvc
        · cases h1 : vcgenPure st e1 with
          | none => simp [h1] at hvc
          | some r1 =>
            rcases r1 with ⟨st1, sv1⟩; simp only [h1] at hvc
            rcases vcgenPure_wf hwf h1 with ⟨hs1, hl1, hv1, hc1, hp1, ho1, hb1⟩
            have hwf1 : SymWf st1 := ⟨by rw [hs1, hv1]; exact hwf.vars_bound,
              by rw [hs1, hl1, hc1]; exact hwf.cells_bound, by rw [hs1, hp1]; exact hwf.path_bound⟩
            cases h2 : vcgenPure st1 e2 with
            | none => simp [h2] at hvc
            | some r2 =>
              rcases r2 with ⟨st2, sv2⟩; simp only [h2] at hvc; cases hvc
              rcases vcgenPure_wf hwf1 h2 with ⟨hs2, hl2, hv2, hc2, hp2, ho2, hb2⟩
              rw [hs1] at hs2 hb2
              split
              · exact ⟨hs2, hl2.trans hl1, hv2.trans hv1, hc2.trans hc1, hp2.trans hp1,
                  fun f hf => List.mem_cons_of_mem _ (ho2 f (ho1 f hf)), ⟨hb1, hb2⟩⟩
              · exact ⟨hs2, hl2.trans hl1, hv2.trans hv1, hc2.trans hc1, hp2.trans hp1,
                  fun f hf => ho2 f (ho1 f hf), ⟨hb1, hb2⟩⟩
  | if_ c t e =>
    simp only [vcgenPure] at hvc
    cases h1 : vcgenPure st c with
    | none => simp [h1] at hvc
    | some r1 =>
      rcases r1 with ⟨st1, svc⟩; simp only [h1] at hvc
      rcases vcgenPure_wf hwf h1 with ⟨hs1, hl1, hv1, hc1, hp1, ho1, hbc⟩
      have hwfT : SymWf (withPath st1 (.isTrue svc)) := by
        refine ⟨by simp only [withPath, hs1, hv1]; exact hwf.vars_bound,
          by simp only [withPath, hs1, hl1, hc1]; exact hwf.cells_bound,
          by simp only [withPath, sformBound, hs1, hp1]; exact ⟨hwf.path_bound, hbc⟩⟩
      cases hT : vcgenPure (withPath st1 (.isTrue svc)) t with
      | none => simp [hT] at hvc
      | some rT =>
        rcases rT with ⟨stT, svT⟩; simp only [hT] at hvc
        rcases vcgenPure_wf hwfT hT with ⟨_, _, _, _, _, hoT, hbT⟩
        have hwfE : SymWf { st1 with path := .and st1.path (.isFalse svc), obs := stT.obs } := by
          refine ⟨by simp only [hs1, hv1]; exact hwf.vars_bound,
            by simp only [hs1, hl1, hc1]; exact hwf.cells_bound,
            by simp only [sformBound, hs1, hp1]; exact ⟨hwf.path_bound, hbc⟩⟩
        cases hE : vcgenPure { st1 with path := .and st1.path (.isFalse svc), obs := stT.obs } e with
        | none => simp [hE] at hvc
        | some rE =>
          rcases rE with ⟨stE, svE⟩; simp [hE] at hvc; rcases hvc with ⟨rfl, rfl⟩
          rcases vcgenPure_wf hwfE hE with ⟨_, _, _, _, _, hoE, hbE⟩
          simp only [withPath, hs1] at hbT hbE
          exact ⟨hs1, hl1, hv1, hc1, hp1, fun f hf => hoE f (hoT f (ho1 f hf)), ⟨hbc, hbT, hbE⟩⟩
  | cellGet e1 =>
    simp only [vcgenPure] at hvc
    cases h1 : vcgenPure st e1 with
    | none => simp [h1] at hvc
    | some r1 =>
      rcases r1 with ⟨st1, sv1⟩; simp only [h1] at hvc
      rcases vcgenPure_wf hwf h1 with ⟨hs1, hl1, hv1, hc1, hp1, ho1, _⟩
      cases sv1 with
      | loc l =>
        simp only at hvc
        cases hlu : locLookup st1.cells l with
        | none => simp [hlu] at hvc
        | some sv =>
          simp [hlu] at hvc; rcases hvc with ⟨rfl, rfl⟩
          rw [hc1] at hlu
          exact ⟨hs1, hl1, hv1, hc1, hp1, ho1, (hwf.cells_bound _ (locLookup_mem hlu)).2⟩
      | _ => simp at hvc
  | getTag e1 =>
    simp only [vcgenPure] at hvc
    cases h1 : vcgenPure st e1 with
    | none => simp [h1] at hvc
    | some r1 =>
      rcases r1 with ⟨st1, sv1⟩; simp [h1] at hvc; rcases hvc with ⟨rfl, rfl⟩
      simpa [svalBound] using vcgenPure_wf hwf h1
  | _ => simp [vcgenPure] at hvc
termination_by sizeOf e

/-- `vcgenPure` never modifies `cellTys`. -/
theorem vcgenPure_cellTys_eq {st st' : SymState} {e : Expr} {sv : SVal}
    (hvc : vcgenPure st e = some (st', sv)) : st'.cellTys = st.cellTys := by
  cases e with
  | lit _ => simp only [vcgenPure] at hvc; split at hvc <;> cases hvc; rfl
  | var x =>
    simp only [vcgenPure] at hvc
    cases hlu : assocLookup st.vars x <;> simp [hlu] at hvc
    rcases hvc with ⟨rfl, _⟩; rfl
  | un op e1 =>
    simp only [vcgenPure] at hvc; split at hvc
    · cases hvc
    · cases h1 : vcgenPure st e1 with
      | none => simp [h1] at hvc
      | some r1 => rcases r1 with ⟨st1, _⟩; simp [h1] at hvc; rcases hvc with ⟨rfl, _⟩; exact vcgenPure_cellTys_eq h1
  | bin op e1 e2 =>
    by_cases hAnd : op = .and
    · subst hAnd; simp only [vcgenPure, ↓reduceIte] at hvc
      cases h1 : vcgenPure st e1 with
      | none => simp [h1] at hvc
      | some r1 =>
        rcases r1 with ⟨st1, sv1⟩; simp only [h1] at hvc
        cases h2 : vcgenPure (withPath st1 (.isTrue sv1)) e2 with
        | none => simp [h2] at hvc
        | some r2 => rcases r2 with ⟨st2, _⟩; simp [h2] at hvc; rcases hvc with ⟨rfl, _⟩; simpa using vcgenPure_cellTys_eq h1
    · by_cases hOr : op = .or
      · subst hOr; simp only [vcgenPure, reduceCtorEq, ↓reduceIte] at hvc
        cases h1 : vcgenPure st e1 with
        | none => simp [h1] at hvc
        | some r1 =>
          rcases r1 with ⟨st1, sv1⟩; simp only [h1] at hvc
          cases h2 : vcgenPure (withPath st1 (.isFalse sv1)) e2 with
          | none => simp [h2] at hvc
          | some r2 => rcases r2 with ⟨st2, _⟩; simp [h2] at hvc; rcases hvc with ⟨rfl, _⟩; simpa using vcgenPure_cellTys_eq h1
      · simp only [vcgenPure, hAnd, hOr, ↓reduceIte] at hvc; split at hvc
        · cases hvc
        · cases h1 : vcgenPure st e1 with
          | none => simp [h1] at hvc
          | some r1 =>
            rcases r1 with ⟨st1, _⟩; simp only [h1] at hvc
            cases h2 : vcgenPure st1 e2 with
            | none => simp [h2] at hvc
            | some r2 =>
              rcases r2 with ⟨st2, _⟩; simp only [h2] at hvc; cases hvc
              split <;> exact (vcgenPure_cellTys_eq h2).trans (vcgenPure_cellTys_eq h1)
  | if_ c t e =>
    simp only [vcgenPure] at hvc
    cases h1 : vcgenPure st c with
    | none => simp [h1] at hvc
    | some r1 =>
      rcases r1 with ⟨st1, svc⟩; simp only [h1] at hvc
      cases hT : vcgenPure (withPath st1 (.isTrue svc)) t with
      | none => simp [hT] at hvc
      | some rT =>
        rcases rT with ⟨stT, _⟩; simp only [hT] at hvc
        cases hE : vcgenPure { st1 with path := .and st1.path (.isFalse svc), obs := stT.obs } e with
        | none => simp [hE] at hvc
        | some rE => rcases rE with ⟨stE, _⟩; simp [hE] at hvc; rcases hvc with ⟨rfl, _⟩; simpa using vcgenPure_cellTys_eq h1
  | cellGet e1 =>
    simp only [vcgenPure] at hvc
    cases h1 : vcgenPure st e1 with
    | none => simp [h1] at hvc
    | some r1 =>
      rcases r1 with ⟨st1, sv1⟩; simp only [h1] at hvc
      cases sv1 <;> simp at hvc
      rename_i l; cases hlu : locLookup st1.cells l <;> simp [hlu] at hvc
      rcases hvc with ⟨rfl, _⟩; exact vcgenPure_cellTys_eq h1
  | getTag e1 =>
    simp only [vcgenPure] at hvc
    cases h1 : vcgenPure st e1 with
    | none => simp [h1] at hvc
    | some r1 => rcases r1 with ⟨st1, _⟩; simp [h1] at hvc; rcases hvc with ⟨rfl, _⟩; exact vcgenPure_cellTys_eq h1
  | _ => simp [vcgenPure] at hvc
termination_by sizeOf e

/-- Soundness of `vcgenPure`: pure contract expressions never trap with `divByZero`,
    leave the store `σ` untouched, and evaluate to `evalSVal M sv`. -/
theorem vcgenPure_sound {Δ : AdtEnv} {Φ : FunEnv} {M : Model} {L : Loc → Loc} {st st' : SymState}
    {ρ : List (Ident × Expr)} {σ : Store} {e : Expr} {sv : SVal}
    (hM : ValidModel M) (hMatch : StateMatches M L st ρ σ)
    (hvc : vcgenPure st e = some (st', sv)) (hObs : ValidObs st'.obs) :
    SafeExec Δ Φ (substMany ρ e) σ (fun v σ' => σ' = σ ∧ evalSVal M L sv = some v) := by
  apply safeExec_of_forall_safeExecN
  intro bound
  cases e with
  | lit l =>
    simp only [vcgenPure] at hvc
    split at hvc
    · cases hvc
      rw [substMany_lit]
      constructor
      · intro k _ σ' hs; rcases stepsN_of_value (.lit l) hs with ⟨_, hEq, _⟩; cases hEq
      · intro k _ v σ' _ hs
        rcases stepsN_of_value (.lit l) hs with ⟨_, rfl, rfl⟩
        exact ⟨rfl, rfl⟩
    · cases hvc
  | var x =>
    simp only [vcgenPure] at hvc
    cases hlu : assocLookup st.vars x with
    | none => simp [hlu] at hvc
    | some sv0 =>
      simp [hlu] at hvc; rcases hvc with ⟨rfl, rfl⟩
      rcases hMatch.vars_match x sv0 hlu with ⟨v0, hρx, hev, _⟩
      have hv0 : IsValue v0 := (evalSVal_closed hM hev).1
      rw [substMany_var hMatch.closed_env, hρx]
      constructor
      · intro k _ σ' hs; rcases stepsN_of_value hv0 hs with ⟨_, hEq, _⟩; subst hEq; cases hv0
      · intro k _ v σ' _ hs
        rcases stepsN_of_value hv0 hs with ⟨_, rfl, rfl⟩
        exact ⟨rfl, hev⟩
  | loc _ => simp [vcgenPure] at hvc
  | un op e1 =>
    simp only [vcgenPure] at hvc
    split at hvc
    · cases hvc
    · cases h1 : vcgenPure st e1 with
      | none => simp [h1] at hvc
      | some r1 =>
        rcases r1 with ⟨st1, sv1⟩; simp [h1] at hvc; rcases hvc with ⟨rfl, rfl⟩
        have ih1 := vcgenPure_sound (Δ := Δ) (Φ := Φ) hM hMatch h1 hObs
        rw [substMany_un]
        constructor
        · intro k _ σ' hs
          rcases stepsN_un_terminal (Or.inr ⟨_, rfl⟩) hs with ⟨k1, _, t, hst1, hEq⟩ | ⟨_, _, _, _, _, _, hEq⟩
          · cases hEq; exact ih1.1 σ' (stepsN_to_steps hst1)
          · cases hEq
        · intro k _ v σ' hv hs
          rcases stepsN_un_terminal (Or.inl hv) hs with ⟨_, _, _, _, hEq⟩ | ⟨k1, _, l, l', hst1, hev, rfl⟩
          · subst hEq; cases hv
          · rcases ih1.2 (.lit l) σ' (.lit l) (stepsN_to_steps hst1) with ⟨rfl, hev1⟩
            exact ⟨rfl, by simp [evalSVal, hev1, hev]⟩
  | bin op e1 e2 =>
    by_cases hAnd : op = .and
    · subst hAnd
      simp only [vcgenPure] at hvc
      cases h1 : vcgenPure st e1 with
      | none => simp [h1] at hvc
      | some r1 =>
        rcases r1 with ⟨st1, sv1⟩; simp only [h1] at hvc
        rcases vcgenPure_wf hMatch.wf h1 with ⟨hs1, hl1, hv1, hc1, hp1, ho1, hb1⟩
        cases h2 : vcgenPure (withPath st1 (.isTrue sv1)) e2 with
        | none => simp [h2] at hvc
        | some r2 =>
          rcases r2 with ⟨st2, sv2⟩; simp [h2] at hvc; rcases hvc with ⟨rfl, rfl⟩
          have hwf1 : SymWf (withPath st1 (.isTrue sv1)) :=
            ⟨by simp only [withPath, hs1, hv1]; exact hMatch.wf.vars_bound,
             by simp only [withPath, hs1, hl1, hc1]; exact hMatch.wf.cells_bound,
             by simp only [withPath, sformBound, hs1, hp1]; exact ⟨hMatch.wf.path_bound, hb1⟩⟩
          rcases vcgenPure_wf hwf1 h2 with ⟨_, _, _, _, _, ho2, _⟩
          have ih1 := vcgenPure_sound (Δ := Δ) (Φ := Φ) hM hMatch h1 (validObs_mono ho2 hObs)
          rw [substMany_bin]
          constructor
          · intro k _ σ' hs
            rcases stepsN_and_terminal (Or.inr ⟨_, rfl⟩) hs with
              ⟨k1, _, t, hst1, hEq⟩ | ⟨_, _, _, hEq⟩ | ⟨k1, k2, _, σ1, hst1, hst2⟩
            · cases hEq; exact ih1.1 σ' (stepsN_to_steps hst1)
            · cases hEq
            · rcases ih1.2 (.lit (.bool true)) σ1 (.lit _) (stepsN_to_steps hst1) with ⟨hσ1, hev1⟩
              subst hσ1
              have hMatch1 : StateMatches M L (withPath st1 (.isTrue sv1)) ρ σ1 :=
                hMatch.of_eq hwf1 hl1 hv1 hc1 (by simpa [withPath] using vcgenPure_cellTys_eq h1)
                  ⟨by simp only [hp1]; exact hMatch.path_holds, evalSVal_lit_iff_id.mp hev1⟩
              have ih2 := vcgenPure_sound (Δ := Δ) (Φ := Φ) hM hMatch1 h2 hObs
              exact ih2.1 σ' (stepsN_to_steps hst2)
          · intro k _ v σ' hv hs
            rcases stepsN_and_terminal (Or.inl hv) hs with
              ⟨_, _, _, _, hEq⟩ | ⟨k1, _, hst1, rfl⟩ | ⟨k1, k2, _, σ1, hst1, hst2⟩
            · subst hEq; cases hv
            · rcases ih1.2 (.lit (.bool false)) σ' (.lit _) (stepsN_to_steps hst1) with ⟨rfl, hev1⟩
              exact ⟨rfl, by simp [evalSVal, hev1]⟩
            · rcases ih1.2 (.lit (.bool true)) σ1 (.lit _) (stepsN_to_steps hst1) with ⟨hσ1, hev1⟩
              subst hσ1
              have hMatch1 : StateMatches M L (withPath st1 (.isTrue sv1)) ρ σ1 :=
                hMatch.of_eq hwf1 hl1 hv1 hc1 (by simpa [withPath] using vcgenPure_cellTys_eq h1)
                  ⟨by simp only [hp1]; exact hMatch.path_holds, evalSVal_lit_iff_id.mp hev1⟩
              have ih2 := vcgenPure_sound (Δ := Δ) (Φ := Φ) hM hMatch1 h2 hObs
              rcases ih2.2 v σ' hv (stepsN_to_steps hst2) with ⟨rfl, hev2⟩
              exact ⟨rfl, by simp [evalSVal, hev1, hev2]⟩
    · by_cases hOr : op = .or
      · subst hOr
        simp only [vcgenPure, reduceCtorEq, ↓reduceIte] at hvc
        cases h1 : vcgenPure st e1 with
        | none => simp [h1] at hvc
        | some r1 =>
          rcases r1 with ⟨st1, sv1⟩; simp only [h1] at hvc
          rcases vcgenPure_wf hMatch.wf h1 with ⟨hs1, hl1, hv1, hc1, hp1, ho1, hb1⟩
          cases h2 : vcgenPure (withPath st1 (.isFalse sv1)) e2 with
          | none => simp [h2] at hvc
          | some r2 =>
            rcases r2 with ⟨st2, sv2⟩; simp [h2] at hvc; rcases hvc with ⟨rfl, rfl⟩
            have hwf1 : SymWf (withPath st1 (.isFalse sv1)) :=
              ⟨by simp only [withPath, hs1, hv1]; exact hMatch.wf.vars_bound,
               by simp only [withPath, hs1, hl1, hc1]; exact hMatch.wf.cells_bound,
               by simp only [withPath, sformBound, hs1, hp1]; exact ⟨hMatch.wf.path_bound, hb1⟩⟩
            rcases vcgenPure_wf hwf1 h2 with ⟨_, _, _, _, _, ho2, _⟩
            have ih1 := vcgenPure_sound (Δ := Δ) (Φ := Φ) hM hMatch h1 (validObs_mono ho2 hObs)
            rw [substMany_bin]
            constructor
            · intro k _ σ' hs
              rcases stepsN_or_terminal (Or.inr ⟨_, rfl⟩) hs with
                ⟨k1, _, t, hst1, hEq⟩ | ⟨_, _, _, hEq⟩ | ⟨k1, k2, _, σ1, hst1, hst2⟩
              · cases hEq; exact ih1.1 σ' (stepsN_to_steps hst1)
              · cases hEq
              · rcases ih1.2 (.lit (.bool false)) σ1 (.lit _) (stepsN_to_steps hst1) with ⟨hσ1, hev1⟩
                subst hσ1
                have hMatch1 : StateMatches M L (withPath st1 (.isFalse sv1)) ρ σ1 :=
                  hMatch.of_eq hwf1 hl1 hv1 hc1 (by simpa [withPath] using vcgenPure_cellTys_eq h1)
                    ⟨by simp only [hp1]; exact hMatch.path_holds, evalSVal_lit_iff_id.mp hev1⟩
                have ih2 := vcgenPure_sound (Δ := Δ) (Φ := Φ) hM hMatch1 h2 hObs
                exact ih2.1 σ' (stepsN_to_steps hst2)
            · intro k _ v σ' hv hs
              rcases stepsN_or_terminal (Or.inl hv) hs with
                ⟨_, _, _, _, hEq⟩ | ⟨k1, _, hst1, rfl⟩ | ⟨k1, k2, _, σ1, hst1, hst2⟩
              · subst hEq; cases hv
              · rcases ih1.2 (.lit (.bool true)) σ' (.lit _) (stepsN_to_steps hst1) with ⟨rfl, hev1⟩
                exact ⟨rfl, by simp [evalSVal, hev1]⟩
              · rcases ih1.2 (.lit (.bool false)) σ1 (.lit _) (stepsN_to_steps hst1) with ⟨hσ1, hev1⟩
                subst hσ1
                have hMatch1 : StateMatches M L (withPath st1 (.isFalse sv1)) ρ σ1 :=
                  hMatch.of_eq hwf1 hl1 hv1 hc1 (by simpa [withPath] using vcgenPure_cellTys_eq h1)
                    ⟨by simp only [hp1]; exact hMatch.path_holds, evalSVal_lit_iff_id.mp hev1⟩
                have ih2 := vcgenPure_sound (Δ := Δ) (Φ := Φ) hM hMatch1 h2 hObs
                rcases ih2.2 v σ' hv (stepsN_to_steps hst2) with ⟨rfl, hev2⟩
                exact ⟨rfl, by simp [evalSVal, hev1, hev2]⟩
      · simp only [vcgenPure, hAnd, hOr, ↓reduceIte] at hvc
        split at hvc
        · cases hvc
        · cases h1 : vcgenPure st e1 with
          | none => simp [h1] at hvc
          | some r1 =>
            rcases r1 with ⟨st1, sv1⟩; simp only [h1] at hvc
            rcases vcgenPure_wf hMatch.wf h1 with ⟨hs1, hl1, hv1, hc1, hp1, ho1, _⟩
            have hwf1 : SymWf st1 := ⟨by rw [hs1, hv1]; exact hMatch.wf.vars_bound,
              by rw [hs1, hl1, hc1]; exact hMatch.wf.cells_bound,
              by rw [hs1, hp1]; exact hMatch.wf.path_bound⟩
            cases h2 : vcgenPure st1 e2 with
            | none => simp [h2] at hvc
            | some r2 =>
              rcases r2 with ⟨st2, sv2⟩; simp only [h2] at hvc; cases hvc
              rcases vcgenPure_wf hwf1 h2 with ⟨hs2, hl2, hv2, hc2, hp2, ho2, _⟩
              have hObs2 : ValidObs st2.obs := by
                intro f hf; apply hObs
                split
                · exact List.mem_cons_of_mem _ hf
                · exact hf
              have hMatch1 : StateMatches M L st1 ρ σ :=
                hMatch.of_eq hwf1 hl1 hv1 hc1 (by simpa [withPath] using vcgenPure_cellTys_eq h1) (by rw [hp1]; exact hMatch.path_holds)
              have ih1 := vcgenPure_sound (Δ := Δ) (Φ := Φ) hM hMatch h1 (validObs_mono ho2 hObs2)
              have ih2 := vcgenPure_sound (Δ := Δ) (Φ := Φ) hM hMatch1 h2 hObs2
              rw [substMany_bin]
              constructor
              · intro k _ σ' hs
                rcases stepsN_bin_strict_terminal hAnd hOr (Or.inr ⟨_, rfl⟩) hs with
                  ⟨k1, _, t, hst1, hEq⟩ |
                  ⟨k1, k2, _, v1, σ1, t, hv1', hst1, hst2, hEq⟩ |
                  ⟨k1, k2, _, l1, l2, σ1, r, hst1, hst2, hev, hres⟩
                · cases hEq; exact ih1.1 σ' (stepsN_to_steps hst1)
                · cases hEq
                  rcases ih1.2 v1 σ1 hv1' (stepsN_to_steps hst1) with ⟨rfl, _⟩
                  exact ih2.1 σ' (stepsN_to_steps hst2)
                · rcases ih1.2 (.lit l1) σ1 (.lit _) (stepsN_to_steps hst1) with ⟨rfl, _⟩
                  rcases ih2.2 (.lit l2) σ' (.lit _) (stepsN_to_steps hst2) with ⟨rfl, hev2⟩
                  cases r with
                  | val _ => cases hres
                  | trap t =>
                    cases hres
                    refine evalBinOp_no_divByZero (evalSVal_lit_iff_id.mp hev2) ?_ hev
                    intro hdiv
                    have hObMem : SForm.imp st2.path (.neZero op sv2) ∈ (if isDivOp op then emitOb st2 (.neZero op sv2) else st2).obs := by
                      simp [hdiv, emitOb]
                    have hImp := hObs _ hObMem M hM
                    exact hImp (by rw [hp2, hp1]; exact hMatch.path_holds)
              · intro k _ v σ' hv hs
                rcases stepsN_bin_strict_terminal hAnd hOr (Or.inl hv) hs with
                  ⟨_, _, _, _, hEq⟩ |
                  ⟨_, _, _, _, _, _, _, _, _, hEq⟩ |
                  ⟨k1, k2, _, l1, l2, σ1, r, hst1, hst2, hev, hres⟩
                · subst hEq; cases hv
                · subst hEq; cases hv
                · cases r with
                  | trap _ => subst hres; cases hv
                  | val l' =>
                    subst hres
                    rcases ih1.2 (.lit l1) σ1 (.lit _) (stepsN_to_steps hst1) with ⟨rfl, hev1⟩
                    rcases ih2.2 (.lit l2) σ' (.lit _) (stepsN_to_steps hst2) with ⟨rfl, hev2⟩
                    exact ⟨rfl, by simp [evalSVal, hev1, hev2, hev]⟩
  | if_ c t e =>
    simp only [vcgenPure] at hvc
    cases h1 : vcgenPure st c with
    | none => simp [h1] at hvc
    | some r1 =>
      rcases r1 with ⟨st1, svc⟩; simp only [h1] at hvc
      rcases vcgenPure_wf hMatch.wf h1 with ⟨hs1, hl1, hv1, hc1, hp1, ho1, hbc⟩
      have hwfT : SymWf (withPath st1 (.isTrue svc)) :=
        ⟨by simp only [withPath, hs1, hv1]; exact hMatch.wf.vars_bound,
         by simp only [withPath, hs1, hl1, hc1]; exact hMatch.wf.cells_bound,
         by simp only [withPath, sformBound, hs1, hp1]; exact ⟨hMatch.wf.path_bound, hbc⟩⟩
      cases hT : vcgenPure (withPath st1 (.isTrue svc)) t with
      | none => simp [hT] at hvc
      | some rT =>
        rcases rT with ⟨stT, svT⟩; simp only [hT] at hvc
        rcases vcgenPure_wf hwfT hT with ⟨_, _, _, _, _, hoT, _⟩
        have hwfE : SymWf { st1 with path := .and st1.path (.isFalse svc), obs := stT.obs } :=
          ⟨by simp only [hs1, hv1]; exact hMatch.wf.vars_bound,
           by simp only [hs1, hl1, hc1]; exact hMatch.wf.cells_bound,
           by simp only [sformBound, hs1, hp1]; exact ⟨hMatch.wf.path_bound, hbc⟩⟩
        cases hE : vcgenPure { st1 with path := .and st1.path (.isFalse svc), obs := stT.obs } e with
        | none => simp [hE] at hvc
        | some rE =>
          rcases rE with ⟨stE, svE⟩; simp [hE] at hvc; rcases hvc with ⟨rfl, rfl⟩
          rcases vcgenPure_wf hwfE hE with ⟨_, _, _, _, _, hoE, _⟩
          have hObsT : ValidObs stT.obs := validObs_mono hoE hObs
          have ihC := vcgenPure_sound (Δ := Δ) (Φ := Φ) hM hMatch h1 (validObs_mono hoT hObsT)
          rw [substMany_if]
          constructor
          · intro k _ σ' hs
            rcases stepsN_if_terminal (Or.inr ⟨_, rfl⟩) hs with
              ⟨k1, _, tr, hst1, hEq⟩ |
              ⟨k1, k2, _, σ1, hst1, hst2⟩ |
              ⟨k1, k2, _, σ1, hst1, hst2⟩
            · cases hEq; exact ihC.1 σ' (stepsN_to_steps hst1)
            · rcases ihC.2 (.lit (.bool true)) σ1 (.lit _) (stepsN_to_steps hst1) with ⟨hσ1, hevC⟩
              subst hσ1
              have hMT : StateMatches M L (withPath st1 (.isTrue svc)) ρ σ1 :=
                hMatch.of_eq hwfT hl1 hv1 hc1 (by simpa [withPath] using vcgenPure_cellTys_eq h1)
                  ⟨by simp only [hp1]; exact hMatch.path_holds, evalSVal_lit_iff_id.mp hevC⟩
              exact (vcgenPure_sound (Δ := Δ) (Φ := Φ) hM hMT hT hObsT).1 σ' (stepsN_to_steps hst2)
            · rcases ihC.2 (.lit (.bool false)) σ1 (.lit _) (stepsN_to_steps hst1) with ⟨hσ1, hevC⟩
              subst hσ1
              have hME : StateMatches M L { st1 with path := .and st1.path (.isFalse svc), obs := stT.obs } ρ σ1 :=
                hMatch.of_eq hwfE hl1 hv1 hc1 (by simpa using vcgenPure_cellTys_eq h1)
                  ⟨by simp only [hp1]; exact hMatch.path_holds, evalSVal_lit_iff_id.mp hevC⟩
              exact (vcgenPure_sound (Δ := Δ) (Φ := Φ) hM hME hE hObs).1 σ' (stepsN_to_steps hst2)
          · intro k _ v σ' hv hs
            rcases stepsN_if_terminal (Or.inl hv) hs with
              ⟨_, _, _, _, hEq⟩ |
              ⟨k1, k2, _, σ1, hst1, hst2⟩ |
              ⟨k1, k2, _, σ1, hst1, hst2⟩
            · subst hEq; cases hv
            · rcases ihC.2 (.lit (.bool true)) σ1 (.lit _) (stepsN_to_steps hst1) with ⟨hσ1, hevC⟩
              subst hσ1
              have hMT : StateMatches M L (withPath st1 (.isTrue svc)) ρ σ1 :=
                hMatch.of_eq hwfT hl1 hv1 hc1 (by simpa [withPath] using vcgenPure_cellTys_eq h1)
                  ⟨by simp only [hp1]; exact hMatch.path_holds, evalSVal_lit_iff_id.mp hevC⟩
              rcases (vcgenPure_sound (Δ := Δ) (Φ := Φ) hM hMT hT hObsT).2 v σ' hv (stepsN_to_steps hst2) with ⟨rfl, hevT⟩
              exact ⟨rfl, by simp [evalSVal, hevC, hevT]⟩
            · rcases ihC.2 (.lit (.bool false)) σ1 (.lit _) (stepsN_to_steps hst1) with ⟨hσ1, hevC⟩
              subst hσ1
              have hME : StateMatches M L { st1 with path := .and st1.path (.isFalse svc), obs := stT.obs } ρ σ1 :=
                hMatch.of_eq hwfE hl1 hv1 hc1 (by simpa using vcgenPure_cellTys_eq h1)
                  ⟨by simp only [hp1]; exact hMatch.path_holds, evalSVal_lit_iff_id.mp hevC⟩
              rcases (vcgenPure_sound (Δ := Δ) (Φ := Φ) hM hME hE hObs).2 v σ' hv (stepsN_to_steps hst2) with ⟨rfl, hevE⟩
              exact ⟨rfl, by simp [evalSVal, hevC, hevE]⟩
  | cellGet e1 =>
    simp only [vcgenPure] at hvc
    cases h1 : vcgenPure st e1 with
    | none => simp [h1] at hvc
    | some r1 =>
      rcases r1 with ⟨st1, sv1⟩; simp only [h1] at hvc
      rcases vcgenPure_wf hMatch.wf h1 with ⟨_, _, _, hc1, _, _, _⟩
      cases sv1 with
      | loc l =>
        simp only at hvc
        cases hlu : locLookup st1.cells l with
        | none => simp [hlu] at hvc
        | some sv =>
          simp [hlu] at hvc; rcases hvc with ⟨rfl, rfl⟩
          rw [hc1] at hlu
          rcases hMatch.cells_match l sv hlu with ⟨v0, hget, hev, _⟩
          have hv0 : IsValue v0 := (evalSVal_closed hM hev).1
          have ih1 := vcgenPure_sound (Δ := Δ) (Φ := Φ) hM hMatch h1 hObs
          rw [substMany_cellGet]
          constructor
          · intro k _ σ' hs
            rcases stepsN_cellGet_terminal (Or.inr ⟨_, rfl⟩) hs with
              ⟨k1, _, tr, hst1, hEq⟩ | ⟨k1, _, l', σ1, v', hst1, hget', hrest⟩
            · cases hEq; exact ih1.1 σ' (stepsN_to_steps hst1)
            · rcases ih1.2 (.loc l') σ1 (.loc l') (stepsN_to_steps hst1) with ⟨hσ1, hev1⟩
              subst hσ1
              simp [evalSVal] at hev1; subst hev1
              rw [hget] at hget'; cases hget'
              rcases stepsN_of_value hv0 hrest with ⟨_, hEq, _⟩; subst hEq; cases hv0
          · intro k _ v σ' hv hs
            rcases stepsN_cellGet_terminal (Or.inl hv) hs with
              ⟨_, _, _, _, hEq⟩ | ⟨k1, _, l', σ1, v', hst1, hget', hrest⟩
            · subst hEq; cases hv
            · rcases ih1.2 (.loc l') σ1 (.loc l') (stepsN_to_steps hst1) with ⟨hσ1, hev1⟩
              subst hσ1
              simp [evalSVal] at hev1; subst hev1
              rw [hget] at hget'; cases hget'
              rcases stepsN_of_value hv0 hrest with ⟨_, rfl, rfl⟩
              exact ⟨rfl, hev⟩
      | _ => simp at hvc
  | getTag e1 =>
    simp only [vcgenPure] at hvc
    cases h1 : vcgenPure st e1 with
    | none => simp [h1] at hvc
    | some r1 =>
      rcases r1 with ⟨st1, sv1⟩; simp [h1] at hvc; rcases hvc with ⟨rfl, rfl⟩
      have ih1 := vcgenPure_sound (Δ := Δ) (Φ := Φ) hM hMatch h1 hObs
      rw [substMany_getTag]
      constructor
      · intro k _ σ' hs
        rcases stepsN_getTag_terminal (Or.inr ⟨_, rfl⟩) hs with ⟨k1, _, tr, hst1, hEq⟩ | ⟨_, _, _, _, _, _, _, hEq⟩
        · cases hEq; exact ih1.1 σ' (stepsN_to_steps hst1)
        · cases hEq
      · intro k _ v σ' hv hs
        rcases stepsN_getTag_terminal (Or.inl hv) hs with ⟨_, _, _, _, hEq⟩ | ⟨k1, _, adt, tag, vs, hvs, hst1, rfl⟩
        · subst hEq; cases hv
        · rcases ih1.2 (.makeData adt tag vs) σ' (.makeData _ _ hvs) (stepsN_to_steps hst1) with ⟨rfl, hev1⟩
          exact ⟨rfl, by simp [evalSVal, hev1]⟩
  | _ => simp [vcgenPure] at hvc
termination_by sizeOf e

/-- Helper: `havocCells` properties (freshness, `SymWf`, cell lookup). -/
theorem havocCells_props (st : SymState) (locs : List Loc)
    (hlocs : ∀ l ∈ locs, l < st.nextLoc) (hwf : SymWf st) :
    st.nextSym ≤ (havocCells st locs).nextSym ∧
    (havocCells st locs).nextLoc = st.nextLoc ∧
    (havocCells st locs).vars = st.vars ∧
    (havocCells st locs).cellTys = st.cellTys ∧
    (havocCells st locs).obs = st.obs ∧
    SymWf (havocCells st locs) ∧
    (∀ l, l ∈ locs → ∃ id, st.nextSym ≤ id ∧ id < (havocCells st locs).nextSym ∧
      locLookup (havocCells st locs).cells l = some (.sym id)) ∧
    (∀ l, l ∉ locs → locLookup (havocCells st locs).cells l = locLookup st.cells l) := by
  induction locs generalizing st with
  | nil =>
    refine ⟨Nat.le_refl _, rfl, rfl, rfl, rfl, hwf, ?_, ?_⟩
    · intro l hl; cases hl
    · intro _ _; rfl
  | cons l0 rest ih =>
    have hl0 : l0 < st.nextLoc := hlocs l0 (List.mem_cons_self ..)
    have hrest : ∀ l ∈ rest, l < st.nextLoc := fun l hl => hlocs l (List.mem_cons_of_mem _ hl)
    let p1 := match locLookup st.cellTys l0 with
      | some ty => SForm.and st.path (.hasTy (.sym st.nextSym) ty)
      | none => st.path
    let st1 : SymState := { st with nextSym := st.nextSym + 1, cells := (l0, .sym st.nextSym) :: st.cells, path := p1 }
    have hpb1 : sformBound (st.nextSym + 1) p1 := by
      dsimp only [p1]
      cases locLookup st.cellTys l0 with
      | none => exact sformBound_mono (Nat.le_succ _) hwf.path_bound
      | some ty => exact ⟨sformBound_mono (Nat.le_succ _) hwf.path_bound, Nat.lt_succ_self _⟩
    have hwf1 : SymWf st1 := {
      vars_bound := fun p hp => svalBound_mono (Nat.le_succ _) (hwf.vars_bound p hp)
      cells_bound := fun p hp => by
        rcases List.mem_cons.mp hp with rfl | hp'
        · exact ⟨hl0, Nat.lt_succ_self _⟩
        · have hb := hwf.cells_bound p hp'
          exact ⟨hb.1, svalBound_mono (Nat.le_succ _) hb.2⟩
      path_bound := hpb1
    }
    have hEqHav : havocCells st (l0 :: rest) = havocCells st1 rest := rfl
    rw [hEqHav]
    rcases ih st1 hrest hwf1 with ⟨hle, hloc, hvars, hctys, hobs, hwf', hin, hout⟩
    refine ⟨Nat.le_trans (Nat.le_succ _) hle, hloc, hvars, hctys, hobs, hwf', ?_, ?_⟩
    · intro l hl
      rcases List.mem_cons.mp hl with rfl | hl'
      · by_cases hm : l ∈ rest
        · rcases hin l hm with ⟨id, hge, hlt, hlu⟩
          exact ⟨id, Nat.le_trans (Nat.le_succ _) hge, hlt, hlu⟩
        · refine ⟨st.nextSym, Nat.le_refl _, Nat.lt_of_lt_of_le (Nat.lt_succ_self _) hle, ?_⟩
          rw [hout l hm]; simp [st1, locLookup]
      · rcases hin l hl' with ⟨id, hge, hlt, hlu⟩
        exact ⟨id, Nat.le_trans (Nat.le_succ _) hge, hlt, hlu⟩
    · intro l hl
      have hne : l ≠ l0 := fun h => hl (h ▸ List.mem_cons_self ..)
      have hnr : l ∉ rest := fun h => hl (List.mem_cons_of_mem _ h)
      rw [hout l hnr]; simp [st1, locLookup, beq_false_of_ne (Ne.symm hne)]

/-- Pointwise binary relation on two equal-length lists (zero-dependency replacement for `PairwiseRel`). -/
inductive PairwiseRel {α β : Type} (R : α → β → Prop) : List α → List β → Prop
  | nil : PairwiseRel R [] []
  | cons {a : α} {b : β} {as : List α} {bs : List β} :
      R a b → PairwiseRel R as bs → PairwiseRel R (a :: as) (b :: bs)

theorem PairwiseRel.length_eq {α β : Type} {R : α → β → Prop} {as : List α} {bs : List β}
    (h : PairwiseRel R as bs) : as.length = bs.length := by
  induction h with
  | nil => rfl
  | cons _ _ ih => simp [ih]

theorem checkCallArgTys_props {st st' : SymState} {ps : List (Ident × Ty)} {svs : List SVal}
    (h : checkCallArgTys st ps svs = some st') :
    st'.nextSym = st.nextSym ∧
    st'.nextLoc = st.nextLoc ∧
    st'.vars = st.vars ∧
    st'.cells = st.cells ∧
    st'.cellTys = st.cellTys ∧
    st'.path = st.path ∧
    (∀ f ∈ st.obs, f ∈ st'.obs) ∧
    (∀ (M : Model), ValidModel M → ValidObs st'.obs → evalSForm M st.path →
      PairwiseRel (fun (p : Ident × Ty) sv =>
        match p.2 with
        | .cell elemTy => ∃ l, sv = .loc l ∧ (∀ ty, locLookup st.cellTys l = some ty → ty = elemTy)
        | ty => isModeledScalarTy ty = true ∧ evalSForm M (.hasTy sv ty)) ps svs) := by
  induction ps generalizing st svs with
  | nil =>
    cases svs with
    | nil => simp [checkCallArgTys] at h; subst h; exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, fun _ hf => hf, fun _ _ _ _ => .nil⟩
    | cons _ _ => simp [checkCallArgTys] at h
  | cons p ps ih =>
    cases svs with
    | nil => simp [checkCallArgTys] at h
    | cons sv svs =>
      rcases p with ⟨pn, pty⟩
      cases pty with
      | cell elemTy =>
        cases sv with
        | loc l =>
          simp only [checkCallArgTys] at h
          cases hct : locLookup st.cellTys l with
          | none =>
            simp [hct] at h
            rcases ih h with ⟨hs, hl, hv, hc, hct', hp, ho, hfa⟩
            exact ⟨hs, hl, hv, hc, hct', hp, ho,
              fun M hM hObs hP => .cons ⟨l, rfl, fun _ hlu => by rw [hct] at hlu; cases hlu⟩ (hfa M hM hObs hP)⟩
          | some ty =>
            simp [hct] at h
            cases htyEq : scalarTyEq ty elemTy with
            | false => simp [htyEq] at h
            | true =>
              simp [htyEq] at h
              have hty : ty = elemTy := scalarTyEq_true htyEq
              subst hty
              rcases ih h with ⟨hs, hl, hv, hc, hct', hp, ho, hfa⟩
              exact ⟨hs, hl, hv, hc, hct', hp, ho,
                fun M hM hObs hP => .cons ⟨l, rfl, fun _ hlu => by rw [hct] at hlu; cases hlu; rfl⟩ (hfa M hM hObs hP)⟩
        | _ => simp [checkCallArgTys, isModeledScalarTy] at h
      | _ =>
        simp only [checkCallArgTys] at h
        split at h
        · rename_i hsc
          rcases ih h with ⟨hs, hl, hv, hc, hct', hp, ho, hfa⟩
          refine ⟨hs, hl, hv, hc, hct', hp, fun f hf => ho f (List.mem_cons_of_mem _ hf), ?_⟩
          intro M hM hObs hP
          have hTy : evalSForm M (.hasTy sv _) :=
            hObs _ (ho _ (List.mem_cons_self ..)) M hM hP
          exact .cons ⟨hsc, hTy⟩ (hfa M hM hObs hP)
        · cases h

/-- Helper: given a concrete store `σ'` agreeing with `σ` on all tracked cells outside `locs`
    (with `∀ k < st.nextLoc, L k < σ'.length`, closed values, and preserved `cellTys`),
    we can extend `M` at the fresh symbols allocated by `havocCells st locs` so
    `StateMatches M' L (havocCells st locs) ρ σ'`. -/
theorem havocCells_extend_model {M : Model} {L : Loc → Loc} {st : SymState} {ρ : List (Ident × Expr)}
    {σ σ' : Store} (locs : List Loc)
    (hM : ValidModel M) (hMatch : StateMatches M L st ρ σ)
    (hlocs : ∀ l ∈ locs, l < st.nextLoc)
    (hbound' : ∀ k < st.nextLoc, L k < σ'.length)
    (hclosed' : ∀ (l : Loc) v, σ'[l]? = some v → IsValue v ∧ freeVars v = [])
    (htys' : ∀ l ty, locLookup st.cellTys l = some ty → l < st.nextLoc ∧ ∃ v, σ'[L l]? = some v ∧ valHasTy v ty)
    (hframe : ∀ (l : Loc) sv, locLookup st.cells l = some sv → l ∉ locs → σ'[L l]? = σ[L l]?) :
    ∃ M', ValidModel M' ∧
      (∀ id < st.nextSym, M' id = M id) ∧
      StateMatches M' L (havocCells st locs) ρ σ' := by
  induction locs generalizing st M σ with
  | nil =>
    refine ⟨M, hM, fun _ _ => rfl, ?_⟩
    exact {
      closed_env := hMatch.closed_env, wf := hMatch.wf,
      loc_bound := hbound', loc_inj := hMatch.loc_inj,
      path_holds := hMatch.path_holds, vars_match := hMatch.vars_match,
      cells_match := fun l sv hlu => by
        rw [hframe l sv hlu (by simp)]; exact hMatch.cells_match l sv hlu,
      cells_ty := htys'
    }
  | cons l0 rest ih =>
    have hl0 : l0 < st.nextLoc := hlocs l0 (List.mem_cons_self ..)
    have hrest : ∀ l ∈ rest, l < st.nextLoc := fun l hl => hlocs l (List.mem_cons_of_mem _ hl)
    have hl0_lt : L l0 < σ'.length := hbound' l0 hl0
    have hget0 : ∃ v0, σ'[L l0]? = some v0 := ⟨σ'[L l0], by simp [hl0_lt]⟩
    rcases hget0 with ⟨v0, hv0get⟩
    rcases hclosed' (L l0) v0 hv0get with ⟨hv0val, hv0cl⟩
    let M1 := updateModel M st.nextSym v0
    have hM1 : ValidModel M1 := validModel_update hM hv0val hv0cl
    let p1 := match locLookup st.cellTys l0 with
      | some ty => SForm.and st.path (.hasTy (.sym st.nextSym) ty)
      | none => st.path
    let st1 : SymState := { st with nextSym := st.nextSym + 1, cells := (l0, .sym st.nextSym) :: st.cells, path := p1 }
    have hpb1 : sformBound (st.nextSym + 1) p1 := by
      dsimp only [p1]
      cases locLookup st.cellTys l0 with
      | none => exact sformBound_mono (Nat.le_succ _) hMatch.wf.path_bound
      | some ty => exact ⟨sformBound_mono (Nat.le_succ _) hMatch.wf.path_bound, Nat.lt_succ_self _⟩
    have hwf1 : SymWf st1 := {
      vars_bound := fun p hp => svalBound_mono (Nat.le_succ _) (hMatch.wf.vars_bound p hp)
      cells_bound := fun p hp => by
        rcases List.mem_cons.mp hp with rfl | hp'
        · exact ⟨hl0, Nat.lt_succ_self _⟩
        · have hb := hMatch.wf.cells_bound p hp'
          exact ⟨hb.1, svalBound_mono (Nat.le_succ _) hb.2⟩
      path_bound := hpb1
    }
    have hpath1 : evalSForm M1 p1 := by
      dsimp only [p1]
      cases hct : locLookup st.cellTys l0 with
      | none => exact (evalSForm_updateModel_ge hMatch.wf.path_bound (Nat.le_refl _)).mpr hMatch.path_holds
      | some ty =>
        refine ⟨(evalSForm_updateModel_ge hMatch.wf.path_bound (Nat.le_refl _)).mpr hMatch.path_holds, ?_⟩
        rcases (htys' l0 ty hct).2 with ⟨vt, hgt, hvt⟩
        rw [hv0get] at hgt; cases hgt
        exact ⟨v0, by simp [evalSVal, M1, updateModel], hvt⟩
    let σ1 := σ.set (L l0) v0
    have hbound1 : ∀ k < st1.nextLoc, L k < σ1.length := fun k hk => by simp [σ1, st1]; exact hMatch.loc_bound k hk
    have hMatch1 : StateMatches M1 L st1 ρ σ1 := {
      closed_env := hMatch.closed_env
      wf := hwf1
      loc_bound := hbound1
      loc_inj := hMatch.loc_inj
      path_holds := hpath1
      vars_match := fun x sv hlu => by
        rcases hMatch.vars_match x sv hlu with ⟨v, hρx, hev, hlb⟩
        have hb := hMatch.wf.vars_bound _ (assocLookup_mem hlu)
        exact ⟨v, hρx, by rw [evalSVal_updateModel_ge hb (Nat.le_refl _)]; exact hev, hlb⟩
      cells_match := fun l sv hlu => by
        simp only [st1, locLookup] at hlu
        by_cases hll0 : (l0 == l) = true
        · have heq : l0 = l := eq_of_beq hll0
          subst heq; simp at hlu; subst hlu
          have hl0σ : L l0 < σ.length := hMatch.loc_bound l0 hl0
          refine ⟨v0, by simp [σ1, hl0σ], by simp [evalSVal, M1, updateModel], trivial⟩
        · simp [hll0] at hlu
          have hne : l ≠ l0 := fun h => by subst h; simp at hll0
          have hl_lt : l < st.nextLoc := (hMatch.wf.cells_bound _ (locLookup_mem hlu)).1
          have hLne : L l ≠ L l0 := fun hL => hne (hMatch.loc_inj l l0 hl_lt hl0 hL)
          rcases hMatch.cells_match l sv hlu with ⟨v, hσl, hev, hlb⟩
          have hb := (hMatch.wf.cells_bound _ (locLookup_mem hlu)).2
          refine ⟨v, ?_, ?_, hlb⟩
          · simp [σ1, List.getElem?_set_ne (Ne.symm hLne), hσl]
          · rw [evalSVal_updateModel_ge hb (Nat.le_refl _)]; exact hev
      cells_ty := fun l ty hlu => by
        refine ⟨(htys' l ty hlu).1, ?_⟩
        by_cases hEq : l = l0
        · subst hEq
          have hl0σ : L l < σ.length := hMatch.loc_bound l hl0
          rcases (htys' l ty hlu).2 with ⟨vt, hgt, hvt⟩
          rw [hv0get] at hgt; cases hgt
          exact ⟨v0, by simp [σ1, hl0σ], hvt⟩
        · by_cases hL : L l = L l0
          · rcases (htys' l ty hlu).2 with ⟨vt, hgt, hvt⟩
            rw [hL, hv0get] at hgt; cases hgt
            have hl0σ : L l0 < σ.length := hMatch.loc_bound l0 hl0
            exact ⟨v0, by simp [σ1, hL, hl0σ], hvt⟩
          · rcases (hMatch.cells_ty l ty hlu).2 with ⟨v, hσl, hvt⟩
            exact ⟨v, by simp [σ1, List.getElem?_set_ne (Ne.symm hL), hσl], hvt⟩
    }
    have hframe1 : ∀ l sv, locLookup st1.cells l = some sv → l ∉ rest → σ'[L l]? = σ1[L l]? := by
      intro l sv hlu hnr
      by_cases hEq : l = l0
      · subst hEq
        have hl0σ : L l < σ.length := hMatch.loc_bound l hl0
        rw [hv0get]
        simp [σ1, List.getElem?_set_self hl0σ]
      · simp only [st1, locLookup, beq_false_of_ne (Ne.symm hEq)] at hlu
        have hl_lt : l < st.nextLoc := (hMatch.wf.cells_bound _ (locLookup_mem hlu)).1
        have hLne : L l ≠ L l0 := fun hL => hEq (hMatch.loc_inj l l0 hl_lt hl0 hL)
        have hnot : l ∉ l0 :: rest := by simp [hEq, hnr]
        rw [hframe l sv hlu hnot]
        simp [σ1, List.getElem?_set_ne (Ne.symm hLne)]
    rcases ih hM1 hMatch1 hrest hbound' htys' hframe1 with ⟨M', hM', hagree, hMatch'⟩
    refine ⟨M', hM', ?_, hMatch'⟩
    intro id hid
    rw [hagree id (Nat.lt_succ_of_lt hid)]
    have hne : (id == st.nextSym) = false := beq_false_of_ne (by omega)
    simp [M1, updateModel, hne]

/-- Soundness invariant for a callee function table `Φ` with respect to `env.contracts`
    at step bound `bound` (Assume-Guarantee modular verification). -/
def CalleeSound (Δ : AdtEnv) (Φ : FunEnv) (env : VcgEnv) (bound : Nat) : Prop :=
  ∀ (name : Ident) (fc : FnContract) (fd : FunDef) (vs : List Expr) (σ : Store),
    env.contracts name = some fc →
    Φ name = some fd →
    vs.length = fc.params.length →
    (∀ v ∈ vs, IsValue v ∧ freeVars v = []) →
    (∀ (l : Loc) v, σ[l]? = some v → IsValue v ∧ freeVars v = []) →
    noDupLocs (collectConcreteLocs vs) = true →
    Steps Δ Φ (substMany (zipParams fc.params vs) fc.req) σ (.lit (.bool true)) σ →
    SafeExecN Δ Φ bound (substMany (zipParams fd.params vs) fd.body) σ
      (fun v σ' =>
        freeVars v = [] ∧
        valHasTy v fc.retTy ∧
        σ.length ≤ σ'.length ∧
        (∀ (l : Loc) w, σ'[l]? = some w → IsValue w ∧ freeVars w = []) ∧
        (∀ (l : Loc), l < σ.length → l ∉ collectConcreteLocs vs → σ'[l]? = σ[l]?) ∧
        (∀ (p : Ident × Ty) (vArg : Expr), (p, vArg) ∈ fc.params.zip vs →
          ∀ elemTy l, p.2 = .cell elemTy → vArg = .loc l →
            ∃ w, σ'[l]? = some w ∧ valHasTy w elemTy) ∧
        Steps Δ Φ (substMany ((fc.retVar, v) :: zipParams fc.params vs) fc.ens) σ' (.lit (.bool true)) σ')

/- Well-formedness and obligation monotonicity for `vcgen` (straight-line, control-flow,
   cells, loops, and modular calls). -/
theorem checkLoopPreDec_props {st0 st1 : SymState} {decOpt : Option Expr}
    {svOpt : Option (Ty × SVal)}
    (hwf : SymWf st0) (h : checkLoopPreDec st0 decOpt = some (st1, svOpt)) :
    st1.nextSym = st0.nextSym ∧ st1.nextLoc = st0.nextLoc ∧ st1.vars = st0.vars ∧
    st1.cells = st0.cells ∧ st1.cellTys = st0.cellTys ∧ st1.path = st0.path ∧
    (∀ f ∈ st0.obs, f ∈ st1.obs) ∧ SymWf st1 := by
  cases decOpt with
  | none =>
    simp [checkLoopPreDec] at h; rcases h with ⟨rfl, _⟩
    exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, fun _ hf => hf, hwf⟩
  | some decE =>
    simp only [checkLoopPreDec] at h
    cases hd : vcgenPure st0 decE with
    | none => simp [hd] at h
    | some rd =>
      rcases rd with ⟨stD0, svD0⟩; simp only [hd] at h
      cases hty : inferSValTy stD0 svD0 with
      | none => simp [hty] at h
      | some decTy =>
        simp only [hty] at h
        cases hops : decOpsForTy decTy with
        | none => simp [hops] at h
        | some rops =>
          rcases rops with ⟨geOp, ltOp, zeroLit⟩
          simp [hops] at h; rcases h with ⟨rfl, _⟩
          rcases vcgenPure_wf hwf hd with ⟨hs, hl, hv, hc, hp, ho, _⟩
          have hct := vcgenPure_cellTys_eq hd
          refine ⟨hs, hl, hv, hc, hct, hp, fun f hf => List.mem_cons_of_mem _ (ho f hf), ?_⟩
          exact ⟨by simp only [emitOb, hs, hv]; exact hwf.vars_bound,
            by simp only [emitOb, hs, hl, hc]; exact hwf.cells_bound,
            by simp only [emitOb, hs, hp]; exact hwf.path_bound⟩

theorem checkLoopPostDec_props {st0 st1 : SymState} {decOpt : Option Expr}
    {svOpt : Option (Ty × SVal)}
    (hwf : SymWf st0) (h : checkLoopPostDec st0 decOpt svOpt = some st1) :
    st1.nextSym = st0.nextSym ∧ st1.nextLoc = st0.nextLoc ∧ st1.vars = st0.vars ∧
    st1.cells = st0.cells ∧ st1.cellTys = st0.cellTys ∧ st1.path = st0.path ∧
    (∀ f ∈ st0.obs, f ∈ st1.obs) ∧ SymWf st1 := by
  cases decOpt <;> cases svOpt <;> simp only [checkLoopPostDec] at h
  · cases h; exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, fun _ hf => hf, hwf⟩
  · cases h; exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, fun _ hf => hf, hwf⟩
  · cases h; exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, fun _ hf => hf, hwf⟩
  · rename_i decE p; rcases p with ⟨decTy, svD0⟩
    cases hd : vcgenPure st0 decE with
    | none => simp [hd] at h
    | some rd =>
      rcases rd with ⟨stD1, svD1⟩; simp only [hd] at h
      cases hty : inferSValTy stD1 svD1 with
      | none => simp [hty] at h
      | some decTy1 =>
        cases hops : decOpsForTy decTy with
        | none => simp [hty, hops] at h
        | some rops =>
          rcases rops with ⟨geOp, ltOp, zeroLit⟩
          simp only [hty, hops] at h
          split at h
          · cases h
            rcases vcgenPure_wf hwf hd with ⟨hs, hl, hv, hc, hp, ho, _⟩
            have hct := vcgenPure_cellTys_eq hd
            refine ⟨hs, hl, hv, hc, hct, hp, fun f hf => List.mem_cons_of_mem _ (ho f hf), ?_⟩
            exact ⟨by simp only [emitOb, hs, hv]; exact hwf.vars_bound,
              by simp only [emitOb, hs, hl, hc]; exact hwf.cells_bound,
              by simp only [emitOb, hs, hp]; exact hwf.path_bound⟩
          · cases h

theorem checkCallDecreases_props {env : VcgEnv} {nm : Ident} {fc : FnContract}
    {st0 st1 : SymState}
    (hwf : SymWf st0) (h : checkCallDecreases env nm fc st0 = some st1) :
    st1.nextSym = st0.nextSym ∧ st1.nextLoc = st0.nextLoc ∧ st1.vars = st0.vars ∧
    st1.cells = st0.cells ∧ st1.cellTys = st0.cellTys ∧ st1.path = st0.path ∧
    (∀ f ∈ st0.obs, f ∈ st1.obs) ∧ SymWf st1 := by
  unfold checkCallDecreases at h
  cases hcur : env.curDec with
  | none =>
    simp [hcur] at h; subst h
    exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, fun _ hf => hf, hwf⟩
  | some p =>
    rcases p with ⟨curTy, curSv⟩; simp only [hcur] at h
    split at h
    · cases hdec : fc.dec with
      | none => simp [hdec] at h
      | some calleeDecE =>
        simp only [hdec] at h
        cases hd : vcgenPure st0 calleeDecE with
        | none => simp [hd] at h
        | some rd =>
          rcases rd with ⟨stDec, nextSv⟩; simp only [hd] at h
          cases hty : inferSValTy stDec nextSv with
          | none => simp [hty] at h
          | some nextTy =>
            cases hops : decOpsForTy curTy with
            | none => simp [hty, hops] at h
            | some rops =>
              rcases rops with ⟨geOp, ltOp, zeroLit⟩
              simp only [hty, hops] at h
              split at h
              · cases h
                rcases vcgenPure_wf hwf hd with ⟨hs, hl, hv, hc, hp, ho, _⟩
                have hct := vcgenPure_cellTys_eq hd
                refine ⟨hs, hl, hv, hc, hct, hp, fun f hf => List.mem_cons_of_mem _ (ho f hf), ?_⟩
                exact ⟨by simp only [emitOb, hs, hv]; exact hwf.vars_bound,
                  by simp only [emitOb, hs, hl, hc]; exact hwf.cells_bound,
                  by simp only [emitOb, hs, hp]; exact hwf.path_bound⟩
              · cases h
    · cases h; exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, fun _ hf => hf, hwf⟩

mutual
theorem vcgen_wf {env : VcgEnv} {st st' : SymState} {e : Expr} {sv : SVal}
    (hwf : SymWf st) (hvc : vcgen env st e = some (st', sv)) :
    st.nextSym ≤ st'.nextSym ∧
    st.nextLoc ≤ st'.nextLoc ∧
    st'.vars = st.vars ∧
    (∀ f ∈ st.obs, f ∈ st'.obs) ∧
    SymWf st' ∧
    svalBound st'.nextSym sv := by
  cases e with
  | lit l =>
    simp only [vcgen] at hvc; split at hvc
    · cases hvc; exact ⟨Nat.le_refl _, Nat.le_refl _, rfl, fun _ h => h, hwf, trivial⟩
    · cases hvc
  | var x =>
    simp only [vcgen] at hvc
    cases hlu : assocLookup st.vars x with
    | none => simp [hlu] at hvc
    | some sv0 =>
      simp [hlu] at hvc; rcases hvc with ⟨rfl, rfl⟩
      exact ⟨Nat.le_refl _, Nat.le_refl _, rfl, fun _ h => h, hwf, hwf.vars_bound _ (assocLookup_mem hlu)⟩
  | loc _ => simp [vcgen] at hvc
  | un op e1 =>
    simp only [vcgen] at hvc; split at hvc
    · cases hvc
    · cases h1 : vcgen env st e1 with
      | none => simp [h1] at hvc
      | some r1 =>
        rcases r1 with ⟨st1, sv1⟩; simp [h1] at hvc; rcases hvc with ⟨rfl, rfl⟩
        simpa [svalBound] using vcgen_wf hwf h1
  | bin op e1 e2 =>
    by_cases hAnd : op = .and
    · subst hAnd
      simp only [vcgen, ↓reduceIte] at hvc
      cases h1 : vcgen env st e1 with
      | none => simp [h1] at hvc
      | some r1 =>
        rcases r1 with ⟨st1, sv1⟩; simp only [h1] at hvc
        rcases vcgen_wf hwf h1 with ⟨hs1, hl1, hv1, ho1, hwf1, hb1⟩
        cases h2 : vcgen env (withPath st1 (.isTrue sv1)) e2 with
        | none => simp [h2] at hvc
        | some r2 =>
          rcases r2 with ⟨st2, sv2⟩; simp only [h2] at hvc
          split at hvc
          · cases hvc
          · cases hvc
            rcases vcgen_wf (symWf_withPath hwf1 (c := .isTrue sv1) hb1) h2 with ⟨hs2, _, _, ho2, hwf2, hb2⟩
            refine ⟨Nat.le_trans hs1 hs2, hl1, hv1, fun f hf => ho2 f (ho1 f hf), ?_, ⟨svalBound_mono hs2 hb1, hb2, trivial⟩⟩
            refine ⟨fun p hp => svalBound_mono hs2 (hwf1.vars_bound p hp), ?_, sformBound_mono hs2 hwf1.path_bound⟩
            intro p hp
            rcases List.mem_map.mp hp with ⟨⟨l, svB⟩, hmemB, rfl⟩
            have hbB := hwf1.cells_bound (l, svB) hmemB
            refine ⟨hbB.1, svalBound_mono hs2 hb1, ?_, ?_⟩
            · cases hluT : locLookup st2.cells l with
              | none => exact svalBound_mono hs2 hbB.2
              | some svT => exact (hwf2.cells_bound _ (locLookup_mem hluT)).2
            · cases hlu1 : locLookup st1.cells l with
              | none => exact svalBound_mono hs2 hbB.2
              | some sv1l => exact svalBound_mono hs2 (hwf1.cells_bound _ (locLookup_mem hlu1)).2
    · by_cases hOr : op = .or
      · subst hOr
        simp only [vcgen, reduceCtorEq, ↓reduceIte] at hvc
        cases h1 : vcgen env st e1 with
        | none => simp [h1] at hvc
        | some r1 =>
          rcases r1 with ⟨st1, sv1⟩; simp only [h1] at hvc
          rcases vcgen_wf hwf h1 with ⟨hs1, hl1, hv1, ho1, hwf1, hb1⟩
          cases h2 : vcgen env (withPath st1 (.isFalse sv1)) e2 with
          | none => simp [h2] at hvc
          | some r2 =>
            rcases r2 with ⟨st2, sv2⟩; simp only [h2] at hvc
            split at hvc
            · cases hvc
            · cases hvc
              rcases vcgen_wf (symWf_withPath hwf1 (c := .isFalse sv1) hb1) h2 with ⟨hs2, _, _, ho2, hwf2, hb2⟩
              refine ⟨Nat.le_trans hs1 hs2, hl1, hv1, fun f hf => ho2 f (ho1 f hf), ?_, ⟨svalBound_mono hs2 hb1, trivial, hb2⟩⟩
              refine ⟨fun p hp => svalBound_mono hs2 (hwf1.vars_bound p hp), ?_, sformBound_mono hs2 hwf1.path_bound⟩
              intro p hp
              rcases List.mem_map.mp hp with ⟨⟨l, svB⟩, hmemB, rfl⟩
              have hbB := hwf1.cells_bound (l, svB) hmemB
              refine ⟨hbB.1, svalBound_mono hs2 hb1, ?_, ?_⟩
              · cases hlu1 : locLookup st1.cells l with
                | none => exact svalBound_mono hs2 hbB.2
                | some sv1l => exact svalBound_mono hs2 (hwf1.cells_bound _ (locLookup_mem hlu1)).2
              · cases hluE : locLookup st2.cells l with
                | none => exact svalBound_mono hs2 hbB.2
                | some svE => exact (hwf2.cells_bound _ (locLookup_mem hluE)).2
      · simp only [vcgen, hAnd, hOr, ↓reduceIte] at hvc
        split at hvc
        · cases hvc
        · cases h1 : vcgen env st e1 with
          | none => simp [h1] at hvc
          | some r1 =>
            rcases r1 with ⟨st1, sv1⟩; simp only [h1] at hvc
            rcases vcgen_wf hwf h1 with ⟨hs1, hl1, hv1, ho1, hwf1, hb1⟩
            cases h2 : vcgen env st1 e2 with
            | none => simp [h2] at hvc
            | some r2 =>
              rcases r2 with ⟨st2, sv2⟩; simp only [h2] at hvc; cases hvc
              rcases vcgen_wf hwf1 h2 with ⟨hs2, hl2, hv2, ho2, hwf2, hb2⟩
              split
              · exact ⟨Nat.le_trans hs1 hs2, Nat.le_trans hl1 hl2, hv2.trans hv1,
                  fun f hf => List.mem_cons_of_mem _ (ho2 f (ho1 f hf)),
                  ⟨hwf2.vars_bound, hwf2.cells_bound, hwf2.path_bound⟩,
                  ⟨svalBound_mono hs2 hb1, hb2⟩⟩
              · exact ⟨Nat.le_trans hs1 hs2, Nat.le_trans hl1 hl2, hv2.trans hv1,
                  fun f hf => ho2 f (ho1 f hf), hwf2,
                  ⟨svalBound_mono hs2 hb1, hb2⟩⟩
  | let_ x e1 e2 =>
    simp only [vcgen] at hvc
    cases h1 : vcgen env st e1 with
    | none => simp [h1] at hvc
    | some r1 =>
      rcases r1 with ⟨st1, sv1⟩; simp only [h1] at hvc
      rcases vcgen_wf hwf h1 with ⟨hs1, hl1, hv1, ho1, hwf1, hb1⟩
      have hwfIn : SymWf { st1 with vars := (x, sv1) :: st1.vars } :=
        ⟨fun p hp => by
           rcases List.mem_cons.mp hp with rfl | hp'
           · exact hb1
           · exact hwf1.vars_bound p hp',
         hwf1.cells_bound, hwf1.path_bound⟩
      cases h2 : vcgen env { st1 with vars := (x, sv1) :: st1.vars } e2 with
      | none => simp [h2] at hvc
      | some r2 =>
        rcases r2 with ⟨st2, sv2⟩; simp [h2] at hvc; rcases hvc with ⟨rfl, rfl⟩
        rcases vcgen_wf hwfIn h2 with ⟨hs2, hl2, _, ho2, hwf2, hb2⟩
        refine ⟨Nat.le_trans hs1 hs2, Nat.le_trans hl1 hl2, hv1,
          fun f hf => ho2 f (ho1 f hf), ?_, hb2⟩
        exact ⟨fun p hp => svalBound_mono hs2 (hwf1.vars_bound p hp), hwf2.cells_bound, hwf2.path_bound⟩
  | block es =>
    simp only [vcgen] at hvc
    exact vcgenBlock_wf hwf hvc
  | if_ c t e =>
    simp only [vcgen] at hvc
    cases h1 : vcgen env st c with
    | none => simp [h1] at hvc
    | some r1 =>
      rcases r1 with ⟨st1, svc⟩; simp only [h1] at hvc
      rcases vcgen_wf hwf h1 with ⟨hs1, hl1, hv1, ho1, hwf1, hbc⟩
      cases hT : vcgen env (withPath st1 (.isTrue svc)) t with
      | none => simp [hT] at hvc
      | some rT =>
        rcases rT with ⟨stT, svT⟩; simp only [hT] at hvc
        rcases vcgen_wf (symWf_withPath hwf1 (c := .isTrue svc) hbc) hT with ⟨hsT, _, _, hoT, hwfT, hbT⟩
        have hwfEIn : SymWf ({ nextSym := stT.nextSym, nextLoc := st1.nextLoc, vars := st1.vars, cells := st1.cells, cellTys := st1.cellTys, path := .and st1.path (.isFalse svc), obs := stT.obs } : SymState) :=
          ⟨fun p hp => svalBound_mono hsT (hwf1.vars_bound p hp),
           fun p hp => ⟨(hwf1.cells_bound p hp).1, svalBound_mono hsT (hwf1.cells_bound p hp).2⟩,
           ⟨sformBound_mono hsT hwf1.path_bound, svalBound_mono hsT hbc⟩⟩
        cases hE : vcgen env ({ nextSym := stT.nextSym, nextLoc := st1.nextLoc, vars := st1.vars, cells := st1.cells, cellTys := st1.cellTys, path := .and st1.path (.isFalse svc), obs := stT.obs } : SymState) e with
        | none => simp [hE] at hvc
        | some rE =>
          rcases rE with ⟨stE, svE⟩; simp only [hE] at hvc
          split at hvc
          · cases hvc
          · cases hvc
            rcases vcgen_wf hwfEIn hE with ⟨hsE, _, _, hoE, hwfE, hbE⟩
            have hsTE : st1.nextSym ≤ stE.nextSym := Nat.le_trans hsT hsE
            refine ⟨Nat.le_trans hs1 hsTE, hl1, hv1, fun f hf => hoE f (hoT f (ho1 f hf)), ?_,
              ⟨svalBound_mono hsTE hbc, svalBound_mono hsE hbT, hbE⟩⟩
            refine ⟨fun p hp => svalBound_mono hsTE (hwf1.vars_bound p hp), ?_,
              sformBound_mono hsTE hwf1.path_bound⟩
            intro p hp
            rcases List.mem_map.mp hp with ⟨⟨l, svB⟩, hmemB, rfl⟩
            have hbB := hwf1.cells_bound (l, svB) hmemB
            refine ⟨hbB.1, svalBound_mono hsTE hbc, ?_, ?_⟩
            · cases hluT : locLookup stT.cells l with
              | none => exact svalBound_mono hsTE hbB.2
              | some svTl => exact svalBound_mono hsE (hwfT.cells_bound _ (locLookup_mem hluT)).2
            · cases hluE : locLookup stE.cells l with
              | none => exact svalBound_mono hsTE hbB.2
              | some svEl => exact (hwfE.cells_bound _ (locLookup_mem hluE)).2
  | cellNew e1 =>
    simp only [vcgen] at hvc
    cases h1 : vcgen env st e1 with
    | none => simp [h1] at hvc
    | some r1 =>
      rcases r1 with ⟨st1, sv1⟩; simp only [h1] at hvc
      cases hty : inferSValTy st1 sv1 with
      | none => simp [hty] at hvc
      | some elemTy =>
        simp only [hty] at hvc; split at hvc
        · cases hvc
        · rcases hvc with ⟨rfl, rfl⟩
          rcases vcgen_wf hwf h1 with ⟨hs1, hl1, hv1, ho1, hwf1, hb1⟩
          refine ⟨hs1, Nat.le_trans hl1 (Nat.le_succ _), hv1, fun f hf => List.mem_cons_of_mem _ (ho1 f hf), ?_, trivial⟩
          refine ⟨hwf1.vars_bound, ?_, hwf1.path_bound⟩
          intro p hp
          rcases List.mem_cons.mp hp with rfl | hp'
          · exact ⟨Nat.lt_succ_self _, hb1⟩
          · exact ⟨Nat.lt_succ_of_lt (hwf1.cells_bound p hp').1, (hwf1.cells_bound p hp').2⟩
  | cellGet e1 =>
    simp only [vcgen] at hvc
    cases h1 : vcgen env st e1 with
    | none => simp [h1] at hvc
    | some r1 =>
      rcases r1 with ⟨st1, sv1⟩; simp only [h1] at hvc
      rcases vcgen_wf hwf h1 with ⟨hs1, hl1, hv1, ho1, hwf1, _⟩
      cases sv1 with
      | loc l =>
        simp only at hvc
        cases hlu : locLookup st1.cells l with
        | none => simp [hlu] at hvc
        | some sv =>
          simp [hlu] at hvc; rcases hvc with ⟨rfl, rfl⟩
          exact ⟨hs1, hl1, hv1, ho1, hwf1, (hwf1.cells_bound _ (locLookup_mem hlu)).2⟩
      | _ => simp at hvc
  | cellSet e1 e2 =>
    simp only [vcgen] at hvc
    cases h1 : vcgen env st e1 with
    | none => simp [h1] at hvc
    | some r1 =>
      rcases r1 with ⟨st1, sv1⟩; simp only [h1] at hvc
      rcases vcgen_wf hwf h1 with ⟨hs1, hl1, hv1, ho1, hwf1, _⟩
      cases sv1 with
      | loc l =>
        simp only at hvc
        cases h2 : vcgen env st1 e2 with
        | none => simp [h2] at hvc
        | some r2 =>
          rcases r2 with ⟨st2, sv2⟩; simp only [h2] at hvc
          rcases vcgen_wf hwf1 h2 with ⟨hs2, hl2, hv2, ho2, hwf2, hb2⟩
          cases hlu : locLookup st2.cells l with
          | none => simp [hlu] at hvc
          | some _ =>
            simp only [hlu] at hvc
            have hlBound : l < st2.nextLoc := (hwf2.cells_bound _ (locLookup_mem hlu)).1
            cases hty : locLookup st2.cellTys l with
            | none =>
              simp [hty] at hvc; rcases hvc with ⟨rfl, rfl⟩
              refine ⟨Nat.le_trans hs1 hs2, Nat.le_trans hl1 hl2, hv2.trans hv1,
                fun f hf => ho2 f (ho1 f hf), ?_, trivial⟩
              refine ⟨hwf2.vars_bound, ?_, hwf2.path_bound⟩
              intro p hp
              rcases List.mem_cons.mp hp with rfl | hp'
              · exact ⟨hlBound, hb2⟩
              · exact hwf2.cells_bound p hp'
            | some ty =>
              simp [hty] at hvc; rcases hvc with ⟨rfl, rfl⟩
              refine ⟨Nat.le_trans hs1 hs2, Nat.le_trans hl1 hl2, hv2.trans hv1,
                fun f hf => List.mem_cons_of_mem _ (ho2 f (ho1 f hf)), ?_, trivial⟩
              refine ⟨hwf2.vars_bound, ?_, hwf2.path_bound⟩
              intro p hp
              rcases List.mem_cons.mp hp with rfl | hp'
              · exact ⟨hlBound, hb2⟩
              · exact hwf2.cells_bound p hp'
      | _ => simp at hvc
  | getTag e1 =>
    simp only [vcgen] at hvc
    cases h1 : vcgen env st e1 with
    | none => simp [h1] at hvc
    | some r1 =>
      rcases r1 with ⟨st1, sv1⟩; simp [h1] at hvc; rcases hvc with ⟨rfl, rfl⟩
      simpa [svalBound] using vcgen_wf hwf h1
  | while_ c b =>
    simp only [vcgen] at hvc
    cases hlc : env.loops c b with
    | none => simp [hlc] at hvc
    | some lc =>
      simp only [hlc] at hvc
      cases hI0 : vcgenPure st lc.inv with
      | none => simp [hI0] at hvc
      | some rI0 =>
        rcases rI0 with ⟨stI0, svI0⟩; simp only [hI0] at hvc
        rcases vcgenPure_wf hwf hI0 with ⟨hsI0, hlI0, hvI0, hcI0, hpI0, hoI0, _⟩
        have hwf1 : SymWf (emitOb stI0 (.isTrue svI0)) :=
          ⟨by simp only [emitOb, hsI0, hvI0]; exact hwf.vars_bound,
           by simp only [emitOb, hsI0, hlI0, hcI0]; exact hwf.cells_bound,
           by simp only [emitOb, hsI0, hpI0]; exact hwf.path_bound⟩
        have hlocs1 : ∀ l ∈ trackedLocs (emitOb stI0 (.isTrue svI0)), l < (emitOb stI0 (.isTrue svI0)).nextLoc := by
          intro l hl
          rcases List.mem_map.mp hl with ⟨p, hp, rfl⟩
          exact (hwf1.cells_bound p hp).1
        rcases havocCells_props (emitOb stI0 (.isTrue svI0)) (trackedLocs (emitOb stI0 (.isTrue svI0))) hlocs1 hwf1 with
          ⟨hsH, hlH, hvH, hpH, hoH, hwfH, _, _⟩
        cases hIH : vcgenPure (havocCells (emitOb stI0 (.isTrue svI0)) (trackedLocs (emitOb stI0 (.isTrue svI0)))) lc.inv with
        | none => simp [hIH] at hvc
        | some rIH =>
          rcases rIH with ⟨stIH, svIH⟩; simp only [hIH] at hvc
          rcases vcgenPure_wf hwfH hIH with ⟨hsIH, hlIH, hvIH, hcIH, hpIH, hoIH, hbIH⟩
          have hwfLE : SymWf (withPath stIH (.isTrue svIH)) :=
            ⟨by simp only [withPath, hsIH, hvIH]; exact hwfH.vars_bound,
             by simp only [withPath, hsIH, hlIH, hcIH]; exact hwfH.cells_bound,
             by simp only [withPath, sformBound, hsIH, hpIH]; exact ⟨hwfH.path_bound, hbIH⟩⟩
          cases hC : vcgen env (withPath stIH (.isTrue svIH)) c with
          | none => simp [hC] at hvc
          | some rC =>
            rcases rC with ⟨stC, svC⟩; simp only [hC] at hvc
            split at hvc
            · cases hvc
            · rcases vcgen_wf hwfLE hC with ⟨hsC, hlC, hvC, hoC, hwfC, hbC⟩
              have hwfB0 : SymWf (withPath stC (.isTrue svC)) := symWf_withPath hwfC (c := .isTrue svC) hbC
              cases hPre : checkLoopPreDec (withPath stC (.isTrue svC)) lc.dec with
              | none => simp [hPre] at hvc
              | some rPre =>
                rcases rPre with ⟨stBodyIn, svD0Opt⟩; simp only [hPre] at hvc
                rcases checkLoopPreDec_props hwfB0 hPre with ⟨hsPre, hlPre, _, _, _, _, hoPre, hwfBodyIn⟩
                cases hB : vcgen env stBodyIn b with
                | none => simp [hB] at hvc
                | some rB =>
                  rcases rB with ⟨stB, _⟩; simp only [hB] at hvc
                  split at hvc
                  · cases hvc
                  · rcases vcgen_wf hwfBodyIn hB with ⟨hsB, _, _, hoB, hwfB, _⟩
                    cases hPost : checkLoopPostDec stB lc.dec svD0Opt with
                    | none => simp [hPost] at hvc
                    | some stBDec =>
                      simp only [hPost] at hvc
                      rcases checkLoopPostDec_props hwfB hPost with ⟨hsPost, _, _, _, _, _, hoPost, hwfBDec⟩
                      cases hBI : vcgenPure stBDec lc.inv with
                      | none => simp [hBI] at hvc
                      | some rBI =>
                        rcases rBI with ⟨stBI, svBI⟩; simp [hBI] at hvc; rcases hvc with ⟨rfl, rfl⟩
                        rcases vcgenPure_wf hwfBDec hBI with ⟨hsBI, _, _, _, _, hoBI, _⟩
                        simp only [emitOb_nextSym, emitOb_nextLoc, withPath_nextSym, withPath_nextLoc] at hsH hlH hsC hlC hsB hsPre
                        have hsAll1 : st.nextSym ≤ stC.nextSym := by omega
                        have hsAll2 : stC.nextSym ≤ stBI.nextSym := by omega
                        have hlAll : st.nextLoc ≤ stC.nextLoc := by omega
                        refine ⟨Nat.le_trans hsAll1 hsAll2, hlAll, rfl, ?_, ?_, trivial⟩
                        · intro f hf
                          exact List.mem_cons_of_mem _ (hoBI f (hoPost f (hoB f (hoPre f (hoC f (hoIH f (by rw [hoH]; exact List.mem_cons_of_mem _ (hoI0 f hf))))))))
                        · refine ⟨fun p hp => svalBound_mono (Nat.le_trans hsAll1 hsAll2) (hwf.vars_bound p hp),
                            fun p hp => ⟨(hwfC.cells_bound p hp).1, svalBound_mono hsAll2 (hwfC.cells_bound p hp).2⟩,
                            ⟨sformBound_mono hsAll2 hwfC.path_bound, svalBound_mono hsAll2 hbC⟩⟩
  | applyDir name args =>
    unfold vcgen at hvc
    dsimp only at hvc
    cases hAssert : (name == "assert")
    · rw [hAssert] at hvc; simp only [Bool.false_eq_true, ↓reduceIte] at hvc
      cases hAssume : (name == "assume")
      · rw [hAssume] at hvc; simp only [Bool.false_eq_true, ↓reduceIte] at hvc
        cases hfc : env.contracts name with
        | none => simp [hfc] at hvc
        | some fc =>
          simp only [hfc] at hvc
          split at hvc
          · cases hvc
          · cases hArgs : vcgenList env st args with
            | none => simp [hArgs] at hvc
            | some rA =>
              rcases rA with ⟨stA, svArgs⟩; simp only [hArgs] at hvc
              rcases vcgenList_wf hwf hArgs with ⟨hsA, hlA, hvA, hoA, hwfA, hbArgs⟩
              split at hvc
              · cases hvc
              · cases hTyp : checkCallArgTys stA fc.params svArgs with
                | none => simp [hTyp] at hvc
                | some stTyped =>
                  simp only [hTyp] at hvc
                  rcases checkCallArgTys_props hTyp with ⟨hsT, hlT, hvT, hcT, hctT, hpT, hoT, _⟩
                  let paramBindings := (fc.params.map Prod.fst).zip svArgs
                  have hwfCall : SymWf { stTyped with vars := paramBindings } := by
                    refine ⟨?_, ?_, ?_⟩
                    · intro p hp
                      have hmem : p.2 ∈ svArgs := List.of_mem_zip hp |>.2
                      rw [hsT]; exact hbArgs p.2 hmem
                    · rw [hsT, hlT, hcT]; exact hwfA.cells_bound
                    · rw [hsT, hpT]; exact hwfA.path_bound
                  cases hReq : vcgenPure { stTyped with vars := (fc.params.map Prod.fst).zip svArgs } fc.req with
                  | none => simp [hReq] at hvc
                  | some rReq =>
                    rcases rReq with ⟨stReq, svReq⟩; simp only [hReq] at hvc
                    rcases vcgenPure_wf hwfCall hReq with ⟨hsReq, hlReq, hvReq, hcReq, hpReq, hoReq, _⟩
                    let stChecked0 := emitOb stReq (.isTrue svReq)
                    have hwfChecked0 : SymWf stChecked0 :=
                      ⟨by simp only [stChecked0, emitOb, hsReq, hvReq]; exact hwfCall.vars_bound,
                       by simp only [stChecked0, emitOb, hsReq, hlReq, hcReq]; exact hwfCall.cells_bound,
                       by simp only [stChecked0, emitOb, hsReq, hpReq]; exact hwfCall.path_bound⟩
                    cases hDec : checkCallDecreases env name fc (emitOb stReq (.isTrue svReq)) with
                    | none => simp [hDec] at hvc
                    | some stChecked =>
                      simp only [hDec] at hvc
                      rcases checkCallDecreases_props hwfChecked0 hDec with
                        ⟨hsDec, hlDec, hvDec, hcDec, hctDec, hpDec, hoDec, hwfChecked⟩
                      let locArgs := collectLocArgs svArgs
                      have hlocAll : ∀ l ∈ locArgs, l < stChecked.nextLoc := by
                        rename_i hcond
                        have hcond' : noDupLocs (collectLocArgs svArgs) = true ∧ (collectLocArgs svArgs).all (· < stA.nextLoc) = true := by
                          cases h1 : noDupLocs (collectLocArgs svArgs) <;>
                          cases h2 : (collectLocArgs svArgs).all (· < stA.nextLoc) <;>
                          simp_all
                        have hall := List.all_eq_true.mp hcond'.2
                        intro l hl
                        have := hall l hl
                        simp only [decide_eq_true_eq] at this
                        rw [hlDec]; simp only [stChecked0, emitOb_nextLoc, hlReq, hlT]; exact this
                      rcases havocCells_props stChecked locArgs hlocAll hwfChecked with
                        ⟨hsHav, hlHav, _, _, hoHav, hwfHav, _, _⟩
                      let stHav := havocCells stChecked locArgs
                      let retId := stHav.nextSym
                      have hwfRet : SymWf ({ stHav with
                          nextSym := retId + 1,
                          vars := (fc.retVar, .sym retId) :: (fc.params.map Prod.fst).zip svArgs,
                          path := .and stHav.path (.hasTy (.sym retId) fc.retTy) } : SymState) := by
                        refine ⟨?_, ?_, ⟨sformBound_mono (Nat.le_succ _) hwfHav.path_bound, Nat.lt_succ_self _⟩⟩
                        · intro p hp
                          rcases List.mem_cons.mp hp with rfl | hp'
                          · exact Nat.lt_succ_self _
                          · have hb := hwfCall.vars_bound p hp'
                            rw [hsDec] at hsHav; simp only [stChecked0, emitOb_nextSym, hsReq] at hsHav
                            exact svalBound_mono (Nat.le_trans hsHav (Nat.le_succ _)) hb
                        · intro p hp
                          exact ⟨(hwfHav.cells_bound p hp).1, svalBound_mono (Nat.le_succ _) (hwfHav.cells_bound p hp).2⟩
                      cases hEns : vcgenPure ({ havocCells stChecked (collectLocArgs svArgs) with
                          nextSym := (havocCells stChecked (collectLocArgs svArgs)).nextSym + 1,
                          vars := (fc.retVar, .sym (havocCells stChecked (collectLocArgs svArgs)).nextSym) :: (fc.params.map Prod.fst).zip svArgs,
                          path := .and (havocCells stChecked (collectLocArgs svArgs)).path (.hasTy (.sym (havocCells stChecked (collectLocArgs svArgs)).nextSym) fc.retTy) } : SymState) fc.ens with
                      | none => simp [hEns] at hvc
                      | some rEns =>
                        rcases rEns with ⟨stEns, svEns⟩; simp [hEns] at hvc; rcases hvc with ⟨rfl, rfl⟩
                        rcases vcgenPure_wf hwfRet hEns with ⟨hsEns, _, _, _, _, hoEns, hbEns⟩
                        have hSymLe : stA.nextSym ≤ stEns.nextSym := by
                          rw [hsDec] at hsHav; simp only [stChecked0, emitOb_nextSym, hsReq, hsT] at hsHav
                          exact Nat.le_trans hsHav (hsEns.symm ▸ Nat.le_succ _)
                        refine ⟨Nat.le_trans hsA hSymLe, hlA, hvA, ?_, ?_, ?_⟩
                        · intro f hf
                          exact hoEns f (by change f ∈ stHav.obs; rw [hoHav]; exact hoDec f (List.mem_cons_of_mem _ (hoReq f (hoT f (hoA f hf)))))
                        · refine ⟨fun p hp => svalBound_mono hSymLe (hwfA.vars_bound p hp), ?_, ?_⟩
                          · intro p hp
                            have hb := hwfHav.cells_bound p hp
                            have hlEq : stHav.nextLoc = stA.nextLoc := by
                              change (havocCells stChecked locArgs).nextLoc = stA.nextLoc
                              rw [hlHav, hlDec]; simp only [stChecked0, emitOb_nextLoc, hlReq, hlT]
                            exact ⟨hlEq ▸ hb.1, svalBound_mono (hsEns.symm ▸ Nat.le_succ _) hb.2⟩
                          · exact ⟨⟨sformBound_mono (hsEns.symm ▸ Nat.le_succ _) hwfHav.path_bound, by rw [hsEns]; exact Nat.lt_succ_self _⟩, by rw [hsEns]; exact hbEns⟩
                        · change retId < stEns.nextSym
                          rw [hsEns]; exact Nat.lt_succ_self _
      · simp only [hAssume, ↓reduceIte] at hvc
        cases args with
        | cons e1 rest =>
          cases rest with
          | nil =>
            cases h1 : vcgen env st e1 with
            | none => simp [h1] at hvc
            | some r1 =>
              rcases r1 with ⟨st1, sv1⟩; simp [h1] at hvc; rcases hvc with ⟨rfl, rfl⟩
              rcases vcgen_wf hwf h1 with ⟨hs1, hl1, hv1, ho1, hwf1, hb1⟩
              exact ⟨hs1, hl1, hv1, ho1, symWf_withPath hwf1 (c := .isTrue sv1) hb1, trivial⟩
          | cons _ _ => simp at hvc
        | nil => simp at hvc
    · simp only [hAssert, ↓reduceIte] at hvc
      cases args with
      | cons e1 rest =>
        cases rest with
        | nil =>
          cases h1 : vcgen env st e1 with
          | none => simp [h1] at hvc
          | some r1 =>
            rcases r1 with ⟨st1, sv1⟩; simp [h1] at hvc; rcases hvc with ⟨rfl, rfl⟩
            rcases vcgen_wf hwf h1 with ⟨hs1, hl1, hv1, ho1, hwf1, _⟩
            exact ⟨hs1, hl1, hv1, fun f hf => List.mem_cons_of_mem _ (ho1 f hf),
              ⟨hwf1.vars_bound, hwf1.cells_bound, hwf1.path_bound⟩, trivial⟩
        | cons _ _ => simp at hvc
      | nil => simp at hvc
  | _ => simp [vcgen] at hvc
termination_by sizeOf e

theorem vcgenBlock_wf {env : VcgEnv} {st st' : SymState} {es : List Expr} {sv : SVal}
    (hwf : SymWf st) (hvc : vcgenBlock env st es = some (st', sv)) :
    st.nextSym ≤ st'.nextSym ∧
    st.nextLoc ≤ st'.nextLoc ∧
    st'.vars = st.vars ∧
    (∀ f ∈ st.obs, f ∈ st'.obs) ∧
    SymWf st' ∧
    svalBound st'.nextSym sv := by
  cases es with
  | nil =>
    simp only [vcgenBlock] at hvc; cases hvc
    exact ⟨Nat.le_refl _, Nat.le_refl _, rfl, fun _ h => h, hwf, trivial⟩
  | cons e1 rest =>
    cases rest with
    | nil =>
      simp only [vcgenBlock] at hvc
      exact vcgen_wf hwf hvc
    | cons e2 rest' =>
      simp only [vcgenBlock] at hvc
      cases h1 : vcgen env st e1 with
      | none => simp [h1] at hvc
      | some r1 =>
        rcases r1 with ⟨st1, _⟩; simp only [h1] at hvc
        rcases vcgen_wf hwf h1 with ⟨hs1, hl1, hv1, ho1, hwf1, _⟩
        rcases vcgenBlock_wf hwf1 hvc with ⟨hs2, hl2, hv2, ho2, hwf2, hb2⟩
        exact ⟨Nat.le_trans hs1 hs2, Nat.le_trans hl1 hl2, hv2.trans hv1,
          fun f hf => ho2 f (ho1 f hf), hwf2, hb2⟩
termination_by sizeOf es

theorem vcgenList_wf {env : VcgEnv} {st st' : SymState} {es : List Expr} {svs : List SVal}
    (hwf : SymWf st) (hvc : vcgenList env st es = some (st', svs)) :
    st.nextSym ≤ st'.nextSym ∧
    st.nextLoc ≤ st'.nextLoc ∧
    st'.vars = st.vars ∧
    (∀ f ∈ st.obs, f ∈ st'.obs) ∧
    SymWf st' ∧
    (∀ sv ∈ svs, svalBound st'.nextSym sv) := by
  cases es with
  | nil =>
    simp only [vcgenList] at hvc; cases hvc
    exact ⟨Nat.le_refl _, Nat.le_refl _, rfl, fun _ h => h, hwf, fun _ h => by cases h⟩
  | cons e1 rest =>
    simp only [vcgenList] at hvc
    cases h1 : vcgen env st e1 with
    | none => simp [h1] at hvc
    | some r1 =>
      rcases r1 with ⟨st1, sv1⟩; simp only [h1] at hvc
      rcases vcgen_wf hwf h1 with ⟨hs1, hl1, hv1, ho1, hwf1, hb1⟩
      cases h2 : vcgenList env st1 rest with
      | none => simp [h2] at hvc
      | some r2 =>
        rcases r2 with ⟨st2, svs2⟩; simp [h2] at hvc; rcases hvc with ⟨rfl, rfl⟩
        rcases vcgenList_wf hwf1 h2 with ⟨hs2, hl2, hv2, ho2, hwf2, hb2⟩
        refine ⟨Nat.le_trans hs1 hs2, Nat.le_trans hl1 hl2, hv2.trans hv1,
          fun f hf => ho2 f (ho1 f hf), hwf2, ?_⟩
        intro sv hsv
        rcases List.mem_cons.mp hsv with rfl | hsv'
        · exact svalBound_mono hs2 hb1
        · exact hb2 sv hsv'
termination_by sizeOf es
end

/-- Store closedness: every stored value in `σ` is a closed value (`IsValue` and `freeVars = []`). -/
def StoreClosed (σ : Store) : Prop :=
  ∀ (l : Loc) v, σ[l]? = some v → IsValue v ∧ freeVars v = []

theorem storeClosed_append {σ : Store} {v : Expr} (hσ : StoreClosed σ)
    (hv : IsValue v) (hcl : freeVars v = []) : StoreClosed (σ ++ [v]) := by
  intro l w hget
  by_cases hlt : l < σ.length
  · rw [List.getElem?_append_left hlt] at hget
    exact hσ l w hget
  · rw [List.getElem?_append_right (Nat.le_of_not_lt hlt)] at hget
    cases h : l - σ.length with
    | zero => simp [h] at hget; subst hget; exact ⟨hv, hcl⟩
    | succ k => simp [h] at hget

theorem storeClosed_set {σ : Store} {l0 : Loc} {v : Expr} (hσ : StoreClosed σ)
    (hv : IsValue v) (hcl : freeVars v = []) : StoreClosed (σ.set l0 v) := by
  intro l w hget
  by_cases hEq : l = l0
  · subst hEq
    by_cases hlt : l < σ.length
    · rw [List.getElem?_set_self hlt] at hget; cases hget; exact ⟨hv, hcl⟩
    · rw [List.getElem?_eq_none (by simp; exact Nat.le_of_not_lt hlt)] at hget; cases hget
  · rw [List.getElem?_set_ne (Ne.symm hEq)] at hget
    exact hσ l w hget

/-! ### `Steps` Context Congruence Lemmas -/

theorem steps_un_congr {Δ : AdtEnv} {Φ : FunEnv} {op : UnOp} {e e' : Expr} {σ σ' : Store}
    (h : Steps Δ Φ e σ e' σ') : Steps Δ Φ (.un op e) σ (.un op e') σ' := by
  induction h with
  | refl => exact .refl _ _
  | trans hs _ ih => exact .trans (.unStep hs) ih

theorem steps_binLeft_congr {Δ : AdtEnv} {Φ : FunEnv} {op : BinOp} {e1 e1' e2 : Expr}
    {σ σ' : Store} (h : Steps Δ Φ e1 σ e1' σ') :
    Steps Δ Φ (.bin op e1 e2) σ (.bin op e1' e2) σ' := by
  induction h with
  | refl => exact .refl _ _
  | trans hs _ ih => exact .trans (.binLeft hs) ih

theorem steps_binRight_congr {Δ : AdtEnv} {Φ : FunEnv} {op : BinOp}
    (hNA : op ≠ .and) (hNO : op ≠ .or) {v1 e2 e2' : Expr} {σ σ' : Store}
    (hv1 : IsValue v1) (h : Steps Δ Φ e2 σ e2' σ') :
    Steps Δ Φ (.bin op v1 e2) σ (.bin op v1 e2') σ' := by
  induction h with
  | refl => exact .refl _ _
  | trans hs _ ih => exact .trans (.binRight hNA hNO hv1 hs) ih

theorem steps_if_congr {Δ : AdtEnv} {Φ : FunEnv} {c c' t e : Expr} {σ σ' : Store}
    (h : Steps Δ Φ c σ c' σ') : Steps Δ Φ (.if_ c t e) σ (.if_ c' t e) σ' := by
  induction h with
  | refl => exact .refl _ _
  | trans hs _ ih => exact .trans (.ifStep hs) ih

theorem steps_cellGet_congr {Δ : AdtEnv} {Φ : FunEnv} {e e' : Expr} {σ σ' : Store}
    (h : Steps Δ Φ e σ e' σ') : Steps Δ Φ (.cellGet e) σ (.cellGet e') σ' := by
  induction h with
  | refl => exact .refl _ _
  | trans hs _ ih => exact .trans (.cellGetStep hs) ih

theorem steps_getTag_congr {Δ : AdtEnv} {Φ : FunEnv} {e e' : Expr} {σ σ' : Store}
    (h : Steps Δ Φ e σ e' σ') : Steps Δ Φ (.getTag e) σ (.getTag e') σ' := by
  induction h with
  | refl => exact .refl _ _
  | trans hs _ ih => exact .trans (.getTagStep hs) ih

theorem steps_blockCons_congr {Δ : AdtEnv} {Φ : FunEnv} {e1 e1' e2 : Expr} {es : List Expr}
    {σ σ' : Store} (h : Steps Δ Φ e1 σ e1' σ') :
    Steps Δ Φ (.block (e1 :: e2 :: es)) σ (.block (e1' :: e2 :: es)) σ' := by
  induction h with
  | refl => exact .refl _ _
  | trans hs _ ih => exact .trans (.blockConsStep hs) ih

/-- Completeness of `vcgenPure`: if `evalSVal M sv = some v` in a matching state `(ρ, σ)`,
    then `substMany ρ e` evaluates via `Steps` to `v` without modifying `σ`. -/
theorem vcgenPure_complete {Δ : AdtEnv} {Φ : FunEnv} {M : Model} {L : Loc → Loc} {st st' : SymState}
    {ρ : List (Ident × Expr)} {σ : Store} {e : Expr} {sv : SVal} {v : Expr}
    (hM : ValidModel M) (hMatch : StateMatches M L st ρ σ)
    (hvc : vcgenPure st e = some (st', sv)) (hev : evalSVal M L sv = some v) :
    Steps Δ Φ (substMany ρ e) σ v σ := by
  cases e with
  | lit l =>
    simp only [vcgenPure] at hvc; split at hvc
    · cases hvc; simp [evalSVal] at hev; subst hev; rw [substMany_lit]; exact .refl _ _
    · cases hvc
  | var x =>
    simp only [vcgenPure] at hvc
    cases hlu : assocLookup st.vars x with
    | none => simp [hlu] at hvc
    | some sv0 =>
      simp [hlu] at hvc; rcases hvc with ⟨rfl, rfl⟩
      rcases hMatch.vars_match x sv0 hlu with ⟨v0, hρx, hev0, _⟩
      rw [hev0] at hev; cases hev
      rw [substMany_var hMatch.closed_env, hρx]; exact .refl _ _
  | loc _ => simp [vcgenPure] at hvc
  | un op e1 =>
    simp only [vcgenPure] at hvc; split at hvc
    · cases hvc
    · cases h1 : vcgenPure st e1 with
      | none => simp [h1] at hvc
      | some r1 =>
        rcases r1 with ⟨st1, sv1⟩; simp [h1] at hvc; rcases hvc with ⟨rfl, rfl⟩
        simp only [evalSVal] at hev
        cases hev1 : evalSVal M L sv1 with
        | none => simp [hev1] at hev
        | some v1 =>
          rw [hev1] at hev; cases v1 <;> simp at hev
          rename_i l1
          cases hop : evalUnOp op l1 with
          | none => simp [hop] at hev
          | some l' =>
            simp [hop] at hev; subst hev
            have hs1 := vcgenPure_complete (Δ := Δ) (Φ := Φ) hM hMatch h1 hev1
            rw [substMany_un]
            exact steps_trans (steps_un_congr hs1) (.trans (.unVal hop) (.refl _ _))
  | bin op e1 e2 =>
    by_cases hAnd : op = .and
    · subst hAnd
      simp only [vcgenPure, ↓reduceIte] at hvc
      cases h1 : vcgenPure st e1 with
      | none => simp [h1] at hvc
      | some r1 =>
        rcases r1 with ⟨st1, sv1⟩; simp only [h1] at hvc
        rcases vcgenPure_wf hMatch.wf h1 with ⟨hs1, hl1, hv1, hc1, hp1, _, hb1⟩
        cases h2 : vcgenPure (withPath st1 (.isTrue sv1)) e2 with
        | none => simp [h2] at hvc
        | some r2 =>
          rcases r2 with ⟨st2, sv2⟩; simp [h2] at hvc; rcases hvc with ⟨rfl, rfl⟩
          simp only [evalSVal] at hev
          cases hev1 : evalSVal M L sv1 with
          | none => simp [hev1] at hev
          | some v1 =>
            rw [hev1] at hev
            cases v1 with
            | lit lc =>
              cases lc with
              | bool b =>
                have hst1 := vcgenPure_complete (Δ := Δ) (Φ := Φ) hM hMatch h1 hev1
                rw [substMany_bin]
                cases b
                · simp [evalSVal] at hev; subst hev
                  exact steps_trans (steps_binLeft_congr hst1) (.trans .binAndFalse (.refl _ _))
                · have hM1 : StateMatches M L (withPath st1 (.isTrue sv1)) ρ σ :=
                    hMatch.of_eq ⟨by simp only [withPath, hs1, hv1]; exact hMatch.wf.vars_bound,
                      by simp only [withPath, hs1, hl1, hc1]; exact hMatch.wf.cells_bound,
                      by simp only [withPath, sformBound, hs1, hp1]; exact ⟨hMatch.wf.path_bound, hb1⟩⟩
                      hl1 hv1 hc1 (by simpa [withPath] using vcgenPure_cellTys_eq h1)
                      ⟨by simp only [hp1]; exact hMatch.path_holds, evalSVal_lit_iff_id.mp hev1⟩
                  have hst2 := vcgenPure_complete (Δ := Δ) (Φ := Φ) hM hM1 h2 hev
                  exact steps_trans (steps_binLeft_congr hst1) (.trans .binAndTrue hst2)
              | _ => simp at hev
            | _ => simp at hev
    · by_cases hOr : op = .or
      · subst hOr
        simp only [vcgenPure, reduceCtorEq, ↓reduceIte] at hvc
        cases h1 : vcgenPure st e1 with
        | none => simp [h1] at hvc
        | some r1 =>
          rcases r1 with ⟨st1, sv1⟩; simp only [h1] at hvc
          rcases vcgenPure_wf hMatch.wf h1 with ⟨hs1, hl1, hv1, hc1, hp1, _, hb1⟩
          cases h2 : vcgenPure (withPath st1 (.isFalse sv1)) e2 with
          | none => simp [h2] at hvc
          | some r2 =>
            rcases r2 with ⟨st2, sv2⟩; simp [h2] at hvc; rcases hvc with ⟨rfl, rfl⟩
            simp only [evalSVal] at hev
            cases hev1 : evalSVal M L sv1 with
            | none => simp [hev1] at hev
            | some v1 =>
              rw [hev1] at hev
              cases v1 with
              | lit lc =>
                cases lc with
                | bool b =>
                  have hst1 := vcgenPure_complete (Δ := Δ) (Φ := Φ) hM hMatch h1 hev1
                  rw [substMany_bin]
                  cases b
                  · have hM1 : StateMatches M L (withPath st1 (.isFalse sv1)) ρ σ :=
                      hMatch.of_eq ⟨by simp only [withPath, hs1, hv1]; exact hMatch.wf.vars_bound,
                        by simp only [withPath, hs1, hl1, hc1]; exact hMatch.wf.cells_bound,
                        by simp only [withPath, sformBound, hs1, hp1]; exact ⟨hMatch.wf.path_bound, hb1⟩⟩
                        hl1 hv1 hc1 (by simpa [withPath] using vcgenPure_cellTys_eq h1)
                        ⟨by simp only [hp1]; exact hMatch.path_holds, evalSVal_lit_iff_id.mp hev1⟩
                    have hst2 := vcgenPure_complete (Δ := Δ) (Φ := Φ) hM hM1 h2 hev
                    exact steps_trans (steps_binLeft_congr hst1) (.trans .binOrFalse hst2)
                  · simp [evalSVal] at hev; subst hev
                    exact steps_trans (steps_binLeft_congr hst1) (.trans .binOrTrue (.refl _ _))
                | _ => simp at hev
              | _ => simp at hev
      · simp only [vcgenPure, hAnd, hOr, ↓reduceIte] at hvc
        split at hvc
        · cases hvc
        · cases h1 : vcgenPure st e1 with
          | none => simp [h1] at hvc
          | some r1 =>
            rcases r1 with ⟨st1, sv1⟩; simp only [h1] at hvc
            rcases vcgenPure_wf hMatch.wf h1 with ⟨hs1, hl1, hv1, hc1, hp1, _, _⟩
            cases h2 : vcgenPure st1 e2 with
            | none => simp [h2] at hvc
            | some r2 =>
              rcases r2 with ⟨st2, sv2⟩; simp only [h2] at hvc; cases hvc
              simp only [evalSVal] at hev
              cases hev1 : evalSVal M L sv1 with
              | none => simp [hev1] at hev
              | some v1 =>
                cases hev2 : evalSVal M L sv2 with
                | none => simp [hev1, hev2] at hev
                | some v2 =>
                  rw [hev1, hev2] at hev
                  cases v1 <;> cases v2 <;> simp at hev
                  rename_i l1 l2
                  cases hop : evalBinOp op l1 l2 with
                  | none => simp [hop] at hev
                  | some r =>
                    cases r with
                    | trap _ => simp [hop] at hev
                    | val l' =>
                      simp [hop] at hev; subst hev
                      have hM1 : StateMatches M L st1 ρ σ :=
                        hMatch.of_eq ⟨by rw [hs1, hv1]; exact hMatch.wf.vars_bound,
                          by rw [hs1, hl1, hc1]; exact hMatch.wf.cells_bound,
                          by rw [hs1, hp1]; exact hMatch.wf.path_bound⟩
                          hl1 hv1 hc1 (by simpa [withPath] using vcgenPure_cellTys_eq h1) (by rw [hp1]; exact hMatch.path_holds)
                      have hst1 := vcgenPure_complete (Δ := Δ) (Φ := Φ) hM hMatch h1 hev1
                      have hst2 := vcgenPure_complete (Δ := Δ) (Φ := Φ) hM hM1 h2 hev2
                      rw [substMany_bin]
                      exact steps_trans (steps_binLeft_congr hst1)
                        (steps_trans (steps_binRight_congr hAnd hOr (.lit l1) hst2)
                          (.trans (.binVal hop) (.refl _ _)))
  | if_ c t e =>
    simp only [vcgenPure] at hvc
    cases h1 : vcgenPure st c with
    | none => simp [h1] at hvc
    | some r1 =>
      rcases r1 with ⟨st1, svc⟩; simp only [h1] at hvc
      rcases vcgenPure_wf hMatch.wf h1 with ⟨hs1, hl1, hv1, hc1, hp1, _, hbc⟩
      cases hT : vcgenPure (withPath st1 (.isTrue svc)) t with
      | none => simp [hT] at hvc
      | some rT =>
        rcases rT with ⟨stT, svT⟩; simp only [hT] at hvc
        cases hE : vcgenPure { st1 with path := .and st1.path (.isFalse svc), obs := stT.obs } e with
        | none => simp [hE] at hvc
        | some rE =>
          rcases rE with ⟨stE, svE⟩; simp [hE] at hvc; rcases hvc with ⟨rfl, rfl⟩
          simp only [evalSVal] at hev
          cases hevc : evalSVal M L svc with
          | none => simp [hevc] at hev
          | some vc =>
            rw [hevc] at hev
            cases vc with
            | lit lc =>
              cases lc with
              | bool b =>
                have hstC := vcgenPure_complete (Δ := Δ) (Φ := Φ) hM hMatch h1 hevc
                rw [substMany_if]
                cases b
                · have hME : StateMatches M L { st1 with path := .and st1.path (.isFalse svc), obs := stT.obs } ρ σ :=
                    hMatch.of_eq ⟨by simp only [hs1, hv1]; exact hMatch.wf.vars_bound,
                      by simp only [hs1, hl1, hc1]; exact hMatch.wf.cells_bound,
                      by simp only [sformBound, hs1, hp1]; exact ⟨hMatch.wf.path_bound, hbc⟩⟩
                      hl1 hv1 hc1 (by simpa [withPath] using vcgenPure_cellTys_eq h1)
                      ⟨by simp only [hp1]; exact hMatch.path_holds, evalSVal_lit_iff_id.mp hevc⟩
                  have hstE := vcgenPure_complete (Δ := Δ) (Φ := Φ) hM hME hE hev
                  exact steps_trans (steps_if_congr hstC) (.trans .ifFalse hstE)
                · have hMT : StateMatches M L (withPath st1 (.isTrue svc)) ρ σ :=
                    hMatch.of_eq ⟨by simp only [withPath, hs1, hv1]; exact hMatch.wf.vars_bound,
                      by simp only [withPath, hs1, hl1, hc1]; exact hMatch.wf.cells_bound,
                      by simp only [withPath, sformBound, hs1, hp1]; exact ⟨hMatch.wf.path_bound, hbc⟩⟩
                      hl1 hv1 hc1 (by simpa [withPath] using vcgenPure_cellTys_eq h1)
                      ⟨by simp only [hp1]; exact hMatch.path_holds, evalSVal_lit_iff_id.mp hevc⟩
                  have hstT := vcgenPure_complete (Δ := Δ) (Φ := Φ) hM hMT hT hev
                  exact steps_trans (steps_if_congr hstC) (.trans .ifTrue hstT)
              | _ => simp at hev
            | _ => simp at hev
  | cellGet e1 =>
    simp only [vcgenPure] at hvc
    cases h1 : vcgenPure st e1 with
    | none => simp [h1] at hvc
    | some r1 =>
      rcases r1 with ⟨st1, sv1⟩; simp only [h1] at hvc
      rcases vcgenPure_wf hMatch.wf h1 with ⟨_, _, _, hc1, _, _, _⟩
      cases sv1 with
      | loc l =>
        simp only at hvc
        cases hlu : locLookup st1.cells l with
        | none => simp [hlu] at hvc
        | some sv0 =>
          simp [hlu] at hvc; rcases hvc with ⟨rfl, rfl⟩
          rw [hc1] at hlu
          rcases hMatch.cells_match l sv0 hlu with ⟨v0, hget, hev0, _⟩
          rw [hev0] at hev; cases hev
          have hst1 := vcgenPure_complete (Δ := Δ) (Φ := Φ) hM hMatch h1 rfl
          rw [substMany_cellGet]
          exact steps_trans (steps_cellGet_congr hst1) (.trans (.cellGetVal hget) (.refl _ _))
      | _ => simp at hvc
  | getTag e1 =>
    simp only [vcgenPure] at hvc
    cases h1 : vcgenPure st e1 with
    | none => simp [h1] at hvc
    | some r1 =>
      rcases r1 with ⟨st1, sv1⟩; simp [h1] at hvc; rcases hvc with ⟨rfl, rfl⟩
      simp only [evalSVal] at hev
      cases hev1 : evalSVal M L sv1 with
      | none => simp [hev1] at hev
      | some v1 =>
        rw [hev1] at hev
        cases v1 with
        | makeData adt tag vs =>
          simp at hev; subst hev
          have hv1 : IsValue (.makeData adt tag vs) := (evalSVal_closed hM hev1).1
          cases hv1 with
          | makeData _ _ hvs =>
            have hst1 := vcgenPure_complete (Δ := Δ) (Φ := Φ) hM hMatch h1 hev1
            rw [substMany_getTag]
            exact steps_trans (steps_getTag_congr hst1) (.trans (.getTagVal hvs) (.refl _ _))
        | _ => simp at hev
  | _ => simp [vcgenPure] at hvc
termination_by sizeOf e

/-- Congruence of `vcgenPure` across any two matching symbolic models on the same concrete state. -/
theorem vcgenPure_eval_congr {M1 M2 : Model} {L1 L2 : Loc → Loc} {st1 st1' st2 st2' : SymState}
    {ρ : List (Ident × Expr)} {σ : Store} {e : Expr} {sv1 sv2 : SVal} {v : Expr}
    (hM1 : ValidModel M1) (hM2 : ValidModel M2)
    (hMatch1 : StateMatches M1 L1 st1 ρ σ) (hMatch2 : StateMatches M2 L2 st2 ρ σ)
    (hvc1 : vcgenPure st1 e = some (st1', sv1))
    (hvc2 : vcgenPure st2 e = some (st2', sv2))
    (hObs2 : ValidObs st2'.obs)
    (hev1 : evalSVal M1 L1 sv1 = some v) :
    evalSVal M2 L2 sv2 = some v := by
  have hsteps : Steps (fun _ => none) (fun _ => none) (substMany ρ e) σ v σ :=
    vcgenPure_complete hM1 hMatch1 hvc1 hev1
  have hv : IsValue v := (evalSVal_closed hM1 hev1).1
  have hsound := vcgenPure_sound (Δ := fun _ => none) (Φ := fun _ => none) hM2 hMatch2 hvc2 hObs2
  exact (hsound.2 v σ hv hsteps).2

/-- Helper: extend model `M` to match `havocCells st (trackedLocs st)` at ANY closed store `σ'`
    preserving `loc_bound` and `cells_ty` (no frame condition needed since every tracked cell is havocked). -/
theorem havocCells_extend_model_tracked {M : Model} {L : Loc → Loc} {st : SymState} {ρ : List (Ident × Expr)}
    {σ σ' : Store} (hM : ValidModel M) (hMatch : StateMatches M L st ρ σ)
    (hbound' : ∀ k < st.nextLoc, L k < σ'.length) (hclosed' : StoreClosed σ')
    (htys' : ∀ l ty, locLookup st.cellTys l = some ty → l < st.nextLoc ∧ ∃ v, σ'[L l]? = some v ∧ valHasTy v ty) :
    ∃ M', ValidModel M' ∧
      (∀ id < st.nextSym, M' id = M id) ∧
      StateMatches M' L (havocCells st (trackedLocs st)) ρ σ' := by
  have hlocs : ∀ l ∈ trackedLocs st, l < st.nextLoc := by
    intro l hl
    rcases List.mem_map.mp hl with ⟨p, hp, rfl⟩
    exact (hMatch.wf.cells_bound p hp).1
  have hframe0 : ∀ (l : Loc) sv, locLookup st.cells l = some sv → l ∉ trackedLocs st → σ'[L l]? = σ[L l]? := by
    intro l sv hlu hnt
    exact absurd (List.mem_map.mpr ⟨(l, sv), locLookup_mem hlu, rfl⟩) hnt
  exact havocCells_extend_model (trackedLocs st) hM hMatch hlocs hbound' hclosed' htys' hframe0

/-- `vcgenPure` unconditionally preserves `st.cells`. -/
theorem vcgenPure_cells_eq {st st' : SymState} {e : Expr} {sv : SVal}
    (hvc : vcgenPure st e = some (st', sv)) : st'.cells = st.cells := by
  cases e with
  | lit _ => simp only [vcgenPure] at hvc; split at hvc <;> cases hvc; rfl
  | var x => simp only [vcgenPure] at hvc; cases hlu : assocLookup st.vars x <;> simp [hlu] at hvc; rcases hvc with ⟨rfl, _⟩; rfl
  | loc _ => simp [vcgenPure] at hvc
  | un op e1 =>
    simp only [vcgenPure] at hvc; split at hvc
    · cases hvc
    · cases h1 : vcgenPure st e1 with
      | none => simp [h1] at hvc
      | some r1 => rcases r1 with ⟨st1, _⟩; simp [h1] at hvc; rcases hvc with ⟨rfl, _⟩; exact vcgenPure_cells_eq h1
  | bin op e1 e2 =>
    by_cases hAnd : op = .and
    · subst hAnd; simp only [vcgenPure, ↓reduceIte] at hvc
      cases h1 : vcgenPure st e1 with
      | none => simp [h1] at hvc
      | some r1 =>
        rcases r1 with ⟨st1, sv1⟩; simp only [h1] at hvc
        cases h2 : vcgenPure (withPath st1 (.isTrue sv1)) e2 with
        | none => simp [h2] at hvc
        | some r2 => rcases r2 with ⟨_, _⟩; simp [h2] at hvc; rcases hvc with ⟨rfl, _⟩; simpa using vcgenPure_cells_eq h1
    · by_cases hOr : op = .or
      · subst hOr; simp only [vcgenPure, reduceCtorEq, ↓reduceIte] at hvc
        cases h1 : vcgenPure st e1 with
        | none => simp [h1] at hvc
        | some r1 =>
          rcases r1 with ⟨st1, sv1⟩; simp only [h1] at hvc
          cases h2 : vcgenPure (withPath st1 (.isFalse sv1)) e2 with
          | none => simp [h2] at hvc
          | some r2 => rcases r2 with ⟨_, _⟩; simp [h2] at hvc; rcases hvc with ⟨rfl, _⟩; simpa using vcgenPure_cells_eq h1
      · simp only [vcgenPure, hAnd, hOr, ↓reduceIte] at hvc; split at hvc
        · cases hvc
        · cases h1 : vcgenPure st e1 with
          | none => simp [h1] at hvc
          | some r1 =>
            rcases r1 with ⟨st1, _⟩; simp only [h1] at hvc
            cases h2 : vcgenPure st1 e2 with
            | none => simp [h2] at hvc
            | some r2 =>
              rcases r2 with ⟨st2, _⟩; simp only [h2] at hvc; cases hvc
              split
              · exact (vcgenPure_cells_eq h2).trans (vcgenPure_cells_eq h1)
              · exact (vcgenPure_cells_eq h2).trans (vcgenPure_cells_eq h1)
  | if_ c t e =>
    simp only [vcgenPure] at hvc
    cases h1 : vcgenPure st c with
    | none => simp [h1] at hvc
    | some r1 =>
      rcases r1 with ⟨st1, svc⟩; simp only [h1] at hvc
      cases hT : vcgenPure (withPath st1 (.isTrue svc)) t with
      | none => simp [hT] at hvc
      | some rT =>
        rcases rT with ⟨stT, _⟩; simp only [hT] at hvc
        cases hE : vcgenPure { st1 with path := .and st1.path (.isFalse svc), obs := stT.obs } e with
        | none => simp [hE] at hvc
        | some rE => rcases rE with ⟨_, _⟩; simp [hE] at hvc; rcases hvc with ⟨rfl, _⟩; simpa using vcgenPure_cells_eq h1
  | cellGet e1 =>
    simp only [vcgenPure] at hvc
    cases h1 : vcgenPure st e1 with
    | none => simp [h1] at hvc
    | some r1 =>
      rcases r1 with ⟨st1, sv1⟩; simp only [h1] at hvc
      cases sv1 with
      | loc l =>
        simp only at hvc; cases hlu : locLookup st1.cells l <;> simp [hlu] at hvc
        rcases hvc with ⟨rfl, _⟩; exact vcgenPure_cells_eq h1
      | _ => simp at hvc
  | getTag e1 =>
    simp only [vcgenPure] at hvc
    cases h1 : vcgenPure st e1 with
    | none => simp [h1] at hvc
    | some r1 => rcases r1 with ⟨st1, _⟩; simp [h1] at hvc; rcases hvc with ⟨rfl, _⟩; exact vcgenPure_cells_eq h1
  | _ => simp [vcgenPure] at hvc
termination_by sizeOf e

theorem checkCallDecreases_cells_eq {env : VcgEnv} {nm : Ident} {fc : FnContract}
    {st0 st1 : SymState} (h : checkCallDecreases env nm fc st0 = some st1) :
    st1.cells = st0.cells := by
  unfold checkCallDecreases at h
  cases hcur : env.curDec with
  | none => simp [hcur] at h; subst h; rfl
  | some p =>
    rcases p with ⟨curTy, curSv⟩; simp only [hcur] at h
    split at h
    · cases hdec : fc.dec with
      | none => simp [hdec] at h
      | some calleeDecE =>
        simp only [hdec] at h
        cases hd : vcgenPure st0 calleeDecE with
        | none => simp [hd] at h
        | some rd =>
          rcases rd with ⟨stDec, nextSv⟩; simp only [hd] at h
          cases hty : inferSValTy stDec nextSv with
          | none => simp [hty] at h
          | some nextTy =>
            cases hops : decOpsForTy curTy with
            | none => simp [hty, hops] at h
            | some rops =>
              rcases rops with ⟨geOp, ltOp, zeroLit⟩
              simp only [hty, hops] at h
              split at h
              · cases h; simpa [emitOb_cells] using vcgenPure_cells_eq hd
              · cases h
    · cases h; rfl

/-- `locLookup` on `mergeCells` is `some` whenever `locLookup baseCells l` is `some`. -/
theorem locLookup_mergeCells_isSome {svc : SVal} {base cellsT cellsE : List (Loc × SVal)}
    {l : Loc} (h : (locLookup base l).isSome = true) :
    (locLookup (mergeCells svc base cellsT cellsE) l).isSome = true := by
  induction base with
  | nil => simp [locLookup] at h
  | cons p rest ih =>
    rcases p with ⟨k, svB⟩
    simp only [mergeCells, List.map, locLookup] at h ⊢
    cases hkl : (k == l)
    · simp [hkl] at h ⊢; exact ih h
    · simp [hkl]

/-- `havocCells` never removes any key from `cells`. -/
theorem locLookup_havocCells_isSome (st : SymState) (locs : List Loc) (l : Loc)
    (h : (locLookup st.cells l).isSome = true) :
    (locLookup (havocCells st locs).cells l).isSome = true := by
  induction locs generalizing st with
  | nil => exact h
  | cons l0 rest ih =>
    apply ih
    simp only [locLookup]
    cases (l0 == l)
    · exact h
    · rfl

/- `vcgen` never drops an already-tracked cell location from `st.cells`. -/
mutual
theorem vcgen_preserves_cell_dom {env : VcgEnv} {st st' : SymState} {e : Expr} {sv : SVal} {l : Loc}
    (hvc : vcgen env st e = some (st', sv)) (h : (locLookup st.cells l).isSome = true) :
    (locLookup st'.cells l).isSome = true := by
  cases e with
  | lit _ =>
    simp only [vcgen] at hvc; split at hvc <;> cases hvc; exact h
  | var x =>
    simp only [vcgen] at hvc; cases hlu : assocLookup st.vars x <;> simp [hlu] at hvc
    rcases hvc with ⟨rfl, _⟩; exact h
  | loc _ => simp [vcgen] at hvc
  | un op e1 =>
    simp only [vcgen] at hvc; split at hvc
    · cases hvc
    · cases h1 : vcgen env st e1 with
      | none => simp [h1] at hvc
      | some r1 =>
        rcases r1 with ⟨st1, sv1⟩; simp [h1] at hvc; rcases hvc with ⟨rfl, _⟩
        exact vcgen_preserves_cell_dom h1 h
  | bin op e1 e2 =>
    by_cases hAnd : op = .and
    · subst hAnd; simp only [vcgen, ↓reduceIte] at hvc
      cases h1 : vcgen env st e1 with
      | none => simp [h1] at hvc
      | some r1 =>
        rcases r1 with ⟨st1, sv1⟩; simp only [h1] at hvc
        cases h2 : vcgen env (withPath st1 (.isTrue sv1)) e2 with
        | none => simp [h2] at hvc
        | some r2 =>
          rcases r2 with ⟨st2, sv2⟩; simp only [h2] at hvc; split at hvc
          · cases hvc
          · cases hvc; exact locLookup_mergeCells_isSome (vcgen_preserves_cell_dom h1 h)
    · by_cases hOr : op = .or
      · subst hOr; simp only [vcgen, reduceCtorEq, ↓reduceIte] at hvc
        cases h1 : vcgen env st e1 with
        | none => simp [h1] at hvc
        | some r1 =>
          rcases r1 with ⟨st1, sv1⟩; simp only [h1] at hvc
          cases h2 : vcgen env (withPath st1 (.isFalse sv1)) e2 with
          | none => simp [h2] at hvc
          | some r2 =>
            rcases r2 with ⟨st2, sv2⟩; simp only [h2] at hvc; split at hvc
            · cases hvc
            · cases hvc; exact locLookup_mergeCells_isSome (vcgen_preserves_cell_dom h1 h)
      · simp only [vcgen, hAnd, hOr, ↓reduceIte] at hvc; split at hvc
        · cases hvc
        · cases h1 : vcgen env st e1 with
          | none => simp [h1] at hvc
          | some r1 =>
            rcases r1 with ⟨st1, sv1⟩; simp only [h1] at hvc
            cases h2 : vcgen env st1 e2 with
            | none => simp [h2] at hvc
            | some r2 =>
              rcases r2 with ⟨st2, sv2⟩; simp only [h2] at hvc; cases hvc
              have h2d := vcgen_preserves_cell_dom h2 (vcgen_preserves_cell_dom h1 h)
              split <;> exact h2d
  | let_ x e1 e2 =>
    simp only [vcgen] at hvc
    cases h1 : vcgen env st e1 with
    | none => simp [h1] at hvc
    | some r1 =>
      rcases r1 with ⟨st1, sv1⟩; simp only [h1] at hvc
      cases h2 : vcgen env { st1 with vars := (x, sv1) :: st1.vars } e2 with
      | none => simp [h2] at hvc
      | some r2 =>
        rcases r2 with ⟨st2, sv2⟩; simp [h2] at hvc; rcases hvc with ⟨rfl, _⟩
        dsimp only
        have h1d : (locLookup st1.cells l).isSome = true := vcgen_preserves_cell_dom h1 h
        have h1d' : (locLookup ({ st1 with vars := (x, sv1) :: st1.vars } : SymState).cells l).isSome = true := h1d
        exact vcgen_preserves_cell_dom h2 h1d'
  | block es =>
    simp only [vcgen] at hvc; exact vcgenBlock_preserves_cell_dom hvc h
  | if_ c t e =>
    simp only [vcgen] at hvc
    cases h1 : vcgen env st c with
    | none => simp [h1] at hvc
    | some r1 =>
      rcases r1 with ⟨st1, svc⟩; simp only [h1] at hvc
      cases hT : vcgen env (withPath st1 (.isTrue svc)) t with
      | none => simp [hT] at hvc
      | some rT =>
        rcases rT with ⟨stT, svT⟩; simp only [hT] at hvc
        cases hE : vcgen env ({ nextSym := stT.nextSym, nextLoc := st1.nextLoc, vars := st1.vars, cells := st1.cells, cellTys := st1.cellTys, path := .and st1.path (.isFalse svc), obs := stT.obs } : SymState) e with
        | none => simp [hE] at hvc
        | some rE =>
          rcases rE with ⟨stE, svE⟩; simp only [hE] at hvc; split at hvc
          · cases hvc
          · cases hvc; exact locLookup_mergeCells_isSome (vcgen_preserves_cell_dom h1 h)
  | cellNew e1 =>
    simp only [vcgen] at hvc
    cases h1 : vcgen env st e1 with
    | none => simp [h1] at hvc
    | some r1 =>
      rcases r1 with ⟨st1, sv1⟩; simp only [h1] at hvc
      cases hty : inferSValTy st1 sv1 with
      | none => simp [hty] at hvc
      | some elemTy =>
        simp only [hty] at hvc; split at hvc
        · cases hvc
        · rcases hvc with ⟨rfl, _⟩
          simp only [locLookup, emitOb_nextLoc, emitOb_cells]
          by_cases hEq : (st1.nextLoc == l) = true
          · simp [hEq]
          · simp [hEq]; exact vcgen_preserves_cell_dom h1 h
  | cellGet e1 =>
    simp only [vcgen] at hvc
    cases h1 : vcgen env st e1 with
    | none => simp [h1] at hvc
    | some r1 =>
      rcases r1 with ⟨st1, sv1⟩; simp only [h1] at hvc
      cases sv1 with
      | loc l0 =>
        simp only at hvc
        cases hlu : locLookup st1.cells l0 <;> simp [hlu] at hvc
        rcases hvc with ⟨rfl, _⟩; exact vcgen_preserves_cell_dom h1 h
      | _ => simp at hvc
  | cellSet e1 e2 =>
    simp only [vcgen] at hvc
    cases h1 : vcgen env st e1 with
    | none => simp [h1] at hvc
    | some r1 =>
      rcases r1 with ⟨st1, sv1⟩; simp only [h1] at hvc
      cases sv1 with
      | loc l0 =>
        simp only at hvc
        cases h2 : vcgen env st1 e2 with
        | none => simp [h2] at hvc
        | some r2 =>
          rcases r2 with ⟨st2, sv2⟩; simp only [h2] at hvc
          cases hlu : locLookup st2.cells l0 <;> simp only [hlu] at hvc
          · cases hvc
          · cases hty : locLookup st2.cellTys l0 <;> simp [hty] at hvc
            · rcases hvc with ⟨rfl, _⟩
              simp only [locLookup]
              cases (l0 == l)
              · exact vcgen_preserves_cell_dom h2 (vcgen_preserves_cell_dom h1 h)
              · rfl
            · rcases hvc with ⟨rfl, _⟩
              simp only [locLookup, emitOb_cells]
              cases (l0 == l)
              · exact vcgen_preserves_cell_dom h2 (vcgen_preserves_cell_dom h1 h)
              · rfl
      | _ => simp at hvc
  | getTag e1 =>
    simp only [vcgen] at hvc
    cases h1 : vcgen env st e1 with
    | none => simp [h1] at hvc
    | some r1 =>
      rcases r1 with ⟨st1, sv1⟩; simp [h1] at hvc; rcases hvc with ⟨rfl, _⟩
      exact vcgen_preserves_cell_dom h1 h
  | while_ c b =>
    simp only [vcgen] at hvc
    cases hlc : env.loops c b with
    | none => simp [hlc] at hvc
    | some lc =>
      simp only [hlc] at hvc
      cases hI0 : vcgenPure st lc.inv with
      | none => simp [hI0] at hvc
      | some rI0 =>
        rcases rI0 with ⟨stI0, svI0⟩; simp only [hI0] at hvc
        cases hIH : vcgenPure (havocCells (emitOb stI0 (.isTrue svI0)) (trackedLocs (emitOb stI0 (.isTrue svI0)))) lc.inv with
        | none => simp [hIH] at hvc
        | some rIH =>
          rcases rIH with ⟨stIH, svIH⟩; simp only [hIH] at hvc
          cases hC : vcgen env (withPath stIH (.isTrue svIH)) c with
          | none => simp [hC] at hvc
          | some rC =>
            rcases rC with ⟨stC, svC⟩; simp only [hC] at hvc; split at hvc
            · cases hvc
            · cases hPre : checkLoopPreDec (withPath stC (.isTrue svC)) lc.dec with
              | none => simp [hPre] at hvc
              | some rPre =>
                rcases rPre with ⟨stBodyIn, svD0Opt⟩; simp only [hPre] at hvc
                cases hB : vcgen env stBodyIn b with
                | none => simp [hB] at hvc
                | some rB =>
                  rcases rB with ⟨stB, _⟩; simp only [hB] at hvc; split at hvc
                  · cases hvc
                  · cases hPost : checkLoopPostDec stB lc.dec svD0Opt with
                    | none => simp [hPost] at hvc
                    | some stBDec =>
                      simp only [hPost] at hvc
                      cases hBI : vcgenPure stBDec lc.inv with
                      | none => simp [hBI] at hvc
                      | some rBI =>
                        rcases rBI with ⟨stBI, svBI⟩; simp [hBI] at hvc; rcases hvc with ⟨rfl, _⟩
                        have hcI0 : stI0.cells = st.cells := vcgenPure_cells_eq hI0
                        have hcIH : stIH.cells = (havocCells (emitOb stI0 (.isTrue svI0)) (trackedLocs (emitOb stI0 (.isTrue svI0)))).cells := vcgenPure_cells_eq hIH
                        apply vcgen_preserves_cell_dom hC
                        simp only [withPath_cells, hcIH]
                        apply locLookup_havocCells_isSome
                        simp only [emitOb_cells, hcI0]
                        exact h
  | applyDir name args =>
    unfold vcgen at hvc; dsimp only at hvc
    cases hAssert : (name == "assert")
    · rw [hAssert] at hvc; simp only [Bool.false_eq_true, ↓reduceIte] at hvc
      cases hAssume : (name == "assume")
      · rw [hAssume] at hvc; simp only [Bool.false_eq_true, ↓reduceIte] at hvc
        cases hfc : env.contracts name with
        | none => simp [hfc] at hvc
        | some fc =>
          simp only [hfc] at hvc; split at hvc
          · cases hvc
          · cases hArgs : vcgenList env st args with
            | none => simp [hArgs] at hvc
            | some rA =>
              rcases rA with ⟨stA, svArgs⟩; simp only [hArgs] at hvc; split at hvc
              · cases hvc
              · cases hTyp : checkCallArgTys stA fc.params svArgs with
                | none => simp [hTyp] at hvc
                | some stTyped =>
                  simp only [hTyp] at hvc
                  rcases checkCallArgTys_props hTyp with ⟨_, _, _, hcT, _, _, _, _⟩
                  cases hReq : vcgenPure { stTyped with vars := (fc.params.map Prod.fst).zip svArgs } fc.req with
                  | none => simp [hReq] at hvc
                  | some rReq =>
                    rcases rReq with ⟨stReq, svReq⟩; simp only [hReq] at hvc
                    cases hDec : checkCallDecreases env name fc (emitOb stReq (.isTrue svReq)) with
                    | none => simp [hDec] at hvc
                    | some stChecked =>
                      simp only [hDec] at hvc
                      cases hEns : vcgenPure { havocCells stChecked (collectLocArgs svArgs) with
                          nextSym := (havocCells stChecked (collectLocArgs svArgs)).nextSym + 1,
                          vars := (fc.retVar, .sym (havocCells stChecked (collectLocArgs svArgs)).nextSym) :: (fc.params.map Prod.fst).zip svArgs,
                          path := .and (havocCells stChecked (collectLocArgs svArgs)).path (.hasTy (.sym (havocCells stChecked (collectLocArgs svArgs)).nextSym) fc.retTy) } fc.ens with
                      | none => simp [hEns] at hvc
                      | some rEns =>
                        rcases rEns with ⟨stEns, svEns⟩; simp [hEns] at hvc; rcases hvc with ⟨rfl, _⟩
                        apply locLookup_havocCells_isSome
                        rw [checkCallDecreases_cells_eq hDec]
                        simp only [emitOb_cells, vcgenPure_cells_eq hReq, hcT]
                        exact vcgenList_preserves_cell_dom hArgs h
      · rw [hAssume] at hvc; simp only [↓reduceIte] at hvc
        cases args with
        | cons e1 rest =>
          cases rest with
          | nil =>
            cases h1 : vcgen env st e1 with
            | none => simp [h1] at hvc
            | some r1 =>
              rcases r1 with ⟨st1, sv1⟩; simp [h1] at hvc; rcases hvc with ⟨rfl, _⟩
              simpa [withPath] using vcgen_preserves_cell_dom h1 h
          | cons _ _ => simp at hvc
        | nil => simp at hvc
    · rw [hAssert] at hvc; simp only [↓reduceIte] at hvc
      cases args with
      | cons e1 rest =>
        cases rest with
        | nil =>
          cases h1 : vcgen env st e1 with
          | none => simp [h1] at hvc
          | some r1 =>
            rcases r1 with ⟨st1, sv1⟩; simp [h1] at hvc; rcases hvc with ⟨rfl, _⟩
            simpa [emitOb] using vcgen_preserves_cell_dom h1 h
        | cons _ _ => simp at hvc
      | nil => simp at hvc
  | _ => simp [vcgen] at hvc
termination_by sizeOf e

theorem vcgenBlock_preserves_cell_dom {env : VcgEnv} {st st' : SymState} {es : List Expr} {sv : SVal} {l : Loc}
    (hvc : vcgenBlock env st es = some (st', sv)) (h : (locLookup st.cells l).isSome = true) :
    (locLookup st'.cells l).isSome = true := by
  cases es with
  | nil => simp [vcgenBlock] at hvc; rcases hvc with ⟨rfl, _⟩; exact h
  | cons e1 rest =>
    cases rest with
    | nil => simp only [vcgenBlock] at hvc; exact vcgen_preserves_cell_dom hvc h
    | cons e2 rest' =>
      simp only [vcgenBlock] at hvc
      cases h1 : vcgen env st e1 with
      | none => simp [h1] at hvc
      | some r1 =>
        rcases r1 with ⟨st1, _⟩; simp only [h1] at hvc
        exact vcgenBlock_preserves_cell_dom hvc (vcgen_preserves_cell_dom h1 h)
termination_by sizeOf es

theorem vcgenList_preserves_cell_dom {env : VcgEnv} {st st' : SymState} {es : List Expr} {svs : List SVal} {l : Loc}
    (hvc : vcgenList env st es = some (st', svs)) (h : (locLookup st.cells l).isSome = true) :
    (locLookup st'.cells l).isSome = true := by
  cases es with
  | nil => simp [vcgenList] at hvc; rcases hvc with ⟨rfl, _⟩; exact h
  | cons e1 rest =>
    simp only [vcgenList] at hvc
    cases h1 : vcgen env st e1 with
    | none => simp [h1] at hvc
    | some r1 =>
      rcases r1 with ⟨st1, _⟩; simp only [h1] at hvc
      cases h2 : vcgenList env st1 rest with
      | none => simp [h2] at hvc
      | some r2 =>
        rcases r2 with ⟨st2, _⟩; simp [h2] at hvc; rcases hvc with ⟨rfl, _⟩
        exact vcgenList_preserves_cell_dom h2 (vcgen_preserves_cell_dom h1 h)
termination_by sizeOf es
end

/-- If two models agree on all symbolic IDs `< n`, they agree on all `SVal` bounded by `n`. -/
theorem evalSVal_agree_lt {M1 M2 : Model} {L : Loc → Loc} {n : Nat} {sv : SVal}
    (hb : svalBound n sv) (hagree : ∀ id < n, M2 id = M1 id) :
    evalSVal M2 L sv = evalSVal M1 L sv := by
  induction sv with
  | lit _ | loc _ => rfl
  | sym id => simp [evalSVal, hagree id hb]
  | un op e ih => simp [evalSVal, ih hb]
  | bin op e1 e2 ih1 ih2 => simp [evalSVal, ih1 hb.1, ih2 hb.2]
  | ite c t e ihc iht ihe => simp [evalSVal, ihc hb.1, iht hb.2.1, ihe hb.2.2]
  | getTag e ih => simp [evalSVal, ih hb]

/-- If two models agree on all symbolic IDs `< n`, they agree on all `SForm` bounded by `n`. -/
theorem evalSForm_agree_lt {M1 M2 : Model} {n : Nat} {f : SForm}
    (hb : sformBound n f) (hagree : ∀ id < n, M2 id = M1 id) :
    evalSForm M2 f ↔ evalSForm M1 f := by
  induction f with
  | tt | ff => exact Iff.rfl
  | isTrue sv | isFalse sv => simp [evalSForm, evalSVal_agree_lt (L := id) hb hagree]
  | neZero op sv => cases op <;> simp [evalSForm, evalSVal_agree_lt (L := id) hb hagree]
  | hasTy sv ty => simp [evalSForm, evalSVal_agree_lt (L := id) hb hagree]
  | not p ih => simp [evalSForm, ih hb]
  | and p q ih1 ih2 => simp [evalSForm, ih1 hb.1, ih2 hb.2]
  | imp p q ih1 ih2 => simp [evalSForm, ih1 hb.1, ih2 hb.2]

/-- Standard operational definitions of `assert` and `assume` in `Φ`. -/
def assertFunDef : FunDef :=
  { name := "assert", params := [("b", .bool)], retTy := .void,
    body := .if_ (.var "b") (.lit .unit) (.trap .divByZero) }

def assumeFunDef : FunDef :=
  { name := "assume", params := [("b", .bool)], retTy := .void,
    body := .if_ (.var "b") (.lit .unit) (.trap .hostTrap) }

/-- `Φ` binds `"assert"` and `"assume"` to their standard operational stubs. -/
def IntrinsicsOk (Φ : FunEnv) : Prop :=
  Φ "assert" = some assertFunDef ∧ Φ "assume" = some assumeFunDef

/- Whenever `vcgen` preserves `nextLoc` (no new local `cellNew`), it preserves `st.cellTys`. -/
mutual
theorem vcgen_cellTys_of_nextLoc_eq {env : VcgEnv} {st st' : SymState} {e : Expr} {sv : SVal}
    (hwf : SymWf st) (hvc : vcgen env st e = some (st', sv)) (hloc : st'.nextLoc = st.nextLoc) :
    st'.cellTys = st.cellTys := by
  cases e with
  | lit _ => simp only [vcgen] at hvc; split at hvc <;> cases hvc; rfl
  | var x => simp only [vcgen] at hvc; cases hlu : assocLookup st.vars x <;> simp [hlu] at hvc; rcases hvc with ⟨rfl, _⟩; rfl
  | loc _ => simp [vcgen] at hvc
  | un op e1 =>
    simp only [vcgen] at hvc; split at hvc
    · cases hvc
    · cases h1 : vcgen env st e1 with
      | none => simp [h1] at hvc
      | some r1 => rcases r1 with ⟨st1, _⟩; simp [h1] at hvc; rcases hvc with ⟨rfl, _⟩; exact vcgen_cellTys_of_nextLoc_eq hwf h1 hloc
  | bin op e1 e2 =>
    by_cases hAnd : op = .and
    · subst hAnd; simp only [vcgen, ↓reduceIte] at hvc
      cases h1 : vcgen env st e1 with
      | none => simp [h1] at hvc
      | some r1 =>
        rcases r1 with ⟨st1, sv1⟩; simp only [h1] at hvc
        cases h2 : vcgen env (withPath st1 (.isTrue sv1)) e2 with
        | none => simp [h2] at hvc
        | some r2 => rcases r2 with ⟨_, _⟩; simp only [h2] at hvc; split at hvc; · cases hvc
                     · cases hvc; simpa using vcgen_cellTys_of_nextLoc_eq hwf h1 hloc
    · by_cases hOr : op = .or
      · subst hOr; simp only [vcgen, reduceCtorEq, ↓reduceIte] at hvc
        cases h1 : vcgen env st e1 with
        | none => simp [h1] at hvc
        | some r1 =>
          rcases r1 with ⟨st1, sv1⟩; simp only [h1] at hvc
          cases h2 : vcgen env (withPath st1 (.isFalse sv1)) e2 with
          | none => simp [h2] at hvc
          | some r2 => rcases r2 with ⟨_, _⟩; simp only [h2] at hvc; split at hvc; · cases hvc
                       · cases hvc; simpa using vcgen_cellTys_of_nextLoc_eq hwf h1 hloc
      · simp only [vcgen, hAnd, hOr, ↓reduceIte] at hvc; split at hvc
        · cases hvc
        · cases h1 : vcgen env st e1 with
          | none => simp [h1] at hvc
          | some r1 =>
            rcases r1 with ⟨st1, _⟩; simp only [h1] at hvc
            rcases vcgen_wf hwf h1 with ⟨_, hl1, _, _, hwf1, _⟩
            cases h2 : vcgen env st1 e2 with
            | none => simp [h2] at hvc
            | some r2 =>
              rcases r2 with ⟨st2, _⟩; simp only [h2] at hvc; cases hvc
              rcases vcgen_wf hwf1 h2 with ⟨_, hl2, _, _, _, _⟩
              by_cases hdiv : isDivOp op <;> simp only [hdiv, ↓reduceIte, Bool.false_eq_true, emitOb_nextLoc, emitOb_cellTys] at hloc ⊢
              · have h1eq : st1.nextLoc = st.nextLoc := by omega
                have h2eq : st2.nextLoc = st1.nextLoc := by omega
                exact (vcgen_cellTys_of_nextLoc_eq hwf1 h2 h2eq).trans (vcgen_cellTys_of_nextLoc_eq hwf h1 h1eq)
              · have h1eq : st1.nextLoc = st.nextLoc := by omega
                have h2eq : st2.nextLoc = st1.nextLoc := by omega
                exact (vcgen_cellTys_of_nextLoc_eq hwf1 h2 h2eq).trans (vcgen_cellTys_of_nextLoc_eq hwf h1 h1eq)
  | let_ x e1 e2 =>
    simp only [vcgen] at hvc
    cases h1 : vcgen env st e1 with
    | none => simp [h1] at hvc
    | some r1 =>
      rcases r1 with ⟨st1, sv1⟩; simp only [h1] at hvc
      rcases vcgen_wf hwf h1 with ⟨_, hl1, _, _, hwf1, hb1⟩
      have hwf1' : SymWf { st1 with vars := (x, sv1) :: st1.vars } :=
        ⟨fun p hp => by rcases List.mem_cons.mp hp with rfl | hp'; exact hb1; exact hwf1.vars_bound p hp',
         hwf1.cells_bound, hwf1.path_bound⟩
      cases h2 : vcgen env { st1 with vars := (x, sv1) :: st1.vars } e2 with
      | none => simp [h2] at hvc
      | some r2 =>
        rcases r2 with ⟨st2, _⟩; simp [h2] at hvc; rcases hvc with ⟨rfl, _⟩
        rcases vcgen_wf hwf1' h2 with ⟨_, hl2, _, _, _, _⟩
        have h1eq : st1.nextLoc = st.nextLoc := by simp only at hloc hl2; omega
        have h2eq : st2.nextLoc = st1.nextLoc := by simp only at hloc hl2; omega
        exact (vcgen_cellTys_of_nextLoc_eq hwf1' h2 h2eq).trans (by simpa using vcgen_cellTys_of_nextLoc_eq hwf h1 h1eq)
  | block es => simp only [vcgen] at hvc; exact vcgenBlock_cellTys_of_nextLoc_eq hwf hvc hloc
  | if_ c t e =>
    simp only [vcgen] at hvc
    cases h1 : vcgen env st c with
    | none => simp [h1] at hvc
    | some r1 =>
      rcases r1 with ⟨st1, svc⟩; simp only [h1] at hvc
      cases hT : vcgen env (withPath st1 (.isTrue svc)) t with
      | none => simp [hT] at hvc
      | some rT =>
        rcases rT with ⟨stT, _⟩; simp only [hT] at hvc
        cases hE : vcgen env ({ nextSym := stT.nextSym, nextLoc := st1.nextLoc, vars := st1.vars, cells := st1.cells, cellTys := st1.cellTys, path := .and st1.path (.isFalse svc), obs := stT.obs } : SymState) e with
        | none => simp [hE] at hvc
        | some rE =>
          rcases rE with ⟨_, _⟩; simp only [hE] at hvc; split at hvc; · cases hvc
          · cases hvc; simpa using vcgen_cellTys_of_nextLoc_eq hwf h1 hloc
  | cellNew e1 =>
    simp only [vcgen] at hvc
    cases h1 : vcgen env st e1 with
    | none => simp [h1] at hvc
    | some r1 =>
      rcases r1 with ⟨st1, sv1⟩; simp only [h1] at hvc
      cases hty : inferSValTy st1 sv1 with
      | none => simp [hty] at hvc
      | some elemTy =>
        simp only [hty] at hvc; split at hvc
        · cases hvc
        · rcases hvc with ⟨rfl, _⟩
          rcases vcgen_wf hwf h1 with ⟨_, hl1, _, _, _, _⟩
          simp only [emitOb_nextLoc] at hloc; omega
  | cellGet e1 =>
    simp only [vcgen] at hvc
    cases h1 : vcgen env st e1 with
    | none => simp [h1] at hvc
    | some r1 =>
      rcases r1 with ⟨st1, sv1⟩; simp only [h1] at hvc
      cases sv1 with
      | loc l => simp only at hvc; cases hlu : locLookup st1.cells l <;> simp [hlu] at hvc; rcases hvc with ⟨rfl, _⟩; exact vcgen_cellTys_of_nextLoc_eq hwf h1 hloc
      | _ => simp at hvc
  | cellSet e1 e2 =>
    simp only [vcgen] at hvc
    cases h1 : vcgen env st e1 with
    | none => simp [h1] at hvc
    | some r1 =>
      rcases r1 with ⟨st1, sv1⟩; simp only [h1] at hvc
      rcases vcgen_wf hwf h1 with ⟨_, hl1, _, _, hwf1, _⟩
      cases sv1 with
      | loc l =>
        simp only at hvc
        cases h2 : vcgen env st1 e2 with
        | none => simp [h2] at hvc
        | some r2 =>
          rcases r2 with ⟨st2, _⟩; simp only [h2] at hvc
          rcases vcgen_wf hwf1 h2 with ⟨_, hl2, _, _, _, _⟩
          cases hlu : locLookup st2.cells l <;> simp only [hlu] at hvc
          · cases hvc
          · cases hct : locLookup st2.cellTys l <;> simp [hct] at hvc
            · rcases hvc with ⟨rfl, _⟩
              have h1eq : st1.nextLoc = st.nextLoc := by simp only at hloc; omega
              have h2eq : st2.nextLoc = st1.nextLoc := by simp only at hloc; omega
              exact (vcgen_cellTys_of_nextLoc_eq hwf1 h2 h2eq).trans (vcgen_cellTys_of_nextLoc_eq hwf h1 h1eq)
            · rcases hvc with ⟨rfl, _⟩
              have h1eq : st1.nextLoc = st.nextLoc := by simp only [emitOb_nextLoc] at hloc; omega
              have h2eq : st2.nextLoc = st1.nextLoc := by simp only [emitOb_nextLoc] at hloc; omega
              simpa [emitOb_cellTys] using (vcgen_cellTys_of_nextLoc_eq hwf1 h2 h2eq).trans (vcgen_cellTys_of_nextLoc_eq hwf h1 h1eq)
      | _ => simp at hvc
  | getTag e1 =>
    simp only [vcgen] at hvc
    cases h1 : vcgen env st e1 with
    | none => simp [h1] at hvc
    | some r1 => rcases r1 with ⟨_, _⟩; simp [h1] at hvc; rcases hvc with ⟨rfl, _⟩; exact vcgen_cellTys_of_nextLoc_eq hwf h1 hloc
  | while_ c b =>
    simp only [vcgen] at hvc
    cases hlc : env.loops c b with
    | none => simp [hlc] at hvc
    | some lc =>
      simp only [hlc] at hvc
      cases hI0 : vcgenPure st lc.inv with
      | none => simp [hI0] at hvc
      | some rI0 =>
        rcases rI0 with ⟨stI0, svI0⟩; simp only [hI0] at hvc
        cases hIH : vcgenPure (havocCells (emitOb stI0 (.isTrue svI0)) (trackedLocs (emitOb stI0 (.isTrue svI0)))) lc.inv with
        | none => simp [hIH] at hvc
        | some rIH =>
          rcases rIH with ⟨stIH, svIH⟩; simp only [hIH] at hvc
          cases hC : vcgen env (withPath stIH (.isTrue svIH)) c with
          | none => simp [hC] at hvc
          | some rC =>
            rcases rC with ⟨stC, svC⟩; simp only [hC] at hvc; split at hvc; · cases hvc
            · cases hPre : checkLoopPreDec (withPath stC (.isTrue svC)) lc.dec with
              | none => simp [hPre] at hvc
              | some rPre =>
                rcases rPre with ⟨stBodyIn, svD0Opt⟩; simp only [hPre] at hvc
                cases hB : vcgen env stBodyIn b with
                | none => simp [hB] at hvc
                | some rB =>
                  rcases rB with ⟨stB, _⟩; simp only [hB] at hvc; split at hvc; · cases hvc
                  · cases hPost : checkLoopPostDec stB lc.dec svD0Opt with
                    | none => simp [hPost] at hvc
                    | some stBDec =>
                      simp only [hPost] at hvc
                      cases hBI : vcgenPure stBDec lc.inv with
                      | none => simp [hBI] at hvc
                      | some rBI => rcases rBI with ⟨_, _⟩; simp [hBI] at hvc; rcases hvc with ⟨rfl, _⟩; rfl
  | applyDir name args =>
    unfold vcgen at hvc; dsimp only at hvc
    cases hAssert : (name == "assert")
    · rw [hAssert] at hvc; simp only [Bool.false_eq_true, ↓reduceIte] at hvc
      cases hAssume : (name == "assume")
      · rw [hAssume] at hvc; simp only [Bool.false_eq_true, ↓reduceIte] at hvc
        cases hfc : env.contracts name with
        | none => simp [hfc] at hvc
        | some fc =>
          simp only [hfc] at hvc; split at hvc; · cases hvc
          · cases hArgs : vcgenList env st args with
            | none => simp [hArgs] at hvc
            | some rA =>
              rcases rA with ⟨stA, svArgs⟩; simp only [hArgs] at hvc; split at hvc; · cases hvc
              · cases hTyp : checkCallArgTys stA fc.params svArgs with
                | none => simp [hTyp] at hvc
                | some stTyped =>
                  simp only [hTyp] at hvc
                  cases hReq : vcgenPure { stTyped with vars := (fc.params.map Prod.fst).zip svArgs } fc.req with
                  | none => simp [hReq] at hvc
                  | some rReq =>
                    rcases rReq with ⟨stReq, svReq⟩; simp only [hReq] at hvc
                    cases hDec : checkCallDecreases env name fc (emitOb stReq (.isTrue svReq)) with
                    | none => simp [hDec] at hvc
                    | some stChecked =>
                      simp only [hDec] at hvc
                      cases hEns : vcgenPure ({ havocCells stChecked (collectLocArgs svArgs) with
                          nextSym := (havocCells stChecked (collectLocArgs svArgs)).nextSym + 1,
                          vars := (fc.retVar, .sym (havocCells stChecked (collectLocArgs svArgs)).nextSym) :: (fc.params.map Prod.fst).zip svArgs,
                          path := .and (havocCells stChecked (collectLocArgs svArgs)).path (.hasTy (.sym (havocCells stChecked (collectLocArgs svArgs)).nextSym) fc.retTy) } : SymState) fc.ens with
                      | none => simp [hEns] at hvc
                      | some rEns => rcases rEns with ⟨_, _⟩; simp [hEns] at hvc; rcases hvc with ⟨rfl, _⟩; simpa using vcgenList_cellTys_of_nextLoc_eq hwf hArgs hloc
      · simp only [hAssume, ↓reduceIte] at hvc
        cases args with
        | nil => simp at hvc
        | cons e1 rest =>
          cases rest with
          | cons _ _ => simp at hvc
          | nil =>
            cases h1 : vcgen env st e1 with
            | none => simp [h1] at hvc
            | some r1 => rcases r1 with ⟨_, _⟩; simp [h1] at hvc; rcases hvc with ⟨rfl, _⟩; simpa [withPath] using vcgen_cellTys_of_nextLoc_eq hwf h1 hloc
    · simp only [hAssert, ↓reduceIte] at hvc
      cases args with
      | nil => simp at hvc
      | cons e1 rest =>
        cases rest with
        | cons _ _ => simp at hvc
        | nil =>
          cases h1 : vcgen env st e1 with
          | none => simp [h1] at hvc
          | some r1 => rcases r1 with ⟨_, _⟩; simp [h1] at hvc; rcases hvc with ⟨rfl, _⟩; simpa [emitOb] using vcgen_cellTys_of_nextLoc_eq hwf h1 hloc
  | _ => simp [vcgen] at hvc
termination_by sizeOf e

theorem vcgenBlock_cellTys_of_nextLoc_eq {env : VcgEnv} {st st' : SymState} {es : List Expr} {sv : SVal}
    (hwf : SymWf st) (hvc : vcgenBlock env st es = some (st', sv)) (hloc : st'.nextLoc = st.nextLoc) :
    st'.cellTys = st.cellTys := by
  cases es with
  | nil => simp [vcgenBlock] at hvc; rcases hvc with ⟨rfl, _⟩; rfl
  | cons e1 rest =>
    cases rest with
    | nil => simp only [vcgenBlock] at hvc; exact vcgen_cellTys_of_nextLoc_eq hwf hvc hloc
    | cons e2 rest' =>
      simp only [vcgenBlock] at hvc
      cases h1 : vcgen env st e1 with
      | none => simp [h1] at hvc
      | some r1 =>
        rcases r1 with ⟨st1, _⟩; simp only [h1] at hvc
        rcases vcgen_wf hwf h1 with ⟨_, hl1, _, _, hwf1, _⟩
        rcases vcgenBlock_wf hwf1 hvc with ⟨_, hl2, _, _, _, _⟩
        have h1eq : st1.nextLoc = st.nextLoc := by omega
        have h2eq : st'.nextLoc = st1.nextLoc := by omega
        exact (vcgenBlock_cellTys_of_nextLoc_eq hwf1 hvc h2eq).trans (vcgen_cellTys_of_nextLoc_eq hwf h1 h1eq)
termination_by sizeOf es

theorem vcgenList_cellTys_of_nextLoc_eq {env : VcgEnv} {st st' : SymState} {es : List Expr} {svs : List SVal}
    (hwf : SymWf st) (hvc : vcgenList env st es = some (st', svs)) (hloc : st'.nextLoc = st.nextLoc) :
    st'.cellTys = st.cellTys := by
  cases es with
  | nil => simp [vcgenList] at hvc; rcases hvc with ⟨rfl, _⟩; rfl
  | cons e1 rest =>
    simp only [vcgenList] at hvc
    cases h1 : vcgen env st e1 with
    | none => simp [h1] at hvc
    | some r1 =>
      rcases r1 with ⟨st1, _⟩; simp only [h1] at hvc
      rcases vcgen_wf hwf h1 with ⟨_, hl1, _, _, hwf1, _⟩
      cases h2 : vcgenList env st1 rest with
      | none => simp [h2] at hvc
      | some r2 =>
        rcases r2 with ⟨st2, _⟩; simp [h2] at hvc; rcases hvc with ⟨rfl, _⟩
        rcases vcgenList_wf hwf1 h2 with ⟨_, hl2, _, _, _, _⟩
        have h1eq : st1.nextLoc = st.nextLoc := by omega
        have h2eq : st2.nextLoc = st1.nextLoc := by omega
        exact (vcgenList_cellTys_of_nextLoc_eq hwf1 h2 h2eq).trans (vcgen_cellTys_of_nextLoc_eq hwf h1 h1eq)
termination_by sizeOf es
end

/-- Location-bound invariant on lookup results of `st.vars` and `st.cells`. -/
def SymLocWf (st : SymState) : Prop :=
  (∀ x sv, assocLookup st.vars x = some sv → svalLocBound st.nextLoc sv) ∧
  (∀ l sv, locLookup st.cells l = some sv → svalLocBound st.nextLoc sv)

theorem StateMatches.locWf {M L st ρ σ} (h : StateMatches M L st ρ σ) : SymLocWf st :=
  ⟨fun x sv hlu => (h.vars_match x sv hlu).choose_spec.2.2,
   fun l sv hlu => (h.cells_match l sv hlu).choose_spec.2.2⟩

theorem havocCells_locWf {st : SymState} {locs : List Loc} (h : SymLocWf st) :
    SymLocWf (havocCells st locs) := by
  induction locs generalizing st with
  | nil => exact h
  | cons l0 rest ih =>
    apply ih
    refine ⟨h.1, fun l sv hlu => ?_⟩
    simp only [locLookup] at hlu
    cases hEq : (l0 == l)
    · simp [hEq] at hlu; exact h.2 l sv hlu
    · simp [hEq] at hlu; subst hlu; trivial

/- `vcgen` preserves `SymLocWf` and returns a `svalLocBound`-bounded `SVal`. -/
mutual
theorem vcgen_locBound {env : VcgEnv} {st st' : SymState} {e : Expr} {sv : SVal}
    (hwf : SymWf st) (hlw : SymLocWf st) (hvc : vcgen env st e = some (st', sv)) :
    SymLocWf st' ∧ svalLocBound st'.nextLoc sv := by
  cases e with
  | lit _ => simp only [vcgen] at hvc; split at hvc <;> cases hvc; exact ⟨hlw, trivial⟩
  | var x =>
    simp only [vcgen] at hvc
    cases hlu : assocLookup st.vars x <;> simp [hlu] at hvc
    rcases hvc with ⟨rfl, rfl⟩; exact ⟨hlw, hlw.1 x _ hlu⟩
  | loc _ => simp [vcgen] at hvc
  | un op e1 =>
    simp only [vcgen] at hvc; split at hvc
    · cases hvc
    · cases h1 : vcgen env st e1 with
      | none => simp [h1] at hvc
      | some r1 => rcases r1 with ⟨st1, sv1⟩; simp [h1] at hvc; rcases hvc with ⟨rfl, rfl⟩; simpa [svalLocBound] using vcgen_locBound hwf hlw h1
  | bin op e1 e2 =>
    by_cases hAnd : op = .and
    · subst hAnd; simp only [vcgen, ↓reduceIte] at hvc
      cases h1 : vcgen env st e1 with
      | none => simp [h1] at hvc
      | some r1 =>
        rcases r1 with ⟨st1, sv1⟩; simp only [h1] at hvc
        rcases vcgen_wf hwf h1 with ⟨_, _, _, _, hwf1, hb1⟩
        rcases vcgen_locBound hwf hlw h1 with ⟨hlw1, hlb1⟩
        cases h2 : vcgen env (withPath st1 (.isTrue sv1)) e2 with
        | none => simp [h2] at hvc
        | some r2 =>
          rcases r2 with ⟨st2, sv2⟩; simp only [h2] at hvc; split at hvc; · cases hvc
          · rename_i hlocEq; simp only [bne_iff_ne, Decidable.not_not] at hlocEq; cases hvc
            rcases vcgen_locBound (symWf_withPath hwf1 (c := .isTrue sv1) hb1) hlw1 h2 with ⟨hlw2, hlb2⟩
            refine ⟨⟨hlw1.1, fun l sv hlu => ?_⟩, ⟨hlb1, hlocEq ▸ hlb2, trivial⟩⟩
            rcases locLookup_mergeCells hlu with ⟨svB, hluB, rfl⟩
            refine ⟨hlb1, ?_, ?_⟩
            · cases hT : locLookup st2.cells l with
              | none => exact hlw1.2 l svB hluB
              | some svT => exact hlocEq ▸ hlw2.2 l svT hT
            · cases hE : locLookup st1.cells l with
              | none => exact hlw1.2 l svB hluB
              | some svE => exact hlw1.2 l svE hE
    · by_cases hOr : op = .or
      · subst hOr; simp only [vcgen, reduceCtorEq, ↓reduceIte] at hvc
        cases h1 : vcgen env st e1 with
        | none => simp [h1] at hvc
        | some r1 =>
          rcases r1 with ⟨st1, sv1⟩; simp only [h1] at hvc
          rcases vcgen_wf hwf h1 with ⟨_, _, _, _, hwf1, hb1⟩
          rcases vcgen_locBound hwf hlw h1 with ⟨hlw1, hlb1⟩
          cases h2 : vcgen env (withPath st1 (.isFalse sv1)) e2 with
          | none => simp [h2] at hvc
          | some r2 =>
            rcases r2 with ⟨st2, sv2⟩; simp only [h2] at hvc; split at hvc; · cases hvc
            · rename_i hlocEq; simp only [bne_iff_ne, Decidable.not_not] at hlocEq; cases hvc
              rcases vcgen_locBound (symWf_withPath hwf1 (c := .isFalse sv1) hb1) hlw1 h2 with ⟨hlw2, hlb2⟩
              refine ⟨⟨hlw1.1, fun l sv hlu => ?_⟩, ⟨hlb1, trivial, hlocEq ▸ hlb2⟩⟩
              rcases locLookup_mergeCells hlu with ⟨svB, hluB, rfl⟩
              refine ⟨hlb1, ?_, ?_⟩
              · cases hT : locLookup st1.cells l with
                | none => exact hlw1.2 l svB hluB
                | some svT => exact hlw1.2 l svT hT
              · cases hE : locLookup st2.cells l with
                | none => exact hlw1.2 l svB hluB
                | some svE => exact hlocEq ▸ hlw2.2 l svE hE
      · simp only [vcgen, hAnd, hOr, ↓reduceIte] at hvc; split at hvc
        · cases hvc
        · cases h1 : vcgen env st e1 with
          | none => simp [h1] at hvc
          | some r1 =>
            rcases r1 with ⟨st1, sv1⟩; simp only [h1] at hvc
            rcases vcgen_wf hwf h1 with ⟨_, _, _, _, hwf1, _⟩
            rcases vcgen_locBound hwf hlw h1 with ⟨hlw1, hlb1⟩
            cases h2 : vcgen env st1 e2 with
            | none => simp [h2] at hvc
            | some r2 =>
              rcases r2 with ⟨st2, sv2⟩; simp only [h2] at hvc; cases hvc
              rcases vcgen_wf hwf1 h2 with ⟨_, hl2, _, _, _, _⟩
              rcases vcgen_locBound hwf1 hlw1 h2 with ⟨hlw2, hlb2⟩
              split <;> exact ⟨hlw2, ⟨svalLocBound_mono hl2 hlb1, hlb2⟩⟩
  | let_ x e1 e2 =>
    simp only [vcgen] at hvc
    cases h1 : vcgen env st e1 with
    | none => simp [h1] at hvc
    | some r1 =>
      rcases r1 with ⟨st1, sv1⟩; simp only [h1] at hvc
      rcases vcgen_wf hwf h1 with ⟨_, _, _, _, hwf1, hb1⟩
      rcases vcgen_locBound hwf hlw h1 with ⟨hlw1, hlb1⟩
      have hwfIn : SymWf { st1 with vars := (x, sv1) :: st1.vars } :=
        ⟨fun p hp => by rcases List.mem_cons.mp hp with rfl | hp'; exact hb1; exact hwf1.vars_bound p hp',
         hwf1.cells_bound, hwf1.path_bound⟩
      have hlwIn : SymLocWf { st1 with vars := (x, sv1) :: st1.vars } :=
        ⟨fun y svy hlu => by
          simp only [assocLookup] at hlu
          cases hxy : (x == y)
          · simp [hxy] at hlu; exact hlw1.1 y svy hlu
          · simp [hxy] at hlu; subst hlu; exact hlb1,
         hlw1.2⟩
      cases h2 : vcgen env { st1 with vars := (x, sv1) :: st1.vars } e2 with
      | none => simp [h2] at hvc
      | some r2 =>
        rcases r2 with ⟨st2, sv2⟩; simp [h2] at hvc; rcases hvc with ⟨rfl, rfl⟩
        rcases vcgen_wf hwfIn h2 with ⟨_, hl2, _, _, _, _⟩
        rcases vcgen_locBound hwfIn hlwIn h2 with ⟨hlw2, hlb2⟩
        exact ⟨⟨fun y svy hlu => svalLocBound_mono hl2 (hlw1.1 y svy hlu), hlw2.2⟩, hlb2⟩
  | block es => simp only [vcgen] at hvc; exact vcgenBlock_locBound hwf hlw hvc
  | if_ c t e =>
    simp only [vcgen] at hvc
    cases h1 : vcgen env st c with
    | none => simp [h1] at hvc
    | some r1 =>
      rcases r1 with ⟨st1, svc⟩; simp only [h1] at hvc
      rcases vcgen_wf hwf h1 with ⟨_, _, _, _, hwf1, hbc⟩
      rcases vcgen_locBound hwf hlw h1 with ⟨hlw1, hlbc⟩
      cases hT : vcgen env (withPath st1 (.isTrue svc)) t with
      | none => simp [hT] at hvc
      | some rT =>
        rcases rT with ⟨stT, svT⟩; simp only [hT] at hvc
        rcases vcgen_wf (symWf_withPath hwf1 (c := .isTrue svc) hbc) hT with ⟨hsT, _, _, _, _, _⟩
        rcases vcgen_locBound (symWf_withPath hwf1 (c := .isTrue svc) hbc) hlw1 hT with ⟨hlwT, hlbT⟩
        have hwfEIn : SymWf ({ nextSym := stT.nextSym, nextLoc := st1.nextLoc, vars := st1.vars, cells := st1.cells, cellTys := st1.cellTys, path := .and st1.path (.isFalse svc), obs := stT.obs } : SymState) :=
          ⟨fun p hp => svalBound_mono hsT (hwf1.vars_bound p hp),
           fun p hp => ⟨(hwf1.cells_bound p hp).1, svalBound_mono hsT (hwf1.cells_bound p hp).2⟩,
           ⟨sformBound_mono hsT hwf1.path_bound, svalBound_mono hsT hbc⟩⟩
        cases hE : vcgen env ({ nextSym := stT.nextSym, nextLoc := st1.nextLoc, vars := st1.vars, cells := st1.cells, cellTys := st1.cellTys, path := .and st1.path (.isFalse svc), obs := stT.obs } : SymState) e with
        | none => simp [hE] at hvc
        | some rE =>
          rcases rE with ⟨stE, svE⟩; simp only [hE] at hvc; split at hvc; · cases hvc
          · rename_i hlocEqs
            simp only [Bool.or_eq_true, bne_iff_ne, not_or, Decidable.not_not] at hlocEqs
            rcases hlocEqs with ⟨hlocT, hlocE⟩; cases hvc
            rcases vcgen_locBound hwfEIn hlw1 hE with ⟨hlwE, hlbE⟩
            refine ⟨⟨hlw1.1, fun l sv hlu => ?_⟩, ⟨hlbc, hlocT ▸ hlbT, hlocE ▸ hlbE⟩⟩
            rcases locLookup_mergeCells hlu with ⟨svB, hluB, rfl⟩
            refine ⟨hlbc, ?_, ?_⟩
            · cases hluT : locLookup stT.cells l with
              | none => exact hlw1.2 l svB hluB
              | some svTl => exact hlocT ▸ hlwT.2 l svTl hluT
            · cases hluE : locLookup stE.cells l with
              | none => exact hlw1.2 l svB hluB
              | some svEl => exact hlocE ▸ hlwE.2 l svEl hluE
  | cellNew e1 =>
    simp only [vcgen] at hvc
    cases h1 : vcgen env st e1 with
    | none => simp [h1] at hvc
    | some r1 =>
      rcases r1 with ⟨st1, sv1⟩; simp only [h1] at hvc
      cases hty : inferSValTy st1 sv1 with
      | none => simp [hty] at hvc
      | some elemTy =>
        simp only [hty] at hvc; split at hvc
        · cases hvc
        · rcases hvc with ⟨rfl, rfl⟩
          rcases vcgen_locBound hwf hlw h1 with ⟨hlw1, hlb1⟩
          refine ⟨⟨fun x svx hlu => svalLocBound_mono (Nat.le_succ _) (hlw1.1 x svx hlu), fun l sv hlu => ?_⟩, Nat.lt_succ_self _⟩
          simp only [locLookup, emitOb_nextLoc, emitOb_cells] at hlu
          cases hEq : (st1.nextLoc == l)
          · simp [hEq] at hlu; exact svalLocBound_mono (Nat.le_succ _) (hlw1.2 l sv hlu)
          · simp [hEq] at hlu; subst hlu; exact svalLocBound_mono (Nat.le_succ _) hlb1
  | cellGet e1 =>
    simp only [vcgen] at hvc
    cases h1 : vcgen env st e1 with
    | none => simp [h1] at hvc
    | some r1 =>
      rcases r1 with ⟨st1, sv1⟩; simp only [h1] at hvc
      rcases vcgen_locBound hwf hlw h1 with ⟨hlw1, _⟩
      cases sv1 with
      | loc l =>
        simp only at hvc
        cases hlu : locLookup st1.cells l <;> simp [hlu] at hvc
        rcases hvc with ⟨rfl, rfl⟩; exact ⟨hlw1, hlw1.2 l _ hlu⟩
      | _ => simp at hvc
  | cellSet e1 e2 =>
    simp only [vcgen] at hvc
    cases h1 : vcgen env st e1 with
    | none => simp [h1] at hvc
    | some r1 =>
      rcases r1 with ⟨st1, sv1⟩; simp only [h1] at hvc
      rcases vcgen_wf hwf h1 with ⟨_, _, _, _, hwf1, _⟩
      rcases vcgen_locBound hwf hlw h1 with ⟨hlw1, _⟩
      cases sv1 with
      | loc l =>
        simp only at hvc
        cases h2 : vcgen env st1 e2 with
        | none => simp [h2] at hvc
        | some r2 =>
          rcases r2 with ⟨st2, sv2⟩; simp only [h2] at hvc
          rcases vcgen_locBound hwf1 hlw1 h2 with ⟨hlw2, hlb2⟩
          cases hlu : locLookup st2.cells l <;> simp only [hlu] at hvc
          · cases hvc
          · cases hct : locLookup st2.cellTys l <;> simp [hct] at hvc
            · rcases hvc with ⟨rfl, rfl⟩
              refine ⟨⟨hlw2.1, fun l0 sv0 hlu0 => ?_⟩, trivial⟩
              simp only [locLookup] at hlu0
              cases hEq : (l == l0)
              · simp [hEq] at hlu0; exact hlw2.2 l0 sv0 hlu0
              · simp [hEq] at hlu0; subst hlu0; exact hlb2
            · rcases hvc with ⟨rfl, rfl⟩
              refine ⟨⟨hlw2.1, fun l0 sv0 hlu0 => ?_⟩, trivial⟩
              simp only [locLookup, emitOb_cells] at hlu0
              cases hEq : (l == l0)
              · simp [hEq] at hlu0; exact hlw2.2 l0 sv0 hlu0
              · simp [hEq] at hlu0; subst hlu0; exact hlb2
      | _ => simp at hvc
  | getTag e1 =>
    simp only [vcgen] at hvc
    cases h1 : vcgen env st e1 with
    | none => simp [h1] at hvc
    | some r1 => rcases r1 with ⟨_, _⟩; simp [h1] at hvc; rcases hvc with ⟨rfl, rfl⟩; simpa [svalLocBound] using vcgen_locBound hwf hlw h1
  | while_ c b =>
    simp only [vcgen] at hvc
    cases hlc : env.loops c b with
    | none => simp [hlc] at hvc
    | some lc =>
      simp only [hlc] at hvc
      cases hI0 : vcgenPure st lc.inv with
      | none => simp [hI0] at hvc
      | some rI0 =>
        rcases rI0 with ⟨stI0, svI0⟩; simp only [hI0] at hvc
        rcases vcgenPure_wf hwf hI0 with ⟨hsI0, hlI0, hvI0, hcI0, hpI0, _, _⟩
        have hwf1 : SymWf (emitOb stI0 (.isTrue svI0)) :=
          ⟨by simp only [emitOb, hsI0, hvI0]; exact hwf.vars_bound,
           by simp only [emitOb, hsI0, hlI0, hcI0]; exact hwf.cells_bound,
           by simp only [emitOb, hsI0, hpI0]; exact hwf.path_bound⟩
        have hlw1 : SymLocWf (emitOb stI0 (.isTrue svI0)) :=
          ⟨by simp only [emitOb, hlI0, hvI0]; exact hlw.1, by simp only [emitOb, hlI0, hcI0]; exact hlw.2⟩
        have hlocs1 : ∀ l ∈ trackedLocs (emitOb stI0 (.isTrue svI0)), l < (emitOb stI0 (.isTrue svI0)).nextLoc :=
          fun l hl => by rcases List.mem_map.mp hl with ⟨p, hp, rfl⟩; exact (hwf1.cells_bound p hp).1
        rcases havocCells_props (emitOb stI0 (.isTrue svI0)) (trackedLocs (emitOb stI0 (.isTrue svI0))) hlocs1 hwf1 with
          ⟨_, hlH, _, _, _, hwfH, _, _⟩
        have hlwH : SymLocWf (havocCells (emitOb stI0 (.isTrue svI0)) (trackedLocs (emitOb stI0 (.isTrue svI0)))) :=
          havocCells_locWf hlw1
        cases hIH : vcgenPure (havocCells (emitOb stI0 (.isTrue svI0)) (trackedLocs (emitOb stI0 (.isTrue svI0)))) lc.inv with
        | none => simp [hIH] at hvc
        | some rIH =>
          rcases rIH with ⟨stIH, svIH⟩; simp only [hIH] at hvc
          rcases vcgenPure_wf hwfH hIH with ⟨hsIH, hlIH, hvIH, hcIH, hpIH, _, hbIH⟩
          have hwfLE : SymWf (withPath stIH (.isTrue svIH)) :=
            ⟨by simp only [withPath, hsIH, hvIH]; exact hwfH.vars_bound,
             by simp only [withPath, hsIH, hlIH, hcIH]; exact hwfH.cells_bound,
             by simp only [withPath, sformBound, hsIH, hpIH]; exact ⟨hwfH.path_bound, hbIH⟩⟩
          have hlwLE : SymLocWf (withPath stIH (.isTrue svIH)) :=
            ⟨by simp only [withPath, hlIH, hvIH]; exact hlwH.1, by simp only [withPath, hlIH, hcIH]; exact hlwH.2⟩
          cases hC : vcgen env (withPath stIH (.isTrue svIH)) c with
          | none => simp [hC] at hvc
          | some rC =>
            rcases rC with ⟨stC, svC⟩; simp only [hC] at hvc; split at hvc; · cases hvc
            · rename_i hlocC; simp only [bne_iff_ne, Decidable.not_not] at hlocC
              rcases vcgen_locBound hwfLE hlwLE hC with ⟨hlwC, _⟩
              cases hPre : checkLoopPreDec (withPath stC (.isTrue svC)) lc.dec with
              | none => simp [hPre] at hvc
              | some rPre =>
                rcases rPre with ⟨stBodyIn, svD0Opt⟩; simp only [hPre] at hvc
                cases hB : vcgen env stBodyIn b with
                | none => simp [hB] at hvc
                | some rB =>
                  rcases rB with ⟨stB, _⟩; simp only [hB] at hvc; split at hvc; · cases hvc
                  · cases hPost : checkLoopPostDec stB lc.dec svD0Opt with
                    | none => simp [hPost] at hvc
                    | some stBDec =>
                      simp only [hPost] at hvc
                      cases hBI : vcgenPure stBDec lc.inv with
                      | none => simp [hBI] at hvc
                      | some rBI =>
                        rcases rBI with ⟨_, _⟩; simp [hBI] at hvc; rcases hvc with ⟨rfl, rfl⟩
                        have hlEq : stC.nextLoc = st.nextLoc := by
                          simp only [withPath_nextLoc, emitOb_nextLoc] at hlocC hlH hlI0 hlIH ⊢; omega
                        exact ⟨⟨fun x svx hlu => hlEq ▸ hlw.1 x svx hlu, hlwC.2⟩, trivial⟩
  | applyDir name args =>
    unfold vcgen at hvc; dsimp only at hvc
    cases hAssert : (name == "assert")
    · rw [hAssert] at hvc; simp only [Bool.false_eq_true, ↓reduceIte] at hvc
      cases hAssume : (name == "assume")
      · rw [hAssume] at hvc; simp only [Bool.false_eq_true, ↓reduceIte] at hvc
        cases hfc : env.contracts name with
        | none => simp [hfc] at hvc
        | some fc =>
          simp only [hfc] at hvc; split at hvc; · cases hvc
          · cases hArgs : vcgenList env st args with
            | none => simp [hArgs] at hvc
            | some rA =>
              rcases rA with ⟨stA, svArgs⟩; simp only [hArgs] at hvc; split at hvc; · cases hvc
              · cases hTyp : checkCallArgTys stA fc.params svArgs with
                | none => simp [hTyp] at hvc
                | some stTyped =>
                  simp only [hTyp] at hvc
                  rcases checkCallArgTys_props hTyp with ⟨_, hlT, _, hcT, _, _, _, _⟩
                  rcases vcgenList_wf hwf hArgs with ⟨_, _, _, _, hwfA, _⟩
                  rcases vcgenList_locBound hwf hlw hArgs with ⟨hlwA, _⟩
                  cases hReq : vcgenPure { stTyped with vars := (fc.params.map Prod.fst).zip svArgs } fc.req with
                  | none => simp [hReq] at hvc
                  | some rReq =>
                    rcases rReq with ⟨stReq, svReq⟩; simp only [hReq] at hvc
                    have hwfCall : SymWf { stTyped with vars := (fc.params.map Prod.fst).zip svArgs } := by
                      rcases vcgenList_wf hwf hArgs with ⟨_, _, _, _, hwfA', hbArgs⟩
                      rcases checkCallArgTys_props hTyp with ⟨hsT, hlT', _, hcT', _, hpT, _, _⟩
                      exact ⟨fun p hp => hsT ▸ hbArgs p.2 (List.of_mem_zip hp).2, by rw [hsT, hlT', hcT']; exact hwfA'.cells_bound, hsT ▸ hpT ▸ hwfA'.path_bound⟩
                    rcases vcgenPure_wf hwfCall hReq with ⟨_, hlReq, _, hcReq, _, _, _⟩
                    cases hDec : checkCallDecreases env name fc (emitOb stReq (.isTrue svReq)) with
                    | none => simp [hDec] at hvc
                    | some stChecked =>
                      simp only [hDec] at hvc
                      cases hEns : vcgenPure ({ havocCells stChecked (collectLocArgs svArgs) with
                          nextSym := (havocCells stChecked (collectLocArgs svArgs)).nextSym + 1,
                          vars := (fc.retVar, .sym (havocCells stChecked (collectLocArgs svArgs)).nextSym) :: (fc.params.map Prod.fst).zip svArgs,
                          path := .and (havocCells stChecked (collectLocArgs svArgs)).path (.hasTy (.sym (havocCells stChecked (collectLocArgs svArgs)).nextSym) fc.retTy) } : SymState) fc.ens with
                      | none => simp [hEns] at hvc
                      | some rEns =>
                        rcases rEns with ⟨_, _⟩; simp [hEns] at hvc; rcases hvc with ⟨rfl, rfl⟩
                        have hcellsHav : ∀ l sv, locLookup (havocCells stChecked (collectLocArgs svArgs)).cells l = some sv → svalLocBound stA.nextLoc sv := by
                          have hsub : ∀ (s : SymState) (locs : List Loc),
                              (∀ l sv, locLookup s.cells l = some sv → svalLocBound stA.nextLoc sv) →
                              (∀ l sv, locLookup (havocCells s locs).cells l = some sv → svalLocBound stA.nextLoc sv) := by
                            intro s locs
                            induction locs generalizing s with
                            | nil => intro hs; exact hs
                            | cons l0 rest ih =>
                              intro hs; apply ih; intro l sv hlu
                              simp only [locLookup] at hlu
                              cases hEq : (l0 == l)
                              · simp [hEq] at hlu; exact hs l sv hlu
                              · simp [hEq] at hlu; subst hlu; trivial
                          exact hsub _ _ (by rw [checkCallDecreases_cells_eq hDec]; simp only [emitOb_cells, hcReq, hcT]; exact hlwA.2)
                        exact ⟨⟨hlwA.1, hcellsHav⟩, trivial⟩
      · simp only [hAssume, ↓reduceIte] at hvc
        cases args with
        | nil => simp at hvc
        | cons e1 rest =>
          cases rest with
          | cons _ _ => simp at hvc
          | nil =>
            cases h1 : vcgen env st e1 with
            | none => simp [h1] at hvc
            | some r1 => rcases r1 with ⟨_, _⟩; simp [h1] at hvc; rcases hvc with ⟨rfl, rfl⟩; exact ⟨(vcgen_locBound hwf hlw h1).1, trivial⟩
    · simp only [hAssert, ↓reduceIte] at hvc
      cases args with
      | nil => simp at hvc
      | cons e1 rest =>
        cases rest with
        | cons _ _ => simp at hvc
        | nil =>
          cases h1 : vcgen env st e1 with
          | none => simp [h1] at hvc
          | some r1 => rcases r1 with ⟨_, _⟩; simp [h1] at hvc; rcases hvc with ⟨rfl, rfl⟩; exact ⟨(vcgen_locBound hwf hlw h1).1, trivial⟩
  | _ => simp [vcgen] at hvc
termination_by sizeOf e

theorem vcgenBlock_locBound {env : VcgEnv} {st st' : SymState} {es : List Expr} {sv : SVal}
    (hwf : SymWf st) (hlw : SymLocWf st) (hvc : vcgenBlock env st es = some (st', sv)) :
    SymLocWf st' ∧ svalLocBound st'.nextLoc sv := by
  cases es with
  | nil => simp [vcgenBlock] at hvc; rcases hvc with ⟨rfl, rfl⟩; exact ⟨hlw, trivial⟩
  | cons e1 rest =>
    cases rest with
    | nil => simp only [vcgenBlock] at hvc; exact vcgen_locBound hwf hlw hvc
    | cons e2 rest' =>
      simp only [vcgenBlock] at hvc
      cases h1 : vcgen env st e1 with
      | none => simp [h1] at hvc
      | some r1 =>
        rcases r1 with ⟨st1, _⟩; simp only [h1] at hvc
        rcases vcgen_wf hwf h1 with ⟨_, _, _, _, hwf1, _⟩
        rcases vcgen_locBound hwf hlw h1 with ⟨hlw1, _⟩
        exact vcgenBlock_locBound hwf1 hlw1 hvc
termination_by sizeOf es

theorem vcgenList_locBound {env : VcgEnv} {st st' : SymState} {es : List Expr} {svs : List SVal}
    (hwf : SymWf st) (hlw : SymLocWf st) (hvc : vcgenList env st es = some (st', svs)) :
    SymLocWf st' ∧ (∀ sv ∈ svs, svalLocBound st'.nextLoc sv) := by
  cases es with
  | nil => simp [vcgenList] at hvc; rcases hvc with ⟨rfl, rfl⟩; exact ⟨hlw, fun _ h => by cases h⟩
  | cons e1 rest =>
    simp only [vcgenList] at hvc
    cases h1 : vcgen env st e1 with
    | none => simp [h1] at hvc
    | some r1 =>
      rcases r1 with ⟨st1, sv1⟩; simp only [h1] at hvc
      rcases vcgen_wf hwf h1 with ⟨_, _, _, _, hwf1, _⟩
      rcases vcgen_locBound hwf hlw h1 with ⟨hlw1, hlb1⟩
      cases h2 : vcgenList env st1 rest with
      | none => simp [h2] at hvc
      | some r2 =>
        rcases r2 with ⟨st2, svs2⟩; simp [h2] at hvc; rcases hvc with ⟨rfl, rfl⟩
        rcases vcgenList_wf hwf1 h2 with ⟨_, hl2, _, _, _, _⟩
        rcases vcgenList_locBound hwf1 hlw1 h2 with ⟨hlw2, hlb2⟩
        refine ⟨hlw2, fun sv hsv => ?_⟩
        rcases List.mem_cons.mp hsv with rfl | hsv'
        · exact svalLocBound_mono hl2 hlb1
        · exact hlb2 sv hsv'
termination_by sizeOf es
end

private theorem list_contains_nat_iff (xs : List Nat) (a : Nat) :
    xs.contains a = true ↔ a ∈ xs := by
  induction xs with
  | nil =>
    constructor
    · intro h; cases h
    · intro h; cases h
  | cons x rest ih =>
    simp only [List.contains, List.elem_cons, List.mem_cons]
    by_cases h : (a == x) = true
    · have hEq : a = x := eq_of_beq h
      subst hEq; simp [h]
    · simp only [Bool.not_eq_true] at h
      have hne : a ≠ x := fun hEq => by subst hEq; simp at h
      rw [h]; simp only [Bool.false_eq_true, ↓reduceIte, hne, false_or]
      exact ih

/-- `noDupLocs` is preserved by mapping an injective function over bounded locations. -/
theorem noDupLocs_map_inj {L : Loc → Loc} {n : Nat} {xs : List Loc}
    (hnd : noDupLocs xs = true) (hb : ∀ l ∈ xs, l < n)
    (hinj : ∀ k1 k2, k1 < n → k2 < n → L k1 = L k2 → k1 = k2) :
    noDupLocs (xs.map L) = true := by
  induction xs with
  | nil => rfl
  | cons l rest ih =>
    simp only [noDupLocs, Bool.and_eq_true, Bool.not_eq_true'] at hnd
    simp only [List.map, noDupLocs, Bool.and_eq_true, Bool.not_eq_true']
    refine ⟨?_, ih hnd.2 (fun x hx => hb x (List.mem_cons_of_mem _ hx))⟩
    cases hc : (rest.map L).contains (L l) with
    | false => rfl
    | true =>
      exfalso
      rcases List.mem_map.mp ((list_contains_nat_iff _ _).mp hc) with ⟨x, hx, hEqL⟩
      have hEq := hinj x l (hb x (List.mem_cons_of_mem _ hx)) (hb l (List.mem_cons_self ..)) hEqL
      subst hEq
      have hT : rest.contains x = true := (list_contains_nat_iff _ _).mpr hx
      rw [hT] at hnd; cases hnd.1

/-- For typed call arguments matching `checkCallArgTys`, concrete `Loc` args equal `(collectLocArgs svs).map L`. -/
theorem collectConcreteLocs_eq_map {M : Model} {L : Loc → Loc} {st : SymState}
    {ps : List (Ident × Ty)} {svs : List SVal} {vs : List Expr}
    (hTyp : PairwiseRel (fun (p : Ident × Ty) sv =>
      match p.2 with
      | .cell elemTy => ∃ l, sv = .loc l ∧ (∀ ty, locLookup st.cellTys l = some ty → ty = elemTy)
      | ty => isModeledScalarTy ty = true ∧ evalSForm M (.hasTy sv ty)) ps svs)
    (hEv : PairwiseRel (fun sv v => evalSVal M L sv = some v) svs vs) :
    collectConcreteLocs vs = (collectLocArgs svs).map L := by
  induction hTyp generalizing vs with
  | nil =>
    cases hEv; rfl
  | cons hp hrest ih =>
    cases hEv with
    | cons hev hEvRest =>
      rename_i p sv ps' svs' v vs'
      rcases p with ⟨pn, pty⟩
      cases pty with
      | cell elemTy =>
        rcases hp with ⟨l, rfl, _⟩
        simp only [evalSVal, Option.some.injEq] at hev; subst hev
        simp only [collectConcreteLocs, collectLocArgs, List.map, ih hEvRest]
      | _ =>
        rcases hp with ⟨_, hht⟩
        rcases hht with ⟨v0, hev0, hty0⟩
        have hnotloc : ∀ l', v ≠ .loc l' := fun l' => by
          have hv0eq : v = v0 := by
            have : evalSVal M id sv = some v0 := hev0
            rcases valHasTy_eq_lit hty0 with ⟨c, rfl⟩
            have hL := evalSVal_lit_iff_id (L := L).mpr this
            rw [hL] at hev; cases hev; rfl
          subst hv0eq; exact valHasTy_not_loc hty0 l'
        have hsvnotloc : ∀ l', sv ≠ .loc l' := fun l' hEq => by
          subst hEq; simp [evalSVal] at hev; exact hnotloc (L l') hev.symm
        cases sv with
        | loc l' => exact absurd rfl (hsvnotloc l')
        | _ =>
          cases v with
          | loc l' => exact absurd rfl (hnotloc l')
          | _ => simp only [collectConcreteLocs, collectLocArgs, ih hEvRest]

/-- If `l ∈ collectLocArgs svs` and `locLookup st.cellTys l = some ty`, then the matching
    parameter in `ps.zip vs` has type `.cell ty` and concrete argument `.loc (L l)`. -/
theorem callArg_cell_ty_mem {M : Model} {L : Loc → Loc} {st : SymState}
    {ps : List (Ident × Ty)} {svs : List SVal} {vs : List Expr} {l : Loc} {ty : Ty}
    (hTyp : PairwiseRel (fun (p : Ident × Ty) sv =>
      match p.2 with
      | .cell elemTy => ∃ l0, sv = .loc l0 ∧ (∀ ty0, locLookup st.cellTys l0 = some ty0 → ty0 = elemTy)
      | ty0 => isModeledScalarTy ty0 = true ∧ evalSForm M (.hasTy sv ty0)) ps svs)
    (hEv : PairwiseRel (fun sv v => evalSVal M L sv = some v) svs vs)
    (hl : l ∈ collectLocArgs svs) (hct : locLookup st.cellTys l = some ty) :
    ∃ p, (p, Expr.loc (L l)) ∈ ps.zip vs ∧ p.2 = .cell ty := by
  induction hTyp generalizing vs with
  | nil => simp [collectLocArgs] at hl
  | cons hp hrest ih =>
    cases hEv with
    | cons hev hEvRest =>
      rename_i p sv ps' svs' v vs'
      rcases p with ⟨pn, pty⟩
      cases pty with
      | cell elemTy =>
        rcases hp with ⟨l0, rfl, htyEq⟩
        simp only [evalSVal, Option.some.injEq] at hev; subst hev
        simp only [collectLocArgs, List.mem_cons] at hl
        rcases hl with rfl | hl'
        · have hEq : ty = elemTy := htyEq ty hct
          subst hEq
          exact ⟨(pn, .cell ty), List.mem_cons_self .., rfl⟩
        · rcases ih hEvRest hl' with ⟨q, hq, hqty⟩
          exact ⟨q, List.mem_cons_of_mem _ hq, hqty⟩
      | _ =>
        rcases hp with ⟨_, ⟨v0, hev0, hty0⟩⟩
        have hsvnotloc : ∀ l', sv ≠ .loc l' := fun l' hEq => by
          subst hEq; simp [evalSVal] at hev0; subst hev0; exact valHasTy_not_loc hty0 l' rfl
        cases sv with
        | loc l' => exact absurd rfl (hsvnotloc l')
        | lit _ | sym _ | un _ _ | bin _ _ _ | ite _ _ _ | getTag _ =>
          simp only [collectLocArgs] at hl
          rcases ih hEvRest hl with ⟨q, hq, hqty⟩
          exact ⟨q, List.mem_cons_of_mem _ hq, hqty⟩

/-- `assocLookup ((ps.map Prod.fst).zip svs) x = some sv` implies matching concrete arg in `zipParams ps vs`. -/
theorem zipParams_match_of_forall2 {M : Model} {L : Loc → Loc} {m : Nat}
    {ps : List (Ident × Ty)} {svs : List SVal} {vs : List Expr}
    (hEv : PairwiseRel (fun sv v => evalSVal M L sv = some v ∧ svalLocBound m sv) svs vs)
    (hlen : ps.length = svs.length) :
    ∀ x sv, assocLookup ((ps.map Prod.fst).zip svs) x = some sv →
      ∃ v, assocLookup (zipParams ps vs) x = some v ∧ evalSVal M L sv = some v ∧ svalLocBound m sv := by
  induction ps generalizing svs vs with
  | nil => intro x sv hlu; simp [assocLookup] at hlu
  | cons p ps ih =>
    cases hEv with
    | nil => simp at hlen
    | cons h1 hrest =>
      rename_i sv0 v0 svs' vs'
      intro x sv hlu
      change assocLookup ((p.1, sv0) :: (ps.map Prod.fst).zip svs') x = some sv at hlu
      change ∃ v, assocLookup ((p.1, v0) :: zipParams ps vs') x = some v ∧ evalSVal M L sv = some v ∧ svalLocBound m sv
      simp only [assocLookup] at hlu ⊢
      cases hEq : (p.1 == x)
      · simp [hEq] at hlu ⊢
        exact ih hrest (by simpa using hlen) x sv hlu
      · simp [hEq] at hlu ⊢
        subst hlu; exact h1

set_option maxHeartbeats 800000 in
set_option maxRecDepth 2048 in
/-- Step-indexed soundness of `vcgen` for the imperative/cell/loop/intrinsic/modular-call language. -/
theorem vcgen_sound_step {Δ : AdtEnv} {Φ : FunEnv} {env : VcgEnv}
    (hIntr : IntrinsicsOk Φ)
    (bound : Nat) (hCallee : CalleeSound Δ Φ env bound) :
      ∀ {M : Model} {L : Loc → Loc} {st st' : SymState} {ρ : List (Ident × Expr)} {σ : Store} {e : Expr} {sv : SVal},
        ValidModel M →
        StoreClosed σ →
        StateMatches M L st ρ σ →
        vcgen env st e = some (st', sv) →
        ValidObs st'.obs →
        SafeExecN Δ Φ bound (substMany ρ e) σ
          (fun v σ' => StoreClosed σ' ∧
            ∃ M' L', ValidModel M' ∧
              (∀ id < st.nextSym, M' id = M id) ∧
              (∀ k < st.nextLoc, L' k = L k) ∧
              StateMatches M' L' st' ρ σ' ∧
              evalSVal M' L' sv = some v) :=
  go
where
  go {M : Model} {L : Loc → Loc} {st st' : SymState} {ρ : List (Ident × Expr)} {σ : Store}
        {e : Expr} {sv : SVal}
        (hM : ValidModel M) (hσ : StoreClosed σ) (hMatch : StateMatches M L st ρ σ)
        (hvc : vcgen env st e = some (st', sv)) (hObs : ValidObs st'.obs) :
        SafeExecN Δ Φ bound (substMany ρ e) σ
          (fun v σ' => StoreClosed σ' ∧
            ∃ M' L', ValidModel M' ∧
              (∀ id < st.nextSym, M' id = M id) ∧
              (∀ k < st.nextLoc, L' k = L k) ∧
              StateMatches M' L' st' ρ σ' ∧
              evalSVal M' L' sv = some v) := by
      cases e with
      | lit l =>
        simp only [vcgen] at hvc; split at hvc
        · cases hvc; rw [substMany_lit]
          constructor
          · intro k _ σ' hs; rcases stepsN_of_value (.lit l) hs with ⟨_, hEq, _⟩; cases hEq
          · intro k _ v σ' _ hs
            rcases stepsN_of_value (.lit l) hs with ⟨_, rfl, rfl⟩
            exact ⟨hσ, M, L, hM, fun _ _ => rfl, fun _ _ => rfl, hMatch, rfl⟩
        · cases hvc
      | var x =>
        simp only [vcgen] at hvc
        cases hlu : assocLookup st.vars x with
        | none => simp [hlu] at hvc
        | some sv0 =>
          simp [hlu] at hvc; rcases hvc with ⟨rfl, rfl⟩
          rcases hMatch.vars_match x sv0 hlu with ⟨v0, hρx, hev, _⟩
          have hv0 : IsValue v0 := (evalSVal_closed hM hev).1
          rw [substMany_var hMatch.closed_env, hρx]
          constructor
          · intro k _ σ' hs; rcases stepsN_of_value hv0 hs with ⟨_, hEq, _⟩; subst hEq; cases hv0
          · intro k _ v σ' _ hs
            rcases stepsN_of_value hv0 hs with ⟨_, rfl, rfl⟩
            exact ⟨hσ, M, L, hM, fun _ _ => rfl, fun _ _ => rfl, hMatch, hev⟩
      | loc _ => simp [vcgen] at hvc
      | un op e1 =>
        simp only [vcgen] at hvc; split at hvc
        · cases hvc
        · cases h1 : vcgen env st e1 with
          | none => simp [h1] at hvc
          | some r1 =>
            rcases r1 with ⟨st1, sv1⟩; simp [h1] at hvc; rcases hvc with ⟨rfl, rfl⟩
            have ih1 := go hM hσ hMatch h1 hObs
            rw [substMany_un]
            constructor
            · intro k hk σ' hs
              rcases stepsN_un_terminal (Or.inr ⟨_, rfl⟩) hs with ⟨k1, hk1, t, hst1, hEq⟩ | ⟨_, _, _, _, _, _, hEq⟩
              · cases hEq; exact ih1.1 k1 (by omega) σ' hst1
              · cases hEq
            · intro k hk v σ' hv hs
              rcases stepsN_un_terminal (Or.inl hv) hs with ⟨_, _, _, _, hEq⟩ | ⟨k1, hk1, l, l', hst1, hev, rfl⟩
              · subst hEq; cases hv
              · rcases ih1.2 k1 (by omega) (.lit l) σ' (.lit l) hst1 with ⟨hσ', M1, L1, hM1, hag1, hagL1, hMatch1, hev1⟩
                exact ⟨hσ', M1, L1, hM1, hag1, hagL1, hMatch1, by simp [evalSVal, hev1, hev]⟩
      | bin op e1 e2 =>
        by_cases hAnd : op = .and
        · subst hAnd
          simp only [vcgen, ↓reduceIte] at hvc
          cases h1 : vcgen env st e1 with
          | none => simp [h1] at hvc
          | some r1 =>
            rcases r1 with ⟨st1, sv1⟩; simp only [h1] at hvc
            rcases vcgen_wf hMatch.wf h1 with ⟨hs1, hl1, hv1, ho1, hwf1, hb1⟩
            have hlw1 := (vcgen_locBound hMatch.wf hMatch.locWf h1).1
            have hlb1 := (vcgen_locBound hMatch.wf hMatch.locWf h1).2
            cases h2 : vcgen env (withPath st1 (.isTrue sv1)) e2 with
            | none => simp [h2] at hvc
            | some r2 =>
              rcases r2 with ⟨st2, sv2⟩; simp only [h2] at hvc
              split at hvc
              · cases hvc
              · rename_i hlocEq
                simp only [bne_iff_ne, Decidable.not_not] at hlocEq
                cases hvc
                rcases vcgen_wf (symWf_withPath hwf1 (c := .isTrue sv1) hb1) h2 with ⟨hs2, _, _, ho2, hwf2, hb2⟩
                have hlw2 := (vcgen_locBound (symWf_withPath hwf1 (c := .isTrue sv1) hb1) hlw1 h2).1
                have ih1 := go hM hσ hMatch h1 (validObs_mono ho2 hObs)
                rw [substMany_bin]
                constructor
                · intro k hk σ' hs
                  rcases stepsN_and_terminal (Or.inr ⟨_, rfl⟩) hs with
                    ⟨k1, hk1, t, hst1, hEq⟩ | ⟨_, _, _, hEq⟩ | ⟨k1, k2, hlt, σ1, hst1, hst2⟩
                  · cases hEq; exact ih1.1 k1 (by omega) σ' hst1
                  · cases hEq
                  · rcases ih1.2 k1 (by omega) (.lit (.bool true)) σ1 (.lit _) hst1 with ⟨hσ1, M1, L1, hM1, _, _, hMatch1, hev1⟩
                    have hM1' : StateMatches M1 L1 (withPath st1 (.isTrue sv1)) ρ σ1 :=
                      hMatch1.of_eq (symWf_withPath hwf1 (c := .isTrue sv1) hb1) rfl rfl rfl rfl
                        ⟨hMatch1.path_holds, evalSVal_lit_iff_id.mp hev1⟩
                    exact (go hM1 hσ1 hM1' h2 hObs).1 k2 (by omega) σ' hst2
                · intro k hk v σ' hv hs
                  have hwfOut : SymWf ({ nextSym := st2.nextSym, nextLoc := st1.nextLoc, vars := st1.vars, cells := mergeCells sv1 st1.cells st2.cells st1.cells, cellTys := st1.cellTys, path := st1.path, obs := st2.obs } : SymState) := by
                    refine ⟨fun p hp => svalBound_mono hs2 (hwf1.vars_bound p hp), ?_, sformBound_mono hs2 hwf1.path_bound⟩
                    intro p hp
                    rcases List.mem_map.mp hp with ⟨⟨l, svB⟩, hmemB, rfl⟩
                    have hbB := hwf1.cells_bound (l, svB) hmemB
                    refine ⟨hbB.1, svalBound_mono hs2 hb1, ?_, ?_⟩
                    · cases hluT : locLookup st2.cells l with
                      | none => exact svalBound_mono hs2 hbB.2
                      | some svT => exact (hwf2.cells_bound _ (locLookup_mem hluT)).2
                    · cases hlu1 : locLookup st1.cells l with
                      | none => exact svalBound_mono hs2 hbB.2
                      | some sv1l => exact svalBound_mono hs2 (hwf1.cells_bound _ (locLookup_mem hlu1)).2
                  rcases stepsN_and_terminal (Or.inl hv) hs with
                    ⟨_, _, _, _, hEq⟩ | ⟨k1, hk1, hst1, rfl⟩ | ⟨k1, k2, hlt, σ1, hst1, hst2⟩
                  · subst hEq; cases hv
                  · rcases ih1.2 k1 (by omega) (.lit (.bool false)) σ' (.lit _) hst1 with ⟨hσ', M1, L1, hM1, hag1, hagL1, hMatch1, hev1⟩
                    refine ⟨hσ', M1, L1, hM1, hag1, hagL1, ?_, by simp [evalSVal, hev1]⟩
                    refine ⟨hMatch1.closed_env, hwfOut, hMatch1.loc_bound, hMatch1.loc_inj, hMatch1.path_holds, hMatch1.vars_match, ?_, hMatch1.cells_ty⟩
                    intro l sv hlu
                    rcases locLookup_mergeCells hlu with ⟨svB, hluB, rfl⟩
                    rcases hMatch1.cells_match l svB hluB with ⟨v0, hget, hev0, hlb0⟩
                    refine ⟨v0, hget, by simp [evalSVal, hev1, hluB, hev0], ⟨hlb1, ?_, ?_⟩⟩
                    · cases hluT : locLookup st2.cells l with
                      | none => exact hlb0
                      | some svT => exact hlocEq ▸ hlw2.2 l svT hluT
                    · simp [hluB, hlb0]
                  · rcases ih1.2 k1 (by omega) (.lit (.bool true)) σ1 (.lit _) hst1 with ⟨hσ1, M1, L1, hM1, hag1, hagL1, hMatch1, hev1⟩
                    have hM1' : StateMatches M1 L1 (withPath st1 (.isTrue sv1)) ρ σ1 :=
                      hMatch1.of_eq (symWf_withPath hwf1 (c := .isTrue sv1) hb1) rfl rfl rfl rfl
                        ⟨hMatch1.path_holds, evalSVal_lit_iff_id.mp hev1⟩
                    rcases (go hM1 hσ1 hM1' h2 hObs).2 k2 (by omega) v σ' hv hst2 with ⟨hσ', M2, L2, hM2, hag2, hagL2, hMatch2, hev2⟩
                    have hag12 : ∀ id < st.nextSym, M2 id = M id :=
                      fun id hid => (hag2 id (Nat.lt_of_lt_of_le hid hs1)).trans (hag1 id hid)
                    have hagL12 : ∀ k < st.nextLoc, L2 k = L k :=
                      fun k hk => (hagL2 k (Nat.lt_of_lt_of_le hk hl1)).trans (hagL1 k hk)
                    have hev1_M2 : evalSVal M2 L2 sv1 = some (.lit (.bool true)) :=
                      evalSVal_lit_iff_id.mpr ((evalSVal_agree_lt hb1 hag2).trans (evalSVal_lit_iff_id.mp hev1))
                    have hct2 : st2.cellTys = st1.cellTys := by simpa [withPath] using vcgen_cellTys_of_nextLoc_eq (symWf_withPath hwf1 (c := .isTrue sv1) hb1) h2 hlocEq
                    refine ⟨hσ', M2, L2, hM2, hag12, hagL12, ?_, by simp [evalSVal, hev1_M2, hev2]⟩
                    refine ⟨hMatch2.closed_env, hwfOut, hlocEq ▸ hMatch2.loc_bound, hlocEq ▸ hMatch2.loc_inj,
                      (evalSForm_agree_lt hwf1.path_bound hag2).mpr hMatch1.path_holds,
                      fun x svx hlu => by
                        rcases hMatch1.vars_match x svx hlu with ⟨vx, hρx, hevx, hlbx⟩
                        exact ⟨vx, hρx, (evalSVal_loc_agree_lt hlbx hagL2).trans ((evalSVal_agree_lt (hwf1.vars_bound _ (assocLookup_mem hlu)) hag2).trans hevx), hlbx⟩,
                      ?_, by rw [← hct2, ← hlocEq]; exact hMatch2.cells_ty⟩
                    intro l sv hlu
                    rcases locLookup_mergeCells hlu with ⟨svB, hluB, rfl⟩
                    cases hluT : locLookup st2.cells l with
                    | some svT =>
                      rcases hMatch2.cells_match l svT hluT with ⟨v0, hget, hev0, hlb0⟩
                      exact ⟨v0, hget, by simp [evalSVal, hev1_M2, hluT, hev0], ⟨hlb1, hlocEq ▸ hlb0, by simpa [hluB] using hlw1.2 l svB hluB⟩⟩
                    | none =>
                      have hSome := vcgen_preserves_cell_dom (l := l) h2 (by simp [withPath, hluB])
                      rw [hluT] at hSome; cases hSome
        · by_cases hOr : op = .or
          · subst hOr
            simp only [vcgen, reduceCtorEq, ↓reduceIte] at hvc
            cases h1 : vcgen env st e1 with
            | none => simp [h1] at hvc
            | some r1 =>
              rcases r1 with ⟨st1, sv1⟩; simp only [h1] at hvc
              rcases vcgen_wf hMatch.wf h1 with ⟨hs1, hl1, hv1, ho1, hwf1, hb1⟩
              have hlw1 := (vcgen_locBound hMatch.wf hMatch.locWf h1).1
              have hlb1 := (vcgen_locBound hMatch.wf hMatch.locWf h1).2
              cases h2 : vcgen env (withPath st1 (.isFalse sv1)) e2 with
              | none => simp [h2] at hvc
              | some r2 =>
                rcases r2 with ⟨st2, sv2⟩; simp only [h2] at hvc
                split at hvc
                · cases hvc
                · rename_i hlocEq
                  simp only [bne_iff_ne, Decidable.not_not] at hlocEq
                  cases hvc
                  rcases vcgen_wf (symWf_withPath hwf1 (c := .isFalse sv1) hb1) h2 with ⟨hs2, _, _, ho2, hwf2, hb2⟩
                  have hlw2 := (vcgen_locBound (symWf_withPath hwf1 (c := .isFalse sv1) hb1) hlw1 h2).1
                  have ih1 := go hM hσ hMatch h1 (validObs_mono ho2 hObs)
                  rw [substMany_bin]
                  constructor
                  · intro k hk σ' hs
                    rcases stepsN_or_terminal (Or.inr ⟨_, rfl⟩) hs with
                      ⟨k1, hk1, t, hst1, hEq⟩ | ⟨_, _, _, hEq⟩ | ⟨k1, k2, hlt, σ1, hst1, hst2⟩
                    · cases hEq; exact ih1.1 k1 (by omega) σ' hst1
                    · cases hEq
                    · rcases ih1.2 k1 (by omega) (.lit (.bool false)) σ1 (.lit _) hst1 with ⟨hσ1, M1, L1, hM1, _, _, hMatch1, hev1⟩
                      have hM1' : StateMatches M1 L1 (withPath st1 (.isFalse sv1)) ρ σ1 :=
                        hMatch1.of_eq (symWf_withPath hwf1 (c := .isFalse sv1) hb1) rfl rfl rfl rfl
                          ⟨hMatch1.path_holds, evalSVal_lit_iff_id.mp hev1⟩
                      exact (go hM1 hσ1 hM1' h2 hObs).1 k2 (by omega) σ' hst2
                  · intro k hk v σ' hv hs
                    have hwfOut : SymWf ({ nextSym := st2.nextSym, nextLoc := st1.nextLoc, vars := st1.vars, cells := mergeCells sv1 st1.cells st1.cells st2.cells, cellTys := st1.cellTys, path := st1.path, obs := st2.obs } : SymState) := by
                      refine ⟨fun p hp => svalBound_mono hs2 (hwf1.vars_bound p hp), ?_, sformBound_mono hs2 hwf1.path_bound⟩
                      intro p hp
                      rcases List.mem_map.mp hp with ⟨⟨l, svB⟩, hmemB, rfl⟩
                      have hbB := hwf1.cells_bound (l, svB) hmemB
                      refine ⟨hbB.1, svalBound_mono hs2 hb1, ?_, ?_⟩
                      · cases hlu1 : locLookup st1.cells l with
                        | none => exact svalBound_mono hs2 hbB.2
                        | some sv1l => exact svalBound_mono hs2 (hwf1.cells_bound _ (locLookup_mem hlu1)).2
                      · cases hluE : locLookup st2.cells l with
                        | none => exact svalBound_mono hs2 hbB.2
                        | some svE => exact (hwf2.cells_bound _ (locLookup_mem hluE)).2
                    rcases stepsN_or_terminal (Or.inl hv) hs with
                      ⟨_, _, _, _, hEq⟩ | ⟨k1, hk1, hst1, rfl⟩ | ⟨k1, k2, hlt, σ1, hst1, hst2⟩
                    · subst hEq; cases hv
                    · rcases ih1.2 k1 (by omega) (.lit (.bool true)) σ' (.lit _) hst1 with ⟨hσ', M1, L1, hM1, hag1, hagL1, hMatch1, hev1⟩
                      refine ⟨hσ', M1, L1, hM1, hag1, hagL1, ?_, by simp [evalSVal, hev1]⟩
                      refine ⟨hMatch1.closed_env, hwfOut, hMatch1.loc_bound, hMatch1.loc_inj, hMatch1.path_holds, hMatch1.vars_match, ?_, hMatch1.cells_ty⟩
                      intro l sv hlu
                      rcases locLookup_mergeCells hlu with ⟨svB, hluB, rfl⟩
                      rcases hMatch1.cells_match l svB hluB with ⟨v0, hget, hev0, hlb0⟩
                      refine ⟨v0, hget, by simp [evalSVal, hev1, hluB, hev0], ⟨hlb1, ?_, ?_⟩⟩
                      · simp [hluB, hlb0]
                      · cases hluE : locLookup st2.cells l with
                        | none => exact hlb0
                        | some svE => exact hlocEq ▸ hlw2.2 l svE hluE
                    · rcases ih1.2 k1 (by omega) (.lit (.bool false)) σ1 (.lit _) hst1 with ⟨hσ1, M1, L1, hM1, hag1, hagL1, hMatch1, hev1⟩
                      have hM1' : StateMatches M1 L1 (withPath st1 (.isFalse sv1)) ρ σ1 :=
                        hMatch1.of_eq (symWf_withPath hwf1 (c := .isFalse sv1) hb1) rfl rfl rfl rfl
                          ⟨hMatch1.path_holds, evalSVal_lit_iff_id.mp hev1⟩
                      rcases (go hM1 hσ1 hM1' h2 hObs).2 k2 (by omega) v σ' hv hst2 with ⟨hσ', M2, L2, hM2, hag2, hagL2, hMatch2, hev2⟩
                      have hag12 : ∀ id < st.nextSym, M2 id = M id :=
                        fun id hid => (hag2 id (Nat.lt_of_lt_of_le hid hs1)).trans (hag1 id hid)
                      have hagL12 : ∀ k < st.nextLoc, L2 k = L k :=
                        fun k hk => (hagL2 k (Nat.lt_of_lt_of_le hk hl1)).trans (hagL1 k hk)
                      have hev1_M2 : evalSVal M2 L2 sv1 = some (.lit (.bool false)) :=
                        evalSVal_lit_iff_id.mpr ((evalSVal_agree_lt hb1 hag2).trans (evalSVal_lit_iff_id.mp hev1))
                      have hct2 : st2.cellTys = st1.cellTys := by simpa [withPath] using vcgen_cellTys_of_nextLoc_eq (symWf_withPath hwf1 (c := .isFalse sv1) hb1) h2 hlocEq
                      refine ⟨hσ', M2, L2, hM2, hag12, hagL12, ?_, by simp [evalSVal, hev1_M2, hev2]⟩
                      refine ⟨hMatch2.closed_env, hwfOut, hlocEq ▸ hMatch2.loc_bound, hlocEq ▸ hMatch2.loc_inj,
                        (evalSForm_agree_lt hwf1.path_bound hag2).mpr hMatch1.path_holds,
                        fun x svx hlu => by
                          rcases hMatch1.vars_match x svx hlu with ⟨vx, hρx, hevx, hlbx⟩
                          exact ⟨vx, hρx, (evalSVal_loc_agree_lt hlbx hagL2).trans ((evalSVal_agree_lt (hwf1.vars_bound _ (assocLookup_mem hlu)) hag2).trans hevx), hlbx⟩,
                        ?_, by rw [← hct2, ← hlocEq]; exact hMatch2.cells_ty⟩
                      intro l sv hlu
                      rcases locLookup_mergeCells hlu with ⟨svB, hluB, rfl⟩
                      cases hluE : locLookup st2.cells l with
                      | some svE =>
                        rcases hMatch2.cells_match l svE hluE with ⟨v0, hget, hev0, hlb0⟩
                        exact ⟨v0, hget, by simp [evalSVal, hev1_M2, hluE, hev0], ⟨hlb1, by simpa [hluB] using hlw1.2 l svB hluB, hlocEq ▸ hlb0⟩⟩
                      | none =>
                        have hSome := vcgen_preserves_cell_dom (l := l) h2 (by simp [withPath, hluB])
                        rw [hluE] at hSome; cases hSome
          · simp only [vcgen, hAnd, hOr, ↓reduceIte] at hvc
            split at hvc
            · cases hvc
            · cases h1 : vcgen env st e1 with
              | none => simp [h1] at hvc
              | some r1 =>
                rcases r1 with ⟨st1, sv1⟩; simp only [h1] at hvc
                rcases vcgen_wf hMatch.wf h1 with ⟨hs1, hl1, _, _, hwf1, hb1⟩
                cases h2 : vcgen env st1 e2 with
                | none => simp [h2] at hvc
                | some r2 =>
                  rcases r2 with ⟨st2, sv2⟩; simp only [h2] at hvc; cases hvc
                  rcases vcgen_wf hwf1 h2 with ⟨hs2, _, _, ho2, hwf2, _⟩
                  have hObs2 : ValidObs st2.obs := by
                    intro f hf; apply hObs; split
                    · exact List.mem_cons_of_mem _ hf
                    · exact hf
                  have ih1 := go hM hσ hMatch h1 (validObs_mono ho2 hObs2)
                  rw [substMany_bin]
                  constructor
                  · intro k hk σ' hs
                    rcases stepsN_bin_strict_terminal hAnd hOr (Or.inr ⟨_, rfl⟩) hs with
                      ⟨k1, hk1, t, hst1, hEq⟩ |
                      ⟨k1, k2, hlt, v1, σ1, t, hv1', hst1, hst2, hEq⟩ |
                      ⟨k1, k2, hlt, l1, l2, σ1, r, hst1, hst2, hev, hres⟩
                    · cases hEq; exact ih1.1 k1 (by omega) σ' hst1
                    · cases hEq
                      rcases ih1.2 k1 (by omega) v1 σ1 hv1' hst1 with ⟨hσ1, M1, L1, hM1, _, _, hMatch1, _⟩
                      exact (go hM1 hσ1 hMatch1 h2 hObs2).1 k2 (by omega) σ' hst2
                    · rcases ih1.2 k1 (by omega) (.lit l1) σ1 (.lit _) hst1 with ⟨hσ1, M1, L1, hM1, _, _, hMatch1, _⟩
                      rcases (go hM1 hσ1 hMatch1 h2 hObs2).2 k2 (by omega) (.lit l2) σ' (.lit _) hst2 with ⟨_, M2, L2, hM2, _, _, hMatch2, hev2⟩
                      cases r with
                      | val _ => cases hres
                      | trap t =>
                        cases hres
                        refine evalBinOp_no_divByZero (evalSVal_lit_iff_id.mp hev2) ?_ hev
                        intro hdiv
                        have hObMem : SForm.imp st2.path (.neZero op sv2) ∈ (if isDivOp op then emitOb st2 (.neZero op sv2) else st2).obs := by
                          simp [hdiv, emitOb]
                        exact hObs _ hObMem M2 hM2 hMatch2.path_holds
                  · intro k hk v σ' hv hs
                    rcases stepsN_bin_strict_terminal hAnd hOr (Or.inl hv) hs with
                      ⟨_, _, _, _, hEq⟩ |
                      ⟨_, _, _, _, _, _, _, _, _, hEq⟩ |
                      ⟨k1, k2, hlt, l1, l2, σ1, r, hst1, hst2, hev, hres⟩
                    · subst hEq; cases hv
                    · subst hEq; cases hv
                    · cases r with
                      | trap _ => subst hres; cases hv
                      | val l' =>
                        subst hres
                        rcases ih1.2 k1 (by omega) (.lit l1) σ1 (.lit _) hst1 with ⟨hσ1, M1, L1, hM1, hag1, hagL1, hMatch1, hev1⟩
                        rcases (go hM1 hσ1 hMatch1 h2 hObs2).2 k2 (by omega) (.lit l2) σ' (.lit _) hst2 with ⟨hσ', M2, L2, hM2, hag2, hagL2, hMatch2, hev2⟩
                        have hag12 : ∀ id < st.nextSym, M2 id = M id :=
                          fun id hid => (hag2 id (Nat.lt_of_lt_of_le hid hs1)).trans (hag1 id hid)
                        have hagL12 : ∀ k < st.nextLoc, L2 k = L k :=
                          fun k hk => (hagL2 k (Nat.lt_of_lt_of_le hk hl1)).trans (hagL1 k hk)
                        have hev1' : evalSVal M2 L2 sv1 = some (.lit l1) :=
                          evalSVal_lit_iff_id.mpr ((evalSVal_agree_lt hb1 hag2).trans (evalSVal_lit_iff_id.mp hev1))
                        refine ⟨hσ', M2, L2, hM2, hag12, hagL12, ?_, by simp [evalSVal, hev1', hev2, hev]⟩
                        split
                        · exact hMatch2.of_eq ⟨hwf2.vars_bound, hwf2.cells_bound, hwf2.path_bound⟩ rfl rfl rfl rfl hMatch2.path_holds
                        · exact hMatch2
      | let_ x e1 e2 =>
        simp only [vcgen] at hvc
        cases h1 : vcgen env st e1 with
        | none => simp [h1] at hvc
        | some r1 =>
          rcases r1 with ⟨st1, sv1⟩; simp only [h1] at hvc
          rcases vcgen_wf hMatch.wf h1 with ⟨hs1, hl1, hv1, ho1, hwf1, hb1⟩
          have hlb1 := (vcgen_locBound hMatch.wf hMatch.locWf h1).2
          have hwfIn : SymWf { st1 with vars := (x, sv1) :: st1.vars } :=
            ⟨fun p hp => by rcases List.mem_cons.mp hp with rfl | hp'; exact hb1; exact hwf1.vars_bound p hp',
             hwf1.cells_bound, hwf1.path_bound⟩
          cases h2 : vcgen env { st1 with vars := (x, sv1) :: st1.vars } e2 with
          | none => simp [h2] at hvc
          | some r2 =>
            rcases r2 with ⟨st2, sv2⟩; simp [h2] at hvc; rcases hvc with ⟨rfl, rfl⟩
            rcases vcgen_wf hwfIn h2 with ⟨hs2, hl2, _, ho2, hwf2, _⟩
            have ih1 := go hM hσ hMatch h1 (validObs_mono ho2 hObs)
            rw [substMany_let]
            have hwfOut : SymWf { st2 with vars := st1.vars } :=
              ⟨fun p hp => svalBound_mono hs2 (hwf1.vars_bound p hp), hwf2.cells_bound, hwf2.path_bound⟩
            constructor
            · intro k hk σ' hs
              rcases stepsN_let_terminal (Or.inr ⟨_, rfl⟩) hs with
                ⟨k1, hk1, t, hst1, hEq⟩ | ⟨k1, k2, hlt, v1, σ1, hv1', hst1, hst2⟩
              · cases hEq; exact ih1.1 k1 (by omega) σ' hst1
              · rcases ih1.2 k1 (by omega) v1 σ1 hv1' hst1 with ⟨hσ1, M1, L1, hM1, _, _, hMatch1, hev1⟩
                have hcl1 : freeVars v1 = [] := (evalSVal_closed hM1 hev1).2
                rw [subst_substMany_remove hMatch1.closed_env hcl1 e2] at hst2
                have hM2In : StateMatches M1 L1 { st1 with vars := (x, sv1) :: st1.vars } ((x, v1) :: ρ) σ1 :=
                  { closed_env := fun p hp => by rcases List.mem_cons.mp hp with rfl | hp'; exact ⟨hv1', hcl1⟩; exact hMatch1.closed_env p hp',
                    wf := hwfIn, loc_bound := hMatch1.loc_bound, loc_inj := hMatch1.loc_inj,
                    path_holds := hMatch1.path_holds,
                    vars_match := fun y svy hlu => by
                      simp only [assocLookup] at hlu ⊢
                      cases hxy : (x == y)
                      · simp [hxy] at hlu ⊢; exact hMatch1.vars_match y svy hlu
                      · simp [hxy] at hlu ⊢; subst hlu; exact ⟨hev1, hlb1⟩,
                    cells_match := hMatch1.cells_match, cells_ty := hMatch1.cells_ty }
                exact (go hM1 hσ1 hM2In h2 hObs).1 k2 (by omega) σ' hst2
            · intro k hk v σ' hv hs
              rcases stepsN_let_terminal (Or.inl hv) hs with
                ⟨_, _, _, _, hEq⟩ | ⟨k1, k2, hlt, v1, σ1, hv1', hst1, hst2⟩
              · subst hEq; cases hv
              · rcases ih1.2 k1 (by omega) v1 σ1 hv1' hst1 with ⟨hσ1, M1, L1, hM1, hag1, hagL1, hMatch1, hev1⟩
                have hcl1 : freeVars v1 = [] := (evalSVal_closed hM1 hev1).2
                rw [subst_substMany_remove hMatch1.closed_env hcl1 e2] at hst2
                have hM2In : StateMatches M1 L1 { st1 with vars := (x, sv1) :: st1.vars } ((x, v1) :: ρ) σ1 :=
                  { closed_env := fun p hp => by rcases List.mem_cons.mp hp with rfl | hp'; exact ⟨hv1', hcl1⟩; exact hMatch1.closed_env p hp',
                    wf := hwfIn, loc_bound := hMatch1.loc_bound, loc_inj := hMatch1.loc_inj,
                    path_holds := hMatch1.path_holds,
                    vars_match := fun y svy hlu => by
                      simp only [assocLookup] at hlu ⊢
                      cases hxy : (x == y)
                      · simp [hxy] at hlu ⊢; exact hMatch1.vars_match y svy hlu
                      · simp [hxy] at hlu ⊢; subst hlu; exact ⟨hev1, hlb1⟩,
                    cells_match := hMatch1.cells_match, cells_ty := hMatch1.cells_ty }
                rcases (go hM1 hσ1 hM2In h2 hObs).2 k2 (by omega) v σ' hv hst2 with ⟨hσ', M2, L2, hM2, hag2, hagL2, hMatch2, hev2⟩
                have hag12 : ∀ id < st.nextSym, M2 id = M id :=
                  fun id hid => (hag2 id (Nat.lt_of_lt_of_le hid hs1)).trans (hag1 id hid)
                have hagL12 : ∀ k < st.nextLoc, L2 k = L k :=
                  fun k hk => (hagL2 k (Nat.lt_of_lt_of_le hk hl1)).trans (hagL1 k hk)
                refine ⟨hσ', M2, L2, hM2, hag12, hagL12, ?_, hev2⟩
                exact ⟨hMatch.closed_env, hwfOut, hMatch2.loc_bound, hMatch2.loc_inj, hMatch2.path_holds,
                  (fun y svy hlu => by
                    rcases hMatch1.vars_match y svy hlu with ⟨vy, hρy, hevy, hlby⟩
                    exact ⟨vy, hρy, (evalSVal_loc_agree_lt hlby hagL2).trans ((evalSVal_agree_lt (hwf1.vars_bound _ (assocLookup_mem hlu)) hag2).trans hevy), svalLocBound_mono hl2 hlby⟩),
                  hMatch2.cells_match, hMatch2.cells_ty⟩
      | block es =>
        simp only [vcgen] at hvc
        rw [substMany_block]
        exact goBlock hM hσ hMatch hvc hObs
      | if_ c t e =>
        simp only [vcgen] at hvc
        cases h1 : vcgen env st c with
        | none => simp [h1] at hvc
        | some r1 =>
          rcases r1 with ⟨st1, svc⟩; simp only [h1] at hvc
          rcases vcgen_wf hMatch.wf h1 with ⟨hs1, hl1, hv1, ho1, hwf1, hbc⟩
          have hlw1 := (vcgen_locBound hMatch.wf hMatch.locWf h1).1
          have hlbc := (vcgen_locBound hMatch.wf hMatch.locWf h1).2
          cases hT : vcgen env (withPath st1 (.isTrue svc)) t with
          | none => simp [hT] at hvc
          | some rT =>
            rcases rT with ⟨stT, svT⟩; simp only [hT] at hvc
            rcases vcgen_wf (symWf_withPath hwf1 (c := .isTrue svc) hbc) hT with ⟨hsT, _, _, hoT, hwfT, hbT⟩
            have hlwT := (vcgen_locBound (symWf_withPath hwf1 (c := .isTrue svc) hbc) hlw1 hT).1
            have hwfEIn : SymWf ({ nextSym := stT.nextSym, nextLoc := st1.nextLoc, vars := st1.vars, cells := st1.cells, cellTys := st1.cellTys, path := .and st1.path (.isFalse svc), obs := stT.obs } : SymState) :=
              ⟨fun p hp => svalBound_mono hsT (hwf1.vars_bound p hp),
               fun p hp => ⟨(hwf1.cells_bound p hp).1, svalBound_mono hsT (hwf1.cells_bound p hp).2⟩,
               ⟨sformBound_mono hsT hwf1.path_bound, svalBound_mono hsT hbc⟩⟩
            cases hE : vcgen env ({ nextSym := stT.nextSym, nextLoc := st1.nextLoc, vars := st1.vars, cells := st1.cells, cellTys := st1.cellTys, path := .and st1.path (.isFalse svc), obs := stT.obs } : SymState) e with
            | none => simp [hE] at hvc
            | some rE =>
              rcases rE with ⟨stE, svE⟩; simp only [hE] at hvc
              split at hvc
              · cases hvc
              · rename_i hlocEqs
                simp only [Bool.or_eq_true, bne_iff_ne, not_or, Decidable.not_not] at hlocEqs
                rcases hlocEqs with ⟨hlocT, hlocE⟩
                cases hvc
                rcases vcgen_wf hwfEIn hE with ⟨hsE, _, _, hoE, hwfE, hbE⟩
                have hlwE := (vcgen_locBound hwfEIn hlw1 hE).1
                have hObsT : ValidObs stT.obs := validObs_mono hoE hObs
                have ihC := go hM hσ hMatch h1 (validObs_mono hoT hObsT)
                have hsTE : st1.nextSym ≤ stE.nextSym := Nat.le_trans hsT hsE
                have hwfOut : SymWf ({ nextSym := stE.nextSym, nextLoc := st1.nextLoc, vars := st1.vars, cells := mergeCells svc st1.cells stT.cells stE.cells, cellTys := st1.cellTys, path := st1.path, obs := stE.obs } : SymState) := by
                  refine ⟨fun p hp => svalBound_mono hsTE (hwf1.vars_bound p hp), ?_, sformBound_mono hsTE hwf1.path_bound⟩
                  intro p hp
                  rcases List.mem_map.mp hp with ⟨⟨l, svB⟩, hmemB, rfl⟩
                  have hbB := hwf1.cells_bound (l, svB) hmemB
                  refine ⟨hbB.1, svalBound_mono hsTE hbc, ?_, ?_⟩
                  · cases hluT : locLookup stT.cells l with
                    | none => exact svalBound_mono hsTE hbB.2
                    | some svTl => exact svalBound_mono hsE (hwfT.cells_bound _ (locLookup_mem hluT)).2
                  · cases hluE : locLookup stE.cells l with
                    | none => exact svalBound_mono hsTE hbB.2
                    | some svEl => exact (hwfE.cells_bound _ (locLookup_mem hluE)).2
                rw [substMany_if]
                constructor
                · intro k hk σ' hs
                  rcases stepsN_if_terminal (Or.inr ⟨_, rfl⟩) hs with
                    ⟨k1, hk1, tr, hst1, hEq⟩ |
                    ⟨k1, k2, hlt, σ1, hst1, hst2⟩ |
                    ⟨k1, k2, hlt, σ1, hst1, hst2⟩
                  · cases hEq; exact ihC.1 k1 (by omega) σ' hst1
                  · rcases ihC.2 k1 (by omega) (.lit (.bool true)) σ1 (.lit _) hst1 with ⟨hσ1, M1, L1, hM1, _, _, hMatch1, hevC⟩
                    have hMT : StateMatches M1 L1 (withPath st1 (.isTrue svc)) ρ σ1 :=
                      hMatch1.of_eq (symWf_withPath hwf1 (c := .isTrue svc) hbc) rfl rfl rfl rfl
                        ⟨hMatch1.path_holds, evalSVal_lit_iff_id.mp hevC⟩
                    exact (go hM1 hσ1 hMT hT hObsT).1 k2 (by omega) σ' hst2
                  · rcases ihC.2 k1 (by omega) (.lit (.bool false)) σ1 (.lit _) hst1 with ⟨hσ1, M1, L1, hM1, _, _, hMatch1, hevC⟩
                    have hME : StateMatches M1 L1 ({ nextSym := stT.nextSym, nextLoc := st1.nextLoc, vars := st1.vars, cells := st1.cells, cellTys := st1.cellTys, path := .and st1.path (.isFalse svc), obs := stT.obs } : SymState) ρ σ1 :=
                      hMatch1.of_eq hwfEIn rfl rfl rfl rfl ⟨hMatch1.path_holds, evalSVal_lit_iff_id.mp hevC⟩
                    exact (go hM1 hσ1 hME hE hObs).1 k2 (by omega) σ' hst2
                · intro k hk v σ' hv hs
                  rcases stepsN_if_terminal (Or.inl hv) hs with
                    ⟨_, _, _, _, hEq⟩ |
                    ⟨k1, k2, hlt, σ1, hst1, hst2⟩ |
                    ⟨k1, k2, hlt, σ1, hst1, hst2⟩
                  · subst hEq; cases hv
                  · rcases ihC.2 k1 (by omega) (.lit (.bool true)) σ1 (.lit _) hst1 with ⟨hσ1, M1, L1, hM1, hag1, hagL1, hMatch1, hevC⟩
                    have hMT : StateMatches M1 L1 (withPath st1 (.isTrue svc)) ρ σ1 :=
                      hMatch1.of_eq (symWf_withPath hwf1 (c := .isTrue svc) hbc) rfl rfl rfl rfl
                        ⟨hMatch1.path_holds, evalSVal_lit_iff_id.mp hevC⟩
                    rcases (go hM1 hσ1 hMT hT hObsT).2 k2 (by omega) v σ' hv hst2 with ⟨hσ', M2, L2, hM2, hag2, hagL2, hMatch2, hevT⟩
                    have hag12 : ∀ id < st.nextSym, M2 id = M id :=
                      fun id hid => (hag2 id (Nat.lt_of_lt_of_le hid hs1)).trans (hag1 id hid)
                    have hagL12 : ∀ k < st.nextLoc, L2 k = L k :=
                      fun k hk => (hagL2 k (Nat.lt_of_lt_of_le hk hl1)).trans (hagL1 k hk)
                    have hevC' : evalSVal M2 L2 svc = some (.lit (.bool true)) :=
                      evalSVal_lit_iff_id.mpr ((evalSVal_agree_lt hbc hag2).trans (evalSVal_lit_iff_id.mp hevC))
                    have hctT : stT.cellTys = st1.cellTys := by simpa [withPath] using vcgen_cellTys_of_nextLoc_eq (symWf_withPath hwf1 (c := .isTrue svc) hbc) hT hlocT
                    refine ⟨hσ', M2, L2, hM2, hag12, hagL12, ?_, by simp [evalSVal, hevC', hevT]⟩
                    refine ⟨hMatch2.closed_env, hwfOut, hlocT ▸ hMatch2.loc_bound, hlocT ▸ hMatch2.loc_inj,
                      (evalSForm_agree_lt hwf1.path_bound hag2).mpr hMatch1.path_holds,
                      fun x svx hlu => by
                        rcases hMatch1.vars_match x svx hlu with ⟨vx, hρx, hevx, hlbx⟩
                        exact ⟨vx, hρx, (evalSVal_loc_agree_lt hlbx hagL2).trans ((evalSVal_agree_lt (hwf1.vars_bound _ (assocLookup_mem hlu)) hag2).trans hevx), hlbx⟩,
                      ?_, by rw [← hctT, ← hlocT]; exact hMatch2.cells_ty⟩
                    intro l sv hlu
                    rcases locLookup_mergeCells hlu with ⟨svB, hluB, rfl⟩
                    cases hluT : locLookup stT.cells l with
                    | some svTl =>
                      rcases hMatch2.cells_match l svTl hluT with ⟨v0, hget, hev0, hlb0⟩
                      refine ⟨v0, hget, by simp [evalSVal, hevC', hluT, hev0], ⟨hlbc, hlocT ▸ hlb0, ?_⟩⟩
                      cases hluE : locLookup stE.cells l with
                      | none => exact hlw1.2 l svB hluB
                      | some svEl => exact hlocE ▸ hlwE.2 l svEl hluE
                    | none =>
                      have hSome := vcgen_preserves_cell_dom (l := l) hT (by simp [withPath, hluB])
                      rw [hluT] at hSome; cases hSome
                  · rcases ihC.2 k1 (by omega) (.lit (.bool false)) σ1 (.lit _) hst1 with ⟨hσ1, M1, L1, hM1, hag1, hagL1, hMatch1, hevC⟩
                    have hME : StateMatches M1 L1 ({ nextSym := stT.nextSym, nextLoc := st1.nextLoc, vars := st1.vars, cells := st1.cells, cellTys := st1.cellTys, path := .and st1.path (.isFalse svc), obs := stT.obs } : SymState) ρ σ1 :=
                      hMatch1.of_eq hwfEIn rfl rfl rfl rfl ⟨hMatch1.path_holds, evalSVal_lit_iff_id.mp hevC⟩
                    rcases (go hM1 hσ1 hME hE hObs).2 k2 (by omega) v σ' hv hst2 with ⟨hσ', M2, L2, hM2, hag2, hagL2, hMatch2, hevE⟩
                    have hag12 : ∀ id < st.nextSym, M2 id = M id :=
                      fun id hid => (hag2 id (Nat.lt_of_lt_of_le (Nat.lt_of_lt_of_le hid hs1) hsT)).trans (hag1 id hid)
                    have hagL12 : ∀ k < st.nextLoc, L2 k = L k :=
                      fun k hk => (hagL2 k (Nat.lt_of_lt_of_le hk hl1)).trans (hagL1 k hk)
                    have hag1_M2 : ∀ id < st1.nextSym, M2 id = M1 id :=
                      fun id hid => hag2 id (Nat.lt_of_lt_of_le hid hsT)
                    have hevC' : evalSVal M2 L2 svc = some (.lit (.bool false)) :=
                      evalSVal_lit_iff_id.mpr ((evalSVal_agree_lt hbc hag1_M2).trans (evalSVal_lit_iff_id.mp hevC))
                    have hctE : stE.cellTys = st1.cellTys := by simpa using vcgen_cellTys_of_nextLoc_eq hwfEIn hE hlocE
                    refine ⟨hσ', M2, L2, hM2, hag12, hagL12, ?_, by simp [evalSVal, hevC', hevE]⟩
                    refine ⟨hMatch2.closed_env, hwfOut, hlocE ▸ hMatch2.loc_bound, hlocE ▸ hMatch2.loc_inj,
                      (evalSForm_agree_lt hwf1.path_bound hag1_M2).mpr hMatch1.path_holds,
                      fun x svx hlu => by
                        rcases hMatch1.vars_match x svx hlu with ⟨vx, hρx, hevx, hlbx⟩
                        exact ⟨vx, hρx, (evalSVal_loc_agree_lt hlbx hagL2).trans ((evalSVal_agree_lt (hwf1.vars_bound _ (assocLookup_mem hlu)) hag1_M2).trans hevx), hlbx⟩,
                      ?_, by rw [← hctE, ← hlocE]; exact hMatch2.cells_ty⟩
                    intro l sv hlu
                    rcases locLookup_mergeCells hlu with ⟨svB, hluB, rfl⟩
                    cases hluE : locLookup stE.cells l with
                    | some svEl =>
                      rcases hMatch2.cells_match l svEl hluE with ⟨v0, hget, hev0, hlb0⟩
                      refine ⟨v0, hget, by simp [evalSVal, hevC', hluE, hev0], ⟨hlbc, ?_, hlocE ▸ hlb0⟩⟩
                      cases hluT : locLookup stT.cells l with
                      | none => exact hlw1.2 l svB hluB
                      | some svTl => exact hlocT ▸ hlwT.2 l svTl hluT
                    | none =>
                      have hSome := vcgen_preserves_cell_dom (l := l) hE (by simp [hluB])
                      rw [hluE] at hSome; cases hSome
      | cellNew e1 =>
        simp only [vcgen] at hvc
        cases h1 : vcgen env st e1 with
        | none => simp [h1] at hvc
        | some r1 =>
          rcases r1 with ⟨st1, sv1⟩; simp only [h1] at hvc
          cases hty : inferSValTy st1 sv1 with
          | none => simp [hty] at hvc
          | some elemTy =>
            simp only [hty] at hvc; split at hvc
            · cases hvc
            · rename_i hModTy
              simp only [Bool.not_eq_true', Bool.not_eq_false] at hModTy
              rcases hvc with ⟨rfl, rfl⟩
              rcases vcgen_wf hMatch.wf h1 with ⟨hs1, hl1, hv1, ho1, hwf1, hb1⟩
              have hlb1 := (vcgen_locBound hMatch.wf hMatch.locWf h1).2
              have hObs1 : ValidObs st1.obs :=
                validObs_mono (fun _ hf => List.mem_cons_of_mem _ hf) (by simpa [emitOb] using hObs)
              have ih1 := go hM hσ hMatch h1 hObs1
              rw [substMany_cellNew]
              constructor
              · intro k hk σ' hs
                rcases stepsN_cellNew_terminal (Or.inr ⟨_, rfl⟩) hs with ⟨k1, hk1, tr, hst1, hEq⟩ | ⟨_, _, _, _, _, _, hEq, _⟩
                · cases hEq; exact ih1.1 k1 (by omega) σ' hst1
                · cases hEq
              · intro k hk v σ' hv hs
                rcases stepsN_cellNew_terminal (Or.inl hv) hs with ⟨_, _, _, _, hEq⟩ | ⟨k1, hk1, v1, σ1, hv1', hst1, rfl, rfl⟩
                · subst hEq; cases hv
                · rcases ih1.2 k1 (by omega) v1 σ1 hv1' hst1 with ⟨hσ1, M1, L1, hM1, hag1, hagL1, hMatch1, hev1⟩
                  have hcl1 : freeVars v1 = [] := (evalSVal_closed hM1 hev1).2
                  have hvt1 : valHasTy v1 elemTy := by
                    have hObTy := hObs _ (List.mem_cons_self ..) M1 hM1 hMatch1.path_holds
                    rcases hObTy with ⟨w, hwId, hwTy⟩
                    rcases valHasTy_lit_of_modeled hModTy hwTy with ⟨c, rfl⟩
                    have hwL : evalSVal M1 L1 sv1 = some (.lit c) := evalSVal_lit_iff_id.mpr hwId
                    rw [hev1] at hwL; cases hwL; exact hwTy
                  let L' : Loc → Loc := fun k => if k == st1.nextLoc then σ1.length else L1 k
                  have hL'lt : ∀ k < st1.nextLoc, L' k = L1 k := fun k hk => by
                    dsimp only [L']; rw [beq_false_of_ne (Nat.ne_of_lt hk)]; rfl
                  have hagL' : ∀ k < st.nextLoc, L' k = L k := fun k hk =>
                    (hL'lt k (Nat.lt_of_lt_of_le hk hl1)).trans (hagL1 k hk)
                  refine ⟨storeClosed_append hσ1 hv1' hcl1, M1, L', hM1, hag1, hagL', ?_, by simp [evalSVal, L']⟩
                  refine ⟨hMatch1.closed_env, ?_, ?_, ?_, hMatch1.path_holds, ?_, ?_, ?_⟩
                  · refine ⟨hwf1.vars_bound, ?_, hwf1.path_bound⟩
                    intro p hp; rcases List.mem_cons.mp hp with rfl | hp'
                    · exact ⟨Nat.lt_succ_self _, hb1⟩
                    · exact ⟨Nat.lt_succ_of_lt (hwf1.cells_bound p hp').1, (hwf1.cells_bound p hp').2⟩
                  · intro k hk
                    simp only [emitOb_nextLoc] at hk
                    by_cases hEq : k = st1.nextLoc
                    · subst hEq; simp [L']
                    · have hlt : k < st1.nextLoc := by omega
                      rw [hL'lt k hlt]; simp; exact Nat.lt_succ_of_lt (hMatch1.loc_bound k hlt)
                  · intro k1 k2 hk1 hk2 hEqL
                    simp only [emitOb_nextLoc] at hk1 hk2
                    by_cases h1Eq : k1 = st1.nextLoc <;> by_cases h2Eq : k2 = st1.nextLoc
                    · exact h1Eq.trans h2Eq.symm
                    · subst h1Eq
                      have hlt2 : k2 < st1.nextLoc := by omega
                      rw [hL'lt k2 hlt2] at hEqL
                      have hEqL' : σ1.length = L1 k2 := by simpa [L'] using hEqL
                      exact absurd hEqL' (Nat.ne_of_gt (hMatch1.loc_bound k2 hlt2))
                    · subst h2Eq
                      have hlt1 : k1 < st1.nextLoc := by omega
                      rw [hL'lt k1 hlt1] at hEqL
                      have hEqL' : L1 k1 = σ1.length := by simpa [L'] using hEqL
                      exact absurd hEqL'.symm (Nat.ne_of_gt (hMatch1.loc_bound k1 hlt1))
                    · have hlt1 : k1 < st1.nextLoc := by omega
                      have hlt2 : k2 < st1.nextLoc := by omega
                      rw [hL'lt k1 hlt1, hL'lt k2 hlt2] at hEqL
                      exact hMatch1.loc_inj k1 k2 hlt1 hlt2 hEqL
                  · intro x svx hlu
                    rcases hMatch1.vars_match x svx hlu with ⟨vx, hρx, hevx, hlbx⟩
                    exact ⟨vx, hρx, (evalSVal_loc_agree_lt hlbx hL'lt).trans hevx, svalLocBound_mono (Nat.le_succ _) hlbx⟩
                  · intro l sv hlu
                    simp only [locLookup, emitOb_nextLoc, emitOb_cells] at hlu
                    cases hEq : (st1.nextLoc == l)
                    · simp [hEq] at hlu
                      rcases hMatch1.cells_match l sv hlu with ⟨v0, hget, hev0, hlb0⟩
                      have hlt_l : l < st1.nextLoc := (hwf1.cells_bound _ (locLookup_mem hlu)).1
                      have hlt_σ : L1 l < σ1.length := hMatch1.loc_bound l hlt_l
                      refine ⟨v0, ?_, (evalSVal_loc_agree_lt hlb0 hL'lt).trans hev0, svalLocBound_mono (Nat.le_succ _) hlb0⟩
                      rw [hL'lt l hlt_l, List.getElem?_append_left hlt_σ]; exact hget
                    · have hle : st1.nextLoc = l := eq_of_beq hEq
                      subst hle; simp at hlu; subst hlu
                      refine ⟨v1, ?_, (evalSVal_loc_agree_lt hlb1 hL'lt).trans hev1, svalLocBound_mono (Nat.le_succ _) hlb1⟩
                      simp [L', List.getElem?_append_right (Nat.le_refl _)]
                  · intro l ty hlu
                    simp only [locLookup, emitOb_nextLoc, emitOb_cellTys] at hlu
                    cases hEq : (st1.nextLoc == l)
                    · simp [hEq] at hlu
                      rcases hMatch1.cells_ty l ty hlu with ⟨hlt_l, v0, hget, hvt⟩
                      have hlt_σ : L1 l < σ1.length := hMatch1.loc_bound l hlt_l
                      refine ⟨Nat.lt_succ_of_lt hlt_l, v0, ?_, hvt⟩
                      rw [hL'lt l hlt_l, List.getElem?_append_left hlt_σ]; exact hget
                    · have hle : st1.nextLoc = l := eq_of_beq hEq
                      subst hle; simp at hlu; subst hlu
                      refine ⟨Nat.lt_succ_self _, v1, ?_, hvt1⟩
                      simp [L', List.getElem?_append_right (Nat.le_refl _)]
      | cellGet e1 =>
        simp only [vcgen] at hvc
        cases h1 : vcgen env st e1 with
        | none => simp [h1] at hvc
        | some r1 =>
          rcases r1 with ⟨st1, sv1⟩; simp only [h1] at hvc
          cases sv1 with
          | loc l =>
            simp only at hvc
            cases hlu : locLookup st1.cells l with
            | none => simp [hlu] at hvc
            | some sv =>
              simp [hlu] at hvc; rcases hvc with ⟨rfl, rfl⟩
              have ih1 := go hM hσ hMatch h1 hObs
              rw [substMany_cellGet]
              constructor
              · intro k hk σ' hs
                rcases stepsN_cellGet_terminal (Or.inr ⟨_, rfl⟩) hs with
                  ⟨k1, hk1, tr, hst1, hEq⟩ | ⟨k1, hk1, l', σ1, v', hst1, hget', hrest⟩
                · cases hEq; exact ih1.1 k1 (by omega) σ' hst1
                · rcases ih1.2 k1 (by omega) (.loc l') σ1 (.loc l') hst1 with ⟨_, M1, L1, hM1, _, _, hMatch1, hev1⟩
                  simp [evalSVal] at hev1; subst hev1
                  rcases hMatch1.cells_match l sv hlu with ⟨v0, hget0, hev0, _⟩
                  rw [hget0] at hget'; cases hget'
                  have hv' : IsValue v' := (evalSVal_closed hM1 hev0).1
                  rcases stepsN_of_value hv' hrest with ⟨_, hEq, _⟩; subst hEq; cases hv'
              · intro k hk v σ' hv hs
                rcases stepsN_cellGet_terminal (Or.inl hv) hs with
                  ⟨_, _, _, _, hEq⟩ | ⟨k1, hk1, l', σ1, v', hst1, hget', hrest⟩
                · subst hEq; cases hv
                · rcases ih1.2 k1 (by omega) (.loc l') σ1 (.loc l') hst1 with ⟨hσ1, M1, L1, hM1, hag1, hagL1, hMatch1, hev1⟩
                  simp [evalSVal] at hev1; subst hev1
                  rcases hMatch1.cells_match l sv hlu with ⟨v0, hget0, hev0, _⟩
                  rw [hget0] at hget'; cases hget'
                  have hv' : IsValue v' := (evalSVal_closed hM1 hev0).1
                  rcases stepsN_of_value hv' hrest with ⟨_, rfl, rfl⟩
                  exact ⟨hσ1, M1, L1, hM1, hag1, hagL1, hMatch1, hev0⟩
          | _ => simp at hvc
      | cellSet e1 e2 =>
        simp only [vcgen] at hvc
        cases h1 : vcgen env st e1 with
        | none => simp [h1] at hvc
        | some r1 =>
          rcases r1 with ⟨st1, sv1⟩; simp only [h1] at hvc
          rcases vcgen_wf hMatch.wf h1 with ⟨hs1, hl1, _, _, hwf1, _⟩
          have hlw1 := (vcgen_locBound hMatch.wf hMatch.locWf h1).1
          cases sv1 with
          | loc l =>
            simp only at hvc
            cases h2 : vcgen env st1 e2 with
            | none => simp [h2] at hvc
            | some r2 =>
              rcases r2 with ⟨st2, sv2⟩; simp only [h2] at hvc
              rcases vcgen_wf hwf1 h2 with ⟨hs2, hl2, _, ho2, hwf2, hb2⟩
              have hlb2 := (vcgen_locBound hwf1 hlw1 h2).2
              cases hlu : locLookup st2.cells l with
              | none => simp [hlu] at hvc
              | some _ =>
                simp only [hlu] at hvc
                have hObs2 : ValidObs st2.obs := by
                  cases hct : locLookup st2.cellTys l with
                  | none => simp [hct] at hvc; rcases hvc with ⟨rfl, _⟩; exact hObs
                  | some ty =>
                    simp [hct] at hvc; rcases hvc with ⟨rfl, _⟩
                    exact validObs_mono (fun _ hf => List.mem_cons_of_mem _ hf) hObs
                have hTyCheck : ∀ (M2 : Model) (L2 : Loc → Loc) (v2 : Expr),
                    ValidModel M2 → evalSForm M2 st2.path → evalSVal M2 L2 sv2 = some v2 →
                    ∀ ty, locLookup st2.cellTys l = some ty → valHasTy v2 ty := by
                  intro M2 L2 v2 hM2 hp2 hev2 ty hct
                  simp [hct] at hvc; rcases hvc with ⟨rfl, _⟩
                  have hObMem : SForm.imp st2.path (.hasTy sv2 ty) ∈ (emitOb st2 (.hasTy sv2 ty)).obs :=
                    List.mem_cons_self ..
                  rcases hObs _ hObMem M2 hM2 hp2 with ⟨v0, hev0, hvt0⟩
                  rcases valHasTy_eq_lit hvt0 with ⟨c, rfl⟩
                  have hL := evalSVal_lit_iff_id (L := L2).mpr hev0
                  rw [hL] at hev2; cases hev2; exact hvt0
                have hStOut : st' = { (match locLookup st2.cellTys l with | some ty => emitOb st2 (.hasTy sv2 ty) | none => st2) with cells := (l, sv2) :: st2.cells } ∧ sv = .lit .unit := by
                  cases hct : locLookup st2.cellTys l <;> simp [hct] at hvc <;> rcases hvc with ⟨rfl, rfl⟩ <;> exact ⟨rfl, rfl⟩
                rcases hStOut with ⟨rfl, rfl⟩
                have ih1 := go hM hσ hMatch h1 (validObs_mono ho2 hObs2)
                rw [substMany_cellSet]
                constructor
                · intro k hk σ' hs
                  rcases stepsN_cellSet_terminal (Or.inr ⟨_, rfl⟩) hs with
                    ⟨k1, hk1, tr, hst1, hEq⟩ |
                    ⟨k1, k2, hlt, v1, σ1, tr, hv1', hst1, hst2, hEq⟩ |
                    ⟨_, _, _, _, _, _, _, _, _, _, _, hEq, _⟩
                  · cases hEq; exact ih1.1 k1 (by omega) σ' hst1
                  · cases hEq
                    rcases ih1.2 k1 (by omega) v1 σ1 hv1' hst1 with ⟨hσ1, M1, L1, hM1, _, _, hMatch1, _⟩
                    exact (go hM1 hσ1 hMatch1 h2 hObs2).1 k2 (by omega) σ' hst2
                  · cases hEq
                · intro k hk v σ' hv hs
                  rcases stepsN_cellSet_terminal (Or.inl hv) hs with
                    ⟨_, _, _, _, hEq⟩ |
                    ⟨_, _, _, _, _, _, _, _, _, hEq⟩ |
                    ⟨k1, k2, hlt, l', v2, σ1, σ2, hv2', hlen2, hst1, hst2, rfl, rfl⟩
                  · subst hEq; cases hv
                  · subst hEq; cases hv
                  · rcases ih1.2 k1 (by omega) (.loc l') σ1 (.loc l') hst1 with ⟨hσ1, M1, L1, hM1, hag1, hagL1, hMatch1, hev1⟩
                    simp [evalSVal] at hev1; subst hev1
                    rcases (go hM1 hσ1 hMatch1 h2 hObs2).2 k2 (by omega) v2 σ2 hv2' hst2 with ⟨hσ2, M2, L2, hM2, hag2, hagL2, hMatch2, hev2⟩
                    have hag12 : ∀ id < st.nextSym, M2 id = M id :=
                      fun id hid => (hag2 id (Nat.lt_of_lt_of_le hid hs1)).trans (hag1 id hid)
                    have hagL12 : ∀ k < st.nextLoc, L2 k = L k :=
                      fun k hk => (hagL2 k (Nat.lt_of_lt_of_le hk hl1)).trans (hagL1 k hk)
                    have hcl2 : freeVars v2 = [] := (evalSVal_closed hM2 hev2).2
                    have hlBound : l < st2.nextLoc := (hwf2.cells_bound _ (locLookup_mem hlu)).1
                    have hlBound1 : l < st1.nextLoc := by
                      have := (vcgen_locBound hMatch.wf hMatch.locWf h1).2
                      exact this
                    have hL2l : L2 l = L1 l := hagL2 l hlBound1
                    refine ⟨storeClosed_set hσ2 hv2' hcl2, M2, L2, hM2, hag12, hagL12, ?_, rfl⟩
                    have hBaseEq : ∀ (s : SymState),
                        s.nextSym = st2.nextSym → s.nextLoc = st2.nextLoc → s.vars = st2.vars →
                        s.cellTys = st2.cellTys → s.path = st2.path →
                        StateMatches M2 L2 { s with cells := (l, sv2) :: st2.cells } ρ (σ2.set (L1 l) v2) := by
                      intro s hsEq hlEq hvEq hctEq hpEq
                      refine ⟨hMatch2.closed_env, ?_, ?_, ?_, hpEq ▸ hMatch2.path_holds, ?_, ?_, ?_⟩
                      · refine ⟨hsEq ▸ hvEq ▸ hwf2.vars_bound, ?_, hsEq ▸ hpEq ▸ hwf2.path_bound⟩
                        intro p hp; rcases List.mem_cons.mp hp with rfl | hp'
                        · exact ⟨hlEq ▸ hlBound, hsEq ▸ hb2⟩
                        · exact ⟨hlEq ▸ (hwf2.cells_bound p hp').1, hsEq ▸ (hwf2.cells_bound p hp').2⟩
                      · intro k hk; simp; exact hMatch2.loc_bound k (hlEq ▸ hk)
                      · intro k1 k2 hk1 hk2; exact hMatch2.loc_inj k1 k2 (hlEq ▸ hk1) (hlEq ▸ hk2)
                      · rw [hvEq, hlEq]; exact hMatch2.vars_match
                      · intro l0 sv0 hlu0
                        simp only [locLookup] at hlu0
                        cases hEq : (l == l0)
                        · simp [hEq] at hlu0
                          have hne : l ≠ l0 := fun h => by subst h; simp at hEq
                          have hl0b : l0 < st2.nextLoc := (hwf2.cells_bound _ (locLookup_mem hlu0)).1
                          have hLne : L2 l ≠ L2 l0 := fun hL => hne (hMatch2.loc_inj l l0 hlBound hl0b hL)
                          rcases hMatch2.cells_match l0 sv0 hlu0 with ⟨v0, hget, hev0, hlb0⟩
                          exact ⟨v0, by rw [← hL2l, List.getElem?_set_ne hLne]; exact hget, hev0, hlEq ▸ hlb0⟩
                        · have heq : l = l0 := eq_of_beq hEq
                          subst heq; simp at hlu0; subst hlu0
                          exact ⟨v2, by rw [hL2l, List.getElem?_set_self hlen2], hev2, hlEq ▸ hlb2⟩
                      · intro l0 ty0 hlu0
                        rw [hctEq] at hlu0
                        rcases hMatch2.cells_ty l0 ty0 hlu0 with ⟨hl0b, v0, hget, hvt⟩
                        refine ⟨hlEq ▸ hl0b, ?_⟩
                        by_cases hEq : l = l0
                        · subst hEq
                          exact ⟨v2, by rw [hL2l, List.getElem?_set_self hlen2], hTyCheck M2 L2 v2 hM2 hMatch2.path_holds hev2 ty0 hlu0⟩
                        · have hLne : L2 l ≠ L2 l0 := fun hL => hEq (hMatch2.loc_inj l l0 hlBound hl0b hL)
                          exact ⟨v0, by rw [← hL2l, List.getElem?_set_ne hLne]; exact hget, hvt⟩
                    cases hct : locLookup st2.cellTys l with
                    | none => exact hBaseEq st2 rfl rfl rfl rfl rfl
                    | some ty => exact hBaseEq (emitOb st2 (.hasTy sv2 ty)) rfl rfl rfl rfl rfl
          | _ => simp at hvc
      | getTag e1 =>
        simp only [vcgen] at hvc
        cases h1 : vcgen env st e1 with
        | none => simp [h1] at hvc
        | some r1 =>
          rcases r1 with ⟨st1, sv1⟩; simp [h1] at hvc; rcases hvc with ⟨rfl, rfl⟩
          have ih1 := go hM hσ hMatch h1 hObs
          rw [substMany_getTag]
          constructor
          · intro k hk σ' hs
            rcases stepsN_getTag_terminal (Or.inr ⟨_, rfl⟩) hs with ⟨k1, hk1, tr, hst1, hEq⟩ | ⟨_, _, _, _, _, _, _, hEq⟩
            · cases hEq; exact ih1.1 k1 (by omega) σ' hst1
            · cases hEq
          · intro k hk v σ' hv hs
            rcases stepsN_getTag_terminal (Or.inl hv) hs with ⟨_, _, _, _, hEq⟩ | ⟨k1, hk1, adt, tag, vs, hvs, hst1, rfl⟩
            · subst hEq; cases hv
            · rcases ih1.2 k1 (by omega) (.makeData adt tag vs) σ' (.makeData _ _ hvs) hst1 with ⟨hσ', M1, L1, hM1, hag1, hagL1, hMatch1, hev1⟩
              exact ⟨hσ', M1, L1, hM1, hag1, hagL1, hMatch1, by simp [evalSVal, hev1]⟩
      | while_ c b =>
        simp only [vcgen] at hvc
        cases hlc : env.loops c b with
        | none => simp [hlc] at hvc
        | some lc =>
          simp only [hlc] at hvc
          cases hI0 : vcgenPure st lc.inv with
          | none => simp [hI0] at hvc
          | some rI0 =>
            rcases rI0 with ⟨stI0, svI0⟩; simp only [hI0] at hvc
            rcases vcgenPure_wf hMatch.wf hI0 with ⟨hsI0, hlI0, hvI0, hcI0, hpI0, hoI0, _⟩
            have hctI0 : stI0.cellTys = st.cellTys := vcgenPure_cellTys_eq hI0
            let st1 := emitOb stI0 (.isTrue svI0)
            let stH := havocCells st1 (trackedLocs st1)
            have hwf1 : SymWf st1 :=
              ⟨by simp only [st1, emitOb, hsI0, hvI0]; exact hMatch.wf.vars_bound,
               by simp only [st1, emitOb, hsI0, hlI0, hcI0]; exact hMatch.wf.cells_bound,
               by simp only [st1, emitOb, hsI0, hpI0]; exact hMatch.wf.path_bound⟩
            have hlocs1 : ∀ l ∈ trackedLocs st1, l < st1.nextLoc := fun l hl => by
              rcases List.mem_map.mp hl with ⟨p, hp, rfl⟩; exact (hwf1.cells_bound p hp).1
            rcases havocCells_props st1 (trackedLocs st1) hlocs1 hwf1 with
              ⟨hsH, hlH, hvH, hctH, hoH, hwfH, _, _⟩
            cases hIH : vcgenPure (havocCells (emitOb stI0 (.isTrue svI0)) (trackedLocs (emitOb stI0 (.isTrue svI0)))) lc.inv with
            | none => simp [hIH] at hvc
            | some rIH =>
              rcases rIH with ⟨stIH, svIH⟩; simp only [hIH] at hvc
              rcases vcgenPure_wf hwfH hIH with ⟨hsIH, hlIH, hvIH, hcIH, hpIH, hoIH, hbIH⟩
              have hctIH : stIH.cellTys = stH.cellTys := vcgenPure_cellTys_eq hIH
              let stLE := withPath stIH (.isTrue svIH)
              have hwfLE : SymWf stLE :=
                ⟨by simp only [stLE, withPath, hsIH, hvIH]; exact hwfH.vars_bound,
                 by simp only [stLE, withPath, hsIH, hlIH, hcIH]; exact hwfH.cells_bound,
                 by simp only [stLE, withPath, sformBound, hsIH, hpIH]; exact ⟨hwfH.path_bound, hbIH⟩⟩
              cases hC : vcgen env (withPath stIH (.isTrue svIH)) c with
              | none => simp [hC] at hvc
              | some rC =>
                rcases rC with ⟨stC, svC⟩; simp only [hC] at hvc
                split at hvc
                · cases hvc
                · rename_i hlocC
                  simp only [bne_iff_ne, Decidable.not_not] at hlocC
                  rcases vcgen_wf hwfLE hC with ⟨hsC, _, _, hoC, hwfC, hbC⟩
                  have hctC : stC.cellTys = stLE.cellTys := vcgen_cellTys_of_nextLoc_eq hwfLE hC hlocC
                  have hwfB0 : SymWf (withPath stC (.isTrue svC)) := symWf_withPath hwfC (c := .isTrue svC) hbC
                  cases hPre : checkLoopPreDec (withPath stC (.isTrue svC)) lc.dec with
                  | none => simp [hPre] at hvc
                  | some rPre =>
                    rcases rPre with ⟨stBodyIn, svD0Opt⟩; simp only [hPre] at hvc
                    rcases checkLoopPreDec_props hwfB0 hPre with
                      ⟨hsPre, hlPre, hvPre, hcPre, hctPre, hpPre, hoPre, hwfBodyIn⟩
                    simp only [withPath_nextSym, withPath_nextLoc, withPath_vars, withPath_cells, withPath_cellTys, withPath_path, withPath_obs] at hsPre hlPre hvPre hcPre hctPre hpPre hoPre
                    cases hB : vcgen env stBodyIn b with
                    | none => simp [hB] at hvc
                    | some rB =>
                      rcases rB with ⟨stB, _⟩; simp only [hB] at hvc
                      split at hvc
                      · cases hvc
                      · rename_i hlocB
                        simp only [bne_iff_ne, Decidable.not_not] at hlocB
                        rcases vcgen_wf hwfBodyIn hB with ⟨hsB, _, _, hoB, hwfB, _⟩
                        have hctB : stB.cellTys = stBodyIn.cellTys := vcgen_cellTys_of_nextLoc_eq hwfBodyIn hB (hlocB.trans hlPre.symm)
                        cases hPost : checkLoopPostDec stB lc.dec svD0Opt with
                        | none => simp [hPost] at hvc
                        | some stBDec =>
                          simp only [hPost] at hvc
                          rcases checkLoopPostDec_props hwfB hPost with
                            ⟨hsPost, hlPost, hvPost, hcPost, hctPost, hpPost, hoPost, hwfBDec⟩
                          cases hBI : vcgenPure stBDec lc.inv with
                          | none => simp [hBI] at hvc
                          | some rBI =>
                            rcases rBI with ⟨stBI, svBI⟩; simp [hBI] at hvc; rcases hvc with ⟨rfl, rfl⟩
                            rcases vcgenPure_wf hwfBDec hBI with ⟨hsBI, _, _, _, hpBI, hoBI, _⟩
                            have hObsBI : ValidObs stBI.obs := validObs_mono (fun _ hf => List.mem_cons_of_mem _ hf) hObs
                            have hObsBDec : ValidObs stBDec.obs := validObs_mono hoBI hObsBI
                            have hObsB : ValidObs stB.obs := validObs_mono hoPost hObsBDec
                            have hObsBodyIn : ValidObs stBodyIn.obs := validObs_mono hoB hObsB
                            have hObsC : ValidObs stC.obs := validObs_mono hoPre hObsBodyIn
                            have hObsIH : ValidObs stIH.obs := validObs_mono hoC hObsC
                            have hEntryMem : SForm.imp stI0.path (.isTrue svI0) ∈ (emitOb stBI (.isTrue svBI)).obs :=
                              List.mem_cons_of_mem _ (hoBI _ (hoPost _ (hoB _ (hoPre _ (hoC _ (hoIH _ (by rw [hoH]; exact List.mem_cons_self ..)))))))
                            have hEntryInv : evalSVal M L svI0 = some (.lit (.bool true)) :=
                              evalSVal_lit_iff_id.mpr (hObs _ hEntryMem M hM (by rw [hpI0]; exact hMatch.path_holds))
                            have hMatch1 : StateMatches M L st1 ρ σ :=
                              hMatch.of_eq hwf1 (by simp only [st1, emitOb, hlI0]) (by simp only [st1, emitOb, hvI0])
                                (by simp only [st1, emitOb, hcI0]) (by simp only [st1, emitOb, hctI0])
                                (by simp only [st1, emitOb, hpI0]; exact hMatch.path_holds)
                            rcases havocCells_extend_model_tracked hM hMatch1 hMatch1.loc_bound hσ hMatch1.cells_ty with
                              ⟨MH, hMH, hagH, hMatchH⟩
                            have hInvH : evalSVal MH L svIH = some (.lit (.bool true)) :=
                              vcgenPure_eval_congr hM hMH hMatch hMatchH hI0 hIH hObsIH hEntryInv
                            have hMatchLE : StateMatches MH L stLE ρ σ :=
                              hMatchH.of_eq hwfLE (by simp only [stLE, withPath, hlIH]) (by simp only [stLE, withPath, hvIH])
                                (by simp only [stLE, withPath, hcIH]) (by simp only [stLE, withPath]; exact hctIH)
                                ⟨by simp only [hpIH]; exact hMatchH.path_holds, evalSVal_lit_iff_id.mp hInvH⟩
                            have hwfExit : SymWf ({ nextSym := (emitOb stBI (.isTrue svBI)).nextSym, nextLoc := stC.nextLoc, vars := st.vars, cells := stC.cells, cellTys := st.cellTys, path := .and stC.path (.isFalse svC), obs := (emitOb stBI (.isTrue svBI)).obs } : SymState) := by
                              have hsC_BI : stC.nextSym ≤ stBI.nextSym := by omega
                              have hs_BI : st.nextSym ≤ stBI.nextSym := by
                                have hs1' : st.nextSym ≤ stH.nextSym := by
                                  rw [← hsI0, ← emitOb_nextSym stI0 (.isTrue svI0)]; exact hsH
                                have hs2' : stH.nextSym ≤ stC.nextSym := by
                                  rw [← hsIH, ← withPath_nextSym stIH (.isTrue svIH)]; exact hsC
                                omega
                              exact ⟨fun p hp => svalBound_mono hs_BI (hMatch.wf.vars_bound p hp),
                                fun p hp => ⟨(hwfC.cells_bound p hp).1, svalBound_mono hsC_BI (hwfC.cells_bound p hp).2⟩,
                                ⟨sformBound_mono hsC_BI hwfC.path_bound, svalBound_mono hsC_BI hbC⟩⟩
                            have hlocEqAll : stC.nextLoc = st.nextLoc := by
                              simp only [stLE, withPath_nextLoc, st1, emitOb_nextLoc] at hlocC hlH hlI0 hlIH ⊢; omega
                            have hctAll : stC.cellTys = st.cellTys := by
                              rw [hctC]; change stIH.cellTys = st.cellTys
                              rw [hctIH]; change (havocCells st1 (trackedLocs st1)).cellTys = st.cellTys
                              rw [hctH]; exact hctI0
                            rw [substMany_while]
                            have hStepLoop : ∀ (m : Nat), m ≤ bound →
                                ∀ {σ_i : Store} {M_i : Model} {L_i : Loc → Loc},
                                  ValidModel M_i → StoreClosed σ_i →
                                  (∀ id < st.nextSym, M_i id = M id) →
                                  (∀ k < st.nextLoc, L_i k = L k) →
                                  StateMatches M_i L_i stLE ρ σ_i →
                                  SafeExecN Δ Φ m (.while_ (substMany ρ c) (substMany ρ b)) σ_i
                                    (fun v σ' => StoreClosed σ' ∧
                                      ∃ M' L', ValidModel M' ∧
                                        (∀ id < st.nextSym, M' id = M id) ∧
                                        (∀ k < st.nextLoc, L' k = L k) ∧
                                        StateMatches M' L' ({ nextSym := (emitOb stBI (.isTrue svBI)).nextSym, nextLoc := stC.nextLoc, vars := st.vars, cells := stC.cells, cellTys := st.cellTys, path := .and stC.path (.isFalse svC), obs := (emitOb stBI (.isTrue svBI)).obs } : SymState) ρ σ' ∧
                                        evalSVal M' L' (.lit .unit) = some v) := by
                              intro m
                              induction m using Nat.strongRecOn with
                              | ind m ihLoop =>
                                intro hm σ_i M_i L_i hMi hσi hagMi hagLi hMatchi
                                constructor
                                · intro k hk σ' hst
                                  rcases stepsN_while_terminal (Or.inr ⟨_, rfl⟩) hst with ⟨m1, hm1, hif⟩
                                  rcases stepsN_if_terminal (Or.inr ⟨_, rfl⟩) hif with
                                    ⟨kc, hkc, tr, hstc, hEq⟩ |
                                    ⟨kc, kb, hlt, σc, hstc, hblk⟩ |
                                    ⟨kc, ke, hlt, σc, hstc, hunit⟩
                                  · cases hEq; exact (go hMi hσi hMatchi hC hObsC).1 kc (by omega) σ' hstc
                                  · rcases (go hMi hσi hMatchi hC hObsC).2 kc (by omega) (.lit (.bool true)) σc (.lit _) hstc with
                                      ⟨hσc, Mc, Lc, hMc, hagMc, hagLc, hMatchc, hevCc⟩
                                    have hMatchBIn : StateMatches Mc Lc stBodyIn ρ σc :=
                                      hMatchc.of_eq hwfBodyIn hlPre hvPre hcPre hctPre
                                        (by rw [hpPre]; exact ⟨hMatchc.path_holds, evalSVal_lit_iff_id.mp hevCc⟩)
                                    rcases stepsN_blockCons_terminal (Or.inr ⟨_, rfl⟩) hblk with
                                      ⟨kb1, hkb1, tr, hstb, hEq⟩ | ⟨kb1, kw, hltb, vb, σb, hvb, hstb, hblk2⟩
                                    · cases hEq; exact (go hMc hσc hMatchBIn hB hObsB).1 kb1 (by omega) σ' hstb
                                    · rcases (go hMc hσc hMatchBIn hB hObsB).2 kb1 (by omega) vb σb hvb hstb with
                                        ⟨hσb, Mb, Lb, hMb, hagMb, hagLb, hMatchb, _⟩
                                      cases hblk2 with
                                      | step hsBlk hwRest =>
                                        cases hsBlk with
                                        | blockSingle =>
                                          have hMatchBDec : StateMatches Mb Lb stBDec ρ σb :=
                                            hMatchb.of_eq hwfBDec hlPost hvPost hcPost hctPost (by rw [hpPost]; exact hMatchb.path_holds)
                                          have hPresInv : evalSVal Mb Lb svBI = some (.lit (.bool true)) :=
                                            evalSVal_lit_iff_id.mpr (hObs _ (List.mem_cons_self ..) Mb hMb (by rw [hpBI]; exact hMatchBDec.path_holds))
                                          have hLocB1 : stB.nextLoc = st1.nextLoc := by
                                            simp only [st1, emitOb_nextLoc] at hlocB hlocEqAll hlI0 ⊢; omega
                                          have hagLb_all : ∀ k < st1.nextLoc, Lb k = L k := fun k hk => by
                                            have hk' : k < st.nextLoc := by simp only [st1, emitOb_nextLoc, hlI0] at hk; exact hk
                                            have hkC : k < stC.nextLoc := hlocEqAll.symm ▸ hk'
                                            have hkLE : k < stLE.nextLoc := hlocC ▸ hkC
                                            exact (hagLb k (hlPre.symm ▸ hkC)).trans ((hagLc k hkLE).trans (hagLi k hk'))
                                          have hboundB : ∀ k < st1.nextLoc, L k < σb.length := fun k hk => by
                                            rw [← hagLb_all k hk]; exact hMatchb.loc_bound k (hLocB1.symm ▸ hk)
                                          have htysB : ∀ l ty, locLookup st1.cellTys l = some ty → l < st1.nextLoc ∧ ∃ v, σb[L l]? = some v ∧ valHasTy v ty := by
                                            intro l ty hlu
                                            have hluB : locLookup stB.cellTys l = some ty := by
                                              rw [hctB, hctPre, hctAll]; simp only [st1, emitOb, hctI0] at hlu; exact hlu
                                            rcases hMatchb.cells_ty l ty hluB with ⟨hlb, v0, hget, hvt⟩
                                            have hlb1 : l < st1.nextLoc := hLocB1 ▸ hlb
                                            exact ⟨hlb1, v0, by rw [← hagLb_all l hlb1]; exact hget, hvt⟩
                                          rcases havocCells_extend_model_tracked hM hMatch1 hboundB hσb htysB with
                                            ⟨MH2, hMH2, hagH2, hMatchH2⟩
                                          have hInvH2 : evalSVal MH2 L svIH = some (.lit (.bool true)) :=
                                            vcgenPure_eval_congr hMb hMH2 hMatchBDec hMatchH2 hBI hIH hObsIH hPresInv
                                          have hMatchLE2 : StateMatches MH2 L stLE ρ σb :=
                                            hMatchH2.of_eq hwfLE (by simp only [stLE, withPath, hlIH]) (by simp only [stLE, withPath, hvIH])
                                              (by simp only [stLE, withPath, hcIH]) (by simp only [stLE, withPath]; exact hctIH)
                                              ⟨by simp only [hpIH]; exact hMatchH2.path_holds, evalSVal_lit_iff_id.mp hInvH2⟩
                                          have hag2 : ∀ id < st.nextSym, MH2 id = M id :=
                                            fun id hid => hagH2 id (by simp only [st1, emitOb_nextSym, hsI0]; exact hid)
                                          exact (ihLoop _ (by omega) (by omega) hMH2 hσb hag2 (fun _ _ => rfl) hMatchLE2).1 _ (Nat.le_refl _) σ' hwRest
                                  · rcases stepsN_of_value (.lit .unit) hunit with ⟨_, hEq, _⟩; cases hEq
                                · intro k hk v σ' hv hst
                                  rcases stepsN_while_terminal (Or.inl hv) hst with ⟨m1, hm1, hif⟩
                                  rcases stepsN_if_terminal (Or.inl hv) hif with
                                    ⟨_, _, _, _, hEq⟩ |
                                    ⟨kc, kb, hlt, σc, hstc, hblk⟩ |
                                    ⟨kc, ke, hlt, σc, hstc, hunit⟩
                                  · subst hEq; cases hv
                                  · rcases (go hMi hσi hMatchi hC hObsC).2 kc (by omega) (.lit (.bool true)) σc (.lit _) hstc with
                                      ⟨hσc, Mc, Lc, hMc, _, hagLc, hMatchc, hevCc⟩
                                    have hMatchBIn : StateMatches Mc Lc stBodyIn ρ σc :=
                                      hMatchc.of_eq hwfBodyIn hlPre hvPre hcPre hctPre
                                        (by rw [hpPre]; exact ⟨hMatchc.path_holds, evalSVal_lit_iff_id.mp hevCc⟩)
                                    rcases stepsN_blockCons_terminal (Or.inl hv) hblk with
                                      ⟨_, _, _, _, hEq⟩ | ⟨kb1, kw, hltb, vb, σb, hvb, hstb, hblk2⟩
                                    · subst hEq; cases hv
                                    · rcases (go hMc hσc hMatchBIn hB hObsB).2 kb1 (by omega) vb σb hvb hstb with
                                        ⟨hσb, Mb, Lb, hMb, _, hagLb, hMatchb, _⟩
                                      cases hblk2 with
                                      | refl => cases hv
                                      | step hsBlk hwRest =>
                                        cases hsBlk with
                                        | blockSingle =>
                                          have hMatchBDec : StateMatches Mb Lb stBDec ρ σb :=
                                            hMatchb.of_eq hwfBDec hlPost hvPost hcPost hctPost (by rw [hpPost]; exact hMatchb.path_holds)
                                          have hPresInv : evalSVal Mb Lb svBI = some (.lit (.bool true)) :=
                                            evalSVal_lit_iff_id.mpr (hObs _ (List.mem_cons_self ..) Mb hMb (by rw [hpBI]; exact hMatchBDec.path_holds))
                                          have hLocB1 : stB.nextLoc = st1.nextLoc := by
                                            simp only [st1, emitOb_nextLoc] at hlocB hlocEqAll hlI0 ⊢; omega
                                          have hagLb_all : ∀ k < st1.nextLoc, Lb k = L k := fun k hk => by
                                            have hk' : k < st.nextLoc := by simp only [st1, emitOb_nextLoc, hlI0] at hk; exact hk
                                            have hkC : k < stC.nextLoc := hlocEqAll.symm ▸ hk'
                                            have hkLE : k < stLE.nextLoc := hlocC ▸ hkC
                                            exact (hagLb k (hlPre.symm ▸ hkC)).trans ((hagLc k hkLE).trans (hagLi k hk'))
                                          have hboundB : ∀ k < st1.nextLoc, L k < σb.length := fun k hk => by
                                            rw [← hagLb_all k hk]; exact hMatchb.loc_bound k (hLocB1.symm ▸ hk)
                                          have htysB : ∀ l ty, locLookup st1.cellTys l = some ty → l < st1.nextLoc ∧ ∃ v, σb[L l]? = some v ∧ valHasTy v ty := by
                                            intro l ty hlu
                                            have hluB : locLookup stB.cellTys l = some ty := by
                                              rw [hctB, hctPre, hctAll]; simp only [st1, emitOb, hctI0] at hlu; exact hlu
                                            rcases hMatchb.cells_ty l ty hluB with ⟨hlb, v0, hget, hvt⟩
                                            have hlb1 : l < st1.nextLoc := hLocB1 ▸ hlb
                                            exact ⟨hlb1, v0, by rw [← hagLb_all l hlb1]; exact hget, hvt⟩
                                          rcases havocCells_extend_model_tracked hM hMatch1 hboundB hσb htysB with
                                            ⟨MH2, hMH2, hagH2, hMatchH2⟩
                                          have hInvH2 : evalSVal MH2 L svIH = some (.lit (.bool true)) :=
                                            vcgenPure_eval_congr hMb hMH2 hMatchBDec hMatchH2 hBI hIH hObsIH hPresInv
                                          have hMatchLE2 : StateMatches MH2 L stLE ρ σb :=
                                            hMatchH2.of_eq hwfLE (by simp only [stLE, withPath, hlIH]) (by simp only [stLE, withPath, hvIH])
                                              (by simp only [stLE, withPath, hcIH]) (by simp only [stLE, withPath]; exact hctIH)
                                              ⟨by simp only [hpIH]; exact hMatchH2.path_holds, evalSVal_lit_iff_id.mp hInvH2⟩
                                          have hag2 : ∀ id < st.nextSym, MH2 id = M id :=
                                            fun id hid => hagH2 id (by simp only [st1, emitOb_nextSym, hsI0]; exact hid)
                                          exact (ihLoop _ (by omega) (by omega) hMH2 hσb hag2 (fun _ _ => rfl) hMatchLE2).2 _ (Nat.le_refl _) v σ' hv hwRest
                                  · rcases stepsN_of_value (.lit .unit) hunit with ⟨_, rfl, rfl⟩
                                    rcases (go hMi hσi hMatchi hC hObsC).2 kc (by omega) (.lit (.bool false)) σ' (.lit _) hstc with
                                      ⟨hσc, Mc, Lc, hMc, hagMc, hagLc, hMatchc, hevCc⟩
                                    have hs_le : st.nextSym ≤ stLE.nextSym := by
                                      simp only [stLE, withPath_nextSym, hsIH, st1, emitOb_nextSym] at hsH ⊢; omega
                                    have hl_le : st.nextLoc ≤ stLE.nextLoc := by
                                      simp only [stLE, withPath_nextLoc, hlIH, st1, emitOb_nextLoc] at hlH ⊢; omega
                                    have hagFinal : ∀ id < st.nextSym, Mc id = M id :=
                                      fun id hid => (hagMc id (Nat.lt_of_lt_of_le hid hs_le)).trans (hagMi id hid)
                                    have hagLFinal : ∀ k < st.nextLoc, Lc k = L k :=
                                      fun k hk => (hagLc k (Nat.lt_of_lt_of_le hk hl_le)).trans (hagLi k hk)
                                    refine ⟨hσc, Mc, Lc, hMc, hagFinal, hagLFinal, ?_, rfl⟩
                                    exact ⟨hMatchc.closed_env, hwfExit, hMatchc.loc_bound, hMatchc.loc_inj,
                                      ⟨hMatchc.path_holds, evalSVal_lit_iff_id.mp hevCc⟩,
                                      (fun x svx hlu => by
                                        rcases hMatch.vars_match x svx hlu with ⟨vx, hρx, hevx, hlbx⟩
                                        exact ⟨vx, hρx, (evalSVal_loc_agree_lt hlbx hagLFinal).trans ((evalSVal_agree_lt (hMatch.wf.vars_bound _ (assocLookup_mem hlu)) hagFinal).trans hevx), hlocEqAll.symm ▸ hlbx⟩),
                                      hMatchc.cells_match, hctAll ▸ hMatchc.cells_ty⟩
                            exact hStepLoop bound (Nat.le_refl bound) hMH hσ (fun id hid => hagH id (by simp only [st1, emitOb_nextSym, hsI0]; exact hid)) (fun _ _ => rfl) hMatchLE
      | applyDir name args =>
        unfold vcgen at hvc; dsimp only at hvc
        cases hAssert : (name == "assert")
        · rw [hAssert] at hvc; simp only [Bool.false_eq_true, ↓reduceIte] at hvc
          cases hAssume : (name == "assume")
          · rw [hAssume] at hvc; simp only [Bool.false_eq_true, ↓reduceIte] at hvc
            cases hfc : env.contracts name with
            | none => simp [hfc] at hvc
            | some fc =>
              simp only [hfc] at hvc
              split at hvc
              · cases hvc
              · rename_i hLenRet
                simp only [Bool.or_eq_true, bne_iff_ne, Bool.not_eq_true', not_or, Decidable.not_not] at hLenRet
                rcases hLenRet with ⟨hArgLen, hRetSc⟩
                cases hArgs : vcgenList env st args with
                | none => simp [hArgs] at hvc
                | some rA =>
                  rcases rA with ⟨stA, svArgs⟩; simp only [hArgs] at hvc
                  rcases vcgenList_wf hMatch.wf hArgs with ⟨hsA, hlA, hvA, hoA, hwfA, hbArgs⟩
                  rcases vcgenList_locBound hMatch.wf hMatch.locWf hArgs with ⟨hlwA, hlbArgs⟩
                  split at hvc
                  · cases hvc
                  · rename_i hLocOk
                    have hLocOk' : noDupLocs (collectLocArgs svArgs) = true ∧ (collectLocArgs svArgs).all (· < stA.nextLoc) = true := by
                      cases h1 : noDupLocs (collectLocArgs svArgs) <;>
                      cases h2 : (collectLocArgs svArgs).all (· < stA.nextLoc) <;>
                      simp_all
                    rcases hLocOk' with ⟨hNoDupSym, hAllLocLt⟩
                    have hLocBound : ∀ l ∈ collectLocArgs svArgs, l < stA.nextLoc := fun l hl => by
                      have := List.all_eq_true.mp hAllLocLt l hl; simpa using this
                    cases hTyp : checkCallArgTys stA fc.params svArgs with
                    | none => simp [hTyp] at hvc
                    | some stTyped =>
                      simp only [hTyp] at hvc
                      rcases checkCallArgTys_props hTyp with ⟨hsT, hlT, hvT, hcT, hctT, hpT, hoT, hTypFa⟩
                      let paramBindings := (fc.params.map Prod.fst).zip svArgs
                      have hwfCall : SymWf { stTyped with vars := paramBindings } :=
                        ⟨fun p hp => hsT ▸ hbArgs p.2 (List.of_mem_zip hp).2,
                         by rw [hsT, hlT, hcT]; exact hwfA.cells_bound,
                         hsT ▸ hpT ▸ hwfA.path_bound⟩
                      cases hReq : vcgenPure { stTyped with vars := (fc.params.map Prod.fst).zip svArgs } fc.req with
                      | none => simp [hReq] at hvc
                      | some rReq =>
                        rcases rReq with ⟨stReq, svReq⟩; simp only [hReq] at hvc
                        rcases vcgenPure_wf hwfCall hReq with ⟨hsReq, hlReq, hvReq, hcReq, hpReq, hoReq, _⟩
                        have hctReq : stReq.cellTys = stA.cellTys := (vcgenPure_cellTys_eq hReq).trans hctT
                        let stChecked0 := emitOb stReq (.isTrue svReq)
                        have hwfChecked0 : SymWf stChecked0 :=
                          ⟨by simp only [stChecked0, emitOb, hsReq, hvReq]; exact hwfCall.vars_bound,
                           by simp only [stChecked0, emitOb, hsReq, hlReq, hcReq]; exact hwfCall.cells_bound,
                           by simp only [stChecked0, emitOb, hsReq, hpReq]; exact hwfCall.path_bound⟩
                        cases hDec : checkCallDecreases env name fc (emitOb stReq (.isTrue svReq)) with
                        | none => simp [hDec] at hvc
                        | some stChecked =>
                          simp only [hDec] at hvc
                          rcases checkCallDecreases_props hwfChecked0 hDec with
                            ⟨hsDec, hlDec, hvDec, hcDec, hctDec, hpDec, hoDec, hwfChecked⟩
                          let locArgs := collectLocArgs svArgs
                          have hlocAll : ∀ l ∈ locArgs, l < stChecked.nextLoc := fun l hl => by
                            rw [hlDec]; simp only [stChecked0, emitOb_nextLoc, hlReq, hlT]; exact hLocBound l hl
                          rcases havocCells_props stChecked locArgs hlocAll hwfChecked with
                            ⟨hsHav, hlHav, _, hctHav, hoHav, hwfHav, _, _⟩
                          let stHav := havocCells stChecked locArgs
                          let retId := stHav.nextSym
                          have hwfRet : SymWf ({ stHav with
                              nextSym := retId + 1,
                              vars := (fc.retVar, .sym retId) :: paramBindings,
                              path := .and stHav.path (.hasTy (.sym retId) fc.retTy) } : SymState) := by
                            refine ⟨?_, ?_, ⟨sformBound_mono (Nat.le_succ _) hwfHav.path_bound, Nat.lt_succ_self _⟩⟩
                            · intro p hp
                              rcases List.mem_cons.mp hp with rfl | hp'
                              · exact Nat.lt_succ_self _
                              · have hb := hwfCall.vars_bound p hp'
                                rw [hsDec] at hsHav; simp only [stChecked0, emitOb_nextSym, hsReq] at hsHav
                                exact svalBound_mono (Nat.le_trans hsHav (Nat.le_succ _)) hb
                            · intro p hp
                              exact ⟨(hwfHav.cells_bound p hp).1, svalBound_mono (Nat.le_succ _) (hwfHav.cells_bound p hp).2⟩
                          cases hEns : vcgenPure ({ havocCells stChecked (collectLocArgs svArgs) with
                              nextSym := (havocCells stChecked (collectLocArgs svArgs)).nextSym + 1,
                              vars := (fc.retVar, .sym (havocCells stChecked (collectLocArgs svArgs)).nextSym) :: (fc.params.map Prod.fst).zip svArgs,
                              path := .and (havocCells stChecked (collectLocArgs svArgs)).path (.hasTy (.sym (havocCells stChecked (collectLocArgs svArgs)).nextSym) fc.retTy) } : SymState) fc.ens with
                          | none => simp [hEns] at hvc
                          | some rEns =>
                            rcases rEns with ⟨stEns, svEns⟩; simp [hEns] at hvc; rcases hvc with ⟨rfl, rfl⟩
                            rcases vcgenPure_wf hwfRet hEns with ⟨hsEns, _, _, _, _, hoEns, hbEns⟩
                            have hObsEns : ValidObs stEns.obs := hObs
                            have hObsHav : ValidObs stHav.obs := validObs_mono hoEns hObsEns
                            have hObsChecked : ValidObs stChecked.obs := by
                              intro f hf; exact hObsHav f (by change f ∈ (havocCells stChecked locArgs).obs; rw [hoHav]; exact hf)
                            have hObsChecked0 : ValidObs stChecked0.obs := validObs_mono hoDec hObsChecked
                            have hObsReq : ValidObs stReq.obs := validObs_mono (fun _ hf => List.mem_cons_of_mem _ hf) hObsChecked0
                            have hObsTyped : ValidObs stTyped.obs := validObs_mono hoReq hObsReq
                            have hObsA : ValidObs stA.obs := validObs_mono hoT hObsTyped
                            have hSymLe : stA.nextSym ≤ stEns.nextSym := by
                              rw [hsDec] at hsHav; simp only [stChecked0, emitOb_nextSym, hsReq, hsT] at hsHav
                              exact Nat.le_trans hsHav (hsEns.symm ▸ Nat.le_succ _)
                            have hlHavEq : stHav.nextLoc = stA.nextLoc := by
                              change (havocCells stChecked locArgs).nextLoc = stA.nextLoc
                              rw [hlHav, hlDec]; simp only [stChecked0, emitOb_nextLoc, hlReq, hlT]
                            have hwfPost : SymWf ({ nextSym := stEns.nextSym, nextLoc := stA.nextLoc, vars := stA.vars, cells := stHav.cells, cellTys := stA.cellTys, path := .and (.and stHav.path (.hasTy (.sym retId) fc.retTy)) (.isTrue svEns), obs := stEns.obs } : SymState) := by
                              refine ⟨fun p hp => svalBound_mono hSymLe (hwfA.vars_bound p hp), ?_, ?_⟩
                              · intro p hp
                                have hb := hwfHav.cells_bound p hp
                                exact ⟨hlHavEq ▸ hb.1, svalBound_mono (hsEns.symm ▸ Nat.le_succ _) hb.2⟩
                              · exact ⟨⟨sformBound_mono (hsEns.symm ▸ Nat.le_succ _) hwfHav.path_bound, by rw [hsEns]; exact Nat.lt_succ_self _⟩, by rw [hsEns]; exact hbEns⟩
                            rw [substMany_applyDir]
                            have hPre0 : ∀ v ∈ ([] : List Expr), IsValue v := fun _ h => by cases h
                            simpa only [List.nil_append] using
                              goApplyArgs (prefixVals := []) (name := name) hPre0 hM hσ hMatch hArgs hObsA
                                (fun {MA LA vs σA} hMA hσA hagMA hagLA hMatchA hvsCl hEvArgs => by
                              have hvsVal : ∀ v ∈ vs, IsValue v := fun v hv => (hvsCl v hv).1
                              have hTypM := hTypFa MA hMA hObsTyped hMatchA.path_holds
                              have hLenVs : vs.length = fc.params.length := by
                                rw [← hEvArgs.length_eq, ← hTypM.length_eq]
                              have hLocsMap : collectConcreteLocs vs = locArgs.map LA :=
                                collectConcreteLocs_eq_map hTypM hEvArgs
                              have hNoDupConc : noDupLocs (collectConcreteLocs vs) = true := by
                                rw [hLocsMap]
                                exact noDupLocs_map_inj hNoDupSym hLocBound hMatchA.loc_inj
                              have hClosedZip : ClosedEnv (zipParams fc.params vs) := by
                                intro p hp
                                have hmem : p.2 ∈ vs := (List.of_mem_zip hp).2
                                exact hvsCl p.2 hmem
                              have hEvArgsLb : PairwiseRel (fun sv v => evalSVal MA LA sv = some v ∧ svalLocBound stA.nextLoc sv) svArgs vs := by
                                have : ∀ {svs' vs'}, PairwiseRel (fun sv v => evalSVal MA LA sv = some v) svs' vs' →
                                    (∀ sv ∈ svs', svalLocBound stA.nextLoc sv) →
                                    PairwiseRel (fun sv v => evalSVal MA LA sv = some v ∧ svalLocBound stA.nextLoc sv) svs' vs' := by
                                  intro svs' vs' hfa hlb
                                  induction hfa with
                                  | nil => exact .nil
                                  | cons h1 _ ih => exact .cons ⟨h1, hlb _ (List.mem_cons_self ..)⟩ (ih fun s hs => hlb s (List.mem_cons_of_mem _ hs))
                                exact this hEvArgs hlbArgs
                              have hMatchCall : StateMatches MA LA { stTyped with vars := paramBindings } (zipParams fc.params vs) σA :=
                                { closed_env := hClosedZip, wf := hwfCall,
                                  loc_bound := hlT ▸ hMatchA.loc_bound, loc_inj := hlT ▸ hMatchA.loc_inj,
                                  path_holds := hpT ▸ hMatchA.path_holds,
                                  vars_match := by rw [hlT]; exact zipParams_match_of_forall2 hEvArgsLb hTypM.length_eq,
                                  cells_match := by rw [hcT, hlT]; exact hMatchA.cells_match,
                                  cells_ty := by rw [hctT, hlT]; exact hMatchA.cells_ty }
                              have hReqTrue : evalSVal MA LA svReq = some (.lit (.bool true)) :=
                                evalSVal_lit_iff_id.mpr (hObsChecked0 _ (List.mem_cons_self ..) MA hMA (by rw [hpReq]; exact hMatchCall.path_holds))
                              have hReqSteps : Steps Δ Φ (substMany (zipParams fc.params vs) fc.req) σA (.lit (.bool true)) σA :=
                                vcgenPure_complete hMA hMatchCall hReq hReqTrue
                              have hMatchChecked : StateMatches MA LA stChecked (zipParams fc.params vs) σA :=
                                hMatchCall.of_eq hwfChecked (by rw [hlDec]; simp only [stChecked0, emitOb, hlReq])
                                  (by rw [hvDec]; simp only [stChecked0, emitOb, hvReq])
                                  (by rw [hcDec]; simp only [stChecked0, emitOb, hcReq])
                                  (by rw [hctDec]; simp only [stChecked0, emitOb, hctReq, hctT])
                                  (by rw [hpDec]; simp only [stChecked0, emitOb, hpReq]; exact hMatchCall.path_holds)
                              constructor
                              · intro k hk σ' hs
                                rcases stepsN_applyDir_vals_terminal hvsVal (Or.inr ⟨_, rfl⟩) hs with ⟨m, hm, fd, hΦ, _, hbody⟩
                                have hSafe := hCallee name fc fd vs σA hfc hΦ hLenVs hvsCl hσA hNoDupConc hReqSteps
                                exact hSafe.1 m (by omega) σ' hbody
                              · intro k hk v σ' hv hs
                                rcases stepsN_applyDir_vals_terminal hvsVal (Or.inl hv) hs with ⟨m, hm, fd, hΦ, _, hbody⟩
                                have hSafe := hCallee name fc fd vs σA hfc hΦ hLenVs hvsCl hσA hNoDupConc hReqSteps
                                rcases hSafe.2 m (by omega) v σ' hv hbody with
                                  ⟨hclV, htyV, hlenGrow, hσ'Cl, hFrame, hCellTys', hEnsSteps⟩
                                have hbound' : ∀ j < stChecked.nextLoc, LA j < σ'.length := fun j hj =>
                                  Nat.lt_of_lt_of_le (hMatchChecked.loc_bound j hj) hlenGrow
                                have htys' : ∀ l ty, locLookup stChecked.cellTys l = some ty → l < stChecked.nextLoc ∧ ∃ w, σ'[LA l]? = some w ∧ valHasTy w ty := by
                                  intro l ty hlu
                                  have hluA : locLookup stA.cellTys l = some ty := by
                                    rw [hctDec] at hlu; simp only [stChecked0, emitOb, hctReq] at hlu; exact hlu
                                  rcases hMatchA.cells_ty l ty hluA with ⟨hlbA, w0, hget0, hvt0⟩
                                  have hlbC : l < stChecked.nextLoc := by rw [hlDec]; simp only [stChecked0, emitOb_nextLoc, hlReq, hlT]; exact hlbA
                                  refine ⟨hlbC, ?_⟩
                                  by_cases hin : l ∈ locArgs
                                  · rcases callArg_cell_ty_mem hTypM hEvArgs hin hluA with ⟨p, hpmem, hpty⟩
                                    exact hCellTys' p (.loc (LA l)) hpmem ty (LA l) hpty rfl
                                  · have hNotInConc : LA l ∉ collectConcreteLocs vs := by
                                      rw [hLocsMap]; intro hmem
                                      rcases List.mem_map.mp hmem with ⟨l', hl', hEqL⟩
                                      have hEq := hMatchA.loc_inj l' l (hLocBound l' hl') hlbA hEqL
                                      subst hEq; exact hin hl'
                                    have hFr := hFrame (LA l) (hMatchA.loc_bound l hlbA) hNotInConc
                                    rw [hFr]; exact ⟨w0, hget0, hvt0⟩
                                have hframe' : ∀ l sv, locLookup stChecked.cells l = some sv → l ∉ locArgs → σ'[LA l]? = σA[LA l]? := by
                                  intro l sv hlu hnot
                                  have hlb : l < stA.nextLoc := by
                                    have := (hwfChecked.cells_bound _ (locLookup_mem hlu)).1
                                    rw [hlDec] at this; simp only [stChecked0, emitOb_nextLoc, hlReq, hlT] at this; exact this
                                  have hNotInConc : LA l ∉ collectConcreteLocs vs := by
                                    rw [hLocsMap]; intro hmem
                                    rcases List.mem_map.mp hmem with ⟨l', hl', hEqL⟩
                                    have hEq := hMatchA.loc_inj l' l (hLocBound l' hl') hlb hEqL
                                    subst hEq; exact hnot hl'
                                  exact hFrame (LA l) (hMatchA.loc_bound l hlb) hNotInConc
                                rcases havocCells_extend_model locArgs hMA hMatchChecked hlocAll hbound' hσ'Cl htys' hframe' with
                                  ⟨MHav, hMHav, hagHav, hMatchHav⟩
                                let MRet := updateModel MHav retId v
                                have hMRet : ValidModel MRet := validModel_update hMHav hv hclV
                                have hagRet_Hav : ∀ id < stHav.nextSym, MRet id = MHav id := fun id hid => by
                                  dsimp only [MRet, retId, updateModel]
                                  rw [beq_false_of_ne (Nat.ne_of_lt hid)]; rfl
                                have hMatchRet : StateMatches MRet LA ({ stHav with
                                    nextSym := retId + 1,
                                    vars := (fc.retVar, .sym retId) :: paramBindings,
                                    path := .and stHav.path (.hasTy (.sym retId) fc.retTy) } : SymState)
                                    ((fc.retVar, v) :: zipParams fc.params vs) σ' := by
                                  refine ⟨fun p hp => by rcases List.mem_cons.mp hp with rfl | hp'; exact ⟨hv, hclV⟩; exact hClosedZip p hp',
                                    hwfRet, hMatchHav.loc_bound, hMatchHav.loc_inj,
                                    ⟨(evalSForm_agree_lt hwfHav.path_bound hagRet_Hav).mpr hMatchHav.path_holds,
                                     ⟨v, by simp [evalSVal, MRet, retId, updateModel], htyV⟩⟩,
                                    ?_, ?_, hMatchHav.cells_ty⟩
                                  · intro y svy hlu
                                    simp only [assocLookup] at hlu ⊢
                                    cases hxy : (fc.retVar == y)
                                    · simp [hxy] at hlu ⊢
                                      have hlu0 : assocLookup stChecked.vars y = some svy := by
                                        rw [hvDec]; simp only [stChecked0, emitOb, hvReq]; exact hlu
                                      rcases hMatchChecked.vars_match y svy hlu0 with ⟨vy, hρy, hevy, hlby⟩
                                      have hby := hwfChecked.vars_bound _ (assocLookup_mem hlu0)
                                      have hag0 : ∀ id < stChecked.nextSym, MRet id = MA id := fun id hid =>
                                        (hagRet_Hav id (Nat.lt_of_lt_of_le hid hsHav)).trans (hagHav id hid)
                                      exact ⟨vy, hρy, (evalSVal_agree_lt hby hag0).trans hevy, hlHav.symm ▸ hlby⟩
                                    · simp [hxy] at hlu ⊢; subst hlu
                                      exact ⟨by simp [evalSVal, MRet, retId, updateModel], trivial⟩
                                  · intro l sv hlu
                                    rcases hMatchHav.cells_match l sv hlu with ⟨w, hget, hev, hlb⟩
                                    have hb := (hwfHav.cells_bound _ (locLookup_mem hlu)).2
                                    exact ⟨w, hget, (evalSVal_agree_lt hb hagRet_Hav).trans hev, hlb⟩
                                have hEnsTrue : evalSVal MRet LA svEns = some (.lit (.bool true)) :=
                                  ((vcgenPure_sound hMRet hMatchRet hEns hObsEns).2 (.lit (.bool true)) σ' (.lit _) hEnsSteps).2
                                have hagFinal : ∀ id < st.nextSym, MRet id = M id := fun id hid => by
                                  have hidA : id < stA.nextSym := Nat.lt_of_lt_of_le hid hsA
                                  have hidC : id < stChecked.nextSym := by rw [hsDec]; simp only [stChecked0, emitOb_nextSym, hsReq, hsT]; exact hidA
                                  have hidH : id < stHav.nextSym := Nat.lt_of_lt_of_le hidC hsHav
                                  exact (hagRet_Hav id hidH).trans ((hagHav id hidC).trans (hagMA id hid))
                                have hagA_Ret : ∀ id < stA.nextSym, MRet id = MA id := fun id hid => by
                                  have hidC : id < stChecked.nextSym := by rw [hsDec]; simp only [stChecked0, emitOb_nextSym, hsReq, hsT]; exact hid
                                  exact (hagRet_Hav id (Nat.lt_of_lt_of_le hidC hsHav)).trans (hagHav id hidC)
                                refine ⟨hσ'Cl, MRet, LA, hMRet, hagFinal, hagLA, ?_, by dsimp only [evalSVal, MRet, retId, stHav, locArgs, updateModel]; simp⟩
                                refine ⟨hMatchA.closed_env, hwfPost, hlHavEq ▸ hMatchHav.loc_bound, hlHavEq ▸ hMatchHav.loc_inj,
                                  ⟨⟨(evalSForm_agree_lt hwfHav.path_bound hagRet_Hav).mpr hMatchHav.path_holds,
                                    ⟨v, by dsimp only [evalSVal, MRet, retId, stHav, locArgs, updateModel]; simp, htyV⟩⟩,
                                   evalSVal_lit_iff_id.mp hEnsTrue⟩,
                                  ?_, ?_, ?_⟩
                                · intro x svx hlu
                                  rcases hMatchA.vars_match x svx hlu with ⟨vx, hρx, hevx, hlbx⟩
                                  exact ⟨vx, hρx, (evalSVal_agree_lt (hwfA.vars_bound _ (assocLookup_mem hlu)) hagA_Ret).trans hevx, hlbx⟩
                                · intro l sv hlu
                                  rcases hMatchHav.cells_match l sv hlu with ⟨w, hget, hev, hlb⟩
                                  have hb := (hwfHav.cells_bound _ (locLookup_mem hlu)).2
                                  exact ⟨w, hget, (evalSVal_agree_lt hb hagRet_Hav).trans hev, hlHavEq ▸ hlb⟩
                                · intro l ty hlu
                                  have hluH : locLookup stHav.cellTys l = some ty := by
                                    change locLookup (havocCells stChecked locArgs).cellTys l = some ty
                                    rw [hctHav, hctDec]; simp only [stChecked0, emitOb, hctReq]; exact hlu
                                  rcases hMatchHav.cells_ty l ty hluH with ⟨hlb, w, hget, hvt⟩
                                  exact ⟨hlHavEq ▸ hlb, w, hget, hvt⟩)
          · rw [hAssume] at hvc; simp only [↓reduceIte] at hvc
            have hName : name = "assume" := eq_of_beq hAssume
            subst hName
            cases args with
            | nil => simp at hvc
            | cons e1 rest =>
              cases rest with
              | cons _ _ => simp at hvc
              | nil =>
                cases h1 : vcgen env st e1 with
                | none => simp [h1] at hvc
                | some r1 =>
                  rcases r1 with ⟨st1, sv1⟩; simp [h1] at hvc; rcases hvc with ⟨rfl, rfl⟩
                  rcases vcgen_wf hMatch.wf h1 with ⟨_, _, _, _, hwf1, hb1⟩
                  have ih1 := go hM hσ hMatch h1 hObs
                  rw [substMany_applyDir]; simp only [List.map]
                  constructor
                  · intro k hk σ' hs
                    rcases stepsN_applyDir_one_terminal (Or.inr ⟨_, rfl⟩) hs with
                      ⟨k1, hk1, tr, hst1, hEq⟩ | ⟨k1, k2, hlt, v1, σ1, fd, hv1, hst1, hfd, _, hbody⟩
                    · cases hEq; exact ih1.1 k1 (by omega) σ' hst1
                    · rw [hIntr.2] at hfd; cases hfd
                      simp only [assumeFunDef, zipParams, List.map, List.zip, substMany, subst, beq_self_eq_true, ↓reduceIte] at hbody
                      rcases stepsN_if_terminal (Or.inr ⟨_, rfl⟩) hbody with
                        ⟨_, _, _, hv1s, hEq⟩ | ⟨_, _, _, _, _, hunit⟩ | ⟨_, _, _, _, _, htrap⟩
                      · rcases stepsN_of_value hv1 hv1s with ⟨_, hEq2, _⟩; subst hEq2; cases hv1
                      · rcases stepsN_of_value (.lit .unit) hunit with ⟨_, hEq, _⟩; cases hEq
                      · rcases stepsN_of_trap htrap with ⟨_, hEq, _⟩; cases hEq
                  · intro k hk v σ' hv hs
                    rcases stepsN_applyDir_one_terminal (Or.inl hv) hs with
                      ⟨_, _, _, _, hEq⟩ | ⟨k1, k2, hlt, v1, σ1, fd, hv1, hst1, hfd, _, hbody⟩
                    · subst hEq; cases hv
                    · rw [hIntr.2] at hfd; cases hfd
                      simp only [assumeFunDef, zipParams, List.map, List.zip, substMany, subst, beq_self_eq_true, ↓reduceIte] at hbody
                      rcases stepsN_if_terminal (Or.inl hv) hbody with
                        ⟨_, _, _, _, hEq⟩ | ⟨_, _, _, σ2, hv1s, hunit⟩ | ⟨_, _, _, _, _, htrap⟩
                      · subst hEq; cases hv
                      · rcases stepsN_of_value hv1 hv1s with ⟨_, rfl, rfl⟩
                        rcases stepsN_of_value (.lit .unit) hunit with ⟨_, rfl, rfl⟩
                        rcases ih1.2 k1 (by omega) (.lit (.bool true)) σ' (.lit _) hst1 with ⟨hσ1, M1, L1, hM1, hag1, hagL1, hMatch1, hev1⟩
                        exact ⟨hσ1, M1, L1, hM1, hag1, hagL1,
                          hMatch1.of_eq (symWf_withPath hwf1 (c := .isTrue sv1) hb1) rfl rfl rfl rfl
                            ⟨hMatch1.path_holds, evalSVal_lit_iff_id.mp hev1⟩, rfl⟩
                      · rcases stepsN_of_trap htrap with ⟨_, hEq, _⟩; subst hEq; cases hv
        · rw [hAssert] at hvc; simp only [↓reduceIte] at hvc
          have hName : name = "assert" := eq_of_beq hAssert
          subst hName
          cases args with
          | nil => simp at hvc
          | cons e1 rest =>
            cases rest with
            | cons _ _ => simp at hvc
            | nil =>
              cases h1 : vcgen env st e1 with
              | none => simp [h1] at hvc
              | some r1 =>
                rcases r1 with ⟨st1, sv1⟩; simp [h1] at hvc; rcases hvc with ⟨rfl, rfl⟩
                rcases vcgen_wf hMatch.wf h1 with ⟨_, _, _, _, hwf1, _⟩
                have hObs1 : ValidObs st1.obs :=
                validObs_mono (fun _ hf => List.mem_cons_of_mem _ hf) (by simpa [emitOb] using hObs)
                have ih1 := go hM hσ hMatch h1 hObs1
                rw [substMany_applyDir]; simp only [List.map]
                constructor
                · intro k hk σ' hs
                  rcases stepsN_applyDir_one_terminal (Or.inr ⟨_, rfl⟩) hs with
                    ⟨k1, hk1, tr, hst1, hEq⟩ | ⟨k1, k2, hlt, v1, σ1, fd, hv1, hst1, hfd, _, hbody⟩
                  · cases hEq; exact ih1.1 k1 (by omega) σ' hst1
                  · rw [hIntr.1] at hfd; cases hfd
                    simp only [assertFunDef, zipParams, List.map, List.zip, substMany, subst, beq_self_eq_true, ↓reduceIte] at hbody
                    rcases ih1.2 k1 (by omega) v1 σ1 hv1 hst1 with ⟨_, M1, L1, hM1, _, _, hMatch1, hev1⟩
                    have hTrue : evalSVal M1 L1 sv1 = some (.lit (.bool true)) :=
                      evalSVal_lit_iff_id.mpr (hObs _ (List.mem_cons_self ..) M1 hM1 hMatch1.path_holds)
                    rw [hTrue] at hev1; cases hev1
                    rcases stepsN_if_terminal (Or.inr ⟨_, rfl⟩) hbody with
                      ⟨_, _, _, hv1s, _⟩ | ⟨_, _, _, _, _, hunit⟩ | ⟨_, _, _, _, hv1s, _⟩
                    · rcases stepsN_of_value (.lit _) hv1s with ⟨_, hEq, _⟩; cases hEq
                    · rcases stepsN_of_value (.lit .unit) hunit with ⟨_, hEq, _⟩; cases hEq
                    · rcases stepsN_of_value (.lit _) hv1s with ⟨_, hEq, _⟩; cases hEq
                · intro k hk v σ' hv hs
                  rcases stepsN_applyDir_one_terminal (Or.inl hv) hs with
                    ⟨_, _, _, _, hEq⟩ | ⟨k1, k2, hlt, v1, σ1, fd, hv1, hst1, hfd, _, hbody⟩
                  · subst hEq; cases hv
                  · rw [hIntr.1] at hfd; cases hfd
                    simp only [assertFunDef, zipParams, List.map, List.zip, substMany, subst, beq_self_eq_true, ↓reduceIte] at hbody
                    rcases ih1.2 k1 (by omega) v1 σ1 hv1 hst1 with ⟨hσ1, M1, L1, hM1, hag1, hagL1, hMatch1, hev1⟩
                    have hTrue : evalSVal M1 L1 sv1 = some (.lit (.bool true)) :=
                      evalSVal_lit_iff_id.mpr (hObs _ (List.mem_cons_self ..) M1 hM1 hMatch1.path_holds)
                    rw [hTrue] at hev1; cases hev1
                    rcases stepsN_if_terminal (Or.inl hv) hbody with
                      ⟨_, _, _, _, hEq⟩ | ⟨_, _, _, σ2, hv1s, hunit⟩ | ⟨_, _, _, _, hv1s, _⟩
                    · subst hEq; cases hv
                    · rcases stepsN_of_value (.lit _) hv1s with ⟨_, _, rfl⟩
                      rcases stepsN_of_value (.lit .unit) hunit with ⟨_, rfl, rfl⟩
                      exact ⟨hσ1, M1, L1, hM1, hag1, hagL1,
                        hMatch1.of_eq ⟨hwf1.vars_bound, hwf1.cells_bound, hwf1.path_bound⟩ rfl rfl rfl rfl hMatch1.path_holds, rfl⟩
                    · rcases stepsN_of_value (.lit _) hv1s with ⟨_, hEq, _⟩; cases hEq
      | _ => simp [vcgen] at hvc
  termination_by sizeOf e
  goBlock {M : Model} {L : Loc → Loc} {st st' : SymState} {ρ : List (Ident × Expr)} {σ : Store}
        {es : List Expr} {sv : SVal}
        (hM : ValidModel M) (hσ : StoreClosed σ) (hMatch : StateMatches M L st ρ σ)
        (hvc : vcgenBlock env st es = some (st', sv)) (hObs : ValidObs st'.obs) :
        SafeExecN Δ Φ bound (.block (es.map (substMany ρ))) σ
          (fun v σ' => StoreClosed σ' ∧
            ∃ M' L', ValidModel M' ∧
              (∀ id < st.nextSym, M' id = M id) ∧
              (∀ k < st.nextLoc, L' k = L k) ∧
              StateMatches M' L' st' ρ σ' ∧
              evalSVal M' L' sv = some v) := by
      cases es with
      | nil =>
        simp [vcgenBlock] at hvc; rcases hvc with ⟨rfl, rfl⟩
        constructor
        · intro k _ σ' hs
          cases hs with
          | step hs1 hrest =>
            cases hs1 with
            | blockEmpty => rcases stepsN_of_value (.lit .unit) hrest with ⟨_, hEq, _⟩; cases hEq
        · intro k _ v σ' hv hs
          cases hs with
          | refl => cases hv
          | step hs1 hrest =>
            cases hs1 with
            | blockEmpty =>
              rcases stepsN_of_value (.lit .unit) hrest with ⟨_, rfl, rfl⟩
              exact ⟨hσ, M, L, hM, fun _ _ => rfl, fun _ _ => rfl, hMatch, rfl⟩
      | cons e1 rest =>
        cases rest with
        | nil =>
          simp only [vcgenBlock] at hvc
          have ih1 := go hM hσ hMatch hvc hObs
          simp only [List.map]
          constructor
          · intro k hk σ' hs
            cases hs with
            | step hs1 hrest =>
              generalize he1 : substMany ρ e1 = e1' at hs1
              cases hs1 with
              | blockSingle => subst he1; exact ih1.1 _ (by omega) σ' hrest
          · intro k hk v σ' hv hs
            cases hs with
            | refl => cases hv
            | step hs1 hrest =>
              generalize he1 : substMany ρ e1 = e1' at hs1
              cases hs1 with
              | blockSingle => subst he1; exact ih1.2 _ (by omega) v σ' hv hrest
        | cons e2 rest' =>
          simp only [vcgenBlock] at hvc
          cases h1 : vcgen env st e1 with
          | none => simp [h1] at hvc
          | some r1 =>
            rcases r1 with ⟨st1, _⟩; simp only [h1] at hvc
            rcases vcgen_wf hMatch.wf h1 with ⟨hs1, hl1, _, _, hwf1, _⟩
            rcases vcgenBlock_wf hwf1 hvc with ⟨_, _, _, ho2, _, _⟩
            have ih1 := go hM hσ hMatch h1 (validObs_mono ho2 hObs)
            simp only [List.map]
            constructor
            · intro k hk σ' hs
              rcases stepsN_blockCons_terminal (Or.inr ⟨_, rfl⟩) hs with
                ⟨k1, hk1, tr, hst1, hEq⟩ | ⟨k1, k2, hlt, v1, σ1, hv1', hst1, hst2⟩
              · cases hEq; exact ih1.1 k1 (by omega) σ' hst1
              · rcases ih1.2 k1 (by omega) v1 σ1 hv1' hst1 with ⟨hσ1, M1, L1, hM1, _, _, hMatch1, _⟩
                exact (goBlock hM1 hσ1 hMatch1 hvc hObs).1 k2 (by omega) σ' hst2
            · intro k hk v σ' hv hs
              rcases stepsN_blockCons_terminal (Or.inl hv) hs with
                ⟨_, _, _, _, hEq⟩ | ⟨k1, k2, hlt, v1, σ1, hv1', hst1, hst2⟩
              · subst hEq; cases hv
              · rcases ih1.2 k1 (by omega) v1 σ1 hv1' hst1 with ⟨hσ1, M1, L1, hM1, hag1, hagL1, hMatch1, _⟩
                rcases (goBlock hM1 hσ1 hMatch1 hvc hObs).2 k2 (by omega) v σ' hv hst2 with ⟨hσ', M2, L2, hM2, hag2, hagL2, hMatch2, hev2⟩
                exact ⟨hσ', M2, L2, hM2,
                  fun id hid => (hag2 id (Nat.lt_of_lt_of_le hid hs1)).trans (hag1 id hid),
                  fun j hj => (hagL2 j (Nat.lt_of_lt_of_le hj hl1)).trans (hagL1 j hj),
                  hMatch2, hev2⟩
  termination_by sizeOf es
  goApplyArgs {M : Model} {L : Loc → Loc} {st st' : SymState} {ρ : List (Ident × Expr)} {σ : Store}
        {prefixVals : List Expr} {es : List Expr} {svs : List SVal} {name : Ident}
        {Post : Expr → Store → Prop}
        (hPref : ∀ v ∈ prefixVals, IsValue v)
        (hM : ValidModel M) (hσ : StoreClosed σ) (hMatch : StateMatches M L st ρ σ)
        (hvc : vcgenList env st es = some (st', svs)) (hObs : ValidObs st'.obs)
        (hCont : ∀ {M' : Model} {L' : Loc → Loc} {vs : List Expr} {σ' : Store},
          ValidModel M' → StoreClosed σ' →
          (∀ id < st.nextSym, M' id = M id) →
          (∀ k < st.nextLoc, L' k = L k) →
          StateMatches M' L' st' ρ σ' →
          (∀ v ∈ vs, IsValue v ∧ freeVars v = []) →
          PairwiseRel (fun sv v => evalSVal M' L' sv = some v) svs vs →
          SafeExecN Δ Φ bound (.applyDir name (prefixVals ++ vs)) σ' Post) :
        SafeExecN Δ Φ bound (.applyDir name (prefixVals ++ es.map (substMany ρ))) σ Post := by
      cases es with
      | nil =>
        simp [vcgenList] at hvc; rcases hvc with ⟨rfl, rfl⟩
        exact hCont hM hσ (fun _ _ => rfl) (fun _ _ => rfl) hMatch (fun _ h => by cases h) .nil
      | cons e1 rest =>
        simp only [vcgenList] at hvc
        cases h1 : vcgen env st e1 with
        | none => simp [h1] at hvc
        | some r1 =>
          rcases r1 with ⟨st1, sv1⟩; simp only [h1] at hvc
          rcases vcgen_wf hMatch.wf h1 with ⟨hs1, hl1, _, _, hwf1, hb1⟩
          have hlb1 := (vcgen_locBound hMatch.wf hMatch.locWf h1).2
          cases h2 : vcgenList env st1 rest with
          | none => simp [h2] at hvc
          | some r2 =>
            rcases r2 with ⟨st2, svs2⟩; simp [h2] at hvc; rcases hvc with ⟨rfl, rfl⟩
            rcases vcgenList_wf hwf1 h2 with ⟨_, _, _, ho2, _, _⟩
            have ih1 := go hM hσ hMatch h1 (validObs_mono ho2 hObs)
            simp only [List.map]
            constructor
            · intro k hk σ' hs
              rcases stepsN_applyDir_cons_terminal hPref (Or.inr ⟨_, rfl⟩) hs with
                ⟨k1, hk1, tr, hst1, hEq⟩ | ⟨k1, k2, hlt, v1, σ1, hv1, hst1, hrest⟩
              · cases hEq; exact ih1.1 k1 (by omega) σ' hst1
              · rcases ih1.2 k1 (by omega) v1 σ1 hv1 hst1 with ⟨hσ1, M1, L1, hM1, hag1, hagL1, hMatch1, hev1⟩
                have hcl1 : freeVars v1 = [] := (evalSVal_closed hM1 hev1).2
                have hPref1 : ∀ v ∈ prefixVals ++ [v1], IsValue v := fun v hv => by
                  rcases List.mem_append.mp hv with hp | h1m
                  · exact hPref v hp
                  · simp at h1m; subst h1m; exact hv1
                have hNext := goApplyArgs (prefixVals := prefixVals ++ [v1]) (name := name) hPref1 hM1 hσ1 hMatch1 h2 hObs
                  (fun {M2 L2 vs2 σ2} hM2 hσ2 hag2 hagL2 hMatch2 hvs2Cl hEv2 => by
                    have hag12 : ∀ id < st.nextSym, M2 id = M id :=
                      fun id hid => (hag2 id (Nat.lt_of_lt_of_le hid hs1)).trans (hag1 id hid)
                    have hagL12 : ∀ j < st.nextLoc, L2 j = L j :=
                      fun j hj => (hagL2 j (Nat.lt_of_lt_of_le hj hl1)).trans (hagL1 j hj)
                    have hev1' : evalSVal M2 L2 sv1 = some v1 :=
                      (evalSVal_loc_agree_lt hlb1 hagL2).trans ((evalSVal_agree_lt hb1 hag2).trans hev1)
                    have hvsCl' : ∀ v ∈ v1 :: vs2, IsValue v ∧ freeVars v = [] := fun v hv => by
                      rcases List.mem_cons.mp hv with rfl | hv2
                      · exact ⟨hv1, hcl1⟩
                      · exact hvs2Cl v hv2
                    have hApp := hCont hM2 hσ2 hag12 hagL12 hMatch2 hvsCl' (.cons hev1' hEv2)
                    simpa only [List.append_assoc, List.singleton_append] using hApp)
                exact hNext.1 k2 (by omega) σ' (by simpa only [List.append_assoc, List.singleton_append] using hrest)
            · intro k hk v σ' hv hs
              rcases stepsN_applyDir_cons_terminal hPref (Or.inl hv) hs with
                ⟨_, _, _, _, hEq⟩ | ⟨k1, k2, hlt, v1, σ1, hv1, hst1, hrest⟩
              · subst hEq; cases hv
              · rcases ih1.2 k1 (by omega) v1 σ1 hv1 hst1 with ⟨hσ1, M1, L1, hM1, hag1, hagL1, hMatch1, hev1⟩
                have hcl1 : freeVars v1 = [] := (evalSVal_closed hM1 hev1).2
                have hPref1 : ∀ v ∈ prefixVals ++ [v1], IsValue v := fun v hv => by
                  rcases List.mem_append.mp hv with hp | h1m
                  · exact hPref v hp
                  · simp at h1m; subst h1m; exact hv1
                have hNext := goApplyArgs (prefixVals := prefixVals ++ [v1]) (name := name) hPref1 hM1 hσ1 hMatch1 h2 hObs
                  (fun {M2 L2 vs2 σ2} hM2 hσ2 hag2 hagL2 hMatch2 hvs2Cl hEv2 => by
                    have hag12 : ∀ id < st.nextSym, M2 id = M id :=
                      fun id hid => (hag2 id (Nat.lt_of_lt_of_le hid hs1)).trans (hag1 id hid)
                    have hagL12 : ∀ j < st.nextLoc, L2 j = L j :=
                      fun j hj => (hagL2 j (Nat.lt_of_lt_of_le hj hl1)).trans (hagL1 j hj)
                    have hev1' : evalSVal M2 L2 sv1 = some v1 :=
                      (evalSVal_loc_agree_lt hlb1 hagL2).trans ((evalSVal_agree_lt hb1 hag2).trans hev1)
                    have hvsCl' : ∀ v ∈ v1 :: vs2, IsValue v ∧ freeVars v = [] := fun v hv => by
                      rcases List.mem_cons.mp hv with rfl | hv2
                      · exact ⟨hv1, hcl1⟩
                      · exact hvs2Cl v hv2
                    have hApp := hCont hM2 hσ2 hag12 hagL12 hMatch2 hvsCl' (.cons hev1' hEv2)
                    simpa only [List.append_assoc, List.singleton_append] using hApp)
                exact hNext.2 k2 (by omega) v σ' hv (by simpa only [List.append_assoc, List.singleton_append] using hrest)
  termination_by sizeOf es

/-- **Theorem 1 (`vcgen_sound`)**:
    Assume-Guarantee modular soundness of `vcgen`:
    If all callees in `env.contracts` satisfy `CalleeSound Δ Φ env bound` for every step bound,
    `vcgen env st e = some (st', sv)`, and all generated obligations in `st'.obs` are valid,
    then starting from any concrete state `(ρ, σ)` matching `(M, L, st)`:
    1. Execution of `substMany ρ e` in `σ` NEVER traps with `Trap.divByZero`;
    2. Every terminating run to a value `v` in store `σ'` preserves `StoreClosed σ'` and
       extends `(M, L)` to `(M', L')` matching `(st', ρ, σ')` with `evalSVal M' L' sv = some v`. -/
theorem vcgen_sound {Δ : AdtEnv} {Φ : FunEnv} {env : VcgEnv}
    (hIntr : IntrinsicsOk Φ) (hCallee : ∀ bound, CalleeSound Δ Φ env bound)
    {M : Model} {L : Loc → Loc} {st st' : SymState} {ρ : List (Ident × Expr)} {σ : Store} {e : Expr} {sv : SVal}
    (hM : ValidModel M) (hσ : StoreClosed σ) (hMatch : StateMatches M L st ρ σ)
    (hvc : vcgen env st e = some (st', sv)) (hObs : ValidObs st'.obs) :
    SafeExec Δ Φ (substMany ρ e) σ
      (fun v σ' => StoreClosed σ' ∧
        ∃ M' L', ValidModel M' ∧
          (∀ id < st.nextSym, M' id = M id) ∧
          (∀ k < st.nextLoc, L' k = L k) ∧
          StateMatches M' L' st' ρ σ' ∧
          evalSVal M' L' sv = some v) :=
  safeExec_of_forall_safeExecN fun bound =>
    vcgen_sound_step hIntr bound (hCallee bound) hM hσ hMatch hvc hObs

/-- `initFnSymState` always produces a well-formed symbolic state whenever it succeeds. -/
theorem initFnSymState_wf {params : List (Ident × Ty)} {st : SymState}
    (h : initFnSymState params = some st) : SymWf st := by
  suffices ∀ (ps : List (Ident × Ty)) (s st' : SymState), SymWf s →
      ps.foldlM (fun (s : SymState) (p : Ident × Ty) =>
        match p.2 with
        | .cell elemTy =>
          if isModeledScalarTy elemTy then
            let l := s.nextLoc
            let id := s.nextSym
            some { s with
              nextSym := id + 1
              nextLoc := l + 1
              vars := (p.1, .loc l) :: s.vars
              cells := (l, .sym id) :: s.cells
              cellTys := (l, elemTy) :: s.cellTys
              path := .and s.path (.hasTy (.sym id) elemTy) }
          else none
        | ty =>
          if isModeledScalarTy ty then
            let id := s.nextSym
            some { s with
              nextSym := id + 1
              vars := (p.1, .sym id) :: s.vars
              path := .and s.path (.hasTy (.sym id) ty) }
          else none) s = some st' → SymWf st' by
    exact this params {} st ⟨(fun _ h => by cases h), (fun _ h => by cases h), trivial⟩ h
  intro ps
  induction ps with
  | nil => intro s st' hs hfold; simp at hfold; subst hfold; exact hs
  | cons p rest ih =>
    intro s st' hs hfold
    simp only [List.foldlM] at hfold
    cases hty : p.2 with
    | cell elemTy =>
      simp only [hty] at hfold
      split at hfold
      · simp only [bind, Option.bind] at hfold
        apply ih _ _ _ hfold
        refine ⟨?_, ?_, ⟨sformBound_mono (Nat.le_succ _) hs.path_bound, Nat.lt_succ_self _⟩⟩
        · intro q hq; rcases List.mem_cons.mp hq with rfl | hq'
          · trivial
          · exact svalBound_mono (Nat.le_succ _) (hs.vars_bound q hq')
        · intro q hq; rcases List.mem_cons.mp hq with rfl | hq'
          · exact ⟨Nat.lt_succ_self _, Nat.lt_succ_self _⟩
          · exact ⟨Nat.lt_succ_of_lt (hs.cells_bound q hq').1, svalBound_mono (Nat.le_succ _) (hs.cells_bound q hq').2⟩
      · simp at hfold
    | _ =>
      simp only [hty] at hfold
      split at hfold
      · simp only [bind, Option.bind] at hfold
        apply ih _ _ _ hfold
        refine ⟨?_, ?_, ⟨sformBound_mono (Nat.le_succ _) hs.path_bound, Nat.lt_succ_self _⟩⟩
        · intro q hq; rcases List.mem_cons.mp hq with rfl | hq'
          · exact Nat.lt_succ_self _
          · exact svalBound_mono (Nat.le_succ _) (hs.vars_bound q hq')
        · intro q hq; exact ⟨(hs.cells_bound q hq).1, svalBound_mono (Nat.le_succ _) (hs.cells_bound q hq).2⟩
      · simp at hfold

/-- **Theorem 2 (`verifyFn_sound`)**:
    Modular function-level contract soundness over ANY pre-existing heap `σ` and injective
    location map `L`: if `verifyFn env fd fc = some obs`, `ValidObs obs`, and every callee
    in `env.contracts` satisfies `CalleeSound`, then for any concrete call `.applyDir fd.name vs`
    in store `σ` matching `initFnSymState fd.params` under `(M, L)` where `fc.req` evaluates
    to `true`:
    1. Calling `.applyDir fd.name vs` NEVER traps with `Trap.divByZero`;
    2. Whenever `.applyDir fd.name vs` terminates to a value `v` in store `σ'`, the postcondition
       `fc.ens` evaluates to `.lit (.bool true)` in `((fc.retVar, v) :: zipParams fd.params vs, σ')`. -/
theorem verifyFn_sound {Δ : AdtEnv} {Φ : FunEnv} {env : VcgEnv}
    (hIntr : IntrinsicsOk Φ) (hCallee : ∀ bound, CalleeSound Δ Φ env bound)
    {fd : FunDef} {fc : FnContract} {obs : List SForm} {initSt : SymState}
    (hΦ : Φ fd.name = some fd)
    (hInit : initFnSymState fd.params = some initSt)
    (hver : verifyFn env fd fc = some obs) (hObs : ValidObs obs)
    {M : Model} {L : Loc → Loc} {vs : List Expr} {σ : Store}
    (hM : ValidModel M) (hσ : StoreClosed σ)
    (hvs : ∀ v ∈ vs, IsValue v) (hlen : vs.length = fd.params.length)
    (hMatchInit : StateMatches M L initSt (zipParams fd.params vs) σ)
    (hReq : Steps Δ Φ (substMany (zipParams fd.params vs) fc.req) σ (.lit (.bool true)) σ) :
    SafeExec Δ Φ (.applyDir fd.name vs) σ
      (fun v σ' =>
        Steps Δ Φ (substMany ((fc.retVar, v) :: zipParams fd.params vs) fc.ens) σ' (.lit (.bool true)) σ') := by
  simp only [verifyFn] at hver
  split at hver
  · cases hver
  · rw [hInit] at hver; simp only at hver
    cases hReqVc : vcgenPure initSt fc.req with
    | none => simp [hReqVc] at hver
    | some rReq =>
      rcases rReq with ⟨stReq, svReq⟩; simp only [hReqVc] at hver
      rcases vcgenPure_wf hMatchInit.wf hReqVc with ⟨hsReq, hlReq, hvReq, hcReq, hpReq, hoReq, hbReq⟩
      have hctReq : stReq.cellTys = initSt.cellTys := vcgenPure_cellTys_eq hReqVc
      have hwfReq0 : SymWf (withPath stReq (.isTrue svReq)) :=
        ⟨by simp only [withPath, hsReq, hvReq]; exact hMatchInit.wf.vars_bound,
         by simp only [withPath, hsReq, hlReq, hcReq]; exact hMatchInit.wf.cells_bound,
         by simp only [withPath, sformBound, hsReq, hpReq]; exact ⟨hMatchInit.wf.path_bound, hbReq⟩⟩
      cases hDecOpt : checkLoopPreDec (withPath stReq (.isTrue svReq)) fc.dec with
      | none => simp [hDecOpt] at hver
      | some rDec =>
        rcases rDec with ⟨stAssumed, curDecOpt⟩; simp only [hDecOpt] at hver
        rcases checkLoopPreDec_props hwfReq0 hDecOpt with
          ⟨hsD, hlD, hvD, hcD, hctD, hpD, hoA, hwfAssumed⟩
        have hsA : stAssumed.nextSym = initSt.nextSym := hsD.trans hsReq
        have hlA : stAssumed.nextLoc = initSt.nextLoc := hlD.trans hlReq
        have hvA : stAssumed.vars = initSt.vars := hvD.trans hvReq
        have hcA : stAssumed.cells = initSt.cells := hcD.trans hcReq
        have hctA : stAssumed.cellTys = initSt.cellTys := hctD.trans hctReq
        have hpA : stAssumed.path = .and initSt.path (.isTrue svReq) := by
          rw [hpD]; simp only [withPath, hpReq]
        cases hBodyVc : vcgen { env with curFn := fd.name, curDec := curDecOpt } stAssumed fd.body with
        | none => simp [hBodyVc] at hver
        | some rBody =>
          rcases rBody with ⟨stBody, svRet⟩; simp only [hBodyVc] at hver
          rcases vcgen_wf hwfAssumed hBodyVc with ⟨_, _, hvBody, hoBody, hwfBody, hbRet⟩
          have hlbRet : svalLocBound stBody.nextLoc svRet :=
            (vcgen_locBound hwfAssumed ⟨by rw [hvA, hlA]; exact hMatchInit.locWf.1, by rw [hcA, hlA]; exact hMatchInit.locWf.2⟩ hBodyVc).2
          have hwfEnsIn : SymWf { stBody with vars := (fc.retVar, svRet) :: stBody.vars } :=
            ⟨fun p hp => by rcases List.mem_cons.mp hp with rfl | hp'; exact hbRet; exact hwfBody.vars_bound p hp',
             hwfBody.cells_bound, hwfBody.path_bound⟩
          cases hEnsVc : vcgenPure { stBody with vars := (fc.retVar, svRet) :: stBody.vars } fc.ens with
          | none => simp [hEnsVc] at hver
          | some rEns =>
            rcases rEns with ⟨stEns, svEns⟩; simp [hEnsVc] at hver; subst hver
            rcases vcgenPure_wf hwfEnsIn hEnsVc with ⟨_, _, _, _, hpEns, hoEns, _⟩
            have hObsEns : ValidObs stEns.obs := validObs_mono (fun _ hf => List.mem_cons_of_mem _ hf) hObs
            have hObsBody : ValidObs stBody.obs := validObs_mono hoEns hObsEns
            have hObsAssumed : ValidObs stAssumed.obs := validObs_mono hoBody hObsBody
            have hObsReq : ValidObs stReq.obs := validObs_mono hoA hObsAssumed
            have hReqTrue : evalSVal M L svReq = some (.lit (.bool true)) :=
              ((vcgenPure_sound (Δ := Δ) (Φ := Φ) hM hMatchInit hReqVc hObsReq).2 (.lit (.bool true)) σ (.lit _) hReq).2
            have hMatchAssumed : StateMatches M L stAssumed (zipParams fd.params vs) σ :=
              hMatchInit.of_eq hwfAssumed hlA hvA hcA hctA (by rw [hpA]; exact ⟨hMatchInit.path_holds, evalSVal_lit_iff_id.mp hReqTrue⟩)
            have hCalleeBody : ∀ bound, CalleeSound Δ Φ { env with curFn := fd.name, curDec := curDecOpt } bound :=
              fun b => by simpa [CalleeSound] using hCallee b
            have hBodySafe := vcgen_sound (Δ := Δ) (Φ := Φ) hIntr hCalleeBody hM hσ hMatchAssumed hBodyVc hObsBody
            constructor
            · intro σ' hsteps
              rcases steps_to_stepsN hsteps with ⟨n, hn⟩
              rcases stepsN_applyDir_vals_terminal hvs (Or.inr ⟨_, rfl⟩) hn with ⟨m, _, fd', hΦ', _, hbody⟩
              rw [hΦ] at hΦ'; cases hΦ'
              exact hBodySafe.1 σ' (stepsN_to_steps hbody)
            · intro v σ' hv hsteps
              rcases steps_to_stepsN hsteps with ⟨n, hn⟩
              rcases stepsN_applyDir_vals_terminal hvs (Or.inl hv) hn with ⟨m, _, fd', hΦ', _, hbody⟩
              rw [hΦ] at hΦ'; cases hΦ'
              rcases hBodySafe.2 v σ' hv (stepsN_to_steps hbody) with ⟨_, M', L', hM', _, _, hMatchBody, hevRet⟩
              have hclV : freeVars v = [] := (evalSVal_closed hM' hevRet).2
              have hMatchEns : StateMatches M' L' { stBody with vars := (fc.retVar, svRet) :: stBody.vars }
                  ((fc.retVar, v) :: zipParams fd.params vs) σ' :=
                { closed_env := fun p hp => by rcases List.mem_cons.mp hp with rfl | hp'; exact ⟨hv, hclV⟩; exact hMatchBody.closed_env p hp',
                  wf := hwfEnsIn, loc_bound := hMatchBody.loc_bound, loc_inj := hMatchBody.loc_inj,
                  path_holds := hMatchBody.path_holds,
                  vars_match := fun y svy hlu => by
                    simp only [assocLookup] at hlu ⊢
                    cases hxy : (fc.retVar == y)
                    · simp [hxy] at hlu ⊢; exact hMatchBody.vars_match y svy hlu
                    · simp [hxy] at hlu ⊢; subst hlu; exact ⟨hevRet, hlbRet⟩,
                  cells_match := hMatchBody.cells_match, cells_ty := hMatchBody.cells_ty }
              have hEnsTrue : evalSVal M' L' svEns = some (.lit (.bool true)) :=
                evalSVal_lit_iff_id.mpr (hObs _ (List.mem_cons_self ..) M' hM' (by rw [hpEns]; exact hMatchBody.path_holds))
              exact vcgenPure_complete (Δ := Δ) (Φ := Φ) hM' hMatchEns hEnsVc hEnsTrue

/-! ### Non-Vacuity Witnesses for R1 (`CalleeSound`) and R4 (`ValidObs` + arbitrary initial heap `σ`) -/

/-- Concrete `identity(x: Int): Int ensures r -> r == x = x` witness definition and contract. -/
def idWitnessFd : FunDef :=
  { name := "identity", params := [("x", .int)], retTy := .int, body := .var "x" }

def idWitnessFc : FnContract :=
  { params := [("x", .int)], retTy := .int,
    req := .lit (.bool true), retVar := "r", ens := .bin .eqInt (.var "r") (.var "x") }

/-- **R4 Non-Vacuity Witness (`identity_verified_nonvacuous`)**:
    Proves directly in the Lean kernel (zero `sorry`) that:
    1. `verifyFn {} idWitnessFd idWitnessFc` succeeds with obligations `obs`;
    2. `ValidObs obs` holds for ALL `ValidModel M` (impossible without `SForm.hasTy`!);
    3. `verifyFn_sound` instantiates on ANY pre-existing heap `σ : Store` (`StoreClosed σ`)
       and ANY `n : Int32`, proving `SafeExec` and `ensures r -> r == x`! -/
theorem identity_verified_nonvacuous
    {Φ : FunEnv} (hIntr : IntrinsicsOk Φ) (hΦ : Φ "identity" = some idWitnessFd)
    (σ : Store) (hσ : StoreClosed σ) (n : Int32) :
    ∃ obs, verifyFn {} idWitnessFd idWitnessFc = some obs ∧ ValidObs obs ∧
      SafeExec emptyAdtEnv Φ (.applyDir "identity" [.lit (.int n)]) σ
        (fun v σ' =>
          Steps emptyAdtEnv Φ
            (substMany (("r", v) :: zipParams idWitnessFd.params [.lit (.int n)]) idWitnessFc.ens)
            σ' (.lit (.bool true)) σ') := by
  have hInit : initFnSymState idWitnessFd.params =
      some { nextSym := 1, nextLoc := 0, vars := [("x", .sym 0)], cells := [], cellTys := [],
             path := .and .tt (.hasTy (.sym 0) .int), obs := [] } := rfl
  have hVer : verifyFn {} idWitnessFd idWitnessFc =
      some [.imp (.and (.and .tt (.hasTy (.sym 0) .int)) (.isTrue (.lit (.bool true))))
                 (.isTrue (.bin .eqInt (.sym 0) (.sym 0)))] := by
    unfold verifyFn
    rw [hInit]
    simp [idWitnessFd, idWitnessFc, vcgenPure, vcgen, assocLookup, withPath, emitOb, checkLoopPreDec,
      isModeledScalarTy, isModeledLit, isModeledStrictBinOp, isDivOp]
  have hObs : ValidObs [.imp (.and (.and .tt (.hasTy (.sym 0) .int)) (.isTrue (.lit (.bool true))))
                             (.isTrue (.bin .eqInt (.sym 0) (.sym 0)))] := by
    intro f hf M _
    simp only [List.mem_singleton] at hf; subst hf
    intro hP
    rcases hP with ⟨⟨_, ⟨v0, hev0, ⟨k, rfl⟩⟩⟩, _⟩
    simp only [evalSVal] at hev0
    simp [evalSForm, evalSVal, hev0, evalBinOp]
  refine ⟨_, hVer, hObs, ?_⟩
  let M0 : Model := fun _ => .lit (.int n)
  have hM0 : ValidModel M0 := fun _ => ⟨.lit _, rfl⟩
  have hMatch0 : StateMatches M0 id
      { nextSym := 1, nextLoc := 0, vars := [("x", .sym 0)], cells := [], cellTys := [],
        path := .and .tt (.hasTy (.sym 0) .int), obs := [] }
      (zipParams idWitnessFd.params [.lit (.int n)]) σ := by
    refine ⟨?_, ?_, (fun _ h => by simp at h), (fun _ _ h _ _ => by simp at h), ?_, ?_, (fun _ _ h => by cases h), (fun _ _ h => by cases h)⟩
    · intro p hp; simp [idWitnessFd, zipParams] at hp; rcases hp with ⟨rfl, rfl⟩; exact ⟨.lit _, rfl⟩
    · exact initFnSymState_wf hInit
    · exact ⟨trivial, ⟨.lit (.int n), rfl, ⟨n, rfl⟩⟩⟩
    · intro x sv hlu
      simp only [assocLookup] at hlu
      cases hEq : ("x" == x)
      · simp [hEq] at hlu
      · simp [hEq] at hlu; subst hlu
        have hx : x = "x" := (eq_of_beq hEq).symm; subst hx
        exact ⟨.lit (.int n), rfl, rfl, trivial⟩
  have hCalleeEmpty : ∀ bound, CalleeSound emptyAdtEnv Φ {} bound := by
    intro _ _ _ _ _ _ hfc; simp at hfc
  exact verifyFn_sound hIntr hCalleeEmpty hΦ hInit hVer hObs hM0 hσ
    (fun v hv => by simp at hv; subst hv; exact .lit _) rfl hMatch0 (.refl _ _)

/-- Concrete local `cellNew(0)` + `while (false) invariant true { () }` + `cellGet(c)` witness for T1. -/
def localCellWhileBody : Expr :=
  .let_ "c" (.cellNew (.lit (.int 0)))
    (.block [.while_ (.lit (.bool false)) (.lit .unit), .cellGet (.var "c")])

def localCellWhileFd : FunDef :=
  { name := "localCellWhile", params := [], retTy := .int, body := localCellWhileBody }

def localCellWhileFc : FnContract :=
  { params := [], retTy := .int,
    req := .lit (.bool true), retVar := "__gs_res",
    ens := .bin .eqInt (.var "__gs_res") (.var "__gs_res") }

def localCellWhileEnv : VcgEnv :=
  { loops := fun c b =>
      match c, b with
      | .lit (.bool false), .lit .unit => some { inv := .lit (.bool true) }
      | _, _ => none }

set_option maxHeartbeats 400000 in
/-- **T1 Non-Vacuity Witness (`local_cell_while_verified_nonvacuous`)**:
    Proves directly in the Lean 4 kernel that a function allocating a local `Cell<Int>`
    via `cellNew(0)`, running a `while (false) invariant (true)` loop (which havocs `c`),
    and returning `cellGet(c)` with `ensures __gs_res == __gs_res` succeeds in `verifyFn`
    AND every generated obligation satisfies `ValidObs` for ALL `ValidModel M`!
    (This was previously `¬ ValidForm` before `cellNew` recorded `(l, elemTy)` in `cellTys`.) -/
theorem local_cell_while_verified_nonvacuous :
    ∃ obs, verifyFn localCellWhileEnv localCellWhileFd localCellWhileFc = some obs ∧ ValidObs obs := by
  let bodyEnv : VcgEnv := { localCellWhileEnv with curFn := "localCellWhile", curDec := none }
  let st0 : SymState :=
    { nextSym := 0, nextLoc := 0, vars := [], cells := [], cellTys := [],
      path := .and .tt (.isTrue (.lit (.bool true))), obs := [] }
  let ob0 : SForm := .imp st0.path (.hasTy (.lit (.int 0)) .int)
  let st1 : SymState :=
    { nextSym := 0, nextLoc := 1, vars := [("c", .loc 0)],
      cells := [(0, .lit (.int 0))], cellTys := [(0, .int)],
      path := st0.path, obs := [ob0] }
  let ob1 : SForm := .imp st0.path (.isTrue (.lit (.bool true)))
  let ob2 : SForm :=
    .imp (.and (.and (.and st0.path (.hasTy (.sym 0) .int))
                     (.isTrue (.lit (.bool true))))
               (.isTrue (.lit (.bool false))))
         (.isTrue (.lit (.bool true)))
  let st2 : SymState :=
    { nextSym := 1, nextLoc := 1, vars := [("c", .loc 0)],
      cells := [(0, .sym 0), (0, .lit (.int 0))], cellTys := [(0, .int)],
      path := .and (.and (.and st0.path (.hasTy (.sym 0) .int))
                         (.isTrue (.lit (.bool true))))
                   (.isFalse (.lit (.bool false))),
      obs := [ob2, ob1, ob0] }
  let ob3 : SForm := .imp st2.path (.isTrue (.bin .eqInt (.sym 0) (.sym 0)))
  have hInit : initFnSymState localCellWhileFd.params = some ({} : SymState) := rfl
  have hNew : vcgen bodyEnv st0 (.cellNew (.lit (.int 0))) =
      some ({ st1 with vars := [] }, .loc 0) := by
    have hLit0 : vcgen bodyEnv st0 (.lit (.int 0)) = some (st0, .lit (.int 0)) := by
      rw [vcgen]; rfl
    rw [vcgen, hLit0]; rfl
  have hWhile : vcgen bodyEnv st1 (.while_ (.lit (.bool false)) (.lit .unit)) =
      some (st2, .lit .unit) := by
    have hLitF : ∀ (e0 : VcgEnv) s, vcgen e0 s (.lit (.bool false)) = some (s, .lit (.bool false)) := by
      intro e0 s; rw [vcgen]; simp only [isModeledLit, ↓reduceIte]
    have hLitU : ∀ (e0 : VcgEnv) s, vcgen e0 s (.lit .unit) = some (s, .lit .unit) := by
      intro e0 s; rw [vcgen]; simp only [isModeledLit, ↓reduceIte]
    rw [vcgen]
    simp only [bodyEnv, localCellWhileEnv, vcgenPure, isModeledLit, emitOb, havocCells,
      trackedLocs, locLookup, withPath, hLitF, hLitU, checkLoopPreDec, checkLoopPostDec,
      st0, st1, st2, ob0, ob1, ob2, List.map, List.foldl, bne_self_eq_false, ↓reduceIte,
      beq_self_eq_true]
    rfl
  have hGet : vcgen bodyEnv st2 (.cellGet (.var "c")) = some (st2, .sym 0) := by
    have hVarC : vcgen bodyEnv st2 (.var "c") = some (st2, .loc 0) := by
      rw [vcgen]; simp only [st2, assocLookup, beq_self_eq_true, ↓reduceIte]
    rw [vcgen]; simp only [hVarC, st2, locLookup, beq_self_eq_true, ↓reduceIte]
  have hBody : vcgen bodyEnv st0 localCellWhileBody = some ({ st2 with vars := [] }, .sym 0) := by
    unfold localCellWhileBody
    rw [vcgen]
    simp only [hNew]
    change (match vcgen bodyEnv st1 (.block [.while_ (.lit (.bool false)) (.lit .unit), .cellGet (.var "c")]) with
      | none => none
      | some (stB, svB) => some ({ stB with vars := [] }, svB)) = some ({ st2 with vars := [] }, .sym 0)
    rw [vcgen]
    rw [vcgenBlock]
    simp only [hWhile]
    rw [vcgenBlock]
    simp only [hGet]
  have hReq : vcgenPure ({} : SymState) (.lit (.bool true)) = some ({}, .lit (.bool true)) := by
    simp [vcgenPure, isModeledLit]
  have hVer : verifyFn localCellWhileEnv localCellWhileFd localCellWhileFc =
      some [ob3, ob2, ob1, ob0] := by
    unfold verifyFn
    rw [hInit]
    simp only [localCellWhileFd, localCellWhileFc, List.length_nil, bne_self_eq_false, ↓reduceIte,
      hReq, withPath, checkLoopPreDec]
    have hBody' : vcgen { localCellWhileEnv with curFn := "localCellWhile", curDec := none }
        { nextSym := 0, nextLoc := 0, vars := [], cells := [], cellTys := [],
          path := .and .tt (.isTrue (.lit (.bool true))), obs := [] }
        localCellWhileBody = some ({ st2 with vars := [] }, .sym 0) := hBody
    rw [hBody']
    simp [vcgenPure, assocLookup, isModeledStrictBinOp, isDivOp, emitOb, st2, ob3]
  refine ⟨[ob3, ob2, ob1, ob0], hVer, ?_⟩
  intro f hf M _
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hf
  rcases hf with rfl | rfl | rfl | rfl
  · intro hP
    rcases hP with ⟨⟨⟨_, ⟨v0, hev0, ⟨k, rfl⟩⟩⟩, _⟩, _⟩
    simp only [evalSVal] at hev0
    simp [evalSForm, evalSVal, hev0, evalBinOp]
  · intro _; simp [evalSForm, evalSVal]
  · intro _; simp [evalSForm, evalSVal]
  · intro _; exact ⟨.lit (.int 0), rfl, ⟨0, rfl⟩⟩

/-- Concrete `safeDiv(a: Int, b: Int): Int requires b != 0` callee witness for R1. -/
def safeDivWitnessFd : FunDef :=
  { name := "safeDiv", params := [("a", .int), ("b", .int)], retTy := .int,
    body := .bin .div (.var "a") (.var "b") }

def safeDivWitnessFc : FnContract :=
  { params := [("a", .int), ("b", .int)], retTy := .int,
    req := .bin .neInt (.var "b") (.lit (.int 0)),
    retVar := "r", ens := .lit (.bool true) }

/-- **R1 Non-Vacuity Witness (`calleeSound_safeDiv_witness`)**:
    Proves directly in the Lean kernel (zero `sorry`) that `CalleeSound` is non-vacuously
    inhabited by a real contract-bearing callee `safeDiv(a, b) requires b != 0` in `env.contracts`,
    so `vcgen_sound` and `verifyFn_sound` genuinely verify modular callers! -/
theorem calleeSound_safeDiv_witness {Φ : FunEnv} (hΦ : Φ "safeDiv" = some safeDivWitnessFd) :
    ∀ bound, CalleeSound emptyAdtEnv Φ
      { contracts := fun n => if n == "safeDiv" then some safeDivWitnessFc else none } bound := by
  intro bound name fc fd vs σ hfc hfd hlen hvsCl hσCl _ hReq
  simp only at hfc
  split at hfc
  · rename_i hNameEq
    have hName : name = "safeDiv" := eq_of_beq hNameEq
    subst hName
    cases hfc
    rw [hΦ] at hfd; cases hfd
    cases vs with
    | nil => simp [safeDivWitnessFc] at hlen
    | cons v1 vs1 =>
      cases vs1 with
      | nil => simp [safeDivWitnessFc] at hlen
      | cons v2 vs2 =>
        cases vs2 with
        | cons _ _ => simp [safeDivWitnessFc] at hlen
        | nil =>
          have hv1 : IsValue v1 := (hvsCl v1 (by simp)).1
          have hv2 : IsValue v2 := (hvsCl v2 (by simp)).1
          have hcl1 : freeVars v1 = [] := (hvsCl v1 (by simp)).2
          have hcl2 : freeVars v2 = [] := (hvsCl v2 (by simp)).2
          have hClosed2 : ClosedEnv (zipParams safeDivWitnessFc.params [v1, v2]) := by
            intro p hp; simp [safeDivWitnessFc, zipParams] at hp
            rcases hp with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
            · exact ⟨hv1, hcl1⟩
            · exact ⟨hv2, hcl2⟩
          have hReqEq : substMany (zipParams safeDivWitnessFc.params [v1, v2]) safeDivWitnessFc.req =
              .bin .neInt v2 (.lit (.int 0)) := by
            change substMany (zipParams safeDivWitnessFc.params [v1, v2]) (.bin .neInt (.var "b") (.lit (.int 0))) = _
            rw [substMany_bin, substMany_var hClosed2, substMany_lit]
            rfl
          rw [hReqEq] at hReq
          rcases steps_to_stepsN hReq with ⟨kr, hkr⟩
          rcases stepsN_bin_strict_terminal (by decide) (by decide) (Or.inl (.lit _)) hkr with
            ⟨_, _, _, _, hEq⟩ | ⟨_, _, _, _, _, _, _, _, _, hEq⟩ | ⟨_, _, _, l1, l2, σ1, r, hs1, hs2, hev, hres⟩
          · cases hEq
          · cases hEq
          · rcases stepsN_of_value hv2 hs1 with ⟨_, rfl, rfl⟩
            rcases stepsN_of_value (.lit (.int 0)) hs2 with ⟨_, hEq0, _⟩
            cases hEq0
            cases l1 with
            | int b =>
              cases r with
              | trap _ => cases hres
              | val lv =>
                cases hres
                simp only [evalBinOp, Option.some.injEq, BinEvalResult.val.injEq] at hev
                have hbne : b ≠ 0 := by
                  intro hb0; subst hb0; simp at hev
                have hBodyEq : substMany (zipParams safeDivWitnessFd.params [v1, .lit (.int b)]) safeDivWitnessFd.body =
                    .bin .div v1 (.lit (.int b)) := by
                  change substMany (zipParams safeDivWitnessFc.params [v1, .lit (.int b)]) (.bin .div (.var "a") (.var "b")) = _
                  rw [substMany_bin, substMany_var hClosed2, substMany_var hClosed2]
                  rfl
                rw [hBodyEq]
                constructor
                · intro k _ σ' hs
                  rcases stepsN_bin_strict_terminal (by decide) (by decide) (Or.inr ⟨_, rfl⟩) hs with
                    ⟨_, _, _, h1, _⟩ | ⟨_, _, _, _, _, _, _, _, h2, _⟩ | ⟨_, _, _, la, lb, _, rb, h1, h2, hevD, hresD⟩
                  · rcases stepsN_of_value hv1 h1 with ⟨_, hEq, _⟩; subst hEq; cases hv1
                  · rcases stepsN_of_value (.lit (.int b)) h2 with ⟨_, hEq, _⟩; cases hEq
                  · rcases stepsN_of_value (.lit (.int b)) h2 with ⟨_, hEqb, _⟩; cases hEqb
                    cases la <;> simp [evalBinOp] at hevD
                    split at hevD
                    · rename_i hb0; exact hbne hb0
                    · cases hevD; cases hresD
                · intro k _ v σ' hv hs
                  rcases stepsN_bin_strict_terminal (by decide) (by decide) (Or.inl hv) hs with
                    ⟨_, _, _, _, hEq⟩ | ⟨_, _, _, _, _, _, _, _, _, hEq⟩ | ⟨_, _, _, la, lb, _, rb, h1, h2, hevD, hresD⟩
                  · subst hEq; cases hv
                  · subst hEq; cases hv
                  · rcases stepsN_of_value hv1 h1 with ⟨_, rfl, rfl⟩
                    rcases stepsN_of_value (.lit (.int b)) h2 with ⟨_, hEqb, rfl⟩; cases hEqb
                    cases la with
                    | int a =>
                      have hbneB : (b == 0) = false := beq_false_of_ne hbne
                      simp only [evalBinOp, hbneB, Bool.false_eq_true, ↓reduceIte, Option.some.injEq] at hevD
                      subst hevD; subst hresD
                      refine ⟨rfl, ⟨a / b, rfl⟩, Nat.le_refl _, hσCl, (fun _ _ _ => rfl), ?_, ?_⟩
                      · intro p vArg hp elemTy l hty _
                        simp [safeDivWitnessFc] at hp
                        rcases hp with ⟨rfl, _⟩ | ⟨rfl, _⟩ <;> cases hty
                      · change Steps emptyAdtEnv Φ (substMany _ (.lit (.bool true))) σ' (.lit (.bool true)) σ'
                        rw [substMany_lit]; exact .refl _ _
                    | _ => simp [evalBinOp] at hevD
            | _ => simp [evalBinOp] at hev
  · cases hfc

/-! ## Part 6: Well-Founded Loop Termination (`while_decreases_terminates`) -/

/-- **Theorem 3 (`while_decreases_terminates`)**:
    Total termination of `.while_ c b` under a loop invariant `I : Store → Prop` and a
    non-negative ranking function `D : Store → Nat` that strictly decreases on every
    iteration where `c` evaluates to `true`. -/
theorem while_decreases_terminates {Δ : AdtEnv} {Φ : FunEnv}
    (c b : Expr) (I : Store → Prop) (D : Store → Nat)
    (hCond : ∀ σ, I σ → ∃ bval : Bool, Steps Δ Φ c σ (.lit (.bool bval)) σ)
    (hBody : ∀ σ, I σ → Steps Δ Φ c σ (.lit (.bool true)) σ →
      ∃ v σ', IsValue v ∧ Steps Δ Φ b σ v σ' ∧ I σ' ∧ D σ' < D σ)
    {σ0 : Store} (hI0 : I σ0) :
    ∃ σ_end, Steps Δ Φ (.while_ c b) σ0 (.lit .unit) σ_end ∧
      I σ_end ∧ Steps Δ Φ c σ_end (.lit (.bool false)) σ_end := by
  suffices ∀ (rank : Nat) (σ : Store), D σ = rank → I σ →
      ∃ σ_end, Steps Δ Φ (.while_ c b) σ (.lit .unit) σ_end ∧
        I σ_end ∧ Steps Δ Φ c σ_end (.lit (.bool false)) σ_end by
    exact this (D σ0) σ0 rfl hI0
  intro rank
  induction rank using Nat.strongRecOn with
  | ind rank ih =>
    intro σ hrank hI
    rcases hCond σ hI with ⟨bval, hC⟩
    cases bval with
    | false =>
      refine ⟨σ, ?_, hI, hC⟩
      exact .trans .whileUnfold (steps_trans (steps_if_congr hC) (.trans .ifFalse (.refl _ _)))
    | true =>
      rcases hBody σ hI hC with ⟨v, σ1, hv, hB, hI1, hDec⟩
      rw [hrank] at hDec
      rcases ih (D σ1) hDec σ1 rfl hI1 with ⟨σ_end, hLoopRest, hIEnd, hCEnd⟩
      refine ⟨σ_end, ?_, hIEnd, hCEnd⟩
      exact .trans .whileUnfold
        (steps_trans (steps_if_congr hC)
          (.trans .ifTrue
            (steps_trans (steps_blockCons_congr hB)
              (.trans (.blockConsVal hv)
                (.trans .blockSingle hLoopRest)))))

/-! ## Part 7: Four Non-Vacuity Counterexample Theorems -/

/-- Empty ADT environment for standalone counterexample proofs. -/
def emptyAdtEnv : AdtEnv := fun _ => none

/-- Empty function environment for standalone counterexample proofs. -/
private def vcgEmptyFunEnv : FunEnv := fun _ => none

/-- **Counterexample 1 (`int32_overflow_counterexample`)**:
    In unbounded mathematical integers, `2147483647 + 1 > 0`, whereas under
    `CoreGeisha.Semantics` (`Int32` two's-complement wrapping), it evaluates to
    `-2147483648 < 0` — proving why an unbounded-`Int` VCG is unsound and exact
    `BitVec 32` modeling is mandatory. -/
theorem int32_overflow_counterexample :
    ∃ v : Int32,
      Steps emptyAdtEnv vcgEmptyFunEnv
        (.bin .add (.lit (.int (2147483647 : Int32))) (.lit (.int (1 : Int32))))
        [] (.lit (.int v)) [] ∧
      v < 0 := by
  refine ⟨(-2147483648 : Int32), ?_, by decide⟩
  exact .trans (.binVal (by rfl)) (.refl _ _)

/-- **Counterexample 2 (`truncating_rem_and_masked_shift_counterexample`)**:
    Demonstrates two exact LLVM/Geisha bit-level semantics enforced by S1:
    1. `(-7) % 3` evaluates to `-1` (truncating toward zero, NOT Euclidean `+2`);
    2. `1 << 32` evaluates to `1` (shift amount masked by `&&& 31`, NOT `0`). -/
theorem truncating_rem_and_masked_shift_counterexample :
    Steps emptyAdtEnv vcgEmptyFunEnv
      (.bin .rem (.lit (.int (-7 : Int32))) (.lit (.int (3 : Int32))))
      [] (.lit (.int (-1 : Int32))) [] ∧
    Steps emptyAdtEnv vcgEmptyFunEnv
      (.bin .shlInt (.lit (.int (1 : Int32))) (.lit (.int (32 : Int32))))
      [] (.lit (.int (1 : Int32))) [] := by
  constructor
  · exact .trans (.binVal (by rfl)) (.refl _ _)
  · exact .trans (.binVal (by rfl)) (.refl _ _)

/-- **Counterexample 3 (`missing_loop_havoc_counterexample`)**:
    A `while_` loop mutating cell `loc 0` from `0` to `1` terminates with
    `σ'[0]? = some (.lit (.int 1)) ≠ some (.lit (.int 0))`, proving that a naive
    VCG omitting loop cell havoc would unsoundly accept `cellGet (loc 0) == 0`
    after the loop. -/
theorem missing_loop_havoc_counterexample :
    let loop : Expr :=
      .while_
        (.bin .ltInt (.cellGet (.loc 0)) (.lit (.int 1)))
        (.cellSet (.loc 0) (.lit (.int 1)))
    Steps emptyAdtEnv vcgEmptyFunEnv loop [.lit (.int 0)] (.lit .unit) [.lit (.int 1)] ∧
    ([.lit (.int 1)] : Store)[0]? ≠ some (.lit (.int 0)) := by
  constructor
  · -- Iteration 1: cond `cellGet (loc 0) < 1` -> `0 < 1` -> `true`, body sets `loc 0 := 1`
    -- Iteration 2: cond `cellGet (loc 0) < 1` -> `1 < 1` -> `false`, exits with `()`
    refine .trans .whileUnfold ?_
    have hc1 : Steps emptyAdtEnv vcgEmptyFunEnv
        (.bin .ltInt (.cellGet (.loc 0)) (.lit (.int 1))) [.lit (.int 0)]
        (.lit (.bool true)) [.lit (.int 0)] :=
      .trans (.binLeft (.cellGetVal (by rfl))) (.trans (.binVal (by rfl)) (.refl _ _))
    refine steps_trans (steps_if_congr hc1) ?_
    refine .trans .ifTrue ?_
    refine .trans (.blockConsStep (.cellSetVal (by decide) (.lit _))) ?_
    refine .trans (.blockConsVal (.lit .unit)) ?_
    refine .trans .blockSingle ?_
    refine .trans .whileUnfold ?_
    have hc2 : Steps emptyAdtEnv vcgEmptyFunEnv
        (.bin .ltInt (.cellGet (.loc 0)) (.lit (.int 1))) [.lit (.int 1)]
        (.lit (.bool false)) [.lit (.int 1)] :=
      .trans (.binLeft (.cellGetVal (by rfl))) (.trans (.binVal (by rfl)) (.refl _ _))
    exact steps_trans (steps_if_congr hc2) (.trans .ifFalse (.refl _ _))
  · intro h; cases h

/-- **Counterexample 4 (`mutable_alias_call_counterexample`)**:
    For `overwriteSecond(a, b) = { cellSet a 10; cellSet b 99 }` with postcondition
    `cellGet a == 10`:
    1. Under distinct `Loc` arguments `(loc 0, loc 1)`, execution ends with `σ'[0]? = some 10`;
    2. Under aliased `Loc` arguments `(loc 0, loc 0)`, execution ends with `σ'[0]? = some 99 ≠ some 10`;
    3. Our fail-closed `vcgen` explicitly rejects the aliased call (`vcgen ... = none`). -/
theorem mutable_alias_call_counterexample :
    let fd : FunDef :=
      { name := "overwriteSecond"
        params := [("a", .cell .int), ("b", .cell .int)]
        retTy := .void
        body := .block [.cellSet (.var "a") (.lit (.int 10)),
                        .cellSet (.var "b") (.lit (.int 99))] }
    let fc : FnContract :=
      { params := fd.params
        req := .lit (.bool true)
        ens := .bin .eqInt (.cellGet (.var "a")) (.lit (.int 10)) }
    let Φ : FunEnv := fun name => if name == "overwriteSecond" then some fd else none
    let env : VcgEnv := { contracts := fun name => if name == "overwriteSecond" then some fc else none }
    Steps emptyAdtEnv Φ (.applyDir "overwriteSecond" [.loc 0, .loc 1])
      [.lit (.int 0), .lit (.int 0)] (.lit .unit) [.lit (.int 10), .lit (.int 99)] ∧
    Steps emptyAdtEnv Φ (.applyDir "overwriteSecond" [.loc 0, .loc 0])
      [.lit (.int 0)] (.lit .unit) [.lit (.int 99)] ∧
    vcgen env { nextLoc := 1, vars := [("c", .loc 0)], cells := [(0, .lit (.int 0))] }
      (.applyDir "overwriteSecond" [.var "c", .var "c"]) = none := by
  refine ⟨?_, ?_, ?_⟩
  · -- Distinct locations (0, 1) -> [10, 99]
    refine .trans (.applyDirBeta (by rfl) (fun a ha => by rcases List.mem_cons.mp ha with rfl | ha'; exact .loc 0; rcases List.mem_cons.mp ha' with rfl | h; exact .loc 1; cases h) (by rfl)) ?_
    simp only [zipParams, List.map, List.zip, substMany, subst, substList]
    refine .trans (.blockConsStep (.cellSetVal (by decide) (.lit _))) ?_
    refine .trans (.blockConsVal (.lit .unit)) ?_
    refine .trans .blockSingle ?_
    exact .trans (.cellSetVal (by decide) (.lit _)) (.refl _ _)
  · -- Aliased locations (0, 0) -> [99] (postcondition cellGet a == 10 violated!)
    refine .trans (.applyDirBeta (by rfl) (fun a ha => by rcases List.mem_cons.mp ha with rfl | ha'; exact .loc 0; rcases List.mem_cons.mp ha' with rfl | h; exact .loc 0; cases h) (by rfl)) ?_
    simp only [zipParams, List.map, List.zip, substMany, subst, substList]
    refine .trans (.blockConsStep (.cellSetVal (by decide) (.lit _))) ?_
    refine .trans (.blockConsVal (.lit .unit)) ?_
    refine .trans .blockSingle ?_
    exact .trans (.cellSetVal (by decide) (.lit _)) (.refl _ _)
  · unfold vcgen; simp [vcgenList, vcgen, assocLookup, collectLocArgs, noDupLocs, isModeledScalarTy]

/-! ## Part 8: Executable VCG Self-Check (`geisha-check --verify-vcg`) -/

/-- Executable self-check verifying positive VCG cases (safe division, masked shift,
    short-circuit `&&`, annotated `while_` loop, distinct mutable call) and negative
    fail-closed rejections (Float `NaN == NaN`, aliased mutable call, unannotated loop). -/
def runVcgSelfCheck : Except String String := do
  -- 1. Positive: safeDiv(a, b) with `requires b != 0` generates exact `neZero` obligation
  let safeDivFd : FunDef :=
    { name := "safeDiv", params := [("a", .int), ("b", .int)], retTy := .int,
      body := .bin .div (.var "a") (.var "b") }
  let safeDivFc : FnContract :=
    { params := safeDivFd.params,
      req := .bin .neInt (.var "b") (.lit (.int 0)),
      ens := .lit (.bool true) }
  match verifyFn {} safeDivFd safeDivFc with
  | none => throw "VCG self-check failed: safeDiv returned none"
  | some obs =>
    if obs.isEmpty then throw "VCG self-check failed: safeDiv produced 0 obligations"

  -- 2. Positive: masked shift `1 << 32 == 1`
  let shiftFd : FunDef :=
    { name := "shift32", params := [], retTy := .int,
      body := .bin .shlInt (.lit (.int 1)) (.lit (.int 32)) }
  let shiftFc : FnContract :=
    { params := [], req := .lit (.bool true),
      ens := .bin .eqInt (.var "__res") (.lit (.int 1)) }
  match verifyFn {} shiftFd shiftFc with
  | none => throw "VCG self-check failed: shift32 returned none"
  | some _ => pure ()

  -- 3. Positive: short-circuit `false && { cellSet c 42; true }`
  let scExpr : Expr :=
    .let_ "c" (.cellNew (.lit (.int 0)))
      (.block [
        .bin .and (.lit (.bool false)) (.block [.cellSet (.var "c") (.lit (.int 42)), .lit (.bool true)]),
        .applyDir "assert" [.bin .eqInt (.cellGet (.var "c")) (.lit (.int 0))]
      ])
  match vcgen {} {} scExpr with
  | none => throw "VCG self-check failed: short-circuit cell test returned none"
  | some _ => pure ()

  -- 4. Negative (fail-closed S3): Float `x == x` MUST return `none`
  let nanExpr : Expr := .bin .eqFloat (.lit (.floatBits 0x7ff8000000000000)) (.lit (.floatBits 0x7ff8000000000000))
  match vcgen {} {} nanExpr with
  | some _ => throw "VCG self-check failed: unmodeled Float equality was not rejected fail-closed"
  | none => pure ()

  -- 5. Negative (fail-closed): unannotated `while_` loop MUST return `none`
  let unannLoop : Expr := .while_ (.lit (.bool false)) (.lit .unit)
  match vcgen {} {} unannLoop with
  | some _ => throw "VCG self-check failed: unannotated while loop was not rejected fail-closed"
  | none => pure ()

  -- 6. Negative (fail-closed): aliased mutable `Cell` call `overwriteSecond(a, a)` MUST return `none`
  let owFc : FnContract :=
    { params := [("a", .cell .int), ("b", .cell .int)],
      req := .lit (.bool true),
      ens := .bin .eqInt (.cellGet (.var "a")) (.lit (.int 10)),
      retTy := .void }
  let owEnv : VcgEnv := { contracts := fun n => if n == "overwriteSecond" then some owFc else none }
  match vcgen owEnv { nextLoc := 1, vars := [("a", .loc 0)], cells := [(0, .lit (.int 0))] }
      (.applyDir "overwriteSecond" [.var "a", .var "a"]) with
  | some _ => throw "VCG self-check failed: aliased mutable Cell call was not rejected fail-closed"
  | none => pure ()

  -- 7. Positive: distinct mutable `Cell` call `overwriteSecond(a, b)` succeeds
  match vcgen owEnv { nextLoc := 2, vars := [("a", .loc 0), ("b", .loc 1)], cells := [(0, .lit (.int 0)), (1, .lit (.int 0))] }
      (.applyDir "overwriteSecond" [.var "a", .var "b"]) with
  | none => throw "VCG self-check failed: distinct mutable Cell call unexpectedly failed"
  | some _ => pure ()

  return "VERIFIED VCG SELF-CHECK OK (7/7 checks: safeDiv, maskedShift32, shortCircuitAnd, fail-closed Float/unannotatedWhile/aliasedCellCall, distinctCellCall; backed by machine-checked vcgen_sound, verifyFn_sound, while_decreases_terminates)"

/-! ## Part 9: Live Compiler `.gscore` Cross-Verification (`geisha-check --verify-vcg <file.gscore>`) -/

/-- Conjoin a list of boolean Core Geisha expressions. -/
def conjoinExprs : List Expr → Expr
  | [] => .lit (.bool true)
  | [e] => e
  | e :: rest => .bin .and e (conjoinExprs rest)

/-- Extract `__gs_ensures` clauses from the trailing ensures block emitted by `src/core.gsa`. -/
def extractEnsuresStmts : List Expr → List Expr
  | [] => []
  | .applyDir "__gs_ensures" [e] :: rest => e :: extractEnsuresStmts rest
  | .let_ r (.var "__gs_res") (.applyDir "__gs_ensures" [e]) :: rest =>
    subst r (.var "__gs_res") e :: extractEnsuresStmts rest
  | _ :: rest => extractEnsuresStmts rest

/-- Strip leading `__gs_requires` / `__gs_decreases` markers from a function body block,
    preserving both preconditions and the optional termination measure (`decreases`). -/
def splitContractHeader : List Expr → List Expr × Option Expr × List Expr
  | .applyDir "__gs_requires" [e] :: rest =>
    let (reqs, decOpt, tail) := splitContractHeader rest
    (e :: reqs, decOpt, tail)
  | .applyDir "__gs_decreases" [d] :: rest =>
    let (reqs, _, tail) := splitContractHeader rest
    (reqs, some d, tail)
  | stmts => ([], none, stmts)

/-- Extract structured `(FnContract, strippedBody, hasContract)` from a compiler-emitted `FunDef`
    (mirroring `extractFnSpec` in `src/verify.gsa`, including `retTy` and optional `decreases`). -/
def extractGscoreFnContract (fd : FunDef) : FnContract × Expr × Bool :=
  match fd.body with
  | .block stmts =>
    let (reqs, decOpt, rest) := splitContractHeader stmts
    let (ensList, coreBody) :=
      match rest with
      | [Expr.let_ "__gs_res" valT (.block ensStmts)] =>
        let es := extractEnsuresStmts ensStmts
        if es.isEmpty then ([], Expr.let_ "__gs_res" valT (.block ensStmts))
        else (es, valT)
      | [single] => ([], single)
      | _ => ([], .block rest)
    let hasContract := !reqs.isEmpty || !ensList.isEmpty || decOpt.isSome
    ({ params := fd.params, req := conjoinExprs reqs, ens := conjoinExprs ensList,
       retVar := "__gs_res", retTy := fd.retTy, dec := decOpt },
     coreBody, hasContract)
  | other =>
    ({ params := fd.params, req := .lit (.bool true), ens := .lit (.bool true),
       retVar := "__gs_res", retTy := fd.retTy, dec := none },
     other, false)

/-- Strip `__gs_invariant` / `__gs_decreases` marker calls from a loop body while
    collecting loop invariant expressions and optional `decreases` measure for `VcgEnv.loops`. -/
def stripLoopMarkers : Expr → List Expr × Option Expr × Expr
  | .block stmts =>
    let rec go : List Expr → List Expr × Option Expr × List Expr
      | [] => ([], none, [])
      | .applyDir "__gs_invariant" [inv] :: rest =>
        let (invs, decOpt, body) := go rest
        (inv :: invs, decOpt, body)
      | .applyDir "__gs_decreases" [d] :: rest =>
        let (invs, _, body) := go rest
        (invs, some d, body)
      | s :: rest =>
        let (invs, decOpt, body) := go rest
        (invs, decOpt, s :: body)
    let (invs, decOpt, clean) := go stmts
    (invs, decOpt, .block clean)
  | other => ([], none, other)

/- Recursively normalize `while_` loops carrying `__gs_invariant`/`__gs_decreases` markers into a
   `(cleanedExpr, loopTable)` pair consumable by `vcgen`. -/
mutual
partial def collectLoopsExpr : Expr → Expr × List (Expr × Expr × LoopContract)
  | .while_ c b =>
    let (invs, decOpt, bClean0) := stripLoopMarkers b
    let (c', lc1) := collectLoopsExpr c
    let (b', lc2) := collectLoopsExpr bClean0
    let entry := if invs.isEmpty then [] else [(c', b', { inv := conjoinExprs invs, dec := decOpt })]
    (.while_ c' b', entry ++ lc1 ++ lc2)
  | .block es =>
    let (es', lcs) := collectLoopsBlock es
    (.block es', lcs)
  | .let_ x e1 e2 =>
    let (e1', l1) := collectLoopsExpr e1
    let (e2', l2) := collectLoopsExpr e2
    (.let_ x e1' e2', l1 ++ l2)
  | .if_ c t e =>
    let (c', l1) := collectLoopsExpr c
    let (t', l2) := collectLoopsExpr t
    let (e', l3) := collectLoopsExpr e
    (.if_ c' t' e', l1 ++ l2 ++ l3)
  | .bin op e1 e2 =>
    let (e1', l1) := collectLoopsExpr e1
    let (e2', l2) := collectLoopsExpr e2
    (.bin op e1' e2', l1 ++ l2)
  | .un op e1 =>
    let (e1', l1) := collectLoopsExpr e1
    (.un op e1', l1)
  | .cellNew e1 =>
    let (e1', l1) := collectLoopsExpr e1
    (.cellNew e1', l1)
  | .cellGet e1 =>
    let (e1', l1) := collectLoopsExpr e1
    (.cellGet e1', l1)
  | .cellSet e1 e2 =>
    let (e1', l1) := collectLoopsExpr e1
    let (e2', l2) := collectLoopsExpr e2
    (.cellSet e1' e2', l1 ++ l2)
  | .applyDir name args =>
    let (args', l1) := collectLoopsList args
    (.applyDir name args', l1)
  | other => (other, [])

partial def collectLoopsBlock : List Expr → List Expr × List (Expr × Expr × LoopContract)
  | [] => ([], [])
  | .applyDir "__gs_invariant" [inv] :: .while_ c b :: rest =>
    let (invsB, decB, bClean0) := stripLoopMarkers b
    let (c', lc1) := collectLoopsExpr c
    let (b', lc2) := collectLoopsExpr bClean0
    let (rest', lcR) := collectLoopsBlock rest
    (.while_ c' b' :: rest', (c', b', { inv := conjoinExprs (inv :: invsB), dec := decB }) :: (lc1 ++ lc2 ++ lcR))
  | .applyDir "__gs_decreases" _ :: rest => collectLoopsBlock rest
  | e :: rest =>
    let (e', lc1) := collectLoopsExpr e
    let (rest', lcR) := collectLoopsBlock rest
    (e' :: rest', lc1 ++ lcR)

partial def collectLoopsList : List Expr → List Expr × List (Expr × Expr × LoopContract)
  | [] => ([], [])
  | e :: es =>
    let (e', l1) := collectLoopsExpr e
    let (es', l2) := collectLoopsList es
    (e' :: es', l1 ++ l2)
end

/-- Check whether a symbolic value contains any symbolic variable `.sym id`. -/
def svalHasSym : SVal → Bool
  | .lit _ | .loc _ => false
  | .sym _ => true
  | .un _ e => svalHasSym e
  | .bin _ e1 e2 => svalHasSym e1 || svalHasSym e2
  | .ite c t e => svalHasSym c || svalHasSym t || svalHasSym e
  | .getTag v => svalHasSym v

/-- Check whether a symbolic formula contains any symbolic variable `.sym id`. -/
def sformHasSym : SForm → Bool
  | .tt | .ff => false
  | .isTrue v | .isFalse v | .neZero _ v | .hasTy v _ => svalHasSym v
  | .not p => sformHasSym p
  | .and p q | .imp p q => sformHasSym p || sformHasSym q

/-- Computable closed-formula evaluator (when `sformHasSym f = false`), backed by
    `evalSFormClosed_sound` below so closed VCs (like `1 / 0`) are decided directly
    inside the Lean kernel without needing any external SMT solver! -/
def evalSValClosed : SVal → Option Expr
  | .lit l => some (.lit l)
  | .sym _ => none
  | .loc l => some (.loc l)
  | .un op e =>
    match evalSValClosed e with
    | some (.lit l) => (evalUnOp op l).map Expr.lit
    | _ => none
  | .bin op e1 e2 =>
    match evalSValClosed e1, evalSValClosed e2 with
    | some (.lit l1), some (.lit l2) =>
      match evalBinOp op l1 l2 with
      | some (.val l') => some (.lit l')
      | _ => none
    | _, _ => none
  | .ite c t e =>
    match evalSValClosed c with
    | some (.lit (.bool true)) => evalSValClosed t
    | some (.lit (.bool false)) => evalSValClosed e
    | _ => none
  | .getTag v =>
    match evalSValClosed v with
    | some (.makeData _ tag _) => some (.lit (.int (Int32.ofNat tag)))
    | _ => none

def evalSFormClosed : SForm → Option Bool
  | .tt => some true
  | .ff => some false
  | .isTrue v =>
    if svalHasSym v then none
    else
      match evalSValClosed v with
      | some (.lit (.bool true)) => some true
      | _ => some false
  | .isFalse v =>
    if svalHasSym v then none
    else
      match evalSValClosed v with
      | some (.lit (.bool false)) => some true
      | _ => some false
  | .neZero op v =>
    if svalHasSym v then none
    else
      match op with
      | .div | .rem =>
        match evalSValClosed v with
        | some (.lit (.int n)) => some (n != 0)
        | _ => some false
      | .div64 | .rem64 =>
        match evalSValClosed v with
        | some (.lit (.int64 n)) => some (n != 0)
        | _ => some false
      | _ => some true
  | .hasTy v ty =>
    if svalHasSym v then none
    else
      match ty, evalSValClosed v with
      | .int, some (.lit (.int _)) => some true
      | .int64, some (.lit (.int64 _)) => some true
      | .bool, some (.lit (.bool _)) => some true
      | .char, some (.lit (.char c)) => some (decide (c.toNat < 256))
      | .void, some (.lit .unit) => some true
      | _, _ => some false
  | .not p => (evalSFormClosed p).map (! ·)
  | .and p q =>
    match evalSFormClosed p, evalSFormClosed q with
    | some a, some b => some (a && b)
    | _, _ => none
  | .imp p q =>
    match evalSFormClosed p, evalSFormClosed q with
    | some a, some b => some (!a || b)
    | _, _ => none

theorem evalSValClosed_eq (M : Model) {sv : SVal} (h : svalHasSym sv = false) :
    evalSValClosed sv = evalSVal M id sv := by
  induction sv with
  | lit _ | loc _ => rfl
  | sym _ => simp [svalHasSym] at h
  | un op e ih =>
    simp only [svalHasSym] at h
    simp only [evalSValClosed, evalSVal, ih h]
    cases evalSVal M id e with
    | none => rfl
    | some v =>
      cases v <;> try rfl
      rename_i l; cases h2 : evalUnOp op l <;> simp [h2]
  | bin op e1 e2 ih1 ih2 =>
    simp only [svalHasSym, Bool.or_eq_false_iff] at h
    simp only [evalSValClosed, evalSVal, ih1 h.1, ih2 h.2]
  | ite c t e ihc iht ihe =>
    simp only [svalHasSym, Bool.or_eq_false_iff] at h
    simp only [evalSValClosed, evalSVal, ihc h.1.1, iht h.1.2, ihe h.2]
  | getTag v ih =>
    simp only [svalHasSym] at h
    simp only [evalSValClosed, evalSVal, ih h]

theorem evalSFormClosed_iff (M : Model) {f : SForm} {b : Bool}
    (heval : evalSFormClosed f = some b) :
    (b = true) ↔ evalSForm M f := by
  induction f generalizing b with
  | tt => simp [evalSFormClosed, evalSForm] at heval ⊢; subst heval; rfl
  | ff => simp [evalSFormClosed, evalSForm] at heval ⊢; subst heval; simp
  | isTrue v =>
    simp only [evalSFormClosed] at heval
    cases h : svalHasSym v
    · simp only [h, Bool.false_eq_true, ↓reduceIte] at heval
      rw [evalSValClosed_eq M h] at heval
      cases h1 : evalSVal M id v with
      | none => simp [h1] at heval; subst heval; simp [evalSForm, h1]
      | some e =>
        cases e with
        | lit l =>
          cases l with
          | bool bv => cases bv <;> simp [h1] at heval <;> subst heval <;> simp [evalSForm, h1]
          | _ => simp [h1] at heval; subst heval; simp [evalSForm, h1]
        | _ => simp [h1] at heval; subst heval; simp [evalSForm, h1]
    · simp [h] at heval
  | isFalse v =>
    simp only [evalSFormClosed] at heval
    cases h : svalHasSym v
    · simp only [h, Bool.false_eq_true, ↓reduceIte] at heval
      rw [evalSValClosed_eq M h] at heval
      cases h1 : evalSVal M id v with
      | none => simp [h1] at heval; subst heval; simp [evalSForm, h1]
      | some e =>
        cases e with
        | lit l =>
          cases l with
          | bool bv => cases bv <;> simp [h1] at heval <;> subst heval <;> simp [evalSForm, h1]
          | _ => simp [h1] at heval; subst heval; simp [evalSForm, h1]
        | _ => simp [h1] at heval; subst heval; simp [evalSForm, h1]
    · simp [h] at heval
  | neZero op v =>
    simp only [evalSFormClosed] at heval
    cases h : svalHasSym v
    · simp only [h, Bool.false_eq_true, ↓reduceIte] at heval
      rw [evalSValClosed_eq M h] at heval
      cases op with
      | div | rem =>
        cases h1 : evalSVal M id v with
        | none => simp [h1] at heval; subst heval; simp [evalSForm, h1]
        | some e =>
          cases e with
          | lit l =>
            cases l with
            | int n => simp [h1] at heval; subst heval; simp [evalSForm, h1]
            | _ => simp [h1] at heval; subst heval; simp [evalSForm, h1]
          | _ => simp [h1] at heval; subst heval; simp [evalSForm, h1]
      | div64 | rem64 =>
        cases h1 : evalSVal M id v with
        | none => simp [h1] at heval; subst heval; simp [evalSForm, h1]
        | some e =>
          cases e with
          | lit l =>
            cases l with
            | int64 n => simp [h1] at heval; subst heval; simp [evalSForm, h1]
            | _ => simp [h1] at heval; subst heval; simp [evalSForm, h1]
          | _ => simp [h1] at heval; subst heval; simp [evalSForm, h1]
      | _ => simp at heval; subst heval; simp [evalSForm]
    · simp [h] at heval
  | hasTy v ty =>
    simp only [evalSFormClosed] at heval
    cases h : svalHasSym v
    · simp only [h, Bool.false_eq_true, ↓reduceIte] at heval
      rw [evalSValClosed_eq M h] at heval
      cases h1 : evalSVal M id v with
      | none =>
        rw [h1] at heval; cases ty <;> simp at heval <;> subst heval <;> simp [evalSForm, h1]
      | some e =>
        rw [h1] at heval
        cases ty with
        | int =>
          cases e with
          | lit l => cases l <;> simp at heval <;> subst heval <;> simp [evalSForm, valHasTy, h1]
          | _ => simp at heval; subst heval; simp [evalSForm, valHasTy, h1]
        | int64 =>
          cases e with
          | lit l => cases l <;> simp at heval <;> subst heval <;> simp [evalSForm, valHasTy, h1]
          | _ => simp at heval; subst heval; simp [evalSForm, valHasTy, h1]
        | bool =>
          cases e with
          | lit l => cases l <;> simp at heval <;> subst heval <;> simp [evalSForm, valHasTy, h1]
          | _ => simp at heval; subst heval; simp [evalSForm, valHasTy, h1]
        | char =>
          cases e with
          | lit l => cases l <;> simp at heval <;> subst heval <;> simp [evalSForm, valHasTy, h1]
          | _ => simp at heval; subst heval; simp [evalSForm, valHasTy, h1]
        | void =>
          cases e with
          | lit l => cases l <;> simp at heval <;> subst heval <;> simp [evalSForm, valHasTy, h1]
          | _ => simp at heval; subst heval; simp [evalSForm, valHasTy, h1]
        | _ => simp at heval; subst heval; simp [evalSForm, valHasTy, h1]
    · simp [h] at heval
  | not p ih =>
    simp only [evalSFormClosed] at heval
    cases hp : evalSFormClosed p with
    | none => simp [hp] at heval
    | some bp =>
      simp [hp] at heval
      have h1 := ih hp
      cases bp <;> simp at heval <;> subst heval <;> simp [evalSForm] at h1 ⊢ <;> exact h1
  | and p q ihp ihq =>
    simp only [evalSFormClosed] at heval
    cases hp : evalSFormClosed p with
    | none => simp [hp] at heval
    | some bp =>
      cases hq : evalSFormClosed q with
      | none => simp [hp, hq] at heval
      | some bq =>
        simp [hp, hq] at heval; subst heval
        have h1 := ihp hp; have h2 := ihq hq
        cases bp <;> cases bq <;> simp [evalSForm] at h1 h2 ⊢
        · intro hP _; exact h1 hP
        · intro hP _; exact h1 hP
        · intro _ hQ; exact h2 hQ
        · exact ⟨h1, h2⟩
  | imp p q ihp ihq =>
    simp only [evalSFormClosed] at heval
    cases hp : evalSFormClosed p with
    | none => simp [hp] at heval
    | some bp =>
      cases hq : evalSFormClosed q with
      | none => simp [hp, hq] at heval
      | some bq =>
        simp [hp, hq] at heval; subst heval
        have h1 := ihp hp; have h2 := ihq hq
        cases bp <;> cases bq <;> simp [evalSForm] at h1 h2 ⊢
        · intro hP; exact absurd hP h1
        · intro _; exact h2
        · exact ⟨h1, h2⟩
        · intro _; exact h2

theorem evalSFormClosed_sound {f : SForm} (h : evalSFormClosed f = some true) :
    ValidForm f := fun M _ => (evalSFormClosed_iff M h).mp rfl

theorem evalSFormClosed_false_not_valid {f : SForm} (h : evalSFormClosed f = some false) :
    ¬ ValidForm f := by
  intro hval
  have hM0 : ValidModel (fun _ => .lit .unit) := fun _ => ⟨.lit .unit, rfl⟩
  have hfalse := (evalSFormClosed_iff (fun _ => .lit .unit) h).mpr (hval _ hM0)
  cases hfalse

/-- Format an unsigned integer as a fixed-width SMT-LIB2 hex bitvector `#x...`. -/
private def hexDigitChar (d : Nat) : Char :=
  if d < 10 then Char.ofNat (48 + d) else Char.ofNat (87 + d)

private def natToHexWidth (n : Nat) (digits : Nat) : String :=
  let rec go (k : Nat) (v : Nat) (acc : List Char) : List Char :=
    match k with
    | 0 => acc
    | k' + 1 => go k' (v / 16) (hexDigitChar (v % 16) :: acc)
  "#x" ++ String.ofList (go digits n [])

/-- Export an `SVal` to SMT-LIB2 BitVec/Bool syntax (fail-closed `none` on unmodeled nodes). -/
def svalToSmt2 : SVal → Option String
  | .lit (.int n) => some (natToHexWidth n.toBitVec.toNat 8)
  | .lit (.int64 n) => some (natToHexWidth n.toBitVec.toNat 16)
  | .lit (.bool b) => some (if b then "true" else "false")
  | .lit (.char c) => some (natToHexWidth (c.toNat % 256) 8)
  | .lit .unit => some "#x00000000"
  | .lit _ => none
  | .sym id => some s!"sym_{id}"
  | .loc _ => none
  | .un op e => do
    let s ← svalToSmt2 e
    match op with
    | .not => some s!"(not {s})"
    | .neg => some s!"(bvneg {s})"
    | .bitNot => some s!"(bvnot {s})"
    | .neg64 => some s!"(bvneg {s})"
    | .bitNot64 => some s!"(bvnot {s})"
    | .intToI64 => some s!"((_ sign_extend 32) {s})"
    | .i64ToInt => some s!"((_ extract 31 0) {s})"
    | _ => none
  | .bin op e1 e2 => do
    let s1 ← svalToSmt2 e1
    let s2 ← svalToSmt2 e2
    match op with
    | .add | .add64 => some s!"(bvadd {s1} {s2})"
    | .sub | .sub64 => some s!"(bvsub {s1} {s2})"
    | .mul | .mul64 => some s!"(bvmul {s1} {s2})"
    | .div | .div64 => some s!"(bvsdiv {s1} {s2})"
    | .rem | .rem64 => some s!"(bvsrem {s1} {s2})"
    | .bitAnd | .bitAnd64 => some s!"(bvand {s1} {s2})"
    | .bitOr | .bitOr64 => some s!"(bvor {s1} {s2})"
    | .bitXor | .bitXor64 => some s!"(bvxor {s1} {s2})"
    | .shlInt => some s!"(bvshl {s1} (bvand {s2} #x0000001f))"
    | .shrInt => some s!"(bvashr {s1} (bvand {s2} #x0000001f))"
    | .ushrInt => some s!"(bvlshr {s1} (bvand {s2} #x0000001f))"
    | .shl64 => some s!"(bvshl {s1} ((_ zero_extend 32) (bvand {s2} #x0000003f)))"
    | .shr64 => some s!"(bvashr {s1} ((_ zero_extend 32) (bvand {s2} #x0000003f)))"
    | .ushr64 => some s!"(bvlshr {s1} ((_ zero_extend 32) (bvand {s2} #x0000003f)))"
    | .eqInt | .eq64 | .eqBool | .eqChar => some s!"(= {s1} {s2})"
    | .neInt | .ne64 | .neBool | .neChar => some s!"(not (= {s1} {s2}))"
    | .ltInt | .lt64 => some s!"(bvslt {s1} {s2})"
    | .leInt | .le64 => some s!"(bvsle {s1} {s2})"
    | .gtInt | .gt64 => some s!"(bvsgt {s1} {s2})"
    | .geInt | .ge64 => some s!"(bvsge {s1} {s2})"
    | .ltChar => some s!"(bvult {s1} {s2})"
    | .leChar => some s!"(bvule {s1} {s2})"
    | .gtChar => some s!"(bvugt {s1} {s2})"
    | .geChar => some s!"(bvuge {s1} {s2})"
    | .and | .bitAndBool => some s!"(and {s1} {s2})"
    | .or | .bitOrBool => some s!"(or {s1} {s2})"
    | .bitXorBool => some s!"(xor {s1} {s2})"
    | _ => none
  | .ite c t e => do
    let sc ← svalToSmt2 c
    let st ← svalToSmt2 t
    let se ← svalToSmt2 e
    some s!"(ite {sc} {st} {se})"
  | .getTag _ => none

/-- Export an `SForm` to SMT-LIB2 syntax. -/
def sformToSmt2 : SForm → Option String
  | .tt => some "true"
  | .ff => some "false"
  | .isTrue v => svalToSmt2 v
  | .isFalse v => do let s ← svalToSmt2 v; some s!"(not {s})"
  | .neZero op v => do
    let s ← svalToSmt2 v
    match op with
    | .div | .rem => some s!"(not (= {s} #x00000000))"
    | .div64 | .rem64 => some s!"(not (= {s} #x0000000000000000))"
    | _ => some "true"
  | .hasTy v ty =>
    match ty with
    | .char => do let s ← svalToSmt2 v; some s!"(bvult {s} #x00000100)"
    | .int | .int64 | .bool | .void => some "true"
    | _ => some "false"
  | .not p => do let sp ← sformToSmt2 p; some s!"(not {sp})"
  | .and p q => do let sp ← sformToSmt2 p; let sq ← sformToSmt2 q; some s!"(and {sp} {sq})"
  | .imp p q => do let sp ← sformToSmt2 p; let sq ← sformToSmt2 q; some s!"(=> {sp} {sq})"

private def collectSValSyms : SVal → List SymId
  | .lit _ | .loc _ => []
  | .sym id => [id]
  | .un _ e => collectSValSyms e
  | .bin _ e1 e2 => collectSValSyms e1 ++ collectSValSyms e2
  | .ite c t e => collectSValSyms c ++ collectSValSyms t ++ collectSValSyms e
  | .getTag v => collectSValSyms v

private def collectSFormSyms : SForm → List SymId
  | .tt | .ff => []
  | .isTrue v | .isFalse v | .neZero _ v | .hasTy v _ => collectSValSyms v
  | .not p => collectSFormSyms p
  | .and p q | .imp p q => collectSFormSyms p ++ collectSFormSyms q

private def tyToSmtSort : Ty → String
  | .int64 => "(_ BitVec 64)"
  | .bool => "Bool"
  | _ => "(_ BitVec 32)"

/-- Emit a self-contained SMT-LIB2 validity query (`(assert (not ob))` + `(check-sat)`)
    for an obligation `ob : SForm` produced by `CoreGeisha.VCG`.
    Fail-closed (`none`) whenever any symbol lacks an explicit modeled scalar `.hasTy` constraint
    in `ob` (never silently defaults missing sorts to `.int`). -/
def emitObSmt2 (ob : SForm) : Option String := do
  let body ← sformToSmt2 ob
  let rawSyms := collectSFormSyms ob
  let uniqueSyms := rawSyms.foldl (fun acc id => if acc.contains id then acc else acc ++ [id]) []
  let tyMap := collectSymTys ob
  let decls ← uniqueSyms.mapM fun id =>
    match tyMap.find? (·.1 == id) with
    | some (_, ty) =>
      if isModeledScalarTy ty then
        some s!"(declare-const sym_{id} {tyToSmtSort ty})"
      else none
    | none => none
  let header := "(set-logic QF_BV)\n" ++ String.intercalate "\n" decls
  some s!"{header}\n(assert (not {body}))\n(check-sat)\n"

/- Normalize `(apply-dir "intToI64" [e])` and `(apply-dir "i64ToInt" [e])` intrinsic calls
   from dumped `.gscore` into first-class `UnOp.intToI64` / `UnOp.i64ToInt` nodes. -/
mutual
private def normalizeCastsExpr : Expr → Expr
  | .un op e => .un op (normalizeCastsExpr e)
  | .bin op e1 e2 => .bin op (normalizeCastsExpr e1) (normalizeCastsExpr e2)
  | .let_ x e1 e2 => .let_ x (normalizeCastsExpr e1) (normalizeCastsExpr e2)
  | .block es => .block (normalizeCastsList es)
  | .tuple es => .tuple (normalizeCastsList es)
  | .if_ c t e => .if_ (normalizeCastsExpr c) (normalizeCastsExpr t) (normalizeCastsExpr e)
  | .while_ c b => .while_ (normalizeCastsExpr c) (normalizeCastsExpr b)
  | .cellNew e => .cellNew (normalizeCastsExpr e)
  | .cellGet e => .cellGet (normalizeCastsExpr e)
  | .cellSet e1 e2 => .cellSet (normalizeCastsExpr e1) (normalizeCastsExpr e2)
  | .getTag e => .getTag (normalizeCastsExpr e)
  | .makeData tn tag es => .makeData tn tag (normalizeCastsList es)
  | .apply f es => .apply (normalizeCastsExpr f) (normalizeCastsList es)
  | .applyDir name args =>
    let args' := normalizeCastsList args
    match name, args' with
    | "intToI64", [e1] => .un .intToI64 e1
    | "i64ToInt", [e1] => .un .i64ToInt e1
    | _, _ => .applyDir name args'
  | .lam m ps rt b => .lam m ps rt (normalizeCastsExpr b)
  | .match_ s arms => .match_ (normalizeCastsExpr s) (normalizeCastsArms arms)
  | .spawn e => .spawn (normalizeCastsExpr e)
  | .await e => .await (normalizeCastsExpr e)
  | .concPrim p es => .concPrim p (normalizeCastsList es)
  | e => e

private def normalizeCastsList : List Expr → List Expr
  | [] => []
  | e :: es => normalizeCastsExpr e :: normalizeCastsList es

private def normalizeCastsArms : List (Pat × Expr) → List (Pat × Expr)
  | [] => []
  | (p, e) :: rest => (p, normalizeCastsExpr e) :: normalizeCastsArms rest
end

/- Collect direct callee names referenced via `.applyDir` in an expression (excluding intrinsics). -/
mutual
private def collectCallsExpr : Expr → List Ident
  | .un _ e | .cellNew e | .cellGet e | .getTag e | .spawn e | .await e => collectCallsExpr e
  | .bin _ e1 e2 | .let_ _ e1 e2 | .cellSet e1 e2 | .while_ e1 e2 =>
    collectCallsExpr e1 ++ collectCallsExpr e2
  | .if_ c t e => collectCallsExpr c ++ collectCallsExpr t ++ collectCallsExpr e
  | .block es | .tuple es | .makeData _ _ es | .concPrim _ es => collectCallsList es
  | .apply f es => collectCallsExpr f ++ collectCallsList es
  | .applyDir name args =>
    let rest := collectCallsList args
    if name == "assert" || name == "assume" then rest else name :: rest
  | .lam _ _ _ b => collectCallsExpr b
  | .match_ s arms => collectCallsExpr s ++ collectCallsArms arms
  | _ => []

private def collectCallsList : List Expr → List Ident
  | [] => []
  | e :: es => collectCallsExpr e ++ collectCallsList es

private def collectCallsArms : List (Pat × Expr) → List Ident
  | [] => []
  | (_, e) :: rest => collectCallsExpr e ++ collectCallsArms rest
end

/-- Bounded reachability in the direct call graph (fuel = number of functions). -/
private def canReachFn (graph : List (Ident × List Ident)) (src dst : Ident) : Nat → Bool
  | 0 => false
  | fuel + 1 =>
    let nbrs := (graph.find? (·.1 == src)).map Prod.snd |>.getD []
    if nbrs.contains dst then true
    else nbrs.any (fun next => canReachFn graph next dst fuel)

private def mapGscoreCallIdent (nm : Ident) : Ident :=
  if nm == "__gs_builtin_assert" then "assert"
  else if nm == "__gs_builtin_assume" then "assume"
  else if nm == "__gs_builtin_intToI64" then "intToI64"
  else if nm == "__gs_builtin_i64ToInt" then "i64ToInt"
  else if nm == "assert" || nm == "assume" || nm == "intToI64" || nm == "i64ToInt" then "$bare$" ++ nm
  else nm

mutual
  private def renameShadowedExpr (f : Ident → Ident) : Expr → Expr
    | .lit l => .lit l
    | .var x => .var x
    | .loc l => .loc l
    | .taskRef t => .taskRef t
    | .syncRef k id => .syncRef k id
    | .tuple es => .tuple (renameShadowedExprList f es)
    | .block es => .block (renameShadowedExprList f es)
    | .lam m ps rt b => .lam m ps rt (renameShadowedExpr f b)
    | .apply fn es => .apply (renameShadowedExpr f fn) (renameShadowedExprList f es)
    | .applyDir nm es =>
        .applyDir (f nm) (renameShadowedExprList f es)
    | .bin op a b => .bin op (renameShadowedExpr f a) (renameShadowedExpr f b)
    | .un op a => .un op (renameShadowedExpr f a)
    | .let_ x v b => .let_ x (renameShadowedExpr f v) (renameShadowedExpr f b)
    | .if_ c t e =>
        .if_ (renameShadowedExpr f c) (renameShadowedExpr f t) (renameShadowedExpr f e)
    | .while_ c b => .while_ (renameShadowedExpr f c) (renameShadowedExpr f b)
    | .match_ s arms => .match_ (renameShadowedExpr f s) (renameShadowedArms f arms)
    | .makeData adt tag fs => .makeData adt tag (renameShadowedExprList f fs)
    | .getTag e => .getTag (renameShadowedExpr f e)
    | .cellNew e => .cellNew (renameShadowedExpr f e)
    | .cellGet e => .cellGet (renameShadowedExpr f e)
    | .cellSet c v => .cellSet (renameShadowedExpr f c) (renameShadowedExpr f v)
    | .spawn e => .spawn (renameShadowedExpr f e)
    | .await e => .await (renameShadowedExpr f e)
    | .concPrim p es => .concPrim p (renameShadowedExprList f es)
    | .trap t => .trap t

  private def renameShadowedExprList (f : Ident → Ident) : List Expr → List Expr
    | [] => []
    | e :: es => renameShadowedExpr f e :: renameShadowedExprList f es

  private def renameShadowedArms (f : Ident → Ident) : List (Pat × Expr) → List (Pat × Expr)
    | [] => []
    | (p, b) :: rest => (p, renameShadowedExpr f b) :: renameShadowedArms f rest
end

/-- Cross-verify a live `.gscore` program emitted by `geisha verify --dump-core`
    through our machine-checked `VCG.verifyFn`, returning the exact list of
    `(fnName, obligation)` pairs for kernel/SMT discharge in `Main.lean`!
    Rejects fail-closed whenever any user function contains unmodeled constructs
    (e.g. Float equality, aliased mutable `Cell` calls, unannotated loops, or
    mutually recursive calls missing `decreases`). -/
def verifyGscoreProgram (funs : List FunDef) (_externs : List ExternDecl := []) (vcgFormat : Nat := 1) : Except String (Nat × List (Ident × SForm)) := do
  -- 0. Reject legacy unversioned `.gscore` inputs lacking `(vcg-format 2)` fail-closed so no
  --    pre-Z8 extern declaration (including user `extern "__gs_builtin_assume"`) can ever be
  --    mistaken for a trusted built-in VCG primitive; then fail-closed on any FunDef claiming
  --    reserved `__gs_builtin_*` names and map only explicit `__gs_builtin_*` tags to true VCG
  --    built-ins while deflecting all bare legacy names to `$bare$<nm>`.
  if vcgFormat < 2 then
    throw "VCG FAIL-CLOSED: legacy unversioned .gscore input (missing '(vcg-format 2)'); please regenerate from source with 'geisha verify --dump-core'"
  if funs.any (fun fd => fd.name.startsWith "__gs_builtin_") then
    throw "VCG FAIL-CLOSED: user function name cannot start with reserved '__gs_builtin_' prefix"
  let funsAlpha : List FunDef := funs.map fun fd =>
    { fd with
      name := mapGscoreCallIdent fd.name
      body := renameShadowedExpr mapGscoreCallIdent fd.body }
  -- 1. Normalize cast intrinsics and extract contracts & loop annotations for all user functions
  let extracted := funsAlpha.map fun fd =>
    let fdNorm : FunDef := { fd with body := normalizeCastsExpr fd.body }
    let (fc, body0, hasC) := extractGscoreFnContract fdNorm
    let (bodyClean, loops) := collectLoopsExpr body0
    (fdNorm, fc, bodyClean, loops, hasC)
  let contractMap : List (Ident × FnContract) :=
    extracted.map fun (fd, fc, _, _, _) => (fd.name, fc)
  let allLoops : List (Expr × Expr × LoopContract) :=
    extracted.foldl (fun acc (_, _, _, ls, _) => acc ++ ls) []
  let callGraph : List (Ident × List Ident) :=
    extracted.map fun (fd, _, bodyClean, _, _) => (fd.name, collectCallsExpr bodyClean)
  let env : VcgEnv := {
    contracts := fun nm => (contractMap.find? (·.1 == nm)).map Prod.snd
    loops := fun c b =>
      (allLoops.find? (fun (c0, b0, _) => reprStr c0 == reprStr c && reprStr b0 == reprStr b)).map
        (fun (_, _, lc) => lc)
    isSameScc := fun cur nm => nm == cur || canReachFn callGraph nm cur extracted.length
  }
  -- 2. Run `verifyFn` on every non-empty user function (skip trivial `main = ()`)
  let mut verifiedFns : Nat := 0
  let mut allObs : List (Ident × SForm) := []
  for (fd, fc, bodyClean, _, hasC) in extracted do
    let isTrivialMain := fd.name == "main" && !hasC &&
      match bodyClean with
      | .lit .unit => true
      | .block [] => true
      | .block [.lit .unit] => true
      | _ => false
    if !isTrivialMain then
      let fdClean : FunDef := { fd with body := bodyClean }
      match verifyFn env fdClean fc with
      | none =>
        throw s!"VCG FAIL-CLOSED: function '{fd.name}' rejected by CoreGeisha.VCG (unmodeled construct, aliased mutable argument, or unannotated loop)"
      | some obs =>
        verifiedFns := verifiedFns + 1
        allObs := allObs ++ obs.map (fun ob => (fd.name, ob))
  return (verifiedFns, allObs)

/-! ## Part 9: Verification-Driven Optimization Soundness (`verified_opt_sound`)

Models `--verified-opt` check elision directly on `CoreGeisha`'s small-step operational
semantics:
1. `elideVerifiedAsserts Φ` replaces `"assert"`'s trapping failure branch `.trap .divByZero`
   with `.lit .unit` (modeling elided runtime assertion / `requires` checks);
2. `StepUnchecked` runs under `elideVerifiedAsserts Φ` and removes `.trap .divByZero`
   transitions (modeling elided division/modulo-by-zero checks).

Without verification, `StepUnchecked` is strictly unsound (`assert(false)` silently
evaluates to `()`, and `1 / 0` silently evaluates to `0` instead of trapping). Theorem `verified_opt_sound`
proves that for every function verified by `verifyFn` with `ValidObs obs` and satisfied
precondition `fc.req`, `StepsUnchecked` is **bidirectionally observationally equivalent**
to `Steps` (identical return value `v` and final heap `σ'`, no `.divByZero` trap, and
postcondition `fc.ens` preserved). -/

/-- Unchecked binary operator evaluation (`--verified-opt`):
    agrees with `evalBinOp` on all non-trapping inputs, but elides the division/remainder-by-zero
    trap check by returning a silent fallback literal (`0` / `0i64`) when dividing by `0`. -/
def evalBinOpUnchecked (op : BinOp) (l1 l2 : Lit) : Option Lit :=
  match evalBinOp op l1 l2 with
  | some (.val l') => some l'
  | some (.trap .divByZero) =>
    match op with
    | .div64 | .rem64 => some (.int64 0)
    | _ => some (.int 0)
  | _ => none

private theorem evalBinOpUnchecked_of_val {op : BinOp} {l1 l2 l' : Lit}
    (h : evalBinOp op l1 l2 = some (.val l')) : evalBinOpUnchecked op l1 l2 = some l' := by
  simp [evalBinOpUnchecked, h]

/-- Unchecked `assert` stub: elides the `.trap .divByZero` failure branch. -/
def assertElidedFunDef : FunDef :=
  { name := "assert", params := [("b", .bool)], retTy := .void,
    body := .if_ (.var "b") (.lit .unit) (.lit .unit) }

/-- Optimized function environment with runtime `assert` traps elided. -/
def elideVerifiedAsserts (Φ : FunEnv) : FunEnv :=
  fun nm => if nm == "assert" then some assertElidedFunDef else Φ nm

/- One-step unchecked operational semantics (`--verified-opt`):
   1. Evaluates direct calls under `elideVerifiedAsserts Φ` (runtime `assert` traps elided);
   2. Evaluates binary operators with `evalBinOpUnchecked` (division/modulo-by-zero checks elided:
      dividing by `0` silently yields `0` instead of trapping `.trap .divByZero`). -/
mutual
inductive StepUnchecked (Δ : AdtEnv) (Φ : FunEnv) : Expr → Store → Expr → Store → Prop where
  | tupleStep {es es' : List Expr} {σ σ' : Store} :
      StepListUnchecked Δ Φ es σ es' σ' → StepUnchecked Δ Φ (.tuple es) σ (.tuple es') σ'
  | tupleTrap {es : List Expr} {t : Trap} {σ : Store} :
      ListFirstTrap es t → StepUnchecked Δ Φ (.tuple es) σ (.trap t) σ
  | blockEmpty {σ : Store} : StepUnchecked Δ Φ (.block []) σ (.lit .unit) σ
  | blockSingle {e : Expr} {σ : Store} : StepUnchecked Δ Φ (.block [e]) σ e σ
  | blockConsStep {e1 e1' e2 : Expr} {es : List Expr} {σ σ' : Store} :
      StepUnchecked Δ Φ e1 σ e1' σ' →
      StepUnchecked Δ Φ (.block (e1 :: e2 :: es)) σ (.block (e1' :: e2 :: es)) σ'
  | blockConsVal {v1 e2 : Expr} {es : List Expr} {σ : Store} :
      IsValue v1 → StepUnchecked Δ Φ (.block (v1 :: e2 :: es)) σ (.block (e2 :: es)) σ
  | blockConsTrap {t : Trap} {e2 : Expr} {es : List Expr} {σ : Store} :
      StepUnchecked Δ Φ (.block (.trap t :: e2 :: es)) σ (.trap t) σ
  | applyFn {fn fn' : Expr} {args : List Expr} {σ σ' : Store} :
      StepUnchecked Δ Φ fn σ fn' σ' → StepUnchecked Δ Φ (.apply fn args) σ (.apply fn' args) σ'
  | applyFnTrap {t : Trap} {args : List Expr} {σ : Store} :
      StepUnchecked Δ Φ (.apply (.trap t) args) σ (.trap t) σ
  | applyArgs {fn : Expr} {args args' : List Expr} {σ σ' : Store} :
      IsValue fn → StepListUnchecked Δ Φ args σ args' σ' →
      StepUnchecked Δ Φ (.apply fn args) σ (.apply fn args') σ'
  | applyArgsTrap {fn : Expr} {args : List Expr} {t : Trap} {σ : Store} :
      IsValue fn → ListFirstTrap args t → StepUnchecked Δ Φ (.apply fn args) σ (.trap t) σ
  | applyBeta {m : Mode} {ps : List (Ident × Ty)} {ret : Ty} {body : Expr}
      {args : List Expr} {σ : Store} :
      (∀ a ∈ args, IsValue a) → args.length = ps.length →
      StepUnchecked Δ Φ (.apply (.lam m ps ret body) args) σ (substMany (zipParams ps args) body) σ
  | applyDirArgs {name : Ident} {args args' : List Expr} {σ σ' : Store} :
      StepListUnchecked Δ Φ args σ args' σ' →
      StepUnchecked Δ Φ (.applyDir name args) σ (.applyDir name args') σ'
  | applyDirTrap {name : Ident} {args : List Expr} {t : Trap} {σ : Store} :
      ListFirstTrap args t → StepUnchecked Δ Φ (.applyDir name args) σ (.trap t) σ
  | applyDirBeta {name : Ident} {fd : FunDef} {args : List Expr} {σ : Store} :
      elideVerifiedAsserts Φ name = some fd →
      (∀ a ∈ args, IsValue a) → args.length = fd.params.length →
      StepUnchecked Δ Φ (.applyDir name args) σ (substMany (zipParams fd.params args) fd.body) σ
  | unStep {op : UnOp} {e e' : Expr} {σ σ' : Store} :
      StepUnchecked Δ Φ e σ e' σ' → StepUnchecked Δ Φ (.un op e) σ (.un op e') σ'
  | unTrap {op : UnOp} {t : Trap} {σ : Store} :
      StepUnchecked Δ Φ (.un op (.trap t)) σ (.trap t) σ
  | unVal {op : UnOp} {l l' : Lit} {σ : Store} :
      evalUnOp op l = some l' → StepUnchecked Δ Φ (.un op (.lit l)) σ (.lit l') σ
  | binLeft {op : BinOp} {e1 e1' e2 : Expr} {σ σ' : Store} :
      StepUnchecked Δ Φ e1 σ e1' σ' → StepUnchecked Δ Φ (.bin op e1 e2) σ (.bin op e1' e2) σ'
  | binLeftTrap {op : BinOp} {t : Trap} {e2 : Expr} {σ : Store} :
      StepUnchecked Δ Φ (.bin op (.trap t) e2) σ (.trap t) σ
  | binAndFalse {e2 : Expr} {σ : Store} :
      StepUnchecked Δ Φ (.bin .and (.lit (.bool false)) e2) σ (.lit (.bool false)) σ
  | binAndTrue {e2 : Expr} {σ : Store} :
      StepUnchecked Δ Φ (.bin .and (.lit (.bool true)) e2) σ e2 σ
  | binOrTrue {e2 : Expr} {σ : Store} :
      StepUnchecked Δ Φ (.bin .or (.lit (.bool true)) e2) σ (.lit (.bool true)) σ
  | binOrFalse {e2 : Expr} {σ : Store} :
      StepUnchecked Δ Φ (.bin .or (.lit (.bool false)) e2) σ e2 σ
  | binRight {op : BinOp} {v1 e2 e2' : Expr} {σ σ' : Store} :
      op ≠ .and → op ≠ .or → IsValue v1 → StepUnchecked Δ Φ e2 σ e2' σ' →
      StepUnchecked Δ Φ (.bin op v1 e2) σ (.bin op v1 e2') σ'
  | binRightTrap {op : BinOp} {v1 : Expr} {t : Trap} {σ : Store} :
      op ≠ .and → op ≠ .or → IsValue v1 →
      StepUnchecked Δ Φ (.bin op v1 (.trap t)) σ (.trap t) σ
  | binVal {op : BinOp} {l1 l2 l' : Lit} {σ : Store} :
      evalBinOpUnchecked op l1 l2 = some l' →
      StepUnchecked Δ Φ (.bin op (.lit l1) (.lit l2)) σ (.lit l') σ
  | binTrap {op : BinOp} {l1 l2 : Lit} {t : Trap} {σ : Store} :
      evalBinOp op l1 l2 = some (.trap t) → t ≠ .divByZero →
      StepUnchecked Δ Φ (.bin op (.lit l1) (.lit l2)) σ (.trap t) σ
  | letStep {x : Ident} {e1 e1' e2 : Expr} {σ σ' : Store} :
      StepUnchecked Δ Φ e1 σ e1' σ' → StepUnchecked Δ Φ (.let_ x e1 e2) σ (.let_ x e1' e2) σ'
  | letTrap {x : Ident} {t : Trap} {e2 : Expr} {σ : Store} :
      StepUnchecked Δ Φ (.let_ x (.trap t) e2) σ (.trap t) σ
  | letVal {x : Ident} {v1 e2 : Expr} {σ : Store} :
      IsValue v1 → StepUnchecked Δ Φ (.let_ x v1 e2) σ (subst x v1 e2) σ
  | ifStep {c c' t e : Expr} {σ σ' : Store} :
      StepUnchecked Δ Φ c σ c' σ' → StepUnchecked Δ Φ (.if_ c t e) σ (.if_ c' t e) σ'
  | ifTrap {tr : Trap} {t e : Expr} {σ : Store} :
      StepUnchecked Δ Φ (.if_ (.trap tr) t e) σ (.trap tr) σ
  | ifTrue {t e : Expr} {σ : Store} :
      StepUnchecked Δ Φ (.if_ (.lit (.bool true)) t e) σ t σ
  | ifFalse {t e : Expr} {σ : Store} :
      StepUnchecked Δ Φ (.if_ (.lit (.bool false)) t e) σ e σ
  | whileUnfold {c b : Expr} {σ : Store} :
      StepUnchecked Δ Φ (.while_ c b) σ (.if_ c (.block [b, .while_ c b]) (.lit .unit)) σ
  | matchScrut {s s' : Expr} {arms : List (Pat × Expr)} {σ σ' : Store} :
      StepUnchecked Δ Φ s σ s' σ' → StepUnchecked Δ Φ (.match_ s arms) σ (.match_ s' arms) σ'
  | matchScrutTrap {t : Trap} {arms : List (Pat × Expr)} {σ : Store} :
      StepUnchecked Δ Φ (.match_ (.trap t) arms) σ (.trap t) σ
  | matchEmpty {v : Expr} {σ : Store} :
      IsValue v → StepUnchecked Δ Φ (.match_ v []) σ (.trap .matchFailure) σ
  | matchHit {v : Expr} {p : Pat} {body : Expr} {rest : List (Pat × Expr)}
      {env : List (Ident × Expr)} {σ : Store} :
      IsValue v → matchPat p v = some env →
      StepUnchecked Δ Φ (.match_ v ((p, body) :: rest)) σ (substMany env body) σ
  | matchMiss {v : Expr} {p : Pat} {body : Expr} {rest : List (Pat × Expr)} {σ : Store} :
      IsValue v → matchPat p v = none →
      StepUnchecked Δ Φ (.match_ v ((p, body) :: rest)) σ (.match_ v rest) σ
  | makeDataStep {adt : Ident} {tag : Nat} {es es' : List Expr} {σ σ' : Store} :
      StepListUnchecked Δ Φ es σ es' σ' →
      StepUnchecked Δ Φ (.makeData adt tag es) σ (.makeData adt tag es') σ'
  | makeDataTrap {adt : Ident} {tag : Nat} {es : List Expr} {t : Trap} {σ : Store} :
      ListFirstTrap es t → StepUnchecked Δ Φ (.makeData adt tag es) σ (.trap t) σ
  | getTagStep {e e' : Expr} {σ σ' : Store} :
      StepUnchecked Δ Φ e σ e' σ' → StepUnchecked Δ Φ (.getTag e) σ (.getTag e') σ'
  | getTagTrap {t : Trap} {σ : Store} :
      StepUnchecked Δ Φ (.getTag (.trap t)) σ (.trap t) σ
  | getTagVal {adt : Ident} {tag : Nat} {vs : List Expr} {σ : Store} :
      (∀ v ∈ vs, IsValue v) →
      StepUnchecked Δ Φ (.getTag (.makeData adt tag vs)) σ (.lit (.int (Int32.ofNat tag))) σ
  | cellNewStep {e e' : Expr} {σ σ' : Store} :
      StepUnchecked Δ Φ e σ e' σ' → StepUnchecked Δ Φ (.cellNew e) σ (.cellNew e') σ'
  | cellNewTrap {t : Trap} {σ : Store} :
      StepUnchecked Δ Φ (.cellNew (.trap t)) σ (.trap t) σ
  | cellNewVal {v : Expr} {σ : Store} :
      IsValue v → StepUnchecked Δ Φ (.cellNew v) σ (.loc σ.length) (σ ++ [v])
  | cellGetStep {e e' : Expr} {σ σ' : Store} :
      StepUnchecked Δ Φ e σ e' σ' → StepUnchecked Δ Φ (.cellGet e) σ (.cellGet e') σ'
  | cellGetTrap {t : Trap} {σ : Store} :
      StepUnchecked Δ Φ (.cellGet (.trap t)) σ (.trap t) σ
  | cellGetVal {l : Loc} {v : Expr} {σ : Store} :
      σ[l]? = some v → StepUnchecked Δ Φ (.cellGet (.loc l)) σ v σ
  | cellSetLeft {e1 e1' e2 : Expr} {σ σ' : Store} :
      StepUnchecked Δ Φ e1 σ e1' σ' → StepUnchecked Δ Φ (.cellSet e1 e2) σ (.cellSet e1' e2) σ'
  | cellSetLeftTrap {t : Trap} {e2 : Expr} {σ : Store} :
      StepUnchecked Δ Φ (.cellSet (.trap t) e2) σ (.trap t) σ
  | cellSetRight {v1 e2 e2' : Expr} {σ σ' : Store} :
      IsValue v1 → StepUnchecked Δ Φ e2 σ e2' σ' →
      StepUnchecked Δ Φ (.cellSet v1 e2) σ (.cellSet v1 e2') σ'
  | cellSetRightTrap {v1 : Expr} {t : Trap} {σ : Store} :
      IsValue v1 → StepUnchecked Δ Φ (.cellSet v1 (.trap t)) σ (.trap t) σ
  | cellSetVal {l : Loc} {v : Expr} {σ : Store} :
      l < σ.length → IsValue v →
      StepUnchecked Δ Φ (.cellSet (.loc l) v) σ (.lit .unit) (σ.set l v)
  | spawnStep {e e' : Expr} {σ σ' : Store} :
      StepUnchecked Δ Φ e σ e' σ' → StepUnchecked Δ Φ (.spawn e) σ (.spawn e') σ'
  | spawnTrap {t : Trap} {σ : Store} :
      StepUnchecked Δ Φ (.spawn (.trap t)) σ (.trap t) σ
  | awaitStep {e e' : Expr} {σ σ' : Store} :
      StepUnchecked Δ Φ e σ e' σ' → StepUnchecked Δ Φ (.await e) σ (.await e') σ'
  | awaitTrap {t : Trap} {σ : Store} :
      StepUnchecked Δ Φ (.await (.trap t)) σ (.trap t) σ
  | awaitVal {tid : TaskId} {v : Expr} {σ : Store} :
      emptyPool.tasks[tid]? = some (.running v) → IsValue v →
      StepUnchecked Δ Φ (.await (.taskRef tid)) σ v σ
  | awaitTaskTrap {tid : TaskId} {t : Trap} {σ : Store} :
      emptyPool.tasks[tid]? = some (.running (.trap t)) →
      StepUnchecked Δ Φ (.await (.taskRef tid)) σ (.trap t) σ
  | concPrimArgs {op : ConcPrim} {args args' : List Expr} {σ σ' : Store} :
      StepListUnchecked Δ Φ args σ args' σ' →
      StepUnchecked Δ Φ (.concPrim op args) σ (.concPrim op args') σ'
  | concPrimTrap {op : ConcPrim} {args : List Expr} {t : Trap} {σ : Store} :
      ListFirstTrap args t → StepUnchecked Δ Φ (.concPrim op args) σ (.trap t) σ
  | concPrimVal {op : ConcPrim} {args : List Expr} {e' : Expr} {σ : Store} :
      StepConcPrim emptyPool op args e' .none →
      StepUnchecked Δ Φ (.concPrim op args) σ e' σ

inductive StepListUnchecked (Δ : AdtEnv) (Φ : FunEnv) :
    List Expr → Store → List Expr → Store → Prop where
  | head {e e' : Expr} {es : List Expr} {σ σ' : Store} :
      StepUnchecked Δ Φ e σ e' σ' →
      StepListUnchecked Δ Φ (e :: es) σ (e' :: es) σ'
  | tail {v : Expr} {es es' : List Expr} {σ σ' : Store} :
      IsValue v → StepListUnchecked Δ Φ es σ es' σ' →
      StepListUnchecked Δ Φ (v :: es) σ (v :: es') σ'
end

/-- Multi-step unchecked operational semantics. -/
inductive StepsUnchecked (Δ : AdtEnv) (Φ : FunEnv) : Expr → Store → Expr → Store → Prop where
  | refl (e : Expr) (σ : Store) : StepsUnchecked Δ Φ e σ e σ
  | trans {e1 e2 e3 : Expr} {σ1 σ2 σ3 : Store} :
      StepUnchecked Δ Φ e1 σ1 e2 σ2 →
      StepsUnchecked Δ Φ e2 σ2 e3 σ3 →
      StepsUnchecked Δ Φ e1 σ1 e3 σ3

/-- Non-vacuity witness 1: without verification, `StepUnchecked` silently evaluates
    `assert(false)` to `()`, whereas original `Steps` traps with `.trap .divByZero`. -/
theorem unchecked_assert_false_diverges {Δ : AdtEnv} {Φ : FunEnv}
    (hIntr : IntrinsicsOk Φ) (σ : Store) :
    Steps Δ Φ (.applyDir "assert" [.lit (.bool false)]) σ (.trap .divByZero) σ ∧
    StepsUnchecked Δ Φ (.applyDir "assert" [.lit (.bool false)]) σ (.lit .unit) σ := by
  constructor
  · exact .trans (.applyDirBeta hIntr.1 (fun _ h => by simp at h; subst h; exact .lit _) rfl)
      (.trans .ifFalse (.refl _ _))
  · exact .trans (.applyDirBeta (fd := assertElidedFunDef) (by simp [elideVerifiedAsserts])
        (fun _ h => by simp at h; subst h; exact .lit _) rfl)
      (.trans .ifFalse (.refl _ _))

/-- Non-vacuity witness 2: without verification, `StepUnchecked` silently evaluates
    `1 / 0` to `0` (elided zero check), whereas original `Steps` traps with `.trap .divByZero`. -/
theorem unchecked_div_zero_diverges {Δ : AdtEnv} {Φ : FunEnv} (σ : Store) :
    Steps Δ Φ (.bin .div (.lit (.int 1)) (.lit (.int 0))) σ (.trap .divByZero) σ ∧
    StepsUnchecked Δ Φ (.bin .div (.lit (.int 1)) (.lit (.int 0))) σ (.lit (.int 0)) σ := by
  constructor
  · exact .trans (.binTrap (by simp [evalBinOp])) (.refl _ _)
  · exact .trans (.binVal (by simp [evalBinOpUnchecked, evalBinOp])) (.refl _ _)

mutual
private theorem value_no_stepUnchecked {Δ : AdtEnv} {Φ : FunEnv} {v e' : Expr} {σ σ' : Store}
    (hv : IsValue v) (hs : StepUnchecked Δ Φ v σ e' σ') : False := by
  cases hs with
  | tupleStep hsl =>
    cases hv with | tuple hvs => exact valueList_no_stepListUnchecked hvs hsl
  | tupleTrap hft =>
    cases hv with | tuple hvs => exact valueList_no_firstTrap hvs hft
  | makeDataStep hsl =>
    cases hv with | makeData _ _ hvs => exact valueList_no_stepListUnchecked hvs hsl
  | makeDataTrap hft =>
    cases hv with | makeData _ _ hvs => exact valueList_no_firstTrap hvs hft
  | _ => cases hv
termination_by sizeOf v

private theorem valueList_no_stepListUnchecked {Δ : AdtEnv} {Φ : FunEnv} {vs es' : List Expr}
    {σ σ' : Store} (hvs : ∀ v ∈ vs, IsValue v) (hsl : StepListUnchecked Δ Φ vs σ es' σ') : False := by
  cases hsl with
  | head hs1 => exact value_no_stepUnchecked (hvs _ (List.mem_cons_self ..)) hs1
  | tail _ hsl' => exact valueList_no_stepListUnchecked (fun x hx => hvs x (List.mem_cons_of_mem _ hx)) hsl'
termination_by sizeOf vs
end

private def NoDivZero (Δ : AdtEnv) (Φ : FunEnv) (e : Expr) (σ : Store) : Prop :=
  ∀ σ', ¬ Steps Δ Φ e σ (.trap .divByZero) σ'

private theorem noDivZero_of_step {Δ : AdtEnv} {Φ : FunEnv} {e e' : Expr} {σ σ' : Store}
    (hnd : NoDivZero Δ Φ e σ) (hs : Step Δ Φ emptyPool e σ e' σ' .none) :
    NoDivZero Δ Φ e' σ' :=
  fun σ'' hst => hnd σ'' (.trans hs hst)

private theorem noDivZero_ne_trap {Δ : AdtEnv} {Φ : FunEnv} {e e' : Expr} {σ σ' : Store}
    (hnd : NoDivZero Δ Φ e σ) (hs : Step Δ Φ emptyPool e σ e' σ' .none) :
    e' ≠ .trap .divByZero := by
  intro hEq; subst hEq
  exact hnd σ' (.trans hs (.refl _ _))

-- Trap-lifting lemmas for active evaluation contexts
private theorem steps_lift_ctx {Δ : AdtEnv} {Φ : FunEnv} {e : Expr} {σ σ' : Store} {t : Trap}
    (C : Expr → Expr)
    (hStep : ∀ {x x' σ1 σ2}, Step Δ Φ emptyPool x σ1 x' σ2 .none →
      Step Δ Φ emptyPool (C x) σ1 (C x') σ2 .none)
    (hTrap : ∀ {σ1}, Step Δ Φ emptyPool (C (.trap t)) σ1 (.trap t) σ1 .none)
    (h : Steps Δ Φ e σ (.trap t) σ') :
    Steps Δ Φ (C e) σ (.trap t) σ' := by
  generalize hres : Expr.trap t = res at h
  induction h with
  | refl => subst hres; exact .trans hTrap (.refl _ _)
  | trans hs _ ih => exact .trans (hStep hs) (ih hres)

/-- Helper: multi-step list reduction ending in a `ListFirstTrap` lifts into any list context `C`. -/
private inductive StepsList (Δ : AdtEnv) (Φ : FunEnv) : List Expr → Store → List Expr → Store → Prop where
  | refl (es : List Expr) (σ : Store) : StepsList Δ Φ es σ es σ
  | trans {es1 es2 es3 : List Expr} {σ1 σ2 σ3 : Store} :
      StepList Δ Φ emptyPool es1 σ1 es2 σ2 .none →
      StepsList Δ Φ es2 σ2 es3 σ3 →
      StepsList Δ Φ es1 σ1 es3 σ3

private def NoDivZeroList (Δ : AdtEnv) (Φ : FunEnv) (es : List Expr) (σ : Store) : Prop :=
  ∀ es' σ', StepsList Δ Φ es σ es' σ' → ¬ ListFirstTrap es' .divByZero

private theorem noDivZeroList_of_ctx {Δ : AdtEnv} {Φ : FunEnv} {es : List Expr} {σ : Store}
    (C : List Expr → Expr)
    (hStep : ∀ {xs xs' σ1 σ2}, StepList Δ Φ emptyPool xs σ1 xs' σ2 .none →
      Step Δ Φ emptyPool (C xs) σ1 (C xs') σ2 .none)
    (hTrap : ∀ {xs σ1}, ListFirstTrap xs .divByZero →
      Step Δ Φ emptyPool (C xs) σ1 (.trap .divByZero) σ1 .none)
    (hnd : NoDivZero Δ Φ (C es) σ) :
    NoDivZeroList Δ Φ es σ := by
  intro es' σ' hsl hft
  have hsteps : Steps Δ Φ (C es) σ (.trap .divByZero) σ' := by
    clear hnd
    induction hsl with
    | refl => exact .trans (hTrap hft) (.refl _ _)
    | trans hs _ ih => exact .trans (hStep hs) (ih hft)
  exact hnd σ' hsteps

private theorem noDivZeroList_head {Δ : AdtEnv} {Φ : FunEnv} {e : Expr} {es : List Expr} {σ : Store}
    (hnd : NoDivZeroList Δ Φ (e :: es) σ) : NoDivZero Δ Φ e σ := by
  intro σ' hst
  have hsl : StepsList Δ Φ (e :: es) σ (.trap .divByZero :: es) σ' := by
    clear hnd
    generalize hres : Expr.trap .divByZero = res at hst
    induction hst with
    | refl => subst hres; exact .refl _ _
    | trans hs _ ih => exact .trans (.head hs) (ih hres)
  exact hnd _ _ hsl (.head _ _)

private theorem noDivZeroList_tail {Δ : AdtEnv} {Φ : FunEnv} {v : Expr} {es : List Expr} {σ : Store}
    (hv : IsValue v) (hnd : NoDivZeroList Δ Φ (v :: es) σ) : NoDivZeroList Δ Φ es σ := by
  intro es' σ' hsl hft
  have hsl' : StepsList Δ Φ (v :: es) σ (v :: es') σ' := by
    clear hnd hft
    induction hsl with
    | refl => exact .refl _ _
    | trans hs _ ih => exact .trans (.tail hv hs) ih
  exact hnd _ _ hsl' (.tail hv hft)

/- Bisimulation relation between an expression running under original `Φ` and under
   `elideVerifiedAsserts Φ`: identical everywhere except an active `assert` body
   `.if_ v (.lit .unit) (.trap .divByZero)` may correspond to `.if_ v (.lit .unit) (.lit .unit)`. -/
mutual
private inductive AssertEq : Expr → Expr → Prop where
  | refl (e : Expr) : AssertEq e e
  | assertIf {v : Expr} : IsValue v →
      AssertEq (.if_ v (.lit .unit) (.trap .divByZero)) (.if_ v (.lit .unit) (.lit .unit))
  | tuple {es1 es2 : List Expr} : AssertEqList es1 es2 → AssertEq (.tuple es1) (.tuple es2)
  | blockCons {e1 e1' e2 : Expr} {es : List Expr} :
      AssertEq e1 e1' → AssertEq (.block (e1 :: e2 :: es)) (.block (e1' :: e2 :: es))
  | applyFn {f1 f2 : Expr} {args : List Expr} :
      AssertEq f1 f2 → AssertEq (.apply f1 args) (.apply f2 args)
  | applyArgs {fn : Expr} {a1 a2 : List Expr} :
      IsValue fn → AssertEqList a1 a2 → AssertEq (.apply fn a1) (.apply fn a2)
  | applyDirArgs {nm : Ident} {a1 a2 : List Expr} :
      AssertEqList a1 a2 → AssertEq (.applyDir nm a1) (.applyDir nm a2)
  | un {op : UnOp} {e1 e2 : Expr} : AssertEq e1 e2 → AssertEq (.un op e1) (.un op e2)
  | binLeft {op : BinOp} {e1 e1' e2 : Expr} :
      AssertEq e1 e1' → AssertEq (.bin op e1 e2) (.bin op e1' e2)
  | binRight {op : BinOp} {v1 e2 e2' : Expr} :
      op ≠ .and → op ≠ .or → IsValue v1 →
      AssertEq e2 e2' → AssertEq (.bin op v1 e2) (.bin op v1 e2')
  | let_ {x : Ident} {e1 e1' e2 : Expr} :
      AssertEq e1 e1' → AssertEq (.let_ x e1 e2) (.let_ x e1' e2)
  | if_ {c1 c2 t e : Expr} :
      AssertEq c1 c2 → AssertEq (.if_ c1 t e) (.if_ c2 t e)
  | match_ {s1 s2 : Expr} {arms : List (Pat × Expr)} :
      AssertEq s1 s2 → AssertEq (.match_ s1 arms) (.match_ s2 arms)
  | makeData {adt : Ident} {tag : Nat} {es1 es2 : List Expr} :
      AssertEqList es1 es2 → AssertEq (.makeData adt tag es1) (.makeData adt tag es2)
  | getTag {e1 e2 : Expr} : AssertEq e1 e2 → AssertEq (.getTag e1) (.getTag e2)
  | cellNew {e1 e2 : Expr} : AssertEq e1 e2 → AssertEq (.cellNew e1) (.cellNew e2)
  | cellGet {e1 e2 : Expr} : AssertEq e1 e2 → AssertEq (.cellGet e1) (.cellGet e2)
  | cellSetLeft {e1 e1' e2 : Expr} :
      AssertEq e1 e1' → AssertEq (.cellSet e1 e2) (.cellSet e1' e2)
  | cellSetRight {v1 e2 e2' : Expr} :
      IsValue v1 → AssertEq e2 e2' → AssertEq (.cellSet v1 e2) (.cellSet v1 e2')
  | spawn {e1 e2 : Expr} : AssertEq e1 e2 → AssertEq (.spawn e1) (.spawn e2)
  | await {e1 e2 : Expr} : AssertEq e1 e2 → AssertEq (.await e1) (.await e2)
  | concPrim {op : ConcPrim} {a1 a2 : List Expr} :
      AssertEqList a1 a2 → AssertEq (.concPrim op a1) (.concPrim op a2)

private inductive AssertEqList : List Expr → List Expr → Prop where
  | refl (es : List Expr) : AssertEqList es es
  | head {e1 e2 : Expr} {es : List Expr} :
      AssertEq e1 e2 → AssertEqList (e1 :: es) (e2 :: es)
  | tail {v : Expr} {es1 es2 : List Expr} :
      IsValue v → AssertEqList es1 es2 → AssertEqList (v :: es1) (v :: es2)
end

mutual
private theorem assertEq_eq_of_val_left {e1 e2 : Expr} (h : AssertEq e1 e2) (hv : IsValue e1) :
    e1 = e2 := by
  cases h with
  | refl => rfl
  | tuple hl => cases hv with | tuple hvs => rw [assertEqList_eq_of_vals_left hl hvs]
  | makeData hl => cases hv with | makeData _ _ hvs => rw [assertEqList_eq_of_vals_left hl hvs]
  | _ => cases hv

private theorem assertEqList_eq_of_vals_left {es1 es2 : List Expr} (h : AssertEqList es1 es2)
    (hvs : ∀ v ∈ es1, IsValue v) : es1 = es2 := by
  cases h with
  | refl => rfl
  | head he =>
    rw [assertEq_eq_of_val_left he (hvs _ (List.mem_cons_self ..))]
  | tail hv hl =>
    rw [assertEqList_eq_of_vals_left hl (fun v hmem => hvs v (List.mem_cons_of_mem _ hmem))]
end

mutual
private theorem assertEq_eq_of_val_right {e1 e2 : Expr} (h : AssertEq e1 e2) (hv : IsValue e2) :
    e1 = e2 := by
  cases h with
  | refl => rfl
  | tuple hl => cases hv with | tuple hvs => rw [assertEqList_eq_of_vals_right hl hvs]
  | makeData hl => cases hv with | makeData _ _ hvs => rw [assertEqList_eq_of_vals_right hl hvs]
  | _ => cases hv

private theorem assertEqList_eq_of_vals_right {es1 es2 : List Expr} (h : AssertEqList es1 es2)
    (hvs : ∀ v ∈ es2, IsValue v) : es1 = es2 := by
  cases h with
  | refl => rfl
  | head he =>
    rw [assertEq_eq_of_val_right he (hvs _ (List.mem_cons_self ..))]
  | tail hv hl =>
    rw [assertEqList_eq_of_vals_right hl (fun v hmem => hvs v (List.mem_cons_of_mem _ hmem))]
end

private theorem assertEq_trap_left {e1 e2 : Expr} {t : Trap} (h : AssertEq e1 e2) (heq : e1 = .trap t) :
    e2 = .trap t := by
  cases h <;> cases heq; rfl

private theorem assertEq_trap_right {e1 e2 : Expr} {t : Trap} (h : AssertEq e1 e2) (heq : e2 = .trap t) :
    e1 = .trap t := by
  cases h <;> cases heq; rfl

private theorem assertEqList_firstTrap_left {es1 es2 : List Expr} {t : Trap}
    (h : AssertEqList es1 es2) (hft : ListFirstTrap es1 t) : ListFirstTrap es2 t := by
  cases h with
  | refl => exact hft
  | head he =>
    cases hft with
    | head => rw [assertEq_trap_left he rfl]; exact .head _ _
    | tail hv hft' => rw [← assertEq_eq_of_val_left he hv]; exact .tail hv hft'
  | tail hv hl =>
    cases hft with
    | head => cases hv
    | tail _ hft' => exact .tail hv (assertEqList_firstTrap_left hl hft')

private theorem assertEqList_firstTrap_right {es1 es2 : List Expr} {t : Trap}
    (h : AssertEqList es1 es2) (hft : ListFirstTrap es2 t) : ListFirstTrap es1 t := by
  cases h with
  | refl => exact hft
  | head he =>
    cases hft with
    | head => rw [assertEq_trap_right he rfl]; exact .head _ _
    | tail hv hft' => rw [assertEq_eq_of_val_right he hv]; exact .tail hv hft'
  | tail hv hl =>
    cases hft with
    | head => cases hv
    | tail _ hft' => exact .tail hv (assertEqList_firstTrap_right hl hft')

private theorem applyDirBeta_fwd {Δ : AdtEnv} {Φ : FunEnv} (hIntr : IntrinsicsOk Φ)
    {nm : Ident} {fd : FunDef} {args : List Expr} {σ : Store}
    (hΦ : Φ nm = some fd) (hvs : ∀ a ∈ args, IsValue a) (hlen : args.length = fd.params.length) :
    ∃ e2', StepUnchecked Δ Φ (.applyDir nm args) σ e2' σ ∧
      AssertEq (substMany (zipParams fd.params args) fd.body) e2' := by
  by_cases hnm : nm = "assert"
  · subst hnm
    rw [hIntr.1] at hΦ; cases hΦ
    cases args with
    | nil => simp [assertFunDef] at hlen
    | cons v rest =>
      cases rest with
      | cons _ _ => simp [assertFunDef] at hlen
      | nil =>
        have hv : IsValue v := hvs v (List.mem_cons_self ..)
        refine ⟨substMany (zipParams assertElidedFunDef.params [v]) assertElidedFunDef.body,
          .applyDirBeta (fd := assertElidedFunDef) (by simp [elideVerifiedAsserts]) hvs rfl, ?_⟩
        simp only [assertFunDef, assertElidedFunDef, zipParams]
        exact .assertIf hv
  · exact ⟨_, .applyDirBeta (by simp [elideVerifiedAsserts, hnm, hΦ]) hvs hlen, .refl _⟩

private theorem binVal_fwd {Δ : AdtEnv} {Φ : FunEnv} {op : BinOp} {l1 l2 l' : Lit} {σ : Store}
    (h : evalBinOp op l1 l2 = some (.val l')) :
    ∃ e2', StepUnchecked Δ Φ (.bin op (.lit l1) (.lit l2)) σ e2' σ ∧ AssertEq (.lit l') e2' :=
  ⟨.lit l', .binVal (evalBinOpUnchecked_of_val h), .refl _⟩

private theorem binTrap_fwd {Δ : AdtEnv} {Φ : FunEnv} {op : BinOp} {l1 l2 : Lit} {t : Trap} {σ : Store}
    (hnd : NoDivZero Δ Φ (.bin op (.lit l1) (.lit l2)) σ)
    (h : evalBinOp op l1 l2 = some (.trap t)) :
    ∃ e2', StepUnchecked Δ Φ (.bin op (.lit l1) (.lit l2)) σ e2' σ ∧ AssertEq (.trap t) e2' := by
  have hne : t ≠ .divByZero := by
    intro ht; subst ht
    exact hnd σ (.trans (.binTrap h) (.refl _ _))
  exact ⟨.trap t, .binTrap h hne, .refl _⟩

private theorem binVal_bwd {Δ : AdtEnv} {Φ : FunEnv} {op : BinOp} {l1 l2 l' : Lit} {σ : Store}
    (hnd : NoDivZero Δ Φ (.bin op (.lit l1) (.lit l2)) σ)
    (h : evalBinOpUnchecked op l1 l2 = some l') :
    ∃ e1', Step Δ Φ emptyPool (.bin op (.lit l1) (.lit l2)) σ e1' σ .none ∧ AssertEq e1' (.lit l') := by
  cases h0 : evalBinOp op l1 l2 with
  | none => simp [evalBinOpUnchecked, h0] at h
  | some r =>
    cases r with
    | val l'' =>
      simp [evalBinOpUnchecked, h0] at h; subst h
      exact ⟨.lit l'', .binVal h0, .refl _⟩
    | trap t =>
      cases t with
      | divByZero => exact False.elim (hnd σ (.trans (.binTrap h0) (.refl _ _)))
      | matchFailure => simp [evalBinOpUnchecked, h0] at h
      | hostTrap => simp [evalBinOpUnchecked, h0] at h

private theorem applyDirBeta_bwd {Δ : AdtEnv} {Φ : FunEnv} (hIntr : IntrinsicsOk Φ)
    {nm : Ident} {fd : FunDef} {args : List Expr} {σ : Store}
    (hΦ : elideVerifiedAsserts Φ nm = some fd) (hvs : ∀ a ∈ args, IsValue a) (hlen : args.length = fd.params.length) :
    ∃ e1', Step Δ Φ emptyPool (.applyDir nm args) σ e1' σ .none ∧
      AssertEq e1' (substMany (zipParams fd.params args) fd.body) := by
  by_cases hnm : nm = "assert"
  · subst hnm
    simp [elideVerifiedAsserts] at hΦ; subst hΦ
    cases args with
    | nil => simp [assertElidedFunDef] at hlen
    | cons v rest =>
      cases rest with
      | cons _ _ => simp [assertElidedFunDef] at hlen
      | nil =>
        have hv : IsValue v := hvs v (List.mem_cons_self ..)
        refine ⟨substMany (zipParams assertFunDef.params [v]) assertFunDef.body,
          .applyDirBeta hIntr.1 hvs rfl, ?_⟩
        simp only [assertFunDef, assertElidedFunDef, zipParams]
        exact .assertIf hv
  · simp [elideVerifiedAsserts, hnm] at hΦ
    exact ⟨_, .applyDirBeta hΦ hvs hlen, .refl _⟩

/- Forward 1-step simulation: any step under `Φ` from a `NoDivZero` state is matched by
   a step under `elideVerifiedAsserts Φ` preserving `AssertEq`. -/
mutual
private theorem assertEq_step_fwd {Δ : AdtEnv} {Φ : FunEnv} (hIntr : IntrinsicsOk Φ)
    {e1 e2 e1' : Expr} {σ σ' : Store}
    (heq : AssertEq e1 e2) (hnd : NoDivZero Δ Φ e1 σ)
    (hs : Step Δ Φ emptyPool e1 σ e1' σ' .none) :
    ∃ e2', StepUnchecked Δ Φ e2 σ e2' σ' ∧ AssertEq e1' e2' := by
  cases heq with
  | refl =>
    cases hs with
    | tupleStep hsl =>
      rcases assertEqList_step_fwd hIntr (.refl _)
        (noDivZeroList_of_ctx .tuple .tupleStep .tupleTrap hnd) hsl with ⟨es', hsl', heql⟩
      exact ⟨.tuple es', .tupleStep hsl', .tuple heql⟩
    | tupleTrap hft => exact ⟨_, .tupleTrap hft, .refl _⟩
    | blockEmpty => exact ⟨_, .blockEmpty, .refl _⟩
    | blockSingle => exact ⟨_, .blockSingle, .refl _⟩
    | blockConsStep hs1 =>
      have hnd1 : NoDivZero Δ Φ _ σ := fun σ'' h => hnd σ'' (steps_lift_ctx (fun x => .block (x :: _ :: _)) .blockConsStep .blockConsTrap h)
      rcases assertEq_step_fwd hIntr (.refl _) hnd1 hs1 with ⟨e2', hs2, heq'⟩
      exact ⟨_, .blockConsStep hs2, .blockCons heq'⟩
    | blockConsVal hv => exact ⟨_, .blockConsVal hv, .refl _⟩
    | blockConsTrap => exact ⟨_, .blockConsTrap, .refl _⟩
    | applyFn hs1 =>
      have hnd1 : NoDivZero Δ Φ _ σ := fun σ'' h => hnd σ'' (steps_lift_ctx (fun x => .apply x _) .applyFn .applyFnTrap h)
      rcases assertEq_step_fwd hIntr (.refl _) hnd1 hs1 with ⟨f2', hs2, heq'⟩
      exact ⟨_, .applyFn hs2, .applyFn heq'⟩
    | applyFnTrap => exact ⟨_, .applyFnTrap, .refl _⟩
    | applyArgs hv hsl =>
      rcases assertEqList_step_fwd hIntr (.refl _)
        (noDivZeroList_of_ctx (.apply _) (.applyArgs hv) (.applyArgsTrap hv) hnd) hsl with ⟨a', hsl', heql⟩
      exact ⟨_, .applyArgs hv hsl', .applyArgs hv heql⟩
    | applyArgsTrap hv hft => exact ⟨_, .applyArgsTrap hv hft, .refl _⟩
    | applyBeta hvs hlen => exact ⟨_, .applyBeta hvs hlen, .refl _⟩
    | applyDirArgs hsl =>
      rcases assertEqList_step_fwd hIntr (.refl _)
        (noDivZeroList_of_ctx (.applyDir _) .applyDirArgs .applyDirTrap hnd) hsl with ⟨a', hsl', heql⟩
      exact ⟨_, .applyDirArgs hsl', .applyDirArgs heql⟩
    | applyDirTrap hft => exact ⟨_, .applyDirTrap hft, .refl _⟩
    | @applyDirBeta nm fd args _ hΦ hvs hlen =>
      by_cases hnm : nm = "assert"
      · subst hnm
        rw [hIntr.1] at hΦ; cases hΦ
        cases args with
        | nil => simp [assertFunDef] at hlen
        | cons v rest =>
          cases rest with
          | cons _ _ => simp [assertFunDef] at hlen
          | nil =>
            have hv : IsValue v := hvs v (List.mem_cons_self ..)
            refine ⟨substMany (zipParams assertElidedFunDef.params [v]) assertElidedFunDef.body,
              .applyDirBeta (by simp [elideVerifiedAsserts]) hvs rfl, ?_⟩
            simp only [assertFunDef, assertElidedFunDef, zipParams]
            exact .assertIf hv
      · exact ⟨_, .applyDirBeta (by simp [elideVerifiedAsserts, hnm, hΦ]) hvs hlen, .refl _⟩
    | unStep hs1 =>
      have hnd1 : NoDivZero Δ Φ _ σ := fun σ'' h => hnd σ'' (steps_lift_ctx (.un _) .unStep .unTrap h)
      rcases assertEq_step_fwd hIntr (.refl _) hnd1 hs1 with ⟨e2', hs2, heq'⟩
      exact ⟨_, .unStep hs2, .un heq'⟩
    | unTrap => exact ⟨_, .unTrap, .refl _⟩
    | unVal h => exact ⟨_, .unVal h, .refl _⟩
    | binLeft hs1 =>
      have hnd1 : NoDivZero Δ Φ _ σ := fun σ'' h => hnd σ'' (steps_lift_ctx (fun x => .bin _ x _) .binLeft .binLeftTrap h)
      rcases assertEq_step_fwd hIntr (.refl _) hnd1 hs1 with ⟨e2', hs2, heq'⟩
      exact ⟨_, .binLeft hs2, .binLeft heq'⟩
    | binLeftTrap => exact ⟨_, .binLeftTrap, .refl _⟩
    | binAndFalse => exact ⟨_, .binAndFalse, .refl _⟩
    | binAndTrue => exact ⟨_, .binAndTrue, .refl _⟩
    | binOrTrue => exact ⟨_, .binOrTrue, .refl _⟩
    | binOrFalse => exact ⟨_, .binOrFalse, .refl _⟩
    | binRight h1 h2 hv hs2 =>
      have hnd2 : NoDivZero Δ Φ _ σ := fun σ'' h => hnd σ'' (steps_lift_ctx (.bin _ _) (.binRight h1 h2 hv) (.binRightTrap h1 h2 hv) h)
      rcases assertEq_step_fwd hIntr (.refl _) hnd2 hs2 with ⟨e2', hs2', heq'⟩
      exact ⟨_, .binRight h1 h2 hv hs2', .binRight h1 h2 hv heq'⟩
    | binRightTrap h1 h2 hv => exact ⟨_, .binRightTrap h1 h2 hv, .refl _⟩
    | binVal h => exact binVal_fwd h
    | binTrap h => exact binTrap_fwd hnd h
    | letStep hs1 =>
      have hnd1 : NoDivZero Δ Φ _ σ := fun σ'' h => hnd σ'' (steps_lift_ctx (fun x => .let_ _ x _) .letStep .letTrap h)
      rcases assertEq_step_fwd hIntr (.refl _) hnd1 hs1 with ⟨e2', hs2, heq'⟩
      exact ⟨_, .letStep hs2, .let_ heq'⟩
    | letTrap => exact ⟨_, .letTrap, .refl _⟩
    | letVal hv => exact ⟨_, .letVal hv, .refl _⟩
    | ifStep hs1 =>
      have hnd1 : NoDivZero Δ Φ _ σ := fun σ'' h => hnd σ'' (steps_lift_ctx (fun x => .if_ x _ _) .ifStep .ifTrap h)
      rcases assertEq_step_fwd hIntr (.refl _) hnd1 hs1 with ⟨c2', hs2, heq'⟩
      exact ⟨_, .ifStep hs2, .if_ heq'⟩
    | ifTrap => exact ⟨_, .ifTrap, .refl _⟩
    | ifTrue => exact ⟨_, .ifTrue, .refl _⟩
    | ifFalse => exact ⟨_, .ifFalse, .refl _⟩
    | whileUnfold => exact ⟨_, .whileUnfold, .refl _⟩
    | matchScrut hs1 =>
      have hnd1 : NoDivZero Δ Φ _ σ := fun σ'' h => hnd σ'' (steps_lift_ctx (fun x => .match_ x _) .matchScrut .matchScrutTrap h)
      rcases assertEq_step_fwd hIntr (.refl _) hnd1 hs1 with ⟨s2', hs2, heq'⟩
      exact ⟨_, .matchScrut hs2, .match_ heq'⟩
    | matchScrutTrap => exact ⟨_, .matchScrutTrap, .refl _⟩
    | matchEmpty hv => exact ⟨_, .matchEmpty hv, .refl _⟩
    | matchHit hv hm => exact ⟨_, .matchHit hv hm, .refl _⟩
    | matchMiss hv hm => exact ⟨_, .matchMiss hv hm, .refl _⟩
    | makeDataStep hsl =>
      rcases assertEqList_step_fwd hIntr (.refl _)
        (noDivZeroList_of_ctx (.makeData _ _) .makeDataStep .makeDataTrap hnd) hsl with ⟨es', hsl', heql⟩
      exact ⟨_, .makeDataStep hsl', .makeData heql⟩
    | makeDataTrap hft => exact ⟨_, .makeDataTrap hft, .refl _⟩
    | getTagStep hs1 =>
      have hnd1 : NoDivZero Δ Φ _ σ := fun σ'' h => hnd σ'' (steps_lift_ctx .getTag .getTagStep .getTagTrap h)
      rcases assertEq_step_fwd hIntr (.refl _) hnd1 hs1 with ⟨e2', hs2, heq'⟩
      exact ⟨_, .getTagStep hs2, .getTag heq'⟩
    | getTagTrap => exact ⟨_, .getTagTrap, .refl _⟩
    | getTagVal hvs => exact ⟨_, .getTagVal hvs, .refl _⟩
    | cellNewStep hs1 =>
      have hnd1 : NoDivZero Δ Φ _ σ := fun σ'' h => hnd σ'' (steps_lift_ctx .cellNew .cellNewStep .cellNewTrap h)
      rcases assertEq_step_fwd hIntr (.refl _) hnd1 hs1 with ⟨e2', hs2, heq'⟩
      exact ⟨_, .cellNewStep hs2, .cellNew heq'⟩
    | cellNewTrap => exact ⟨_, .cellNewTrap, .refl _⟩
    | cellNewVal hv => exact ⟨_, .cellNewVal hv, .refl _⟩
    | cellGetStep hs1 =>
      have hnd1 : NoDivZero Δ Φ _ σ := fun σ'' h => hnd σ'' (steps_lift_ctx .cellGet .cellGetStep .cellGetTrap h)
      rcases assertEq_step_fwd hIntr (.refl _) hnd1 hs1 with ⟨e2', hs2, heq'⟩
      exact ⟨_, .cellGetStep hs2, .cellGet heq'⟩
    | cellGetTrap => exact ⟨_, .cellGetTrap, .refl _⟩
    | cellGetVal h => exact ⟨_, .cellGetVal h, .refl _⟩
    | cellSetLeft hs1 =>
      have hnd1 : NoDivZero Δ Φ _ σ := fun σ'' h => hnd σ'' (steps_lift_ctx (fun x => .cellSet x _) .cellSetLeft .cellSetLeftTrap h)
      rcases assertEq_step_fwd hIntr (.refl _) hnd1 hs1 with ⟨e2', hs2, heq'⟩
      exact ⟨_, .cellSetLeft hs2, .cellSetLeft heq'⟩
    | cellSetLeftTrap => exact ⟨_, .cellSetLeftTrap, .refl _⟩
    | cellSetRight hv hs2 =>
      have hnd2 : NoDivZero Δ Φ _ σ := fun σ'' h => hnd σ'' (steps_lift_ctx (.cellSet _) (.cellSetRight hv) (.cellSetRightTrap hv) h)
      rcases assertEq_step_fwd hIntr (.refl _) hnd2 hs2 with ⟨e2', hs2', heq'⟩
      exact ⟨_, .cellSetRight hv hs2', .cellSetRight hv heq'⟩
    | cellSetRightTrap hv => exact ⟨_, .cellSetRightTrap hv, .refl _⟩
    | cellSetVal hl hv => exact ⟨_, .cellSetVal hl hv, .refl _⟩
    | spawnStep hs1 =>
      have hnd1 : NoDivZero Δ Φ _ σ := fun σ'' h => hnd σ'' (steps_lift_ctx .spawn .spawnStep .spawnTrap h)
      rcases assertEq_step_fwd hIntr (.refl _) hnd1 hs1 with ⟨e2', hs2, heq'⟩
      exact ⟨_, .spawnStep hs2, .spawn heq'⟩
    | spawnTrap => exact ⟨_, .spawnTrap, .refl _⟩
    | awaitStep hs1 =>
      have hnd1 : NoDivZero Δ Φ _ σ := fun σ'' h => hnd σ'' (steps_lift_ctx .await .awaitStep .awaitTrap h)
      rcases assertEq_step_fwd hIntr (.refl _) hnd1 hs1 with ⟨e2', hs2, heq'⟩
      exact ⟨_, .awaitStep hs2, .await heq'⟩
    | awaitTrap => exact ⟨_, .awaitTrap, .refl _⟩
    | awaitVal h hv => exact ⟨_, .awaitVal h hv, .refl _⟩
    | awaitTaskTrap h => exact ⟨_, .awaitTaskTrap h, .refl _⟩
    | concPrimArgs hsl =>
      rcases assertEqList_step_fwd hIntr (.refl _)
        (noDivZeroList_of_ctx (.concPrim _) .concPrimArgs .concPrimTrap hnd) hsl with ⟨a', hsl', heql⟩
      exact ⟨_, .concPrimArgs hsl', .concPrim heql⟩
    | concPrimTrap hft => exact ⟨_, .concPrimTrap hft, .refl _⟩
    | concPrimVal h => exact ⟨_, .concPrimVal h, .refl _⟩
  | assertIf hv =>
    cases hs with
    | ifStep hs1 => exact False.elim (value_no_step hv hs1)
    | ifTrap => cases hv
    | ifTrue => exact ⟨.lit .unit, .ifTrue, .refl _⟩
    | ifFalse => exact False.elim (hnd σ (.trans .ifFalse (.refl _ _)))
  | tuple hl =>
    cases hs with
    | tupleStep hsl =>
      rcases assertEqList_step_fwd hIntr hl
        (noDivZeroList_of_ctx .tuple .tupleStep .tupleTrap hnd) hsl with ⟨es', hsl', heql⟩
      exact ⟨_, .tupleStep hsl', .tuple heql⟩
    | tupleTrap hft => exact ⟨_, .tupleTrap (assertEqList_firstTrap_left hl hft), .refl _⟩
  | blockCons he =>
    cases hs with
    | blockConsStep hs1 =>
      have hnd1 : NoDivZero Δ Φ _ σ := fun σ'' h => hnd σ'' (steps_lift_ctx (fun x => .block (x :: _ :: _)) .blockConsStep .blockConsTrap h)
      rcases assertEq_step_fwd hIntr he hnd1 hs1 with ⟨e2', hs2, heq'⟩
      exact ⟨_, .blockConsStep hs2, .blockCons heq'⟩
    | blockConsVal hv => rw [← assertEq_eq_of_val_left he hv]; exact ⟨_, .blockConsVal hv, .refl _⟩
    | blockConsTrap => rw [assertEq_trap_left he rfl]; exact ⟨_, .blockConsTrap, .refl _⟩
  | applyFn he =>
    cases hs with
    | applyFn hs1 =>
      have hnd1 : NoDivZero Δ Φ _ σ := fun σ'' h => hnd σ'' (steps_lift_ctx (fun x => .apply x _) .applyFn .applyFnTrap h)
      rcases assertEq_step_fwd hIntr he hnd1 hs1 with ⟨f2', hs2, heq'⟩
      exact ⟨_, .applyFn hs2, .applyFn heq'⟩
    | applyFnTrap => rw [assertEq_trap_left he rfl]; exact ⟨_, .applyFnTrap, .refl _⟩
    | applyArgs hv hsl =>
      rw [← assertEq_eq_of_val_left he hv]
      rcases assertEqList_step_fwd hIntr (.refl _)
        (noDivZeroList_of_ctx (.apply _) (.applyArgs hv) (.applyArgsTrap hv) hnd) hsl with ⟨a', hsl', heql⟩
      exact ⟨_, .applyArgs hv hsl', .applyArgs hv heql⟩
    | applyArgsTrap hv hft => rw [← assertEq_eq_of_val_left he hv]; exact ⟨_, .applyArgsTrap hv hft, .refl _⟩
    | applyBeta hvs hlen =>
      rw [← assertEq_eq_of_val_left he (.lam _ _ _ _)]
      exact ⟨_, .applyBeta hvs hlen, .refl _⟩
  | applyArgs hv hl =>
    cases hs with
    | applyFn hs1 => exact False.elim (value_no_step hv hs1)
    | applyFnTrap => cases hv
    | applyArgs _ hsl =>
      rcases assertEqList_step_fwd hIntr hl
        (noDivZeroList_of_ctx (.apply _) (.applyArgs hv) (.applyArgsTrap hv) hnd) hsl with ⟨a', hsl', heql⟩
      exact ⟨_, .applyArgs hv hsl', .applyArgs hv heql⟩
    | applyArgsTrap _ hft => exact ⟨_, .applyArgsTrap hv (assertEqList_firstTrap_left hl hft), .refl _⟩
    | applyBeta hvs hlen =>
      rw [← assertEqList_eq_of_vals_left hl hvs]
      exact ⟨_, .applyBeta hvs hlen, .refl _⟩
  | applyDirArgs hl =>
    cases hs with
    | applyDirArgs hsl =>
      rcases assertEqList_step_fwd hIntr hl
        (noDivZeroList_of_ctx (.applyDir _) .applyDirArgs .applyDirTrap hnd) hsl with ⟨a', hsl', heql⟩
      exact ⟨_, .applyDirArgs hsl', .applyDirArgs heql⟩
    | applyDirTrap hft => exact ⟨_, .applyDirTrap (assertEqList_firstTrap_left hl hft), .refl _⟩
    | applyDirBeta hΦ hvs hlen =>
      rw [← assertEqList_eq_of_vals_left hl hvs]
      exact applyDirBeta_fwd hIntr hΦ hvs hlen
  | un he =>
    cases hs with
    | unStep hs1 =>
      have hnd1 : NoDivZero Δ Φ _ σ := fun σ'' h => hnd σ'' (steps_lift_ctx (.un _) .unStep .unTrap h)
      rcases assertEq_step_fwd hIntr he hnd1 hs1 with ⟨e2', hs2, heq'⟩
      exact ⟨_, .unStep hs2, .un heq'⟩
    | unTrap => rw [assertEq_trap_left he rfl]; exact ⟨_, .unTrap, .refl _⟩
    | unVal h => rw [← assertEq_eq_of_val_left he (.lit _)]; exact ⟨_, .unVal h, .refl _⟩
  | binLeft he =>
    cases hs with
    | binLeft hs1 =>
      have hnd1 : NoDivZero Δ Φ _ σ := fun σ'' h => hnd σ'' (steps_lift_ctx (fun x => .bin _ x _) .binLeft .binLeftTrap h)
      rcases assertEq_step_fwd hIntr he hnd1 hs1 with ⟨e2', hs2, heq'⟩
      exact ⟨_, .binLeft hs2, .binLeft heq'⟩
    | binLeftTrap => rw [assertEq_trap_left he rfl]; exact ⟨_, .binLeftTrap, .refl _⟩
    | binAndFalse => rw [← assertEq_eq_of_val_left he (.lit _)]; exact ⟨_, .binAndFalse, .refl _⟩
    | binAndTrue => rw [← assertEq_eq_of_val_left he (.lit _)]; exact ⟨_, .binAndTrue, .refl _⟩
    | binOrTrue => rw [← assertEq_eq_of_val_left he (.lit _)]; exact ⟨_, .binOrTrue, .refl _⟩
    | binOrFalse => rw [← assertEq_eq_of_val_left he (.lit _)]; exact ⟨_, .binOrFalse, .refl _⟩
    | binRight h1 h2 hv hs2 =>
      rw [← assertEq_eq_of_val_left he hv]
      have hnd2 : NoDivZero Δ Φ _ σ := fun σ'' h => hnd σ'' (steps_lift_ctx (.bin _ _) (.binRight h1 h2 hv) (.binRightTrap h1 h2 hv) h)
      rcases assertEq_step_fwd hIntr (.refl _) hnd2 hs2 with ⟨e2', hs2', heq'⟩
      exact ⟨_, .binRight h1 h2 hv hs2', .binRight h1 h2 hv heq'⟩
    | binRightTrap h1 h2 hv =>
      rw [← assertEq_eq_of_val_left he hv]
      exact ⟨_, .binRightTrap h1 h2 hv, .refl _⟩
    | binVal h => rw [← assertEq_eq_of_val_left he (.lit _)]; exact binVal_fwd h
    | binTrap h => rw [← assertEq_eq_of_val_left he (.lit _)]; exact binTrap_fwd hnd h
  | binRight h1 h2 hv he =>
    cases hs with
    | binLeft hs1 => exact False.elim (value_no_step hv hs1)
    | binLeftTrap => cases hv
    | binAndFalse => exact False.elim (h1 rfl)
    | binAndTrue => exact False.elim (h1 rfl)
    | binOrTrue => exact False.elim (h2 rfl)
    | binOrFalse => exact False.elim (h2 rfl)
    | binRight _ _ _ hs2 =>
      have hnd2 : NoDivZero Δ Φ _ σ := fun σ'' h => hnd σ'' (steps_lift_ctx (.bin _ _) (.binRight h1 h2 hv) (.binRightTrap h1 h2 hv) h)
      rcases assertEq_step_fwd hIntr he hnd2 hs2 with ⟨e2', hs2', heq'⟩
      exact ⟨_, .binRight h1 h2 hv hs2', .binRight h1 h2 hv heq'⟩
    | binRightTrap _ _ _ => rw [assertEq_trap_left he rfl]; exact ⟨_, .binRightTrap h1 h2 hv, .refl _⟩
    | binVal h => rw [← assertEq_eq_of_val_left he (.lit _)]; exact binVal_fwd h
    | binTrap h => rw [← assertEq_eq_of_val_left he (.lit _)]; exact binTrap_fwd hnd h
  | let_ he =>
    cases hs with
    | letStep hs1 =>
      have hnd1 : NoDivZero Δ Φ _ σ := fun σ'' h => hnd σ'' (steps_lift_ctx (fun x => .let_ _ x _) .letStep .letTrap h)
      rcases assertEq_step_fwd hIntr he hnd1 hs1 with ⟨e2', hs2, heq'⟩
      exact ⟨_, .letStep hs2, .let_ heq'⟩
    | letTrap => rw [assertEq_trap_left he rfl]; exact ⟨_, .letTrap, .refl _⟩
    | letVal hv => rw [← assertEq_eq_of_val_left he hv]; exact ⟨_, .letVal hv, .refl _⟩
  | if_ he =>
    cases hs with
    | ifStep hs1 =>
      have hnd1 : NoDivZero Δ Φ _ σ := fun σ'' h => hnd σ'' (steps_lift_ctx (fun x => .if_ x _ _) .ifStep .ifTrap h)
      rcases assertEq_step_fwd hIntr he hnd1 hs1 with ⟨c2', hs2, heq'⟩
      exact ⟨_, .ifStep hs2, .if_ heq'⟩
    | ifTrap => rw [assertEq_trap_left he rfl]; exact ⟨_, .ifTrap, .refl _⟩
    | ifTrue => rw [← assertEq_eq_of_val_left he (.lit _)]; exact ⟨_, .ifTrue, .refl _⟩
    | ifFalse => rw [← assertEq_eq_of_val_left he (.lit _)]; exact ⟨_, .ifFalse, .refl _⟩
  | match_ he =>
    cases hs with
    | matchScrut hs1 =>
      have hnd1 : NoDivZero Δ Φ _ σ := fun σ'' h => hnd σ'' (steps_lift_ctx (fun x => .match_ x _) .matchScrut .matchScrutTrap h)
      rcases assertEq_step_fwd hIntr he hnd1 hs1 with ⟨s2', hs2, heq'⟩
      exact ⟨_, .matchScrut hs2, .match_ heq'⟩
    | matchScrutTrap => rw [assertEq_trap_left he rfl]; exact ⟨_, .matchScrutTrap, .refl _⟩
    | matchEmpty hv => rw [← assertEq_eq_of_val_left he hv]; exact ⟨_, .matchEmpty hv, .refl _⟩
    | matchHit hv hm => rw [← assertEq_eq_of_val_left he hv]; exact ⟨_, .matchHit hv hm, .refl _⟩
    | matchMiss hv hm => rw [← assertEq_eq_of_val_left he hv]; exact ⟨_, .matchMiss hv hm, .refl _⟩
  | makeData hl =>
    cases hs with
    | makeDataStep hsl =>
      rcases assertEqList_step_fwd hIntr hl
        (noDivZeroList_of_ctx (.makeData _ _) .makeDataStep .makeDataTrap hnd) hsl with ⟨es', hsl', heql⟩
      exact ⟨_, .makeDataStep hsl', .makeData heql⟩
    | makeDataTrap hft => exact ⟨_, .makeDataTrap (assertEqList_firstTrap_left hl hft), .refl _⟩
  | getTag he =>
    cases hs with
    | getTagStep hs1 =>
      have hnd1 : NoDivZero Δ Φ _ σ := fun σ'' h => hnd σ'' (steps_lift_ctx .getTag .getTagStep .getTagTrap h)
      rcases assertEq_step_fwd hIntr he hnd1 hs1 with ⟨e2', hs2, heq'⟩
      exact ⟨_, .getTagStep hs2, .getTag heq'⟩
    | getTagTrap => rw [assertEq_trap_left he rfl]; exact ⟨_, .getTagTrap, .refl _⟩
    | getTagVal hvs => rw [← assertEq_eq_of_val_left he (.makeData _ _ hvs)]; exact ⟨_, .getTagVal hvs, .refl _⟩
  | cellNew he =>
    cases hs with
    | cellNewStep hs1 =>
      have hnd1 : NoDivZero Δ Φ _ σ := fun σ'' h => hnd σ'' (steps_lift_ctx .cellNew .cellNewStep .cellNewTrap h)
      rcases assertEq_step_fwd hIntr he hnd1 hs1 with ⟨e2', hs2, heq'⟩
      exact ⟨_, .cellNewStep hs2, .cellNew heq'⟩
    | cellNewTrap => rw [assertEq_trap_left he rfl]; exact ⟨_, .cellNewTrap, .refl _⟩
    | cellNewVal hv => rw [← assertEq_eq_of_val_left he hv]; exact ⟨_, .cellNewVal hv, .refl _⟩
  | cellGet he =>
    cases hs with
    | cellGetStep hs1 =>
      have hnd1 : NoDivZero Δ Φ _ σ := fun σ'' h => hnd σ'' (steps_lift_ctx .cellGet .cellGetStep .cellGetTrap h)
      rcases assertEq_step_fwd hIntr he hnd1 hs1 with ⟨e2', hs2, heq'⟩
      exact ⟨_, .cellGetStep hs2, .cellGet heq'⟩
    | cellGetTrap => rw [assertEq_trap_left he rfl]; exact ⟨_, .cellGetTrap, .refl _⟩
    | cellGetVal h => rw [← assertEq_eq_of_val_left he (.loc _)]; exact ⟨_, .cellGetVal h, .refl _⟩
  | cellSetLeft he =>
    cases hs with
    | cellSetLeft hs1 =>
      have hnd1 : NoDivZero Δ Φ _ σ := fun σ'' h => hnd σ'' (steps_lift_ctx (fun x => .cellSet x _) .cellSetLeft .cellSetLeftTrap h)
      rcases assertEq_step_fwd hIntr he hnd1 hs1 with ⟨e2', hs2, heq'⟩
      exact ⟨_, .cellSetLeft hs2, .cellSetLeft heq'⟩
    | cellSetLeftTrap => rw [assertEq_trap_left he rfl]; exact ⟨_, .cellSetLeftTrap, .refl _⟩
    | cellSetRight hv hs2 =>
      rw [← assertEq_eq_of_val_left he hv]
      have hnd2 : NoDivZero Δ Φ _ σ := fun σ'' h => hnd σ'' (steps_lift_ctx (.cellSet _) (.cellSetRight hv) (.cellSetRightTrap hv) h)
      rcases assertEq_step_fwd hIntr (.refl _) hnd2 hs2 with ⟨e2', hs2', heq'⟩
      exact ⟨_, .cellSetRight hv hs2', .cellSetRight hv heq'⟩
    | cellSetRightTrap hv => rw [← assertEq_eq_of_val_left he hv]; exact ⟨_, .cellSetRightTrap hv, .refl _⟩
    | cellSetVal hl hv => rw [← assertEq_eq_of_val_left he (.loc _)]; exact ⟨_, .cellSetVal hl hv, .refl _⟩
  | cellSetRight hv he =>
    cases hs with
    | cellSetLeft hs1 => exact False.elim (value_no_step hv hs1)
    | cellSetLeftTrap => cases hv
    | cellSetRight _ hs2 =>
      have hnd2 : NoDivZero Δ Φ _ σ := fun σ'' h => hnd σ'' (steps_lift_ctx (.cellSet _) (.cellSetRight hv) (.cellSetRightTrap hv) h)
      rcases assertEq_step_fwd hIntr he hnd2 hs2 with ⟨e2', hs2', heq'⟩
      exact ⟨_, .cellSetRight hv hs2', .cellSetRight hv heq'⟩
    | cellSetRightTrap _ => rw [assertEq_trap_left he rfl]; exact ⟨_, .cellSetRightTrap hv, .refl _⟩
    | cellSetVal hl hv2 => rw [← assertEq_eq_of_val_left he hv2]; exact ⟨_, .cellSetVal hl hv2, .refl _⟩
  | spawn he =>
    cases hs with
    | spawnStep hs1 =>
      have hnd1 : NoDivZero Δ Φ _ σ := fun σ'' h => hnd σ'' (steps_lift_ctx .spawn .spawnStep .spawnTrap h)
      rcases assertEq_step_fwd hIntr he hnd1 hs1 with ⟨e2', hs2, heq'⟩
      exact ⟨_, .spawnStep hs2, .spawn heq'⟩
    | spawnTrap => rw [assertEq_trap_left he rfl]; exact ⟨_, .spawnTrap, .refl _⟩
  | await he =>
    cases hs with
    | awaitStep hs1 =>
      have hnd1 : NoDivZero Δ Φ _ σ := fun σ'' h => hnd σ'' (steps_lift_ctx .await .awaitStep .awaitTrap h)
      rcases assertEq_step_fwd hIntr he hnd1 hs1 with ⟨e2', hs2, heq'⟩
      exact ⟨_, .awaitStep hs2, .await heq'⟩
    | awaitTrap => rw [assertEq_trap_left he rfl]; exact ⟨_, .awaitTrap, .refl _⟩
    | awaitVal h hv => rw [← assertEq_eq_of_val_left he (.taskRef _)]; exact ⟨_, .awaitVal h hv, .refl _⟩
    | awaitTaskTrap h => rw [← assertEq_eq_of_val_left he (.taskRef _)]; exact ⟨_, .awaitTaskTrap h, .refl _⟩
  | concPrim hl =>
    cases hs with
    | concPrimArgs hsl =>
      rcases assertEqList_step_fwd hIntr hl
        (noDivZeroList_of_ctx (.concPrim _) .concPrimArgs .concPrimTrap hnd) hsl with ⟨a', hsl', heql⟩
      exact ⟨_, .concPrimArgs hsl', .concPrim heql⟩
    | concPrimTrap hft => exact ⟨_, .concPrimTrap (assertEqList_firstTrap_left hl hft), .refl _⟩
    | concPrimVal h =>
      cases h with
      | chanSendClosed hch _ _ => simp [emptyPool] at hch
      | chanRecvClosed hch _ _ => simp [emptyPool] at hch
termination_by sizeOf e1

private theorem assertEqList_step_fwd {Δ : AdtEnv} {Φ : FunEnv} (hIntr : IntrinsicsOk Φ)
    {es1 es2 es1' : List Expr} {σ σ' : Store}
    (heql : AssertEqList es1 es2) (hnd : NoDivZeroList Δ Φ es1 σ)
    (hsl : StepList Δ Φ emptyPool es1 σ es1' σ' .none) :
    ∃ es2', StepListUnchecked Δ Φ es2 σ es2' σ' ∧ AssertEqList es1' es2' := by
  cases heql with
  | refl =>
    cases hsl with
    | head hs1 =>
      rcases assertEq_step_fwd hIntr (.refl _) (noDivZeroList_head hnd) hs1 with ⟨e2', hs2, heq'⟩
      exact ⟨_, .head hs2, .head heq'⟩
    | tail hv hsl1 =>
      rcases assertEqList_step_fwd hIntr (.refl _) (noDivZeroList_tail hv hnd) hsl1 with ⟨es2', hsl2, heql'⟩
      exact ⟨_, .tail hv hsl2, .tail hv heql'⟩
  | head he =>
    cases hsl with
    | head hs1 =>
      rcases assertEq_step_fwd hIntr he (noDivZeroList_head hnd) hs1 with ⟨e2', hs2, heq'⟩
      exact ⟨_, .head hs2, .head heq'⟩
    | tail hv hsl1 =>
      rw [← assertEq_eq_of_val_left he hv]
      rcases assertEqList_step_fwd hIntr (.refl _) (noDivZeroList_tail hv hnd) hsl1 with ⟨es2', hsl2, heql'⟩
      exact ⟨_, .tail hv hsl2, .tail hv heql'⟩
  | tail hv hl =>
    cases hsl with
    | head hs1 => exact False.elim (value_no_step hv hs1)
    | tail _ hsl1 =>
      rcases assertEqList_step_fwd hIntr hl (noDivZeroList_tail hv hnd) hsl1 with ⟨es2', hsl2, heql'⟩
      exact ⟨_, .tail hv hsl2, .tail hv heql'⟩
termination_by sizeOf es1
end

/- Backward 1-step simulation: any step under `elideVerifiedAsserts Φ` from a state `AssertEq`-related
   to a `NoDivZero` original state `e1` is matched by a step under `Φ` preserving `AssertEq`. -/
mutual
private theorem assertEq_step_bwd {Δ : AdtEnv} {Φ : FunEnv} (hIntr : IntrinsicsOk Φ)
    {e1 e2 e2' : Expr} {σ σ' : Store}
    (heq : AssertEq e1 e2) (hnd : NoDivZero Δ Φ e1 σ)
    (hs : StepUnchecked Δ Φ e2 σ e2' σ') :
    ∃ e1', Step Δ Φ emptyPool e1 σ e1' σ' .none ∧ AssertEq e1' e2' := by
  cases heq with
  | refl =>
    cases hs with
    | tupleStep hsl =>
      rcases assertEqList_step_bwd hIntr (.refl _)
        (noDivZeroList_of_ctx .tuple .tupleStep .tupleTrap hnd) hsl with ⟨es', hsl', heql⟩
      exact ⟨.tuple es', .tupleStep hsl', .tuple heql⟩
    | tupleTrap hft => exact ⟨_, .tupleTrap hft, .refl _⟩
    | blockEmpty => exact ⟨_, .blockEmpty, .refl _⟩
    | blockSingle => exact ⟨_, .blockSingle, .refl _⟩
    | blockConsStep hs1 =>
      have hnd1 : NoDivZero Δ Φ _ σ := fun σ'' h => hnd σ'' (steps_lift_ctx (fun x => .block (x :: _ :: _)) .blockConsStep .blockConsTrap h)
      rcases assertEq_step_bwd hIntr (.refl _) hnd1 hs1 with ⟨e1', hs1', heq'⟩
      exact ⟨_, .blockConsStep hs1', .blockCons heq'⟩
    | blockConsVal hv => exact ⟨_, .blockConsVal hv, .refl _⟩
    | blockConsTrap => exact ⟨_, .blockConsTrap, .refl _⟩
    | applyFn hs1 =>
      have hnd1 : NoDivZero Δ Φ _ σ := fun σ'' h => hnd σ'' (steps_lift_ctx (fun x => .apply x _) .applyFn .applyFnTrap h)
      rcases assertEq_step_bwd hIntr (.refl _) hnd1 hs1 with ⟨f1', hs1', heq'⟩
      exact ⟨_, .applyFn hs1', .applyFn heq'⟩
    | applyFnTrap => exact ⟨_, .applyFnTrap, .refl _⟩
    | applyArgs hv hsl =>
      rcases assertEqList_step_bwd hIntr (.refl _)
        (noDivZeroList_of_ctx (.apply _) (.applyArgs hv) (.applyArgsTrap hv) hnd) hsl with ⟨a', hsl', heql⟩
      exact ⟨_, .applyArgs hv hsl', .applyArgs hv heql⟩
    | applyArgsTrap hv hft => exact ⟨_, .applyArgsTrap hv hft, .refl _⟩
    | applyBeta hvs hlen => exact ⟨_, .applyBeta hvs hlen, .refl _⟩
    | applyDirArgs hsl =>
      rcases assertEqList_step_bwd hIntr (.refl _)
        (noDivZeroList_of_ctx (.applyDir _) .applyDirArgs .applyDirTrap hnd) hsl with ⟨a', hsl', heql⟩
      exact ⟨_, .applyDirArgs hsl', .applyDirArgs heql⟩
    | applyDirTrap hft => exact ⟨_, .applyDirTrap hft, .refl _⟩
    | @applyDirBeta nm fd args _ hΦ hvs hlen =>
      by_cases hnm : nm = "assert"
      · subst hnm
        simp [elideVerifiedAsserts] at hΦ; subst hΦ
        cases args with
        | nil => simp [assertElidedFunDef] at hlen
        | cons v rest =>
          cases rest with
          | cons _ _ => simp [assertElidedFunDef] at hlen
          | nil =>
            have hv : IsValue v := hvs v (List.mem_cons_self ..)
            refine ⟨substMany (zipParams assertFunDef.params [v]) assertFunDef.body,
              .applyDirBeta hIntr.1 hvs rfl, ?_⟩
            simp only [assertFunDef, assertElidedFunDef, zipParams]
            exact .assertIf hv
      · simp [elideVerifiedAsserts, hnm] at hΦ
        exact ⟨_, .applyDirBeta hΦ hvs hlen, .refl _⟩
    | unStep hs1 =>
      have hnd1 : NoDivZero Δ Φ _ σ := fun σ'' h => hnd σ'' (steps_lift_ctx (.un _) .unStep .unTrap h)
      rcases assertEq_step_bwd hIntr (.refl _) hnd1 hs1 with ⟨e1', hs1', heq'⟩
      exact ⟨_, .unStep hs1', .un heq'⟩
    | unTrap => exact ⟨_, .unTrap, .refl _⟩
    | unVal h => exact ⟨_, .unVal h, .refl _⟩
    | binLeft hs1 =>
      have hnd1 : NoDivZero Δ Φ _ σ := fun σ'' h => hnd σ'' (steps_lift_ctx (fun x => .bin _ x _) .binLeft .binLeftTrap h)
      rcases assertEq_step_bwd hIntr (.refl _) hnd1 hs1 with ⟨e1', hs1', heq'⟩
      exact ⟨_, .binLeft hs1', .binLeft heq'⟩
    | binLeftTrap => exact ⟨_, .binLeftTrap, .refl _⟩
    | binAndFalse => exact ⟨_, .binAndFalse, .refl _⟩
    | binAndTrue => exact ⟨_, .binAndTrue, .refl _⟩
    | binOrTrue => exact ⟨_, .binOrTrue, .refl _⟩
    | binOrFalse => exact ⟨_, .binOrFalse, .refl _⟩
    | binRight h1 h2 hv hs2 =>
      have hnd2 : NoDivZero Δ Φ _ σ := fun σ'' h => hnd σ'' (steps_lift_ctx (.bin _ _) (.binRight h1 h2 hv) (.binRightTrap h1 h2 hv) h)
      rcases assertEq_step_bwd hIntr (.refl _) hnd2 hs2 with ⟨e1', hs1', heq'⟩
      exact ⟨_, .binRight h1 h2 hv hs1', .binRight h1 h2 hv heq'⟩
    | binRightTrap h1 h2 hv => exact ⟨_, .binRightTrap h1 h2 hv, .refl _⟩
    | binVal h => exact binVal_bwd hnd h
    | binTrap h _ => exact ⟨_, .binTrap h, .refl _⟩
    | letStep hs1 =>
      have hnd1 : NoDivZero Δ Φ _ σ := fun σ'' h => hnd σ'' (steps_lift_ctx (fun x => .let_ _ x _) .letStep .letTrap h)
      rcases assertEq_step_bwd hIntr (.refl _) hnd1 hs1 with ⟨e1', hs1', heq'⟩
      exact ⟨_, .letStep hs1', .let_ heq'⟩
    | letTrap => exact ⟨_, .letTrap, .refl _⟩
    | letVal hv => exact ⟨_, .letVal hv, .refl _⟩
    | ifStep hs1 =>
      have hnd1 : NoDivZero Δ Φ _ σ := fun σ'' h => hnd σ'' (steps_lift_ctx (fun x => .if_ x _ _) .ifStep .ifTrap h)
      rcases assertEq_step_bwd hIntr (.refl _) hnd1 hs1 with ⟨c1', hs1', heq'⟩
      exact ⟨_, .ifStep hs1', .if_ heq'⟩
    | ifTrap => exact ⟨_, .ifTrap, .refl _⟩
    | ifTrue => exact ⟨_, .ifTrue, .refl _⟩
    | ifFalse => exact ⟨_, .ifFalse, .refl _⟩
    | whileUnfold => exact ⟨_, .whileUnfold, .refl _⟩
    | matchScrut hs1 =>
      have hnd1 : NoDivZero Δ Φ _ σ := fun σ'' h => hnd σ'' (steps_lift_ctx (fun x => .match_ x _) .matchScrut .matchScrutTrap h)
      rcases assertEq_step_bwd hIntr (.refl _) hnd1 hs1 with ⟨s1', hs1', heq'⟩
      exact ⟨_, .matchScrut hs1', .match_ heq'⟩
    | matchScrutTrap => exact ⟨_, .matchScrutTrap, .refl _⟩
    | matchEmpty hv => exact ⟨_, .matchEmpty hv, .refl _⟩
    | matchHit hv hm => exact ⟨_, .matchHit hv hm, .refl _⟩
    | matchMiss hv hm => exact ⟨_, .matchMiss hv hm, .refl _⟩
    | makeDataStep hsl =>
      rcases assertEqList_step_bwd hIntr (.refl _)
        (noDivZeroList_of_ctx (.makeData _ _) .makeDataStep .makeDataTrap hnd) hsl with ⟨es', hsl', heql⟩
      exact ⟨_, .makeDataStep hsl', .makeData heql⟩
    | makeDataTrap hft => exact ⟨_, .makeDataTrap hft, .refl _⟩
    | getTagStep hs1 =>
      have hnd1 : NoDivZero Δ Φ _ σ := fun σ'' h => hnd σ'' (steps_lift_ctx .getTag .getTagStep .getTagTrap h)
      rcases assertEq_step_bwd hIntr (.refl _) hnd1 hs1 with ⟨e1', hs1', heq'⟩
      exact ⟨_, .getTagStep hs1', .getTag heq'⟩
    | getTagTrap => exact ⟨_, .getTagTrap, .refl _⟩
    | getTagVal hvs => exact ⟨_, .getTagVal hvs, .refl _⟩
    | cellNewStep hs1 =>
      have hnd1 : NoDivZero Δ Φ _ σ := fun σ'' h => hnd σ'' (steps_lift_ctx .cellNew .cellNewStep .cellNewTrap h)
      rcases assertEq_step_bwd hIntr (.refl _) hnd1 hs1 with ⟨e1', hs1', heq'⟩
      exact ⟨_, .cellNewStep hs1', .cellNew heq'⟩
    | cellNewTrap => exact ⟨_, .cellNewTrap, .refl _⟩
    | cellNewVal hv => exact ⟨_, .cellNewVal hv, .refl _⟩
    | cellGetStep hs1 =>
      have hnd1 : NoDivZero Δ Φ _ σ := fun σ'' h => hnd σ'' (steps_lift_ctx .cellGet .cellGetStep .cellGetTrap h)
      rcases assertEq_step_bwd hIntr (.refl _) hnd1 hs1 with ⟨e1', hs1', heq'⟩
      exact ⟨_, .cellGetStep hs1', .cellGet heq'⟩
    | cellGetTrap => exact ⟨_, .cellGetTrap, .refl _⟩
    | cellGetVal h => exact ⟨_, .cellGetVal h, .refl _⟩
    | cellSetLeft hs1 =>
      have hnd1 : NoDivZero Δ Φ _ σ := fun σ'' h => hnd σ'' (steps_lift_ctx (fun x => .cellSet x _) .cellSetLeft .cellSetLeftTrap h)
      rcases assertEq_step_bwd hIntr (.refl _) hnd1 hs1 with ⟨e1', hs1', heq'⟩
      exact ⟨_, .cellSetLeft hs1', .cellSetLeft heq'⟩
    | cellSetLeftTrap => exact ⟨_, .cellSetLeftTrap, .refl _⟩
    | cellSetRight hv hs2 =>
      have hnd2 : NoDivZero Δ Φ _ σ := fun σ'' h => hnd σ'' (steps_lift_ctx (.cellSet _) (.cellSetRight hv) (.cellSetRightTrap hv) h)
      rcases assertEq_step_bwd hIntr (.refl _) hnd2 hs2 with ⟨e1', hs1', heq'⟩
      exact ⟨_, .cellSetRight hv hs1', .cellSetRight hv heq'⟩
    | cellSetRightTrap hv => exact ⟨_, .cellSetRightTrap hv, .refl _⟩
    | cellSetVal hl hv => exact ⟨_, .cellSetVal hl hv, .refl _⟩
    | spawnStep hs1 =>
      have hnd1 : NoDivZero Δ Φ _ σ := fun σ'' h => hnd σ'' (steps_lift_ctx .spawn .spawnStep .spawnTrap h)
      rcases assertEq_step_bwd hIntr (.refl _) hnd1 hs1 with ⟨e1', hs1', heq'⟩
      exact ⟨_, .spawnStep hs1', .spawn heq'⟩
    | spawnTrap => exact ⟨_, .spawnTrap, .refl _⟩
    | awaitStep hs1 =>
      have hnd1 : NoDivZero Δ Φ _ σ := fun σ'' h => hnd σ'' (steps_lift_ctx .await .awaitStep .awaitTrap h)
      rcases assertEq_step_bwd hIntr (.refl _) hnd1 hs1 with ⟨e1', hs1', heq'⟩
      exact ⟨_, .awaitStep hs1', .await heq'⟩
    | awaitTrap => exact ⟨_, .awaitTrap, .refl _⟩
    | awaitVal h hv => exact ⟨_, .awaitVal h hv, .refl _⟩
    | awaitTaskTrap h => exact ⟨_, .awaitTaskTrap h, .refl _⟩
    | concPrimArgs hsl =>
      rcases assertEqList_step_bwd hIntr (.refl _)
        (noDivZeroList_of_ctx (.concPrim _) .concPrimArgs .concPrimTrap hnd) hsl with ⟨a', hsl', heql⟩
      exact ⟨_, .concPrimArgs hsl', .concPrim heql⟩
    | concPrimTrap hft => exact ⟨_, .concPrimTrap hft, .refl _⟩
    | concPrimVal h => exact ⟨_, .concPrimVal h, .refl _⟩
  | assertIf hv =>
    cases hs with
    | ifStep hs1 => exact False.elim (value_no_stepUnchecked hv hs1)
    | ifTrap => cases hv
    | ifTrue => exact ⟨.lit .unit, .ifTrue, .refl _⟩
    | ifFalse => exact False.elim (hnd σ (.trans .ifFalse (.refl _ _)))
  | tuple hl =>
    cases hs with
    | tupleStep hsl =>
      rcases assertEqList_step_bwd hIntr hl
        (noDivZeroList_of_ctx .tuple .tupleStep .tupleTrap hnd) hsl with ⟨es', hsl', heql⟩
      exact ⟨_, .tupleStep hsl', .tuple heql⟩
    | tupleTrap hft => exact ⟨_, .tupleTrap (assertEqList_firstTrap_right hl hft), .refl _⟩
  | blockCons he =>
    cases hs with
    | blockConsStep hs1 =>
      have hnd1 : NoDivZero Δ Φ _ σ := fun σ'' h => hnd σ'' (steps_lift_ctx (fun x => .block (x :: _ :: _)) .blockConsStep .blockConsTrap h)
      rcases assertEq_step_bwd hIntr he hnd1 hs1 with ⟨e1', hs1', heq'⟩
      exact ⟨_, .blockConsStep hs1', .blockCons heq'⟩
    | blockConsVal hv => rw [assertEq_eq_of_val_right he hv]; exact ⟨_, .blockConsVal hv, .refl _⟩
    | blockConsTrap => rw [assertEq_trap_right he rfl]; exact ⟨_, .blockConsTrap, .refl _⟩
  | applyFn he =>
    cases hs with
    | applyFn hs1 =>
      have hnd1 : NoDivZero Δ Φ _ σ := fun σ'' h => hnd σ'' (steps_lift_ctx (fun x => .apply x _) .applyFn .applyFnTrap h)
      rcases assertEq_step_bwd hIntr he hnd1 hs1 with ⟨f1', hs1', heq'⟩
      exact ⟨_, .applyFn hs1', .applyFn heq'⟩
    | applyFnTrap => rw [assertEq_trap_right he rfl]; exact ⟨_, .applyFnTrap, .refl _⟩
    | applyArgs hv hsl =>
      have hEq := assertEq_eq_of_val_right he hv
      rw [hEq]
      rcases assertEqList_step_bwd hIntr (.refl _)
        (noDivZeroList_of_ctx (.apply _) (.applyArgs hv) (.applyArgsTrap hv) (hEq ▸ hnd)) hsl with ⟨a', hsl', heql⟩
      exact ⟨_, .applyArgs hv hsl', .applyArgs hv heql⟩
    | applyArgsTrap hv hft => rw [assertEq_eq_of_val_right he hv]; exact ⟨_, .applyArgsTrap hv hft, .refl _⟩
    | applyBeta hvs hlen =>
      rw [assertEq_eq_of_val_right he (.lam _ _ _ _)]
      exact ⟨_, .applyBeta hvs hlen, .refl _⟩
  | applyArgs hv hl =>
    cases hs with
    | applyFn hs1 => exact False.elim (value_no_stepUnchecked hv hs1)
    | applyFnTrap => cases hv
    | applyArgs _ hsl =>
      rcases assertEqList_step_bwd hIntr hl
        (noDivZeroList_of_ctx (.apply _) (.applyArgs hv) (.applyArgsTrap hv) hnd) hsl with ⟨a', hsl', heql⟩
      exact ⟨_, .applyArgs hv hsl', .applyArgs hv heql⟩
    | applyArgsTrap _ hft => exact ⟨_, .applyArgsTrap hv (assertEqList_firstTrap_right hl hft), .refl _⟩
    | applyBeta hvs hlen =>
      rw [assertEqList_eq_of_vals_right hl hvs]
      exact ⟨_, .applyBeta hvs hlen, .refl _⟩
  | applyDirArgs hl =>
    cases hs with
    | applyDirArgs hsl =>
      rcases assertEqList_step_bwd hIntr hl
        (noDivZeroList_of_ctx (.applyDir _) .applyDirArgs .applyDirTrap hnd) hsl with ⟨a', hsl', heql⟩
      exact ⟨_, .applyDirArgs hsl', .applyDirArgs heql⟩
    | applyDirTrap hft => exact ⟨_, .applyDirTrap (assertEqList_firstTrap_right hl hft), .refl _⟩
    | applyDirBeta hΦ hvs hlen =>
      have hEq := assertEqList_eq_of_vals_right hl hvs
      rw [hEq]
      exact applyDirBeta_bwd hIntr hΦ hvs hlen
  | un he =>
    cases hs with
    | unStep hs1 =>
      have hnd1 : NoDivZero Δ Φ _ σ := fun σ'' h => hnd σ'' (steps_lift_ctx (.un _) .unStep .unTrap h)
      rcases assertEq_step_bwd hIntr he hnd1 hs1 with ⟨e1', hs1', heq'⟩
      exact ⟨_, .unStep hs1', .un heq'⟩
    | unTrap => rw [assertEq_trap_right he rfl]; exact ⟨_, .unTrap, .refl _⟩
    | unVal h => rw [assertEq_eq_of_val_right he (.lit _)]; exact ⟨_, .unVal h, .refl _⟩
  | binLeft he =>
    cases hs with
    | binLeft hs1 =>
      have hnd1 : NoDivZero Δ Φ _ σ := fun σ'' h => hnd σ'' (steps_lift_ctx (fun x => .bin _ x _) .binLeft .binLeftTrap h)
      rcases assertEq_step_bwd hIntr he hnd1 hs1 with ⟨e1', hs1', heq'⟩
      exact ⟨_, .binLeft hs1', .binLeft heq'⟩
    | binLeftTrap => rw [assertEq_trap_right he rfl]; exact ⟨_, .binLeftTrap, .refl _⟩
    | binAndFalse => rw [assertEq_eq_of_val_right he (.lit _)]; exact ⟨_, .binAndFalse, .refl _⟩
    | binAndTrue => rw [assertEq_eq_of_val_right he (.lit _)]; exact ⟨_, .binAndTrue, .refl _⟩
    | binOrTrue => rw [assertEq_eq_of_val_right he (.lit _)]; exact ⟨_, .binOrTrue, .refl _⟩
    | binOrFalse => rw [assertEq_eq_of_val_right he (.lit _)]; exact ⟨_, .binOrFalse, .refl _⟩
    | binRight h1 h2 hv hs2 =>
      have hEq := assertEq_eq_of_val_right he hv
      rw [hEq]
      have hnd2 : NoDivZero Δ Φ _ σ := fun σ'' h => (hEq ▸ hnd) σ'' (steps_lift_ctx (.bin _ _) (.binRight h1 h2 hv) (.binRightTrap h1 h2 hv) h)
      rcases assertEq_step_bwd hIntr (.refl _) hnd2 hs2 with ⟨e1', hs1', heq'⟩
      exact ⟨_, .binRight h1 h2 hv hs1', .binRight h1 h2 hv heq'⟩
    | binRightTrap h1 h2 hv =>
      rw [assertEq_eq_of_val_right he hv]
      exact ⟨_, .binRightTrap h1 h2 hv, .refl _⟩
    | binVal h => have hEq := assertEq_eq_of_val_right he (.lit _); rw [hEq]; exact binVal_bwd (hEq ▸ hnd) h
    | binTrap h _ => rw [assertEq_eq_of_val_right he (.lit _)]; exact ⟨_, .binTrap h, .refl _⟩
  | binRight h1 h2 hv he =>
    cases hs with
    | binLeft hs1 => exact False.elim (value_no_stepUnchecked hv hs1)
    | binLeftTrap => cases hv
    | binAndFalse => exact False.elim (h1 rfl)
    | binAndTrue => exact False.elim (h1 rfl)
    | binOrTrue => exact False.elim (h2 rfl)
    | binOrFalse => exact False.elim (h2 rfl)
    | binRight _ _ _ hs2 =>
      have hnd2 : NoDivZero Δ Φ _ σ := fun σ'' h => hnd σ'' (steps_lift_ctx (.bin _ _) (.binRight h1 h2 hv) (.binRightTrap h1 h2 hv) h)
      rcases assertEq_step_bwd hIntr he hnd2 hs2 with ⟨e1', hs1', heq'⟩
      exact ⟨_, .binRight h1 h2 hv hs1', .binRight h1 h2 hv heq'⟩
    | binRightTrap _ _ _ => rw [assertEq_trap_right he rfl]; exact ⟨_, .binRightTrap h1 h2 hv, .refl _⟩
    | binVal h => have hEq := assertEq_eq_of_val_right he (.lit _); rw [hEq]; exact binVal_bwd (hEq ▸ hnd) h
    | binTrap h _ => rw [assertEq_eq_of_val_right he (.lit _)]; exact ⟨_, .binTrap h, .refl _⟩
  | let_ he =>
    cases hs with
    | letStep hs1 =>
      have hnd1 : NoDivZero Δ Φ _ σ := fun σ'' h => hnd σ'' (steps_lift_ctx (fun x => .let_ _ x _) .letStep .letTrap h)
      rcases assertEq_step_bwd hIntr he hnd1 hs1 with ⟨e1', hs1', heq'⟩
      exact ⟨_, .letStep hs1', .let_ heq'⟩
    | letTrap => rw [assertEq_trap_right he rfl]; exact ⟨_, .letTrap, .refl _⟩
    | letVal hv => rw [assertEq_eq_of_val_right he hv]; exact ⟨_, .letVal hv, .refl _⟩
  | if_ he =>
    cases hs with
    | ifStep hs1 =>
      have hnd1 : NoDivZero Δ Φ _ σ := fun σ'' h => hnd σ'' (steps_lift_ctx (fun x => .if_ x _ _) .ifStep .ifTrap h)
      rcases assertEq_step_bwd hIntr he hnd1 hs1 with ⟨c1', hs1', heq'⟩
      exact ⟨_, .ifStep hs1', .if_ heq'⟩
    | ifTrap => rw [assertEq_trap_right he rfl]; exact ⟨_, .ifTrap, .refl _⟩
    | ifTrue => rw [assertEq_eq_of_val_right he (.lit _)]; exact ⟨_, .ifTrue, .refl _⟩
    | ifFalse => rw [assertEq_eq_of_val_right he (.lit _)]; exact ⟨_, .ifFalse, .refl _⟩
  | match_ he =>
    cases hs with
    | matchScrut hs1 =>
      have hnd1 : NoDivZero Δ Φ _ σ := fun σ'' h => hnd σ'' (steps_lift_ctx (fun x => .match_ x _) .matchScrut .matchScrutTrap h)
      rcases assertEq_step_bwd hIntr he hnd1 hs1 with ⟨s1', hs1', heq'⟩
      exact ⟨_, .matchScrut hs1', .match_ heq'⟩
    | matchScrutTrap => rw [assertEq_trap_right he rfl]; exact ⟨_, .matchScrutTrap, .refl _⟩
    | matchEmpty hv => rw [assertEq_eq_of_val_right he hv]; exact ⟨_, .matchEmpty hv, .refl _⟩
    | matchHit hv hm => rw [assertEq_eq_of_val_right he hv]; exact ⟨_, .matchHit hv hm, .refl _⟩
    | matchMiss hv hm => rw [assertEq_eq_of_val_right he hv]; exact ⟨_, .matchMiss hv hm, .refl _⟩
  | makeData hl =>
    cases hs with
    | makeDataStep hsl =>
      rcases assertEqList_step_bwd hIntr hl
        (noDivZeroList_of_ctx (.makeData _ _) .makeDataStep .makeDataTrap hnd) hsl with ⟨es', hsl', heql⟩
      exact ⟨_, .makeDataStep hsl', .makeData heql⟩
    | makeDataTrap hft => exact ⟨_, .makeDataTrap (assertEqList_firstTrap_right hl hft), .refl _⟩
  | getTag he =>
    cases hs with
    | getTagStep hs1 =>
      have hnd1 : NoDivZero Δ Φ _ σ := fun σ'' h => hnd σ'' (steps_lift_ctx .getTag .getTagStep .getTagTrap h)
      rcases assertEq_step_bwd hIntr he hnd1 hs1 with ⟨e1', hs1', heq'⟩
      exact ⟨_, .getTagStep hs1', .getTag heq'⟩
    | getTagTrap => rw [assertEq_trap_right he rfl]; exact ⟨_, .getTagTrap, .refl _⟩
    | getTagVal hvs => rw [assertEq_eq_of_val_right he (.makeData _ _ hvs)]; exact ⟨_, .getTagVal hvs, .refl _⟩
  | cellNew he =>
    cases hs with
    | cellNewStep hs1 =>
      have hnd1 : NoDivZero Δ Φ _ σ := fun σ'' h => hnd σ'' (steps_lift_ctx .cellNew .cellNewStep .cellNewTrap h)
      rcases assertEq_step_bwd hIntr he hnd1 hs1 with ⟨e1', hs1', heq'⟩
      exact ⟨_, .cellNewStep hs1', .cellNew heq'⟩
    | cellNewTrap => rw [assertEq_trap_right he rfl]; exact ⟨_, .cellNewTrap, .refl _⟩
    | cellNewVal hv => rw [assertEq_eq_of_val_right he hv]; exact ⟨_, .cellNewVal hv, .refl _⟩
  | cellGet he =>
    cases hs with
    | cellGetStep hs1 =>
      have hnd1 : NoDivZero Δ Φ _ σ := fun σ'' h => hnd σ'' (steps_lift_ctx .cellGet .cellGetStep .cellGetTrap h)
      rcases assertEq_step_bwd hIntr he hnd1 hs1 with ⟨e1', hs1', heq'⟩
      exact ⟨_, .cellGetStep hs1', .cellGet heq'⟩
    | cellGetTrap => rw [assertEq_trap_right he rfl]; exact ⟨_, .cellGetTrap, .refl _⟩
    | cellGetVal h => rw [assertEq_eq_of_val_right he (.loc _)]; exact ⟨_, .cellGetVal h, .refl _⟩
  | cellSetLeft he =>
    cases hs with
    | cellSetLeft hs1 =>
      have hnd1 : NoDivZero Δ Φ _ σ := fun σ'' h => hnd σ'' (steps_lift_ctx (fun x => .cellSet x _) .cellSetLeft .cellSetLeftTrap h)
      rcases assertEq_step_bwd hIntr he hnd1 hs1 with ⟨e1', hs1', heq'⟩
      exact ⟨_, .cellSetLeft hs1', .cellSetLeft heq'⟩
    | cellSetLeftTrap => rw [assertEq_trap_right he rfl]; exact ⟨_, .cellSetLeftTrap, .refl _⟩
    | cellSetRight hv hs2 =>
      have hEq := assertEq_eq_of_val_right he hv
      rw [hEq]
      have hnd2 : NoDivZero Δ Φ _ σ := fun σ'' h => (hEq ▸ hnd) σ'' (steps_lift_ctx (.cellSet _) (.cellSetRight hv) (.cellSetRightTrap hv) h)
      rcases assertEq_step_bwd hIntr (.refl _) hnd2 hs2 with ⟨e1', hs1', heq'⟩
      exact ⟨_, .cellSetRight hv hs1', .cellSetRight hv heq'⟩
    | cellSetRightTrap hv => rw [assertEq_eq_of_val_right he hv]; exact ⟨_, .cellSetRightTrap hv, .refl _⟩
    | cellSetVal hl hv => rw [assertEq_eq_of_val_right he (.loc _)]; exact ⟨_, .cellSetVal hl hv, .refl _⟩
  | cellSetRight hv he =>
    cases hs with
    | cellSetLeft hs1 => exact False.elim (value_no_stepUnchecked hv hs1)
    | cellSetLeftTrap => cases hv
    | cellSetRight _ hs2 =>
      have hnd2 : NoDivZero Δ Φ _ σ := fun σ'' h => hnd σ'' (steps_lift_ctx (.cellSet _) (.cellSetRight hv) (.cellSetRightTrap hv) h)
      rcases assertEq_step_bwd hIntr he hnd2 hs2 with ⟨e1', hs1', heq'⟩
      exact ⟨_, .cellSetRight hv hs1', .cellSetRight hv heq'⟩
    | cellSetRightTrap _ => rw [assertEq_trap_right he rfl]; exact ⟨_, .cellSetRightTrap hv, .refl _⟩
    | cellSetVal hl hv2 => rw [assertEq_eq_of_val_right he hv2]; exact ⟨_, .cellSetVal hl hv2, .refl _⟩
  | spawn he =>
    cases hs with
    | spawnStep hs1 =>
      have hnd1 : NoDivZero Δ Φ _ σ := fun σ'' h => hnd σ'' (steps_lift_ctx .spawn .spawnStep .spawnTrap h)
      rcases assertEq_step_bwd hIntr he hnd1 hs1 with ⟨e1', hs1', heq'⟩
      exact ⟨_, .spawnStep hs1', .spawn heq'⟩
    | spawnTrap => rw [assertEq_trap_right he rfl]; exact ⟨_, .spawnTrap, .refl _⟩
  | await he =>
    cases hs with
    | awaitStep hs1 =>
      have hnd1 : NoDivZero Δ Φ _ σ := fun σ'' h => hnd σ'' (steps_lift_ctx .await .awaitStep .awaitTrap h)
      rcases assertEq_step_bwd hIntr he hnd1 hs1 with ⟨e1', hs1', heq'⟩
      exact ⟨_, .awaitStep hs1', .await heq'⟩
    | awaitTrap => rw [assertEq_trap_right he rfl]; exact ⟨_, .awaitTrap, .refl _⟩
    | awaitVal h hv => rw [assertEq_eq_of_val_right he (.taskRef _)]; exact ⟨_, .awaitVal h hv, .refl _⟩
    | awaitTaskTrap h => rw [assertEq_eq_of_val_right he (.taskRef _)]; exact ⟨_, .awaitTaskTrap h, .refl _⟩
  | concPrim hl =>
    cases hs with
    | concPrimArgs hsl =>
      rcases assertEqList_step_bwd hIntr hl
        (noDivZeroList_of_ctx (.concPrim _) .concPrimArgs .concPrimTrap hnd) hsl with ⟨a', hsl', heql⟩
      exact ⟨_, .concPrimArgs hsl', .concPrim heql⟩
    | concPrimTrap hft => exact ⟨_, .concPrimTrap (assertEqList_firstTrap_right hl hft), .refl _⟩
    | concPrimVal h =>
      cases h with
      | chanSendClosed hch _ _ => simp [emptyPool] at hch
      | chanRecvClosed hch _ _ => simp [emptyPool] at hch
termination_by sizeOf e2

private theorem assertEqList_step_bwd {Δ : AdtEnv} {Φ : FunEnv} (hIntr : IntrinsicsOk Φ)
    {es1 es2 es2' : List Expr} {σ σ' : Store}
    (heql : AssertEqList es1 es2) (hnd : NoDivZeroList Δ Φ es1 σ)
    (hsl : StepListUnchecked Δ Φ es2 σ es2' σ') :
    ∃ es1', StepList Δ Φ emptyPool es1 σ es1' σ' .none ∧ AssertEqList es1' es2' := by
  cases heql with
  | refl =>
    cases hsl with
    | head hs1 =>
      rcases assertEq_step_bwd hIntr (.refl _) (noDivZeroList_head hnd) hs1 with ⟨e1', hs1', heq'⟩
      exact ⟨_, .head hs1', .head heq'⟩
    | tail hv hsl1 =>
      rcases assertEqList_step_bwd hIntr (.refl _) (noDivZeroList_tail hv hnd) hsl1 with ⟨es1', hsl1', heql'⟩
      exact ⟨_, .tail hv hsl1', .tail hv heql'⟩
  | head he =>
    cases hsl with
    | head hs1 =>
      rcases assertEq_step_bwd hIntr he (noDivZeroList_head hnd) hs1 with ⟨e1', hs1', heq'⟩
      exact ⟨_, .head hs1', .head heq'⟩
    | tail hv hsl1 =>
      have hEq := assertEq_eq_of_val_right he hv
      rw [hEq]
      rcases assertEqList_step_bwd hIntr (.refl _) (noDivZeroList_tail hv (hEq ▸ hnd)) hsl1 with ⟨es1', hsl1', heql'⟩
      exact ⟨_, .tail hv hsl1', .tail hv heql'⟩
  | tail hv hl =>
    cases hsl with
    | head hs1 => exact False.elim (value_no_stepUnchecked hv hs1)
    | tail _ hsl1 =>
      rcases assertEqList_step_bwd hIntr hl (noDivZeroList_tail hv hnd) hsl1 with ⟨es1', hsl1', heql'⟩
      exact ⟨_, .tail hv hsl1', .tail hv heql'⟩
termination_by sizeOf es2
end

private theorem steps_to_stepsUnchecked {Δ : AdtEnv} {Φ : FunEnv} (hIntr : IntrinsicsOk Φ)
    {e1 e2 v : Expr} {σ σ' : Store}
    (heq : AssertEq e1 e2) (hnd : NoDivZero Δ Φ e1 σ) (hv : IsValue v)
    (hst : Steps Δ Φ e1 σ v σ') :
    StepsUnchecked Δ Φ e2 σ v σ' := by
  induction hst generalizing e2 with
  | refl =>
    rw [← assertEq_eq_of_val_left heq hv]
    exact .refl _ _
  | trans hs hrest ih =>
    rcases assertEq_step_fwd hIntr heq hnd hs with ⟨e2', hs2, heq'⟩
    exact .trans hs2 (ih heq' (noDivZero_of_step hnd hs) hv)

private theorem stepsUnchecked_to_steps {Δ : AdtEnv} {Φ : FunEnv} (hIntr : IntrinsicsOk Φ)
    {e1 e2 v : Expr} {σ σ' : Store}
    (heq : AssertEq e1 e2) (hnd : NoDivZero Δ Φ e1 σ) (hv : IsValue v)
    (hst : StepsUnchecked Δ Φ e2 σ v σ') :
    Steps Δ Φ e1 σ v σ' := by
  induction hst generalizing e1 with
  | refl =>
    rw [assertEq_eq_of_val_right heq hv]
    exact .refl _ _
  | trans hs hrest ih =>
    rcases assertEq_step_bwd hIntr heq hnd hs with ⟨e1', hs1, heq'⟩
    exact .trans hs1 (ih heq' (noDivZero_of_step hnd hs1) hv)

private theorem stepsUnchecked_to_steps_trap {Δ : AdtEnv} {Φ : FunEnv} (hIntr : IntrinsicsOk Φ)
    {e1 e2 : Expr} {t : Trap} {σ σ' : Store}
    (heq : AssertEq e1 e2) (hnd : NoDivZero Δ Φ e1 σ)
    (hst : StepsUnchecked Δ Φ e2 σ (.trap t) σ') :
    Steps Δ Φ e1 σ (.trap t) σ' := by
  generalize hres : Expr.trap t = res at hst
  induction hst generalizing e1 with
  | refl =>
    subst hres
    rw [assertEq_trap_right heq rfl]
    exact .refl _ _
  | trans hs _ ih =>
    rcases assertEq_step_bwd hIntr heq hnd hs with ⟨e1', hs1, heq'⟩
    exact .trans hs1 (ih heq' (noDivZero_of_step hnd hs1) hres)

/-- **Theorem (`verified_opt_sound`)**:
    Machine-checked soundness of `--verified-opt` check elision.
    For any function `fd` verified by `verifyFn env fd fc = some obs` with `ValidObs obs`,
    under any pre-existing heap `σ` and arguments `vs` satisfying `fc.req`:
    1. Execution under `StepsUnchecked` (runtime `assert` checks and `.divByZero` guards elided
       via `elideVerifiedAsserts` and `evalBinOpUnchecked`) never traps with `.trap .divByZero`;
    2. `StepsUnchecked` is **bidirectionally observationally equivalent** to original `Steps`
       (identical return value `v` and final heap `σ'`);
    3. Every terminating unchecked execution satisfies the postcondition `fc.ens`. -/
theorem verified_opt_sound {Δ : AdtEnv} {Φ : FunEnv} {env : VcgEnv}
    (hIntr : IntrinsicsOk Φ) (hCallee : ∀ bound, CalleeSound Δ Φ env bound)
    {fd : FunDef} {fc : FnContract} {obs : List SForm} {initSt : SymState}
    (hΦ : Φ fd.name = some fd)
    (hInit : initFnSymState fd.params = some initSt)
    (hver : verifyFn env fd fc = some obs) (hObs : ValidObs obs)
    {M : Model} {L : Loc → Loc} {vs : List Expr} {σ : Store}
    (hM : ValidModel M) (hσ : StoreClosed σ)
    (hvs : ∀ v ∈ vs, IsValue v) (hlen : vs.length = fd.params.length)
    (hMatchInit : StateMatches M L initSt (zipParams fd.params vs) σ)
    (hReq : Steps Δ Φ (substMany (zipParams fd.params vs) fc.req) σ (.lit (.bool true)) σ) :
    (∀ σ', ¬ StepsUnchecked Δ Φ (.applyDir fd.name vs) σ (.trap .divByZero) σ') ∧
    (∀ v σ', IsValue v →
      (Steps Δ Φ (.applyDir fd.name vs) σ v σ' ↔ StepsUnchecked Δ Φ (.applyDir fd.name vs) σ v σ')) ∧
    (∀ v σ', IsValue v →
      StepsUnchecked Δ Φ (.applyDir fd.name vs) σ v σ' →
      Steps Δ Φ (substMany ((fc.retVar, v) :: zipParams fd.params vs) fc.ens) σ' (.lit (.bool true)) σ') := by
  have hSafe := verifyFn_sound hIntr hCallee hΦ hInit hver hObs hM hσ hvs hlen hMatchInit hReq
  have hnd : NoDivZero Δ Φ (.applyDir fd.name vs) σ := hSafe.1
  refine ⟨?_, ?_, ?_⟩
  · intro σ' hstU
    exact hnd σ' (stepsUnchecked_to_steps_trap hIntr (.refl _) hnd hstU)
  · intro v σ' hv
    exact ⟨steps_to_stepsUnchecked hIntr (.refl _) hnd hv,
           stepsUnchecked_to_steps hIntr (.refl _) hnd hv⟩
  · intro v σ' hv hstU
    exact hSafe.2 v σ' hv (stepsUnchecked_to_steps hIntr (.refl _) hnd hv hstU)

end CoreGeisha
