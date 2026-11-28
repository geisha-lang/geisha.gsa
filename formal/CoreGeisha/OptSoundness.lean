import CoreGeisha.Syntax
import CoreGeisha.Typing
import CoreGeisha.Semantics
import CoreGeisha.Soundness

/-!
# Core Geisha: Higher-Order Optimization & Specialization Metatheory

Machine-checked operational soundness proofs (zero `sorry`, zero custom axioms)
for the general Core IR optimization pipeline in `src/core.gsa`:

1. **Sequential Determinism (`step_det`, `steps_terminal_det`) & Observational Equivalence (`ObsEquiv`)**:
   Full determinism of single-thread operational semantics `Step Δ Φ emptyPool`,
   giving exact equivalence of terminal outcomes (both `IsValue` results and
   runtime `Trap`s) and final mutable `Cell` heaps `Store`.
2. **Dead Pure/Closure `let` Elimination & Cross-Pass Fresh-Binder Hygiene**:
   - `dead_val_let_obsEquiv` & `coFinishLetWithDeadElim_open_obsEquiv`: eliminating
     `let x = rhs; body` for closed `IsValue`s and open `coTermIsPure` expressions
     (`src/core.gsa:5363,7078`) when `x ∉ freeVars body`.
   - `impure_trap_dead_let_unsound` & `impure_cellSet_dead_let_unsound`:
     non-vacuity counterexamples witnessing that dropping purity alters traps or `Store`.
   - `fresh_inlined2_eval_iff`, `wrapLetParams_obsEquiv_substMany`, &
     `pipeline_shared_counter_disjoint`: soundness of pipeline-wide monotonic
     binder allocation (`allocFreshCoreBinder`, `src/core.gsa:4634,7490,7740`),
     paired with the `27 ≠ 22` counter-reset counterexample (`reset_inl_counter_captures_arg_counterexample`).
3. **Strict Left-to-Right Selective ANF Argument & Callee Lifting (`coFloatSelectedArgs`)**:
   - `anfLift_applyDir_obsEquiv`, `anfLift_apply_obsEquiv`, `selectiveAnfDir_obsEquiv`,
     `selectiveAnfDir_open_obsEquiv`, & `selectiveAnfApply_obsEquiv`: selective prefix
     lifting (skipping simple terms and preserving unfloated suffixes `idx > lastIdx`,
     `src/core.gsa:6212-6249`) preserves `Store` mutations and leftmost `Trap`s.
   - `out_of_order_float_changes_cell_value` (`11 ≠ 21`) &
     `out_of_order_float_mutates_before_trap`.
4. **Case-of-Known-Constructor / Tuple / Non-Float Literal (`coMatchPatKnown`, `coTryReduceMatch`)**:
   - `known_ctor_match_hit_obsEquiv`, `known_ctor_match_miss_obsEquiv`,
     `known_tuple_match_obsEquiv`, `known_lit_match_hit_obsEquiv`,
     `known_lit_match_miss_obsEquiv`, 3-valued `coMatchPatKnownB_no_sound` /
     `known_pat_miss_of_coPatNo_obsEquiv` (including nested subpattern misses on
     same-tag constructors), and fresh-renamed `coTryReduceMatch_fresh_lets_obsEquiv`.
   - `float_negZero_bits_neq_counterexample` (representation divergence witness) &
     `self_shadowed_ctor_let_counterexample` (`let x = End; let x = Next(x)`).
5. **Known-Closure Flattening Devirtualization (`$flat$`, `coGetOrCreateFlatClsFn`)**:
   - Both `ps ++ fvs` (`flat_closure_devirt_obsEquiv`) and the compiler's exact
     **captures-first ABI** (`fvsFresh ++ psFresh`, call `fvVals ++ args`, fresh
     parameter cloning, non-value argument evaluation, and `Φ ↦ Φ'` table extension:
     `flat_closure_devirt_capturesFirst_full_obsEquiv`, `actual_adv_flat44_witness`,
     matching `src/core.gsa:5989-6030,7379`).
6. **Self-Recursive Higher-Order Loop Specialization (`$spec$`, `coTrySpecializeHofLoop`)**:
   - Single-callback lockstep bisimulation (`hof_loop_spec_obsEquiv`) AND full
     **positional multi-callback specialization** (`PositionalLoopSpec`,
     `posSpecRel_step_forward`, `posSpecRel_step_backward`,
     `positional_hof_loop_spec_obsEquiv`, `spec_makeCls_wrapper_obsEquiv`) supporting
     callbacks at arbitrary parameter indices (`0`, middle, last), multiple callbacks,
     captures-first `.flatDir` and `.inline1` callback lowerings, and `Φ ↦ Φ'` extension,
     with witnesses for `specLoopColl(n, f, acc)`, `foldSepLoop(pos, itemFn, sepFn, acc)`,
     and unguarded `posSpecializeLoopExpr` miscompilation (`100 ≠ 1`).
7. **Contextual Observational Equivalence (`CtxObsEquiv`) Across Returned Closures**:
   - Proves raw syntactic `ObsEquiv` is not closed under `.lam` (`obsEquiv_not_lam_congr_counterexample`),
     establishes compositional higher-order `CtxObsEquiv` over all `ExprCtx` (including
     inside `.lam` bodies) with `CtxObsEquiv.congr_ctx` & `CtxObsEquiv.trans`, and proves
     congruence bisimulation soundness (`pureLetDrop_implies_ctxObsEquiv`,
     `returned_closure_dead_let_ctxObsEquiv`).
-/

namespace CoreGeisha

/-! ## Part 1: Sequential Determinism, Observational Equivalence & `let` Inversion -/

/-- Two expressions `(Φ1, e1)` and `(Φ2, e2)` are observationally equivalent if,
    from every initial heap `σ`, they reach the exact same terminal outcomes
    (both `IsValue` results and `Trap`s) and final heaps `σ'`. -/
def ObsEquiv (Δ : AdtEnv) (Φ1 Φ2 : FunEnv) (e1 e2 : Expr) : Prop :=
  ∀ (σ σ' : Store) (out : Expr),
    IsTerminal out →
    (Steps Δ Φ1 e1 σ out σ' ↔ Steps Δ Φ2 e2 σ out σ')

theorem ObsEquiv.refl (Δ : AdtEnv) (Φ : FunEnv) (e : Expr) :
    ObsEquiv Δ Φ Φ e e :=
  fun _ _ _ _ => Iff.rfl

theorem ObsEquiv.symm {Δ : AdtEnv} {Φ1 Φ2 : FunEnv} {e1 e2 : Expr}
    (h : ObsEquiv Δ Φ1 Φ2 e1 e2) : ObsEquiv Δ Φ2 Φ1 e2 e1 :=
  fun σ σ' out hout => (h σ σ' out hout).symm

theorem ObsEquiv.trans {Δ : AdtEnv} {Φ1 Φ2 Φ3 : FunEnv} {e1 e2 e3 : Expr}
    (h12 : ObsEquiv Δ Φ1 Φ2 e1 e2) (h23 : ObsEquiv Δ Φ2 Φ3 e2 e3) :
    ObsEquiv Δ Φ1 Φ3 e1 e3 :=
  fun σ σ' out hout => (h12 σ σ' out hout).trans (h23 σ σ' out hout)

theorem isValue_ne_trap {v : Expr} (hv : IsValue v) (t : Trap) : v ≠ .trap t := by
  intro heq; subst heq; cases hv

mutual
/-- Values are irreducible under `Step`. -/
theorem isValue_no_step {Δ : AdtEnv} {Φ : FunEnv} {pool : ConcPool}
    {v e' : Expr} {σ σ' : Store} {eff : ConcEff}
    (hv : IsValue v) (hs : Step Δ Φ pool v σ e' σ' eff) : False := by
  cases hv with
  | lit _ | loc _ | taskRef _ | syncRef _ _ | lam _ _ _ _ => cases hs
  | tuple hvs =>
    cases hs with
    | tupleStep hsl => exact isValueList_no_step hvs hsl
    | tupleTrap htr => exact isValueList_no_trap hvs htr
  | makeData _ _ hvs =>
    cases hs with
    | makeDataStep hsl => exact isValueList_no_step hvs hsl
    | makeDataTrap htr => exact isValueList_no_trap hvs htr
termination_by sizeOf v

theorem isValueList_no_step {Δ : AdtEnv} {Φ : FunEnv} {pool : ConcPool}
    {vs es' : List Expr} {σ σ' : Store} {eff : ConcEff}
    (hvs : ∀ v ∈ vs, IsValue v) (hsl : StepList Δ Φ pool vs σ es' σ' eff) : False := by
  cases hsl with
  | head hs => exact isValue_no_step (hvs _ (List.mem_cons_self ..)) hs
  | tail _ hsl' =>
    exact isValueList_no_step (fun x hx => hvs x (List.mem_cons_of_mem _ hx)) hsl'
termination_by sizeOf vs

theorem isValueList_no_trap {vs : List Expr} {t : Trap}
    (hvs : ∀ v ∈ vs, IsValue v) (htr : ListFirstTrap vs t) : False := by
  cases htr with
  | head t rest => exact isValue_ne_trap (hvs _ (List.mem_cons_self ..)) t rfl
  | tail _ htr' => exact isValueList_no_trap (fun x hx => hvs x (List.mem_cons_of_mem _ hx)) htr'
termination_by sizeOf vs
end

theorem trap_no_step {Δ : AdtEnv} {Φ : FunEnv} {pool : ConcPool}
    {t : Trap} {e' : Expr} {σ σ' : Store} {eff : ConcEff}
    (hs : Step Δ Φ pool (.trap t) σ e' σ' eff) : False := by
  cases hs

theorem stepList_disjoint_trap {Δ : AdtEnv} {Φ : FunEnv} {pool : ConcPool}
    {es es' : List Expr} {σ σ' : Store} {eff : ConcEff} {t : Trap}
    (hsl : StepList Δ Φ pool es σ es' σ' eff) (htr : ListFirstTrap es t) : False := by
  induction htr generalizing es' with
  | head t rest =>
    cases hsl with
    | head hs => exact trap_no_step hs
    | tail hv _ => exact isValue_ne_trap hv t rfl
  | tail hv _ ih =>
    cases hsl with
    | head hs => exact isValue_no_step hv hs
    | tail _ hsl' => exact ih hsl'

theorem listFirstTrap_det {es : List Expr} {t1 t2 : Trap}
    (h1 : ListFirstTrap es t1) (h2 : ListFirstTrap es t2) : t1 = t2 := by
  induction h1 with
  | head _ _ =>
    cases h2 with
    | head _ _ => rfl
    | tail hv _ => exact False.elim (isValue_ne_trap hv _ rfl)
  | tail hv _ ih =>
    cases h2 with
    | head _ _ => exact False.elim (isValue_ne_trap hv _ rfl)
    | tail _ h2' => exact ih h2'

theorem isTerminal_no_step {Δ : AdtEnv} {Φ : FunEnv} {pool : ConcPool}
    {out e' : Expr} {σ σ' : Store} {eff : ConcEff}
    (hterm : IsTerminal out) (hs : Step Δ Φ pool out σ e' σ' eff) : False := by
  rcases hterm with hv | ⟨t, rfl⟩
  · exact isValue_no_step hv hs
  · exact trap_no_step hs

theorem stepConcPrim_emptyPool_none_false {op : ConcPrim} {args : List Expr} {e' : Expr}
    (hc : StepConcPrim emptyPool op args e' .none) : False := by
  cases hc with
  | chanSendClosed h => simp [emptyPool] at h
  | chanRecvClosed h => simp [emptyPool] at h

mutual
/-- **Determinism of Sequential Single-Step Evaluation (`step_det`)**:
    Every pure sequential step on `emptyPool` uniquely determines `(e', σ')`. -/
theorem step_det {Δ : AdtEnv} {Φ : FunEnv} {e e1 e2 : Expr} {σ σ1 σ2 : Store}
    (h1 : Step Δ Φ emptyPool e σ e1 σ1 .none)
    (h2 : Step Δ Φ emptyPool e σ e2 σ2 .none) :
    e1 = e2 ∧ σ1 = σ2 := by
  cases h1 with
  | tupleStep hsl1 =>
    cases h2 with
    | tupleStep hsl2 =>
      rcases stepList_det hsl1 hsl2 with ⟨rfl, rfl⟩; exact ⟨rfl, rfl⟩
    | tupleTrap htr2 => exact False.elim (stepList_disjoint_trap hsl1 htr2)
  | tupleTrap htr1 =>
    cases h2 with
    | tupleStep hsl2 => exact False.elim (stepList_disjoint_trap hsl2 htr1)
    | tupleTrap htr2 => rw [listFirstTrap_det htr1 htr2]; exact ⟨rfl, rfl⟩
  | blockEmpty => cases h2; exact ⟨rfl, rfl⟩
  | blockSingle => cases h2; exact ⟨rfl, rfl⟩
  | blockConsStep hs1 =>
    cases h2 with
    | blockConsStep hs2 =>
      rcases step_det hs1 hs2 with ⟨rfl, rfl⟩; exact ⟨rfl, rfl⟩
    | blockConsVal hv2 => exact False.elim (isValue_no_step hv2 hs1)
    | blockConsTrap => exact False.elim (trap_no_step hs1)
  | blockConsVal hv1 =>
    cases h2 with
    | blockConsStep hs2 => exact False.elim (isValue_no_step hv1 hs2)
    | blockConsVal _ => exact ⟨rfl, rfl⟩
    | blockConsTrap => exact False.elim (isValue_ne_trap hv1 _ rfl)
  | blockConsTrap =>
    cases h2 with
    | blockConsStep hs2 => exact False.elim (trap_no_step hs2)
    | blockConsVal hv2 => exact False.elim (isValue_ne_trap hv2 _ rfl)
    | blockConsTrap => exact ⟨rfl, rfl⟩
  | applyFn hs1 =>
    cases h2 with
    | applyFn hs2 =>
      rcases step_det hs1 hs2 with ⟨rfl, rfl⟩; exact ⟨rfl, rfl⟩
    | applyFnTrap => exact False.elim (trap_no_step hs1)
    | applyArgs hv2 _ => exact False.elim (isValue_no_step hv2 hs1)
    | applyArgsTrap hv2 _ => exact False.elim (isValue_no_step hv2 hs1)
    | applyBeta _ _ => exact False.elim (isValue_no_step (.lam _ _ _ _) hs1)
  | applyFnTrap =>
    cases h2 with
    | applyFn hs2 => exact False.elim (trap_no_step hs2)
    | applyFnTrap => exact ⟨rfl, rfl⟩
    | applyArgs hv2 _ => exact False.elim (isValue_ne_trap hv2 _ rfl)
    | applyArgsTrap hv2 _ => exact False.elim (isValue_ne_trap hv2 _ rfl)
  | applyArgs hv1 hsl1 =>
    cases h2 with
    | applyFn hs2 => exact False.elim (isValue_no_step hv1 hs2)
    | applyFnTrap => exact False.elim (isValue_ne_trap hv1 _ rfl)
    | applyArgs _ hsl2 =>
      rcases stepList_det hsl1 hsl2 with ⟨rfl, rfl⟩; exact ⟨rfl, rfl⟩
    | applyArgsTrap _ htr2 => exact False.elim (stepList_disjoint_trap hsl1 htr2)
    | applyBeta hvs2 _ => exact False.elim (isValueList_no_step hvs2 hsl1)
  | applyArgsTrap hv1 htr1 =>
    cases h2 with
    | applyFn hs2 => exact False.elim (isValue_no_step hv1 hs2)
    | applyFnTrap => exact False.elim (isValue_ne_trap hv1 _ rfl)
    | applyArgs _ hsl2 => exact False.elim (stepList_disjoint_trap hsl2 htr1)
    | applyArgsTrap _ htr2 => rw [listFirstTrap_det htr1 htr2]; exact ⟨rfl, rfl⟩
    | applyBeta hvs2 _ => exact False.elim (isValueList_no_trap hvs2 htr1)
  | applyBeta hvs1 _ =>
    cases h2 with
    | applyFn hs2 => exact False.elim (isValue_no_step (.lam _ _ _ _) hs2)
    | applyArgs _ hsl2 => exact False.elim (isValueList_no_step hvs1 hsl2)
    | applyArgsTrap _ htr2 => exact False.elim (isValueList_no_trap hvs1 htr2)
    | applyBeta _ _ => exact ⟨rfl, rfl⟩
  | applyDirArgs hsl1 =>
    cases h2 with
    | applyDirArgs hsl2 =>
      rcases stepList_det hsl1 hsl2 with ⟨rfl, rfl⟩; exact ⟨rfl, rfl⟩
    | applyDirTrap htr2 => exact False.elim (stepList_disjoint_trap hsl1 htr2)
    | applyDirBeta _ hvs2 _ => exact False.elim (isValueList_no_step hvs2 hsl1)
  | applyDirTrap htr1 =>
    cases h2 with
    | applyDirArgs hsl2 => exact False.elim (stepList_disjoint_trap hsl2 htr1)
    | applyDirTrap htr2 => rw [listFirstTrap_det htr1 htr2]; exact ⟨rfl, rfl⟩
    | applyDirBeta _ hvs2 _ => exact False.elim (isValueList_no_trap hvs2 htr1)
  | applyDirBeta hfn1 hvs1 _ =>
    cases h2 with
    | applyDirArgs hsl2 => exact False.elim (isValueList_no_step hvs1 hsl2)
    | applyDirTrap htr2 => exact False.elim (isValueList_no_trap hvs1 htr2)
    | applyDirBeta hfn2 _ _ =>
      rw [hfn1] at hfn2; injection hfn2 with hfd; subst hfd; exact ⟨rfl, rfl⟩
  | unStep hs1 =>
    cases h2 with
    | unStep hs2 =>
      rcases step_det hs1 hs2 with ⟨rfl, rfl⟩; exact ⟨rfl, rfl⟩
    | unTrap => exact False.elim (trap_no_step hs1)
    | unVal _ => exact False.elim (isValue_no_step (.lit _) hs1)
  | unTrap =>
    cases h2 with
    | unStep hs2 => exact False.elim (trap_no_step hs2)
    | unTrap => exact ⟨rfl, rfl⟩
  | unVal hev1 =>
    cases h2 with
    | unStep hs2 => exact False.elim (isValue_no_step (.lit _) hs2)
    | unVal hev2 => rw [hev1] at hev2; injection hev2 with hl; subst hl; exact ⟨rfl, rfl⟩
  | binLeft hs1 =>
    cases h2 with
    | binLeft hs2 =>
      rcases step_det hs1 hs2 with ⟨rfl, rfl⟩; exact ⟨rfl, rfl⟩
    | binLeftTrap => exact False.elim (trap_no_step hs1)
    | binAndFalse | binAndTrue | binOrTrue | binOrFalse =>
      exact False.elim (isValue_no_step (.lit _) hs1)
    | binRight _ _ hv2 _ | binRightTrap _ _ hv2 =>
      exact False.elim (isValue_no_step hv2 hs1)
    | binVal _ | binTrap _ =>
      exact False.elim (isValue_no_step (.lit _) hs1)
  | binLeftTrap =>
    cases h2 with
    | binLeft hs2 => exact False.elim (trap_no_step hs2)
    | binLeftTrap => exact ⟨rfl, rfl⟩
    | binRight _ _ hv2 _ | binRightTrap _ _ hv2 =>
      exact False.elim (isValue_ne_trap hv2 _ rfl)
  | binAndFalse =>
    cases h2 with
    | binLeft hs2 => exact False.elim (isValue_no_step (.lit _) hs2)
    | binAndFalse => exact ⟨rfl, rfl⟩
    | binRight hna _ _ _ | binRightTrap hna _ _ => exact False.elim (hna rfl)
    | binVal hev | binTrap hev => simp [evalBinOp] at hev
  | binAndTrue =>
    cases h2 with
    | binLeft hs2 => exact False.elim (isValue_no_step (.lit _) hs2)
    | binAndTrue => exact ⟨rfl, rfl⟩
    | binRight hna _ _ _ | binRightTrap hna _ _ => exact False.elim (hna rfl)
    | binVal hev | binTrap hev => simp [evalBinOp] at hev
  | binOrTrue =>
    cases h2 with
    | binLeft hs2 => exact False.elim (isValue_no_step (.lit _) hs2)
    | binOrTrue => exact ⟨rfl, rfl⟩
    | binRight _ hno _ _ | binRightTrap _ hno _ => exact False.elim (hno rfl)
    | binVal hev | binTrap hev => simp [evalBinOp] at hev
  | binOrFalse =>
    cases h2 with
    | binLeft hs2 => exact False.elim (isValue_no_step (.lit _) hs2)
    | binOrFalse => exact ⟨rfl, rfl⟩
    | binRight _ hno _ _ | binRightTrap _ hno _ => exact False.elim (hno rfl)
    | binVal hev | binTrap hev => simp [evalBinOp] at hev
  | binRight hna1 hno1 hv1 hs1 =>
    cases h2 with
    | binLeft hs2 => exact False.elim (isValue_no_step hv1 hs2)
    | binLeftTrap => exact False.elim (isValue_ne_trap hv1 _ rfl)
    | binAndFalse | binAndTrue => exact False.elim (hna1 rfl)
    | binOrTrue | binOrFalse => exact False.elim (hno1 rfl)
    | binRight _ _ _ hs2 =>
      rcases step_det hs1 hs2 with ⟨rfl, rfl⟩; exact ⟨rfl, rfl⟩
    | binRightTrap _ _ _ => exact False.elim (trap_no_step hs1)
    | binVal _ | binTrap _ => exact False.elim (isValue_no_step (.lit _) hs1)
  | binRightTrap hna1 hno1 hv1 =>
    cases h2 with
    | binLeft hs2 => exact False.elim (isValue_no_step hv1 hs2)
    | binLeftTrap => exact False.elim (isValue_ne_trap hv1 _ rfl)
    | binAndFalse | binAndTrue => exact False.elim (hna1 rfl)
    | binOrTrue | binOrFalse => exact False.elim (hno1 rfl)
    | binRight _ _ _ hs2 => exact False.elim (trap_no_step hs2)
    | binRightTrap _ _ _ => exact ⟨rfl, rfl⟩
  | binVal hev1 =>
    cases h2 with
    | binLeft hs2 => exact False.elim (isValue_no_step (.lit _) hs2)
    | binAndFalse | binAndTrue | binOrTrue | binOrFalse => simp [evalBinOp] at hev1
    | binRight _ _ _ hs2 => exact False.elim (isValue_no_step (.lit _) hs2)
    | binVal hev2 => rw [hev1] at hev2; injection hev2 with hr; injection hr with hl; subst hl; exact ⟨rfl, rfl⟩
    | binTrap hev2 => rw [hev1] at hev2; cases hev2
  | binTrap hev1 =>
    cases h2 with
    | binLeft hs2 => exact False.elim (isValue_no_step (.lit _) hs2)
    | binAndFalse | binAndTrue | binOrTrue | binOrFalse => simp [evalBinOp] at hev1
    | binRight _ _ _ hs2 => exact False.elim (isValue_no_step (.lit _) hs2)
    | binVal hev2 => rw [hev1] at hev2; cases hev2
    | binTrap hev2 => rw [hev1] at hev2; injection hev2 with hr; injection hr with ht; subst ht; exact ⟨rfl, rfl⟩
  | letStep hs1 =>
    cases h2 with
    | letStep hs2 =>
      rcases step_det hs1 hs2 with ⟨rfl, rfl⟩; exact ⟨rfl, rfl⟩
    | letTrap => exact False.elim (trap_no_step hs1)
    | letVal hv2 => exact False.elim (isValue_no_step hv2 hs1)
  | letTrap =>
    cases h2 with
    | letStep hs2 => exact False.elim (trap_no_step hs2)
    | letTrap => exact ⟨rfl, rfl⟩
    | letVal hv2 => exact False.elim (isValue_ne_trap hv2 _ rfl)
  | letVal hv1 =>
    cases h2 with
    | letStep hs2 => exact False.elim (isValue_no_step hv1 hs2)
    | letTrap => exact False.elim (isValue_ne_trap hv1 _ rfl)
    | letVal _ => exact ⟨rfl, rfl⟩
  | ifStep hs1 =>
    cases h2 with
    | ifStep hs2 =>
      rcases step_det hs1 hs2 with ⟨rfl, rfl⟩; exact ⟨rfl, rfl⟩
    | ifTrap => exact False.elim (trap_no_step hs1)
    | ifTrue | ifFalse => exact False.elim (isValue_no_step (.lit _) hs1)
  | ifTrap =>
    cases h2 with
    | ifStep hs2 => exact False.elim (trap_no_step hs2)
    | ifTrap => exact ⟨rfl, rfl⟩
  | ifTrue =>
    cases h2 with
    | ifStep hs2 => exact False.elim (isValue_no_step (.lit _) hs2)
    | ifTrue => exact ⟨rfl, rfl⟩
  | ifFalse =>
    cases h2 with
    | ifStep hs2 => exact False.elim (isValue_no_step (.lit _) hs2)
    | ifFalse => exact ⟨rfl, rfl⟩
  | whileUnfold => cases h2; exact ⟨rfl, rfl⟩
  | matchScrut hs1 =>
    cases h2 with
    | matchScrut hs2 =>
      rcases step_det hs1 hs2 with ⟨rfl, rfl⟩; exact ⟨rfl, rfl⟩
    | matchScrutTrap => exact False.elim (trap_no_step hs1)
    | matchEmpty hv2 | matchHit hv2 _ | matchMiss hv2 _ =>
      exact False.elim (isValue_no_step hv2 hs1)
  | matchScrutTrap =>
    cases h2 with
    | matchScrut hs2 => exact False.elim (trap_no_step hs2)
    | matchScrutTrap => exact ⟨rfl, rfl⟩
    | matchEmpty hv2 | matchHit hv2 _ | matchMiss hv2 _ =>
      exact False.elim (isValue_ne_trap hv2 _ rfl)
  | matchEmpty hv1 =>
    cases h2 with
    | matchScrut hs2 => exact False.elim (isValue_no_step hv1 hs2)
    | matchScrutTrap => exact False.elim (isValue_ne_trap hv1 _ rfl)
    | matchEmpty _ => exact ⟨rfl, rfl⟩
  | matchHit hv1 hm1 =>
    cases h2 with
    | matchScrut hs2 => exact False.elim (isValue_no_step hv1 hs2)
    | matchScrutTrap => exact False.elim (isValue_ne_trap hv1 _ rfl)
    | matchHit _ hm2 => rw [hm1] at hm2; injection hm2 with henv; subst henv; exact ⟨rfl, rfl⟩
    | matchMiss _ hm2 => rw [hm1] at hm2; cases hm2
  | matchMiss hv1 hm1 =>
    cases h2 with
    | matchScrut hs2 => exact False.elim (isValue_no_step hv1 hs2)
    | matchScrutTrap => exact False.elim (isValue_ne_trap hv1 _ rfl)
    | matchHit _ hm2 => rw [hm1] at hm2; cases hm2
    | matchMiss _ _ => exact ⟨rfl, rfl⟩
  | makeDataStep hsl1 =>
    cases h2 with
    | makeDataStep hsl2 =>
      rcases stepList_det hsl1 hsl2 with ⟨rfl, rfl⟩; exact ⟨rfl, rfl⟩
    | makeDataTrap htr2 => exact False.elim (stepList_disjoint_trap hsl1 htr2)
  | makeDataTrap htr1 =>
    cases h2 with
    | makeDataStep hsl2 => exact False.elim (stepList_disjoint_trap hsl2 htr1)
    | makeDataTrap htr2 => rw [listFirstTrap_det htr1 htr2]; exact ⟨rfl, rfl⟩
  | getTagStep hs1 =>
    cases h2 with
    | getTagStep hs2 =>
      rcases step_det hs1 hs2 with ⟨rfl, rfl⟩; exact ⟨rfl, rfl⟩
    | getTagTrap => exact False.elim (trap_no_step hs1)
    | getTagVal hvs2 => exact False.elim (isValue_no_step (.makeData _ _ hvs2) hs1)
  | getTagTrap =>
    cases h2 with
    | getTagStep hs2 => exact False.elim (trap_no_step hs2)
    | getTagTrap => exact ⟨rfl, rfl⟩
  | getTagVal hvs1 =>
    cases h2 with
    | getTagStep hs2 => exact False.elim (isValue_no_step (.makeData _ _ hvs1) hs2)
    | getTagVal _ => exact ⟨rfl, rfl⟩
  | cellNewStep hs1 =>
    cases h2 with
    | cellNewStep hs2 =>
      rcases step_det hs1 hs2 with ⟨rfl, rfl⟩; exact ⟨rfl, rfl⟩
    | cellNewTrap => exact False.elim (trap_no_step hs1)
    | cellNewVal hv2 => exact False.elim (isValue_no_step hv2 hs1)
  | cellNewTrap =>
    cases h2 with
    | cellNewStep hs2 => exact False.elim (trap_no_step hs2)
    | cellNewTrap => exact ⟨rfl, rfl⟩
    | cellNewVal hv2 => exact False.elim (isValue_ne_trap hv2 _ rfl)
  | cellNewVal hv1 =>
    cases h2 with
    | cellNewStep hs2 => exact False.elim (isValue_no_step hv1 hs2)
    | cellNewTrap => exact False.elim (isValue_ne_trap hv1 _ rfl)
    | cellNewVal _ => exact ⟨rfl, rfl⟩
  | cellGetStep hs1 =>
    cases h2 with
    | cellGetStep hs2 =>
      rcases step_det hs1 hs2 with ⟨rfl, rfl⟩; exact ⟨rfl, rfl⟩
    | cellGetTrap => exact False.elim (trap_no_step hs1)
    | cellGetVal _ => exact False.elim (isValue_no_step (.loc _) hs1)
  | cellGetTrap =>
    cases h2 with
    | cellGetStep hs2 => exact False.elim (trap_no_step hs2)
    | cellGetTrap => exact ⟨rfl, rfl⟩
  | cellGetVal hl1 =>
    cases h2 with
    | cellGetStep hs2 => exact False.elim (isValue_no_step (.loc _) hs2)
    | cellGetVal hl2 => rw [hl1] at hl2; injection hl2 with hv; subst hv; exact ⟨rfl, rfl⟩
  | cellSetLeft hs1 =>
    cases h2 with
    | cellSetLeft hs2 =>
      rcases step_det hs1 hs2 with ⟨rfl, rfl⟩; exact ⟨rfl, rfl⟩
    | cellSetLeftTrap => exact False.elim (trap_no_step hs1)
    | cellSetRight hv2 _ | cellSetRightTrap hv2 => exact False.elim (isValue_no_step hv2 hs1)
    | cellSetVal _ _ => exact False.elim (isValue_no_step (.loc _) hs1)
  | cellSetLeftTrap =>
    cases h2 with
    | cellSetLeft hs2 => exact False.elim (trap_no_step hs2)
    | cellSetLeftTrap => exact ⟨rfl, rfl⟩
    | cellSetRight hv2 _ | cellSetRightTrap hv2 => exact False.elim (isValue_ne_trap hv2 _ rfl)
  | cellSetRight hv1 hs1 =>
    cases h2 with
    | cellSetLeft hs2 => exact False.elim (isValue_no_step hv1 hs2)
    | cellSetLeftTrap => exact False.elim (isValue_ne_trap hv1 _ rfl)
    | cellSetRight _ hs2 =>
      rcases step_det hs1 hs2 with ⟨rfl, rfl⟩; exact ⟨rfl, rfl⟩
    | cellSetRightTrap _ => exact False.elim (trap_no_step hs1)
    | cellSetVal _ hv2 => exact False.elim (isValue_no_step hv2 hs1)
  | cellSetRightTrap hv1 =>
    cases h2 with
    | cellSetLeft hs2 => exact False.elim (isValue_no_step hv1 hs2)
    | cellSetLeftTrap => exact False.elim (isValue_ne_trap hv1 _ rfl)
    | cellSetRight _ hs2 => exact False.elim (trap_no_step hs2)
    | cellSetRightTrap _ => exact ⟨rfl, rfl⟩
    | cellSetVal _ hv2 => exact False.elim (isValue_ne_trap hv2 _ rfl)
  | cellSetVal _ hv1 =>
    cases h2 with
    | cellSetLeft hs2 => exact False.elim (isValue_no_step (.loc _) hs2)
    | cellSetRight _ hs2 => exact False.elim (isValue_no_step hv1 hs2)
    | cellSetRightTrap _ => exact False.elim (isValue_ne_trap hv1 _ rfl)
    | cellSetVal _ _ => exact ⟨rfl, rfl⟩
  | spawnStep hs1 =>
    cases h2 with
    | spawnStep hs2 =>
      rcases step_det hs1 hs2 with ⟨rfl, rfl⟩; exact ⟨rfl, rfl⟩
    | spawnTrap => exact False.elim (trap_no_step hs1)
  | spawnTrap =>
    cases h2 with
    | spawnStep hs2 => exact False.elim (trap_no_step hs2)
    | spawnTrap => exact ⟨rfl, rfl⟩
  | awaitStep hs1 =>
    cases h2 with
    | awaitStep hs2 =>
      rcases step_det hs1 hs2 with ⟨rfl, rfl⟩; exact ⟨rfl, rfl⟩
    | awaitTrap => exact False.elim (trap_no_step hs1)
    | awaitVal h _ | awaitTaskTrap h => simp [emptyPool] at h
  | awaitTrap =>
    cases h2 with
    | awaitStep hs2 => exact False.elim (trap_no_step hs2)
    | awaitTrap => exact ⟨rfl, rfl⟩
  | awaitVal h _ | awaitTaskTrap h => simp [emptyPool] at h
  | concPrimArgs hsl1 =>
    cases h2 with
    | concPrimArgs hsl2 =>
      rcases stepList_det hsl1 hsl2 with ⟨rfl, rfl⟩; exact ⟨rfl, rfl⟩
    | concPrimTrap htr2 => exact False.elim (stepList_disjoint_trap hsl1 htr2)
    | concPrimVal hc2 => exact False.elim (stepConcPrim_emptyPool_none_false hc2)
  | concPrimTrap htr1 =>
    cases h2 with
    | concPrimArgs hsl2 => exact False.elim (stepList_disjoint_trap hsl2 htr1)
    | concPrimTrap htr2 => rw [listFirstTrap_det htr1 htr2]; exact ⟨rfl, rfl⟩
    | concPrimVal hc2 => exact False.elim (stepConcPrim_emptyPool_none_false hc2)
  | concPrimVal hc1 => exact False.elim (stepConcPrim_emptyPool_none_false hc1)
termination_by sizeOf e

theorem stepList_det {Δ : AdtEnv} {Φ : FunEnv} {es es1 es2 : List Expr} {σ σ1 σ2 : Store}
    (h1 : StepList Δ Φ emptyPool es σ es1 σ1 .none)
    (h2 : StepList Δ Φ emptyPool es σ es2 σ2 .none) :
    es1 = es2 ∧ σ1 = σ2 := by
  cases h1 with
  | head hs1 =>
    cases h2 with
    | head hs2 =>
      rcases step_det hs1 hs2 with ⟨rfl, rfl⟩; exact ⟨rfl, rfl⟩
    | tail hv2 _ => exact False.elim (isValue_no_step hv2 hs1)
  | tail hv1 hsl1 =>
    cases h2 with
    | head hs2 => exact False.elim (isValue_no_step hv1 hs2)
    | tail _ hsl2 =>
      rcases stepList_det hsl1 hsl2 with ⟨rfl, rfl⟩; exact ⟨rfl, rfl⟩
termination_by sizeOf es
end

theorem steps_of_isTerminal {Δ : AdtEnv} {Φ : FunEnv} {out e' : Expr} {σ σ' : Store}
    (hterm : IsTerminal out) (hsteps : Steps Δ Φ out σ e' σ') :
    e' = out ∧ σ' = σ := by
  cases hsteps with
  | refl => exact ⟨rfl, rfl⟩
  | trans hs _ => exact False.elim (isTerminal_no_step hterm hs)

/-- **Determinism of Terminal Multi-Step Evaluation (`steps_terminal_det`)**:
    Any sequential expression `e` starting from store `σ` reaches at most one
    terminal outcome `(out, σ')`. -/
theorem steps_terminal_det {Δ : AdtEnv} {Φ : FunEnv}
    {e out1 out2 : Expr} {σ σ1 σ2 : Store}
    (h1 : Steps Δ Φ e σ out1 σ1) (ht1 : IsTerminal out1)
    (h2 : Steps Δ Φ e σ out2 σ2) (ht2 : IsTerminal out2) :
    out1 = out2 ∧ σ1 = σ2 := by
  induction h1 with
  | refl =>
    rcases steps_of_isTerminal ht1 h2 with ⟨rfl, rfl⟩
    exact ⟨rfl, rfl⟩
  | trans hs1 _ ih =>
    cases h2 with
    | refl => exact False.elim (isTerminal_no_step ht2 hs1)
    | trans hs2 hrest2 =>
      rcases step_det hs1 hs2 with ⟨rfl, rfl⟩
      exact ih ht1 hrest2

/-- Any single deterministic transition `e1 ↦ e2` (across all stores `σ`) induces `ObsEquiv`. -/
theorem obsEquiv_of_det_step {Δ : AdtEnv} {Φ : FunEnv} {e1 e2 : Expr}
    (hstep : ∀ σ, Step Δ Φ emptyPool e1 σ e2 σ .none) :
    ObsEquiv Δ Φ Φ e1 e2 := by
  intro σ σ' out hout
  constructor
  · intro h1
    cases h1 with
    | refl => exact False.elim (isTerminal_no_step hout (hstep σ))
    | trans hs1 hrest =>
      rcases step_det hs1 (hstep σ) with ⟨rfl, rfl⟩
      exact hrest
  · intro h2
    exact .trans (hstep σ) h2

theorem Steps.append {Δ : AdtEnv} {Φ : FunEnv} {e1 e2 e3 : Expr} {σ1 σ2 σ3 : Store}
    (h12 : Steps Δ Φ e1 σ1 e2 σ2) (h23 : Steps Δ Φ e2 σ2 e3 σ3) :
    Steps Δ Φ e1 σ1 e3 σ3 := by
  induction h12 with
  | refl => exact h23
  | trans hs _ ih => exact .trans hs (ih h23)

theorem Steps.single {Δ : AdtEnv} {Φ : FunEnv} {e1 e2 : Expr} {σ1 σ2 : Store}
    (hs : Step Δ Φ emptyPool e1 σ1 e2 σ2 .none) :
    Steps Δ Φ e1 σ1 e2 σ2 :=
  .trans hs (.refl _ _)

theorem Steps.letCongr {Δ : AdtEnv} {Φ : FunEnv} {x : Ident} {e1 e1' e2 : Expr} {σ1 σ2 : Store}
    (h : Steps Δ Φ e1 σ1 e1' σ2) :
    Steps Δ Φ (.let_ x e1 e2) σ1 (.let_ x e1' e2) σ2 := by
  induction h with
  | refl => exact .refl _ _
  | trans hs _ ih => exact .trans (.letStep hs) ih

theorem Steps.liftCongr {Δ : AdtEnv} {Φ : FunEnv} (f : Expr → Expr)
    (hf : ∀ {a a' : Expr} {s s' : Store},
      Step Δ Φ emptyPool a s a' s' .none → Step Δ Φ emptyPool (f a) s (f a') s' .none)
    {e1 e2 : Expr} {σ1 σ2 : Store}
    (h : Steps Δ Φ e1 σ1 e2 σ2) :
    Steps Δ Φ (f e1) σ1 (f e2) σ2 := by
  induction h with
  | refl => exact .refl _ _
  | trans hs _ ih => exact .trans (hf hs) ih

/-- **Exact Operational Inversion for `let x = e1; e2` Reaching a Terminal Outcome**. -/
theorem steps_let_terminal_iff {Δ : AdtEnv} {Φ : FunEnv}
    {x : Ident} {e1 e2 out : Expr} {σ σ' : Store} (hout : IsTerminal out) :
    Steps Δ Φ (.let_ x e1 e2) σ out σ' ↔
      (∃ t, out = .trap t ∧ Steps Δ Φ e1 σ (.trap t) σ') ∨
      (∃ v1 σ1, IsValue v1 ∧ Steps Δ Φ e1 σ v1 σ1 ∧ Steps Δ Φ (subst x v1 e2) σ1 out σ') := by
  constructor
  · intro h
    generalize hlet : Expr.let_ x e1 e2 = full at h
    induction h generalizing e1 with
    | refl =>
      subst hlet
      rcases hout with hv | ⟨t, htr⟩
      · cases hv
      · cases htr
    | trans hs hrest ih =>
      subst hlet
      cases hs with
      | letStep hs1 =>
        rcases ih hout rfl with ⟨t, rfl, htr⟩ | ⟨v1, σ1, hv1, hs_v1, hs_body⟩
        · exact Or.inl ⟨t, rfl, .trans hs1 htr⟩
        · exact Or.inr ⟨v1, σ1, hv1, .trans hs1 hs_v1, hs_body⟩
      | letTrap =>
        rcases steps_of_isTerminal (Or.inr ⟨_, rfl⟩) hrest with ⟨rfl, rfl⟩
        exact Or.inl ⟨_, rfl, .refl _ _⟩
      | letVal hv1 =>
        exact Or.inr ⟨e1, _, hv1, .refl _ _, hrest⟩
  · intro h
    rcases h with ⟨t, rfl, htr⟩ | ⟨v1, σ1, hv1, hs1, hs2⟩
    · exact Steps.append (Steps.letCongr htr) (Steps.single .letTrap)
    · exact Steps.append (Steps.letCongr hs1) (.trans (.letVal hv1) hs2)

/-- Helper witnessing `¬ ObsEquiv` whenever two expressions reach distinct `(out, σ')`. -/
theorem not_obsEquiv_of_distinct_terminals {Δ : AdtEnv} {Φ : FunEnv}
    {e1 e2 out1 out2 : Expr} {σ σ1 σ2 : Store}
    (hs1 : Steps Δ Φ e1 σ out1 σ1) (ht1 : IsTerminal out1)
    (hs2 : Steps Δ Φ e2 σ out2 σ2) (ht2 : IsTerminal out2)
    (hne : out1 ≠ out2 ∨ σ1 ≠ σ2) :
    ¬ ObsEquiv Δ Φ Φ e1 e2 := by
  intro heq
  have hs2' := (heq σ σ1 out1 ht1).mp hs1
  rcases steps_terminal_det hs2' ht1 hs2 ht2 with ⟨ho, hσ⟩
  rcases hne with hno | hnσ
  · exact hno ho
  · exact hnσ hσ

/-! ## Part 2: Dead Pure/Closure `let` Elimination & Cross-Pass Fresh-Binder Hygiene -/

/-- **Soundness of Dead Value / Closure `let` Elimination (`coFinishLetWithDeadElim`, `coFinishMakeClsWithDeadElim`)**:
    Eliminating `let x = v; body` when `IsValue v` (including `.lam` closures, tuples of values,
    and ADT constructors of values) and `x ∉ freeVars body` preserves exact observational equivalence. -/
theorem dead_val_let_obsEquiv (Δ : AdtEnv) (Φ : FunEnv)
    {x : Ident} {v body : Expr} (hv : IsValue v) (hnot : x ∉ freeVars body) :
    ObsEquiv Δ Φ Φ (.let_ x v body) body := by
  have hstep : ∀ σ, Step Δ Φ emptyPool (.let_ x v body) σ body σ .none := by
    intro σ
    have hs := Step.letVal (Δ := Δ) (Φ := Φ) (pool := emptyPool) (x := x) (e2 := body) (σ := σ) hv
    rwa [subst_not_mem_freeVars body hnot] at hs
  exact obsEquiv_of_det_step hstep

/-- **Non-Vacuity Counterexample 1a (`impure_trap_dead_let_unsound`)**:
    Eliminating an unused `let x = 1 / 0; 0` without checking valuehood/purity
    turns a guaranteed `divByZero` trap into returning `0`. -/
theorem impure_trap_dead_let_unsound :
    ¬ ObsEquiv (fun _ => none) (fun _ => none) (fun _ => none)
        (.let_ "x" (.bin .div (.lit (.int 1)) (.lit (.int 0))) (.lit (.int 0)))
        (.lit (.int 0)) := by
  refine not_obsEquiv_of_distinct_terminals
    (out1 := .trap .divByZero) (σ1 := [])
    (out2 := .lit (.int 0)) (σ2 := []) (σ := []) ?_ (Or.inr ⟨_, rfl⟩) (.refl _ _) (Or.inl (.lit _))
    (Or.inl (by rintro ⟨⟩))
  exact .trans (.letStep (.binTrap (by rfl))) (.single .letTrap)

/-- **Non-Vacuity Counterexample 1b (`impure_cellSet_dead_let_unsound`)**:
    Eliminating an unused `let x = cellSet(loc 0, 99); 0` drops the heap write,
    leaving `Store` `[0]` instead of `[99]`. -/
theorem impure_cellSet_dead_let_unsound :
    ¬ ObsEquiv (fun _ => none) (fun _ => none) (fun _ => none)
        (.let_ "x" (.cellSet (.loc 0) (.lit (.int 99))) (.lit (.int 0)))
        (.lit (.int 0)) := by
  refine not_obsEquiv_of_distinct_terminals
    (out1 := .lit (.int 0)) (σ1 := [.lit (.int 99)])
    (out2 := .lit (.int 0)) (σ2 := [.lit (.int 0)]) (σ := [.lit (.int 0)])
    ?_ (Or.inl (.lit _)) (.refl _ _) (Or.inl (.lit _))
    (Or.inr (by rintro ⟨⟩))
  exact .trans (.letStep (.cellSetVal (by decide) (.lit _))) (.single (.letVal (.lit _)))

/-- Parameter-binding wrapper produced when `inlineTinyLeafFns` inlines a 2-parameter function. -/
def wrapInlined2 (p1 p2 : Ident) (a1 a2 body : Expr) : Expr :=
  .let_ p1 a1 (.let_ p2 a2 body)

/-- **Soundness of Pipeline-Wide Fresh Parameter Binders (`allocFreshCoreBinder`)**:
    When `p1 ≠ p2` and `p1 ∉ freeVars a2` (strictly guaranteed by a single pipeline-wide
    monotonic fresh binder counter across all leaf-inlining and combinator passes),
    `wrapInlined2` evaluates `a1` then `a2` in the unshadowed caller scope. -/
theorem fresh_inlined2_eval_iff {Δ : AdtEnv} {Φ : FunEnv}
    {p1 p2 : Ident} {a1 a2 body out : Expr} {σ σ' : Store}
    (hout : IsTerminal out) (hne : p1 ≠ p2) (hfresh : p1 ∉ freeVars a2) :
    Steps Δ Φ (wrapInlined2 p1 p2 a1 a2 body) σ out σ' ↔
      (∃ t, out = .trap t ∧ Steps Δ Φ a1 σ (.trap t) σ') ∨
      (∃ v1 σ1, IsValue v1 ∧ Steps Δ Φ a1 σ v1 σ1 ∧
        ((∃ t, out = .trap t ∧ Steps Δ Φ a2 σ1 (.trap t) σ') ∨
         (∃ v2 σ2, IsValue v2 ∧ Steps Δ Φ a2 σ1 v2 σ2 ∧
           Steps Δ Φ (subst p2 v2 (subst p1 v1 body)) σ2 out σ'))) := by
  unfold wrapInlined2
  rw [steps_let_terminal_iff hout]
  apply or_congr Iff.rfl
  have hbeq : (p2 == p1) = false := beq_false_of_ne (Ne.symm hne)
  constructor
  · rintro ⟨v1, σ1, hv1, hs1, hs2⟩
    simp only [subst, hbeq, Bool.false_eq_true, ↓reduceIte, subst_not_mem_freeVars a2 hfresh] at hs2
    exact ⟨v1, σ1, hv1, hs1, (steps_let_terminal_iff hout).mp hs2⟩
  · rintro ⟨v1, σ1, hv1, hs1, hinner⟩
    refine ⟨v1, σ1, hv1, hs1, ?_⟩
    simp only [subst, hbeq, Bool.false_eq_true, ↓reduceIte, subst_not_mem_freeVars a2 hfresh]
    exact (steps_let_terminal_iff hout).mpr hinner

/-- **Non-Vacuity Counterexample 1c (`reset_inl_counter_captures_arg_counterexample`)**:
    Exact Core IR model of the two-pass `$inl$0$x` counter-reset bug (`leafagain.gsa`):
    Pass 1 binds `$inl$0$x = cellGet(c)` (`7`); if Pass 2 resets its counter to `0` when
    inlining `late(2, $inl$0$x)`, `p1 = "$inl$0$x"` shadows the outer `$inl$0$x` in `a2`,
    producing `22` instead of `27`. With pipeline-shared fresh binders (`$inl$1$x`, `$inl$2$y`),
    evaluation produces `27`. -/
theorem reset_inl_counter_captures_arg_counterexample :
    let eFresh : Expr :=
      .let_ "$inl$0$x" (.cellGet (.loc 0))
        (wrapInlined2 "$inl$1$x" "$inl$2$y" (.lit (.int 2)) (.var "$inl$0$x")
          (.bin .add (.bin .mul (.var "$inl$1$x") (.lit (.int 10))) (.var "$inl$2$y")))
    let eColliding : Expr :=
      .let_ "$inl$0$x" (.cellGet (.loc 0))
        (wrapInlined2 "$inl$0$x" "$inl$0$y" (.lit (.int 2)) (.var "$inl$0$x")
          (.bin .add (.bin .mul (.var "$inl$0$x") (.lit (.int 10))) (.var "$inl$0$y")))
    Steps (fun _ => none) (fun _ => none) eFresh [.lit (.int 7)] (.lit (.int 27)) [.lit (.int 7)] ∧
    Steps (fun _ => none) (fun _ => none) eColliding [.lit (.int 7)] (.lit (.int 22)) [.lit (.int 7)] ∧
    ¬ ObsEquiv (fun _ => none) (fun _ => none) (fun _ => none) eFresh eColliding := by
  let eFresh : Expr :=
    .let_ "$inl$0$x" (.cellGet (.loc 0))
      (wrapInlined2 "$inl$1$x" "$inl$2$y" (.lit (.int 2)) (.var "$inl$0$x")
        (.bin .add (.bin .mul (.var "$inl$1$x") (.lit (.int 10))) (.var "$inl$2$y")))
  let eColliding : Expr :=
    .let_ "$inl$0$x" (.cellGet (.loc 0))
      (wrapInlined2 "$inl$0$x" "$inl$0$y" (.lit (.int 2)) (.var "$inl$0$x")
        (.bin .add (.bin .mul (.var "$inl$0$x") (.lit (.int 10))) (.var "$inl$0$y")))
  have h1 : Steps (fun _ => none) (fun _ => none) eFresh [.lit (.int 7)] (.lit (.int 27)) [.lit (.int 7)] :=
    .trans (.letStep (.cellGetVal (by rfl)))
      (.trans (.letVal (.lit _))
        (.trans (.letVal (.lit _))
          (.trans (.letVal (.lit _))
            (.trans (.binLeft (.binVal (by rfl)))
              (.single (.binVal (by rfl)))))))
  have h2 : Steps (fun _ => none) (fun _ => none) eColliding [.lit (.int 7)] (.lit (.int 22)) [.lit (.int 7)] :=
    .trans (.letStep (.cellGetVal (by rfl)))
      (.trans (.letVal (.lit _))
        (.trans (.letVal (.lit _))
          (.trans (.letVal (.lit _))
            (.trans (.binLeft (.binVal (by rfl)))
              (.single (.binVal (by rfl)))))))
  exact ⟨h1, h2, not_obsEquiv_of_distinct_terminals h1 (Or.inl (.lit _)) h2 (Or.inl (.lit _))
    (Or.inl (by rintro ⟨⟩))⟩

/-! ## Part 3: Strict Left-to-Right ANF Argument & Callee Lifting (`coFloatSelectedArgs`) -/

/-- Closed store invariant: every value stored in the heap has no free lexical variables. -/
def ClosedStore (σ : Store) : Prop :=
  ∀ v ∈ σ, freeVars v = []

/-- Closed top-level function table invariant: every `FunDef` body references only its declared parameters. -/
def ClosedFunEnv (Φ : FunEnv) : Prop :=
  ∀ name fd, Φ name = some fd → ∀ z ∈ freeVars fd.body, z ∈ fd.params.map Prod.fst

mutual
theorem subst_freeVars_subset (x : Ident) (v : Expr) (hv : freeVars v = []) :
    (e : Expr) → ∀ z ∈ freeVars (subst x v e), z ≠ x ∧ z ∈ freeVars e
  | .lit _, _, hz => by simp [subst, freeVars] at hz
  | .loc _, _, hz => by simp [subst, freeVars] at hz
  | .taskRef _, _, hz => by simp [subst, freeVars] at hz
  | .syncRef _ _, _, hz => by simp [subst, freeVars] at hz
  | .trap _, _, hz => by simp [subst, freeVars] at hz
  | .var y, z, hz => by
    simp only [subst] at hz
    by_cases hyx : (y == x) = true
    · simp [hyx, hv] at hz
    · simp only [hyx, Bool.false_eq_true, ↓reduceIte, freeVars, List.mem_singleton] at hz
      subst hz
      exact ⟨fun h => hyx (beq_iff_eq.mpr h), List.mem_singleton.mpr rfl⟩
  | .tuple es, z, hz => by
    simp only [subst, freeVars] at hz ⊢
    exact substList_freeVars_subset x v hv es z hz
  | .block es, z, hz => by
    simp only [subst, freeVars] at hz ⊢
    exact substList_freeVars_subset x v hv es z hz
  | .lam m ps ret body, z, hz => by
    simp only [subst] at hz
    by_cases hany : ps.any (fun p => p.1 == x) = true
    · simp only [hany, ↓reduceIte, freeVars, List.mem_filter] at hz
      refine ⟨?_, by simp [freeVars, hz.1, hz.2]⟩
      intro hzx; subst hzx; simp [hany] at hz
    · simp only [hany, Bool.false_eq_true, ↓reduceIte, freeVars, List.mem_filter] at hz
      rcases subst_freeVars_subset x v hv body z hz.1 with ⟨hne, hmem⟩
      exact ⟨hne, by simp [freeVars, hmem, hz.2]⟩
  | .apply fn args, z, hz => by
    simp only [subst, freeVars, List.mem_append] at hz ⊢
    rcases hz with hfn | hargs
    · rcases subst_freeVars_subset x v hv fn z hfn with ⟨hne, hm⟩
      exact ⟨hne, Or.inl hm⟩
    · rcases substList_freeVars_subset x v hv args z hargs with ⟨hne, hm⟩
      exact ⟨hne, Or.inr hm⟩
  | .applyDir fn args, z, hz => by
    simp only [subst, freeVars] at hz ⊢
    exact substList_freeVars_subset x v hv args z hz
  | .bin op e1 e2, z, hz => by
    simp only [subst, freeVars, List.mem_append] at hz ⊢
    rcases hz with h1 | h2
    · rcases subst_freeVars_subset x v hv e1 z h1 with ⟨hne, hm⟩
      exact ⟨hne, Or.inl hm⟩
    · rcases subst_freeVars_subset x v hv e2 z h2 with ⟨hne, hm⟩
      exact ⟨hne, Or.inr hm⟩
  | .un op e1, z, hz => by
    simp only [subst, freeVars] at hz ⊢
    exact subst_freeVars_subset x v hv e1 z hz
  | .let_ y e1 e2, z, hz => by
    simp only [subst] at hz
    by_cases hyx : (y == x) = true
    · have heqy : y = x := eq_of_beq hyx
      subst heqy
      simp only [beq_self_eq_true, ↓reduceIte, freeVars, List.mem_append, List.mem_filter, bne_iff_ne] at hz
      rcases hz with h1 | ⟨hm2, hne⟩
      · rcases subst_freeVars_subset y v hv e1 z h1 with ⟨hne, hm⟩
        exact ⟨hne, by simp [freeVars, hm]⟩
      · exact ⟨hne, by simp [freeVars, hm2, hne]⟩
    · simp only [hyx, Bool.false_eq_true, ↓reduceIte, freeVars, List.mem_append, List.mem_filter, bne_iff_ne] at hz
      rcases hz with h1 | ⟨hm2, hney⟩
      · rcases subst_freeVars_subset x v hv e1 z h1 with ⟨hne, hm⟩
        exact ⟨hne, by simp [freeVars, hm]⟩
      · rcases subst_freeVars_subset x v hv e2 z hm2 with ⟨hne, hm⟩
        exact ⟨hne, by simp [freeVars, hm, hney]⟩
  | .if_ c t e2, z, hz => by
    simp only [subst, freeVars, List.mem_append] at hz ⊢
    rcases hz with (hc | ht) | he
    · rcases subst_freeVars_subset x v hv c z hc with ⟨hne, hm⟩; exact ⟨hne, Or.inl (Or.inl hm)⟩
    · rcases subst_freeVars_subset x v hv t z ht with ⟨hne, hm⟩; exact ⟨hne, Or.inl (Or.inr hm)⟩
    · rcases subst_freeVars_subset x v hv e2 z he with ⟨hne, hm⟩; exact ⟨hne, Or.inr hm⟩
  | .while_ c b, z, hz => by
    simp only [subst, freeVars, List.mem_append] at hz ⊢
    rcases hz with hc | hb
    · rcases subst_freeVars_subset x v hv c z hc with ⟨hne, hm⟩; exact ⟨hne, Or.inl hm⟩
    · rcases subst_freeVars_subset x v hv b z hb with ⟨hne, hm⟩; exact ⟨hne, Or.inr hm⟩
  | .match_ s arms, z, hz => by
    simp only [subst, freeVars, List.mem_append] at hz ⊢
    rcases hz with hs | ha
    · rcases subst_freeVars_subset x v hv s z hs with ⟨hne, hm⟩; exact ⟨hne, Or.inl hm⟩
    · rcases substArms_freeVars_subset x v hv arms z ha with ⟨hne, hm⟩; exact ⟨hne, Or.inr hm⟩
  | .makeData adt tag es, z, hz => by
    simp only [subst, freeVars] at hz ⊢
    exact substList_freeVars_subset x v hv es z hz
  | .getTag e1, z, hz => by
    simp only [subst, freeVars] at hz ⊢
    exact subst_freeVars_subset x v hv e1 z hz
  | .cellNew e1, z, hz => by
    simp only [subst, freeVars] at hz ⊢
    exact subst_freeVars_subset x v hv e1 z hz
  | .cellGet e1, z, hz => by
    simp only [subst, freeVars] at hz ⊢
    exact subst_freeVars_subset x v hv e1 z hz
  | .cellSet e1 e2, z, hz => by
    simp only [subst, freeVars, List.mem_append] at hz ⊢
    rcases hz with h1 | h2
    · rcases subst_freeVars_subset x v hv e1 z h1 with ⟨hne, hm⟩; exact ⟨hne, Or.inl hm⟩
    · rcases subst_freeVars_subset x v hv e2 z h2 with ⟨hne, hm⟩; exact ⟨hne, Or.inr hm⟩
  | .spawn e1, z, hz => by
    simp only [subst, freeVars] at hz ⊢
    exact subst_freeVars_subset x v hv e1 z hz
  | .await e1, z, hz => by
    simp only [subst, freeVars] at hz ⊢
    exact subst_freeVars_subset x v hv e1 z hz
  | .concPrim op args, z, hz => by
    simp only [subst, freeVars] at hz ⊢
    exact substList_freeVars_subset x v hv args z hz
termination_by e => sizeOf e

theorem substList_freeVars_subset (x : Ident) (v : Expr) (hv : freeVars v = []) :
    (es : List Expr) → ∀ z ∈ freeVarsList (substList x v es), z ≠ x ∧ z ∈ freeVarsList es
  | [], _, hz => by simp [substList, freeVarsList] at hz
  | e :: rest, z, hz => by
    simp only [substList, freeVarsList, List.mem_append] at hz ⊢
    rcases hz with h1 | hr
    · rcases subst_freeVars_subset x v hv e z h1 with ⟨hne, hm⟩; exact ⟨hne, Or.inl hm⟩
    · rcases substList_freeVars_subset x v hv rest z hr with ⟨hne, hm⟩; exact ⟨hne, Or.inr hm⟩
termination_by es => sizeOf es

theorem substArms_freeVars_subset (x : Ident) (v : Expr) (hv : freeVars v = []) :
    (arms : List (Pat × Expr)) → ∀ z ∈ freeVarsArms (substArms x v arms), z ≠ x ∧ z ∈ freeVarsArms arms
  | [], _, hz => by simp [substArms, freeVarsArms] at hz
  | (p, body) :: rest, z, hz => by
    simp only [substArms, freeVarsArms, List.mem_append, List.mem_filter] at hz ⊢
    rcases hz with ⟨hb, hnotp⟩ | hr
    · by_cases hpx : (patBoundNames p).contains x = true
      · simp only [hpx, ↓reduceIte] at hb
        refine ⟨?_, Or.inl ⟨hb, hnotp⟩⟩
        intro hzx; subst hzx; rw [hpx] at hnotp; simp at hnotp
      · simp only [hpx, Bool.false_eq_true, ↓reduceIte] at hb
        rcases subst_freeVars_subset x v hv body z hb with ⟨hne, hm⟩
        exact ⟨hne, Or.inl ⟨hm, hnotp⟩⟩
    · rcases substArms_freeVars_subset x v hv rest z hr with ⟨hne, hm⟩
      exact ⟨hne, Or.inr hm⟩
termination_by arms => sizeOf arms
end

theorem substMany_freeVars_subset (ρ : List (Ident × Expr)) (hρ : ∀ p ∈ ρ, freeVars p.2 = [])
    (e : Expr) :
    ∀ z ∈ freeVars (substMany ρ e), z ∉ ρ.map Prod.fst ∧ z ∈ freeVars e := by
  induction ρ generalizing e with
  | nil => intro z hz; exact ⟨by simp, hz⟩
  | cons p rest ih =>
    rcases p with ⟨x, v⟩
    intro z hz
    simp only [substMany] at hz
    have hrest : ∀ q ∈ rest, freeVars q.2 = [] := fun q hq => hρ q (List.mem_cons_of_mem _ hq)
    have hv : freeVars v = [] := hρ (x, v) (List.mem_cons_self ..)
    rcases ih hrest (subst x v e) z hz with ⟨hnotr, hsub⟩
    rcases subst_freeVars_subset x v hv e z hsub with ⟨hne, hmem⟩
    exact ⟨by simp [hne, hnotr], hmem⟩

theorem freeVarsList_eq_nil_iff {es : List Expr} :
    freeVarsList es = [] ↔ ∀ e ∈ es, freeVars e = [] := by
  induction es with
  | nil => simp [freeVarsList]
  | cons a rest ih =>
    simp only [freeVarsList, List.append_eq_nil_iff, ih, List.mem_cons]
    constructor
    · rintro ⟨ha, hr⟩ x (rfl | hx)
      · exact ha
      · exact hr x hx
    · intro hall
      exact ⟨hall a (Or.inl rfl), fun x hx => hall x (Or.inr hx)⟩

mutual
theorem matchPat_closed {p : Pat} {v : Expr} {env : List (Ident × Expr)}
    (hv : freeVars v = []) (hm : matchPat p v = some env) :
    (∀ q ∈ env, freeVars q.2 = []) ∧ ∀ z ∈ patBoundNames p, z ∈ env.map Prod.fst := by
  cases p with
  | wild =>
    simp only [matchPat] at hm; injection hm with hm; subst hm
    simp [patBoundNames]
  | var x =>
    simp only [matchPat] at hm; injection hm with hm; subst hm
    exact ⟨fun q hq => by simp at hq; rcases hq with ⟨_, rfl⟩; exact hv, by simp [patBoundNames]⟩
  | lit l =>
    cases v <;> simp [matchPat] at hm
    rcases hm with ⟨_, rfl⟩; simp [patBoundNames]
  | tuple ps =>
    cases v <;> simp [matchPat] at hm
    simp only [patBoundNames]
    exact matchPats_closed hv hm
  | ctor adt1 tag1 ps =>
    cases v <;> simp [matchPat] at hm
    simp only [patBoundNames]
    exact matchPats_closed hv hm.2
termination_by sizeOf p

theorem matchPats_closed {ps : List Pat} {vs : List Expr} {env : List (Ident × Expr)}
    (hvs : freeVarsList vs = []) (hm : matchPats ps vs = some env) :
    (∀ q ∈ env, freeVars q.2 = []) ∧
      ∀ z ∈ ps.foldr (fun p acc => patBoundNames p ++ acc) [], z ∈ env.map Prod.fst := by
  cases ps with
  | nil =>
    cases vs <;> simp [matchPats] at hm
    subst hm; simp
  | cons p pr =>
    cases vs with
    | nil => simp [matchPats] at hm
    | cons v vr =>
      simp only [freeVarsList, List.append_eq_nil_iff] at hvs
      simp only [matchPats] at hm
      cases h1 : matchPat p v with
      | none => rw [h1] at hm; cases hm
      | some b1 =>
        cases h2 : matchPats pr vr with
        | none => rw [h1, h2] at hm; cases hm
        | some b2 =>
          rw [h1, h2] at hm; injection hm with hm; subst hm
          rcases matchPat_closed hvs.1 h1 with ⟨hc1, hb1⟩
          rcases matchPats_closed hvs.2 h2 with ⟨hc2, hb2⟩
          refine ⟨fun q hq => ?_, fun z hz => ?_⟩
          · rcases List.mem_append.mp hq with hq1 | hq2
            · exact hc1 q hq1
            · exact hc2 q hq2
          · simp only [List.foldr_cons, List.mem_append] at hz
            simp only [List.map_append, List.mem_append]
            rcases hz with hz1 | hz2
            · exact Or.inl (hb1 z hz1)
            · exact Or.inr (hb2 z hz2)
termination_by sizeOf ps
end

theorem zipParams_closed {ps : List (Ident × Ty)} {vs : List Expr}
    (hvs : ∀ v ∈ vs, freeVars v = []) :
    ∀ p ∈ zipParams ps vs, freeVars p.2 = [] := by
  induction ps generalizing vs with
  | nil => intro p hp; simp [zipParams] at hp
  | cons pd pr ih =>
    cases vs with
    | nil => intro p hp; simp [zipParams] at hp
    | cons v vr =>
      intro p hp
      simp only [zipParams, List.map_cons, List.zip_cons_cons, List.mem_cons] at hp
      rcases hp with rfl | hrest
      · exact hvs v (List.mem_cons_self ..)
      · exact ih (fun w hw => hvs w (List.mem_cons_of_mem _ hw)) p hrest

theorem zipParams_fst_eq {ps : List (Ident × Ty)} {vs : List Expr}
    (hlen : vs.length = ps.length) :
    (zipParams ps vs).map Prod.fst = ps.map Prod.fst := by
  induction ps generalizing vs with
  | nil => cases vs <;> simp [zipParams] at hlen ⊢
  | cons pd pr ih =>
    cases vs with
    | nil => simp at hlen
    | cons v vr =>
      simp only [List.length_cons, Nat.succ.injEq] at hlen
      have hrec := ih hlen
      simp only [zipParams] at hrec ⊢
      simp [hrec]

mutual
/-- Sequential `Step` preserves closedness of both expression and `Store`. -/
theorem step_preserves_closed {Δ : AdtEnv} {Φ : FunEnv}
    {e e' : Expr} {σ σ' : Store}
    (hΦ : ClosedFunEnv Φ) (hσ : ClosedStore σ) (he : freeVars e = [])
    (hs : Step Δ Φ emptyPool e σ e' σ' .none) :
    freeVars e' = [] ∧ ClosedStore σ' := by
  cases hs with
  | tupleStep hsl =>
    simp only [freeVars] at he
    rcases stepList_preserves_closed hΦ hσ he hsl with ⟨hl, hσ'⟩
    exact ⟨hl, hσ'⟩
  | tupleTrap _ => exact ⟨rfl, hσ⟩
  | blockEmpty => exact ⟨rfl, hσ⟩
  | blockSingle =>
    simp only [freeVars, freeVarsList, List.append_nil] at he
    exact ⟨he, hσ⟩
  | blockConsStep hs1 =>
    simp only [freeVars, freeVarsList, List.append_eq_nil_iff] at he
    rcases step_preserves_closed hΦ hσ he.1 hs1 with ⟨he1', hσ'⟩
    exact ⟨by simp [freeVars, freeVarsList, he1', he.2.1, he.2.2], hσ'⟩
  | blockConsVal _ =>
    simp only [freeVars, freeVarsList, List.append_eq_nil_iff] at he
    exact ⟨by simp [freeVars, freeVarsList, he.2.1, he.2.2], hσ⟩
  | blockConsTrap => exact ⟨rfl, hσ⟩
  | applyFn hs1 =>
    simp only [freeVars, List.append_eq_nil_iff] at he
    rcases step_preserves_closed hΦ hσ he.1 hs1 with ⟨hfn', hσ'⟩
    exact ⟨by simp [freeVars, hfn', he.2], hσ'⟩
  | applyFnTrap => exact ⟨rfl, hσ⟩
  | applyArgs _ hsl =>
    simp only [freeVars, List.append_eq_nil_iff] at he
    rcases stepList_preserves_closed hΦ hσ he.2 hsl with ⟨hl, hσ'⟩
    exact ⟨by simp [freeVars, he.1, hl], hσ'⟩
  | applyArgsTrap _ _ => exact ⟨rfl, hσ⟩
  | @applyBeta _ ps _ body args _ _ hlen =>
    simp only [freeVars, List.append_eq_nil_iff] at he
    have hargs : ∀ a ∈ args, freeVars a = [] := freeVarsList_eq_nil_iff.mp he.2
    refine ⟨List.eq_nil_iff_forall_not_mem.mpr fun z hz => ?_, hσ⟩
    rcases substMany_freeVars_subset (zipParams ps args) (zipParams_closed hargs) body z hz with ⟨hnot, hzb⟩
    rw [zipParams_fst_eq hlen] at hnot
    have hlam := List.eq_nil_iff_forall_not_mem.mp he.1 z
    apply hlam
    simp only [List.mem_filter, hzb, true_and, Bool.not_eq_true']
    cases hany : ps.any (fun p => p.1 == z)
    · rfl
    · rcases List.any_eq_true.mp hany with ⟨p, hp, hpz⟩
      exact False.elim (hnot (List.mem_map.mpr ⟨p, hp, eq_of_beq hpz⟩))
  | applyDirArgs hsl =>
    simp only [freeVars] at he
    rcases stepList_preserves_closed hΦ hσ he hsl with ⟨hl, hσ'⟩
    exact ⟨hl, hσ'⟩
  | applyDirTrap _ => exact ⟨rfl, hσ⟩
  | @applyDirBeta name fd args _ hfn _ hlen =>
    simp only [freeVars] at he
    have hargs : ∀ a ∈ args, freeVars a = [] := freeVarsList_eq_nil_iff.mp he
    refine ⟨List.eq_nil_iff_forall_not_mem.mpr fun z hz => ?_, hσ⟩
    rcases substMany_freeVars_subset (zipParams fd.params args) (zipParams_closed hargs) fd.body z hz with ⟨hnot, hzb⟩
    rw [zipParams_fst_eq hlen] at hnot
    exact hnot (hΦ name fd hfn z hzb)
  | unStep hs1 =>
    simp only [freeVars] at he
    rcases step_preserves_closed hΦ hσ he hs1 with ⟨he1', hσ'⟩
    exact ⟨he1', hσ'⟩
  | unTrap | unVal _ => exact ⟨rfl, hσ⟩
  | binLeft hs1 =>
    simp only [freeVars, List.append_eq_nil_iff] at he
    rcases step_preserves_closed hΦ hσ he.1 hs1 with ⟨he1', hσ'⟩
    exact ⟨by simp [freeVars, he1', he.2], hσ'⟩
  | binLeftTrap | binAndFalse | binOrTrue | binRightTrap _ _ _ | binVal _ | binTrap _ =>
    exact ⟨rfl, hσ⟩
  | binAndTrue | binOrFalse =>
    simp only [freeVars, List.append_eq_nil_iff] at he
    exact ⟨he.2, hσ⟩
  | binRight _ _ _ hs2 =>
    simp only [freeVars, List.append_eq_nil_iff] at he
    rcases step_preserves_closed hΦ hσ he.2 hs2 with ⟨he2', hσ'⟩
    exact ⟨by simp [freeVars, he.1, he2'], hσ'⟩
  | letStep hs1 =>
    simp only [freeVars, List.append_eq_nil_iff] at he
    rcases step_preserves_closed hΦ hσ he.1 hs1 with ⟨he1', hσ'⟩
    exact ⟨by simp [freeVars, he1', he.2], hσ'⟩
  | letTrap => exact ⟨rfl, hσ⟩
  | @letVal x v1 e2 _ _ =>
    simp only [freeVars, List.append_eq_nil_iff] at he
    refine ⟨List.eq_nil_iff_forall_not_mem.mpr fun z hz => ?_, hσ⟩
    rcases subst_freeVars_subset x v1 he.1 e2 z hz with ⟨hne, hm⟩
    have h2 := List.eq_nil_iff_forall_not_mem.mp he.2 z
    exact h2 (List.mem_filter.mpr ⟨hm, bne_iff_ne.mpr hne⟩)
  | ifStep hs1 =>
    simp only [freeVars, List.append_eq_nil_iff] at he
    rcases step_preserves_closed hΦ hσ he.1.1 hs1 with ⟨hc', hσ'⟩
    exact ⟨by simp [freeVars, hc', he.1.2, he.2], hσ'⟩
  | ifTrap => exact ⟨rfl, hσ⟩
  | ifTrue =>
    simp only [freeVars, List.append_eq_nil_iff] at he
    exact ⟨he.1.2, hσ⟩
  | ifFalse =>
    simp only [freeVars, List.append_eq_nil_iff] at he
    exact ⟨he.2, hσ⟩
  | whileUnfold =>
    simp only [freeVars, List.append_eq_nil_iff] at he
    exact ⟨by simp [freeVars, freeVarsList, he.1, he.2], hσ⟩
  | matchScrut hs1 =>
    simp only [freeVars, List.append_eq_nil_iff] at he
    rcases step_preserves_closed hΦ hσ he.1 hs1 with ⟨hs', hσ'⟩
    exact ⟨by simp [freeVars, hs', he.2], hσ'⟩
  | matchScrutTrap | matchEmpty _ => exact ⟨rfl, hσ⟩
  | @matchHit v p body rest env _ _ hm =>
    simp only [freeVars, freeVarsArms, List.append_eq_nil_iff] at he
    rcases matchPat_closed he.1 hm with ⟨henv, hcov⟩
    refine ⟨List.eq_nil_iff_forall_not_mem.mpr fun z hz => ?_, hσ⟩
    rcases substMany_freeVars_subset env henv body z hz with ⟨hnot, hzb⟩
    have harm := List.eq_nil_iff_forall_not_mem.mp he.2.1 z
    apply harm
    simp only [List.mem_filter, hzb, true_and, Bool.not_eq_true', List.contains_eq_mem,
      decide_eq_false_iff_not]
    exact fun hp => hnot (hcov z hp)
  | matchMiss _ _ =>
    simp only [freeVars, freeVarsArms, List.append_eq_nil_iff] at he
    exact ⟨by simp [freeVars, he.1, he.2.2], hσ⟩
  | makeDataStep hsl =>
    simp only [freeVars] at he
    rcases stepList_preserves_closed hΦ hσ he hsl with ⟨hl, hσ'⟩
    exact ⟨hl, hσ'⟩
  | makeDataTrap _ => exact ⟨rfl, hσ⟩
  | getTagStep hs1 =>
    simp only [freeVars] at he
    rcases step_preserves_closed hΦ hσ he hs1 with ⟨he1', hσ'⟩
    exact ⟨he1', hσ'⟩
  | getTagTrap | getTagVal _ => exact ⟨rfl, hσ⟩
  | cellNewStep hs1 =>
    simp only [freeVars] at he
    rcases step_preserves_closed hΦ hσ he hs1 with ⟨he1', hσ'⟩
    exact ⟨he1', hσ'⟩
  | cellNewTrap => exact ⟨rfl, hσ⟩
  | cellNewVal _ =>
    simp only [freeVars] at he
    refine ⟨rfl, fun w hw => ?_⟩
    rcases List.mem_append.mp hw with hwσ | hwe
    · exact hσ w hwσ
    · simp at hwe; subst hwe; exact he
  | cellGetStep hs1 =>
    simp only [freeVars] at he
    rcases step_preserves_closed hΦ hσ he hs1 with ⟨he1', hσ'⟩
    exact ⟨he1', hσ'⟩
  | cellGetTrap => exact ⟨rfl, hσ⟩
  | cellGetVal hl =>
    exact ⟨hσ _ (List.mem_of_getElem? hl), hσ⟩
  | cellSetLeft hs1 =>
    simp only [freeVars, List.append_eq_nil_iff] at he
    rcases step_preserves_closed hΦ hσ he.1 hs1 with ⟨he1', hσ'⟩
    exact ⟨by simp [freeVars, he1', he.2], hσ'⟩
  | cellSetLeftTrap | cellSetRightTrap _ => exact ⟨rfl, hσ⟩
  | cellSetRight _ hs2 =>
    simp only [freeVars, List.append_eq_nil_iff] at he
    rcases step_preserves_closed hΦ hσ he.2 hs2 with ⟨he2', hσ'⟩
    exact ⟨by simp [freeVars, he.1, he2'], hσ'⟩
  | @cellSetVal l v _ _ _ =>
    simp only [freeVars, List.append_eq_nil_iff] at he
    refine ⟨rfl, fun w hw => ?_⟩
    rcases List.mem_or_eq_of_mem_set hw with hwσ | rfl
    · exact hσ w hwσ
    · exact he.2
  | spawnStep hs1 =>
    simp only [freeVars] at he
    rcases step_preserves_closed hΦ hσ he hs1 with ⟨he1', hσ'⟩
    exact ⟨he1', hσ'⟩
  | spawnTrap | awaitTrap | concPrimTrap _ => exact ⟨rfl, hσ⟩
  | awaitStep hs1 =>
    simp only [freeVars] at he
    rcases step_preserves_closed hΦ hσ he hs1 with ⟨he1', hσ'⟩
    exact ⟨he1', hσ'⟩
  | awaitVal h _ | awaitTaskTrap h => simp [emptyPool] at h
  | concPrimArgs hsl =>
    simp only [freeVars] at he
    rcases stepList_preserves_closed hΦ hσ he hsl with ⟨hl, hσ'⟩
    exact ⟨hl, hσ'⟩
  | concPrimVal hc => exact False.elim (stepConcPrim_emptyPool_none_false hc)
termination_by sizeOf e

theorem stepList_preserves_closed {Δ : AdtEnv} {Φ : FunEnv}
    {es es' : List Expr} {σ σ' : Store}
    (hΦ : ClosedFunEnv Φ) (hσ : ClosedStore σ) (hes : freeVarsList es = [])
    (hsl : StepList Δ Φ emptyPool es σ es' σ' .none) :
    freeVarsList es' = [] ∧ ClosedStore σ' := by
  cases hsl with
  | head hs =>
    simp only [freeVarsList, List.append_eq_nil_iff] at hes
    rcases step_preserves_closed hΦ hσ hes.1 hs with ⟨he', hσ'⟩
    exact ⟨by simp [freeVarsList, he', hes.2], hσ'⟩
  | tail _ hsl' =>
    simp only [freeVarsList, List.append_eq_nil_iff] at hes
    rcases stepList_preserves_closed hΦ hσ hes.2 hsl' with ⟨hl', hσ'⟩
    exact ⟨by simp [freeVarsList, hes.1, hl'], hσ'⟩
termination_by sizeOf es
end

theorem steps_preserves_closed {Δ : AdtEnv} {Φ : FunEnv}
    {e e' : Expr} {σ σ' : Store}
    (hΦ : ClosedFunEnv Φ) (hσ : ClosedStore σ) (he : freeVars e = [])
    (hsteps : Steps Δ Φ e σ e' σ') :
    freeVars e' = [] ∧ ClosedStore σ' := by
  induction hsteps with
  | refl => exact ⟨he, hσ⟩
  | trans hs _ ih =>
    rcases step_preserves_closed hΦ hσ he hs with ⟨he1, hσ1⟩
    exact ih hσ1 he1

/-- Prefix value helpers for `StepList` and `ListFirstTrap`. -/
theorem stepList_prepend_vals_inv {Δ : AdtEnv} {Φ : FunEnv} {pool : ConcPool}
    {vs es full' : List Expr} {σ σ' : Store} {eff : ConcEff}
    (hvs : ∀ v ∈ vs, IsValue v)
    (h : StepList Δ Φ pool (vs ++ es) σ full' σ' eff) :
    ∃ es', full' = vs ++ es' ∧ StepList Δ Φ pool es σ es' σ' eff := by
  induction vs generalizing full' with
  | nil => exact ⟨full', rfl, h⟩
  | cons v vr ih =>
    have hv : IsValue v := hvs v (List.mem_cons_self ..)
    have hvr : ∀ w ∈ vr, IsValue w := fun w hw => hvs w (List.mem_cons_of_mem _ hw)
    cases h with
    | head hs => exact False.elim (isValue_no_step hv hs)
    | tail _ hsl =>
      rcases ih hvr hsl with ⟨es', rfl, hsl'⟩
      exact ⟨es', rfl, hsl'⟩

theorem stepList_prepend_vals_forward {Δ : AdtEnv} {Φ : FunEnv} {pool : ConcPool}
    {vs es es' : List Expr} {σ σ' : Store} {eff : ConcEff}
    (hvs : ∀ v ∈ vs, IsValue v)
    (hsl : StepList Δ Φ pool es σ es' σ' eff) :
    StepList Δ Φ pool (vs ++ es) σ (vs ++ es') σ' eff := by
  induction vs with
  | nil => exact hsl
  | cons v vr ih =>
    exact .tail (hvs v (List.mem_cons_self ..))
      (ih (fun w hw => hvs w (List.mem_cons_of_mem _ hw)))

theorem stepList_prepend_vals_iff {Δ : AdtEnv} {Φ : FunEnv} {pool : ConcPool}
    {vs es es' : List Expr} {σ σ' : Store} {eff : ConcEff}
    (hvs : ∀ v ∈ vs, IsValue v) :
    StepList Δ Φ pool (vs ++ es) σ (vs ++ es') σ' eff ↔
      StepList Δ Φ pool es σ es' σ' eff := by
  constructor
  · intro h
    rcases stepList_prepend_vals_inv hvs h with ⟨es'', heq, hsl⟩
    rcases List.append_cancel_left heq.symm with rfl
    exact hsl
  · exact stepList_prepend_vals_forward hvs

theorem listFirstTrap_prepend_vals_iff {vs es : List Expr} {t : Trap}
    (hvs : ∀ v ∈ vs, IsValue v) :
    ListFirstTrap (vs ++ es) t ↔ ListFirstTrap es t := by
  induction vs with
  | nil => exact Iff.rfl
  | cons v vr ih =>
    have hv : IsValue v := hvs v (List.mem_cons_self ..)
    have hvr : ∀ w ∈ vr, IsValue w := fun w hw => hvs w (List.mem_cons_of_mem _ hw)
    constructor
    · intro h
      cases h with
      | head _ _ => exact False.elim (isValue_ne_trap hv _ rfl)
      | tail _ htr => exact (ih hvr).mp htr
    · intro h
      exact .tail hv ((ih hvr).mpr h)

theorem Steps.applyDirArgCongr {Δ : AdtEnv} {Φ : FunEnv}
    {fn : Ident} {vs er : List Expr} {e e' : Expr} {σ1 σ2 : Store}
    (hvs : ∀ v ∈ vs, IsValue v) (h : Steps Δ Φ e σ1 e' σ2) :
    Steps Δ Φ (.applyDir fn (vs ++ e :: er)) σ1 (.applyDir fn (vs ++ e' :: er)) σ2 := by
  induction h with
  | refl => exact .refl _ _
  | trans hs _ ih =>
    exact .trans (.applyDirArgs (stepList_prepend_vals_forward hvs (.head hs))) ih

/-- Exact operational decomposition of evaluating the next non-value argument in `.applyDir fn (vs ++ e :: er)`. -/
theorem steps_applyDir_next_arg_iff {Δ : AdtEnv} {Φ : FunEnv}
    {fn : Ident} {vs er : List Expr} {e out : Expr} {σ σ' : Store}
    (hout : IsTerminal out) (hvs : ∀ v ∈ vs, IsValue v) :
    Steps Δ Φ (.applyDir fn (vs ++ e :: er)) σ out σ' ↔
      (∃ t, out = .trap t ∧ Steps Δ Φ e σ (.trap t) σ') ∨
      (∃ v σ1, IsValue v ∧ Steps Δ Φ e σ v σ1 ∧
        Steps Δ Φ (.applyDir fn ((vs ++ [v]) ++ er)) σ1 out σ') := by
  constructor
  · intro h
    generalize hcall : Expr.applyDir fn (vs ++ e :: er) = full at h
    induction h generalizing e with
    | refl =>
      subst hcall
      rcases hout with hv | ⟨t, htr⟩
      · cases hv
      · cases htr
    | trans hs hrest ih =>
      subst hcall
      cases hs with
      | applyDirArgs hsl =>
        rcases stepList_prepend_vals_inv hvs hsl with ⟨es', heq, hsl_er⟩
        subst heq
        cases hsl_er with
        | head hs_e =>
          rcases ih hout rfl with ⟨t, rfl, htr⟩ | ⟨v, σ1, hv, hs_v, hs_tail⟩
          · exact Or.inl ⟨t, rfl, .trans hs_e htr⟩
          · exact Or.inr ⟨v, σ1, hv, .trans hs_e hs_v, hs_tail⟩
        | tail hv_e _ =>
          refine Or.inr ⟨e, _, hv_e, .refl _ _, ?_⟩
          rw [List.append_assoc, List.singleton_append]
          exact .trans (.applyDirArgs hsl) hrest
      | @applyDirTrap _ _ tr _ htr =>
        have htr_er := (listFirstTrap_prepend_vals_iff hvs).mp htr
        cases htr_er with
        | head _ _ =>
          rcases steps_of_isTerminal (Or.inr ⟨_, rfl⟩) hrest with ⟨rfl, rfl⟩
          exact Or.inl ⟨tr, rfl, .refl _ _⟩
        | tail hv_e htr_rest =>
          refine Or.inr ⟨e, _, hv_e, .refl _ _, ?_⟩
          have hvs' : ∀ w ∈ vs ++ [e], IsValue w := by
            intro w hw
            rcases List.mem_append.mp hw with hwv | hwe
            · exact hvs w hwv
            · simp at hwe; subst hwe; exact hv_e
          have htr_full : ListFirstTrap ((vs ++ [e]) ++ er) tr :=
            (listFirstTrap_prepend_vals_iff hvs').mpr htr_rest
          exact .trans (.applyDirTrap htr_full) hrest
      | applyDirBeta hfn hall hlen =>
        have hv_e : IsValue e := hall e (by simp)
        refine Or.inr ⟨e, _, hv_e, .refl _ _, ?_⟩
        rw [List.append_assoc, List.singleton_append]
        exact .trans (.applyDirBeta hfn hall hlen) hrest
  · intro h
    rcases h with ⟨t, rfl, htr⟩ | ⟨v, σ1, _, hs_v, hs_tail⟩
    · have htr_full : ListFirstTrap (vs ++ .trap t :: er) t :=
        (listFirstTrap_prepend_vals_iff hvs).mpr (.head t er)
      exact Steps.append (Steps.applyDirArgCongr hvs htr) (Steps.single (.applyDirTrap htr_full))
    · rw [List.append_assoc, List.singleton_append] at hs_tail
      exact Steps.append (Steps.applyDirArgCongr hvs hs_v) hs_tail

/-- Left-to-right ANF argument lifter mirroring `coFloatSelectedArgs` for direct calls (`TmApplyDir`). -/
def anfLiftDirAux (xs : List Ident) (args : List Expr) (fn : Ident) (acc : List Expr) : Expr :=
  match xs, args with
  | x :: xr, e :: er => .let_ x e (anfLiftDirAux xr er fn (acc ++ [.var x]))
  | _, _ => .applyDir fn acc

def anfLiftApplyDir (xs : List Ident) (fn : Ident) (args : List Expr) : Expr :=
  anfLiftDirAux xs args fn []

theorem subst_anfLiftDirAux (x : Ident) (v : Expr) (xr : List Ident) (er : List Expr)
    (fn : Ident) (acc : List Expr)
    (hx_xr : x ∉ xr) (hx_er : ∀ e ∈ er, x ∉ freeVars e) :
    subst x v (anfLiftDirAux xr er fn acc) =
      anfLiftDirAux xr er fn (substList x v acc) := by
  induction xr generalizing er acc with
  | nil => simp [anfLiftDirAux, subst]
  | cons y yr ih =>
    cases er with
    | nil => simp [anfLiftDirAux, subst]
    | cons e rest =>
      simp only [List.mem_cons, not_or] at hx_xr
      have he : x ∉ freeVars e := hx_er e (List.mem_cons_self ..)
      have hrest : ∀ a ∈ rest, x ∉ freeVars a := fun a ha => hx_er a (List.mem_cons_of_mem _ ha)
      have hyx : (y == x) = false := beq_false_of_ne (Ne.symm hx_xr.1)
      have hsub_acc : substList x v (acc ++ [.var y]) = substList x v acc ++ [.var y] := by
        induction acc with
        | nil => simp [substList, subst, hyx]
        | cons a ar iha => simp [substList, iha]
      simp only [anfLiftDirAux, subst, hyx, Bool.false_eq_true, ↓reduceIte,
        subst_not_mem_freeVars e he, ih rest (acc ++ [.var y]) hx_xr.2 hrest, hsub_acc]

theorem substList_closed_append_self (x : Ident) (v : Expr) (vs : List Expr)
    (hvs : ∀ w ∈ vs, freeVars w = []) :
    substList x v (vs ++ [.var x]) = vs ++ [v] := by
  induction vs with
  | nil => simp [substList, subst]
  | cons w wr ih =>
    have hw : x ∉ freeVars w := by simp [hvs w (List.mem_cons_self ..)]
    simp [substList, subst_not_mem_freeVars w hw,
      ih (fun u hu => hvs u (List.mem_cons_of_mem _ hu))]

private theorem anfLiftDirAux_equiv_closed {Δ : AdtEnv} {Φ : FunEnv}
    (hΦ : ClosedFunEnv Φ) {xs : List Ident} {args vs : List Expr} {fn : Ident}
    {σ σ' : Store} {out : Expr}
    (hσ : ClosedStore σ) (hout : IsTerminal out)
    (hnodup : xs.Nodup) (hlen : xs.length = args.length)
    (hargs : ∀ e ∈ args, freeVars e = [])
    (hvs_val : ∀ v ∈ vs, IsValue v) (hvs_cl : ∀ v ∈ vs, freeVars v = []) :
    Steps Δ Φ (anfLiftDirAux xs args fn vs) σ out σ' ↔
      Steps Δ Φ (.applyDir fn (vs ++ args)) σ out σ' := by
  induction xs generalizing args vs σ with
  | nil =>
    cases args with
    | nil => simp [anfLiftDirAux]
    | cons _ _ => simp at hlen
  | cons x xr ih =>
    cases args with
    | nil => simp at hlen
    | cons e er =>
      simp only [List.length_cons, Nat.succ.injEq] at hlen
      rcases List.nodup_cons.mp hnodup with ⟨hx_xr, hnodup_xr⟩
      have he_cl : freeVars e = [] := hargs e (List.mem_cons_self ..)
      have her_cl : ∀ a ∈ er, freeVars a = [] := fun a ha => hargs a (List.mem_cons_of_mem _ ha)
      have hx_er : ∀ a ∈ er, x ∉ freeVars a := fun a ha => by simp [her_cl a ha]
      have hsub_eq : ∀ v, subst x v (anfLiftDirAux xr er fn (vs ++ [.var x])) =
          anfLiftDirAux xr er fn (vs ++ [v]) := by
        intro v
        rw [subst_anfLiftDirAux x v xr er fn (vs ++ [Expr.var x]) hx_xr hx_er,
            substList_closed_append_self x v vs hvs_cl]
      simp only [anfLiftDirAux]
      rw [steps_let_terminal_iff hout, steps_applyDir_next_arg_iff hout hvs_val]
      apply or_congr Iff.rfl
      constructor
      · rintro ⟨v, σ1, hv, hs_v, hs_rest⟩
        rcases steps_preserves_closed hΦ hσ he_cl hs_v with ⟨hv_cl, hσ1⟩
        rw [hsub_eq v] at hs_rest
        have hvs_val' : ∀ w ∈ vs ++ [v], IsValue w := by
          intro w hw; rcases List.mem_append.mp hw with h1 | h2
          · exact hvs_val w h1
          · simp at h2; subst h2; exact hv
        have hvs_cl' : ∀ w ∈ vs ++ [v], freeVars w = [] := by
          intro w hw; rcases List.mem_append.mp hw with h1 | h2
          · exact hvs_cl w h1
          · simp at h2; subst h2; exact hv_cl
        exact ⟨v, σ1, hv, hs_v,
          (ih hσ1 hnodup_xr hlen her_cl hvs_val' hvs_cl').mp hs_rest⟩
      · rintro ⟨v, σ1, hv, hs_v, hs_rest⟩
        rcases steps_preserves_closed hΦ hσ he_cl hs_v with ⟨hv_cl, hσ1⟩
        have hvs_val' : ∀ w ∈ vs ++ [v], IsValue w := by
          intro w hw; rcases List.mem_append.mp hw with h1 | h2
          · exact hvs_val w h1
          · simp at h2; subst h2; exact hv
        have hvs_cl' : ∀ w ∈ vs ++ [v], freeVars w = [] := by
          intro w hw; rcases List.mem_append.mp hw with h1 | h2
          · exact hvs_cl w h1
          · simp at h2; subst h2; exact hv_cl
        refine ⟨v, σ1, hv, hs_v, ?_⟩
        rw [hsub_eq v]
        exact (ih hσ1 hnodup_xr hlen her_cl hvs_val' hvs_cl').mpr hs_rest

/-- **Soundness of Strict Left-to-Right ANF Argument Lifting on Direct Calls (`coFloatSelectedArgs`)**. -/
theorem anfLift_applyDir_obsEquiv {Δ : AdtEnv} {Φ : FunEnv}
    (hΦ : ClosedFunEnv Φ) {xs : List Ident} {fn : Ident} {args : List Expr}
    {σ σ' : Store} {out : Expr}
    (hσ : ClosedStore σ) (hout : IsTerminal out)
    (hnodup : xs.Nodup) (hlen : xs.length = args.length)
    (hargs : ∀ e ∈ args, freeVars e = []) :
    Steps Δ Φ (anfLiftApplyDir xs fn args) σ out σ' ↔
      Steps Δ Φ (.applyDir fn args) σ out σ' := by
  exact anfLiftDirAux_equiv_closed hΦ hσ hout hnodup hlen hargs
    (fun _ h => by cases h) (fun _ h => by cases h)

/-- Left-to-right ANF callee + argument lifter mirroring `coFloatSelectedArgs` on `TmApplyCls`. -/
def anfLiftClsAux (xs : List Ident) (args : List Expr) (vf : Expr) (acc : List Expr) : Expr :=
  match xs, args with
  | x :: xr, e :: er => .let_ x e (anfLiftClsAux xr er vf (acc ++ [.var x]))
  | _, _ => .apply vf acc

def anfLiftApplyCls (xf : Ident) (xs : List Ident) (callee : Expr) (args : List Expr) : Expr :=
  .let_ xf callee (anfLiftClsAux xs args (.var xf) [])

theorem Steps.applyFnCongr {Δ : AdtEnv} {Φ : FunEnv}
    {fn fn' : Expr} {args : List Expr} {σ1 σ2 : Store}
    (h : Steps Δ Φ fn σ1 fn' σ2) :
    Steps Δ Φ (.apply fn args) σ1 (.apply fn' args) σ2 := by
  induction h with
  | refl => exact .refl _ _
  | trans hs _ ih => exact .trans (.applyFn hs) ih

theorem Steps.applyArgCongr {Δ : AdtEnv} {Φ : FunEnv}
    {vf : Expr} {vs er : List Expr} {e e' : Expr} {σ1 σ2 : Store}
    (hvf : IsValue vf) (hvs : ∀ v ∈ vs, IsValue v) (h : Steps Δ Φ e σ1 e' σ2) :
    Steps Δ Φ (.apply vf (vs ++ e :: er)) σ1 (.apply vf (vs ++ e' :: er)) σ2 := by
  induction h with
  | refl => exact .refl _ _
  | trans hs _ ih =>
    exact .trans (.applyArgs hvf (stepList_prepend_vals_forward hvs (.head hs))) ih

theorem steps_apply_callee_iff {Δ : AdtEnv} {Φ : FunEnv}
    {callee out : Expr} {args : List Expr} {σ σ' : Store} (hout : IsTerminal out) :
    Steps Δ Φ (.apply callee args) σ out σ' ↔
      (∃ t, out = .trap t ∧ Steps Δ Φ callee σ (.trap t) σ') ∨
      (∃ vf σ1, IsValue vf ∧ Steps Δ Φ callee σ vf σ1 ∧
        Steps Δ Φ (.apply vf args) σ1 out σ') := by
  constructor
  · intro h
    generalize happ : Expr.apply callee args = full at h
    induction h generalizing callee with
    | refl =>
      subst happ
      rcases hout with hv | ⟨t, htr⟩
      · cases hv
      · cases htr
    | trans hs hrest ih =>
      subst happ
      cases hs with
      | applyFn hs1 =>
        rcases ih hout rfl with ⟨t, rfl, htr⟩ | ⟨vf, σ1, hvf, hs_vf, hs_tail⟩
        · exact Or.inl ⟨t, rfl, .trans hs1 htr⟩
        · exact Or.inr ⟨vf, σ1, hvf, .trans hs1 hs_vf, hs_tail⟩
      | applyFnTrap =>
        rcases steps_of_isTerminal (Or.inr ⟨_, rfl⟩) hrest with ⟨rfl, rfl⟩
        exact Or.inl ⟨_, rfl, .refl _ _⟩
      | applyArgs hvf hsl =>
        exact Or.inr ⟨callee, _, hvf, .refl _ _, .trans (.applyArgs hvf hsl) hrest⟩
      | applyArgsTrap hvf htr =>
        exact Or.inr ⟨callee, _, hvf, .refl _ _, .trans (.applyArgsTrap hvf htr) hrest⟩
      | applyBeta hvs hlen =>
        exact Or.inr ⟨_, _, .lam _ _ _ _, .refl _ _, .trans (.applyBeta hvs hlen) hrest⟩
  · intro h
    rcases h with ⟨t, rfl, htr⟩ | ⟨vf, σ1, _, hs_vf, hs_tail⟩
    · exact Steps.append (Steps.applyFnCongr htr) (Steps.single .applyFnTrap)
    · exact Steps.append (Steps.applyFnCongr hs_vf) hs_tail

theorem steps_apply_next_arg_iff {Δ : AdtEnv} {Φ : FunEnv}
    {vf : Expr} {vs er : List Expr} {e out : Expr} {σ σ' : Store}
    (hout : IsTerminal out) (hvf : IsValue vf) (hvs : ∀ v ∈ vs, IsValue v) :
    Steps Δ Φ (.apply vf (vs ++ e :: er)) σ out σ' ↔
      (∃ t, out = .trap t ∧ Steps Δ Φ e σ (.trap t) σ') ∨
      (∃ v σ1, IsValue v ∧ Steps Δ Φ e σ v σ1 ∧
        Steps Δ Φ (.apply vf ((vs ++ [v]) ++ er)) σ1 out σ') := by
  constructor
  · intro h
    generalize happ : Expr.apply vf (vs ++ e :: er) = full at h
    induction h generalizing e with
    | refl =>
      subst happ
      rcases hout with hv | ⟨t, htr⟩
      · cases hv
      · cases htr
    | trans hs hrest ih =>
      subst happ
      cases hs with
      | applyFn hs1 => exact False.elim (isValue_no_step hvf hs1)
      | applyFnTrap => exact False.elim (isValue_ne_trap hvf _ rfl)
      | applyArgs _ hsl =>
        rcases stepList_prepend_vals_inv hvs hsl with ⟨es', heq, hsl_er⟩
        subst heq
        cases hsl_er with
        | head hs_e =>
          rcases ih hout rfl with ⟨t, rfl, htr⟩ | ⟨v, σ1, hv, hs_v, hs_tail⟩
          · exact Or.inl ⟨t, rfl, .trans hs_e htr⟩
          · exact Or.inr ⟨v, σ1, hv, .trans hs_e hs_v, hs_tail⟩
        | tail hv_e _ =>
          refine Or.inr ⟨e, _, hv_e, .refl _ _, ?_⟩
          rw [List.append_assoc, List.singleton_append]
          exact .trans (.applyArgs hvf hsl) hrest
      | @applyArgsTrap _ _ tr _ _ htr =>
        have htr_er := (listFirstTrap_prepend_vals_iff hvs).mp htr
        cases htr_er with
        | head _ _ =>
          rcases steps_of_isTerminal (Or.inr ⟨_, rfl⟩) hrest with ⟨rfl, rfl⟩
          exact Or.inl ⟨tr, rfl, .refl _ _⟩
        | tail hv_e htr_rest =>
          refine Or.inr ⟨e, _, hv_e, .refl _ _, ?_⟩
          have hvs' : ∀ w ∈ vs ++ [e], IsValue w := by
            intro w hw; rcases List.mem_append.mp hw with h1 | h2
            · exact hvs w h1
            · simp at h2; subst h2; exact hv_e
          have htr_full : ListFirstTrap ((vs ++ [e]) ++ er) tr :=
            (listFirstTrap_prepend_vals_iff hvs').mpr htr_rest
          exact .trans (.applyArgsTrap hvf htr_full) hrest
      | applyBeta hall hlen =>
        have hv_e : IsValue e := hall e (by simp)
        refine Or.inr ⟨e, _, hv_e, .refl _ _, ?_⟩
        rw [List.append_assoc, List.singleton_append]
        exact .trans (.applyBeta hall hlen) hrest
  · intro h
    rcases h with ⟨t, rfl, htr⟩ | ⟨v, σ1, _, hs_v, hs_tail⟩
    · have htr_full : ListFirstTrap (vs ++ .trap t :: er) t :=
        (listFirstTrap_prepend_vals_iff hvs).mpr (.head t er)
      exact Steps.append (Steps.applyArgCongr hvf hvs htr)
        (Steps.single (.applyArgsTrap hvf htr_full))
    · rw [List.append_assoc, List.singleton_append] at hs_tail
      exact Steps.append (Steps.applyArgCongr hvf hvs hs_v) hs_tail

theorem subst_anfLiftClsAux (x : Ident) (v : Expr) (xr : List Ident) (er : List Expr)
    (vf : Expr) (acc : List Expr)
    (hx_xr : x ∉ xr) (hx_er : ∀ e ∈ er, x ∉ freeVars e) :
    subst x v (anfLiftClsAux xr er vf acc) =
      anfLiftClsAux xr er (subst x v vf) (substList x v acc) := by
  induction xr generalizing er acc with
  | nil => simp [anfLiftClsAux, subst]
  | cons y yr ih =>
    cases er with
    | nil => simp [anfLiftClsAux, subst]
    | cons e rest =>
      simp only [List.mem_cons, not_or] at hx_xr
      have he : x ∉ freeVars e := hx_er e (List.mem_cons_self ..)
      have hrest : ∀ a ∈ rest, x ∉ freeVars a := fun a ha => hx_er a (List.mem_cons_of_mem _ ha)
      have hyx : (y == x) = false := beq_false_of_ne (Ne.symm hx_xr.1)
      have hsub_acc : substList x v (acc ++ [.var y]) = substList x v acc ++ [.var y] := by
        induction acc with
        | nil => simp [substList, subst, hyx]
        | cons a ar iha => simp [substList, iha]
      simp only [anfLiftClsAux, subst, hyx, Bool.false_eq_true, ↓reduceIte,
        subst_not_mem_freeVars e he, ih rest (acc ++ [.var y]) hx_xr.2 hrest, hsub_acc]

private theorem anfLiftClsAux_equiv_closed {Δ : AdtEnv} {Φ : FunEnv}
    (hΦ : ClosedFunEnv Φ) {xs : List Ident} {args vs : List Expr} {vf : Expr}
    {σ σ' : Store} {out : Expr}
    (hσ : ClosedStore σ) (hout : IsTerminal out)
    (hnodup : xs.Nodup) (hlen : xs.length = args.length)
    (hargs : ∀ e ∈ args, freeVars e = [])
    (hvf_val : IsValue vf) (hvf_cl : freeVars vf = [])
    (hvs_val : ∀ v ∈ vs, IsValue v) (hvs_cl : ∀ v ∈ vs, freeVars v = []) :
    Steps Δ Φ (anfLiftClsAux xs args vf vs) σ out σ' ↔
      Steps Δ Φ (.apply vf (vs ++ args)) σ out σ' := by
  induction xs generalizing args vs σ with
  | nil =>
    cases args with
    | nil => simp [anfLiftClsAux]
    | cons _ _ => simp at hlen
  | cons x xr ih =>
    cases args with
    | nil => simp at hlen
    | cons e er =>
      simp only [List.length_cons, Nat.succ.injEq] at hlen
      rcases List.nodup_cons.mp hnodup with ⟨hx_xr, hnodup_xr⟩
      have he_cl : freeVars e = [] := hargs e (List.mem_cons_self ..)
      have her_cl : ∀ a ∈ er, freeVars a = [] := fun a ha => hargs a (List.mem_cons_of_mem _ ha)
      have hx_er : ∀ a ∈ er, x ∉ freeVars a := fun a ha => by simp [her_cl a ha]
      have hx_vf : x ∉ freeVars vf := by simp [hvf_cl]
      have hsub_eq : ∀ v, subst x v (anfLiftClsAux xr er vf (vs ++ [.var x])) =
          anfLiftClsAux xr er vf (vs ++ [v]) := by
        intro v
        rw [subst_anfLiftClsAux x v xr er vf (vs ++ [Expr.var x]) hx_xr hx_er,
            subst_not_mem_freeVars vf hx_vf,
            substList_closed_append_self x v vs hvs_cl]
      simp only [anfLiftClsAux]
      rw [steps_let_terminal_iff hout, steps_apply_next_arg_iff hout hvf_val hvs_val]
      apply or_congr Iff.rfl
      constructor
      · rintro ⟨v, σ1, hv, hs_v, hs_rest⟩
        rcases steps_preserves_closed hΦ hσ he_cl hs_v with ⟨hv_cl, hσ1⟩
        rw [hsub_eq v] at hs_rest
        have hvs_val' : ∀ w ∈ vs ++ [v], IsValue w := by
          intro w hw; rcases List.mem_append.mp hw with h1 | h2
          · exact hvs_val w h1
          · simp at h2; subst h2; exact hv
        have hvs_cl' : ∀ w ∈ vs ++ [v], freeVars w = [] := by
          intro w hw; rcases List.mem_append.mp hw with h1 | h2
          · exact hvs_cl w h1
          · simp at h2; subst h2; exact hv_cl
        exact ⟨v, σ1, hv, hs_v,
          (ih hσ1 hnodup_xr hlen her_cl hvs_val' hvs_cl').mp hs_rest⟩
      · rintro ⟨v, σ1, hv, hs_v, hs_rest⟩
        rcases steps_preserves_closed hΦ hσ he_cl hs_v with ⟨hv_cl, hσ1⟩
        have hvs_val' : ∀ w ∈ vs ++ [v], IsValue w := by
          intro w hw; rcases List.mem_append.mp hw with h1 | h2
          · exact hvs_val w h1
          · simp at h2; subst h2; exact hv
        have hvs_cl' : ∀ w ∈ vs ++ [v], freeVars w = [] := by
          intro w hw; rcases List.mem_append.mp hw with h1 | h2
          · exact hvs_cl w h1
          · simp at h2; subst h2; exact hv_cl
        refine ⟨v, σ1, hv, hs_v, ?_⟩
        rw [hsub_eq v]
        exact (ih hσ1 hnodup_xr hlen her_cl hvs_val' hvs_cl').mpr hs_rest

/-- **Soundness of Strict Left-to-Right ANF Callee + Argument Lifting (`TmApplyCls`)**. -/
theorem anfLift_apply_obsEquiv {Δ : AdtEnv} {Φ : FunEnv}
    (hΦ : ClosedFunEnv Φ) {xf : Ident} {xs : List Ident} {callee : Expr} {args : List Expr}
    {σ σ' : Store} {out : Expr}
    (hσ : ClosedStore σ) (hout : IsTerminal out)
    (hnodup : (xf :: xs).Nodup) (hlen : xs.length = args.length)
    (hcallee : freeVars callee = []) (hargs : ∀ e ∈ args, freeVars e = []) :
    Steps Δ Φ (anfLiftApplyCls xf xs callee args) σ out σ' ↔
      Steps Δ Φ (.apply callee args) σ out σ' := by
  rcases List.nodup_cons.mp hnodup with ⟨hxf_xs, hnodup_xs⟩
  have hxf_args : ∀ a ∈ args, xf ∉ freeVars a := fun a ha => by simp [hargs a ha]
  unfold anfLiftApplyCls
  rw [steps_let_terminal_iff hout, steps_apply_callee_iff hout]
  apply or_congr Iff.rfl
  constructor
  · rintro ⟨vf, σ1, hvf, hs_vf, hs_rest⟩
    rcases steps_preserves_closed hΦ hσ hcallee hs_vf with ⟨hvf_cl, hσ1⟩
    rw [subst_anfLiftClsAux xf vf xs args (.var xf) [] hxf_xs hxf_args] at hs_rest
    simp only [subst, beq_self_eq_true, ↓reduceIte, substList] at hs_rest
    have heq := (anfLiftClsAux_equiv_closed hΦ hσ1 hout hnodup_xs hlen hargs hvf hvf_cl
      (fun _ h => by cases h) (fun _ h => by cases h)).mp hs_rest
    simp only [List.nil_append] at heq
    exact ⟨vf, σ1, hvf, hs_vf, heq⟩
  · rintro ⟨vf, σ1, hvf, hs_vf, hs_rest⟩
    rcases steps_preserves_closed hΦ hσ hcallee hs_vf with ⟨hvf_cl, hσ1⟩
    refine ⟨vf, σ1, hvf, hs_vf, ?_⟩
    rw [subst_anfLiftClsAux xf vf xs args (.var xf) [] hxf_xs hxf_args]
    simp only [subst, beq_self_eq_true, ↓reduceIte, substList]
    exact (anfLiftClsAux_equiv_closed hΦ hσ1 hout hnodup_xs hlen hargs hvf hvf_cl
      (fun _ h => by cases h) (fun _ h => by cases h)).mpr (by simpa using hs_rest)

/-- **Non-Vacuity Counterexample 2a (`out_of_order_float_changes_cell_value`)**:
    Floating a right-hand `let`-bearing argument `{ cellSet(c, 20); 1 }` across an
    unlifted left-hand `cellGet(c)` changes `pairAdd(cellGet(c), ...)` from `11` to `21`. -/
theorem out_of_order_float_changes_cell_value :
    let Φpair : FunEnv := fun nm =>
      if nm == "pairAdd" then
        some { name := "pairAdd", params := [("a", .int), ("b", .int)], retTy := .int,
               body := .bin .add (.var "a") (.var "b") }
      else none
    let eOrig : Expr :=
      .applyDir "pairAdd" [.cellGet (.loc 0), .block [.cellSet (.loc 0) (.lit (.int 20)), .lit (.int 1)]]
    let eOutOfOrder : Expr :=
      .let_ "$arg1" (.block [.cellSet (.loc 0) (.lit (.int 20)), .lit (.int 1)])
        (.applyDir "pairAdd" [.cellGet (.loc 0), .var "$arg1"])
    Steps (fun _ => none) Φpair eOrig [.lit (.int 10)] (.lit (.int 11)) [.lit (.int 20)] ∧
    Steps (fun _ => none) Φpair eOutOfOrder [.lit (.int 10)] (.lit (.int 21)) [.lit (.int 20)] ∧
    ¬ ObsEquiv (fun _ => none) Φpair Φpair eOrig eOutOfOrder := by
  let Φpair : FunEnv := fun nm =>
    if nm == "pairAdd" then
      some { name := "pairAdd", params := [("a", .int), ("b", .int)], retTy := .int,
             body := .bin .add (.var "a") (.var "b") }
    else none
  let eOrig : Expr :=
    .applyDir "pairAdd" [.cellGet (.loc 0), .block [.cellSet (.loc 0) (.lit (.int 20)), .lit (.int 1)]]
  let eOutOfOrder : Expr :=
    .let_ "$arg1" (.block [.cellSet (.loc 0) (.lit (.int 20)), .lit (.int 1)])
      (.applyDir "pairAdd" [.cellGet (.loc 0), .var "$arg1"])
  have h2vals : ∀ v ∈ ([.lit (.int 10), .lit (.int 1)] : List Expr), IsValue v := by
    intro v hv; rcases List.mem_cons.mp hv with rfl | hv2
    · exact .lit _
    · rcases List.mem_cons.mp hv2 with rfl | h
      · exact .lit _
      · cases h
  have h2vals' : ∀ v ∈ ([.lit (.int 20), .lit (.int 1)] : List Expr), IsValue v := by
    intro v hv; rcases List.mem_cons.mp hv with rfl | hv2
    · exact .lit _
    · rcases List.mem_cons.mp hv2 with rfl | h
      · exact .lit _
      · cases h
  have h1 : Steps (fun _ => none) Φpair eOrig [.lit (.int 10)] (.lit (.int 11)) [.lit (.int 20)] := by
    refine .trans (.applyDirArgs (.head (.cellGetVal rfl))) ?_
    refine .trans (.applyDirArgs (.tail (.lit _) (.head (.blockConsStep (.cellSetVal (by decide) (.lit _)))))) ?_
    refine .trans (.applyDirArgs (.tail (.lit _) (.head (.blockConsVal (.lit _))))) ?_
    refine .trans (.applyDirArgs (.tail (.lit _) (.head .blockSingle))) ?_
    refine .trans (.applyDirBeta rfl h2vals rfl) ?_
    exact .single (.binVal rfl)
  have h2 : Steps (fun _ => none) Φpair eOutOfOrder [.lit (.int 10)] (.lit (.int 21)) [.lit (.int 20)] := by
    refine .trans (.letStep (.blockConsStep (.cellSetVal (by decide) (.lit _)))) ?_
    refine .trans (.letStep (.blockConsVal (.lit _))) ?_
    refine .trans (.letStep .blockSingle) ?_
    refine .trans (.letVal (.lit _)) ?_
    refine .trans (.applyDirArgs (.head (.cellGetVal rfl))) ?_
    refine .trans (.applyDirBeta rfl h2vals' rfl) ?_
    exact .single (.binVal rfl)
  exact ⟨h1, h2, not_obsEquiv_of_distinct_terminals h1 (Or.inl (.lit _)) h2 (Or.inl (.lit _))
    (Or.inl (by rintro ⟨⟩))⟩

/-- **Non-Vacuity Counterexample 2b (`out_of_order_float_mutates_before_trap`)**:
    Floating a side-effecting right-hand argument `cellSet(loc 0, 1)` before a
    trapping left-hand argument `10 / 0` mutates the heap (`[1]` vs `[0]`) prior to trapping. -/
theorem out_of_order_float_mutates_before_trap :
    let Φboth : FunEnv := fun nm =>
      if nm == "both" then
        some { name := "both", params := [("a", .int), ("b", .int)], retTy := .int,
               body := .bin .add (.var "a") (.var "b") }
      else none
    let eOrig : Expr :=
      .applyDir "both"
        [.bin .div (.lit (.int 10)) (.lit (.int 0)),
         .block [.cellSet (.loc 0) (.lit (.int 1)), .lit (.int 5)]]
    let eOutOfOrder : Expr :=
      .let_ "$arg1" (.block [.cellSet (.loc 0) (.lit (.int 1)), .lit (.int 5)])
        (.applyDir "both" [.bin .div (.lit (.int 10)) (.lit (.int 0)), .var "$arg1"])
    Steps (fun _ => none) Φboth eOrig [.lit (.int 0)] (.trap .divByZero) [.lit (.int 0)] ∧
    Steps (fun _ => none) Φboth eOutOfOrder [.lit (.int 0)] (.trap .divByZero) [.lit (.int 1)] ∧
    ¬ ObsEquiv (fun _ => none) Φboth Φboth eOrig eOutOfOrder := by
  let Φboth : FunEnv := fun nm =>
    if nm == "both" then
      some { name := "both", params := [("a", .int), ("b", .int)], retTy := .int,
             body := .bin .add (.var "a") (.var "b") }
    else none
  let eOrig : Expr :=
    .applyDir "both"
      [.bin .div (.lit (.int 10)) (.lit (.int 0)),
       .block [.cellSet (.loc 0) (.lit (.int 1)), .lit (.int 5)]]
  let eOutOfOrder : Expr :=
    .let_ "$arg1" (.block [.cellSet (.loc 0) (.lit (.int 1)), .lit (.int 5)])
      (.applyDir "both" [.bin .div (.lit (.int 10)) (.lit (.int 0)), .var "$arg1"])
  have hdiv : evalBinOp .div (.int 10) (.int 0) = some (.trap .divByZero) := by rfl
  have h1 : Steps (fun _ => none) Φboth eOrig [.lit (.int 0)] (.trap .divByZero) [.lit (.int 0)] :=
    .trans (.applyDirArgs (.head (.binTrap hdiv))) (.single (.applyDirTrap (.head _ _)))
  have h2 : Steps (fun _ => none) Φboth eOutOfOrder [.lit (.int 0)] (.trap .divByZero) [.lit (.int 1)] :=
    .trans (.letStep (.blockConsStep (.cellSetVal (by decide) (.lit _))))
      (.trans (.letStep (.blockConsVal (.lit _)))
        (.trans (.letStep .blockSingle)
          (.trans (.letVal (.lit _))
            (.trans (.applyDirArgs (.head (.binTrap hdiv)))
              (.single (.applyDirTrap (.head _ _)))))))
  exact ⟨h1, h2, not_obsEquiv_of_distinct_terminals h1 (Or.inr ⟨_, rfl⟩) h2 (Or.inr ⟨_, rfl⟩)
    (Or.inr (by rintro ⟨⟩))⟩

/-! ## Part 4: Case-of-Known-Constructor, Tuple & Non-Float Literal (`coTryReduceMatch`) -/

/-- **Soundness of Case-of-Known-Constructor Hit (`CoPatYes`)**. -/
theorem known_ctor_match_hit_obsEquiv (Δ : AdtEnv) (Φ : FunEnv)
    {adt : Ident} {tag : Nat} {vs : List Expr} {ps : List Pat}
    {body : Expr} {rest : List (Pat × Expr)} {env : List (Ident × Expr)}
    (hvs : ∀ v ∈ vs, IsValue v) (hm : matchPats ps vs = some env) :
    ObsEquiv Δ Φ Φ (.match_ (.makeData adt tag vs) ((.ctor adt tag ps, body) :: rest))
      (substMany env body) := by
  apply obsEquiv_of_det_step
  intro σ
  exact .matchHit (.makeData adt tag hvs) (by simp [matchPat, hm])

/-- **Soundness of Case-of-Known-Constructor Miss (`CoPatNo`)**. -/
theorem known_ctor_match_miss_obsEquiv (Δ : AdtEnv) (Φ : FunEnv)
    {adt : Ident} {tag1 tag2 : Nat} {vs : List Expr} {ps : List Pat}
    {body : Expr} {rest : List (Pat × Expr)}
    (hvs : ∀ v ∈ vs, IsValue v) (hne : tag2 ≠ tag1) :
    ObsEquiv Δ Φ Φ (.match_ (.makeData adt tag1 vs) ((.ctor adt tag2 ps, body) :: rest))
      (.match_ (.makeData adt tag1 vs) rest) := by
  apply obsEquiv_of_det_step
  intro σ
  have hbeq : (tag2 == tag1) = false := beq_false_of_ne hne
  exact .matchMiss (.makeData adt tag1 hvs) (by simp [matchPat, hbeq])

/-- **Soundness of Case-of-Known-Tuple (`TmTuple`)**. -/
theorem known_tuple_match_obsEquiv (Δ : AdtEnv) (Φ : FunEnv)
    {vs : List Expr} {ps : List Pat} {body : Expr} {rest : List (Pat × Expr)}
    {env : List (Ident × Expr)}
    (hvs : ∀ v ∈ vs, IsValue v) (hm : matchPats ps vs = some env) :
    ObsEquiv Δ Φ Φ (.match_ (.tuple vs) ((.tuple ps, body) :: rest))
      (substMany env body) := by
  apply obsEquiv_of_det_step
  intro σ
  exact .matchHit (.tuple hvs) (by simp [matchPat, hm])

theorem lit_beq_refl (l : Lit) : (l == l) = true := by
  cases l with
  | int a => exact beq_self_eq_true a
  | int64 a => exact beq_self_eq_true a
  | floatBits a => exact beq_self_eq_true a
  | float32Bits a => exact beq_self_eq_true a
  | bool b => exact beq_self_eq_true b
  | char c => exact beq_self_eq_true c
  | str s => exact beq_self_eq_true s
  | unit => rfl

/-- Non-float literals eligible for compile-time `coMatchPatKnown` reduction in `src/core.gsa`. -/
def IsNonFloatLit : Lit → Prop
  | .floatBits _ | .float32Bits _ => False
  | _ => True

/-- **Soundness of Case-of-Known-Literal Hit (`LitInt`, `LitInt64`, `LitBool`, `LitChar`, `LitStr`, `LitUnit`)**. -/
theorem known_lit_match_hit_obsEquiv (Δ : AdtEnv) (Φ : FunEnv)
    (l : Lit) (_hnonFloat : IsNonFloatLit l) (body : Expr) (rest : List (Pat × Expr)) :
    ObsEquiv Δ Φ Φ (.match_ (.lit l) ((.lit l, body) :: rest)) body := by
  apply obsEquiv_of_det_step
  intro σ
  have hs := Step.matchHit (Δ := Δ) (Φ := Φ) (pool := emptyPool)
    (v := .lit l) (p := .lit l) (body := body) (rest := rest) (env := []) (σ := σ)
    (.lit l) (by simp [matchPat, lit_beq_refl l])
  simpa [substMany] using hs

/-- **Soundness of Case-of-Known-Literal Miss (`CoPatNo` on non-float literals)**. -/
theorem known_lit_match_miss_obsEquiv (Δ : AdtEnv) (Φ : FunEnv)
    {l1 l2 : Lit} (_h1 : IsNonFloatLit l1) (_h2 : IsNonFloatLit l2)
    (hne : (l2 == l1) = false) (body : Expr) (rest : List (Pat × Expr)) :
    ObsEquiv Δ Φ Φ (.match_ (.lit l1) ((.lit l2, body) :: rest))
      (.match_ (.lit l1) rest) := by
  apply obsEquiv_of_det_step
  intro σ
  exact .matchMiss (.lit l1) (by simp [matchPat, hne])

/-- **Representation Divergence Witness 3a (`float_negZero_bits_neq_counterexample`)**:
    In `CoreGeisha.Semantics` (`Semantics.lean:129`), `matchPat` on `Lit.floatBits` compares raw
    64-bit patterns via `BEq`: `-0.0` (`0x8000000000000000`) and `+0.0` (`0x0000000000000000`)
    have `BEq = false` (`matchPat = none`), while identical quiet `NaN` bitstrings
    (`0x7ff8000000000000`) have `BEq = true` (`matchPat = some []`). Because backend codegen
    (`src/codegen.gsa:4479` `fcmp oeq`, JS `===`, WasmGC `f64.eq`) uses IEEE-754 numeric equality,
    `coMatchPatKnown` (`src/core.gsa:6071`) conservatively returns `CoPatUnknown` on `LitFloat`. -/
theorem float_negZero_bits_neq_counterexample :
    let negZeroBits : UInt64 := 0x8000000000000000
    let posZeroBits : UInt64 := 0x0000000000000000
    let nanBits : UInt64 := 0x7ff8000000000000
    (Lit.floatBits negZeroBits == Lit.floatBits posZeroBits) = false ∧
    matchPat (.lit (.floatBits posZeroBits)) (.lit (.floatBits negZeroBits)) = none ∧
    (Lit.floatBits nanBits == Lit.floatBits nanBits) = true ∧
    matchPat (.lit (.floatBits nanBits)) (.lit (.floatBits nanBits)) = some [] := by
  exact ⟨by decide, by rfl, by decide, by rfl⟩

/-- **Non-Vacuity Counterexample 3b (`self_shadowed_ctor_let_counterexample`)**:
    In `let x = End; let x = Next(x); match x { Next(End) -> 1, _ -> 0 }`,
    the true evaluation yields `1`, whereas naively re-resolving `Next(x)`'s payload
    variable `x` in the shadowed scope (`Next(Next(End))`) yields `0` — justifying
    the `!coTermListMentionsVar(fs, vd.vname)` guard in `coRecordLetBindingInEnv`. -/
theorem self_shadowed_ctor_let_counterexample :
    let arms : List (Pat × Expr) :=
      [(.ctor "Chain" 1 [.ctor "Chain" 0 []], .lit (.int 1)),
       (.wild, .lit (.int 0))]
    let eTrue : Expr :=
      .let_ "x" (.makeData "Chain" 0 [])
        (.let_ "x" (.makeData "Chain" 1 [.var "x"])
          (.match_ (.var "x") arms))
    let eMisresolved : Expr :=
      .match_ (.makeData "Chain" 1 [.makeData "Chain" 1 [.makeData "Chain" 0 []]]) arms
    Steps (fun _ => none) (fun _ => none) eTrue [] (.lit (.int 1)) [] ∧
    Steps (fun _ => none) (fun _ => none) eMisresolved [] (.lit (.int 0)) [] ∧
    ¬ ObsEquiv (fun _ => none) (fun _ => none) (fun _ => none) eTrue eMisresolved := by
  let arms : List (Pat × Expr) :=
    [(.ctor "Chain" 1 [.ctor "Chain" 0 []], .lit (.int 1)),
     (.wild, .lit (.int 0))]
  let eTrue : Expr :=
    .let_ "x" (.makeData "Chain" 0 [])
      (.let_ "x" (.makeData "Chain" 1 [.var "x"])
        (.match_ (.var "x") arms))
  let eMisresolved : Expr :=
    .match_ (.makeData "Chain" 1 [.makeData "Chain" 1 [.makeData "Chain" 0 []]]) arms
  have hv0 : IsValue (.makeData "Chain" 0 []) := .makeData "Chain" 0 (fun _ h => by cases h)
  have hv1 : IsValue (.makeData "Chain" 1 [.makeData "Chain" 0 []]) :=
    .makeData "Chain" 1 (fun _ h => by
      rcases List.mem_cons.mp h with rfl | h2
      · exact hv0
      · cases h2)
  have hv2 : IsValue (.makeData "Chain" 1 [.makeData "Chain" 1 [.makeData "Chain" 0 []]]) :=
    .makeData "Chain" 1 (fun _ h => by
      rcases List.mem_cons.mp h with rfl | h2
      · exact hv1
      · cases h2)
  have h1 : Steps (fun _ => none) (fun _ => none) eTrue [] (.lit (.int 1)) [] := by
    refine .trans (.letVal hv0) ?_
    refine .trans (.letVal hv1) ?_
    have hsub : subst "x" (subst "x" (.makeData "Chain" 0 []) (.makeData "Chain" 1 [.var "x"]))
        (Expr.match_ (.var "x") arms) =
        Expr.match_ (.makeData "Chain" 1 [.makeData "Chain" 0 []]) arms := by
      simp [arms, subst, substList, substArms, patBoundNames]
    rw [hsub]
    exact .single (Step.matchHit
      (p := .ctor "Chain" 1 [.ctor "Chain" 0 []])
      (body := .lit (.int 1))
      (rest := [(.wild, .lit (.int 0))])
      (env := []) hv1 rfl)
  have h2 : Steps (fun _ => none) (fun _ => none) eMisresolved [] (.lit (.int 0)) [] := by
    refine .trans (.matchMiss hv2 rfl) ?_
    exact .single (Step.matchHit (env := []) hv2 rfl)
  exact ⟨h1, h2, not_obsEquiv_of_distinct_terminals h1 (Or.inl (.lit _)) h2 (Or.inl (.lit _))
    (Or.inl (by rintro ⟨⟩))⟩

/-! ## Part 5: Known-Closure Flattening Devirtualization (`$flat$`, `coGetOrCreateFlatClsFn`) -/

mutual
theorem subst_comm_of_closed {x y : Ident} {v w : Expr}
    (hne : x ≠ y) (hv : freeVars v = []) (hw : freeVars w = []) :
    (e : Expr) → subst x v (subst y w e) = subst y w (subst x v e)
  | .lit _ | .loc _ | .taskRef _ | .syncRef _ _ | .trap _ => rfl
  | .var z => by
    simp only [subst]
    cases hzy : (z == y)
    · cases hzx : (z == x)
      · simp [subst, hzy, hzx]
      · simp only [Bool.false_eq_true, ↓reduceIte, subst, hzx]
        exact (subst_not_mem_freeVars v (by simp [hv])).symm
    · have hzx : (z == x) = false := by
        have := eq_of_beq hzy; subst this; exact beq_false_of_ne (Ne.symm hne)
      simp only [↓reduceIte, subst, hzx, hzy, Bool.false_eq_true]
      exact subst_not_mem_freeVars w (by simp [hw])
  | .tuple es => by simp [subst, substList_comm_of_closed hne hv hw es]
  | .block es => by simp [subst, substList_comm_of_closed hne hv hw es]
  | .lam m ps ret body => by
    simp only [subst]
    cases hmy : ps.any (fun p => p.1 == y) <;> cases hmx : ps.any (fun p => p.1 == x) <;>
      simp [subst, hmy, hmx, subst_comm_of_closed hne hv hw body]
  | .apply fn args => by
    simp [subst, subst_comm_of_closed hne hv hw fn, substList_comm_of_closed hne hv hw args]
  | .applyDir fn args => by simp [subst, substList_comm_of_closed hne hv hw args]
  | .bin op e1 e2 => by
    simp [subst, subst_comm_of_closed hne hv hw e1, subst_comm_of_closed hne hv hw e2]
  | .un op e1 => by simp [subst, subst_comm_of_closed hne hv hw e1]
  | .let_ z e1 e2 => by
    simp only [subst]
    cases hzy : (z == y) <;> cases hzx : (z == x) <;>
      simp [subst, hzy, hzx, subst_comm_of_closed hne hv hw e1, subst_comm_of_closed hne hv hw e2]
  | .if_ c t e2 => by
    simp [subst, subst_comm_of_closed hne hv hw c,
      subst_comm_of_closed hne hv hw t, subst_comm_of_closed hne hv hw e2]
  | .while_ c b => by
    simp [subst, subst_comm_of_closed hne hv hw c, subst_comm_of_closed hne hv hw b]
  | .match_ s arms => by
    simp [subst, subst_comm_of_closed hne hv hw s, substArms_comm_of_closed hne hv hw arms]
  | .makeData adt tag es => by simp [subst, substList_comm_of_closed hne hv hw es]
  | .getTag e1 => by simp [subst, subst_comm_of_closed hne hv hw e1]
  | .cellNew e1 => by simp [subst, subst_comm_of_closed hne hv hw e1]
  | .cellGet e1 => by simp [subst, subst_comm_of_closed hne hv hw e1]
  | .cellSet e1 e2 => by
    simp [subst, subst_comm_of_closed hne hv hw e1, subst_comm_of_closed hne hv hw e2]
  | .spawn e1 => by simp [subst, subst_comm_of_closed hne hv hw e1]
  | .await e1 => by simp [subst, subst_comm_of_closed hne hv hw e1]
  | .concPrim op args => by simp [subst, substList_comm_of_closed hne hv hw args]
termination_by e => sizeOf e

theorem substList_comm_of_closed {x y : Ident} {v w : Expr}
    (hne : x ≠ y) (hv : freeVars v = []) (hw : freeVars w = []) :
    (es : List Expr) → substList x v (substList y w es) = substList y w (substList x v es)
  | [] => rfl
  | a :: rest => by
    simp [substList, subst_comm_of_closed hne hv hw a, substList_comm_of_closed hne hv hw rest]
termination_by es => sizeOf es

theorem substArms_comm_of_closed {x y : Ident} {v w : Expr}
    (hne : x ≠ y) (hv : freeVars v = []) (hw : freeVars w = []) :
    (arms : List (Pat × Expr)) → substArms x v (substArms y w arms) = substArms y w (substArms x v arms)
  | [] => rfl
  | (p, body) :: rest => by
    simp only [substArms, substArms_comm_of_closed hne hv hw rest]
    cases hmy : (patBoundNames p).contains y <;> cases hmx : (patBoundNames p).contains x <;>
      simp [subst_comm_of_closed hne hv hw body]
termination_by arms => sizeOf arms
end

theorem substMany_append (ρ1 ρ2 : List (Ident × Expr)) (e : Expr) :
    substMany (ρ1 ++ ρ2) e = substMany ρ2 (substMany ρ1 e) := by
  induction ρ1 generalizing e with
  | nil => rfl
  | cons p rest ih => simp [substMany, ih]

theorem subst_substMany_comm {x : Ident} {v : Expr} {ρ : List (Ident × Expr)}
    (hv : freeVars v = []) (hρ : ∀ p ∈ ρ, freeVars p.2 = [])
    (hx : x ∉ ρ.map Prod.fst) (e : Expr) :
    subst x v (substMany ρ e) = substMany ρ (subst x v e) := by
  induction ρ generalizing e with
  | nil => rfl
  | cons p rest ih =>
    rcases p with ⟨y, w⟩
    simp only [List.map_cons, List.mem_cons, not_or] at hx
    have hw : freeVars w = [] := hρ (y, w) (List.mem_cons_self ..)
    have hrest : ∀ q ∈ rest, freeVars q.2 = [] := fun q hq => hρ q (List.mem_cons_of_mem _ hq)
    simp only [substMany]
    rw [ih hrest hx.2, subst_comm_of_closed hx.1 hv hw e]

theorem substMany_comm_disjoint {ρ1 ρ2 : List (Ident × Expr)}
    (h1 : ∀ p ∈ ρ1, freeVars p.2 = []) (h2 : ∀ p ∈ ρ2, freeVars p.2 = [])
    (hdisj : ∀ x ∈ ρ1.map Prod.fst, x ∉ ρ2.map Prod.fst) (e : Expr) :
    substMany ρ1 (substMany ρ2 e) = substMany ρ2 (substMany ρ1 e) := by
  induction ρ1 generalizing e with
  | nil => rfl
  | cons p rest ih =>
    rcases p with ⟨x, v⟩
    have hv : freeVars v = [] := h1 (x, v) (List.mem_cons_self ..)
    have hrest : ∀ q ∈ rest, freeVars q.2 = [] := fun q hq => h1 q (List.mem_cons_of_mem _ hq)
    have hx : x ∉ ρ2.map Prod.fst := hdisj x (List.mem_cons_self ..)
    have hdr : ∀ z ∈ rest.map Prod.fst, z ∉ ρ2.map Prod.fst :=
      fun z hz => hdisj z (List.mem_cons_of_mem _ hz)
    simp only [substMany]
    rw [subst_substMany_comm hv h2 hx e, ih hrest hdr (subst x v e)]

theorem zipParams_append {ps1 ps2 : List (Ident × Ty)} {vs1 vs2 : List Expr}
    (h1 : vs1.length = ps1.length) :
    zipParams (ps1 ++ ps2) (vs1 ++ vs2) = zipParams ps1 vs1 ++ zipParams ps2 vs2 := by
  induction ps1 generalizing vs1 with
  | nil =>
    cases vs1 <;> simp [zipParams] at h1 ⊢
  | cons p pr ih =>
    cases vs1 with
    | nil => simp at h1
    | cons v vr =>
      simp only [List.length_cons, Nat.succ.injEq] at h1
      have hrec := ih h1
      simp only [zipParams] at hrec ⊢
      rw [List.map_append] at hrec
      simp only [List.map_append, List.map_cons, List.cons_append, List.zip_cons_cons]
      exact congrArg ((p.1, v) :: ·) hrec

theorem substMany_lam_disjoint (m : Mode) (ps : List (Ident × Ty)) (ret : Ty) (body : Expr)
    (ρ : List (Ident × Expr))
    (hdisj : ∀ x ∈ ps.map Prod.fst, x ∉ ρ.map Prod.fst) :
    substMany ρ (.lam m ps ret body) = .lam m ps ret (substMany ρ body) := by
  induction ρ generalizing body with
  | nil => rfl
  | cons p rest ih =>
    rcases p with ⟨y, w⟩
    have hany : ps.any (fun q => q.1 == y) = false := by
      cases h : ps.any (fun q => q.1 == y)
      · rfl
      · rcases List.any_eq_true.mp h with ⟨q, hq, hqy⟩
        exact False.elim (hdisj q.1 (List.mem_map.mpr ⟨q, hq, rfl⟩)
          (by simp [eq_of_beq hqy]))
    have hdr : ∀ x ∈ ps.map Prod.fst, x ∉ rest.map Prod.fst :=
      fun x hx hmem => hdisj x hx (List.mem_cons_of_mem _ hmem)
    simp [substMany, subst, hany, ih _ hdr]

/-- **Core Substitution Algebra of Known-Closure Flattening (`$flat$`)**. -/
theorem substMany_lam_apply_eq_flat
    (ps fvs : List (Ident × Ty)) (argVals fvVals : List Expr) (body : Expr)
    (hargLen : argVals.length = ps.length)
    (hfvLen : fvVals.length = fvs.length)
    (hargCl : ∀ v ∈ argVals, freeVars v = [])
    (hfvCl : ∀ v ∈ fvVals, freeVars v = [])
    (hdisj : ∀ x ∈ ps.map Prod.fst, x ∉ fvs.map Prod.fst) :
    substMany (zipParams ps argVals) (substMany (zipParams fvs fvVals) body) =
      substMany (zipParams (ps ++ fvs) (argVals ++ fvVals)) body := by
  rw [zipParams_append hargLen, substMany_append]
  apply substMany_comm_disjoint (zipParams_closed hargCl) (zipParams_closed hfvCl)
  rw [zipParams_fst_eq hargLen, zipParams_fst_eq hfvLen]
  exact hdisj

/-- **Soundness of Known-Closure Flattening Devirtualization (`$flat$`, `coGetOrCreateFlatClsFn`)**. -/
theorem flat_closure_devirt_obsEquiv (Δ : AdtEnv) (Φ : FunEnv)
    {flatName : Ident} {m : Mode} {ps fvs : List (Ident × Ty)} {ret : Ty} {body : Expr}
    {argVals fvVals : List Expr}
    (hflat : Φ flatName = some { name := flatName, params := ps ++ fvs, retTy := ret, body := body })
    (hargVal : ∀ v ∈ argVals, IsValue v) (hfvVal : ∀ v ∈ fvVals, IsValue v)
    (hargCl : ∀ v ∈ argVals, freeVars v = []) (hfvCl : ∀ v ∈ fvVals, freeVars v = [])
    (hargLen : argVals.length = ps.length) (hfvLen : fvVals.length = fvs.length)
    (hdisj : ∀ x ∈ ps.map Prod.fst, x ∉ fvs.map Prod.fst) :
    ObsEquiv Δ Φ Φ
      (.apply (substMany (zipParams fvs fvVals) (.lam m ps ret body)) argVals)
      (.applyDir flatName (argVals ++ fvVals)) := by
  have hd : ∀ x ∈ ps.map Prod.fst, x ∉ (zipParams fvs fvVals).map Prod.fst := by
    rw [zipParams_fst_eq hfvLen]; exact hdisj
  rw [substMany_lam_disjoint m ps ret body (zipParams fvs fvVals) hd]
  have h1 : ObsEquiv Δ Φ Φ
      (.apply (.lam m ps ret (substMany (zipParams fvs fvVals) body)) argVals)
      (substMany (zipParams ps argVals) (substMany (zipParams fvs fvVals) body)) :=
    obsEquiv_of_det_step fun σ => .applyBeta hargVal hargLen
  have hallVal : ∀ v ∈ argVals ++ fvVals, IsValue v := by
    intro v hv; rcases List.mem_append.mp hv with h1 | h2
    · exact hargVal v h1
    · exact hfvVal v h2
  have hallLen : (argVals ++ fvVals).length = (ps ++ fvs).length := by
    simp [hargLen, hfvLen]
  have h2 : ObsEquiv Δ Φ Φ
      (.applyDir flatName (argVals ++ fvVals))
      (substMany (zipParams (ps ++ fvs) (argVals ++ fvVals)) body) :=
    obsEquiv_of_det_step fun σ => .applyDirBeta hflat hallVal hallLen
  rw [substMany_lam_apply_eq_flat ps fvs argVals fvVals body hargLen hfvLen hargCl hfvCl hdisj] at h1
  exact ObsEquiv.trans h1 h2.symm

/-! ## Part 6: Self-Recursive Higher-Order Loop Specialization (`$spec$`, `coTrySpecializeHofLoop`) -/

/- Code transformation mirroring `coTrySpecializeHofLoop` + `coRewriteSelfCallsInSpecBody`:
   - callback invocations `.apply (.var fParam) cbArgs` rewrite to direct `.applyDir cbEntry (cbArgs' ++ fvVars)`,
   - invariant self-recursive calls `.applyDir loopName (.var fParam :: recArgs)` rewrite to
     `.applyDir specName (fvVars ++ recArgs')`. -/
mutual
def specializeLoopExpr (loopName specName cbEntry fParam : Ident)
    (fvNames : List Ident) : Expr → Expr
  | .lit l => .lit l
  | .var x => .var x
  | .loc l => .loc l
  | .taskRef tid => .taskRef tid
  | .syncRef k id => .syncRef k id
  | .tuple es => .tuple (specializeLoopList loopName specName cbEntry fParam fvNames es)
  | .block es => .block (specializeLoopList loopName specName cbEntry fParam fvNames es)
  | .lam m ps ret body => .lam m ps ret body
  | .apply (.var f) cbArgs =>
    if f == fParam then
      .applyDir cbEntry
        (specializeLoopList loopName specName cbEntry fParam fvNames cbArgs ++
          fvNames.map .var)
    else
      .apply (.var f) (specializeLoopList loopName specName cbEntry fParam fvNames cbArgs)
  | .apply fn args =>
    .apply (specializeLoopExpr loopName specName cbEntry fParam fvNames fn)
      (specializeLoopList loopName specName cbEntry fParam fvNames args)
  | .applyDir nm (.var f :: recArgs) =>
    if nm == loopName && f == fParam then
      .applyDir specName
        (fvNames.map .var ++
          specializeLoopList loopName specName cbEntry fParam fvNames recArgs)
    else
      .applyDir nm
        (.var f :: specializeLoopList loopName specName cbEntry fParam fvNames recArgs)
  | .applyDir nm args =>
    .applyDir nm (specializeLoopList loopName specName cbEntry fParam fvNames args)
  | .bin op e1 e2 =>
    .bin op (specializeLoopExpr loopName specName cbEntry fParam fvNames e1)
      (specializeLoopExpr loopName specName cbEntry fParam fvNames e2)
  | .un op e1 =>
    .un op (specializeLoopExpr loopName specName cbEntry fParam fvNames e1)
  | .let_ y e1 e2 =>
    .let_ y (specializeLoopExpr loopName specName cbEntry fParam fvNames e1)
      (specializeLoopExpr loopName specName cbEntry fParam fvNames e2)
  | .if_ c t e2 =>
    .if_ (specializeLoopExpr loopName specName cbEntry fParam fvNames c)
      (specializeLoopExpr loopName specName cbEntry fParam fvNames t)
      (specializeLoopExpr loopName specName cbEntry fParam fvNames e2)
  | .while_ c b =>
    .while_ (specializeLoopExpr loopName specName cbEntry fParam fvNames c)
      (specializeLoopExpr loopName specName cbEntry fParam fvNames b)
  | .match_ s arms =>
    .match_ (specializeLoopExpr loopName specName cbEntry fParam fvNames s)
      (specializeLoopArms loopName specName cbEntry fParam fvNames arms)
  | .makeData adt tag es =>
    .makeData adt tag (specializeLoopList loopName specName cbEntry fParam fvNames es)
  | .getTag e1 =>
    .getTag (specializeLoopExpr loopName specName cbEntry fParam fvNames e1)
  | .cellNew e1 =>
    .cellNew (specializeLoopExpr loopName specName cbEntry fParam fvNames e1)
  | .cellGet e1 =>
    .cellGet (specializeLoopExpr loopName specName cbEntry fParam fvNames e1)
  | .cellSet e1 e2 =>
    .cellSet (specializeLoopExpr loopName specName cbEntry fParam fvNames e1)
      (specializeLoopExpr loopName specName cbEntry fParam fvNames e2)
  | .spawn e1 => .spawn (specializeLoopExpr loopName specName cbEntry fParam fvNames e1)
  | .await e1 => .await (specializeLoopExpr loopName specName cbEntry fParam fvNames e1)
  | .concPrim op args =>
    .concPrim op (specializeLoopList loopName specName cbEntry fParam fvNames args)
  | .trap t => .trap t
termination_by e => sizeOf e

def specializeLoopList (loopName specName cbEntry fParam : Ident)
    (fvNames : List Ident) : List Expr → List Expr
  | [] => []
  | e :: es =>
    specializeLoopExpr loopName specName cbEntry fParam fvNames e ::
      specializeLoopList loopName specName cbEntry fParam fvNames es
termination_by es => sizeOf es

def specializeLoopArms (loopName specName cbEntry fParam : Ident)
    (fvNames : List Ident) : List (Pat × Expr) → List (Pat × Expr)
  | [] => []
  | (p, body) :: rest =>
    (p, specializeLoopExpr loopName specName cbEntry fParam fvNames body) ::
      specializeLoopArms loopName specName cbEntry fParam fvNames rest
termination_by arms => sizeOf arms
end

/- Syntactic invariant of a cloned loop body eligible for `SpecConstr` specialization. -/
mutual
inductive SpecEligible (loopName fParam : Ident) (avoid : List Ident)
    (cbArity stateArity : Nat) : Expr → Prop where
  | lit (l : Lit) : SpecEligible loopName fParam avoid cbArity stateArity (.lit l)
  | var {x : Ident} :
      x ≠ fParam →
      SpecEligible loopName fParam avoid cbArity stateArity (.var x)
  | loc (l : Loc) : SpecEligible loopName fParam avoid cbArity stateArity (.loc l)
  | taskRef (tid : TaskId) : SpecEligible loopName fParam avoid cbArity stateArity (.taskRef tid)
  | syncRef (k : SyncKind) (id : Nat) :
      SpecEligible loopName fParam avoid cbArity stateArity (.syncRef k id)
  | trap (t : Trap) : SpecEligible loopName fParam avoid cbArity stateArity (.trap t)
  | lam {m : Mode} {ps : List (Ident × Ty)} {ret : Ty} {body : Expr} :
      fParam ∉ freeVars (.lam m ps ret body) →
      (∀ z ∈ ps.map Prod.fst, z ∉ avoid) →
      SpecEligible loopName fParam avoid cbArity stateArity (.lam m ps ret body)
  | tuple {es : List Expr} :
      SpecEligibleList loopName fParam avoid cbArity stateArity es →
      SpecEligible loopName fParam avoid cbArity stateArity (.tuple es)
  | block {es : List Expr} :
      SpecEligibleList loopName fParam avoid cbArity stateArity es →
      SpecEligible loopName fParam avoid cbArity stateArity (.block es)
  | cbCall {cbArgs : List Expr} :
      cbArgs.length = cbArity →
      SpecEligibleList loopName fParam avoid cbArity stateArity cbArgs →
      SpecEligible loopName fParam avoid cbArity stateArity (.apply (.var fParam) cbArgs)
  | applyGen {fn : Expr} {args : List Expr} :
      (∀ z, fn = .var z → z ≠ fParam) →
      SpecEligible loopName fParam avoid cbArity stateArity fn →
      SpecEligibleList loopName fParam avoid cbArity stateArity args →
      SpecEligible loopName fParam avoid cbArity stateArity (.apply fn args)
  | selfCall {recArgs : List Expr} :
      recArgs.length = stateArity →
      SpecEligibleList loopName fParam avoid cbArity stateArity recArgs →
      SpecEligible loopName fParam avoid cbArity stateArity
        (.applyDir loopName (.var fParam :: recArgs))
  | applyDirGen {nm : Ident} {args : List Expr} :
      (∀ z rest, args = .var z :: rest → ¬ (nm == loopName && z == fParam)) →
      SpecEligibleList loopName fParam avoid cbArity stateArity args →
      SpecEligible loopName fParam avoid cbArity stateArity (.applyDir nm args)
  | bin {op : BinOp} {e1 e2 : Expr} :
      SpecEligible loopName fParam avoid cbArity stateArity e1 →
      SpecEligible loopName fParam avoid cbArity stateArity e2 →
      SpecEligible loopName fParam avoid cbArity stateArity (.bin op e1 e2)
  | un {op : UnOp} {e1 : Expr} :
      SpecEligible loopName fParam avoid cbArity stateArity e1 →
      SpecEligible loopName fParam avoid cbArity stateArity (.un op e1)
  | let_ {y : Ident} {e1 e2 : Expr} :
      y ∉ avoid →
      SpecEligible loopName fParam avoid cbArity stateArity e1 →
      SpecEligible loopName fParam avoid cbArity stateArity e2 →
      SpecEligible loopName fParam avoid cbArity stateArity (.let_ y e1 e2)
  | if_ {c t e2 : Expr} :
      SpecEligible loopName fParam avoid cbArity stateArity c →
      SpecEligible loopName fParam avoid cbArity stateArity t →
      SpecEligible loopName fParam avoid cbArity stateArity e2 →
      SpecEligible loopName fParam avoid cbArity stateArity (.if_ c t e2)
  | while_ {c b : Expr} :
      SpecEligible loopName fParam avoid cbArity stateArity c →
      SpecEligible loopName fParam avoid cbArity stateArity b →
      SpecEligible loopName fParam avoid cbArity stateArity (.while_ c b)
  | match_ {s : Expr} {arms : List (Pat × Expr)} :
      SpecEligible loopName fParam avoid cbArity stateArity s →
      SpecEligibleArms loopName fParam avoid cbArity stateArity arms →
      SpecEligible loopName fParam avoid cbArity stateArity (.match_ s arms)
  | makeData {adt : Ident} {tag : Nat} {es : List Expr} :
      SpecEligibleList loopName fParam avoid cbArity stateArity es →
      SpecEligible loopName fParam avoid cbArity stateArity (.makeData adt tag es)
  | getTag {e1 : Expr} :
      SpecEligible loopName fParam avoid cbArity stateArity e1 →
      SpecEligible loopName fParam avoid cbArity stateArity (.getTag e1)
  | cellNew {e1 : Expr} :
      SpecEligible loopName fParam avoid cbArity stateArity e1 →
      SpecEligible loopName fParam avoid cbArity stateArity (.cellNew e1)
  | cellGet {e1 : Expr} :
      SpecEligible loopName fParam avoid cbArity stateArity e1 →
      SpecEligible loopName fParam avoid cbArity stateArity (.cellGet e1)
  | cellSet {e1 e2 : Expr} :
      SpecEligible loopName fParam avoid cbArity stateArity e1 →
      SpecEligible loopName fParam avoid cbArity stateArity e2 →
      SpecEligible loopName fParam avoid cbArity stateArity (.cellSet e1 e2)

inductive SpecEligibleList (loopName fParam : Ident) (avoid : List Ident)
    (cbArity stateArity : Nat) : List Expr → Prop where
  | nil : SpecEligibleList loopName fParam avoid cbArity stateArity []
  | cons {e : Expr} {es : List Expr} :
      SpecEligible loopName fParam avoid cbArity stateArity e →
      SpecEligibleList loopName fParam avoid cbArity stateArity es →
      SpecEligibleList loopName fParam avoid cbArity stateArity (e :: es)

inductive SpecEligibleArms (loopName fParam : Ident) (avoid : List Ident)
    (cbArity stateArity : Nat) : List (Pat × Expr) → Prop where
  | nil : SpecEligibleArms loopName fParam avoid cbArity stateArity []
  | cons {p : Pat} {body : Expr} {rest : List (Pat × Expr)} :
      (∀ z ∈ patBoundNames p, z ∉ avoid) →
      SpecEligible loopName fParam avoid cbArity stateArity body →
      SpecEligibleArms loopName fParam avoid cbArity stateArity rest →
      SpecEligibleArms loopName fParam avoid cbArity stateArity ((p, body) :: rest)
end

/- Lockstep bisimulation relation `SpecRel` between the unspecialized execution
   (`loopName(cls, ...)` and `.apply cls ...`) and the `$spec$` specialized execution
   (`specName(fvVals..., ...)` and `.applyDir cbEntry (... ++ fvVals)`). -/
mutual
inductive SpecRel (loopName specName cbEntry : Ident) (cls : Expr) (fvVals : List Expr)
    (cbArity stateArity : Nat) : Expr → Expr → Prop where
  | lit (l : Lit) : SpecRel loopName specName cbEntry cls fvVals cbArity stateArity (.lit l) (.lit l)
  | var (x : Ident) : SpecRel loopName specName cbEntry cls fvVals cbArity stateArity (.var x) (.var x)
  | loc (l : Loc) : SpecRel loopName specName cbEntry cls fvVals cbArity stateArity (.loc l) (.loc l)
  | taskRef (tid : TaskId) :
      SpecRel loopName specName cbEntry cls fvVals cbArity stateArity (.taskRef tid) (.taskRef tid)
  | syncRef (k : SyncKind) (id : Nat) :
      SpecRel loopName specName cbEntry cls fvVals cbArity stateArity (.syncRef k id) (.syncRef k id)
  | lam (m : Mode) (ps : List (Ident × Ty)) (ret : Ty) (body : Expr) :
      SpecRel loopName specName cbEntry cls fvVals cbArity stateArity (.lam m ps ret body) (.lam m ps ret body)
  | trap (t : Trap) :
      SpecRel loopName specName cbEntry cls fvVals cbArity stateArity (.trap t) (.trap t)
  | tuple {es1 es2 : List Expr} :
      SpecRelList loopName specName cbEntry cls fvVals cbArity stateArity es1 es2 →
      SpecRel loopName specName cbEntry cls fvVals cbArity stateArity (.tuple es1) (.tuple es2)
  | block {es1 es2 : List Expr} :
      SpecRelList loopName specName cbEntry cls fvVals cbArity stateArity es1 es2 →
      SpecRel loopName specName cbEntry cls fvVals cbArity stateArity (.block es1) (.block es2)
  | specCb {args1 args2 : List Expr} :
      args1.length = cbArity →
      SpecRelList loopName specName cbEntry cls fvVals cbArity stateArity args1 args2 →
      SpecRel loopName specName cbEntry cls fvVals cbArity stateArity
        (.apply cls args1) (.applyDir cbEntry (args2 ++ fvVals))
  | apply {fn1 fn2 : Expr} {args1 args2 : List Expr} :
      SpecRel loopName specName cbEntry cls fvVals cbArity stateArity fn1 fn2 →
      SpecRelList loopName specName cbEntry cls fvVals cbArity stateArity args1 args2 →
      SpecRel loopName specName cbEntry cls fvVals cbArity stateArity (.apply fn1 args1) (.apply fn2 args2)
  | specCall {args1 args2 : List Expr} :
      args1.length = stateArity →
      SpecRelList loopName specName cbEntry cls fvVals cbArity stateArity args1 args2 →
      SpecRel loopName specName cbEntry cls fvVals cbArity stateArity
        (.applyDir loopName (cls :: args1)) (.applyDir specName (fvVals ++ args2))
  | applyDir {nm : Ident} {args1 args2 : List Expr} :
      SpecRelList loopName specName cbEntry cls fvVals cbArity stateArity args1 args2 →
      SpecRel loopName specName cbEntry cls fvVals cbArity stateArity (.applyDir nm args1) (.applyDir nm args2)
  | bin {op : BinOp} {a1 a2 b1 b2 : Expr} :
      SpecRel loopName specName cbEntry cls fvVals cbArity stateArity a1 a2 →
      SpecRel loopName specName cbEntry cls fvVals cbArity stateArity b1 b2 →
      SpecRel loopName specName cbEntry cls fvVals cbArity stateArity (.bin op a1 b1) (.bin op a2 b2)
  | un {op : UnOp} {e1 e2 : Expr} :
      SpecRel loopName specName cbEntry cls fvVals cbArity stateArity e1 e2 →
      SpecRel loopName specName cbEntry cls fvVals cbArity stateArity (.un op e1) (.un op e2)
  | let_ {x : Ident} {a1 a2 b1 b2 : Expr} :
      SpecRel loopName specName cbEntry cls fvVals cbArity stateArity a1 a2 →
      SpecRel loopName specName cbEntry cls fvVals cbArity stateArity b1 b2 →
      SpecRel loopName specName cbEntry cls fvVals cbArity stateArity (.let_ x a1 b1) (.let_ x a2 b2)
  | if_ {c1 c2 t1 t2 e1 e2 : Expr} :
      SpecRel loopName specName cbEntry cls fvVals cbArity stateArity c1 c2 →
      SpecRel loopName specName cbEntry cls fvVals cbArity stateArity t1 t2 →
      SpecRel loopName specName cbEntry cls fvVals cbArity stateArity e1 e2 →
      SpecRel loopName specName cbEntry cls fvVals cbArity stateArity (.if_ c1 t1 e1) (.if_ c2 t2 e2)
  | while_ {c1 c2 b1 b2 : Expr} :
      SpecRel loopName specName cbEntry cls fvVals cbArity stateArity c1 c2 →
      SpecRel loopName specName cbEntry cls fvVals cbArity stateArity b1 b2 →
      SpecRel loopName specName cbEntry cls fvVals cbArity stateArity (.while_ c1 b1) (.while_ c2 b2)
  | match_ {s1 s2 : Expr} {arms1 arms2 : List (Pat × Expr)} :
      SpecRel loopName specName cbEntry cls fvVals cbArity stateArity s1 s2 →
      SpecRelArms loopName specName cbEntry cls fvVals cbArity stateArity arms1 arms2 →
      SpecRel loopName specName cbEntry cls fvVals cbArity stateArity (.match_ s1 arms1) (.match_ s2 arms2)
  | makeData {adt : Ident} {tag : Nat} {es1 es2 : List Expr} :
      SpecRelList loopName specName cbEntry cls fvVals cbArity stateArity es1 es2 →
      SpecRel loopName specName cbEntry cls fvVals cbArity stateArity
        (.makeData adt tag es1) (.makeData adt tag es2)
  | getTag {e1 e2 : Expr} :
      SpecRel loopName specName cbEntry cls fvVals cbArity stateArity e1 e2 →
      SpecRel loopName specName cbEntry cls fvVals cbArity stateArity (.getTag e1) (.getTag e2)
  | cellNew {e1 e2 : Expr} :
      SpecRel loopName specName cbEntry cls fvVals cbArity stateArity e1 e2 →
      SpecRel loopName specName cbEntry cls fvVals cbArity stateArity (.cellNew e1) (.cellNew e2)
  | cellGet {e1 e2 : Expr} :
      SpecRel loopName specName cbEntry cls fvVals cbArity stateArity e1 e2 →
      SpecRel loopName specName cbEntry cls fvVals cbArity stateArity (.cellGet e1) (.cellGet e2)
  | cellSet {a1 a2 b1 b2 : Expr} :
      SpecRel loopName specName cbEntry cls fvVals cbArity stateArity a1 a2 →
      SpecRel loopName specName cbEntry cls fvVals cbArity stateArity b1 b2 →
      SpecRel loopName specName cbEntry cls fvVals cbArity stateArity (.cellSet a1 b1) (.cellSet a2 b2)
  | spawn {e1 e2 : Expr} :
      SpecRel loopName specName cbEntry cls fvVals cbArity stateArity e1 e2 →
      SpecRel loopName specName cbEntry cls fvVals cbArity stateArity (.spawn e1) (.spawn e2)
  | await {e1 e2 : Expr} :
      SpecRel loopName specName cbEntry cls fvVals cbArity stateArity e1 e2 →
      SpecRel loopName specName cbEntry cls fvVals cbArity stateArity (.await e1) (.await e2)
  | concPrim {op : ConcPrim} {args1 args2 : List Expr} :
      SpecRelList loopName specName cbEntry cls fvVals cbArity stateArity args1 args2 →
      SpecRel loopName specName cbEntry cls fvVals cbArity stateArity (.concPrim op args1) (.concPrim op args2)

inductive SpecRelList (loopName specName cbEntry : Ident) (cls : Expr) (fvVals : List Expr)
    (cbArity stateArity : Nat) : List Expr → List Expr → Prop where
  | nil : SpecRelList loopName specName cbEntry cls fvVals cbArity stateArity [] []
  | cons {e1 e2 : Expr} {es1 es2 : List Expr} :
      SpecRel loopName specName cbEntry cls fvVals cbArity stateArity e1 e2 →
      SpecRelList loopName specName cbEntry cls fvVals cbArity stateArity es1 es2 →
      SpecRelList loopName specName cbEntry cls fvVals cbArity stateArity (e1 :: es1) (e2 :: es2)

inductive SpecRelArms (loopName specName cbEntry : Ident) (cls : Expr) (fvVals : List Expr)
    (cbArity stateArity : Nat) : List (Pat × Expr) → List (Pat × Expr) → Prop where
  | nil : SpecRelArms loopName specName cbEntry cls fvVals cbArity stateArity [] []
  | cons {p : Pat} {b1 b2 : Expr} {r1 r2 : List (Pat × Expr)} :
      SpecRel loopName specName cbEntry cls fvVals cbArity stateArity b1 b2 →
      SpecRelArms loopName specName cbEntry cls fvVals cbArity stateArity r1 r2 →
      SpecRelArms loopName specName cbEntry cls fvVals cbArity stateArity ((p, b1) :: r1) ((p, b2) :: r2)
end

mutual
theorem SpecRel.refl (loopName specName cbEntry : Ident) (cls : Expr) (fvVals : List Expr)
    (cbArity stateArity : Nat) :
    (e : Expr) → SpecRel loopName specName cbEntry cls fvVals cbArity stateArity e e
  | .lit l => .lit l
  | .var x => .var x
  | .loc l => .loc l
  | .taskRef tid => .taskRef tid
  | .syncRef k id => .syncRef k id
  | .lam m ps ret body => .lam m ps ret body
  | .trap t => .trap t
  | .tuple es => .tuple (SpecRelList.refl loopName specName cbEntry cls fvVals cbArity stateArity es)
  | .block es => .block (SpecRelList.refl loopName specName cbEntry cls fvVals cbArity stateArity es)
  | .apply fn args =>
    .apply (SpecRel.refl loopName specName cbEntry cls fvVals cbArity stateArity fn)
      (SpecRelList.refl loopName specName cbEntry cls fvVals cbArity stateArity args)
  | .applyDir nm args =>
    .applyDir (SpecRelList.refl loopName specName cbEntry cls fvVals cbArity stateArity args)
  | .bin op a b =>
    .bin (SpecRel.refl loopName specName cbEntry cls fvVals cbArity stateArity a)
      (SpecRel.refl loopName specName cbEntry cls fvVals cbArity stateArity b)
  | .un op e1 => .un (SpecRel.refl loopName specName cbEntry cls fvVals cbArity stateArity e1)
  | .let_ x a b =>
    .let_ (SpecRel.refl loopName specName cbEntry cls fvVals cbArity stateArity a)
      (SpecRel.refl loopName specName cbEntry cls fvVals cbArity stateArity b)
  | .if_ c t e2 =>
    .if_ (SpecRel.refl loopName specName cbEntry cls fvVals cbArity stateArity c)
      (SpecRel.refl loopName specName cbEntry cls fvVals cbArity stateArity t)
      (SpecRel.refl loopName specName cbEntry cls fvVals cbArity stateArity e2)
  | .while_ c b =>
    .while_ (SpecRel.refl loopName specName cbEntry cls fvVals cbArity stateArity c)
      (SpecRel.refl loopName specName cbEntry cls fvVals cbArity stateArity b)
  | .match_ s arms =>
    .match_ (SpecRel.refl loopName specName cbEntry cls fvVals cbArity stateArity s)
      (SpecRelArms.refl loopName specName cbEntry cls fvVals cbArity stateArity arms)
  | .makeData adt tag es =>
    .makeData (SpecRelList.refl loopName specName cbEntry cls fvVals cbArity stateArity es)
  | .getTag e1 => .getTag (SpecRel.refl loopName specName cbEntry cls fvVals cbArity stateArity e1)
  | .cellNew e1 => .cellNew (SpecRel.refl loopName specName cbEntry cls fvVals cbArity stateArity e1)
  | .cellGet e1 => .cellGet (SpecRel.refl loopName specName cbEntry cls fvVals cbArity stateArity e1)
  | .cellSet a b =>
    .cellSet (SpecRel.refl loopName specName cbEntry cls fvVals cbArity stateArity a)
      (SpecRel.refl loopName specName cbEntry cls fvVals cbArity stateArity b)
  | .spawn e1 => .spawn (SpecRel.refl loopName specName cbEntry cls fvVals cbArity stateArity e1)
  | .await e1 => .await (SpecRel.refl loopName specName cbEntry cls fvVals cbArity stateArity e1)
  | .concPrim op args =>
    .concPrim (SpecRelList.refl loopName specName cbEntry cls fvVals cbArity stateArity args)
termination_by e => sizeOf e

theorem SpecRelList.refl (loopName specName cbEntry : Ident) (cls : Expr) (fvVals : List Expr)
    (cbArity stateArity : Nat) :
    (es : List Expr) → SpecRelList loopName specName cbEntry cls fvVals cbArity stateArity es es
  | [] => .nil
  | e :: es =>
    .cons (SpecRel.refl loopName specName cbEntry cls fvVals cbArity stateArity e)
      (SpecRelList.refl loopName specName cbEntry cls fvVals cbArity stateArity es)
termination_by es => sizeOf es

theorem SpecRelArms.refl (loopName specName cbEntry : Ident) (cls : Expr) (fvVals : List Expr)
    (cbArity stateArity : Nat) :
    (arms : List (Pat × Expr)) → SpecRelArms loopName specName cbEntry cls fvVals cbArity stateArity arms arms
  | [] => .nil
  | (_, b) :: rest =>
    .cons (SpecRel.refl loopName specName cbEntry cls fvVals cbArity stateArity b)
      (SpecRelArms.refl loopName specName cbEntry cls fvVals cbArity stateArity rest)
termination_by arms => sizeOf arms
end

/- On values, `SpecRel` coincides with syntactic equality (`e1 = e2`). -/
mutual
theorem specRel_val_left {loopName specName cbEntry : Ident} {cls : Expr} {fvVals : List Expr}
    {cbArity stateArity : Nat} {e1 e2 : Expr}
    (hr : SpecRel loopName specName cbEntry cls fvVals cbArity stateArity e1 e2)
    (hv1 : IsValue e1) : e1 = e2 ∧ IsValue e2 := by
  cases hr with
  | lit _ | loc _ | taskRef _ | syncRef _ _ | lam _ _ _ _ => exact ⟨rfl, hv1⟩
  | tuple hrl =>
    cases hv1 with
    | tuple hvs1 =>
      rcases specRelList_val_left hrl hvs1 with ⟨rfl, hvs2⟩
      exact ⟨rfl, .tuple hvs2⟩
  | @makeData adt tag _ _ hrl =>
    cases hv1 with
    | makeData _ _ hvs1 =>
      rcases specRelList_val_left hrl hvs1 with ⟨rfl, hvs2⟩
      exact ⟨rfl, .makeData adt tag hvs2⟩
  | var _ | trap _ | block _ | specCb _ _ | apply _ _ | specCall _ _ | applyDir _
  | bin _ _ | un _ | let_ _ _ | if_ _ _ _ | while_ _ _ | match_ _ _
  | getTag _ | cellNew _ | cellGet _ | cellSet _ _ | spawn _ | await _ | concPrim _ =>
    cases hv1
termination_by sizeOf e1

theorem specRelList_val_left {loopName specName cbEntry : Ident} {cls : Expr} {fvVals : List Expr}
    {cbArity stateArity : Nat} {es1 es2 : List Expr}
    (hrl : SpecRelList loopName specName cbEntry cls fvVals cbArity stateArity es1 es2)
    (hvs1 : ∀ v ∈ es1, IsValue v) : es1 = es2 ∧ (∀ v ∈ es2, IsValue v) := by
  cases hrl with
  | nil => exact ⟨rfl, fun _ h => by cases h⟩
  | cons hr hrs =>
    rcases specRel_val_left hr (hvs1 _ (List.mem_cons_self ..)) with ⟨rfl, hv2⟩
    rcases specRelList_val_left hrs (fun x hx => hvs1 x (List.mem_cons_of_mem _ hx)) with ⟨rfl, hvs2⟩
    exact ⟨rfl, fun x hx => by rcases List.mem_cons.mp hx with rfl | hxr; exact hv2; exact hvs2 x hxr⟩
termination_by sizeOf es1
end

mutual
theorem specRel_val_right {loopName specName cbEntry : Ident} {cls : Expr} {fvVals : List Expr}
    {cbArity stateArity : Nat} {e1 e2 : Expr}
    (hr : SpecRel loopName specName cbEntry cls fvVals cbArity stateArity e1 e2)
    (hv2 : IsValue e2) : e1 = e2 ∧ IsValue e1 := by
  cases hr with
  | lit _ | loc _ | taskRef _ | syncRef _ _ | lam _ _ _ _ => exact ⟨rfl, hv2⟩
  | tuple hrl =>
    cases hv2 with
    | tuple hvs2 =>
      rcases specRelList_val_right hrl hvs2 with ⟨rfl, hvs1⟩
      exact ⟨rfl, .tuple hvs1⟩
  | @makeData adt tag _ _ hrl =>
    cases hv2 with
    | makeData _ _ hvs2 =>
      rcases specRelList_val_right hrl hvs2 with ⟨rfl, hvs1⟩
      exact ⟨rfl, .makeData adt tag hvs1⟩
  | var _ | trap _ | block _ | specCb _ _ | apply _ _ | specCall _ _ | applyDir _
  | bin _ _ | un _ | let_ _ _ | if_ _ _ _ | while_ _ _ | match_ _ _
  | getTag _ | cellNew _ | cellGet _ | cellSet _ _ | spawn _ | await _ | concPrim _ =>
    cases hv2
termination_by sizeOf e2

theorem specRelList_val_right {loopName specName cbEntry : Ident} {cls : Expr} {fvVals : List Expr}
    {cbArity stateArity : Nat} {es1 es2 : List Expr}
    (hrl : SpecRelList loopName specName cbEntry cls fvVals cbArity stateArity es1 es2)
    (hvs2 : ∀ v ∈ es2, IsValue v) : es1 = es2 ∧ (∀ v ∈ es1, IsValue v) := by
  cases hrl with
  | nil => exact ⟨rfl, fun _ h => by cases h⟩
  | cons hr hrs =>
    rcases specRel_val_right hr (hvs2 _ (List.mem_cons_self ..)) with ⟨rfl, hv1⟩
    rcases specRelList_val_right hrs (fun x hx => hvs2 x (List.mem_cons_of_mem _ hx)) with ⟨rfl, hvs1⟩
    exact ⟨rfl, fun x hx => by rcases List.mem_cons.mp hx with rfl | hxr; exact hv1; exact hvs1 x hxr⟩
termination_by sizeOf es2
end

theorem specRel_trap_left {loopName specName cbEntry : Ident} {cls : Expr} {fvVals : List Expr}
    {cbArity stateArity : Nat} {e2 : Expr} {t : Trap}
    (hr : SpecRel loopName specName cbEntry cls fvVals cbArity stateArity (.trap t) e2) :
    e2 = .trap t := by
  cases hr; rfl

theorem specRel_trap_right {loopName specName cbEntry : Ident} {cls : Expr} {fvVals : List Expr}
    {cbArity stateArity : Nat} {e1 : Expr} {t : Trap}
    (hr : SpecRel loopName specName cbEntry cls fvVals cbArity stateArity e1 (.trap t)) :
    e1 = .trap t := by
  cases hr; rfl

theorem specRel_terminal_left {loopName specName cbEntry : Ident} {cls : Expr} {fvVals : List Expr}
    {cbArity stateArity : Nat} {out e2 : Expr}
    (hr : SpecRel loopName specName cbEntry cls fvVals cbArity stateArity out e2)
    (hout : IsTerminal out) : e2 = out := by
  rcases hout with hv | ⟨t, rfl⟩
  · exact (specRel_val_left hr hv).1.symm
  · exact specRel_trap_left hr

theorem specRel_terminal_right {loopName specName cbEntry : Ident} {cls : Expr} {fvVals : List Expr}
    {cbArity stateArity : Nat} {e1 out : Expr}
    (hr : SpecRel loopName specName cbEntry cls fvVals cbArity stateArity e1 out)
    (hout : IsTerminal out) : e1 = out := by
  rcases hout with hv | ⟨t, rfl⟩
  · exact (specRel_val_right hr hv).1
  · exact specRel_trap_right hr

theorem specRelList_firstTrap_iff {loopName specName cbEntry : Ident} {cls : Expr} {fvVals : List Expr}
    {cbArity stateArity : Nat} {es1 es2 : List Expr} {t : Trap}
    (hrl : SpecRelList loopName specName cbEntry cls fvVals cbArity stateArity es1 es2) :
    ListFirstTrap es1 t ↔ ListFirstTrap es2 t := by
  induction es1 generalizing es2 with
  | nil =>
    cases hrl
    constructor <;> (intro h; cases h)
  | cons _ _ ih =>
    cases hrl with
    | cons hr hrs =>
      constructor
      · intro h
        cases h with
        | head _ _ =>
          rw [specRel_trap_left hr]; exact .head _ _
        | tail hv1 htr1 =>
          rcases specRel_val_left hr hv1 with ⟨rfl, hv2⟩
          exact .tail hv2 ((ih hrs).mp htr1)
      · intro h
        cases h with
        | head _ _ =>
          rw [specRel_trap_right hr]; exact .head _ _
        | tail hv2 htr2 =>
          rcases specRel_val_right hr hv2 with ⟨rfl, hv1⟩
          exact .tail hv1 ((ih hrs).mpr htr2)

theorem stepList_length_eq {Δ : AdtEnv} {Φ : FunEnv} {pool : ConcPool}
    {xs ys : List Expr} {σ σ' : Store} {eff : ConcEff}
    (hsl : StepList Δ Φ pool xs σ ys σ' eff) : ys.length = xs.length := by
  induction xs generalizing ys with
  | nil => cases hsl
  | cons _ _ ih =>
    cases hsl with
    | head _ => rfl
    | tail _ hsl' => simp [ih hsl']

/-- Suffix value helpers for `StepList` and `ListFirstTrap`. -/
theorem stepList_append_vals_forward {Δ : AdtEnv} {Φ : FunEnv} {pool : ConcPool}
    {es es' vs : List Expr} {σ σ' : Store} {eff : ConcEff}
    (hsl : StepList Δ Φ pool es σ es' σ' eff) :
    StepList Δ Φ pool (es ++ vs) σ (es' ++ vs) σ' eff := by
  induction es generalizing es' with
  | nil => cases hsl
  | cons _ _ ih =>
    cases hsl with
    | head hs => exact .head hs
    | tail hv hsl' => exact .tail hv (ih hsl')

theorem stepList_append_vals_inv {Δ : AdtEnv} {Φ : FunEnv} {pool : ConcPool}
    {es vs full' : List Expr} {σ σ' : Store} {eff : ConcEff}
    (hvs : ∀ v ∈ vs, IsValue v)
    (h : StepList Δ Φ pool (es ++ vs) σ full' σ' eff) :
    ∃ es', full' = es' ++ vs ∧ StepList Δ Φ pool es σ es' σ' eff := by
  induction es generalizing full' with
  | nil => exact False.elim (isValueList_no_step hvs h)
  | cons e er ih =>
    cases h with
    | head hs => exact ⟨_ :: er, rfl, .head hs⟩
    | tail hv hsl =>
      rcases ih hsl with ⟨er', rfl, hsl'⟩
      exact ⟨e :: er', rfl, .tail hv hsl'⟩

theorem listFirstTrap_append_vals_iff {es vs : List Expr} {t : Trap}
    (hvs : ∀ v ∈ vs, IsValue v) :
    ListFirstTrap (es ++ vs) t ↔ ListFirstTrap es t := by
  induction es with
  | nil =>
    constructor
    · intro h; exact False.elim (isValueList_no_trap hvs h)
    · intro h; cases h
  | cons e er ih =>
    constructor
    · intro h
      cases h with
      | head _ _ => exact .head _ _
      | tail hv htr => exact .tail hv (ih.mp htr)
    · intro h
      cases h with
      | head _ _ => exact .head _ _
      | tail hv htr => exact .tail hv (ih.mpr htr)

private theorem substList_closed_id (x : Ident) (v : Expr) (ws : List Expr)
    (hws : ∀ w ∈ ws, freeVars w = []) :
    substList x v ws = ws := by
  induction ws with
  | nil => rfl
  | cons w wr ih =>
    have hw : x ∉ freeVars w := by simp [hws w (List.mem_cons_self ..)]
    have hrec := ih (fun u hu => hws u (List.mem_cons_of_mem _ hu))
    simp [substList, subst_not_mem_freeVars w hw, hrec]

private theorem substList_append_eq (x : Ident) (v : Expr) (as bs : List Expr) :
    substList x v (as ++ bs) = substList x v as ++ substList x v bs := by
  induction as with
  | nil => rfl
  | cons a ar ih => simp [substList, ih]

private theorem substList_length_eq (x : Ident) (v : Expr) (as : List Expr) :
    (substList x v as).length = as.length := by
  induction as with
  | nil => rfl
  | cons _ _ ih => simp [substList, ih]

/- `SpecRel` is preserved under substituting any closed value `v`. -/
mutual
theorem specRel_subst {loopName specName cbEntry : Ident} {cls : Expr} {fvVals : List Expr}
    {cbArity stateArity : Nat} (hcls : freeVars cls = []) (hfv : ∀ w ∈ fvVals, freeVars w = [])
    (x : Ident) {v : Expr} (hv : freeVars v = [])
    {e1 e2 : Expr}
    (hr : SpecRel loopName specName cbEntry cls fvVals cbArity stateArity e1 e2) :
    SpecRel loopName specName cbEntry cls fvVals cbArity stateArity (subst x v e1) (subst x v e2) := by
  cases hr with
  | lit l => exact .lit l
  | loc l => exact .loc l
  | taskRef tid => exact .taskRef tid
  | syncRef k id => exact .syncRef k id
  | trap t => exact .trap t
  | var z =>
    simp only [subst]
    split
    · exact SpecRel.refl _ _ _ _ _ _ _ v
    · exact .var z
  | lam m ps ret body =>
    simp only [subst]
    split <;> exact .lam _ _ _ _
  | tuple hrl => exact .tuple (specRelList_subst hcls hfv x hv hrl)
  | block hrl => exact .block (specRelList_subst hcls hfv x hv hrl)
  | @specCb args1 args2 hlen hrl =>
    have hcls_sub : subst x v cls = cls := subst_not_mem_freeVars cls (by simp [hcls])
    have hfv_sub : substList x v fvVals = fvVals := substList_closed_id x v fvVals hfv
    have hlen' : (substList x v args1).length = cbArity := by
      rw [substList_length_eq]; exact hlen
    simp only [subst, hcls_sub, substList_append_eq, hfv_sub]
    exact .specCb hlen' (specRelList_subst hcls hfv x hv hrl)
  | apply hfn hrl =>
    exact .apply (specRel_subst hcls hfv x hv hfn) (specRelList_subst hcls hfv x hv hrl)
  | @specCall args1 args2 hlen hrl =>
    have hcls_sub : subst x v cls = cls := subst_not_mem_freeVars cls (by simp [hcls])
    have hfv_sub : substList x v fvVals = fvVals := substList_closed_id x v fvVals hfv
    have hlen' : (substList x v args1).length = stateArity := by
      rw [substList_length_eq]; exact hlen
    simp only [subst, substList, hcls_sub, substList_append_eq, hfv_sub]
    exact .specCall hlen' (specRelList_subst hcls hfv x hv hrl)
  | applyDir hrl => exact .applyDir (specRelList_subst hcls hfv x hv hrl)
  | bin ha hb => exact .bin (specRel_subst hcls hfv x hv ha) (specRel_subst hcls hfv x hv hb)
  | un he => exact .un (specRel_subst hcls hfv x hv he)
  | let_ ha hb =>
    simp only [subst]
    split
    · exact .let_ (specRel_subst hcls hfv x hv ha) hb
    · exact .let_ (specRel_subst hcls hfv x hv ha) (specRel_subst hcls hfv x hv hb)
  | if_ hc ht he =>
    exact .if_ (specRel_subst hcls hfv x hv hc) (specRel_subst hcls hfv x hv ht)
      (specRel_subst hcls hfv x hv he)
  | while_ hc hb =>
    exact .while_ (specRel_subst hcls hfv x hv hc) (specRel_subst hcls hfv x hv hb)
  | match_ hs harms =>
    exact .match_ (specRel_subst hcls hfv x hv hs) (specRelArms_subst hcls hfv x hv harms)
  | makeData hrl => exact .makeData (specRelList_subst hcls hfv x hv hrl)
  | getTag he => exact .getTag (specRel_subst hcls hfv x hv he)
  | cellNew he => exact .cellNew (specRel_subst hcls hfv x hv he)
  | cellGet he => exact .cellGet (specRel_subst hcls hfv x hv he)
  | cellSet ha hb =>
    exact .cellSet (specRel_subst hcls hfv x hv ha) (specRel_subst hcls hfv x hv hb)
  | spawn he => exact .spawn (specRel_subst hcls hfv x hv he)
  | await he => exact .await (specRel_subst hcls hfv x hv he)
  | concPrim hrl => exact .concPrim (specRelList_subst hcls hfv x hv hrl)
termination_by sizeOf e1

theorem specRelList_subst {loopName specName cbEntry : Ident} {cls : Expr} {fvVals : List Expr}
    {cbArity stateArity : Nat} (hcls : freeVars cls = []) (hfv : ∀ w ∈ fvVals, freeVars w = [])
    (x : Ident) {v : Expr} (hv : freeVars v = [])
    {es1 es2 : List Expr}
    (hrl : SpecRelList loopName specName cbEntry cls fvVals cbArity stateArity es1 es2) :
    SpecRelList loopName specName cbEntry cls fvVals cbArity stateArity (substList x v es1) (substList x v es2) := by
  cases hrl with
  | nil => exact .nil
  | cons hr hrs =>
    exact .cons (specRel_subst hcls hfv x hv hr) (specRelList_subst hcls hfv x hv hrs)
termination_by sizeOf es1

theorem specRelArms_subst {loopName specName cbEntry : Ident} {cls : Expr} {fvVals : List Expr}
    {cbArity stateArity : Nat} (hcls : freeVars cls = []) (hfv : ∀ w ∈ fvVals, freeVars w = [])
    (x : Ident) {v : Expr} (hv : freeVars v = [])
    {arms1 arms2 : List (Pat × Expr)}
    (harms : SpecRelArms loopName specName cbEntry cls fvVals cbArity stateArity arms1 arms2) :
    SpecRelArms loopName specName cbEntry cls fvVals cbArity stateArity (substArms x v arms1) (substArms x v arms2) := by
  cases harms with
  | nil => exact .nil
  | cons hb hrs =>
    simp only [substArms]
    split
    · exact .cons hb (specRelArms_subst hcls hfv x hv hrs)
    · exact .cons (specRel_subst hcls hfv x hv hb) (specRelArms_subst hcls hfv x hv hrs)
termination_by sizeOf arms1
end

theorem specRel_substMany {loopName specName cbEntry : Ident} {cls : Expr} {fvVals : List Expr}
    {cbArity stateArity : Nat} (hcls : freeVars cls = []) (hfv : ∀ w ∈ fvVals, freeVars w = [])
    {ρ : List (Ident × Expr)} (hρ : ∀ p ∈ ρ, freeVars p.2 = [])
    {e1 e2 : Expr}
    (hr : SpecRel loopName specName cbEntry cls fvVals cbArity stateArity e1 e2) :
    SpecRel loopName specName cbEntry cls fvVals cbArity stateArity
      (substMany ρ e1) (substMany ρ e2) := by
  induction ρ generalizing e1 e2 with
  | nil => exact hr
  | cons p rest ih =>
    rcases p with ⟨x, v⟩
    exact ih (fun q hq => hρ q (List.mem_cons_of_mem _ hq))
      (specRel_subst hcls hfv x (hρ (x, v) (List.mem_cons_self ..)) hr)

private theorem substList_eq_map' (x : Ident) (v : Expr) (es : List Expr) :
    substList x v es = es.map (subst x v) := by
  induction es with | nil => rfl | cons _ _ ih => simp [substList, ih]

private theorem substMany_map_helper (ρ : List (Ident × Expr)) :
    (∀ es, substMany ρ (.tuple es) = .tuple (es.map (substMany ρ))) ∧
    (∀ es, substMany ρ (.block es) = .block (es.map (substMany ρ))) ∧
    (∀ fn args, substMany ρ (.apply fn args) = .apply (substMany ρ fn) (args.map (substMany ρ))) ∧
    (∀ nm args, substMany ρ (.applyDir nm args) = .applyDir nm (args.map (substMany ρ))) ∧
    (∀ adt tag es, substMany ρ (.makeData adt tag es) = .makeData adt tag (es.map (substMany ρ))) := by
  induction ρ with
  | nil => simp [substMany]
  | cons p rest ih =>
    rcases p with ⟨x, v⟩
    rcases ih with ⟨htup, hblk, happ, hdir, hdat⟩
    refine ⟨?_, ?_, ?_, ?_, ?_⟩
    · intro es; simp only [substMany, subst, substList_eq_map', htup, List.map_map]; rfl
    · intro es; simp only [substMany, subst, substList_eq_map', hblk, List.map_map]; rfl
    · intro fn args; simp only [substMany, subst, substList_eq_map', happ, List.map_map]; rfl
    · intro nm args; simp only [substMany, subst, substList_eq_map', hdir, List.map_map]; rfl
    · intro adt tag es; simp only [substMany, subst, substList_eq_map', hdat, List.map_map]; rfl

private theorem substMany_let_not_mem (ρ : List (Ident × Expr)) {y : Ident} (hy : y ∉ ρ.map Prod.fst)
    (e1 e2 : Expr) :
    substMany ρ (.let_ y e1 e2) = .let_ y (substMany ρ e1) (substMany ρ e2) := by
  induction ρ generalizing e1 e2 with
  | nil => rfl
  | cons p rest ih =>
    rcases p with ⟨x, v⟩
    simp only [List.map_cons, List.mem_cons, not_or] at hy
    have hyx : (y == x) = false := beq_false_of_ne hy.1
    simp [substMany, subst, hyx, ih hy.2]

private theorem substMany_match_disjoint (ρ : List (Ident × Expr)) (s : Expr)
    (arms : List (Pat × Expr))
    (hdisj : ∀ a ∈ arms, ∀ z ∈ patBoundNames a.1, z ∉ ρ.map Prod.fst) :
    substMany ρ (.match_ s arms) =
      .match_ (substMany ρ s) (arms.map fun a => (a.1, substMany ρ a.2)) := by
  induction ρ generalizing s arms with
  | nil => simp [substMany]
  | cons p rest ih =>
    rcases p with ⟨x, v⟩
    have harms_sub : substArms x v arms = arms.map (fun a => (a.1, subst x v a.2)) := by
      induction arms with
      | nil => rfl
      | cons a ar iha =>
        have hnotc : (patBoundNames a.1).contains x = false := by
          cases h : (patBoundNames a.1).contains x
          · rfl
          · exact False.elim (hdisj a (List.mem_cons_self ..) x
              (List.contains_iff_mem.mp h) (List.mem_cons_self ..))
        have hrec := iha (fun b hb => hdisj b (List.mem_cons_of_mem _ hb))
        simp only [substArms, hnotc, Bool.false_eq_true, ↓reduceIte, hrec, List.map_cons]
    have hdisj' : ∀ b ∈ arms.map (fun a : Pat × Expr => (a.1, subst x v a.2)),
        ∀ z ∈ patBoundNames b.1, z ∉ rest.map Prod.fst := by
      intro b hb z hz hmem
      rcases List.mem_map.mp hb with ⟨a, ha, rfl⟩
      exact hdisj a ha z hz (List.mem_cons_of_mem _ hmem)
    simp only [substMany, subst, harms_sub, ih _ _ hdisj', List.map_map]; rfl

private theorem substMany_closed_val_id (ρ : List (Ident × Expr)) {v : Expr}
    (hv : freeVars v = []) : substMany ρ v = v := by
  induction ρ with
  | nil => rfl
  | cons q qr ih =>
    simp only [substMany]
    rw [subst_not_mem_freeVars v (by simp [hv])]
    exact ih

private theorem map_substMany_zipParams_vars_aux {fvs stateParams : List (Ident × Ty)}
    {fvVals stateVals : List Expr}
    (hnodup : (fvs.map Prod.fst ++ stateParams.map Prod.fst).Nodup)
    (hfvLen : fvVals.length = fvs.length)
    (hfvCl : ∀ v ∈ fvVals, freeVars v = []) :
    (fvs.map (fun p => Expr.var p.1)).map
      (substMany (zipParams (fvs ++ stateParams) (fvVals ++ stateVals))) = fvVals := by
  induction fvs generalizing fvVals with
  | nil => cases fvVals <;> simp at hfvLen ⊢
  | cons fd fr ih =>
    cases fvVals with
    | nil => simp at hfvLen
    | cons v vr =>
      simp only [List.length_cons, Nat.succ.injEq] at hfvLen
      simp only [List.map_cons, List.cons_append] at hnodup ⊢
      rcases List.nodup_cons.mp hnodup with ⟨hfd_not, hnodup_rest⟩
      have hv_cl : freeVars v = [] := hfvCl v (List.mem_cons_self ..)
      have hvr_cl : ∀ w ∈ vr, freeVars w = [] := fun w hw => hfvCl w (List.mem_cons_of_mem _ hw)
      have hhead : substMany (zipParams (fd :: (fr ++ stateParams)) (v :: (vr ++ stateVals))) (.var fd.1) = v := by
        simp only [zipParams, List.map_cons, List.zip_cons_cons, substMany, subst, beq_self_eq_true, ↓reduceIte]
        exact substMany_closed_val_id _ hv_cl
      have hmap_rest :
          (fr.map (fun p => Expr.var p.1)).map
            (substMany (zipParams (fd :: (fr ++ stateParams)) (v :: (vr ++ stateVals)))) =
          (fr.map (fun p => Expr.var p.1)).map
            (substMany (zipParams (fr ++ stateParams) (vr ++ stateVals))) := by
        apply List.map_congr_left
        intro e he
        rcases List.mem_map.mp he with ⟨p, hp, rfl⟩
        have hpne : p.1 ≠ fd.1 := by
          intro heq
          apply hfd_not
          rw [← heq]
          exact List.mem_append_left _ (List.mem_map.mpr ⟨p, hp, rfl⟩)
        have hbeq : (p.1 == fd.1) = false := beq_false_of_ne hpne
        simp [zipParams, substMany, subst, hbeq]
      rw [hhead, hmap_rest, ih hnodup_rest hfvLen hvr_cl]

private theorem map_substMany_zipParams_vars {fvs stateParams : List (Ident × Ty)}
    {fvVals stateVals : List Expr}
    (hnodup : (fvs.map Prod.fst ++ stateParams.map Prod.fst).Nodup)
    (hfvLen : fvVals.length = fvs.length)
    (hfvCl : ∀ v ∈ fvVals, freeVars v = []) :
    ((fvs.map Prod.fst).map Expr.var).map
      (substMany (zipParams (fvs ++ stateParams) (fvVals ++ stateVals))) = fvVals := by
  have hm : (fvs.map Prod.fst).map Expr.var = fvs.map (fun p => Expr.var p.1) := List.map_map
  rw [hm]
  exact map_substMany_zipParams_vars_aux (stateVals := stateVals) hnodup hfvLen hfvCl

/- Loop Body Specialization Substitution Lemma (`specEligible_subst_rel`). -/
mutual
theorem specEligible_subst_rel
    (loopName specName cbEntry fParam : Ident) (fnTy : Ty)
    {fvs stateParams : List (Ident × Ty)}
    {cls : Expr} {fvVals stateVals : List Expr}
    {cbArity stateArity : Nat}
    (hcls : freeVars cls = [])
    (hfvCl : ∀ v ∈ fvVals, freeVars v = [])
    (hfvLen : fvVals.length = fvs.length)
    (hstLen : stateVals.length = stateParams.length)
    (hnodup : (fvs.map Prod.fst ++ stateParams.map Prod.fst).Nodup)
    {e : Expr}
    (hnoFv : ∀ z ∈ freeVars e, z ∉ fvs.map Prod.fst)
    (helig : SpecEligible loopName fParam (fParam :: (fvs.map Prod.fst ++ stateParams.map Prod.fst))
      cbArity stateArity e) :
    SpecRel loopName specName cbEntry cls fvVals cbArity stateArity
      (substMany (zipParams ((fParam, fnTy) :: stateParams) (cls :: stateVals)) e)
      (substMany (zipParams (fvs ++ stateParams) (fvVals ++ stateVals))
        (specializeLoopExpr loopName specName cbEntry fParam (fvs.map Prod.fst) e)) := by
  cases helig with
  | lit l =>
    have h1 : ∀ ρ, substMany ρ (.lit l) = .lit l := fun ρ => by
      induction ρ with | nil => rfl | cons _ _ ih => exact ih
    rw [specializeLoopExpr, h1, h1]; exact .lit l
  | loc l =>
    have h1 : ∀ ρ, substMany ρ (.loc l) = .loc l := fun ρ => by
      induction ρ with | nil => rfl | cons _ _ ih => exact ih
    rw [specializeLoopExpr, h1, h1]; exact .loc l
  | taskRef tid =>
    have h1 : ∀ ρ, substMany ρ (.taskRef tid) = .taskRef tid := fun ρ => by
      induction ρ with | nil => rfl | cons _ _ ih => exact ih
    rw [specializeLoopExpr, h1, h1]; exact .taskRef tid
  | syncRef k id =>
    have h1 : ∀ ρ, substMany ρ (.syncRef k id) = .syncRef k id := fun ρ => by
      induction ρ with | nil => rfl | cons _ _ ih => exact ih
    rw [specializeLoopExpr, h1, h1]; exact .syncRef k id
  | trap t =>
    have h1 : ∀ ρ, substMany ρ (.trap t) = .trap t := fun ρ => by
      induction ρ with | nil => rfl | cons _ _ ih => exact ih
    rw [specializeLoopExpr, h1, h1]; exact .trap t
  | @var x hne =>
    have hx_fvs : x ∉ fvs.map Prod.fst := hnoFv x (by simp [freeVars])
    have hbeq : (x == fParam) = false := beq_false_of_ne hne
    have hlhs : substMany (zipParams ((fParam, fnTy) :: stateParams) (cls :: stateVals)) (.var x) =
        substMany (zipParams stateParams stateVals) (.var x) := by
      simp [zipParams, substMany, subst, hbeq]
    have hrhs : substMany (zipParams (fvs ++ stateParams) (fvVals ++ stateVals)) (.var x) =
        substMany (zipParams stateParams stateVals) (.var x) := by
      rw [zipParams_append hfvLen, substMany_append]
      have hx_not_zip : x ∉ (zipParams fvs fvVals).map Prod.fst := by
        rw [zipParams_fst_eq hfvLen]; exact hx_fvs
      have hsub_id : ∀ ρ, x ∉ ρ.map Prod.fst → substMany ρ (.var x) = .var x := by
        intro ρ hnot
        induction ρ with
        | nil => rfl
        | cons q qr ihq =>
          simp only [List.map_cons, List.mem_cons, not_or] at hnot
          have hxq : (x == q.1) = false := beq_false_of_ne hnot.1
          simp [substMany, subst, hxq, ihq hnot.2]
      rw [hsub_id _ hx_not_zip]
    rw [specializeLoopExpr, hlhs, hrhs]
    exact SpecRel.refl _ _ _ _ _ _ _ _
  | @lam m ps ret body hnotF hpsAvoid =>
    have hlhs : substMany (zipParams ((fParam, fnTy) :: stateParams) (cls :: stateVals))
        (.lam m ps ret body) =
        substMany (zipParams stateParams stateVals) (.lam m ps ret body) := by
      simp only [zipParams, List.map_cons, List.zip_cons_cons, substMany]
      rw [subst_not_mem_freeVars (.lam m ps ret body) hnotF]
    have hrhs : substMany (zipParams (fvs ++ stateParams) (fvVals ++ stateVals))
        (.lam m ps ret body) =
        substMany (zipParams stateParams stateVals) (.lam m ps ret body) := by
      rw [zipParams_append hfvLen, substMany_append]
      have hid : ∀ ρ, (∀ z ∈ freeVars (.lam m ps ret body), z ∉ ρ.map Prod.fst) →
          substMany ρ (.lam m ps ret body) = .lam m ps ret body := by
        intro ρ hdisj
        induction ρ with
        | nil => rfl
        | cons q qr ihq =>
          have hnq : q.1 ∉ freeVars (.lam m ps ret body) :=
            fun hmem => hdisj q.1 hmem (List.mem_cons_self ..)
          simp only [substMany, subst_not_mem_freeVars (.lam m ps ret body) hnq]
          exact ihq (fun z hz hm => hdisj z hz (List.mem_cons_of_mem _ hm))
      rw [hid (zipParams fvs fvVals) (by rw [zipParams_fst_eq hfvLen]; exact hnoFv)]
    rw [specializeLoopExpr, hlhs, hrhs,
        substMany_lam_disjoint m ps ret body (zipParams stateParams stateVals)
          (by rw [zipParams_fst_eq hstLen]; intro z hz hm
              exact hpsAvoid z hz (List.mem_cons_of_mem _ (List.mem_append_right _ hm)))]
    exact .lam _ _ _ _
  | tuple hes =>
    rcases substMany_map_helper (zipParams ((fParam, fnTy) :: stateParams) (cls :: stateVals)) with ⟨ht1, _, _, _, _⟩
    rcases substMany_map_helper (zipParams (fvs ++ stateParams) (fvVals ++ stateVals)) with ⟨ht2, _, _, _, _⟩
    simp only [specializeLoopExpr, ht1, ht2]
    exact .tuple (specEligibleList_subst_rel loopName specName cbEntry fParam fnTy hcls hfvCl hfvLen hstLen hnodup hnoFv hes)
  | block hes =>
    rcases substMany_map_helper (zipParams ((fParam, fnTy) :: stateParams) (cls :: stateVals)) with ⟨_, hb1, _, _, _⟩
    rcases substMany_map_helper (zipParams (fvs ++ stateParams) (fvVals ++ stateVals)) with ⟨_, hb2, _, _, _⟩
    simp only [specializeLoopExpr, hb1, hb2]
    exact .block (specEligibleList_subst_rel loopName specName cbEntry fParam fnTy hcls hfvCl hfvLen hstLen hnodup hnoFv hes)
  | @cbCall cbArgs hlen hargs =>
    rcases substMany_map_helper (zipParams ((fParam, fnTy) :: stateParams) (cls :: stateVals)) with ⟨_, _, ha1, _, _⟩
    rcases substMany_map_helper (zipParams (fvs ++ stateParams) (fvVals ++ stateVals)) with ⟨_, _, _, hd2, _⟩
    have hf_lhs : substMany (zipParams ((fParam, fnTy) :: stateParams) (cls :: stateVals)) (.var fParam) = cls := by
      simp only [zipParams, List.map_cons, List.zip_cons_cons, substMany, subst, beq_self_eq_true, ↓reduceIte]
      exact substMany_closed_val_id _ hcls
    have hnoFvArgs : ∀ z ∈ freeVarsList cbArgs, z ∉ fvs.map Prod.fst :=
      fun z hz => hnoFv z (by simp [freeVars, hz])
    simp only [specializeLoopExpr, beq_self_eq_true, ↓reduceIte, ha1, hd2, hf_lhs, List.map_append]
    rw [map_substMany_zipParams_vars hnodup hfvLen hfvCl]
    exact .specCb (by simp [hlen])
      (specEligibleList_subst_rel loopName specName cbEntry fParam fnTy hcls hfvCl hfvLen hstLen hnodup hnoFvArgs hargs)
  | @applyGen fn args hnotVar hfn hargs =>
    rcases substMany_map_helper (zipParams ((fParam, fnTy) :: stateParams) (cls :: stateVals)) with ⟨_, _, ha1, _, _⟩
    rcases substMany_map_helper (zipParams (fvs ++ stateParams) (fvVals ++ stateVals)) with ⟨_, _, ha2, _, _⟩
    have hspec : specializeLoopExpr loopName specName cbEntry fParam (fvs.map Prod.fst) (.apply fn args) =
        .apply (specializeLoopExpr loopName specName cbEntry fParam (fvs.map Prod.fst) fn)
          (specializeLoopList loopName specName cbEntry fParam (fvs.map Prod.fst) args) := by
      cases fn with
      | var z =>
        have hzf : (z == fParam) = false := beq_false_of_ne (hnotVar z rfl)
        simp [specializeLoopExpr, hzf]
      | _ => simp [specializeLoopExpr]
    rw [hspec, ha1, ha2]
    exact .apply
      (specEligible_subst_rel loopName specName cbEntry fParam fnTy hcls hfvCl hfvLen hstLen hnodup
        (fun z hz => hnoFv z (by simp [freeVars, hz])) hfn)
      (specEligibleList_subst_rel loopName specName cbEntry fParam fnTy hcls hfvCl hfvLen hstLen hnodup
        (fun z hz => hnoFv z (by simp [freeVars, hz])) hargs)
  | @selfCall recArgs hlen hargs =>
    rcases substMany_map_helper (zipParams ((fParam, fnTy) :: stateParams) (cls :: stateVals)) with ⟨_, _, _, hd1, _⟩
    rcases substMany_map_helper (zipParams (fvs ++ stateParams) (fvVals ++ stateVals)) with ⟨_, _, _, hd2, _⟩
    have hf_lhs : substMany (zipParams ((fParam, fnTy) :: stateParams) (cls :: stateVals)) (.var fParam) = cls := by
      simp only [zipParams, List.map_cons, List.zip_cons_cons, substMany, subst, beq_self_eq_true, ↓reduceIte]
      exact substMany_closed_val_id _ hcls
    have hnoFvArgs : ∀ z ∈ freeVarsList recArgs, z ∉ fvs.map Prod.fst :=
      fun z hz => hnoFv z (by simp [freeVars, freeVarsList, hz])
    simp only [specializeLoopExpr, beq_self_eq_true, Bool.and_self, ↓reduceIte,
      hd1, hd2, List.map_cons, hf_lhs, List.map_append]
    rw [map_substMany_zipParams_vars hnodup hfvLen hfvCl]
    exact .specCall (by simp [hlen])
      (specEligibleList_subst_rel loopName specName cbEntry fParam fnTy hcls hfvCl hfvLen hstLen hnodup hnoFvArgs hargs)
  | @applyDirGen nm args hnotSelf hargs =>
    rcases substMany_map_helper (zipParams ((fParam, fnTy) :: stateParams) (cls :: stateVals)) with ⟨_, _, _, hd1, _⟩
    rcases substMany_map_helper (zipParams (fvs ++ stateParams) (fvVals ++ stateVals)) with ⟨_, _, _, hd2, _⟩
    have hspec : specializeLoopExpr loopName specName cbEntry fParam (fvs.map Prod.fst) (.applyDir nm args) =
        .applyDir nm (specializeLoopList loopName specName cbEntry fParam (fvs.map Prod.fst) args) := by
      cases args with
      | nil => simp [specializeLoopExpr, specializeLoopList]
      | cons a rest =>
        cases a with
        | var z =>
          have hcond : (nm == loopName && z == fParam) = false := by
            cases hc : (nm == loopName && z == fParam)
            · rfl
            · exact False.elim (hnotSelf z rest rfl hc)
          simp [specializeLoopExpr, specializeLoopList, hcond]
        | _ => simp [specializeLoopExpr, specializeLoopList]
    rw [hspec, hd1, hd2]
    exact .applyDir (specEligibleList_subst_rel loopName specName cbEntry fParam fnTy hcls hfvCl hfvLen hstLen hnodup hnoFv hargs)
  | @bin op _ _ ha hb =>
    have hbin : ∀ ρ x y, substMany ρ (.bin op x y) = .bin op (substMany ρ x) (substMany ρ y) := fun ρ x y => by
      induction ρ generalizing x y with | nil => rfl | cons _ _ ih => exact ih _ _
    simp only [specializeLoopExpr, hbin]
    exact .bin
      (specEligible_subst_rel loopName specName cbEntry fParam fnTy hcls hfvCl hfvLen hstLen hnodup
        (fun z hz => hnoFv z (by simp [freeVars, hz])) ha)
      (specEligible_subst_rel loopName specName cbEntry fParam fnTy hcls hfvCl hfvLen hstLen hnodup
        (fun z hz => hnoFv z (by simp [freeVars, hz])) hb)
  | @un op _ he =>
    have hun : ∀ ρ x, substMany ρ (.un op x) = .un op (substMany ρ x) := fun ρ x => by
      induction ρ generalizing x with | nil => rfl | cons _ _ ih => exact ih _
    simp only [specializeLoopExpr, hun]
    exact .un (specEligible_subst_rel loopName specName cbEntry fParam fnTy hcls hfvCl hfvLen hstLen hnodup hnoFv he)
  | @let_ y e1 e2 hyAvoid he1 he2 =>
    have hy1 : y ∉ (zipParams ((fParam, fnTy) :: stateParams) (cls :: stateVals)).map Prod.fst := by
      rw [zipParams_fst_eq (by simp [hstLen])]
      intro hm; apply hyAvoid
      simp only [List.map_cons, List.mem_cons] at hm
      rcases hm with rfl | hst
      · exact List.mem_cons_self ..
      · exact List.mem_cons_of_mem _ (List.mem_append_right _ hst)
    have hy2 : y ∉ (zipParams (fvs ++ stateParams) (fvVals ++ stateVals)).map Prod.fst := by
      rw [zipParams_fst_eq (by simp [hfvLen, hstLen]), List.map_append]
      exact fun hm => hyAvoid (List.mem_cons_of_mem _ hm)
    have hnoFv2 : ∀ z ∈ freeVars e2, z ∉ fvs.map Prod.fst := by
      intro z hz hmem
      by_cases hzy : z = y
      · subst hzy; exact hyAvoid (List.mem_cons_of_mem _ (List.mem_append_left _ hmem))
      · exact hnoFv z (by simp [freeVars, hz, hzy]) hmem
    simp only [specializeLoopExpr, substMany_let_not_mem _ hy1, substMany_let_not_mem _ hy2]
    exact .let_
      (specEligible_subst_rel loopName specName cbEntry fParam fnTy hcls hfvCl hfvLen hstLen hnodup
        (fun z hz => hnoFv z (by simp [freeVars, hz])) he1)
      (specEligible_subst_rel loopName specName cbEntry fParam fnTy hcls hfvCl hfvLen hstLen hnodup hnoFv2 he2)
  | if_ hc ht he =>
    have hif : ∀ ρ c t e, substMany ρ (.if_ c t e) = .if_ (substMany ρ c) (substMany ρ t) (substMany ρ e) :=
      fun ρ c t e => by induction ρ generalizing c t e with | nil => rfl | cons _ _ ih => exact ih _ _ _
    simp only [specializeLoopExpr, hif]
    exact .if_
      (specEligible_subst_rel loopName specName cbEntry fParam fnTy hcls hfvCl hfvLen hstLen hnodup
        (fun z hz => hnoFv z (by simp [freeVars, hz])) hc)
      (specEligible_subst_rel loopName specName cbEntry fParam fnTy hcls hfvCl hfvLen hstLen hnodup
        (fun z hz => hnoFv z (by simp [freeVars, hz])) ht)
      (specEligible_subst_rel loopName specName cbEntry fParam fnTy hcls hfvCl hfvLen hstLen hnodup
        (fun z hz => hnoFv z (by simp [freeVars, hz])) he)
  | while_ hc hb =>
    have hwh : ∀ ρ c b, substMany ρ (.while_ c b) = .while_ (substMany ρ c) (substMany ρ b) :=
      fun ρ c b => by induction ρ generalizing c b with | nil => rfl | cons _ _ ih => exact ih _ _
    simp only [specializeLoopExpr, hwh]
    exact .while_
      (specEligible_subst_rel loopName specName cbEntry fParam fnTy hcls hfvCl hfvLen hstLen hnodup
        (fun z hz => hnoFv z (by simp [freeVars, hz])) hc)
      (specEligible_subst_rel loopName specName cbEntry fParam fnTy hcls hfvCl hfvLen hstLen hnodup
        (fun z hz => hnoFv z (by simp [freeVars, hz])) hb)
  | @match_ s arms hs harms =>
    have hdisj : ∀ a ∈ arms, ∀ z ∈ patBoundNames a.1, z ∉ fParam :: (fvs.map Prod.fst ++ stateParams.map Prod.fst) := by
      clear hs hnoFv
      induction arms with
      | nil => intro _ h; cases h
      | cons a0 ar ih =>
        cases harms with
        | cons hp _ hrs =>
          intro a ha
          rcases List.mem_cons.mp ha with rfl | har
          · exact hp
          · exact ih hrs a har
    have hdisj1 : ∀ a ∈ arms, ∀ z ∈ patBoundNames a.1,
        z ∉ (zipParams ((fParam, fnTy) :: stateParams) (cls :: stateVals)).map Prod.fst := by
      rw [zipParams_fst_eq (by simp [hstLen])]
      intro a ha z hz hm
      apply hdisj a ha z hz
      simp only [List.map_cons, List.mem_cons] at hm
      rcases hm with rfl | hst
      · exact List.mem_cons_self ..
      · exact List.mem_cons_of_mem _ (List.mem_append_right _ hst)
    have hdisj2 : ∀ a ∈ specializeLoopArms loopName specName cbEntry fParam (fvs.map Prod.fst) arms,
        ∀ z ∈ patBoundNames a.1,
        z ∉ (zipParams (fvs ++ stateParams) (fvVals ++ stateVals)).map Prod.fst := by
      rw [zipParams_fst_eq (by simp [hfvLen, hstLen]), List.map_append]
      have hfst : ∀ as, (specializeLoopArms loopName specName cbEntry fParam (fvs.map Prod.fst) as).map Prod.fst =
          as.map Prod.fst := by
        intro as
        induction as with
        | nil => simp [specializeLoopArms]
        | cons a0 ar iha => rcases a0 with ⟨p0, b0⟩; simp [specializeLoopArms, iha]
      intro a ha z hz hm
      have ha1 : a.1 ∈ arms.map Prod.fst := by
        rw [← hfst]; exact List.mem_map.mpr ⟨a, ha, rfl⟩
      rcases List.mem_map.mp ha1 with ⟨orig, horig, heq1⟩
      rw [← heq1] at hz
      exact hdisj orig horig z hz (List.mem_cons_of_mem _ hm)
    simp only [specializeLoopExpr, substMany_match_disjoint _ _ _ hdisj1,
      substMany_match_disjoint _ _ _ hdisj2]
    exact .match_
      (specEligible_subst_rel loopName specName cbEntry fParam fnTy hcls hfvCl hfvLen hstLen hnodup
        (fun z hz => hnoFv z (by simp [freeVars, hz])) hs)
      (specEligibleArms_subst_rel loopName specName cbEntry fParam fnTy hcls hfvCl hfvLen hstLen hnodup
        (fun z hz => hnoFv z (by simp [freeVars, hz])) harms)
  | makeData hes =>
    rcases substMany_map_helper (zipParams ((fParam, fnTy) :: stateParams) (cls :: stateVals)) with ⟨_, _, _, _, hm1⟩
    rcases substMany_map_helper (zipParams (fvs ++ stateParams) (fvVals ++ stateVals)) with ⟨_, _, _, _, hm2⟩
    simp only [specializeLoopExpr, hm1, hm2]
    exact .makeData (specEligibleList_subst_rel loopName specName cbEntry fParam fnTy hcls hfvCl hfvLen hstLen hnodup hnoFv hes)
  | getTag he =>
    have hgt : ∀ ρ x, substMany ρ (.getTag x) = .getTag (substMany ρ x) := fun ρ x => by
      induction ρ generalizing x with | nil => rfl | cons _ _ ih => exact ih _
    simp only [specializeLoopExpr, hgt]
    exact .getTag (specEligible_subst_rel loopName specName cbEntry fParam fnTy hcls hfvCl hfvLen hstLen hnodup hnoFv he)
  | cellNew he =>
    have hcn : ∀ ρ x, substMany ρ (.cellNew x) = .cellNew (substMany ρ x) := fun ρ x => by
      induction ρ generalizing x with | nil => rfl | cons _ _ ih => exact ih _
    simp only [specializeLoopExpr, hcn]
    exact .cellNew (specEligible_subst_rel loopName specName cbEntry fParam fnTy hcls hfvCl hfvLen hstLen hnodup hnoFv he)
  | cellGet he =>
    have hcg : ∀ ρ x, substMany ρ (.cellGet x) = .cellGet (substMany ρ x) := fun ρ x => by
      induction ρ generalizing x with | nil => rfl | cons _ _ ih => exact ih _
    simp only [specializeLoopExpr, hcg]
    exact .cellGet (specEligible_subst_rel loopName specName cbEntry fParam fnTy hcls hfvCl hfvLen hstLen hnodup hnoFv he)
  | cellSet ha hb =>
    have hcs : ∀ ρ x y, substMany ρ (.cellSet x y) = .cellSet (substMany ρ x) (substMany ρ y) := fun ρ x y => by
      induction ρ generalizing x y with | nil => rfl | cons _ _ ih => exact ih _ _
    simp only [specializeLoopExpr, hcs]
    exact .cellSet
      (specEligible_subst_rel loopName specName cbEntry fParam fnTy hcls hfvCl hfvLen hstLen hnodup
        (fun z hz => hnoFv z (by simp [freeVars, hz])) ha)
      (specEligible_subst_rel loopName specName cbEntry fParam fnTy hcls hfvCl hfvLen hstLen hnodup
        (fun z hz => hnoFv z (by simp [freeVars, hz])) hb)
termination_by sizeOf e

theorem specEligibleList_subst_rel
    (loopName specName cbEntry fParam : Ident) (fnTy : Ty)
    {fvs stateParams : List (Ident × Ty)}
    {cls : Expr} {fvVals stateVals : List Expr}
    {cbArity stateArity : Nat}
    (hcls : freeVars cls = [])
    (hfvCl : ∀ v ∈ fvVals, freeVars v = [])
    (hfvLen : fvVals.length = fvs.length)
    (hstLen : stateVals.length = stateParams.length)
    (hnodup : (fvs.map Prod.fst ++ stateParams.map Prod.fst).Nodup)
    {es : List Expr}
    (hnoFv : ∀ z ∈ freeVarsList es, z ∉ fvs.map Prod.fst)
    (helig : SpecEligibleList loopName fParam (fParam :: (fvs.map Prod.fst ++ stateParams.map Prod.fst))
      cbArity stateArity es) :
    SpecRelList loopName specName cbEntry cls fvVals cbArity stateArity
      (es.map (substMany (zipParams ((fParam, fnTy) :: stateParams) (cls :: stateVals))))
      ((specializeLoopList loopName specName cbEntry fParam (fvs.map Prod.fst) es).map
        (substMany (zipParams (fvs ++ stateParams) (fvVals ++ stateVals)))) := by
  cases helig with
  | nil => simp only [specializeLoopList, List.map_nil]; exact .nil
  | cons he hes =>
    simp only [specializeLoopList, List.map_cons]
    exact .cons
      (specEligible_subst_rel loopName specName cbEntry fParam fnTy hcls hfvCl hfvLen hstLen hnodup
        (fun z hz => hnoFv z (by simp [freeVarsList, hz])) he)
      (specEligibleList_subst_rel loopName specName cbEntry fParam fnTy hcls hfvCl hfvLen hstLen hnodup
        (fun z hz => hnoFv z (by simp [freeVarsList, hz])) hes)
termination_by sizeOf es

theorem specEligibleArms_subst_rel
    (loopName specName cbEntry fParam : Ident) (fnTy : Ty)
    {fvs stateParams : List (Ident × Ty)}
    {cls : Expr} {fvVals stateVals : List Expr}
    {cbArity stateArity : Nat}
    (hcls : freeVars cls = [])
    (hfvCl : ∀ v ∈ fvVals, freeVars v = [])
    (hfvLen : fvVals.length = fvs.length)
    (hstLen : stateVals.length = stateParams.length)
    (hnodup : (fvs.map Prod.fst ++ stateParams.map Prod.fst).Nodup)
    {arms : List (Pat × Expr)}
    (hnoFv : ∀ z ∈ freeVarsArms arms, z ∉ fvs.map Prod.fst)
    (helig : SpecEligibleArms loopName fParam (fParam :: (fvs.map Prod.fst ++ stateParams.map Prod.fst))
      cbArity stateArity arms) :
    SpecRelArms loopName specName cbEntry cls fvVals cbArity stateArity
      (arms.map fun a => (a.1, substMany (zipParams ((fParam, fnTy) :: stateParams) (cls :: stateVals)) a.2))
      ((specializeLoopArms loopName specName cbEntry fParam (fvs.map Prod.fst) arms).map
        fun a => (a.1, substMany (zipParams (fvs ++ stateParams) (fvVals ++ stateVals)) a.2)) := by
  cases helig with
  | nil => simp only [specializeLoopArms, List.map_nil]; exact .nil
  | @cons p body rest hpAvoid hb hrs =>
    simp only [specializeLoopArms, List.map_cons]
    have hnoFvBody : ∀ z ∈ freeVars body, z ∉ fvs.map Prod.fst := by
      intro z hz hmem
      by_cases hzp : z ∈ patBoundNames p
      · exact hpAvoid z hzp (List.mem_cons_of_mem _ (List.mem_append_left _ hmem))
      · exact hnoFv z (by simp [freeVarsArms, hz, hzp]) hmem
    exact .cons
      (specEligible_subst_rel loopName specName cbEntry fParam fnTy hcls hfvCl hfvLen hstLen hnodup hnoFvBody hb)
      (specEligibleArms_subst_rel loopName specName cbEntry fParam fnTy hcls hfvCl hfvLen hstLen hnodup
        (fun z hz => hnoFv z (by simp [freeVarsArms, hz])) hrs)
termination_by sizeOf arms
end

/-- Bundled configuration of a valid `SpecConstr` higher-order loop specialization in `Φ`. -/
structure ValidLoopSpec (Δ : AdtEnv) (Φ : FunEnv) where
  loopName    : Ident
  specName    : Ident
  cbEntry     : Ident
  fParam      : Ident
  fnTy        : Ty
  loopRet     : Ty
  loopBody    : Expr
  cbMode      : Mode
  cbParams    : List (Ident × Ty)
  cbRet       : Ty
  cbBody      : Expr
  fvs         : List (Ident × Ty)
  fvVals      : List Expr
  stateParams : List (Ident × Ty)
  hΦcl        : ClosedFunEnv Φ
  hLoop       : Φ loopName = some { name := loopName, params := (fParam, fnTy) :: stateParams,
                                    retTy := loopRet, body := loopBody }
  hSpec       : Φ specName = some { name := specName, params := fvs ++ stateParams,
                                    retTy := loopRet,
                                    body := specializeLoopExpr loopName specName cbEntry
                                              fParam (fvs.map Prod.fst) loopBody }
  hCb         : Φ cbEntry = some { name := cbEntry, params := cbParams ++ fvs,
                                   retTy := cbRet, body := cbBody }
  hfvVal      : ∀ v ∈ fvVals, IsValue v
  hfvCl       : ∀ v ∈ fvVals, freeVars v = []
  hfvLen      : fvVals.length = fvs.length
  hcbDisj     : ∀ x ∈ cbParams.map Prod.fst, x ∉ fvs.map Prod.fst
  hfParamNot  : fParam ∉ fvs.map Prod.fst ++ stateParams.map Prod.fst
  hSpecNodup  : (fvs.map Prod.fst ++ stateParams.map Prod.fst).Nodup
  hLoopNoFv   : ∀ z ∈ freeVars loopBody, z ∉ fvs.map Prod.fst
  hEligible   : SpecEligible loopName fParam
                  (fParam :: (fvs.map Prod.fst ++ stateParams.map Prod.fst))
                  cbParams.length stateParams.length loopBody

/-- Known call-site closure value specialized by `ValidLoopSpec`. -/
def ValidLoopSpec.cls {Δ : AdtEnv} {Φ : FunEnv} (S : ValidLoopSpec Δ Φ) : Expr :=
  substMany (zipParams S.fvs S.fvVals) (.lam S.cbMode S.cbParams S.cbRet S.cbBody)

theorem ValidLoopSpec.cls_eq_lam {Δ : AdtEnv} {Φ : FunEnv} (S : ValidLoopSpec Δ Φ) :
    S.cls = .lam S.cbMode S.cbParams S.cbRet (substMany (zipParams S.fvs S.fvVals) S.cbBody) := by
  unfold ValidLoopSpec.cls
  apply substMany_lam_disjoint
  rw [zipParams_fst_eq S.hfvLen]
  exact S.hcbDisj

theorem ValidLoopSpec.cls_isValue {Δ : AdtEnv} {Φ : FunEnv} (S : ValidLoopSpec Δ Φ) :
    IsValue S.cls := by
  rw [S.cls_eq_lam]; exact .lam _ _ _ _

theorem ValidLoopSpec.cls_closed {Δ : AdtEnv} {Φ : FunEnv} (S : ValidLoopSpec Δ Φ) :
    freeVars S.cls = [] := by
  rw [S.cls_eq_lam]
  apply List.eq_nil_iff_forall_not_mem.mpr
  intro z hz
  simp only [freeVars, List.mem_filter, Bool.not_eq_true'] at hz
  rcases substMany_freeVars_subset (zipParams S.fvs S.fvVals) (zipParams_closed S.hfvCl) S.cbBody z hz.1 with ⟨hnot, hzb⟩
  rw [zipParams_fst_eq S.hfvLen] at hnot
  have hcb_in := S.hΦcl S.cbEntry _ S.hCb z hzb
  simp only [List.map_append, List.mem_append] at hcb_in
  rcases hcb_in with hcp | hfv
  · rcases List.mem_map.mp hcp with ⟨p, hp, rfl⟩
    have hany : S.cbParams.any (fun q => q.1 == p.1) = true :=
      List.any_eq_true.mpr ⟨p, hp, beq_self_eq_true _⟩
    rw [hany] at hz; cases hz.2
  · exact hnot hfv

/- 1-to-1 Forward Lockstep Simulation (`specRel_step_forward`). -/
mutual
theorem specRel_step_forward {Δ : AdtEnv} {Φ : FunEnv} (S : ValidLoopSpec Δ Φ)
    {e1 e2 e1' : Expr} {σ σ' : Store}
    (hσ : ClosedStore σ) (he1 : freeVars e1 = [])
    (hr : SpecRel S.loopName S.specName S.cbEntry S.cls S.fvVals S.cbParams.length S.stateParams.length e1 e2)
    (hs : Step Δ Φ emptyPool e1 σ e1' σ' .none) :
    ∃ e2', SpecRel S.loopName S.specName S.cbEntry S.cls S.fvVals S.cbParams.length S.stateParams.length e1' e2' ∧
           Step Δ Φ emptyPool e2 σ e2' σ' .none := by
  cases hr with
  | lit _ | var _ | loc _ | taskRef _ | syncRef _ _ | lam _ _ _ _ | trap _ =>
    cases hs
  | tuple hrl =>
    simp only [freeVars] at he1
    cases hs with
    | tupleStep hsl =>
      rcases specRelList_step_forward S hσ he1 hrl hsl with ⟨es2', hrl', hsl2⟩
      exact ⟨.tuple es2', .tuple hrl', .tupleStep hsl2⟩
    | tupleTrap htr =>
      exact ⟨.trap _, .trap _, .tupleTrap ((specRelList_firstTrap_iff hrl).mp htr)⟩
  | block hrl =>
    cases hrl with
    | nil => cases hs; exact ⟨.lit .unit, .lit .unit, .blockEmpty⟩
    | cons hr1 hrs =>
      cases hrs with
      | nil => cases hs; exact ⟨_, hr1, .blockSingle⟩
      | cons hr2 hrs' =>
        simp only [freeVars, freeVarsList, List.append_eq_nil_iff] at he1
        cases hs with
        | blockConsStep hs1 =>
          rcases specRel_step_forward S hσ he1.1 hr1 hs1 with ⟨e2', hr1', hs2⟩
          exact ⟨.block (e2' :: _), .block (.cons hr1' (.cons hr2 hrs')), .blockConsStep hs2⟩
        | blockConsVal hv1 =>
          rcases specRel_val_left hr1 hv1 with ⟨rfl, hv2⟩
          exact ⟨.block _, .block (.cons hr2 hrs'), .blockConsVal hv2⟩
        | blockConsTrap =>
          rw [specRel_trap_left hr1]
          exact ⟨.trap _, .trap _, .blockConsTrap⟩
  | @specCb args1 args2 hlen hrl =>
    simp only [freeVars, List.append_eq_nil_iff] at he1
    generalize hcls_eq : S.cls = c at hs
    cases hs with
    | applyFn hs_fn =>
      rw [← hcls_eq] at hs_fn
      exact False.elim (isValue_no_step S.cls_isValue hs_fn)
    | applyFnTrap => exact False.elim (isValue_ne_trap S.cls_isValue _ hcls_eq)
    | applyArgs _ hsl =>
      rw [← hcls_eq]
      rcases specRelList_step_forward S hσ he1.2 hrl hsl with ⟨args2', hrl', hsl2⟩
      exact ⟨.applyDir S.cbEntry (args2' ++ S.fvVals),
        .specCb (by rw [stepList_length_eq hsl, hlen]) hrl',
        .applyDirArgs (stepList_append_vals_forward hsl2)⟩
    | applyArgsTrap _ htr =>
      have htr2 := (listFirstTrap_append_vals_iff S.hfvVal).mpr ((specRelList_firstTrap_iff hrl).mp htr)
      exact ⟨.trap _, .trap _, .applyDirTrap htr2⟩
    | applyBeta hvs1 _ =>
      rcases specRelList_val_left hrl hvs1 with ⟨rfl, _⟩
      have hargsCl : ∀ v ∈ args1, freeVars v = [] := freeVarsList_eq_nil_iff.mp he1.2
      have hallVal' : ∀ v ∈ args1 ++ S.fvVals, IsValue v := by
        intro v hv; rcases List.mem_append.mp hv with h1 | h2
        · exact hvs1 v h1
        · exact S.hfvVal v h2
      have hallLen : (args1 ++ S.fvVals).length = (S.cbParams ++ S.fvs).length := by
        simp [hlen, S.hfvLen]
      have hlam_eq := S.cls_eq_lam.symm.trans hcls_eq
      injection hlam_eq with _ hps _ hbody
      subst hps hbody
      rw [substMany_lam_apply_eq_flat S.cbParams S.fvs args1 S.fvVals S.cbBody
            hlen S.hfvLen hargsCl S.hfvCl S.hcbDisj]
      exact ⟨_, SpecRel.refl _ _ _ _ _ _ _ _, .applyDirBeta S.hCb hallVal' hallLen⟩
  | apply hfn hrl =>
    simp only [freeVars, List.append_eq_nil_iff] at he1
    cases hs with
    | applyFn hs1 =>
      rcases specRel_step_forward S hσ he1.1 hfn hs1 with ⟨fn2', hfn', hs2⟩
      exact ⟨.apply fn2' _, .apply hfn' hrl, .applyFn hs2⟩
    | applyFnTrap =>
      rw [specRel_trap_left hfn]
      exact ⟨.trap _, .trap _, .applyFnTrap⟩
    | applyArgs hv1 hsl =>
      rcases specRel_val_left hfn hv1 with ⟨rfl, hv2⟩
      rcases specRelList_step_forward S hσ he1.2 hrl hsl with ⟨args2', hrl', hsl2⟩
      exact ⟨.apply _ args2', .apply hfn hrl', .applyArgs hv2 hsl2⟩
    | applyArgsTrap hv1 htr =>
      rcases specRel_val_left hfn hv1 with ⟨rfl, hv2⟩
      exact ⟨.trap _, .trap _, .applyArgsTrap hv2 ((specRelList_firstTrap_iff hrl).mp htr)⟩
    | applyBeta hvs1 hlen =>
      rcases specRel_val_left hfn (.lam _ _ _ _) with ⟨heq_fn, _⟩
      rcases specRelList_val_left hrl hvs1 with ⟨rfl, hvs2⟩
      rw [← heq_fn]
      exact ⟨_, SpecRel.refl _ _ _ _ _ _ _ _, .applyBeta hvs2 hlen⟩
  | @specCall args1 args2 hlen hrl =>
    simp only [freeVars, freeVarsList, List.append_eq_nil_iff] at he1
    cases hs with
    | applyDirArgs hsl =>
      cases hsl with
      | head hs_cls => exact False.elim (isValue_no_step S.cls_isValue hs_cls)
      | tail _ hsl_args =>
        rcases specRelList_step_forward S hσ he1.2 hrl hsl_args with ⟨args2', hrl', hsl2⟩
        exact ⟨.applyDir S.specName (S.fvVals ++ args2'),
          .specCall (by rw [stepList_length_eq hsl_args, hlen]) hrl',
          .applyDirArgs (stepList_prepend_vals_forward S.hfvVal hsl2)⟩
    | applyDirTrap htr =>
      generalize hcls_eq : S.cls = c at htr
      cases htr with
      | head _ _ => exact False.elim (isValue_ne_trap S.cls_isValue _ hcls_eq)
      | tail _ htr_args =>
        have htr2 := (listFirstTrap_prepend_vals_iff S.hfvVal).mpr ((specRelList_firstTrap_iff hrl).mp htr_args)
        exact ⟨.trap _, .trap _, .applyDirTrap htr2⟩
    | applyDirBeta hfn hall _ =>
      have hvs1 : ∀ v ∈ args1, IsValue v := fun v hv => hall v (List.mem_cons_of_mem _ hv)
      rcases specRelList_val_left hrl hvs1 with ⟨rfl, _⟩
      rw [S.hLoop] at hfn; injection hfn with hfd; subst hfd
      have hallVal2 : ∀ v ∈ S.fvVals ++ args1, IsValue v := by
        intro v hv; rcases List.mem_append.mp hv with h1 | h2
        · exact S.hfvVal v h1
        · exact hvs1 v h2
      have hallLen2 : (S.fvVals ++ args1).length = (S.fvs ++ S.stateParams).length := by
        simp [S.hfvLen, hlen]
      refine ⟨_, ?_, .applyDirBeta S.hSpec hallVal2 hallLen2⟩
      exact specEligible_subst_rel S.loopName S.specName S.cbEntry S.fParam S.fnTy
        S.cls_closed S.hfvCl S.hfvLen hlen S.hSpecNodup S.hLoopNoFv S.hEligible
  | applyDir hrl =>
    simp only [freeVars] at he1
    cases hs with
    | applyDirArgs hsl =>
      rcases specRelList_step_forward S hσ he1 hrl hsl with ⟨args2', hrl', hsl2⟩
      exact ⟨.applyDir _ args2', .applyDir hrl', .applyDirArgs hsl2⟩
    | applyDirTrap htr =>
      exact ⟨.trap _, .trap _, .applyDirTrap ((specRelList_firstTrap_iff hrl).mp htr)⟩
    | applyDirBeta hfn hvs1 hlen =>
      rcases specRelList_val_left hrl hvs1 with ⟨rfl, hvs2⟩
      exact ⟨_, SpecRel.refl _ _ _ _ _ _ _ _, .applyDirBeta hfn hvs2 hlen⟩
  | bin ha hb =>
    simp only [freeVars, List.append_eq_nil_iff] at he1
    cases hs with
    | binLeft hs1 =>
      rcases specRel_step_forward S hσ he1.1 ha hs1 with ⟨a2', ha', hs2⟩
      exact ⟨.bin _ a2' _, .bin ha' hb, .binLeft hs2⟩
    | binLeftTrap =>
      rw [specRel_trap_left ha]; exact ⟨.trap _, .trap _, .binLeftTrap⟩
    | binAndFalse =>
      rcases specRel_val_left ha (.lit _) with ⟨heq, _⟩; rw [← heq]
      exact ⟨.lit (.bool false), .lit _, .binAndFalse⟩
    | binAndTrue =>
      rcases specRel_val_left ha (.lit _) with ⟨heq, _⟩; rw [← heq]
      exact ⟨_, hb, .binAndTrue⟩
    | binOrTrue =>
      rcases specRel_val_left ha (.lit _) with ⟨heq, _⟩; rw [← heq]
      exact ⟨.lit (.bool true), .lit _, .binOrTrue⟩
    | binOrFalse =>
      rcases specRel_val_left ha (.lit _) with ⟨heq, _⟩; rw [← heq]
      exact ⟨_, hb, .binOrFalse⟩
    | binRight hna hno hv1 hs1 =>
      rcases specRel_val_left ha hv1 with ⟨rfl, hv2⟩
      rcases specRel_step_forward S hσ he1.2 hb hs1 with ⟨b2', hb', hs2⟩
      exact ⟨.bin _ _ b2', .bin ha hb', .binRight hna hno hv2 hs2⟩
    | binRightTrap hna hno hv1 =>
      rcases specRel_val_left ha hv1 with ⟨rfl, hv2⟩
      rw [specRel_trap_left hb]
      exact ⟨.trap _, .trap _, .binRightTrap hna hno hv2⟩
    | binVal hev =>
      rcases specRel_val_left ha (.lit _) with ⟨heq1, _⟩
      rcases specRel_val_left hb (.lit _) with ⟨heq2, _⟩
      rw [← heq1, ← heq2]
      exact ⟨.lit _, .lit _, .binVal hev⟩
    | binTrap hev =>
      rcases specRel_val_left ha (.lit _) with ⟨heq1, _⟩
      rcases specRel_val_left hb (.lit _) with ⟨heq2, _⟩
      rw [← heq1, ← heq2]
      exact ⟨.trap _, .trap _, .binTrap hev⟩
  | un he =>
    simp only [freeVars] at he1
    cases hs with
    | unStep hs1 =>
      rcases specRel_step_forward S hσ he1 he hs1 with ⟨e2', he', hs2⟩
      exact ⟨.un _ e2', .un he', .unStep hs2⟩
    | unTrap => rw [specRel_trap_left he]; exact ⟨.trap _, .trap _, .unTrap⟩
    | unVal hev =>
      rcases specRel_val_left he (.lit _) with ⟨heq, _⟩; rw [← heq]
      exact ⟨.lit _, .lit _, .unVal hev⟩
  | let_ ha hb =>
    simp only [freeVars, List.append_eq_nil_iff] at he1
    cases hs with
    | letStep hs1 =>
      rcases specRel_step_forward S hσ he1.1 ha hs1 with ⟨a2', ha', hs2⟩
      exact ⟨.let_ _ a2' _, .let_ ha' hb, .letStep hs2⟩
    | letTrap =>
      rw [specRel_trap_left ha]; exact ⟨.trap _, .trap _, .letTrap⟩
    | letVal hv1 =>
      rcases specRel_val_left ha hv1 with ⟨rfl, hv2⟩
      exact ⟨_, specRel_subst S.cls_closed S.hfvCl _ he1.1 hb, .letVal hv2⟩
  | if_ hc ht he =>
    simp only [freeVars, List.append_eq_nil_iff] at he1
    cases hs with
    | ifStep hs1 =>
      rcases specRel_step_forward S hσ he1.1.1 hc hs1 with ⟨c2', hc', hs2⟩
      exact ⟨.if_ c2' _ _, .if_ hc' ht he, .ifStep hs2⟩
    | ifTrap => rw [specRel_trap_left hc]; exact ⟨.trap _, .trap _, .ifTrap⟩
    | ifTrue =>
      rcases specRel_val_left hc (.lit _) with ⟨heq, _⟩; rw [← heq]
      exact ⟨_, ht, .ifTrue⟩
    | ifFalse =>
      rcases specRel_val_left hc (.lit _) with ⟨heq, _⟩; rw [← heq]
      exact ⟨_, he, .ifFalse⟩
  | while_ hc hb =>
    cases hs with
    | whileUnfold =>
      exact ⟨_, .if_ hc (.block (.cons hb (.cons (.while_ hc hb) .nil))) (.lit .unit), .whileUnfold⟩
  | match_ hs_r harms =>
    simp only [freeVars, List.append_eq_nil_iff] at he1
    cases hs with
    | matchScrut hs1 =>
      rcases specRel_step_forward S hσ he1.1 hs_r hs1 with ⟨s2', hs_r', hs2⟩
      exact ⟨.match_ s2' _, .match_ hs_r' harms, .matchScrut hs2⟩
    | matchScrutTrap =>
      rw [specRel_trap_left hs_r]; exact ⟨.trap _, .trap _, .matchScrutTrap⟩
    | matchEmpty hv1 =>
      cases harms with
      | nil =>
        rcases specRel_val_left hs_r hv1 with ⟨rfl, hv2⟩
        exact ⟨.trap .matchFailure, .trap _, .matchEmpty hv2⟩
    | matchHit hv1 hm =>
      cases harms with
      | cons hb _ =>
        rcases specRel_val_left hs_r hv1 with ⟨rfl, hv2⟩
        rcases matchPat_closed he1.1 hm with ⟨henv, _⟩
        exact ⟨_, specRel_substMany S.cls_closed S.hfvCl henv hb, .matchHit hv2 hm⟩
    | matchMiss hv1 hm =>
      cases harms with
      | cons _ hrs =>
        rcases specRel_val_left hs_r hv1 with ⟨rfl, hv2⟩
        exact ⟨_, .match_ hs_r hrs, .matchMiss hv2 hm⟩
  | makeData hrl =>
    simp only [freeVars] at he1
    cases hs with
    | makeDataStep hsl =>
      rcases specRelList_step_forward S hσ he1 hrl hsl with ⟨es2', hrl', hsl2⟩
      exact ⟨.makeData _ _ es2', .makeData hrl', .makeDataStep hsl2⟩
    | makeDataTrap htr =>
      exact ⟨.trap _, .trap _, .makeDataTrap ((specRelList_firstTrap_iff hrl).mp htr)⟩
  | getTag he =>
    simp only [freeVars] at he1
    cases hs with
    | getTagStep hs1 =>
      rcases specRel_step_forward S hσ he1 he hs1 with ⟨e2', he', hs2⟩
      exact ⟨.getTag e2', .getTag he', .getTagStep hs2⟩
    | getTagTrap => rw [specRel_trap_left he]; exact ⟨.trap _, .trap _, .getTagTrap⟩
    | getTagVal hvs1 =>
      rcases specRel_val_left he (.makeData _ _ hvs1) with ⟨heq, _⟩; rw [← heq]
      exact ⟨.lit _, .lit _, .getTagVal hvs1⟩
  | cellNew he =>
    simp only [freeVars] at he1
    cases hs with
    | cellNewStep hs1 =>
      rcases specRel_step_forward S hσ he1 he hs1 with ⟨e2', he', hs2⟩
      exact ⟨.cellNew e2', .cellNew he', .cellNewStep hs2⟩
    | cellNewTrap => rw [specRel_trap_left he]; exact ⟨.trap _, .trap _, .cellNewTrap⟩
    | cellNewVal hv1 =>
      rcases specRel_val_left he hv1 with ⟨rfl, hv2⟩
      exact ⟨.loc _, .loc _, .cellNewVal hv2⟩
  | cellGet he =>
    simp only [freeVars] at he1
    cases hs with
    | cellGetStep hs1 =>
      rcases specRel_step_forward S hσ he1 he hs1 with ⟨e2', he', hs2⟩
      exact ⟨.cellGet e2', .cellGet he', .cellGetStep hs2⟩
    | cellGetTrap => rw [specRel_trap_left he]; exact ⟨.trap _, .trap _, .cellGetTrap⟩
    | cellGetVal hl =>
      rcases specRel_val_left he (.loc _) with ⟨heq, _⟩; rw [← heq]
      exact ⟨_, SpecRel.refl _ _ _ _ _ _ _ _, .cellGetVal hl⟩
  | cellSet ha hb =>
    simp only [freeVars, List.append_eq_nil_iff] at he1
    cases hs with
    | cellSetLeft hs1 =>
      rcases specRel_step_forward S hσ he1.1 ha hs1 with ⟨a2', ha', hs2⟩
      exact ⟨.cellSet a2' _, .cellSet ha' hb, .cellSetLeft hs2⟩
    | cellSetLeftTrap => rw [specRel_trap_left ha]; exact ⟨.trap _, .trap _, .cellSetLeftTrap⟩
    | cellSetRight hv1 hs1 =>
      rcases specRel_val_left ha hv1 with ⟨rfl, hv2⟩
      rcases specRel_step_forward S hσ he1.2 hb hs1 with ⟨b2', hb', hs2⟩
      exact ⟨.cellSet _ b2', .cellSet ha hb', .cellSetRight hv2 hs2⟩
    | cellSetRightTrap hv1 =>
      rcases specRel_val_left ha hv1 with ⟨rfl, hv2⟩
      rw [specRel_trap_left hb]
      exact ⟨.trap _, .trap _, .cellSetRightTrap hv2⟩
    | cellSetVal hlt hv1 =>
      rcases specRel_val_left ha (.loc _) with ⟨heq, _⟩; rw [← heq]
      rcases specRel_val_left hb hv1 with ⟨rfl, hv2⟩
      exact ⟨.lit .unit, .lit .unit, .cellSetVal hlt hv2⟩
  | spawn he =>
    simp only [freeVars] at he1
    cases hs with
    | spawnStep hs1 =>
      rcases specRel_step_forward S hσ he1 he hs1 with ⟨e2', he', hs2⟩
      exact ⟨.spawn e2', .spawn he', .spawnStep hs2⟩
    | spawnTrap => rw [specRel_trap_left he]; exact ⟨.trap _, .trap _, .spawnTrap⟩
  | await he =>
    simp only [freeVars] at he1
    cases hs with
    | awaitStep hs1 =>
      rcases specRel_step_forward S hσ he1 he hs1 with ⟨e2', he', hs2⟩
      exact ⟨.await e2', .await he', .awaitStep hs2⟩
    | awaitTrap => rw [specRel_trap_left he]; exact ⟨.trap _, .trap _, .awaitTrap⟩
    | awaitVal h _ | awaitTaskTrap h => simp [emptyPool] at h
  | concPrim hrl =>
    simp only [freeVars] at he1
    cases hs with
    | concPrimArgs hsl =>
      rcases specRelList_step_forward S hσ he1 hrl hsl with ⟨args2', hrl', hsl2⟩
      exact ⟨.concPrim _ args2', .concPrim hrl', .concPrimArgs hsl2⟩
    | concPrimTrap htr =>
      exact ⟨.trap _, .trap _, .concPrimTrap ((specRelList_firstTrap_iff hrl).mp htr)⟩
    | concPrimVal hc => exact False.elim (stepConcPrim_emptyPool_none_false hc)
termination_by sizeOf e1

theorem specRelList_step_forward {Δ : AdtEnv} {Φ : FunEnv} (S : ValidLoopSpec Δ Φ)
    {es1 es2 es1' : List Expr} {σ σ' : Store}
    (hσ : ClosedStore σ) (hes1 : freeVarsList es1 = [])
    (hrl : SpecRelList S.loopName S.specName S.cbEntry S.cls S.fvVals S.cbParams.length S.stateParams.length es1 es2)
    (hsl : StepList Δ Φ emptyPool es1 σ es1' σ' .none) :
    ∃ es2', SpecRelList S.loopName S.specName S.cbEntry S.cls S.fvVals S.cbParams.length S.stateParams.length es1' es2' ∧
            StepList Δ Φ emptyPool es2 σ es2' σ' .none := by
  cases hrl with
  | nil => cases hsl
  | cons hr hrs =>
    simp only [freeVarsList, List.append_eq_nil_iff] at hes1
    cases hsl with
    | head hs1 =>
      rcases specRel_step_forward S hσ hes1.1 hr hs1 with ⟨e2', hr', hs2⟩
      exact ⟨e2' :: _, .cons hr' hrs, .head hs2⟩
    | tail hv1 hsl1 =>
      rcases specRel_val_left hr hv1 with ⟨rfl, hv2⟩
      rcases specRelList_step_forward S hσ hes1.2 hrs hsl1 with ⟨es2', hrs', hsl2⟩
      exact ⟨_ :: es2', .cons hr hrs', .tail hv2 hsl2⟩
termination_by sizeOf es1
end

/- 1-to-1 Backward Lockstep Simulation (`specRel_step_backward`). -/
mutual
theorem specRel_step_backward {Δ : AdtEnv} {Φ : FunEnv} (S : ValidLoopSpec Δ Φ)
    {e1 e2 e2' : Expr} {σ σ' : Store}
    (hσ : ClosedStore σ) (he1 : freeVars e1 = [])
    (hr : SpecRel S.loopName S.specName S.cbEntry S.cls S.fvVals S.cbParams.length S.stateParams.length e1 e2)
    (hs2 : Step Δ Φ emptyPool e2 σ e2' σ' .none) :
    ∃ e1', SpecRel S.loopName S.specName S.cbEntry S.cls S.fvVals S.cbParams.length S.stateParams.length e1' e2' ∧
           Step Δ Φ emptyPool e1 σ e1' σ' .none := by
  cases hr with
  | lit _ | var _ | loc _ | taskRef _ | syncRef _ _ | lam _ _ _ _ | trap _ =>
    cases hs2
  | tuple hrl =>
    simp only [freeVars] at he1
    cases hs2 with
    | tupleStep hsl2 =>
      rcases specRelList_step_backward S hσ he1 hrl hsl2 with ⟨es1', hrl', hsl1⟩
      exact ⟨.tuple es1', .tuple hrl', .tupleStep hsl1⟩
    | tupleTrap htr2 =>
      exact ⟨.trap _, .trap _, .tupleTrap ((specRelList_firstTrap_iff hrl).mpr htr2)⟩
  | block hrl =>
    cases hrl with
    | nil => cases hs2; exact ⟨.lit .unit, .lit .unit, .blockEmpty⟩
    | cons hr1 hrs =>
      cases hrs with
      | nil => cases hs2; exact ⟨_, hr1, .blockSingle⟩
      | cons hr2 hrs' =>
        simp only [freeVars, freeVarsList, List.append_eq_nil_iff] at he1
        cases hs2 with
        | blockConsStep hs_b2 =>
          rcases specRel_step_backward S hσ he1.1 hr1 hs_b2 with ⟨e1', hr1', hs_b1⟩
          exact ⟨.block (e1' :: _), .block (.cons hr1' (.cons hr2 hrs')), .blockConsStep hs_b1⟩
        | blockConsVal hv2 =>
          rcases specRel_val_right hr1 hv2 with ⟨rfl, hv1⟩
          exact ⟨.block _, .block (.cons hr2 hrs'), .blockConsVal hv1⟩
        | blockConsTrap =>
          rw [specRel_trap_right hr1]
          exact ⟨.trap _, .trap _, .blockConsTrap⟩
  | @specCb args1 args2 hlen hrl =>
    simp only [freeVars, List.append_eq_nil_iff] at he1
    cases hs2 with
    | applyDirArgs hsl2 =>
      rcases stepList_append_vals_inv S.hfvVal hsl2 with ⟨args2', rfl, hsl_cb2⟩
      rcases specRelList_step_backward S hσ he1.2 hrl hsl_cb2 with ⟨args1', hrl', hsl1⟩
      have hlen' : args1'.length = S.cbParams.length := by
        rw [stepList_length_eq hsl1, hlen]
      exact ⟨.apply S.cls args1', .specCb hlen' hrl', .applyArgs S.cls_isValue hsl1⟩
    | applyDirTrap htr2 =>
      have htr1 := (specRelList_firstTrap_iff hrl).mpr ((listFirstTrap_append_vals_iff S.hfvVal).mp htr2)
      exact ⟨.trap _, .trap _, .applyArgsTrap S.cls_isValue htr1⟩
    | applyDirBeta hfn hall2 _ =>
      have hvs2 : ∀ v ∈ args2, IsValue v := fun v hv => hall2 v (List.mem_append_left _ hv)
      rcases specRelList_val_right hrl hvs2 with ⟨rfl, hvs1⟩
      rw [S.hCb] at hfn; injection hfn with hfd; subst hfd
      have hargsCl : ∀ v ∈ args1, freeVars v = [] := freeVarsList_eq_nil_iff.mp he1.2
      have hs1_beta : Step Δ Φ emptyPool (.apply S.cls args1) σ
          (substMany (zipParams S.cbParams args1) (substMany (zipParams S.fvs S.fvVals) S.cbBody)) σ .none := by
        rw [S.cls_eq_lam]; exact .applyBeta hvs1 hlen
      rw [← substMany_lam_apply_eq_flat S.cbParams S.fvs args1 S.fvVals S.cbBody
            hlen S.hfvLen hargsCl S.hfvCl S.hcbDisj]
      exact ⟨_, SpecRel.refl _ _ _ _ _ _ _ _, hs1_beta⟩
  | apply hfn hrl =>
    simp only [freeVars, List.append_eq_nil_iff] at he1
    cases hs2 with
    | applyFn hs_fn2 =>
      rcases specRel_step_backward S hσ he1.1 hfn hs_fn2 with ⟨fn1', hfn', hs_fn1⟩
      exact ⟨.apply fn1' _, .apply hfn' hrl, .applyFn hs_fn1⟩
    | applyFnTrap =>
      rw [specRel_trap_right hfn]
      exact ⟨.trap _, .trap _, .applyFnTrap⟩
    | applyArgs hv2 hsl2 =>
      rcases specRel_val_right hfn hv2 with ⟨rfl, hv1⟩
      rcases specRelList_step_backward S hσ he1.2 hrl hsl2 with ⟨args1', hrl', hsl1⟩
      exact ⟨.apply _ args1', .apply hfn hrl', .applyArgs hv1 hsl1⟩
    | applyArgsTrap hv2 htr2 =>
      rcases specRel_val_right hfn hv2 with ⟨rfl, hv1⟩
      exact ⟨.trap _, .trap _, .applyArgsTrap hv1 ((specRelList_firstTrap_iff hrl).mpr htr2)⟩
    | applyBeta hvs2 hlen =>
      rcases specRel_val_right hfn (.lam _ _ _ _) with ⟨heq_fn, _⟩
      rcases specRelList_val_right hrl hvs2 with ⟨rfl, hvs1⟩
      rw [heq_fn]
      exact ⟨_, SpecRel.refl _ _ _ _ _ _ _ _, .applyBeta hvs1 hlen⟩
  | @specCall args1 args2 hlen hrl =>
    simp only [freeVars, freeVarsList, List.append_eq_nil_iff] at he1
    cases hs2 with
    | applyDirArgs hsl2 =>
      rcases stepList_prepend_vals_inv S.hfvVal hsl2 with ⟨args2', rfl, hsl_st2⟩
      rcases specRelList_step_backward S hσ he1.2 hrl hsl_st2 with ⟨args1', hrl', hsl_st1⟩
      have hlen' : args1'.length = S.stateParams.length := by
        rw [stepList_length_eq hsl_st1, hlen]
      exact ⟨.applyDir S.loopName (S.cls :: args1'), .specCall hlen' hrl',
        .applyDirArgs (.tail S.cls_isValue hsl_st1)⟩
    | applyDirTrap htr2 =>
      have htr1 := (specRelList_firstTrap_iff hrl).mpr ((listFirstTrap_prepend_vals_iff S.hfvVal).mp htr2)
      exact ⟨.trap _, .trap _, .applyDirTrap (.tail S.cls_isValue htr1)⟩
    | applyDirBeta hfn hall2 _ =>
      have hvs2 : ∀ v ∈ args2, IsValue v := fun v hv => hall2 v (List.mem_append_right _ hv)
      rcases specRelList_val_right hrl hvs2 with ⟨rfl, hvs1⟩
      rw [S.hSpec] at hfn; injection hfn with hfd; subst hfd
      have hallVal1 : ∀ v ∈ S.cls :: args1, IsValue v := by
        intro v hv; rcases List.mem_cons.mp hv with rfl | h2
        · exact S.cls_isValue
        · exact hvs1 v h2
      have hallLen1 : (S.cls :: args1).length = ((S.fParam, S.fnTy) :: S.stateParams).length := by
        simp [hlen]
      refine ⟨_, ?_, .applyDirBeta S.hLoop hallVal1 hallLen1⟩
      exact specEligible_subst_rel S.loopName S.specName S.cbEntry S.fParam S.fnTy
        S.cls_closed S.hfvCl S.hfvLen hlen S.hSpecNodup S.hLoopNoFv S.hEligible
  | applyDir hrl =>
    simp only [freeVars] at he1
    cases hs2 with
    | applyDirArgs hsl2 =>
      rcases specRelList_step_backward S hσ he1 hrl hsl2 with ⟨args1', hrl', hsl1⟩
      exact ⟨.applyDir _ args1', .applyDir hrl', .applyDirArgs hsl1⟩
    | applyDirTrap htr2 =>
      exact ⟨.trap _, .trap _, .applyDirTrap ((specRelList_firstTrap_iff hrl).mpr htr2)⟩
    | applyDirBeta hfn hvs2 hlen =>
      rcases specRelList_val_right hrl hvs2 with ⟨rfl, hvs1⟩
      exact ⟨_, SpecRel.refl _ _ _ _ _ _ _ _, .applyDirBeta hfn hvs1 hlen⟩
  | bin ha hb =>
    simp only [freeVars, List.append_eq_nil_iff] at he1
    cases hs2 with
    | binLeft hs_a2 =>
      rcases specRel_step_backward S hσ he1.1 ha hs_a2 with ⟨a1', ha', hs_a1⟩
      exact ⟨.bin _ a1' _, .bin ha' hb, .binLeft hs_a1⟩
    | binLeftTrap => rw [specRel_trap_right ha]; exact ⟨.trap _, .trap _, .binLeftTrap⟩
    | binAndFalse =>
      rcases specRel_val_right ha (.lit _) with ⟨heq, _⟩; rw [heq]
      exact ⟨.lit (.bool false), .lit _, .binAndFalse⟩
    | binAndTrue =>
      rcases specRel_val_right ha (.lit _) with ⟨heq, _⟩; rw [heq]
      exact ⟨_, hb, .binAndTrue⟩
    | binOrTrue =>
      rcases specRel_val_right ha (.lit _) with ⟨heq, _⟩; rw [heq]
      exact ⟨.lit (.bool true), .lit _, .binOrTrue⟩
    | binOrFalse =>
      rcases specRel_val_right ha (.lit _) with ⟨heq, _⟩; rw [heq]
      exact ⟨_, hb, .binOrFalse⟩
    | binRight hna hno hv2 hs_b2 =>
      rcases specRel_val_right ha hv2 with ⟨rfl, hv1⟩
      rcases specRel_step_backward S hσ he1.2 hb hs_b2 with ⟨b1', hb', hs_b1⟩
      exact ⟨.bin _ _ b1', .bin ha hb', .binRight hna hno hv1 hs_b1⟩
    | binRightTrap hna hno hv2 =>
      rcases specRel_val_right ha hv2 with ⟨rfl, hv1⟩
      rw [specRel_trap_right hb]
      exact ⟨.trap _, .trap _, .binRightTrap hna hno hv1⟩
    | binVal hev =>
      rcases specRel_val_right ha (.lit _) with ⟨heq1, _⟩
      rcases specRel_val_right hb (.lit _) with ⟨heq2, _⟩
      rw [heq1, heq2]
      exact ⟨.lit _, .lit _, .binVal hev⟩
    | binTrap hev =>
      rcases specRel_val_right ha (.lit _) with ⟨heq1, _⟩
      rcases specRel_val_right hb (.lit _) with ⟨heq2, _⟩
      rw [heq1, heq2]
      exact ⟨.trap _, .trap _, .binTrap hev⟩
  | un he =>
    simp only [freeVars] at he1
    cases hs2 with
    | unStep hs_e2 =>
      rcases specRel_step_backward S hσ he1 he hs_e2 with ⟨e1', he', hs_e1⟩
      exact ⟨.un _ e1', .un he', .unStep hs_e1⟩
    | unTrap => rw [specRel_trap_right he]; exact ⟨.trap _, .trap _, .unTrap⟩
    | unVal hev =>
      rcases specRel_val_right he (.lit _) with ⟨heq, _⟩; rw [heq]
      exact ⟨.lit _, .lit _, .unVal hev⟩
  | let_ ha hb =>
    simp only [freeVars, List.append_eq_nil_iff] at he1
    cases hs2 with
    | letStep hs_a2 =>
      rcases specRel_step_backward S hσ he1.1 ha hs_a2 with ⟨a1', ha', hs_a1⟩
      exact ⟨.let_ _ a1' _, .let_ ha' hb, .letStep hs_a1⟩
    | letTrap => rw [specRel_trap_right ha]; exact ⟨.trap _, .trap _, .letTrap⟩
    | letVal hv2 =>
      rcases specRel_val_right ha hv2 with ⟨rfl, hv1⟩
      exact ⟨_, specRel_subst S.cls_closed S.hfvCl _ he1.1 hb, .letVal hv1⟩
  | if_ hc ht he =>
    simp only [freeVars, List.append_eq_nil_iff] at he1
    cases hs2 with
    | ifStep hs_c2 =>
      rcases specRel_step_backward S hσ he1.1.1 hc hs_c2 with ⟨c1', hc', hs_c1⟩
      exact ⟨.if_ c1' _ _, .if_ hc' ht he, .ifStep hs_c1⟩
    | ifTrap => rw [specRel_trap_right hc]; exact ⟨.trap _, .trap _, .ifTrap⟩
    | ifTrue =>
      rcases specRel_val_right hc (.lit _) with ⟨heq, _⟩; rw [heq]
      exact ⟨_, ht, .ifTrue⟩
    | ifFalse =>
      rcases specRel_val_right hc (.lit _) with ⟨heq, _⟩; rw [heq]
      exact ⟨_, he, .ifFalse⟩
  | while_ hc hb =>
    cases hs2 with
    | whileUnfold =>
      exact ⟨_, .if_ hc (.block (.cons hb (.cons (.while_ hc hb) .nil))) (.lit .unit), .whileUnfold⟩
  | match_ hs_r harms =>
    simp only [freeVars, List.append_eq_nil_iff] at he1
    cases hs2 with
    | matchScrut hs_s2 =>
      rcases specRel_step_backward S hσ he1.1 hs_r hs_s2 with ⟨s1', hs_r', hs_s1⟩
      exact ⟨.match_ s1' _, .match_ hs_r' harms, .matchScrut hs_s1⟩
    | matchScrutTrap => rw [specRel_trap_right hs_r]; exact ⟨.trap _, .trap _, .matchScrutTrap⟩
    | matchEmpty hv2 =>
      cases harms with
      | nil =>
        rcases specRel_val_right hs_r hv2 with ⟨rfl, hv1⟩
        exact ⟨.trap .matchFailure, .trap _, .matchEmpty hv1⟩
    | matchHit hv2 hm =>
      cases harms with
      | cons hb _ =>
        rcases specRel_val_right hs_r hv2 with ⟨rfl, hv1⟩
        rcases matchPat_closed he1.1 hm with ⟨henv, _⟩
        exact ⟨_, specRel_substMany S.cls_closed S.hfvCl henv hb, .matchHit hv1 hm⟩
    | matchMiss hv2 hm =>
      cases harms with
      | cons _ hrs =>
        rcases specRel_val_right hs_r hv2 with ⟨rfl, hv1⟩
        exact ⟨_, .match_ hs_r hrs, .matchMiss hv1 hm⟩
  | makeData hrl =>
    simp only [freeVars] at he1
    cases hs2 with
    | makeDataStep hsl2 =>
      rcases specRelList_step_backward S hσ he1 hrl hsl2 with ⟨es1', hrl', hsl1⟩
      exact ⟨.makeData _ _ es1', .makeData hrl', .makeDataStep hsl1⟩
    | makeDataTrap htr2 =>
      exact ⟨.trap _, .trap _, .makeDataTrap ((specRelList_firstTrap_iff hrl).mpr htr2)⟩
  | getTag he =>
    simp only [freeVars] at he1
    cases hs2 with
    | getTagStep hs_e2 =>
      rcases specRel_step_backward S hσ he1 he hs_e2 with ⟨e1', he', hs_e1⟩
      exact ⟨.getTag e1', .getTag he', .getTagStep hs_e1⟩
    | getTagTrap => rw [specRel_trap_right he]; exact ⟨.trap _, .trap _, .getTagTrap⟩
    | getTagVal hvs2 =>
      rcases specRel_val_right he (.makeData _ _ hvs2) with ⟨heq, _⟩; rw [heq]
      exact ⟨.lit _, .lit _, .getTagVal hvs2⟩
  | cellNew he =>
    simp only [freeVars] at he1
    cases hs2 with
    | cellNewStep hs_e2 =>
      rcases specRel_step_backward S hσ he1 he hs_e2 with ⟨e1', he', hs_e1⟩
      exact ⟨.cellNew e1', .cellNew he', .cellNewStep hs_e1⟩
    | cellNewTrap => rw [specRel_trap_right he]; exact ⟨.trap _, .trap _, .cellNewTrap⟩
    | cellNewVal hv2 =>
      rcases specRel_val_right he hv2 with ⟨rfl, hv1⟩
      exact ⟨.loc _, .loc _, .cellNewVal hv1⟩
  | cellGet he =>
    simp only [freeVars] at he1
    cases hs2 with
    | cellGetStep hs_e2 =>
      rcases specRel_step_backward S hσ he1 he hs_e2 with ⟨e1', he', hs_e1⟩
      exact ⟨.cellGet e1', .cellGet he', .cellGetStep hs_e1⟩
    | cellGetTrap => rw [specRel_trap_right he]; exact ⟨.trap _, .trap _, .cellGetTrap⟩
    | cellGetVal hl =>
      rcases specRel_val_right he (.loc _) with ⟨heq, _⟩; rw [heq]
      exact ⟨_, SpecRel.refl _ _ _ _ _ _ _ _, .cellGetVal hl⟩
  | cellSet ha hb =>
    simp only [freeVars, List.append_eq_nil_iff] at he1
    cases hs2 with
    | cellSetLeft hs_a2 =>
      rcases specRel_step_backward S hσ he1.1 ha hs_a2 with ⟨a1', ha', hs_a1⟩
      exact ⟨.cellSet a1' _, .cellSet ha' hb, .cellSetLeft hs_a1⟩
    | cellSetLeftTrap => rw [specRel_trap_right ha]; exact ⟨.trap _, .trap _, .cellSetLeftTrap⟩
    | cellSetRight hv2 hs_b2 =>
      rcases specRel_val_right ha hv2 with ⟨rfl, hv1⟩
      rcases specRel_step_backward S hσ he1.2 hb hs_b2 with ⟨b1', hb', hs_b1⟩
      exact ⟨.cellSet _ b1', .cellSet ha hb', .cellSetRight hv1 hs_b1⟩
    | cellSetRightTrap hv2 =>
      rcases specRel_val_right ha hv2 with ⟨rfl, hv1⟩
      rw [specRel_trap_right hb]
      exact ⟨.trap _, .trap _, .cellSetRightTrap hv1⟩
    | cellSetVal hlt hv2 =>
      rcases specRel_val_right ha (.loc _) with ⟨heq, _⟩; rw [heq]
      rcases specRel_val_right hb hv2 with ⟨rfl, hv1⟩
      exact ⟨.lit .unit, .lit .unit, .cellSetVal hlt hv1⟩
  | spawn he =>
    simp only [freeVars] at he1
    cases hs2 with
    | spawnStep hs_e2 =>
      rcases specRel_step_backward S hσ he1 he hs_e2 with ⟨e1', he', hs_e1⟩
      exact ⟨.spawn e1', .spawn he', .spawnStep hs_e1⟩
    | spawnTrap => rw [specRel_trap_right he]; exact ⟨.trap _, .trap _, .spawnTrap⟩
  | await he =>
    simp only [freeVars] at he1
    cases hs2 with
    | awaitStep hs_e2 =>
      rcases specRel_step_backward S hσ he1 he hs_e2 with ⟨e1', he', hs_e1⟩
      exact ⟨.await e1', .await he', .awaitStep hs_e1⟩
    | awaitTrap => rw [specRel_trap_right he]; exact ⟨.trap _, .trap _, .awaitTrap⟩
    | awaitVal h _ | awaitTaskTrap h => simp [emptyPool] at h
  | concPrim hrl =>
    simp only [freeVars] at he1
    cases hs2 with
    | concPrimArgs hsl2 =>
      rcases specRelList_step_backward S hσ he1 hrl hsl2 with ⟨args1', hrl', hsl1⟩
      exact ⟨.concPrim _ args1', .concPrim hrl', .concPrimArgs hsl1⟩
    | concPrimTrap htr2 =>
      exact ⟨.trap _, .trap _, .concPrimTrap ((specRelList_firstTrap_iff hrl).mpr htr2)⟩
    | concPrimVal hc => exact False.elim (stepConcPrim_emptyPool_none_false hc)
termination_by sizeOf e1

theorem specRelList_step_backward {Δ : AdtEnv} {Φ : FunEnv} (S : ValidLoopSpec Δ Φ)
    {es1 es2 es2' : List Expr} {σ σ' : Store}
    (hσ : ClosedStore σ) (hes1 : freeVarsList es1 = [])
    (hrl : SpecRelList S.loopName S.specName S.cbEntry S.cls S.fvVals S.cbParams.length S.stateParams.length es1 es2)
    (hsl2 : StepList Δ Φ emptyPool es2 σ es2' σ' .none) :
    ∃ es1', SpecRelList S.loopName S.specName S.cbEntry S.cls S.fvVals S.cbParams.length S.stateParams.length es1' es2' ∧
            StepList Δ Φ emptyPool es1 σ es1' σ' .none := by
  cases hrl with
  | nil => cases hsl2
  | cons hr hrs =>
    simp only [freeVarsList, List.append_eq_nil_iff] at hes1
    cases hsl2 with
    | head hs2 =>
      rcases specRel_step_backward S hσ hes1.1 hr hs2 with ⟨e1', hr', hs1⟩
      exact ⟨e1' :: _, .cons hr' hrs, .head hs1⟩
    | tail hv2 hsl_r2 =>
      rcases specRel_val_right hr hv2 with ⟨rfl, hv1⟩
      rcases specRelList_step_backward S hσ hes1.2 hrs hsl_r2 with ⟨es1', hrs', hsl1⟩
      exact ⟨_ :: es1', .cons hr hrs', .tail hv1 hsl1⟩
termination_by sizeOf es1
end

theorem specRel_steps_forward {Δ : AdtEnv} {Φ : FunEnv} (S : ValidLoopSpec Δ Φ)
    {e1 e2 e1' : Expr} {σ σ' : Store}
    (hσ : ClosedStore σ) (he1 : freeVars e1 = [])
    (hr : SpecRel S.loopName S.specName S.cbEntry S.cls S.fvVals S.cbParams.length S.stateParams.length e1 e2)
    (hsteps : Steps Δ Φ e1 σ e1' σ') :
    ∃ e2', SpecRel S.loopName S.specName S.cbEntry S.cls S.fvVals S.cbParams.length S.stateParams.length e1' e2' ∧
           Steps Δ Φ e2 σ e2' σ' := by
  induction hsteps generalizing e2 with
  | refl => exact ⟨e2, hr, .refl _ _⟩
  | trans hs1 _ ih =>
    rcases specRel_step_forward S hσ he1 hr hs1 with ⟨e2_mid, hr_mid, hs2⟩
    rcases step_preserves_closed S.hΦcl hσ he1 hs1 with ⟨he1_mid, hσ_mid⟩
    rcases ih hσ_mid he1_mid hr_mid with ⟨e2', hr', hsteps2⟩
    exact ⟨e2', hr', .trans hs2 hsteps2⟩

theorem specRel_steps_backward {Δ : AdtEnv} {Φ : FunEnv} (S : ValidLoopSpec Δ Φ)
    {e1 e2 e2' : Expr} {σ σ' : Store}
    (hσ : ClosedStore σ) (he1 : freeVars e1 = [])
    (hr : SpecRel S.loopName S.specName S.cbEntry S.cls S.fvVals S.cbParams.length S.stateParams.length e1 e2)
    (hsteps : Steps Δ Φ e2 σ e2' σ') :
    ∃ e1', SpecRel S.loopName S.specName S.cbEntry S.cls S.fvVals S.cbParams.length S.stateParams.length e1' e2' ∧
           Steps Δ Φ e1 σ e1' σ' := by
  induction hsteps generalizing e1 with
  | refl => exact ⟨e1, hr, .refl _ _⟩
  | trans hs2 _ ih =>
    rcases specRel_step_backward S hσ he1 hr hs2 with ⟨e1_mid, hr_mid, hs1⟩
    rcases step_preserves_closed S.hΦcl hσ he1 hs1 with ⟨he1_mid, hσ_mid⟩
    rcases ih hσ_mid he1_mid hr_mid with ⟨e1', hr', hsteps1⟩
    exact ⟨e1', hr', .trans hs1 hsteps1⟩

/-- **Main Theorem: Soundness of Self-Recursive Higher-Order Loop Specialization (`$spec$`, `coTrySpecializeHofLoop`)**:
    For any valid `SpecConstr` specialization `S : ValidLoopSpec Δ Φ` and closed initial loop state
    arguments `initArgs` (`initArgs.length = S.stateParams.length`), calling the specialized direct
    loop `.applyDir S.specName (S.fvVals ++ initArgs)` reaches the exact same terminal values,
    runtime traps, and final mutable `Cell` heaps `σ'` as `.applyDir S.loopName (S.cls :: initArgs)`! -/
theorem hof_loop_spec_obsEquiv {Δ : AdtEnv} {Φ : FunEnv} (S : ValidLoopSpec Δ Φ)
    {initArgs : List Expr} {σ σ' : Store} {out : Expr}
    (hσ : ClosedStore σ) (hout : IsTerminal out)
    (hlen : initArgs.length = S.stateParams.length)
    (hargsCl : ∀ e ∈ initArgs, freeVars e = []) :
    Steps Δ Φ (.applyDir S.loopName (S.cls :: initArgs)) σ out σ' ↔
      Steps Δ Φ (.applyDir S.specName (S.fvVals ++ initArgs)) σ out σ' := by
  have he1 : freeVars (.applyDir S.loopName (S.cls :: initArgs)) = [] := by
    simp [freeVars, freeVarsList, S.cls_closed, freeVarsList_eq_nil_iff.mpr hargsCl]
  have hr0 : SpecRel S.loopName S.specName S.cbEntry S.cls S.fvVals
      S.cbParams.length S.stateParams.length
      (.applyDir S.loopName (S.cls :: initArgs))
      (.applyDir S.specName (S.fvVals ++ initArgs)) :=
    .specCall hlen (SpecRelList.refl _ _ _ _ _ _ _ initArgs)
  constructor
  · intro h1
    rcases specRel_steps_forward S hσ he1 hr0 h1 with ⟨e2', hr', h2⟩
    rw [specRel_terminal_left hr' hout] at h2
    exact h2
  · intro h2
    rcases specRel_steps_backward S hσ he1 hr0 h2 with ⟨e1', hr', h1⟩
    rw [specRel_terminal_right hr' hout] at h1
    exact h1

/-- **Concrete Positive Witness (`concrete_spec_loop_witness`)**:
    Explicitly inhabits `ValidLoopSpec` on a recursive higher-order loop `foldLoop(f, n, acc)`
    with capturing closure `(x) -> x * k` (`k = 3`, `n = 1`, `acc = 9`), proves `foldLoop`
    evaluates to `15`, and derives `foldLoop$spec(3, 1, 9) -> 15` via `hof_loop_spec_obsEquiv`
    (demonstrating end-to-end non-vacuity of `ValidLoopSpec` and `SpecEligible`). -/
theorem concrete_spec_loop_witness :
    let loopBody : Expr :=
      .if_ (.bin .leInt (.var "n") (.lit (.int 0)))
        (.var "acc")
        (.applyDir "foldLoop"
          [.var "f",
           .bin .sub (.var "n") (.lit (.int 1)),
           .bin .add (.var "acc") (.apply (.var "f") [.lit (.int 2)])])
    let cbBody : Expr := .bin .mul (.var "x") (.var "k")
    let specBody : Expr :=
      specializeLoopExpr "foldLoop" "foldLoop$spec" "cb$entry" "f" ["k"] loopBody
    let Φ : FunEnv := fun nm =>
      if nm == "foldLoop" then
        some { name := "foldLoop",
               params := [("f", .fn .local [.int] .int), ("n", .int), ("acc", .int)],
               retTy := .int, body := loopBody }
      else if nm == "foldLoop$spec" then
        some { name := "foldLoop$spec",
               params := [("k", .int), ("n", .int), ("acc", .int)],
               retTy := .int, body := specBody }
      else if nm == "cb$entry" then
        some { name := "cb$entry",
               params := [("x", .int), ("k", .int)],
               retTy := .int, body := cbBody }
      else none
    let cls : Expr := .lam .local [("x", .int)] .int (.bin .mul (.var "x") (.lit (.int 3)))
    ∃ S : ValidLoopSpec (fun _ => none) Φ,
      S.cls = cls ∧
      Steps (fun _ => none) Φ (.applyDir "foldLoop" [cls, .lit (.int 1), .lit (.int 9)]) []
        (.lit (.int 15)) [] ∧
      Steps (fun _ => none) Φ (.applyDir "foldLoop$spec" [.lit (.int 3), .lit (.int 1), .lit (.int 9)]) []
        (.lit (.int 15)) [] := by
  let loopBody : Expr :=
    .if_ (.bin .leInt (.var "n") (.lit (.int 0)))
      (.var "acc")
      (.applyDir "foldLoop"
        [.var "f",
         .bin .sub (.var "n") (.lit (.int 1)),
         .bin .add (.var "acc") (.apply (.var "f") [.lit (.int 2)])])
  let cbBody : Expr := .bin .mul (.var "x") (.var "k")
  let specBody : Expr :=
    specializeLoopExpr "foldLoop" "foldLoop$spec" "cb$entry" "f" ["k"] loopBody
  let Φ : FunEnv := fun nm =>
    if nm == "foldLoop" then
      some { name := "foldLoop",
             params := [("f", .fn .local [.int] .int), ("n", .int), ("acc", .int)],
             retTy := .int, body := loopBody }
    else if nm == "foldLoop$spec" then
      some { name := "foldLoop$spec",
             params := [("k", .int), ("n", .int), ("acc", .int)],
             retTy := .int, body := specBody }
    else if nm == "cb$entry" then
      some { name := "cb$entry",
             params := [("x", .int), ("k", .int)],
             retTy := .int, body := cbBody }
    else none
  let cls : Expr := .lam .local [("x", .int)] .int (.bin .mul (.var "x") (.lit (.int 3)))
  have hspec_eq : specBody =
      .if_ (.bin .leInt (.var "n") (.lit (.int 0)))
        (.var "acc")
        (.applyDir "foldLoop$spec"
          [.var "k",
           .bin .sub (.var "n") (.lit (.int 1)),
           .bin .add (.var "acc") (.applyDir "cb$entry" [.lit (.int 2), .var "k"])]) := by
    simp [specBody, loopBody, specializeLoopExpr, specializeLoopList]
  have hΦcl : ClosedFunEnv Φ := by
    intro nm fd hfd z hz
    simp only [Φ] at hfd
    split at hfd
    · injection hfd with hfd; subst hfd
      simp [loopBody, freeVars, freeVarsList] at hz ⊢
      rcases hz with rfl | rfl | rfl | rfl | rfl | rfl <;> simp
    · split at hfd
      · injection hfd with hfd; subst hfd
        rw [hspec_eq] at hz
        simp [freeVars, freeVarsList] at hz ⊢
        rcases hz with rfl | rfl | rfl | rfl | rfl | rfl <;> simp
      · split at hfd
        · injection hfd with hfd; subst hfd
          simp [cbBody, freeVars] at hz ⊢
          exact hz
        · cases hfd
  let S : ValidLoopSpec (fun _ => none) Φ := {
    loopName := "foldLoop"
    specName := "foldLoop$spec"
    cbEntry := "cb$entry"
    fParam := "f"
    fnTy := .fn .local [.int] .int
    loopRet := .int
    loopBody := loopBody
    cbMode := .local
    cbParams := [("x", .int)]
    cbRet := .int
    cbBody := cbBody
    fvs := [("k", .int)]
    fvVals := [.lit (.int 3)]
    stateParams := [("n", .int), ("acc", .int)]
    hΦcl := hΦcl
    hLoop := by rfl
    hSpec := by rfl
    hCb := by rfl
    hfvVal := fun v hv => by
      rcases List.mem_cons.mp hv with rfl | h
      · exact .lit _
      · cases h
    hfvCl := fun v hv => by
      rcases List.mem_cons.mp hv with rfl | h
      · rfl
      · cases h
    hfvLen := rfl
    hcbDisj := by decide
    hfParamNot := by decide
    hSpecNodup := by decide
    hLoopNoFv := by
      intro z hz
      simp [loopBody, freeVars, freeVarsList] at hz
      rcases hz with rfl | rfl | rfl | rfl | rfl | rfl <;> decide
    hEligible := .if_
      (.bin (.var (by decide)) (.lit _))
      (.var (by decide))
      (.selfCall rfl (.cons (.bin (.var (by decide)) (.lit _))
        (.cons (.bin (.var (by decide)) (.cbCall rfl (.cons (.lit _) .nil))) .nil)))
  }
  have hcls_eq : S.cls = cls := rfl
  have hv_init : ∀ v ∈ ([cls, .lit (.int 1), .lit (.int 9)] : List Expr), IsValue v := by
    intro v hv; rcases List.mem_cons.mp hv with rfl | h1
    · exact .lam _ _ _ _
    · rcases List.mem_cons.mp h1 with rfl | h2
      · exact .lit _
      · rcases List.mem_cons.mp h2 with rfl | h3
        · exact .lit _
        · cases h3
  have hv_iter1 : ∀ v ∈ ([cls, .lit (.int 0), .lit (.int 15)] : List Expr), IsValue v := by
    intro v hv; rcases List.mem_cons.mp hv with rfl | h1
    · exact .lam _ _ _ _
    · rcases List.mem_cons.mp h1 with rfl | h2
      · exact .lit _
      · rcases List.mem_cons.mp h2 with rfl | h3
        · exact .lit _
        · cases h3
  have hv_cb : ∀ v ∈ ([.lit (.int 2)] : List Expr), IsValue v := by
    intro v hv; rcases List.mem_cons.mp hv with rfl | h
    · exact .lit _
    · cases h
  have hOrig : Steps (fun _ => none) Φ (.applyDir "foldLoop" [cls, .lit (.int 1), .lit (.int 9)]) []
      (.lit (.int 15)) [] := by
    refine .trans (.applyDirBeta rfl hv_init rfl) ?_
    refine .trans (.ifStep (.binVal rfl)) ?_
    refine .trans .ifFalse ?_
    refine .trans (.applyDirArgs (.tail (.lam _ _ _ _) (.head (.binVal rfl)))) ?_
    refine .trans (.applyDirArgs (.tail (.lam _ _ _ _) (.tail (.lit _)
      (.head (.binRight (by decide) (by decide) (.lit _) (.applyBeta hv_cb rfl)))))) ?_
    refine .trans (.applyDirArgs (.tail (.lam _ _ _ _) (.tail (.lit _)
      (.head (.binRight (by decide) (by decide) (.lit _) (.binVal rfl)))))) ?_
    refine .trans (.applyDirArgs (.tail (.lam _ _ _ _) (.tail (.lit _)
      (.head (.binVal rfl))))) ?_
    refine .trans (.applyDirBeta rfl hv_iter1 rfl) ?_
    refine .trans (.ifStep (.binVal rfl)) ?_
    exact .single .ifTrue
  have hSpec : Steps (fun _ => none) Φ (.applyDir "foldLoop$spec" [.lit (.int 3), .lit (.int 1), .lit (.int 9)]) []
      (.lit (.int 15)) [] := by
    refine (hof_loop_spec_obsEquiv S (fun _ h => by cases h) (Or.inl (.lit _)) rfl ?_).mp hOrig
    intro e he
    rcases List.mem_cons.mp he with rfl | h2
    · rfl
    · rcases List.mem_cons.mp h2 with rfl | h3
      · rfl
      · cases h3
  exact ⟨S, hcls_eq, hOrig, hSpec⟩

/-- **Non-Vacuity Counterexample 4 (`varying_closure_spec_unsound`)**:
    If a recursive function `varyLoop(f, n)` passes a *different* closure `(x) -> x + 100`
    instead of the invariant parameter `f` in its recursive call, rewriting that recursive call
    to `varyLoop$badSpec` (as `coRewriteSelfCallsInSpecBody` at `src/core.gsa:6407` would do if
    `coParamInvariantAndOnlyCalledInTerm` at `src/core.gsa:6253,6275` did not reject this slot;
    see also `unguarded_posSpecialize_varyLoop_counterexample` below where `posSpecializeLoopExpr`
    computes `varyLoop$badSpec` directly!) changes the result from `100` to `1`. -/
theorem varying_closure_spec_unsound :
    let Φ : FunEnv := fun nm =>
      if nm == "varyLoop" then
        some { name := "varyLoop",
               params := [("f", .fn .local [.int] .int), ("n", .int)],
               retTy := .int,
               body := .if_ (.bin .leInt (.var "n") (.lit (.int 0)))
                         (.apply (.var "f") [.lit (.int 0)])
                         (.applyDir "varyLoop"
                           [.lam .local [("x", .int)] .int (.bin .add (.var "x") (.lit (.int 100))),
                            .bin .sub (.var "n") (.lit (.int 1))]) }
      else if nm == "varyLoop$badSpec" then
        some { name := "varyLoop$badSpec",
               params := [("n", .int)],
               retTy := .int,
               body := .if_ (.bin .leInt (.var "n") (.lit (.int 0)))
                         (.bin .add (.lit (.int 0)) (.lit (.int 1)))
                         (.applyDir "varyLoop$badSpec" [.bin .sub (.var "n") (.lit (.int 1))]) }
      else none
    let initCls : Expr := .lam .local [("x", .int)] .int (.bin .add (.var "x") (.lit (.int 1)))
    Steps (fun _ => none) Φ (.applyDir "varyLoop" [initCls, .lit (.int 1)]) [] (.lit (.int 100)) [] ∧
    Steps (fun _ => none) Φ (.applyDir "varyLoop$badSpec" [.lit (.int 1)]) [] (.lit (.int 1)) [] ∧
    ¬ ObsEquiv (fun _ => none) Φ Φ
        (.applyDir "varyLoop" [initCls, .lit (.int 1)])
        (.applyDir "varyLoop$badSpec" [.lit (.int 1)]) := by
  let Φ : FunEnv := fun nm =>
    if nm == "varyLoop" then
      some { name := "varyLoop",
             params := [("f", .fn .local [.int] .int), ("n", .int)],
             retTy := .int,
             body := .if_ (.bin .leInt (.var "n") (.lit (.int 0)))
                       (.apply (.var "f") [.lit (.int 0)])
                       (.applyDir "varyLoop"
                         [.lam .local [("x", .int)] .int (.bin .add (.var "x") (.lit (.int 100))),
                          .bin .sub (.var "n") (.lit (.int 1))]) }
    else if nm == "varyLoop$badSpec" then
      some { name := "varyLoop$badSpec",
             params := [("n", .int)],
             retTy := .int,
             body := .if_ (.bin .leInt (.var "n") (.lit (.int 0)))
                       (.bin .add (.lit (.int 0)) (.lit (.int 1)))
                       (.applyDir "varyLoop$badSpec" [.bin .sub (.var "n") (.lit (.int 1))]) }
    else none
  let initCls : Expr := .lam .local [("x", .int)] .int (.bin .add (.var "x") (.lit (.int 1)))
  let cls100 : Expr := .lam .local [("x", .int)] .int (.bin .add (.var "x") (.lit (.int 100)))
  have hv_init : ∀ v ∈ ([initCls, .lit (.int 1)] : List Expr), IsValue v := by
    intro v hv; rcases List.mem_cons.mp hv with rfl | h2
    · exact .lam _ _ _ _
    · rcases List.mem_cons.mp h2 with rfl | h3
      · exact .lit _
      · cases h3
  have hv_rec : ∀ v ∈ ([cls100, .lit (.int 0)] : List Expr), IsValue v := by
    intro v hv; rcases List.mem_cons.mp hv with rfl | h2
    · exact .lam _ _ _ _
    · rcases List.mem_cons.mp h2 with rfl | h3
      · exact .lit _
      · cases h3
  have hv_1 : ∀ v ∈ ([.lit (.int 1)] : List Expr), IsValue v := by
    intro v hv; rcases List.mem_cons.mp hv with rfl | h
    · exact .lit _
    · cases h
  have hv_0 : ∀ v ∈ ([.lit (.int 0)] : List Expr), IsValue v := by
    intro v hv; rcases List.mem_cons.mp hv with rfl | h
    · exact .lit _
    · cases h
  have h1 : Steps (fun _ => none) Φ (.applyDir "varyLoop" [initCls, .lit (.int 1)]) [] (.lit (.int 100)) [] := by
    refine .trans (.applyDirBeta rfl hv_init rfl) ?_
    refine .trans (.ifStep (.binVal rfl)) ?_
    refine .trans .ifFalse ?_
    refine .trans (.applyDirArgs (.tail (.lam _ _ _ _) (.head (.binVal rfl)))) ?_
    refine .trans (.applyDirBeta rfl hv_rec rfl) ?_
    refine .trans (.ifStep (.binVal rfl)) ?_
    refine .trans .ifTrue ?_
    refine .trans (.applyBeta hv_0 rfl) ?_
    exact .single (.binVal rfl)
  have h2 : Steps (fun _ => none) Φ (.applyDir "varyLoop$badSpec" [.lit (.int 1)]) [] (.lit (.int 1)) [] := by
    refine .trans (.applyDirBeta rfl hv_1 rfl) ?_
    refine .trans (.ifStep (.binVal rfl)) ?_
    refine .trans .ifFalse ?_
    refine .trans (.applyDirArgs (.head (.binVal rfl))) ?_
    refine .trans (.applyDirBeta rfl hv_0 rfl) ?_
    refine .trans (.ifStep (.binVal rfl)) ?_
    refine .trans .ifTrue ?_
    exact .single (.binVal rfl)
  exact ⟨h1, h2, not_obsEquiv_of_distinct_terminals h1 (Or.inl (.lit _)) h2 (Or.inl (.lit _))
    (Or.inl (by rintro ⟨⟩))⟩

/-! ## Part 7: Compiler-Exact Pipeline Alignment (`Φ ↦ Φ'`, `coTermIsPure`, Selective ANF, 3-Valued `coMatchPatKnown` & Captures-First `$flat$`) -/

/- 7.1 Function-Table Extension (`Φ ↦ Φ'`): registering fresh `$flat$` / `$spec$` functions
   outside `dom` preserves exact operational behavior of all existing expressions in `dom`. -/
mutual
def exprInDom (dom : Ident → Bool) : Expr → Bool
  | .lit _ | .var _ | .loc _ | .taskRef _ | .syncRef _ _ | .trap _ => true
  | .tuple es | .block es | .makeData _ _ es | .concPrim _ es => exprListInDom dom es
  | .lam _ _ _ body => exprInDom dom body
  | .apply fn args => exprInDom dom fn && exprListInDom dom args
  | .applyDir nm args => dom nm && exprListInDom dom args
  | .bin _ a b | .let_ _ a b | .while_ a b | .cellSet a b => exprInDom dom a && exprInDom dom b
  | .un _ a | .getTag a | .cellNew a | .cellGet a | .spawn a | .await a => exprInDom dom a
  | .if_ c t e => exprInDom dom c && exprInDom dom t && exprInDom dom e
  | .match_ s arms => exprInDom dom s && exprArmsInDom dom arms

def exprListInDom (dom : Ident → Bool) : List Expr → Bool
  | [] => true
  | e :: es => exprInDom dom e && exprListInDom dom es

def exprArmsInDom (dom : Ident → Bool) : List (Pat × Expr) → Bool
  | [] => true
  | (_, b) :: rest => exprInDom dom b && exprArmsInDom dom rest
end

def StoreInDom (dom : Ident → Bool) (σ : Store) : Prop :=
  ∀ v ∈ σ, exprInDom dom v = true

def ClosedDomEnv (dom : Ident → Bool) (Φ : FunEnv) : Prop :=
  ∀ nm fd, dom nm = true → Φ nm = some fd → exprInDom dom fd.body = true

def FunEnvAgreesOn (dom : Ident → Bool) (Φ1 Φ2 : FunEnv) : Prop :=
  ∀ nm, dom nm = true → Φ2 nm = Φ1 nm

theorem zipParams_snd_subset {ps : List (Ident × Ty)} {vs : List Expr} {p : Ident × Expr}
    (hp : p ∈ zipParams ps vs) : p.2 ∈ vs := by
  unfold zipParams at hp
  exact (List.of_mem_zip hp).2

theorem exprListInDom_iff {dom : Ident → Bool} {es : List Expr} :
    exprListInDom dom es = true ↔ ∀ e ∈ es, exprInDom dom e = true := by
  induction es with
  | nil => simp [exprListInDom]
  | cons a r ih =>
    simp only [exprListInDom, Bool.and_eq_true, ih, List.mem_cons, forall_eq_or_imp]

mutual
theorem subst_exprInDom {dom : Ident → Bool} {x : Ident} {v : Expr}
    (hv : exprInDom dom v = true) :
    (e : Expr) → exprInDom dom e = true → exprInDom dom (subst x v e) = true
  | .lit _, _ | .loc _, _ | .taskRef _, _ | .syncRef _ _, _ | .trap _, _ => rfl
  | .var z, _ => by
    simp only [subst]; split
    · exact hv
    · rfl
  | .tuple es, h => by
    simp only [exprInDom] at h ⊢; exact substList_exprInDom hv es h
  | .block es, h => by
    simp only [exprInDom] at h ⊢; exact substList_exprInDom hv es h
  | .lam m ps ret body, h => by
    simp only [exprInDom] at h; simp only [subst]
    split
    · exact h
    · simp only [exprInDom]; exact subst_exprInDom hv body h
  | .apply fn args, h => by
    simp only [exprInDom, Bool.and_eq_true] at h
    simp only [subst, exprInDom, Bool.and_eq_true]
    exact ⟨subst_exprInDom hv fn h.1, substList_exprInDom hv args h.2⟩
  | .applyDir nm args, h => by
    simp only [exprInDom, Bool.and_eq_true] at h
    simp only [subst, exprInDom, Bool.and_eq_true]
    exact ⟨h.1, substList_exprInDom hv args h.2⟩
  | .bin op a b, h => by
    simp only [exprInDom, Bool.and_eq_true] at h
    simp only [subst, exprInDom, Bool.and_eq_true]
    exact ⟨subst_exprInDom hv a h.1, subst_exprInDom hv b h.2⟩
  | .un op a, h => by
    simp only [exprInDom] at h; simp only [subst, exprInDom]; exact subst_exprInDom hv a h
  | .let_ z a b, h => by
    simp only [exprInDom, Bool.and_eq_true] at h; simp only [subst]
    split
    · simp only [exprInDom, Bool.and_eq_true]; exact ⟨subst_exprInDom hv a h.1, h.2⟩
    · simp only [exprInDom, Bool.and_eq_true]; exact ⟨subst_exprInDom hv a h.1, subst_exprInDom hv b h.2⟩
  | .if_ c t e2, h => by
    simp only [exprInDom, Bool.and_eq_true] at h
    simp only [subst, exprInDom, Bool.and_eq_true]
    exact ⟨⟨subst_exprInDom hv c h.1.1, subst_exprInDom hv t h.1.2⟩, subst_exprInDom hv e2 h.2⟩
  | .while_ c b, h => by
    simp only [exprInDom, Bool.and_eq_true] at h
    simp only [subst, exprInDom, Bool.and_eq_true]
    exact ⟨subst_exprInDom hv c h.1, subst_exprInDom hv b h.2⟩
  | .match_ s arms, h => by
    simp only [exprInDom, Bool.and_eq_true] at h
    simp only [subst, exprInDom, Bool.and_eq_true]
    exact ⟨subst_exprInDom hv s h.1, substArms_exprInDom hv arms h.2⟩
  | .makeData adt tag es, h => by
    simp only [exprInDom] at h; simp only [subst, exprInDom]; exact substList_exprInDom hv es h
  | .getTag a, h => by
    simp only [exprInDom] at h; simp only [subst, exprInDom]; exact subst_exprInDom hv a h
  | .cellNew a, h => by
    simp only [exprInDom] at h; simp only [subst, exprInDom]; exact subst_exprInDom hv a h
  | .cellGet a, h => by
    simp only [exprInDom] at h; simp only [subst, exprInDom]; exact subst_exprInDom hv a h
  | .cellSet a b, h => by
    simp only [exprInDom, Bool.and_eq_true] at h
    simp only [subst, exprInDom, Bool.and_eq_true]
    exact ⟨subst_exprInDom hv a h.1, subst_exprInDom hv b h.2⟩
  | .spawn a, h => by
    simp only [exprInDom] at h; simp only [subst, exprInDom]; exact subst_exprInDom hv a h
  | .await a, h => by
    simp only [exprInDom] at h; simp only [subst, exprInDom]; exact subst_exprInDom hv a h
  | .concPrim op es, h => by
    simp only [exprInDom] at h; simp only [subst, exprInDom]; exact substList_exprInDom hv es h
termination_by e => sizeOf e

theorem substList_exprInDom {dom : Ident → Bool} {x : Ident} {v : Expr}
    (hv : exprInDom dom v = true) :
    (es : List Expr) → exprListInDom dom es = true → exprListInDom dom (substList x v es) = true
  | [], _ => rfl
  | a :: r, h => by
    simp only [exprListInDom, Bool.and_eq_true] at h
    simp only [substList, exprListInDom, Bool.and_eq_true]
    exact ⟨subst_exprInDom hv a h.1, substList_exprInDom hv r h.2⟩
termination_by es => sizeOf es

theorem substArms_exprInDom {dom : Ident → Bool} {x : Ident} {v : Expr}
    (hv : exprInDom dom v = true) :
    (arms : List (Pat × Expr)) → exprArmsInDom dom arms = true →
      exprArmsInDom dom (substArms x v arms) = true
  | [], _ => rfl
  | (p, b) :: r, h => by
    simp only [exprArmsInDom, Bool.and_eq_true] at h
    simp only [substArms, exprArmsInDom, Bool.and_eq_true]
    refine ⟨?_, substArms_exprInDom hv r h.2⟩
    split
    · exact h.1
    · exact subst_exprInDom hv b h.1
termination_by arms => sizeOf arms
end

theorem substMany_exprInDom {dom : Ident → Bool} {ρ : List (Ident × Expr)} {e : Expr}
    (hρ : ∀ p ∈ ρ, exprInDom dom p.2 = true) (he : exprInDom dom e = true) :
    exprInDom dom (substMany ρ e) = true := by
  induction ρ generalizing e with
  | nil => exact he
  | cons p rest ih =>
    exact ih (fun q hq => hρ q (List.mem_cons_of_mem _ hq))
      (subst_exprInDom (hρ p (List.mem_cons_self ..)) e he)

mutual
theorem matchPat_exprInDom {dom : Ident → Bool} :
    (p : Pat) → {v : Expr} → {env : List (Ident × Expr)} →
    exprInDom dom v = true → matchPat p v = some env →
    ∀ q ∈ env, exprInDom dom q.2 = true
  | .wild, _, _, _, hm => by simp [matchPat] at hm; subst hm; intro _ h; cases h
  | .var x, v, _, hv, hm => by
    simp [matchPat] at hm; subst hm
    intro q hq; simp at hq; subst hq; exact hv
  | .lit l1, v, _, _, hm => by
    cases v <;> simp [matchPat] at hm
    rcases hm with ⟨_, rfl⟩; intro _ h; cases h
  | .tuple ps, v, _, hv, hm => by
    cases v <;> simp [matchPat] at hm
    simp only [exprInDom] at hv
    exact matchPats_exprInDom ps hv hm
  | .ctor adt1 tag1 ps, v, _, hv, hm => by
    cases v <;> simp [matchPat] at hm
    simp only [exprInDom] at hv
    exact matchPats_exprInDom ps hv hm.2
termination_by p => sizeOf p

theorem matchPats_exprInDom {dom : Ident → Bool} :
    (ps : List Pat) → {vs : List Expr} → {env : List (Ident × Expr)} →
    exprListInDom dom vs = true → matchPats ps vs = some env →
    ∀ q ∈ env, exprInDom dom q.2 = true
  | [], vs, _, _, hm => by
    cases vs <;> simp [matchPats] at hm
    subst hm; intro _ h; cases h
  | p :: pr, vs, _, hvs, hm => by
    cases vs with
    | nil => simp [matchPats] at hm
    | cons v vr =>
      simp only [exprListInDom, Bool.and_eq_true] at hvs
      simp only [matchPats] at hm
      cases h1 : matchPat p v <;> rw [h1] at hm
      · simp at hm
      · cases h2 : matchPats pr vr <;> rw [h2] at hm
        · simp at hm
        · simp at hm; subst hm
          intro q hq
          rcases List.mem_append.mp hq with hq1 | hq2
          · exact matchPat_exprInDom p hvs.1 h1 q hq1
          · exact matchPats_exprInDom pr hvs.2 h2 q hq2
termination_by ps => sizeOf ps
end

mutual
theorem step_preserves_inDom {Δ : AdtEnv} {Φ : FunEnv} {dom : Ident → Bool}
    (hΦ : ClosedDomEnv dom Φ) {e e' : Expr} {σ σ' : Store}
    (hσ : StoreInDom dom σ) (he : exprInDom dom e = true)
    (hs : Step Δ Φ emptyPool e σ e' σ' .none) :
    exprInDom dom e' = true ∧ StoreInDom dom σ' ∧
      (∀ Φ2, FunEnvAgreesOn dom Φ Φ2 → Step Δ Φ2 emptyPool e σ e' σ' .none) := by
  cases hs with
  | tupleStep hsl =>
    simp only [exprInDom] at he
    rcases stepList_preserves_inDom hΦ hσ he hsl with ⟨he', hσ', hf⟩
    exact ⟨by simpa [exprInDom] using he', hσ', fun Φ2 ha => .tupleStep (hf Φ2 ha)⟩
  | tupleTrap htr => exact ⟨rfl, hσ, fun _ _ => .tupleTrap htr⟩
  | blockEmpty => exact ⟨rfl, hσ, fun _ _ => .blockEmpty⟩
  | blockSingle =>
    simp only [exprInDom, exprListInDom, Bool.and_true] at he
    exact ⟨he, hσ, fun _ _ => .blockSingle⟩
  | blockConsStep hs1 =>
    simp only [exprInDom, exprListInDom, Bool.and_eq_true] at he
    rcases step_preserves_inDom hΦ hσ he.1 hs1 with ⟨h1', hσ', hf⟩
    exact ⟨by simp [exprInDom, exprListInDom, h1', he.2], hσ', fun Φ2 ha => .blockConsStep (hf Φ2 ha)⟩
  | blockConsVal hv =>
    simp only [exprInDom, exprListInDom, Bool.and_eq_true] at he
    exact ⟨by simp [exprInDom, exprListInDom, he.2.1, he.2.2], hσ, fun _ _ => .blockConsVal hv⟩
  | blockConsTrap => exact ⟨rfl, hσ, fun _ _ => .blockConsTrap⟩
  | applyFn hs1 =>
    simp only [exprInDom, Bool.and_eq_true] at he
    rcases step_preserves_inDom hΦ hσ he.1 hs1 with ⟨h1', hσ', hf⟩
    exact ⟨by simp [exprInDom, h1', he.2], hσ', fun Φ2 ha => .applyFn (hf Φ2 ha)⟩
  | applyFnTrap => exact ⟨rfl, hσ, fun _ _ => .applyFnTrap⟩
  | applyArgs hv hsl =>
    simp only [exprInDom, Bool.and_eq_true] at he
    rcases stepList_preserves_inDom hΦ hσ he.2 hsl with ⟨h2', hσ', hf⟩
    exact ⟨by simp [exprInDom, he.1, h2'], hσ', fun Φ2 ha => .applyArgs hv (hf Φ2 ha)⟩
  | applyArgsTrap hv htr => exact ⟨rfl, hσ, fun _ _ => .applyArgsTrap hv htr⟩
  | @applyBeta _ ps _ _ args _ hvs hlen =>
    simp only [exprInDom, Bool.and_eq_true] at he
    have hρ : ∀ p ∈ zipParams ps args, exprInDom dom p.2 = true := by
      intro p hp
      exact exprListInDom_iff.mp he.2 p.2 (zipParams_snd_subset hp)
    exact ⟨substMany_exprInDom hρ he.1, hσ, fun _ _ => .applyBeta hvs hlen⟩
  | applyDirArgs hsl =>
    simp only [exprInDom, Bool.and_eq_true] at he
    rcases stepList_preserves_inDom hΦ hσ he.2 hsl with ⟨h2', hσ', hf⟩
    exact ⟨by simp [exprInDom, he.1, h2'], hσ', fun Φ2 ha => .applyDirArgs (hf Φ2 ha)⟩
  | applyDirTrap htr => exact ⟨rfl, hσ, fun _ _ => .applyDirTrap htr⟩
  | @applyDirBeta fn fd vs _ hfn hvs hlen =>
    simp only [exprInDom, Bool.and_eq_true] at he
    have hbody : exprInDom dom fd.body = true := hΦ fn fd he.1 hfn
    have hρ : ∀ p ∈ zipParams fd.params vs, exprInDom dom p.2 = true := by
      intro p hp
      exact exprListInDom_iff.mp he.2 p.2 (zipParams_snd_subset hp)
    refine ⟨substMany_exprInDom hρ hbody, hσ, fun Φ2 ha => ?_⟩
    have hfn2 : Φ2 fn = some fd := by rw [ha fn he.1]; exact hfn
    exact .applyDirBeta hfn2 hvs hlen
  | unStep hs1 =>
    simp only [exprInDom] at he
    rcases step_preserves_inDom hΦ hσ he hs1 with ⟨h1', hσ', hf⟩
    exact ⟨by simpa [exprInDom] using h1', hσ', fun Φ2 ha => .unStep (hf Φ2 ha)⟩
  | unTrap => exact ⟨rfl, hσ, fun _ _ => .unTrap⟩
  | unVal hev => exact ⟨rfl, hσ, fun _ _ => .unVal hev⟩
  | binLeft hs1 =>
    simp only [exprInDom, Bool.and_eq_true] at he
    rcases step_preserves_inDom hΦ hσ he.1 hs1 with ⟨h1', hσ', hf⟩
    exact ⟨by simp [exprInDom, h1', he.2], hσ', fun Φ2 ha => .binLeft (hf Φ2 ha)⟩
  | binLeftTrap => exact ⟨rfl, hσ, fun _ _ => .binLeftTrap⟩
  | binAndFalse => exact ⟨rfl, hσ, fun _ _ => .binAndFalse⟩
  | binAndTrue =>
    simp only [exprInDom, Bool.and_eq_true] at he
    exact ⟨he.2, hσ, fun _ _ => .binAndTrue⟩
  | binOrTrue => exact ⟨rfl, hσ, fun _ _ => .binOrTrue⟩
  | binOrFalse =>
    simp only [exprInDom, Bool.and_eq_true] at he
    exact ⟨he.2, hσ, fun _ _ => .binOrFalse⟩
  | binRight hna hno hv hs2 =>
    simp only [exprInDom, Bool.and_eq_true] at he
    rcases step_preserves_inDom hΦ hσ he.2 hs2 with ⟨h2', hσ', hf⟩
    exact ⟨by simp [exprInDom, he.1, h2'], hσ', fun Φ2 ha => .binRight hna hno hv (hf Φ2 ha)⟩
  | binRightTrap hna hno hv => exact ⟨rfl, hσ, fun _ _ => .binRightTrap hna hno hv⟩
  | binVal hev => exact ⟨rfl, hσ, fun _ _ => .binVal hev⟩
  | binTrap hev => exact ⟨rfl, hσ, fun _ _ => .binTrap hev⟩
  | letStep hs1 =>
    simp only [exprInDom, Bool.and_eq_true] at he
    rcases step_preserves_inDom hΦ hσ he.1 hs1 with ⟨h1', hσ', hf⟩
    exact ⟨by simp [exprInDom, h1', he.2], hσ', fun Φ2 ha => .letStep (hf Φ2 ha)⟩
  | letTrap => exact ⟨rfl, hσ, fun _ _ => .letTrap⟩
  | letVal hv =>
    simp only [exprInDom, Bool.and_eq_true] at he
    exact ⟨subst_exprInDom he.1 _ he.2, hσ, fun _ _ => .letVal hv⟩
  | ifStep hs1 =>
    simp only [exprInDom, Bool.and_eq_true] at he
    rcases step_preserves_inDom hΦ hσ he.1.1 hs1 with ⟨h1', hσ', hf⟩
    exact ⟨by simp [exprInDom, h1', he.1.2, he.2], hσ', fun Φ2 ha => .ifStep (hf Φ2 ha)⟩
  | ifTrap => exact ⟨rfl, hσ, fun _ _ => .ifTrap⟩
  | ifTrue =>
    simp only [exprInDom, Bool.and_eq_true] at he
    exact ⟨he.1.2, hσ, fun _ _ => .ifTrue⟩
  | ifFalse =>
    simp only [exprInDom, Bool.and_eq_true] at he
    exact ⟨he.2, hσ, fun _ _ => .ifFalse⟩
  | whileUnfold =>
    simp only [exprInDom, Bool.and_eq_true] at he
    exact ⟨by simp [exprInDom, exprListInDom, he.1, he.2], hσ, fun _ _ => .whileUnfold⟩
  | matchScrut hs1 =>
    simp only [exprInDom, Bool.and_eq_true] at he
    rcases step_preserves_inDom hΦ hσ he.1 hs1 with ⟨h1', hσ', hf⟩
    exact ⟨by simp [exprInDom, h1', he.2], hσ', fun Φ2 ha => .matchScrut (hf Φ2 ha)⟩
  | matchScrutTrap => exact ⟨rfl, hσ, fun _ _ => .matchScrutTrap⟩
  | matchEmpty hv => exact ⟨rfl, hσ, fun _ _ => .matchEmpty hv⟩
  | @matchHit _ p _ _ _ _ hv hm =>
    simp only [exprInDom, exprArmsInDom, Bool.and_eq_true] at he
    exact ⟨substMany_exprInDom (matchPat_exprInDom p he.1 hm) he.2.1, hσ, fun _ _ => .matchHit hv hm⟩
  | matchMiss hv hm =>
    simp only [exprInDom, exprArmsInDom, Bool.and_eq_true] at he
    exact ⟨by simp [exprInDom, he.1, he.2.2], hσ, fun _ _ => .matchMiss hv hm⟩
  | makeDataStep hsl =>
    simp only [exprInDom] at he
    rcases stepList_preserves_inDom hΦ hσ he hsl with ⟨he', hσ', hf⟩
    exact ⟨by simpa [exprInDom] using he', hσ', fun Φ2 ha => .makeDataStep (hf Φ2 ha)⟩
  | makeDataTrap htr => exact ⟨rfl, hσ, fun _ _ => .makeDataTrap htr⟩
  | getTagStep hs1 =>
    simp only [exprInDom] at he
    rcases step_preserves_inDom hΦ hσ he hs1 with ⟨h1', hσ', hf⟩
    exact ⟨by simpa [exprInDom] using h1', hσ', fun Φ2 ha => .getTagStep (hf Φ2 ha)⟩
  | getTagTrap => exact ⟨rfl, hσ, fun _ _ => .getTagTrap⟩
  | getTagVal hvs => exact ⟨rfl, hσ, fun _ _ => .getTagVal hvs⟩
  | cellNewStep hs1 =>
    simp only [exprInDom] at he
    rcases step_preserves_inDom hΦ hσ he hs1 with ⟨h1', hσ', hf⟩
    exact ⟨by simpa [exprInDom] using h1', hσ', fun Φ2 ha => .cellNewStep (hf Φ2 ha)⟩
  | cellNewTrap => exact ⟨rfl, hσ, fun _ _ => .cellNewTrap⟩
  | @cellNewVal v _ hv =>
    simp only [exprInDom] at he
    have hσ' : StoreInDom dom (σ ++ [v]) := by
      intro w hw; rcases List.mem_append.mp hw with h1 | h2
      · exact hσ w h1
      · simp at h2; subst h2; exact he
    exact ⟨rfl, hσ', fun _ _ => .cellNewVal hv⟩
  | cellGetStep hs1 =>
    simp only [exprInDom] at he
    rcases step_preserves_inDom hΦ hσ he hs1 with ⟨h1', hσ', hf⟩
    exact ⟨by simpa [exprInDom] using h1', hσ', fun Φ2 ha => .cellGetStep (hf Φ2 ha)⟩
  | cellGetTrap => exact ⟨rfl, hσ, fun _ _ => .cellGetTrap⟩
  | cellGetVal hl =>
    exact ⟨hσ _ (List.mem_of_getElem? hl), hσ, fun _ _ => .cellGetVal hl⟩
  | cellSetLeft hs1 =>
    simp only [exprInDom, Bool.and_eq_true] at he
    rcases step_preserves_inDom hΦ hσ he.1 hs1 with ⟨h1', hσ', hf⟩
    exact ⟨by simp [exprInDom, h1', he.2], hσ', fun Φ2 ha => .cellSetLeft (hf Φ2 ha)⟩
  | cellSetLeftTrap => exact ⟨rfl, hσ, fun _ _ => .cellSetLeftTrap⟩
  | cellSetRight hv hs2 =>
    simp only [exprInDom, Bool.and_eq_true] at he
    rcases step_preserves_inDom hΦ hσ he.2 hs2 with ⟨h2', hσ', hf⟩
    exact ⟨by simp [exprInDom, he.1, h2'], hσ', fun Φ2 ha => .cellSetRight hv (hf Φ2 ha)⟩
  | cellSetRightTrap hv => exact ⟨rfl, hσ, fun _ _ => .cellSetRightTrap hv⟩
  | @cellSetVal l v _ hlt hv =>
    simp only [exprInDom, Bool.and_eq_true] at he
    have hσ' : StoreInDom dom (σ.set l v) := by
      intro w hw
      rcases List.mem_or_eq_of_mem_set hw with h1 | rfl
      · exact hσ w h1
      · exact he.2
    exact ⟨rfl, hσ', fun _ _ => .cellSetVal hlt hv⟩
  | spawnStep hs1 =>
    simp only [exprInDom] at he
    rcases step_preserves_inDom hΦ hσ he hs1 with ⟨h1', hσ', hf⟩
    exact ⟨by simpa [exprInDom] using h1', hσ', fun Φ2 ha => .spawnStep (hf Φ2 ha)⟩
  | spawnTrap => exact ⟨rfl, hσ, fun _ _ => .spawnTrap⟩
  | awaitStep hs1 =>
    simp only [exprInDom] at he
    rcases step_preserves_inDom hΦ hσ he hs1 with ⟨h1', hσ', hf⟩
    exact ⟨by simpa [exprInDom] using h1', hσ', fun Φ2 ha => .awaitStep (hf Φ2 ha)⟩
  | awaitTrap => exact ⟨rfl, hσ, fun _ _ => .awaitTrap⟩
  | awaitVal h _ | awaitTaskTrap h => simp [emptyPool] at h
  | concPrimArgs hsl =>
    simp only [exprInDom] at he
    rcases stepList_preserves_inDom hΦ hσ he hsl with ⟨he', hσ', hf⟩
    exact ⟨by simpa [exprInDom] using he', hσ', fun Φ2 ha => .concPrimArgs (hf Φ2 ha)⟩
  | concPrimTrap htr => exact ⟨rfl, hσ, fun _ _ => .concPrimTrap htr⟩
  | concPrimVal hc => exact False.elim (stepConcPrim_emptyPool_none_false hc)
termination_by sizeOf e

theorem stepList_preserves_inDom {Δ : AdtEnv} {Φ : FunEnv} {dom : Ident → Bool}
    (hΦ : ClosedDomEnv dom Φ) {es es' : List Expr} {σ σ' : Store}
    (hσ : StoreInDom dom σ) (hes : exprListInDom dom es = true)
    (hsl : StepList Δ Φ emptyPool es σ es' σ' .none) :
    exprListInDom dom es' = true ∧ StoreInDom dom σ' ∧
      (∀ Φ2, FunEnvAgreesOn dom Φ Φ2 → StepList Δ Φ2 emptyPool es σ es' σ' .none) := by
  cases hsl with
  | head hs =>
    simp only [exprListInDom, Bool.and_eq_true] at hes
    rcases step_preserves_inDom hΦ hσ hes.1 hs with ⟨h1', hσ', hf⟩
    exact ⟨by simp [exprListInDom, h1', hes.2], hσ', fun Φ2 ha => .head (hf Φ2 ha)⟩
  | tail hv hsl' =>
    simp only [exprListInDom, Bool.and_eq_true] at hes
    rcases stepList_preserves_inDom hΦ hσ hes.2 hsl' with ⟨h2', hσ', hf⟩
    exact ⟨by simp [exprListInDom, hes.1, h2'], hσ', fun Φ2 ha => .tail hv (hf Φ2 ha)⟩
termination_by sizeOf es
end

theorem steps_funEnv_agree_forward {Δ : AdtEnv} {Φ1 Φ2 : FunEnv} {dom : Ident → Bool}
    (hagree : FunEnvAgreesOn dom Φ1 Φ2) (hΦ1 : ClosedDomEnv dom Φ1)
    {e e' : Expr} {σ σ' : Store}
    (hσ : StoreInDom dom σ) (he : exprInDom dom e = true)
    (hsteps : Steps Δ Φ1 e σ e' σ') :
    Steps Δ Φ2 e σ e' σ' ∧ exprInDom dom e' = true ∧ StoreInDom dom σ' := by
  induction hsteps with
  | refl => exact ⟨.refl _ _, he, hσ⟩
  | trans hs _ ih =>
    rcases step_preserves_inDom hΦ1 hσ he hs with ⟨he1, hσ1, hf⟩
    rcases ih hσ1 he1 with ⟨hs2_rest, he', hσ'⟩
    exact ⟨.trans (hf Φ2 hagree) hs2_rest, he', hσ'⟩

/-- **Soundness of Fresh Function-Table Registration (`Φ ↦ Φ'`)**:
    Adding newly synthesized `$flat$` / `$spec$` functions outside `dom` leaves all
    evaluations of expressions in `dom` completely unchanged in both directions. -/
theorem steps_funEnv_agree_iff {Δ : AdtEnv} {Φ1 Φ2 : FunEnv} {dom : Ident → Bool}
    (hagree : FunEnvAgreesOn dom Φ1 Φ2) (hΦ1 : ClosedDomEnv dom Φ1)
    {e out : Expr} {σ σ' : Store}
    (hσ : StoreInDom dom σ) (he : exprInDom dom e = true) :
    Steps Δ Φ1 e σ out σ' ↔ Steps Δ Φ2 e σ out σ' := by
  have hagree_sym : FunEnvAgreesOn dom Φ2 Φ1 := fun nm h => (hagree nm h).symm
  have hΦ2 : ClosedDomEnv dom Φ2 := by
    intro nm fd hd hfd
    rw [hagree nm hd] at hfd
    exact hΦ1 nm fd hd hfd
  constructor
  · exact fun h => (steps_funEnv_agree_forward hagree hΦ1 hσ he h).1
  · exact fun h => (steps_funEnv_agree_forward hagree_sym hΦ2 hσ he h).1

/- 7.2 `coTermIsPure` (`src/core.gsa:5363-5376`) Open-Scope Dead-`let` Elimination &
   Pipeline-Wide Monotonic Fresh Binder Allocation (`allocFreshCoreBinder`, `src/core.gsa:4634,7490,7740`). -/
mutual
def coTermIsPureB : Expr → Bool
  | .lit _ => true
  | .var _ => true
  | .lam _ _ _ body => coTermIsPureB body
  | .tuple es => coTermListIsPureB es
  | .makeData _ _ es => coTermListIsPureB es
  | _ => false

def coTermListIsPureB : List Expr → Bool
  | [] => true
  | e :: es => coTermIsPureB e && coTermListIsPureB es
end

theorem substMany_lam_exists (ρ : List (Ident × Expr)) (m : Mode)
    (ps : List (Ident × Ty)) (ret : Ty) (body : Expr) :
    ∃ body', substMany ρ (.lam m ps ret body) = .lam m ps ret body' := by
  induction ρ generalizing body with
  | nil => exact ⟨body, rfl⟩
  | cons p rest ih =>
    simp only [substMany, subst]
    split
    · exact ih body
    · exact ih (subst p.1 p.2 body)

mutual
theorem coTermIsPureB_substMany_isValue {ρ : List (Ident × Expr)}
    (hρVal : ∀ p ∈ ρ, IsValue p.2) (hρCl : ∀ p ∈ ρ, freeVars p.2 = []) :
    (e : Expr) → coTermIsPureB e = true →
      (∀ z ∈ freeVars e, z ∈ ρ.map Prod.fst) → IsValue (substMany ρ e)
  | .lit l, _, _ => by
    have hid : ∀ ρ', substMany ρ' (.lit l) = .lit l := fun ρ' => by
      induction ρ' with | nil => rfl | cons _ _ ih => exact ih
    rw [hid]; exact .lit l
  | .var x, _, hfv => by
    have hx : x ∈ ρ.map Prod.fst := hfv x (by simp [freeVars])
    induction ρ with
    | nil => cases hx
    | cons p rest ih =>
      rcases p with ⟨y, w⟩
      simp only [substMany, subst]
      cases hxy : (x == y)
      · simp only [Bool.false_eq_true, ↓reduceIte]
        simp only [List.map_cons, List.mem_cons] at hx
        rcases hx with rfl | hrest
        · rw [beq_self_eq_true] at hxy; cases hxy
        · exact ih (fun q hq => hρVal q (List.mem_cons_of_mem _ hq))
            (fun q hq => hρCl q (List.mem_cons_of_mem _ hq))
            (fun z hz => by simp [freeVars] at hz; subst hz; exact hrest)
            hrest
      · simp only [↓reduceIte]
        rw [substMany_closed_val_id rest (hρCl (y, w) (List.mem_cons_self ..))]
        exact hρVal (y, w) (List.mem_cons_self ..)
  | .lam m ps ret body, _, _ => by
    rcases substMany_lam_exists ρ m ps ret body with ⟨body', heq⟩
    rw [heq]; exact .lam _ _ _ _
  | .tuple es, hp, hfv => by
    rcases substMany_map_helper ρ with ⟨ht, _, _, _, _⟩
    rw [ht]
    exact .tuple (coTermListIsPureB_substMany_isValue hρVal hρCl es hp hfv)
  | .makeData adt tag es, hp, hfv => by
    rcases substMany_map_helper ρ with ⟨_, _, _, _, hm⟩
    rw [hm]
    exact .makeData adt tag (coTermListIsPureB_substMany_isValue hρVal hρCl es hp hfv)
  | .loc _, hp, _ | .taskRef _, hp, _ | .syncRef _ _, hp, _ | .block _, hp, _
  | .apply _ _, hp, _ | .applyDir _ _, hp, _ | .bin _ _ _, hp, _ | .un _ _, hp, _
  | .let_ _ _ _, hp, _ | .if_ _ _ _, hp, _ | .while_ _ _, hp, _ | .match_ _ _, hp, _
  | .getTag _, hp, _ | .cellNew _, hp, _ | .cellGet _, hp, _ | .cellSet _ _, hp, _
  | .spawn _, hp, _ | .await _, hp, _ | .concPrim _ _, hp, _ | .trap _, hp, _ => by
    simp [coTermIsPureB] at hp
termination_by e => sizeOf e

theorem coTermListIsPureB_substMany_isValue {ρ : List (Ident × Expr)}
    (hρVal : ∀ p ∈ ρ, IsValue p.2) (hρCl : ∀ p ∈ ρ, freeVars p.2 = []) :
    (es : List Expr) → coTermListIsPureB es = true →
      (∀ z ∈ freeVarsList es, z ∈ ρ.map Prod.fst) →
      ∀ v ∈ es.map (substMany ρ), IsValue v
  | [], _, _ => fun _ h => by cases h
  | e :: r, hp, hfv => by
    simp only [coTermListIsPureB, Bool.and_eq_true] at hp
    intro v hv
    rcases List.mem_cons.mp hv with rfl | hvr
    · exact coTermIsPureB_substMany_isValue hρVal hρCl e hp.1
        (fun z hz => hfv z (by simp [freeVarsList, hz]))
    · exact coTermListIsPureB_substMany_isValue hρVal hρCl r hp.2
        (fun z hz => hfv z (by simp [freeVarsList, hz])) v hvr
termination_by es => sizeOf es
end

/-- **Soundness of `coFinishLetWithDeadElim` (`src/core.gsa:7078`) on Open `coTermIsPure` Terms**:
    In any closing caller value environment `ρ`, eliminating `let x = rhs; body` when
    `coTermIsPureB rhs = true` (covering literals, local variables, closures, and recursive
    pure tuples/ADTs) and `x ∉ freeVars body` preserves exact `ObsEquiv`. -/
theorem coFinishLetWithDeadElim_open_obsEquiv (Δ : AdtEnv) (Φ : FunEnv)
    {ρ : List (Ident × Expr)} {x : Ident} {rhs body : Expr}
    (hpure : coTermIsPureB rhs = true)
    (hx_body : x ∉ freeVars body)
    (hx_env : x ∉ ρ.map Prod.fst)
    (hrhs_scope : ∀ z ∈ freeVars rhs, z ∈ ρ.map Prod.fst)
    (hρVal : ∀ p ∈ ρ, IsValue p.2)
    (hρCl : ∀ p ∈ ρ, freeVars p.2 = []) :
    ObsEquiv Δ Φ Φ (substMany ρ (.let_ x rhs body)) (substMany ρ body) := by
  rw [substMany_let_not_mem ρ hx_env]
  have hv_rhs : IsValue (substMany ρ rhs) :=
    coTermIsPureB_substMany_isValue hρVal hρCl rhs hpure hrhs_scope
  have hx_sub_body : x ∉ freeVars (substMany ρ body) := by
    intro hmem
    exact hx_body (substMany_freeVars_subset ρ hρCl body x hmem).2
  exact dead_val_let_obsEquiv Δ Φ hv_rhs hx_sub_body

/-- Abstract pipeline-wide monotonic fresh binder batch allocator (`allocFreshCoreBinder`). -/
def allocFreshBatch (enc : Nat → String → Ident) (startId : Nat) : List String → List Ident
  | [] => []
  | h :: rest => enc startId h :: allocFreshBatch enc (startId + 1) rest

theorem allocFreshBatch_mem_range {enc : Nat → String → Ident} {startId : Nat}
    {hints : List String} {x : Ident}
    (hmem : x ∈ allocFreshBatch enc startId hints) :
    ∃ i h, startId ≤ i ∧ i < startId + hints.length ∧ x = enc i h := by
  induction hints generalizing startId with
  | nil => cases hmem
  | cons h0 rest ih =>
    rcases List.mem_cons.mp hmem with rfl | hr
    · exact ⟨startId, h0, Nat.le_refl _, by simp only [List.length_cons]; omega, rfl⟩
    · rcases ih hr with ⟨i, h, hlo, hhi, heq⟩
      exact ⟨i, h, by omega, by simp only [List.length_cons]; omega, heq⟩

/-- **Pipeline-Wide Shared Counter Disjointness (`allocFreshCoreBinder`, `src/core.gsa:4634,7490,7740`)**:
    Given an ID-injective binder encoder `enc` (`enc i h1 = enc j h2 → i = j`), sharing one
    monotonic counter across Pass 1 (`c0`), Pass 2 (`c1 ≥ c0 + hints1.length`), and Pass 3
    (`c2 ≥ c1 + hints2.length`) guarantees `Nodup` within each pass and pairwise disjointness
    across all passes. -/
theorem pipeline_shared_counter_disjoint {enc : Nat → String → Ident}
    (hinj : ∀ i j h1 h2, enc i h1 = enc j h2 → i = j)
    {c0 c1 c2 : Nat} {hints1 hints2 hints3 : List String}
    (hc1 : c0 + hints1.length ≤ c1) (hc2 : c1 + hints2.length ≤ c2) :
    (allocFreshBatch enc c0 hints1).Nodup ∧
    (allocFreshBatch enc c1 hints2).Nodup ∧
    (allocFreshBatch enc c2 hints3).Nodup ∧
    (∀ x ∈ allocFreshBatch enc c0 hints1, x ∉ allocFreshBatch enc c1 hints2) ∧
    (∀ x ∈ allocFreshBatch enc c0 hints1, x ∉ allocFreshBatch enc c2 hints3) ∧
    (∀ x ∈ allocFreshBatch enc c1 hints2, x ∉ allocFreshBatch enc c2 hints3) := by
  have hnodup : ∀ start (hs : List String), (allocFreshBatch enc start hs).Nodup := by
    intro start hs
    induction hs generalizing start with
    | nil => exact List.nodup_nil
    | cons h0 rest ih =>
      refine List.nodup_cons.mpr ⟨?_, ih (start + 1)⟩
      intro hm
      rcases allocFreshBatch_mem_range hm with ⟨i, h', hlo, _, heq⟩
      have := hinj start i h0 h' heq
      omega
  refine ⟨hnodup c0 hints1, hnodup c1 hints2, hnodup c2 hints3, ?_, ?_, ?_⟩
  · intro x hx1 hx2
    rcases allocFreshBatch_mem_range hx1 with ⟨i, h1, _, hi, rfl⟩
    rcases allocFreshBatch_mem_range hx2 with ⟨j, h2, hj, _, heq⟩
    have := hinj i j h1 h2 heq; omega
  · intro x hx1 hx3
    rcases allocFreshBatch_mem_range hx1 with ⟨i, h1, _, hi, rfl⟩
    rcases allocFreshBatch_mem_range hx3 with ⟨j, h3, hj, _, heq⟩
    have := hinj i j h1 h3 heq; omega
  · intro x hx2 hx3
    rcases allocFreshBatch_mem_range hx2 with ⟨i, h2, _, hi, rfl⟩
    rcases allocFreshBatch_mem_range hx3 with ⟨j, h3, hj, _, heq⟩
    have := hinj i j h2 h3 heq; omega

/-- Multi-parameter `let` wrapper emitted by `coBuildCallArgsInline` / `coWrapLetBindings`. -/
def wrapLetParams : List (Ident × Ty) → List Expr → Expr → Expr
  | (p, _) :: pr, a :: ar, body => .let_ p a (wrapLetParams pr ar body)
  | _, _, body => body

theorem subst_wrapLetParams_disjoint (x : Ident) (v : Expr)
    (ps : List (Ident × Ty)) (args : List Expr) (body : Expr)
    (hx_ps : x ∉ ps.map Prod.fst) (hx_args : ∀ a ∈ args, x ∉ freeVars a) :
    subst x v (wrapLetParams ps args body) =
      wrapLetParams ps args (subst x v body) := by
  induction ps generalizing args with
  | nil => rfl
  | cons p pr ih =>
    cases args with
    | nil => rfl
    | cons a ar =>
      simp only [List.map_cons, List.mem_cons, not_or] at hx_ps
      have hpx : (p.1 == x) = false := beq_false_of_ne (Ne.symm hx_ps.1)
      have ha : x ∉ freeVars a := hx_args a (List.mem_cons_self ..)
      have har : ∀ b ∈ ar, x ∉ freeVars b := fun b hb => hx_args b (List.mem_cons_of_mem _ hb)
      simp [wrapLetParams, subst, hpx, subst_not_mem_freeVars a ha, ih ar hx_ps.2 har]

/-- **Soundness of `n`-Parameter Fresh `let` Wrapping (`coBuildCallArgsInline`, `coWrapLetBindings`)**. -/
theorem wrapLetParams_obsEquiv_substMany (Δ : AdtEnv) (Φ : FunEnv)
    (ps : List (Ident × Ty)) (vals : List Expr) (body : Expr)
    (hnodup : (ps.map Prod.fst).Nodup) (hlen : vals.length = ps.length)
    (hvals : ∀ v ∈ vals, IsValue v) (hcl : ∀ v ∈ vals, freeVars v = []) :
    ObsEquiv Δ Φ Φ (wrapLetParams ps vals body) (substMany (zipParams ps vals) body) := by
  induction ps generalizing vals body with
  | nil =>
    cases vals <;> simp [wrapLetParams, zipParams, substMany] at hlen ⊢
    exact ObsEquiv.refl _ _ _
  | cons p pr ih =>
    cases vals with
    | nil => simp at hlen
    | cons v vr =>
      simp only [List.length_cons, Nat.succ.injEq] at hlen
      simp only [List.map_cons] at hnodup
      rcases List.nodup_cons.mp hnodup with ⟨hp_pr, hnodup_pr⟩
      have hv : IsValue v := hvals v (List.mem_cons_self ..)
      have hvr : ∀ w ∈ vr, IsValue w := fun w hw => hvals w (List.mem_cons_of_mem _ hw)
      have hvr_cl : ∀ w ∈ vr, freeVars w = [] := fun w hw => hcl w (List.mem_cons_of_mem _ hw)
      have hp_vr : ∀ w ∈ vr, p.1 ∉ freeVars w := fun w hw => by simp [hvr_cl w hw]
      have hstep : ObsEquiv Δ Φ Φ
          (.let_ p.1 v (wrapLetParams pr vr body))
          (wrapLetParams pr vr (subst p.1 v body)) := by
        apply obsEquiv_of_det_step
        intro σ
        have hs := Step.letVal (Δ := Δ) (Φ := Φ) (pool := emptyPool)
          (x := p.1) (e2 := wrapLetParams pr vr body) (σ := σ) hv
        rwa [subst_wrapLetParams_disjoint p.1 v pr vr body hp_pr hp_vr] at hs
      exact ObsEquiv.trans hstep (ih vr (subst p.1 v body) hnodup_pr hlen hvr hvr_cl)

/- 7.3 Selective Mask + Preserved Suffix ANF Lifting (`coFloatSelectedArgs`, `src/core.gsa:6212-6249`):
   skips `coIsSimpleTerm` items in `0..lastIdx` and leaves the entire suffix `idx > lastIdx` untouched. -/
inductive SelectiveArg where
  | keepSimple (e : Expr)
  | floatLet (x : Ident) (e : Expr)

def selectiveOrigArgs : List SelectiveArg → List Expr
  | [] => []
  | .keepSimple e :: r => e :: selectiveOrigArgs r
  | .floatLet _ e :: r => e :: selectiveOrigArgs r

def selectiveOutArgs : List SelectiveArg → List Expr
  | [] => []
  | .keepSimple e :: r => e :: selectiveOutArgs r
  | .floatLet x _ :: r => .var x :: selectiveOutArgs r

def selectiveBinders : List SelectiveArg → List Ident
  | [] => []
  | .keepSimple _ :: r => selectiveBinders r
  | .floatLet x _ :: r => x :: selectiveBinders r

def wrapSelectiveLets : List SelectiveArg → Expr → Expr
  | [], core => core
  | .keepSimple _ :: r, core => wrapSelectiveLets r core
  | .floatLet x e :: r, core => .let_ x e (wrapSelectiveLets r core)

def selectiveAnfDir (plan : List SelectiveArg) (suffix : List Expr) (fn : Ident) : Expr :=
  wrapSelectiveLets plan (.applyDir fn (selectiveOutArgs plan ++ suffix))

def SelectivePlanWF (plan : List SelectiveArg) : Prop :=
  (∀ e, SelectiveArg.keepSimple e ∈ plan → IsValue e ∧ freeVars e = []) ∧
  (∀ x e, SelectiveArg.floatLet x e ∈ plan → freeVars e = [])

theorem subst_wrapSelectiveLets_disjoint (x : Ident) (v : Expr)
    (plan : List SelectiveArg) (core : Expr)
    (hx_b : x ∉ selectiveBinders plan)
    (hx_e : ∀ a ∈ selectiveOrigArgs plan, x ∉ freeVars a) :
    subst x v (wrapSelectiveLets plan core) = wrapSelectiveLets plan (subst x v core) := by
  induction plan with
  | nil => rfl
  | cons item r ih =>
    cases item with
    | keepSimple s =>
      exact ih hx_b (fun a ha => hx_e a (List.mem_cons_of_mem _ ha))
    | floatLet y e =>
      simp only [selectiveBinders, List.mem_cons, not_or] at hx_b
      have hyx : (y == x) = false := beq_false_of_ne (Ne.symm hx_b.1)
      have he : x ∉ freeVars e := hx_e e (List.mem_cons_self ..)
      have hr : ∀ a ∈ selectiveOrigArgs r, x ∉ freeVars a :=
        fun a ha => hx_e a (List.mem_cons_of_mem _ ha)
      simp [wrapSelectiveLets, subst, hyx, subst_not_mem_freeVars e he, ih hx_b.2 hr]

theorem substList_selectiveOutArgs_disjoint (x : Ident) (v : Expr)
    (plan : List SelectiveArg)
    (hx_b : x ∉ selectiveBinders plan)
    (hsimple : ∀ e, SelectiveArg.keepSimple e ∈ plan → freeVars e = []) :
    substList x v (selectiveOutArgs plan) = selectiveOutArgs plan := by
  induction plan with
  | nil => rfl
  | cons item r ih =>
    cases item with
    | keepSimple e =>
      have he : x ∉ freeVars e := by simp [hsimple e (List.mem_cons_self ..)]
      simp [selectiveOutArgs, substList, subst_not_mem_freeVars e he,
        ih hx_b (fun s hs => hsimple s (List.mem_cons_of_mem _ hs))]
    | floatLet y e =>
      simp only [selectiveBinders, List.mem_cons, not_or] at hx_b
      have hyx : (y == x) = false := beq_false_of_ne (Ne.symm hx_b.1)
      simp [selectiveOutArgs, substList, subst, hyx,
        ih hx_b.2 (fun s hs => hsimple s (List.mem_cons_of_mem _ hs))]

theorem substList_disjoint_id (x : Ident) (v : Expr) (es : List Expr)
    (h : ∀ s ∈ es, x ∉ freeVars s) : substList x v es = es := by
  induction es with
  | nil => rfl
  | cons s sr ih =>
    simp [substList, subst_not_mem_freeVars s (h s (List.mem_cons_self ..)),
      ih (fun u hu => h u (List.mem_cons_of_mem _ hu))]

theorem selectiveOrigArgs_closed {plan : List SelectiveArg} (hwf : SelectivePlanWF plan) :
    ∀ a ∈ selectiveOrigArgs plan, freeVars a = [] := by
  induction plan with
  | nil => intro _ h; cases h
  | cons it rr ihr =>
    have hwf_r : SelectivePlanWF rr :=
      ⟨fun u hu => hwf.1 u (List.mem_cons_of_mem _ hu),
       fun z ez hz => hwf.2 z ez (List.mem_cons_of_mem _ hz)⟩
    cases it with
    | keepSimple s =>
      intro a ha
      simp only [selectiveOrigArgs, List.mem_cons] at ha
      rcases ha with rfl | har
      · exact (hwf.1 a (List.mem_cons_self ..)).2
      · exact ihr hwf_r a har
    | floatLet z ez =>
      intro a ha
      simp only [selectiveOrigArgs, List.mem_cons] at ha
      rcases ha with rfl | har
      · exact hwf.2 z a (List.mem_cons_self ..)
      · exact ihr hwf_r a har

private theorem selectiveAnfDir_aux_iff {Δ : AdtEnv} {Φ : FunEnv}
    (hΦ : ClosedFunEnv Φ) {plan : List SelectiveArg} {vs suffix : List Expr} {fn : Ident}
    {σ σ' : Store} {out : Expr}
    (hσ : ClosedStore σ) (hout : IsTerminal out)
    (hnodup : (selectiveBinders plan).Nodup)
    (hwf : SelectivePlanWF plan)
    (hsuf_disj : ∀ x ∈ selectiveBinders plan, ∀ s ∈ suffix, x ∉ freeVars s)
    (hvs_val : ∀ v ∈ vs, IsValue v) (hvs_cl : ∀ v ∈ vs, freeVars v = []) :
    Steps Δ Φ (wrapSelectiveLets plan (.applyDir fn (vs ++ (selectiveOutArgs plan ++ suffix)))) σ out σ' ↔
      Steps Δ Φ (.applyDir fn (vs ++ (selectiveOrigArgs plan ++ suffix))) σ out σ' := by
  induction plan generalizing vs σ with
  | nil => simp [wrapSelectiveLets, selectiveOutArgs, selectiveOrigArgs]
  | cons item r ih =>
    rcases hwf with ⟨hkeep, hfloat⟩
    have hwf_r : SelectivePlanWF r :=
      ⟨fun s hs => hkeep s (List.mem_cons_of_mem _ hs),
       fun y ey hy => hfloat y ey (List.mem_cons_of_mem _ hy)⟩
    cases item with
    | keepSimple s =>
      rcases hkeep s (List.mem_cons_self ..) with ⟨hs_val, hs_cl⟩
      have hvs_val' : ∀ w ∈ vs ++ [s], IsValue w := by
        intro w hw; rcases List.mem_append.mp hw with h1 | h2
        · exact hvs_val w h1
        · simp at h2; subst h2; exact hs_val
      have hvs_cl' : ∀ w ∈ vs ++ [s], freeVars w = [] := by
        intro w hw; rcases List.mem_append.mp hw with h1 | h2
        · exact hvs_cl w h1
        · simp at h2; subst h2; exact hs_cl
      simpa [wrapSelectiveLets, selectiveOutArgs, selectiveOrigArgs, List.append_assoc] using
        ih hσ hnodup hwf_r hsuf_disj hvs_val' hvs_cl'
    | floatLet x e =>
      simp only [selectiveBinders] at hnodup
      rcases List.nodup_cons.mp hnodup with ⟨hx_r, hnodup_r⟩
      have he_cl : freeVars e = [] := hfloat x e (List.mem_cons_self ..)
      have hx_orig_r : ∀ a ∈ selectiveOrigArgs r, x ∉ freeVars a :=
        fun a ha => by rw [selectiveOrigArgs_closed hwf_r a ha]; simp
      have hsub_suf : ∀ v, substList x v suffix = suffix :=
        fun v => substList_disjoint_id x v suffix (fun s hs => hsuf_disj x (List.mem_cons_self ..) s hs)
      have hsub_core : ∀ v,
          subst x v (wrapSelectiveLets r (.applyDir fn (vs ++ Expr.var x :: (selectiveOutArgs r ++ suffix)))) =
            wrapSelectiveLets r (.applyDir fn ((vs ++ [v]) ++ (selectiveOutArgs r ++ suffix))) := by
        intro v
        rw [subst_wrapSelectiveLets_disjoint x v r _ hx_r hx_orig_r]
        congr 1
        simp only [subst]
        have hsplit : vs ++ Expr.var x :: (selectiveOutArgs r ++ suffix) =
            (vs ++ [Expr.var x]) ++ (selectiveOutArgs r ++ suffix) := by simp
        rw [hsplit, substList_append_eq, substList_closed_append_self x v vs hvs_cl,
            substList_append_eq, substList_selectiveOutArgs_disjoint x v r hx_r (fun s hs => (hwf_r.1 s hs).2),
            hsub_suf v]
      simp only [wrapSelectiveLets, selectiveOrigArgs, selectiveOutArgs, List.cons_append]
      rw [steps_let_terminal_iff hout, steps_applyDir_next_arg_iff hout hvs_val]
      apply or_congr Iff.rfl
      have hsuf_r : ∀ y ∈ selectiveBinders r, ∀ s ∈ suffix, y ∉ freeVars s :=
        fun y hy => hsuf_disj y (List.mem_cons_of_mem _ hy)
      constructor
      · rintro ⟨v, σ1, hv, hs_v, hs_rest⟩
        rcases steps_preserves_closed hΦ hσ he_cl hs_v with ⟨hv_cl, hσ1⟩
        rw [hsub_core v] at hs_rest
        have hvs_val' : ∀ w ∈ vs ++ [v], IsValue w := by
          intro w hw; rcases List.mem_append.mp hw with h1 | h2
          · exact hvs_val w h1
          · simp at h2; subst h2; exact hv
        have hvs_cl' : ∀ w ∈ vs ++ [v], freeVars w = [] := by
          intro w hw; rcases List.mem_append.mp hw with h1 | h2
          · exact hvs_cl w h1
          · simp at h2; subst h2; exact hv_cl
        exact ⟨v, σ1, hv, hs_v, (ih hσ1 hnodup_r hwf_r hsuf_r hvs_val' hvs_cl').mp hs_rest⟩
      · rintro ⟨v, σ1, hv, hs_v, hs_rest⟩
        rcases steps_preserves_closed hΦ hσ he_cl hs_v with ⟨hv_cl, hσ1⟩
        have hvs_val' : ∀ w ∈ vs ++ [v], IsValue w := by
          intro w hw; rcases List.mem_append.mp hw with h1 | h2
          · exact hvs_val w h1
          · simp at h2; subst h2; exact hv
        have hvs_cl' : ∀ w ∈ vs ++ [v], freeVars w = [] := by
          intro w hw; rcases List.mem_append.mp hw with h1 | h2
          · exact hvs_cl w h1
          · simp at h2; subst h2; exact hv_cl
        refine ⟨v, σ1, hv, hs_v, ?_⟩
        rw [hsub_core v]
        exact (ih hσ1 hnodup_r hwf_r hsuf_r hvs_val' hvs_cl').mpr hs_rest

/-- **Soundness of Selective Mask + Preserved Suffix ANF Argument Lifting (`coFloatSelectedArgs` on `TmApplyDir`)**:
    Matches `src/core.gsa:6212-6249` directly: skips simple value items in `0..lastIdx`,
    lifts non-simple items in `0..lastIdx` left-to-right, and leaves `suffix` (`idx > lastIdx`) untouched! -/
theorem selectiveAnfDir_obsEquiv {Δ : AdtEnv} {Φ : FunEnv}
    (hΦ : ClosedFunEnv Φ) {plan : List SelectiveArg} {suffix : List Expr} {fn : Ident}
    {σ σ' : Store} {out : Expr}
    (hσ : ClosedStore σ) (hout : IsTerminal out)
    (hnodup : (selectiveBinders plan).Nodup)
    (hwf : SelectivePlanWF plan)
    (hsuf_disj : ∀ x ∈ selectiveBinders plan, ∀ s ∈ suffix, x ∉ freeVars s) :
    Steps Δ Φ (selectiveAnfDir plan suffix fn) σ out σ' ↔
      Steps Δ Φ (.applyDir fn (selectiveOrigArgs plan ++ suffix)) σ out σ' := by
  simpa [selectiveAnfDir] using
    selectiveAnfDir_aux_iff (vs := []) hΦ hσ hout hnodup hwf hsuf_disj
      (fun _ h => by cases h) (fun _ h => by cases h)

def substSelectivePlan (ρ : List (Ident × Expr)) : List SelectiveArg → List SelectiveArg
  | [] => []
  | .keepSimple e :: r => .keepSimple (substMany ρ e) :: substSelectivePlan ρ r
  | .floatLet x e :: r => .floatLet x (substMany ρ e) :: substSelectivePlan ρ r

theorem selectiveBinders_substPlan (ρ : List (Ident × Expr)) (plan : List SelectiveArg) :
    selectiveBinders (substSelectivePlan ρ plan) = selectiveBinders plan := by
  induction plan with
  | nil => rfl
  | cons it r ih => cases it <;> simp [substSelectivePlan, selectiveBinders, ih]

theorem selectiveOrigArgs_substPlan (ρ : List (Ident × Expr)) (plan : List SelectiveArg) :
    (selectiveOrigArgs plan).map (substMany ρ) = selectiveOrigArgs (substSelectivePlan ρ plan) := by
  induction plan with
  | nil => rfl
  | cons it r ih => cases it <;> simp [substSelectivePlan, selectiveOrigArgs, ih]

theorem selectiveOutArgs_substPlan (ρ : List (Ident × Expr)) (plan : List SelectiveArg)
    (hdisj : ∀ x ∈ selectiveBinders plan, x ∉ ρ.map Prod.fst) :
    (selectiveOutArgs plan).map (substMany ρ) = selectiveOutArgs (substSelectivePlan ρ plan) := by
  induction plan with
  | nil => rfl
  | cons it r ih =>
    cases it with
    | keepSimple e =>
      simp [substSelectivePlan, selectiveOutArgs, ih hdisj]
    | floatLet x e =>
      simp only [selectiveBinders, List.mem_cons] at hdisj
      have hx_not : x ∉ ρ.map Prod.fst := hdisj x (Or.inl rfl)
      have hid : ∀ ρ', x ∉ ρ'.map Prod.fst → substMany ρ' (.var x) = .var x := by
        intro ρ' hn; induction ρ' with
        | nil => rfl
        | cons q qr ihq =>
          simp only [List.map_cons, List.mem_cons, not_or] at hn
          simp [substMany, subst, beq_false_of_ne hn.1, ihq hn.2]
      simp [substSelectivePlan, selectiveOutArgs, hid ρ hx_not,
        ih (fun y hy => hdisj y (Or.inr hy))]

theorem wrapSelectiveLets_substMany (ρ : List (Ident × Expr)) (plan : List SelectiveArg) (core : Expr)
    (hdisj : ∀ x ∈ selectiveBinders plan, x ∉ ρ.map Prod.fst) :
    substMany ρ (wrapSelectiveLets plan core) =
      wrapSelectiveLets (substSelectivePlan ρ plan) (substMany ρ core) := by
  induction plan with
  | nil => rfl
  | cons it r ih =>
    cases it with
    | keepSimple _ => exact ih hdisj
    | floatLet x e =>
      simp only [selectiveBinders, List.mem_cons] at hdisj
      rw [wrapSelectiveLets, substMany_let_not_mem ρ (hdisj x (Or.inl rfl)),
          ih (fun y hy => hdisj y (Or.inr hy))]
      rfl

/-- **Open-Term Selective ANF Lifting (`coFloatSelectedArgs` under Closing Environment `ρ`)**:
    Covers open variable simple terms (`.keepSimple (.var z)`) and open suffix expressions! -/
theorem selectiveAnfDir_open_obsEquiv {Δ : AdtEnv} {Φ : FunEnv}
    (hΦ : ClosedFunEnv Φ) {ρ : List (Ident × Expr)}
    {plan : List SelectiveArg} {suffix : List Expr} {fn : Ident}
    {σ σ' : Store} {out : Expr}
    (hσ : ClosedStore σ) (hout : IsTerminal out)
    (hnodup : (selectiveBinders plan).Nodup)
    (hdisjρ : ∀ x ∈ selectiveBinders plan, x ∉ ρ.map Prod.fst)
    (hwfρ : SelectivePlanWF (substSelectivePlan ρ plan))
    (hsuf_cl : ∀ s ∈ suffix, freeVars (substMany ρ s) = []) :
    Steps Δ Φ (substMany ρ (selectiveAnfDir plan suffix fn)) σ out σ' ↔
      Steps Δ Φ (substMany ρ (.applyDir fn (selectiveOrigArgs plan ++ suffix))) σ out σ' := by
  rcases substMany_map_helper ρ with ⟨_, _, _, hdir, _⟩
  rw [selectiveAnfDir, wrapSelectiveLets_substMany ρ plan _ hdisjρ,
      hdir, List.map_append, selectiveOutArgs_substPlan ρ plan hdisjρ,
      hdir, List.map_append, selectiveOrigArgs_substPlan ρ plan]
  apply selectiveAnfDir_obsEquiv hΦ hσ hout
  · rw [selectiveBinders_substPlan]; exact hnodup
  · exact hwfρ
  · intro x hx s hs
    rcases List.mem_map.mp hs with ⟨s0, hs0, rfl⟩
    simp [hsuf_cl s0 hs0]

/-- Indirect closure call (`TmApply`) selective ANF lifting (`src/core.gsa:7406`). -/
def selectiveAnfApply (callee : SelectiveArg) (plan : List SelectiveArg) (suffix : List Expr) : Expr :=
  match callee with
  | .keepSimple fn =>
    wrapSelectiveLets plan (.apply fn (selectiveOutArgs plan ++ suffix))
  | .floatLet xf fn =>
    .let_ xf fn (wrapSelectiveLets plan (.apply (.var xf) (selectiveOutArgs plan ++ suffix)))

private theorem selectiveAnfApply_val_aux_iff {Δ : AdtEnv} {Φ : FunEnv}
    (hΦ : ClosedFunEnv Φ) {plan : List SelectiveArg} {vs suffix : List Expr} {vf : Expr}
    {σ σ' : Store} {out : Expr}
    (hσ : ClosedStore σ) (hout : IsTerminal out)
    (hvf_val : IsValue vf) (hvf_cl : freeVars vf = [])
    (hnodup : (selectiveBinders plan).Nodup)
    (hwf : SelectivePlanWF plan)
    (hsuf_disj : ∀ x ∈ selectiveBinders plan, ∀ s ∈ suffix, x ∉ freeVars s)
    (hvs_val : ∀ v ∈ vs, IsValue v) (hvs_cl : ∀ v ∈ vs, freeVars v = []) :
    Steps Δ Φ (wrapSelectiveLets plan (.apply vf (vs ++ (selectiveOutArgs plan ++ suffix)))) σ out σ' ↔
      Steps Δ Φ (.apply vf (vs ++ (selectiveOrigArgs plan ++ suffix))) σ out σ' := by
  induction plan generalizing vs σ with
  | nil => simp [wrapSelectiveLets, selectiveOutArgs, selectiveOrigArgs]
  | cons item r ih =>
    rcases hwf with ⟨hkeep, hfloat⟩
    have hwf_r : SelectivePlanWF r :=
      ⟨fun s hs => hkeep s (List.mem_cons_of_mem _ hs),
       fun y ey hy => hfloat y ey (List.mem_cons_of_mem _ hy)⟩
    cases item with
    | keepSimple s =>
      rcases hkeep s (List.mem_cons_self ..) with ⟨hs_val, hs_cl⟩
      have hvs_val' : ∀ w ∈ vs ++ [s], IsValue w := by
        intro w hw; rcases List.mem_append.mp hw with h1 | h2
        · exact hvs_val w h1
        · simp at h2; subst h2; exact hs_val
      have hvs_cl' : ∀ w ∈ vs ++ [s], freeVars w = [] := by
        intro w hw; rcases List.mem_append.mp hw with h1 | h2
        · exact hvs_cl w h1
        · simp at h2; subst h2; exact hs_cl
      simpa [wrapSelectiveLets, selectiveOutArgs, selectiveOrigArgs, List.append_assoc] using
        ih hσ hnodup hwf_r hsuf_disj hvs_val' hvs_cl'
    | floatLet x e =>
      simp only [selectiveBinders] at hnodup
      rcases List.nodup_cons.mp hnodup with ⟨hx_r, hnodup_r⟩
      have he_cl : freeVars e = [] := hfloat x e (List.mem_cons_self ..)
      have hx_orig_r : ∀ a ∈ selectiveOrigArgs r, x ∉ freeVars a :=
        fun a ha => by rw [selectiveOrigArgs_closed hwf_r a ha]; simp
      have hsub_suf : ∀ v, substList x v suffix = suffix :=
        fun v => substList_disjoint_id x v suffix (fun s hs => hsuf_disj x (List.mem_cons_self ..) s hs)
      have hx_vf : x ∉ freeVars vf := by simp [hvf_cl]
      have hsub_core : ∀ v,
          subst x v (wrapSelectiveLets r (.apply vf (vs ++ Expr.var x :: (selectiveOutArgs r ++ suffix)))) =
            wrapSelectiveLets r (.apply vf ((vs ++ [v]) ++ (selectiveOutArgs r ++ suffix))) := by
        intro v
        rw [subst_wrapSelectiveLets_disjoint x v r _ hx_r hx_orig_r]
        congr 1
        simp only [subst, subst_not_mem_freeVars vf hx_vf]
        have hsplit : vs ++ Expr.var x :: (selectiveOutArgs r ++ suffix) =
            (vs ++ [Expr.var x]) ++ (selectiveOutArgs r ++ suffix) := by simp
        rw [hsplit, substList_append_eq, substList_closed_append_self x v vs hvs_cl,
            substList_append_eq, substList_selectiveOutArgs_disjoint x v r hx_r (fun s hs => (hwf_r.1 s hs).2),
            hsub_suf v]
      simp only [wrapSelectiveLets, selectiveOrigArgs, selectiveOutArgs, List.cons_append]
      rw [steps_let_terminal_iff hout, steps_apply_next_arg_iff hout hvf_val hvs_val]
      apply or_congr Iff.rfl
      have hsuf_r : ∀ y ∈ selectiveBinders r, ∀ s ∈ suffix, y ∉ freeVars s :=
        fun y hy => hsuf_disj y (List.mem_cons_of_mem _ hy)
      constructor
      · rintro ⟨v, σ1, hv, hs_v, hs_rest⟩
        rcases steps_preserves_closed hΦ hσ he_cl hs_v with ⟨hv_cl, hσ1⟩
        rw [hsub_core v] at hs_rest
        have hvs_val' : ∀ w ∈ vs ++ [v], IsValue w := by
          intro w hw; rcases List.mem_append.mp hw with h1 | h2
          · exact hvs_val w h1
          · simp at h2; subst h2; exact hv
        have hvs_cl' : ∀ w ∈ vs ++ [v], freeVars w = [] := by
          intro w hw; rcases List.mem_append.mp hw with h1 | h2
          · exact hvs_cl w h1
          · simp at h2; subst h2; exact hv_cl
        exact ⟨v, σ1, hv, hs_v, (ih hσ1 hnodup_r hwf_r hsuf_r hvs_val' hvs_cl').mp hs_rest⟩
      · rintro ⟨v, σ1, hv, hs_v, hs_rest⟩
        rcases steps_preserves_closed hΦ hσ he_cl hs_v with ⟨hv_cl, hσ1⟩
        have hvs_val' : ∀ w ∈ vs ++ [v], IsValue w := by
          intro w hw; rcases List.mem_append.mp hw with h1 | h2
          · exact hvs_val w h1
          · simp at h2; subst h2; exact hv
        have hvs_cl' : ∀ w ∈ vs ++ [v], freeVars w = [] := by
          intro w hw; rcases List.mem_append.mp hw with h1 | h2
          · exact hvs_cl w h1
          · simp at h2; subst h2; exact hv_cl
        refine ⟨v, σ1, hv, hs_v, ?_⟩
        rw [hsub_core v]
        exact (ih hσ1 hnodup_r hwf_r hsuf_r hvs_val' hvs_cl').mpr hs_rest

/-- **Soundness of Selective ANF Lifting on Indirect `TmApply` (`src/core.gsa:7406`)**:
    Covers both simple unfloated callees (`.keepSimple vf`) and floated callees (`.floatLet xf fn`),
    together with selective argument prefix `plan` and preserved `suffix` (`idx > lastIdx`). -/
theorem selectiveAnfApply_obsEquiv {Δ : AdtEnv} {Φ : FunEnv}
    (hΦ : ClosedFunEnv Φ) {callee : SelectiveArg} {plan : List SelectiveArg} {suffix : List Expr}
    {σ σ' : Store} {out : Expr}
    (hσ : ClosedStore σ) (hout : IsTerminal out)
    (hnodup : (selectiveBinders (callee :: plan)).Nodup)
    (hwf : SelectivePlanWF (callee :: plan))
    (hsuf_disj : ∀ x ∈ selectiveBinders (callee :: plan), ∀ s ∈ suffix, x ∉ freeVars s) :
    let origFn := match callee with | .keepSimple fn => fn | .floatLet _ fn => fn
    Steps Δ Φ (selectiveAnfApply callee plan suffix) σ out σ' ↔
      Steps Δ Φ (.apply origFn (selectiveOrigArgs plan ++ suffix)) σ out σ' := by
  have hwf_plan : SelectivePlanWF plan :=
    ⟨fun s hs => hwf.1 s (List.mem_cons_of_mem _ hs),
     fun y ey hy => hwf.2 y ey (List.mem_cons_of_mem _ hy)⟩
  cases callee with
  | keepSimple vf =>
    rcases hwf.1 vf (List.mem_cons_self ..) with ⟨hvf_val, hvf_cl⟩
    simp only [selectiveBinders] at hnodup hsuf_disj
    simpa [selectiveAnfApply] using
      selectiveAnfApply_val_aux_iff (vs := []) hΦ hσ hout hvf_val hvf_cl hnodup hwf_plan hsuf_disj
        (fun _ h => by cases h) (fun _ h => by cases h)
  | floatLet xf fn =>
    simp only [selectiveBinders] at hnodup
    rcases List.nodup_cons.mp hnodup with ⟨hxf_plan, hnodup_plan⟩
    have hfn_cl : freeVars fn = [] := hwf.2 xf fn (List.mem_cons_self ..)
    have hxf_orig : ∀ a ∈ selectiveOrigArgs plan, xf ∉ freeVars a :=
      fun a ha => by rw [selectiveOrigArgs_closed hwf_plan a ha]; simp
    have hsub_suf : ∀ vf, substList xf vf suffix = suffix :=
      fun vf => substList_disjoint_id xf vf suffix (fun s hs => hsuf_disj xf (List.mem_cons_self ..) s hs)
    have hsub_inner : ∀ vf,
        subst xf vf (wrapSelectiveLets plan (.apply (.var xf) (selectiveOutArgs plan ++ suffix))) =
          wrapSelectiveLets plan (.apply vf (selectiveOutArgs plan ++ suffix)) := by
      intro vf
      rw [subst_wrapSelectiveLets_disjoint xf vf plan _ hxf_plan hxf_orig]
      congr 1
      simp [subst, substList_append_eq,
        substList_selectiveOutArgs_disjoint xf vf plan hxf_plan (fun s hs => (hwf_plan.1 s hs).2),
        hsub_suf vf]
    simp only [selectiveAnfApply]
    rw [steps_let_terminal_iff hout, steps_apply_callee_iff hout]
    apply or_congr Iff.rfl
    have hsuf_plan : ∀ x ∈ selectiveBinders plan, ∀ s ∈ suffix, x ∉ freeVars s :=
      fun x hx => hsuf_disj x (List.mem_cons_of_mem _ hx)
    constructor
    · rintro ⟨vf, σ1, hvf, hs_vf, hs_rest⟩
      rcases steps_preserves_closed hΦ hσ hfn_cl hs_vf with ⟨hvf_cl, hσ1⟩
      rw [hsub_inner vf] at hs_rest
      have hr := (selectiveAnfApply_val_aux_iff (vs := []) hΦ hσ1 hout hvf hvf_cl hnodup_plan hwf_plan hsuf_plan
        (fun _ h => by cases h) (fun _ h => by cases h)).mp (by simpa using hs_rest)
      exact ⟨vf, σ1, hvf, hs_vf, by simpa using hr⟩
    · rintro ⟨vf, σ1, hvf, hs_vf, hs_rest⟩
      rcases steps_preserves_closed hΦ hσ hfn_cl hs_vf with ⟨hvf_cl, hσ1⟩
      refine ⟨vf, σ1, hvf, hs_vf, ?_⟩
      rw [hsub_inner vf]
      exact (selectiveAnfApply_val_aux_iff (vs := []) hΦ hσ1 hout hvf hvf_cl hnodup_plan hwf_plan hsuf_plan
        (fun _ h => by cases h) (fun _ h => by cases h)).mpr (by simpa using hs_rest)

/-- Concrete positive witness of selective ANF lifting with skipped simple prefix and unfloated suffix. -/
theorem selective_anf_suffix_witness :
    let Φ3 : FunEnv := fun nm =>
      if nm == "sum3" then
        some { name := "sum3", params := [("a", .int), ("b", .int), ("c", .int)], retTy := .int,
               body := .bin .add (.bin .add (.var "a") (.var "b")) (.var "c") }
      else none
    let plan : List SelectiveArg :=
      [.keepSimple (.lit (.int 10)),
       .floatLet "$co$0$arg" (.block [.cellSet (.loc 0) (.lit (.int 30)), .lit (.int 2)])]
    let suffix : List Expr := [.cellGet (.loc 0)]
    Steps (fun _ => none) Φ3 (selectiveAnfDir plan suffix "sum3") [.lit (.int 5)]
      (.lit (.int 42)) [.lit (.int 30)] ∧
    Steps (fun _ => none) Φ3 (.applyDir "sum3" (selectiveOrigArgs plan ++ suffix)) [.lit (.int 5)]
      (.lit (.int 42)) [.lit (.int 30)] := by
  let Φ3 : FunEnv := fun nm =>
    if nm == "sum3" then
      some { name := "sum3", params := [("a", .int), ("b", .int), ("c", .int)], retTy := .int,
             body := .bin .add (.bin .add (.var "a") (.var "b")) (.var "c") }
    else none
  let plan : List SelectiveArg :=
    [.keepSimple (.lit (.int 10)),
     .floatLet "$co$0$arg" (.block [.cellSet (.loc 0) (.lit (.int 30)), .lit (.int 2)])]
  let suffix : List Expr := [.cellGet (.loc 0)]
  have hΦ3 : ClosedFunEnv Φ3 := by
    intro nm fd hfd z hz
    simp only [Φ3] at hfd
    split at hfd
    · injection hfd with hfd; subst hfd
      simp [freeVars] at hz ⊢
      rcases hz with rfl | rfl | rfl <;> simp
    · cases hfd
  have hv3 : ∀ v ∈ ([.lit (.int 10), .lit (.int 2), .lit (.int 30)] : List Expr), IsValue v := by
    intro v hv; rcases List.mem_cons.mp hv with rfl | h1
    · exact .lit _
    · rcases List.mem_cons.mp h1 with rfl | h2
      · exact .lit _
      · rcases List.mem_cons.mp h2 with rfl | h3
        · exact .lit _
        · cases h3
  have hLifted : Steps (fun _ => none) Φ3 (selectiveAnfDir plan suffix "sum3") [.lit (.int 5)]
      (.lit (.int 42)) [.lit (.int 30)] := by
    refine .trans (.letStep (.blockConsStep (.cellSetVal (by decide) (.lit _)))) ?_
    refine .trans (.letStep (.blockConsVal (.lit _))) ?_
    refine .trans (.letStep .blockSingle) ?_
    refine .trans (.letVal (.lit _)) ?_
    refine .trans (.applyDirArgs (.tail (.lit _) (.tail (.lit _) (.head (.cellGetVal rfl))))) ?_
    refine .trans (.applyDirBeta rfl hv3 rfl) ?_
    refine .trans (.binLeft (.binVal rfl)) ?_
    exact .single (.binVal rfl)
  have hwf : SelectivePlanWF plan := by
    refine ⟨?_, ?_⟩
    · intro e he; simp [plan] at he; subst he; exact ⟨.lit _, rfl⟩
    · intro x e he; simp [plan] at he; rcases he with ⟨rfl, rfl⟩; rfl
  have hOrig := (selectiveAnfDir_obsEquiv hΦ3
    (fun v hv => by simp at hv; subst hv; rfl)
    (Or.inl (.lit _)) (by decide) hwf
    (by intro x hx s hs; simp [plan, selectiveBinders] at hx; simp [suffix] at hs; subst hx hs; decide)).mp hLifted
  exact ⟨hLifted, hOrig⟩

/- 7.4 Recursive 3-Valued `coMatchPatKnownB` (`src/core.gsa:6047-6118`) & Fresh-Cloned `coTryReduceMatch` (`src/core.gsa:6148-6163`). -/
inductive CoPatRes where
  | yes (binds : List (Ident × Expr))
  | no
  | unknown

def isNonFloatLitB : Lit → Bool
  | .floatBits _ | .float32Bits _ => false
  | _ => true

mutual
def coMatchPatKnownB : Pat → Expr → CoPatRes
  | .wild, _ => .yes []
  | .var v, tm => .yes [(v, tm)]
  | .lit pLit, .lit tLit =>
    if isNonFloatLitB pLit && isNonFloatLitB tLit then
      if pLit == tLit then .yes [] else .no
    else .unknown
  | .lit _, _ => .unknown
  | .tuple subPats, .tuple elems =>
    if subPats.length != elems.length then .unknown
    else coMatchPatListKnownB subPats elems
  | .tuple _, _ => .unknown
  | .ctor patAdt patTag subPats, .makeData dataAdt dataTag fields =>
    if patAdt != dataAdt then .unknown
    else if patTag != dataTag then .no
    else if subPats.length != fields.length then .unknown
    else coMatchPatListKnownB subPats fields
  | .ctor _ _ _, _ => .unknown

def coMatchPatListKnownB : List Pat → List Expr → CoPatRes
  | [], [] => .yes []
  | p :: rp, e :: re =>
    match coMatchPatKnownB p e with
    | .no => .no
    | .unknown =>
      match coMatchPatListKnownB rp re with
      | .no => .no
      | _ => .unknown
    | .yes b1 =>
      match coMatchPatListKnownB rp re with
      | .no => .no
      | .unknown => .unknown
      | .yes b2 => .yes (b1 ++ b2)
  | _, _ => .unknown
end

mutual
theorem coMatchPatKnownB_no_sound :
    (p : Pat) → {v : Expr} → coMatchPatKnownB p v = .no → matchPat p v = none
  | .wild, _, h => by simp [coMatchPatKnownB] at h
  | .var _, _, h => by simp [coMatchPatKnownB] at h
  | .lit pLit, v, h => by
    cases v with
    | lit tLit =>
      simp only [coMatchPatKnownB] at h
      split at h
      · split at h
        · cases h
        · rename_i hneq
          have hfalse : (pLit == tLit) = false := Bool.eq_false_iff.mpr hneq
          simp [matchPat, hfalse]
      · cases h
    | _ => simp [coMatchPatKnownB] at h
  | .tuple subPats, v, h => by
    cases v with
    | tuple elems =>
      simp only [coMatchPatKnownB] at h
      split at h
      · cases h
      · simp [matchPat, coMatchPatListKnownB_no_sound subPats h]
    | _ => simp [coMatchPatKnownB] at h
  | .ctor patAdt patTag subPats, v, h => by
    cases v with
    | makeData dataAdt dataTag fields =>
      simp only [coMatchPatKnownB] at h
      split at h
      · cases h
      · split at h
        · rename_i htagNe
          have htagF : (patTag == dataTag) = false :=
            beq_false_of_ne (bne_iff_ne.mp htagNe)
          simp [matchPat, htagF]
        · split at h
          · cases h
          · have hsub := coMatchPatListKnownB_no_sound subPats h
            simp [matchPat, hsub]
    | _ => simp [coMatchPatKnownB] at h
termination_by p => sizeOf p

theorem coMatchPatListKnownB_no_sound :
    (ps : List Pat) → {vs : List Expr} → coMatchPatListKnownB ps vs = .no → matchPats ps vs = none
  | [], vs, h => by cases vs <;> simp [coMatchPatListKnownB] at h
  | p :: rp, vs, h => by
    cases vs with
    | nil => simp [coMatchPatListKnownB] at h
    | cons e re =>
      simp only [coMatchPatListKnownB] at h
      cases h1 : coMatchPatKnownB p e <;> rw [h1] at h
      · cases h2 : coMatchPatListKnownB rp re <;> rw [h2] at h <;> try cases h
        simp [matchPats, coMatchPatListKnownB_no_sound rp h2]
      · simp [matchPats, coMatchPatKnownB_no_sound p h1]
      · cases h2 : coMatchPatListKnownB rp re <;> rw [h2] at h <;> try cases h
        have hr := coMatchPatListKnownB_no_sound rp h2
        cases hm1 : matchPat p e <;> simp [matchPats, hm1, hr]
termination_by ps => sizeOf ps
end

mutual
theorem coMatchPatKnownB_yes_sound :
    (p : Pat) → {v : Expr} → {binds : List (Ident × Expr)} →
    coMatchPatKnownB p v = .yes binds → matchPat p v = some binds
  | .wild, _, _, h => by simp [coMatchPatKnownB] at h; subst h; rfl
  | .var x, v, _, h => by simp [coMatchPatKnownB] at h; subst h; rfl
  | .lit pLit, v, _, h => by
    cases v with
    | lit tLit =>
      simp only [coMatchPatKnownB] at h
      split at h
      · split at h
        · rename_i hbeq
          injection h with h; subst h
          simp [matchPat, hbeq]
        · cases h
      · cases h
    | _ => simp [coMatchPatKnownB] at h
  | .tuple subPats, v, _, h => by
    cases v with
    | tuple elems =>
      simp only [coMatchPatKnownB] at h
      split at h
      · cases h
      · simp [matchPat, coMatchPatListKnownB_yes_sound subPats h]
    | _ => simp [coMatchPatKnownB] at h
  | .ctor patAdt patTag subPats, v, _, h => by
    cases v with
    | makeData dataAdt dataTag fields =>
      simp only [coMatchPatKnownB] at h
      split at h
      · cases h
      · rename_i hadtNe
        have hadtT : (patAdt == dataAdt) = true := by
          cases hc : (patAdt == dataAdt)
          · exact False.elim (hadtNe (by simp [bne, hc]))
          · rfl
        split at h
        · cases h
        · rename_i htagNe
          have htagT : (patTag == dataTag) = true := by
            cases hc : (patTag == dataTag)
            · exact False.elim (htagNe (by simp [bne, hc]))
            · rfl
          split at h
          · cases h
          · simp [matchPat, hadtT, htagT, coMatchPatListKnownB_yes_sound subPats h]
    | _ => simp [coMatchPatKnownB] at h

theorem coMatchPatListKnownB_yes_sound :
    (ps : List Pat) → {vs : List Expr} → {binds : List (Ident × Expr)} →
    coMatchPatListKnownB ps vs = .yes binds → matchPats ps vs = some binds
  | [], vs, _, h => by
    cases vs <;> simp [coMatchPatListKnownB] at h
    subst h; rfl
  | p :: rp, vs, _, h => by
    cases vs with
    | nil => simp [coMatchPatListKnownB] at h
    | cons e re =>
      cases h1 : coMatchPatKnownB p e with
      | no => simp [coMatchPatListKnownB, h1] at h
      | unknown =>
        cases h2 : coMatchPatListKnownB rp re <;> simp [coMatchPatListKnownB, h1, h2] at h
      | yes b1 =>
        cases h2 : coMatchPatListKnownB rp re with
        | no | unknown => simp [coMatchPatListKnownB, h1, h2] at h
        | yes b2 =>
          simp only [coMatchPatListKnownB, h1, h2, CoPatRes.yes.injEq] at h
          subst h
          simp [matchPats, coMatchPatKnownB_yes_sound p h1, coMatchPatListKnownB_yes_sound rp h2]
end

/-- Scoped known-value environment update (`coRecordLetBindingInEnv`, `src/core.gsa:7062-7068`):
    evaluating `rhs` against the *pre-shadow* environment `env` and then updating `x ↦ known?`
    (`some v` for resolved pure constructors/tuples/literals, `none` to kill shadowed bindings)
    preserves exact correspondence with runtime substitution `ρ ++ [(x, rhsVal)]`. -/
def coRecordLetKnown (env : Ident → Option Expr) (x : Ident) (known? : Option Expr) :
    Ident → Option Expr :=
  fun z => if z == x then known? else env z

def KnownEnvConsistent (env : Ident → Option Expr) (ρ : List (Ident × Expr)) : Prop :=
  ∀ z w, env z = some w → substMany ρ (.var z) = w ∧ freeVars w = []

theorem coRecordLetKnown_preserves_consistent
    {env : Ident → Option Expr} {ρ : List (Ident × Expr)} {x : Ident} {rhsVal : Expr}
    {known? : Option Expr}
    (hcons : KnownEnvConsistent env ρ)
    (hknown : ∀ w, known? = some w → w = rhsVal ∧ freeVars w = []) :
    KnownEnvConsistent (coRecordLetKnown env x known?) ((x, rhsVal) :: ρ) := by
  intro z w hget
  simp only [coRecordLetKnown] at hget
  cases hzx : (z == x) <;> rw [hzx] at hget
  · simp only [Bool.false_eq_true, ↓reduceIte] at hget
    simpa [substMany, subst, hzx] using hcons z w hget
  · simp only [↓reduceIte] at hget
    rcases hknown w hget with ⟨rfl, hw_cl⟩
    simp only [substMany, subst, hzx, ↓reduceIte]
    exact ⟨substMany_closed_val_id ρ hw_cl, hw_cl⟩

/-- **Soundness of General `CoPatNo` Arm Elimination (`coTryReduceMatch`, `src/core.gsa:6144`)**:
    Covers tag mismatches, non-float literal mismatches, tuple subpattern mismatches, AND
    same-tag constructor nested subpattern mismatches (e.g. `Some(1)` against `Some(2)`). -/
theorem known_pat_miss_of_coPatNo_obsEquiv (Δ : AdtEnv) (Φ : FunEnv)
    {v : Expr} {p : Pat} {body : Expr} {rest : List (Pat × Expr)}
    (hv : IsValue v) (hno : coMatchPatKnownB p v = .no) :
    ObsEquiv Δ Φ Φ (.match_ v ((p, body) :: rest)) (.match_ v rest) :=
  obsEquiv_of_det_step fun _ => .matchMiss hv (coMatchPatKnownB_no_sound p hno)

/-- Concrete witness of same-tag nested constructor `CoPatNo` reduction (`Some(1)` vs `Some(2)`). -/
theorem same_tag_nested_ctor_miss_witness :
    let v : Expr := .makeData "Option" 1 [.lit (.int 1)]
    let pMiss : Pat := .ctor "Option" 1 [.lit (.int 2)]
    let rest : List (Pat × Expr) := [(.wild, .lit (.int 99))]
    coMatchPatKnownB pMiss v = .no ∧
    ObsEquiv (fun _ => none) (fun _ => none) (fun _ => none)
      (.match_ v ((pMiss, .lit (.int 0)) :: rest))
      (.match_ v rest) := by
  refine ⟨by rfl, known_pat_miss_of_coPatNo_obsEquiv _ _ ?_ (by rfl)⟩
  exact .makeData "Option" 1 (fun e he => by simp at he; subst he; exact .lit _)

/- Fresh-binder α-renaming (`coCloneTerm`) used by `coTryReduceMatch` and `coGetOrCreateFlatClsFn`. -/
mutual
def exprMentionsIdent (y : Ident) : Expr → Bool
  | .lit _ | .loc _ | .taskRef _ | .syncRef _ _ | .trap _ => false
  | .var z => z == y
  | .tuple es | .block es | .makeData _ _ es | .concPrim _ es => listMentionsIdent y es
  | .lam _ ps _ body => ps.any (fun p => p.1 == y) || exprMentionsIdent y body
  | .apply fn args => exprMentionsIdent y fn || listMentionsIdent y args
  | .applyDir _ args => listMentionsIdent y args
  | .bin _ a b | .while_ a b | .cellSet a b => exprMentionsIdent y a || exprMentionsIdent y b
  | .un _ a | .getTag a | .cellNew a | .cellGet a | .spawn a | .await a => exprMentionsIdent y a
  | .let_ z a b => (z == y) || exprMentionsIdent y a || exprMentionsIdent y b
  | .if_ c t e => exprMentionsIdent y c || exprMentionsIdent y t || exprMentionsIdent y e
  | .match_ s arms => exprMentionsIdent y s || armsMentionsIdent y arms

def listMentionsIdent (y : Ident) : List Expr → Bool
  | [] => false
  | e :: es => exprMentionsIdent y e || listMentionsIdent y es

def armsMentionsIdent (y : Ident) : List (Pat × Expr) → Bool
  | [] => false
  | (p, b) :: rest =>
    (patBoundNames p).contains y || exprMentionsIdent y b || armsMentionsIdent y rest
end

mutual
inductive SafeFreshFor (y : Ident) : Expr → Prop where
  | closed {e : Expr} : freeVars e = [] → SafeFreshFor y e
  | lit (l : Lit) : SafeFreshFor y (.lit l)
  | var {z : Ident} : (z == y) = false → SafeFreshFor y (.var z)
  | loc (l : Loc) : SafeFreshFor y (.loc l)
  | taskRef (tid : TaskId) : SafeFreshFor y (.taskRef tid)
  | syncRef (k : SyncKind) (id : Nat) : SafeFreshFor y (.syncRef k id)
  | trap (t : Trap) : SafeFreshFor y (.trap t)
  | tuple {es : List Expr} : SafeFreshForList y es → SafeFreshFor y (.tuple es)
  | block {es : List Expr} : SafeFreshForList y es → SafeFreshFor y (.block es)
  | lam {m : Mode} {ps : List (Ident × Ty)} {ret : Ty} {body : Expr} :
      ps.any (fun p => p.1 == y) = false →
      SafeFreshFor y body →
      SafeFreshFor y (.lam m ps ret body)
  | apply {fn : Expr} {args : List Expr} :
      SafeFreshFor y fn → SafeFreshForList y args → SafeFreshFor y (.apply fn args)
  | applyDir {nm : Ident} {args : List Expr} :
      SafeFreshForList y args → SafeFreshFor y (.applyDir nm args)
  | bin {op : BinOp} {a b : Expr} :
      SafeFreshFor y a → SafeFreshFor y b → SafeFreshFor y (.bin op a b)
  | un {op : UnOp} {a : Expr} :
      SafeFreshFor y a → SafeFreshFor y (.un op a)
  | let_ {z : Ident} {a b : Expr} :
      (z == y) = false → SafeFreshFor y a → SafeFreshFor y b → SafeFreshFor y (.let_ z a b)
  | if_ {c t e2 : Expr} :
      SafeFreshFor y c → SafeFreshFor y t → SafeFreshFor y e2 → SafeFreshFor y (.if_ c t e2)
  | while_ {c b : Expr} :
      SafeFreshFor y c → SafeFreshFor y b → SafeFreshFor y (.while_ c b)
  | match_ {s : Expr} {arms : List (Pat × Expr)} :
      SafeFreshFor y s → SafeFreshForArms y arms → SafeFreshFor y (.match_ s arms)
  | makeData {adt : Ident} {tag : Nat} {es : List Expr} :
      SafeFreshForList y es → SafeFreshFor y (.makeData adt tag es)
  | getTag {a : Expr} : SafeFreshFor y a → SafeFreshFor y (.getTag a)
  | cellNew {a : Expr} : SafeFreshFor y a → SafeFreshFor y (.cellNew a)
  | cellGet {a : Expr} : SafeFreshFor y a → SafeFreshFor y (.cellGet a)
  | cellSet {a b : Expr} : SafeFreshFor y a → SafeFreshFor y b → SafeFreshFor y (.cellSet a b)
  | spawn {a : Expr} : SafeFreshFor y a → SafeFreshFor y (.spawn a)
  | await {a : Expr} : SafeFreshFor y a → SafeFreshFor y (.await a)
  | concPrim {op : ConcPrim} {es : List Expr} :
      SafeFreshForList y es → SafeFreshFor y (.concPrim op es)

inductive SafeFreshForList (y : Ident) : List Expr → Prop where
  | nil : SafeFreshForList y []
  | cons {e : Expr} {es : List Expr} :
      SafeFreshFor y e → SafeFreshForList y es → SafeFreshForList y (e :: es)

inductive SafeFreshForArms (y : Ident) : List (Pat × Expr) → Prop where
  | nil : SafeFreshForArms y []
  | cons {p : Pat} {b : Expr} {rest : List (Pat × Expr)} :
      (patBoundNames p).contains y = false →
      SafeFreshFor y b →
      SafeFreshForArms y rest →
      SafeFreshForArms y ((p, b) :: rest)
end

mutual
theorem safeFreshFor_of_mentions_false {y : Ident} :
    (e : Expr) → exprMentionsIdent y e = false → SafeFreshFor y e
  | .lit l, _ => .lit l
  | .var _, h => .var h
  | .loc l, _ => .loc l
  | .taskRef tid, _ => .taskRef tid
  | .syncRef k id, _ => .syncRef k id
  | .trap t, _ => .trap t
  | .tuple es, h => by simp only [exprMentionsIdent] at h; exact .tuple (safeFreshForList_of_mentions_false es h)
  | .block es, h => by simp only [exprMentionsIdent] at h; exact .block (safeFreshForList_of_mentions_false es h)
  | .lam _ _ _ body, h => by
    simp only [exprMentionsIdent, Bool.or_eq_false_iff] at h
    exact .lam h.1 (safeFreshFor_of_mentions_false body h.2)
  | .apply fn args, h => by
    simp only [exprMentionsIdent, Bool.or_eq_false_iff] at h
    exact .apply (safeFreshFor_of_mentions_false fn h.1) (safeFreshForList_of_mentions_false args h.2)
  | .applyDir _ args, h => by
    simp only [exprMentionsIdent] at h; exact .applyDir (safeFreshForList_of_mentions_false args h)
  | .bin _ a b, h => by
    simp only [exprMentionsIdent, Bool.or_eq_false_iff] at h
    exact .bin (safeFreshFor_of_mentions_false a h.1) (safeFreshFor_of_mentions_false b h.2)
  | .un _ a, h => by simp only [exprMentionsIdent] at h; exact .un (safeFreshFor_of_mentions_false a h)
  | .let_ _ a b, h => by
    simp only [exprMentionsIdent, Bool.or_eq_false_iff] at h
    exact .let_ h.1.1 (safeFreshFor_of_mentions_false a h.1.2) (safeFreshFor_of_mentions_false b h.2)
  | .if_ c t e2, h => by
    simp only [exprMentionsIdent, Bool.or_eq_false_iff] at h
    exact .if_ (safeFreshFor_of_mentions_false c h.1.1)
      (safeFreshFor_of_mentions_false t h.1.2) (safeFreshFor_of_mentions_false e2 h.2)
  | .while_ c b, h => by
    simp only [exprMentionsIdent, Bool.or_eq_false_iff] at h
    exact .while_ (safeFreshFor_of_mentions_false c h.1) (safeFreshFor_of_mentions_false b h.2)
  | .match_ s arms, h => by
    simp only [exprMentionsIdent, Bool.or_eq_false_iff] at h
    exact .match_ (safeFreshFor_of_mentions_false s h.1) (safeFreshForArms_of_mentions_false arms h.2)
  | .makeData _ _ es, h => by
    simp only [exprMentionsIdent] at h; exact .makeData (safeFreshForList_of_mentions_false es h)
  | .getTag a, h => by simp only [exprMentionsIdent] at h; exact .getTag (safeFreshFor_of_mentions_false a h)
  | .cellNew a, h => by simp only [exprMentionsIdent] at h; exact .cellNew (safeFreshFor_of_mentions_false a h)
  | .cellGet a, h => by simp only [exprMentionsIdent] at h; exact .cellGet (safeFreshFor_of_mentions_false a h)
  | .cellSet a b, h => by
    simp only [exprMentionsIdent, Bool.or_eq_false_iff] at h
    exact .cellSet (safeFreshFor_of_mentions_false a h.1) (safeFreshFor_of_mentions_false b h.2)
  | .spawn a, h => by simp only [exprMentionsIdent] at h; exact .spawn (safeFreshFor_of_mentions_false a h)
  | .await a, h => by simp only [exprMentionsIdent] at h; exact .await (safeFreshFor_of_mentions_false a h)
  | .concPrim _ es, h => by
    simp only [exprMentionsIdent] at h; exact .concPrim (safeFreshForList_of_mentions_false es h)
termination_by e => sizeOf e

theorem safeFreshForList_of_mentions_false {y : Ident} :
    (es : List Expr) → listMentionsIdent y es = false → SafeFreshForList y es
  | [], _ => .nil
  | e :: r, h => by
    simp only [listMentionsIdent, Bool.or_eq_false_iff] at h
    exact .cons (safeFreshFor_of_mentions_false e h.1) (safeFreshForList_of_mentions_false r h.2)
termination_by es => sizeOf es

theorem safeFreshForArms_of_mentions_false {y : Ident} :
    (arms : List (Pat × Expr)) → armsMentionsIdent y arms = false → SafeFreshForArms y arms
  | [], _ => .nil
  | (_, b) :: r, h => by
    simp only [armsMentionsIdent, Bool.or_eq_false_iff] at h
    exact .cons h.1.1 (safeFreshFor_of_mentions_false b h.1.2) (safeFreshForArms_of_mentions_false r h.2)
termination_by arms => sizeOf arms
end

mutual
theorem not_mem_freeVars_of_safeFresh {y : Ident} :
    (e : Expr) → SafeFreshFor y e → y ∉ freeVars e
  | _, .closed hcl => by simp [hcl]
  | .lit _, .lit _ | .loc _, .loc _ | .taskRef _, .taskRef _
  | .syncRef _ _, .syncRef _ _ | .trap _, .trap _ => by simp [freeVars]
  | .var z, .var hzy => by
    simp only [freeVars, List.mem_singleton]
    intro heq; subst heq; rw [beq_self_eq_true] at hzy; cases hzy
  | .tuple es, .tuple hs => by simp [freeVars, not_mem_freeVarsList_of_safeFresh es hs]
  | .block es, .block hs => by simp [freeVars, not_mem_freeVarsList_of_safeFresh es hs]
  | .lam _ _ _ body, .lam _ hb => by
    simp only [freeVars, List.mem_filter]
    rintro ⟨hmem, _⟩; exact not_mem_freeVars_of_safeFresh body hb hmem
  | .apply fn args, .apply hf ha => by
    simp [freeVars, not_mem_freeVars_of_safeFresh fn hf, not_mem_freeVarsList_of_safeFresh args ha]
  | .applyDir _ args, .applyDir ha => by
    simp [freeVars, not_mem_freeVarsList_of_safeFresh args ha]
  | .bin _ a b, .bin ha hb => by
    simp [freeVars, not_mem_freeVars_of_safeFresh a ha, not_mem_freeVars_of_safeFresh b hb]
  | .un _ a, .un ha => by simp [freeVars, not_mem_freeVars_of_safeFresh a ha]
  | .let_ _ a b, .let_ _ ha hb => by
    simp only [freeVars, List.mem_append, List.mem_filter]
    rintro (hmem | ⟨hmem, _⟩)
    · exact not_mem_freeVars_of_safeFresh a ha hmem
    · exact not_mem_freeVars_of_safeFresh b hb hmem
  | .if_ c t e2, .if_ hc ht he => by
    simp [freeVars, not_mem_freeVars_of_safeFresh c hc,
      not_mem_freeVars_of_safeFresh t ht, not_mem_freeVars_of_safeFresh e2 he]
  | .while_ c b, .while_ hc hb => by
    simp [freeVars, not_mem_freeVars_of_safeFresh c hc, not_mem_freeVars_of_safeFresh b hb]
  | .match_ s arms, .match_ hs ha => by
    simp [freeVars, not_mem_freeVars_of_safeFresh s hs, not_mem_freeVarsArms_of_safeFresh arms ha]
  | .makeData _ _ es, .makeData hs => by
    simp [freeVars, not_mem_freeVarsList_of_safeFresh es hs]
  | .getTag a, .getTag ha => by simp [freeVars, not_mem_freeVars_of_safeFresh a ha]
  | .cellNew a, .cellNew ha => by simp [freeVars, not_mem_freeVars_of_safeFresh a ha]
  | .cellGet a, .cellGet ha => by simp [freeVars, not_mem_freeVars_of_safeFresh a ha]
  | .cellSet a b, .cellSet ha hb => by
    simp [freeVars, not_mem_freeVars_of_safeFresh a ha, not_mem_freeVars_of_safeFresh b hb]
  | .spawn a, .spawn ha => by simp [freeVars, not_mem_freeVars_of_safeFresh a ha]
  | .await a, .await ha => by simp [freeVars, not_mem_freeVars_of_safeFresh a ha]
  | .concPrim _ es, .concPrim hs => by
    simp [freeVars, not_mem_freeVarsList_of_safeFresh es hs]
termination_by e => sizeOf e

theorem not_mem_freeVarsList_of_safeFresh {y : Ident} :
    (es : List Expr) → SafeFreshForList y es → y ∉ freeVarsList es
  | [], .nil => by simp [freeVarsList]
  | e :: r, .cons he hr => by
    simp [freeVarsList, not_mem_freeVars_of_safeFresh e he, not_mem_freeVarsList_of_safeFresh r hr]
termination_by es => sizeOf es

theorem not_mem_freeVarsArms_of_safeFresh {y : Ident} :
    (arms : List (Pat × Expr)) → SafeFreshForArms y arms → y ∉ freeVarsArms arms
  | [], .nil => by simp [freeVarsArms]
  | (_, b) :: r, .cons _ hb hr => by
    simp only [freeVarsArms, List.mem_append, List.mem_filter]
    rintro (⟨hmem, _⟩ | hrest)
    · exact not_mem_freeVars_of_safeFresh b hb hmem
    · exact not_mem_freeVarsArms_of_safeFresh r hr hrest
termination_by arms => sizeOf arms
end

mutual
theorem subst_fresh_var_cancel {x y : Ident} {w : Expr} :
    (e : Expr) → SafeFreshFor y e → subst y w (subst x (.var y) e) = subst x w e
  | e, .closed hcl => by
    have hx : x ∉ freeVars e := by simp [hcl]
    have hy : y ∉ freeVars e := by simp [hcl]
    rw [subst_not_mem_freeVars e hx, subst_not_mem_freeVars e hy, subst_not_mem_freeVars e hx]
  | .lit _, .lit _ | .loc _, .loc _ | .taskRef _, .taskRef _
  | .syncRef _ _, .syncRef _ _ | .trap _, .trap _ => rfl
  | .var z, .var hzy => by
    simp only [subst]
    cases hzx : (z == x)
    · simp [subst, hzy]
    · simp [subst]
  | .tuple es, .tuple hs => by simp [subst, substList_fresh_var_cancel es hs]
  | .block es, .block hs => by simp [subst, substList_fresh_var_cancel es hs]
  | .lam m ps ret body, .lam hany hb => by
    simp only [subst]
    cases hax : ps.any (fun p => p.1 == x)
    · simp only [Bool.false_eq_true, ↓reduceIte, subst, hany, subst_fresh_var_cancel body hb]
    · simp only [↓reduceIte, subst, hany, Bool.false_eq_true,
        subst_not_mem_freeVars body (not_mem_freeVars_of_safeFresh body hb)]
  | .apply fn args, .apply hf ha => by
    simp [subst, subst_fresh_var_cancel fn hf, substList_fresh_var_cancel args ha]
  | .applyDir _ args, .applyDir ha => by simp [subst, substList_fresh_var_cancel args ha]
  | .bin _ a b, .bin ha hb => by
    simp [subst, subst_fresh_var_cancel a ha, subst_fresh_var_cancel b hb]
  | .un _ a, .un ha => by simp [subst, subst_fresh_var_cancel a ha]
  | .let_ z a b, .let_ hzy ha hb => by
    simp only [subst]
    cases hzx : (z == x)
    · simp only [Bool.false_eq_true, ↓reduceIte, subst, hzy,
        subst_fresh_var_cancel a ha, subst_fresh_var_cancel b hb]
    · simp only [↓reduceIte, subst, hzy, Bool.false_eq_true, subst_fresh_var_cancel a ha,
        subst_not_mem_freeVars b (not_mem_freeVars_of_safeFresh b hb)]
  | .if_ c t e2, .if_ hc ht he => by
    simp [subst, subst_fresh_var_cancel c hc, subst_fresh_var_cancel t ht, subst_fresh_var_cancel e2 he]
  | .while_ c b, .while_ hc hb => by
    simp [subst, subst_fresh_var_cancel c hc, subst_fresh_var_cancel b hb]
  | .match_ s arms, .match_ hs ha => by
    simp [subst, subst_fresh_var_cancel s hs, substArms_fresh_var_cancel arms ha]
  | .makeData _ _ es, .makeData hs => by simp [subst, substList_fresh_var_cancel es hs]
  | .getTag a, .getTag ha => by simp [subst, subst_fresh_var_cancel a ha]
  | .cellNew a, .cellNew ha => by simp [subst, subst_fresh_var_cancel a ha]
  | .cellGet a, .cellGet ha => by simp [subst, subst_fresh_var_cancel a ha]
  | .cellSet a b, .cellSet ha hb => by
    simp [subst, subst_fresh_var_cancel a ha, subst_fresh_var_cancel b hb]
  | .spawn a, .spawn ha => by simp [subst, subst_fresh_var_cancel a ha]
  | .await a, .await ha => by simp [subst, subst_fresh_var_cancel a ha]
  | .concPrim _ es, .concPrim hs => by simp [subst, substList_fresh_var_cancel es hs]
termination_by e => sizeOf e

theorem substList_fresh_var_cancel {x y : Ident} {w : Expr} :
    (es : List Expr) → SafeFreshForList y es →
      substList y w (substList x (.var y) es) = substList x w es
  | [], .nil => rfl
  | e :: r, .cons he hr => by
    simp [substList, subst_fresh_var_cancel e he, substList_fresh_var_cancel r hr]
termination_by es => sizeOf es

theorem substArms_fresh_var_cancel {x y : Ident} {w : Expr} :
    (arms : List (Pat × Expr)) → SafeFreshForArms y arms →
      substArms y w (substArms x (.var y) arms) = substArms x w arms
  | [], .nil => rfl
  | (p, b) :: r, .cons hpy hb hr => by
    simp only [substArms, substArms_fresh_var_cancel r hr]
    cases hpx : (patBoundNames p).contains x
    · simp only [Bool.false_eq_true, ↓reduceIte, hpy, subst_fresh_var_cancel b hb]
    · simp only [↓reduceIte, hpy, Bool.false_eq_true,
        subst_not_mem_freeVars b (not_mem_freeVars_of_safeFresh b hb)]
termination_by arms => sizeOf arms
end

mutual
theorem safeFreshFor_subst_closed {y x : Ident} {v : Expr} (hv : freeVars v = []) :
    (e : Expr) → SafeFreshFor y e → SafeFreshFor y (subst x v e)
  | e, .closed hcl => .closed (by rw [subst_not_mem_freeVars e (by simp [hcl])]; exact hcl)
  | .lit l, .lit _ => .lit l
  | .var z, .var hzy => by
    simp only [subst]; split
    · exact .closed hv
    · exact .var hzy
  | .loc l, .loc _ => .loc l
  | .taskRef tid, .taskRef _ => .taskRef tid
  | .syncRef k id, .syncRef _ _ => .syncRef k id
  | .trap t, .trap _ => .trap t
  | .tuple es, .tuple hs => .tuple (safeFreshForList_subst_closed hv es hs)
  | .block es, .block hs => .block (safeFreshForList_subst_closed hv es hs)
  | .lam _ _ _ body, .lam hany hb => by
    simp only [subst]; split
    · exact .lam hany hb
    · exact .lam hany (safeFreshFor_subst_closed hv body hb)
  | .apply fn args, .apply hf ha =>
    .apply (safeFreshFor_subst_closed hv fn hf) (safeFreshForList_subst_closed hv args ha)
  | .applyDir _ args, .applyDir ha => .applyDir (safeFreshForList_subst_closed hv args ha)
  | .bin _ a b, .bin ha hb =>
    .bin (safeFreshFor_subst_closed hv a ha) (safeFreshFor_subst_closed hv b hb)
  | .un _ a, .un ha => .un (safeFreshFor_subst_closed hv a ha)
  | .let_ _ a b, .let_ hzy ha hb => by
    simp only [subst]; split
    · exact .let_ hzy (safeFreshFor_subst_closed hv a ha) hb
    · exact .let_ hzy (safeFreshFor_subst_closed hv a ha) (safeFreshFor_subst_closed hv b hb)
  | .if_ c t e2, .if_ hc ht he =>
    .if_ (safeFreshFor_subst_closed hv c hc)
      (safeFreshFor_subst_closed hv t ht) (safeFreshFor_subst_closed hv e2 he)
  | .while_ c b, .while_ hc hb =>
    .while_ (safeFreshFor_subst_closed hv c hc) (safeFreshFor_subst_closed hv b hb)
  | .match_ s arms, .match_ hs ha =>
    .match_ (safeFreshFor_subst_closed hv s hs) (safeFreshForArms_subst_closed hv arms ha)
  | .makeData _ _ es, .makeData hs => .makeData (safeFreshForList_subst_closed hv es hs)
  | .getTag a, .getTag ha => .getTag (safeFreshFor_subst_closed hv a ha)
  | .cellNew a, .cellNew ha => .cellNew (safeFreshFor_subst_closed hv a ha)
  | .cellGet a, .cellGet ha => .cellGet (safeFreshFor_subst_closed hv a ha)
  | .cellSet a b, .cellSet ha hb =>
    .cellSet (safeFreshFor_subst_closed hv a ha) (safeFreshFor_subst_closed hv b hb)
  | .spawn a, .spawn ha => .spawn (safeFreshFor_subst_closed hv a ha)
  | .await a, .await ha => .await (safeFreshFor_subst_closed hv a ha)
  | .concPrim _ es, .concPrim hs => .concPrim (safeFreshForList_subst_closed hv es hs)
termination_by e => sizeOf e

theorem safeFreshForList_subst_closed {y x : Ident} {v : Expr} (hv : freeVars v = []) :
    (es : List Expr) → SafeFreshForList y es → SafeFreshForList y (substList x v es)
  | [], .nil => .nil
  | e :: r, .cons he hr =>
    .cons (safeFreshFor_subst_closed hv e he) (safeFreshForList_subst_closed hv r hr)
termination_by es => sizeOf es

theorem safeFreshForArms_subst_closed {y x : Ident} {v : Expr} (hv : freeVars v = []) :
    (arms : List (Pat × Expr)) → SafeFreshForArms y arms → SafeFreshForArms y (substArms x v arms)
  | [], .nil => .nil
  | (p, b) :: r, .cons hpy hb hr => by
    refine .cons hpy ?_ (safeFreshForArms_subst_closed hv r hr)
    split
    · exact hb
    · exact safeFreshFor_subst_closed hv b hb
termination_by arms => sizeOf arms
end

mutual
theorem subst_var_comm_disjoint {y x2 y2 : Ident} {v : Expr}
    (hy_x2 : y ≠ x2) (hy_y2 : y ≠ y2) (hv : freeVars v = []) :
    (e : Expr) → subst y v (subst x2 (.var y2) e) = subst x2 (.var y2) (subst y v e)
  | .lit _ | .loc _ | .taskRef _ | .syncRef _ _ | .trap _ => rfl
  | .var z => by
    simp only [subst]
    cases hzx2 : (z == x2)
    · cases hzy : (z == y)
      · simp [subst, hzx2, hzy]
      · simp only [Bool.false_eq_true, ↓reduceIte, subst, hzy]
        exact (subst_not_mem_freeVars v (by simp [hv])).symm
    · have hzy : (z == y) = false := by
        have := eq_of_beq hzx2; subst this; exact beq_false_of_ne hy_x2.symm
      have hy2y : (y2 == y) = false := beq_false_of_ne hy_y2.symm
      simp [subst, hzx2, hzy, hy2y]
  | .tuple es => by simp [subst, substList_var_comm_disjoint hy_x2 hy_y2 hv es]
  | .block es => by simp [subst, substList_var_comm_disjoint hy_x2 hy_y2 hv es]
  | .lam _ ps _ body => by
    simp only [subst]
    cases h1 : ps.any (fun p => p.1 == x2) <;> cases h2 : ps.any (fun p => p.1 == y) <;>
      simp [subst, h1, h2, subst_var_comm_disjoint hy_x2 hy_y2 hv body]
  | .apply fn args => by
    simp [subst, subst_var_comm_disjoint hy_x2 hy_y2 hv fn,
      substList_var_comm_disjoint hy_x2 hy_y2 hv args]
  | .applyDir _ args => by simp [subst, substList_var_comm_disjoint hy_x2 hy_y2 hv args]
  | .bin _ a b => by
    simp [subst, subst_var_comm_disjoint hy_x2 hy_y2 hv a, subst_var_comm_disjoint hy_x2 hy_y2 hv b]
  | .un _ a => by simp [subst, subst_var_comm_disjoint hy_x2 hy_y2 hv a]
  | .let_ z a b => by
    simp only [subst]
    cases h1 : (z == x2) <;> cases h2 : (z == y) <;>
      simp [subst, h1, h2, subst_var_comm_disjoint hy_x2 hy_y2 hv a,
        subst_var_comm_disjoint hy_x2 hy_y2 hv b]
  | .if_ c t e2 => by
    simp [subst, subst_var_comm_disjoint hy_x2 hy_y2 hv c,
      subst_var_comm_disjoint hy_x2 hy_y2 hv t, subst_var_comm_disjoint hy_x2 hy_y2 hv e2]
  | .while_ c b => by
    simp [subst, subst_var_comm_disjoint hy_x2 hy_y2 hv c, subst_var_comm_disjoint hy_x2 hy_y2 hv b]
  | .match_ s arms => by
    simp [subst, subst_var_comm_disjoint hy_x2 hy_y2 hv s,
      substArms_var_comm_disjoint hy_x2 hy_y2 hv arms]
  | .makeData _ _ es => by simp [subst, substList_var_comm_disjoint hy_x2 hy_y2 hv es]
  | .getTag a => by simp [subst, subst_var_comm_disjoint hy_x2 hy_y2 hv a]
  | .cellNew a => by simp [subst, subst_var_comm_disjoint hy_x2 hy_y2 hv a]
  | .cellGet a => by simp [subst, subst_var_comm_disjoint hy_x2 hy_y2 hv a]
  | .cellSet a b => by
    simp [subst, subst_var_comm_disjoint hy_x2 hy_y2 hv a, subst_var_comm_disjoint hy_x2 hy_y2 hv b]
  | .spawn a => by simp [subst, subst_var_comm_disjoint hy_x2 hy_y2 hv a]
  | .await a => by simp [subst, subst_var_comm_disjoint hy_x2 hy_y2 hv a]
  | .concPrim _ es => by simp [subst, substList_var_comm_disjoint hy_x2 hy_y2 hv es]
termination_by e => sizeOf e

theorem substList_var_comm_disjoint {y x2 y2 : Ident} {v : Expr}
    (hy_x2 : y ≠ x2) (hy_y2 : y ≠ y2) (hv : freeVars v = []) :
    (es : List Expr) → substList y v (substList x2 (.var y2) es) =
      substList x2 (.var y2) (substList y v es)
  | [] => rfl
  | e :: r => by
    simp [substList, subst_var_comm_disjoint hy_x2 hy_y2 hv e,
      substList_var_comm_disjoint hy_x2 hy_y2 hv r]
termination_by es => sizeOf es

theorem substArms_var_comm_disjoint {y x2 y2 : Ident} {v : Expr}
    (hy_x2 : y ≠ x2) (hy_y2 : y ≠ y2) (hv : freeVars v = []) :
    (arms : List (Pat × Expr)) → substArms y v (substArms x2 (.var y2) arms) =
      substArms x2 (.var y2) (substArms y v arms)
  | [] => rfl
  | (p, b) :: r => by
    simp only [substArms, substArms_var_comm_disjoint hy_x2 hy_y2 hv r]
    cases h1 : (patBoundNames p).contains x2 <;> cases h2 : (patBoundNames p).contains y <;>
      simp [subst_var_comm_disjoint hy_x2 hy_y2 hv b]
termination_by arms => sizeOf arms
end

/-- Parameter/pattern-binder fresh renaming (`coCloneTerm` on `(origPs, freshPs)`). -/
def cloneRenameParams : List (Ident × Ty) → List (Ident × Ty) → Expr → Expr
  | (x, _) :: or_, (y, _) :: fr, body =>
    cloneRenameParams or_ fr (subst x (.var y) body)
  | _, _, body => body

theorem subst_cloneRenameParams_comm {y : Ident} {v : Expr}
    (or_ fr : List (Ident × Ty)) (e : Expr)
    (hy_or : y ∉ or_.map Prod.fst) (hy_fr : y ∉ fr.map Prod.fst)
    (hv : freeVars v = []) :
    subst y v (cloneRenameParams or_ fr e) = cloneRenameParams or_ fr (subst y v e) := by
  induction or_ generalizing fr e with
  | nil => rfl
  | cons p orRest ih =>
    cases fr with
    | nil => rfl
    | cons q frRest =>
      simp only [List.map_cons, List.mem_cons, not_or] at hy_or hy_fr
      simp only [cloneRenameParams]
      rw [ih frRest _ hy_or.2 hy_fr.2, subst_var_comm_disjoint hy_or.1 hy_fr.1 hv e]

/-- **Fresh Parameter/Pattern Cloning Cancellation (`coCloneTerm` + `substMany`)**:
    Renaming `origPs` to fresh `freshPs` (`exprMentionsIdent y body = false` and disjoint from `origPs`)
    and then substituting closed values `vals` for `freshPs` yields `substMany (zipParams origPs vals) body`. -/
theorem substMany_cloneRenameParams_eq
    (origPs freshPs : List (Ident × Ty)) (vals : List Expr) (body : Expr)
    (hlen1 : freshPs.length = origPs.length)
    (hlen2 : vals.length = origPs.length)
    (hfnodup : (freshPs.map Prod.fst).Nodup)
    (hfdisj : ∀ y ∈ freshPs.map Prod.fst, y ∉ origPs.map Prod.fst)
    (hsafe : ∀ y ∈ freshPs.map Prod.fst, SafeFreshFor y body)
    (hvalsCl : ∀ v ∈ vals, freeVars v = []) :
    substMany (zipParams freshPs vals) (cloneRenameParams origPs freshPs body) =
      substMany (zipParams origPs vals) body := by
  induction origPs generalizing freshPs vals body with
  | nil =>
    cases freshPs <;> cases vals <;> simp [zipParams, substMany, cloneRenameParams] at hlen1 hlen2 ⊢
  | cons px orRest ih =>
    cases freshPs with
    | nil => simp at hlen1
    | cons py frRest =>
      cases vals with
      | nil => simp at hlen2
      | cons v vr =>
        simp only [List.length_cons, Nat.succ.injEq] at hlen1 hlen2
        simp only [List.map_cons] at hfnodup
        rcases List.nodup_cons.mp hfnodup with ⟨hpy_fr, hnodup_fr⟩
        have hv_cl : freeVars v = [] := hvalsCl v (List.mem_cons_self ..)
        have hvr_cl : ∀ w ∈ vr, freeVars w = [] := fun w hw => hvalsCl w (List.mem_cons_of_mem _ hw)
        have hpy_or : py.1 ∉ orRest.map Prod.fst :=
          fun hm => hfdisj py.1 (List.mem_cons_self ..) (List.mem_cons_of_mem _ hm)
        have hpy_safe : SafeFreshFor py.1 body := hsafe py.1 (List.mem_cons_self ..)
        simp only [zipParams, List.map_cons, List.zip_cons_cons, substMany, cloneRenameParams]
        rw [subst_cloneRenameParams_comm orRest frRest _ hpy_or hpy_fr hv_cl,
            subst_fresh_var_cancel body hpy_safe]
        exact ih frRest vr (subst px.1 v body) hlen1 hlen2 hnodup_fr
          (fun y hy hm => hfdisj y (List.mem_cons_of_mem _ hy) (List.mem_cons_of_mem _ hm))
          (fun y hy => safeFreshFor_subst_closed hv_cl body (hsafe y (List.mem_cons_of_mem _ hy)))
          hvr_cl

/-- **Soundness of `coTryReduceMatch` Hit with Fresh `let` Wrapping & Body Cloning (`src/core.gsa:6148-6163`)**. -/
theorem coTryReduceMatch_fresh_lets_obsEquiv (Δ : AdtEnv) (Φ : FunEnv)
    {v : Expr} {p : Pat} {body : Expr} {rest : List (Pat × Expr)}
    {binds : List (Ident × Expr)} {origDecls freshDecls : List (Ident × Ty)}
    (hv : IsValue v) (hm : matchPat p v = some binds)
    (horig : origDecls.map Prod.fst = binds.map Prod.fst)
    (hlen : freshDecls.length = origDecls.length)
    (hfnodup : (freshDecls.map Prod.fst).Nodup)
    (hfdisj : ∀ y ∈ freshDecls.map Prod.fst, y ∉ origDecls.map Prod.fst)
    (hfresh : ∀ y ∈ freshDecls.map Prod.fst, exprMentionsIdent y body = false)
    (hbVal : ∀ q ∈ binds, IsValue q.2) (hbCl : ∀ q ∈ binds, freeVars q.2 = []) :
    ObsEquiv Δ Φ Φ
      (.match_ v ((p, body) :: rest))
      (wrapLetParams freshDecls (binds.map Prod.snd) (cloneRenameParams origDecls freshDecls body)) := by
  have hhit : ObsEquiv Δ Φ Φ (.match_ v ((p, body) :: rest)) (substMany binds body) :=
    obsEquiv_of_det_step fun _ => .matchHit hv hm
  have hzip_eq : zipParams origDecls (binds.map Prod.snd) = binds := by
    unfold zipParams; rw [horig]
    clear hm horig hbVal hbCl hhit
    induction binds with
    | nil => rfl
    | cons b br ihb => rcases b with ⟨k, w⟩; simp [ihb]
  have hlen_vals : (binds.map Prod.snd).length = origDecls.length := by
    have := congrArg List.length horig; simpa using this.symm
  have hlets := wrapLetParams_obsEquiv_substMany Δ Φ freshDecls (binds.map Prod.snd)
    (cloneRenameParams origDecls freshDecls body) hfnodup (by omega)
    (fun w hw => by rcases List.mem_map.mp hw with ⟨q, hq, rfl⟩; exact hbVal q hq)
    (fun w hw => by rcases List.mem_map.mp hw with ⟨q, hq, rfl⟩; exact hbCl q hq)
  rw [substMany_cloneRenameParams_eq origDecls freshDecls (binds.map Prod.snd) body
        hlen hlen_vals hfnodup hfdisj
        (fun y hy => safeFreshFor_of_mentions_false body (hfresh y hy))
        (fun w hw => by rcases List.mem_map.mp hw with ⟨q, hq, rfl⟩; exact hbCl q hq),
      hzip_eq] at hlets
  exact ObsEquiv.trans hhit hlets.symm

/- 7.5 Actual Captures-First `$flat$` (`coGetOrCreateFlatClsFn`, `src/core.gsa:5989-6030,7379`):
   `params = fvsFresh ++ psFresh`, call `fvVals ++ args` (captures FIRST, ordinary params SECOND!),
   fresh parameter cloning, non-value argument evaluation, AND `Φ ↦ Φ'` registration! -/

/-- **Captures-First Substitution Identity (`src/core.gsa:5989-6013,7379`)**. -/
theorem substMany_lam_apply_eq_flat_capturesFirst
    (fvs ps : List (Ident × Ty)) (fvVals argVals : List Expr) (body : Expr)
    (hfvLen : fvVals.length = fvs.length) :
    substMany (zipParams ps argVals) (substMany (zipParams fvs fvVals) body) =
      substMany (zipParams (fvs ++ ps) (fvVals ++ argVals)) body := by
  rw [zipParams_append hfvLen, substMany_append]

private theorem steps_apply_vs_applyDir_capturesFirst {Δ : AdtEnv} {Φ1 Φ2 : FunEnv}
    {dom : Ident → Bool}
    (hagree : FunEnvAgreesOn dom Φ1 Φ2) (hΦ1dom : ClosedDomEnv dom Φ1) (hΦ1cl : ClosedFunEnv Φ1)
    {flatName : Ident} {m : Mode} {fvs ps fvsFresh psFresh : List (Ident × Ty)}
    {ret : Ty} {body : Expr} {fvVals doneVals remArgs : List Expr}
    {σ σ' : Store} {out : Expr}
    (hσCl : ClosedStore σ) (hσDom : StoreInDom dom σ) (hout : IsTerminal out)
    (hflat : Φ2 flatName = some {
      name := flatName,
      params := fvsFresh ++ psFresh,
      retTy := ret,
      body := cloneRenameParams (fvs ++ ps) (fvsFresh ++ psFresh) body })
    (hfvVal : ∀ v ∈ fvVals, IsValue v) (hfvCl : ∀ v ∈ fvVals, freeVars v = [])
    (hfvDom : ∀ v ∈ fvVals, exprInDom dom v = true)
    (hdoneVal : ∀ v ∈ doneVals, IsValue v) (hdoneCl : ∀ v ∈ doneVals, freeVars v = [])
    (hdoneDom : ∀ v ∈ doneVals, exprInDom dom v = true)
    (hremCl : ∀ e ∈ remArgs, freeVars e = []) (hremDom : ∀ e ∈ remArgs, exprInDom dom e = true)
    (hfvLen : fvVals.length = fvs.length)
    (htotLen : (doneVals ++ remArgs).length = ps.length)
    (hfrFvLen : fvsFresh.length = fvs.length) (hfrPsLen : psFresh.length = ps.length)
    (_hdisjPsFvs : ∀ x ∈ ps.map Prod.fst, x ∉ fvs.map Prod.fst)
    (hfrNodup : ((fvsFresh ++ psFresh).map Prod.fst).Nodup)
    (hfrDisjOrig : ∀ y ∈ (fvsFresh ++ psFresh).map Prod.fst, y ∉ (fvs ++ ps).map Prod.fst)
    (hfrFreshBody : ∀ y ∈ (fvsFresh ++ psFresh).map Prod.fst, exprMentionsIdent y body = false)
    (hbodyDom : exprInDom dom body = true) :
    Steps Δ Φ1 (.apply (.lam m ps ret (substMany (zipParams fvs fvVals) body)) (doneVals ++ remArgs)) σ out σ' ↔
      Steps Δ Φ2 (.applyDir flatName ((fvVals ++ doneVals) ++ remArgs)) σ out σ' := by
  induction remArgs generalizing doneVals σ with
  | nil =>
    simp only [List.append_nil] at htotLen ⊢
    have hfvDoneVal : ∀ v ∈ fvVals ++ doneVals, IsValue v := by
      intro v hv; rcases List.mem_append.mp hv with h1 | h2
      · exact hfvVal v h1
      · exact hdoneVal v h2
    have hfvDoneCl : ∀ v ∈ fvVals ++ doneVals, freeVars v = [] := by
      intro v hv; rcases List.mem_append.mp hv with h1 | h2
      · exact hfvCl v h1
      · exact hdoneCl v h2
    have hbeta1 : ∀ σ0, Step Δ Φ1 emptyPool
        (.apply (.lam m ps ret (substMany (zipParams fvs fvVals) body)) doneVals) σ0
        (substMany (zipParams ps doneVals) (substMany (zipParams fvs fvVals) body)) σ0 .none :=
      fun _ => .applyBeta hdoneVal htotLen
    have hbeta2 : ∀ σ0, Step Δ Φ2 emptyPool
        (.applyDir flatName (fvVals ++ doneVals)) σ0
        (substMany (zipParams (fvsFresh ++ psFresh) (fvVals ++ doneVals))
          (cloneRenameParams (fvs ++ ps) (fvsFresh ++ psFresh) body)) σ0 .none :=
      fun _ => .applyDirBeta hflat hfvDoneVal (by simp [hfvLen, htotLen, hfrFvLen, hfrPsLen])
    have hclone_eq :
        substMany (zipParams (fvsFresh ++ psFresh) (fvVals ++ doneVals))
          (cloneRenameParams (fvs ++ ps) (fvsFresh ++ psFresh) body) =
        substMany (zipParams ps doneVals) (substMany (zipParams fvs fvVals) body) := by
      rw [substMany_cloneRenameParams_eq (fvs ++ ps) (fvsFresh ++ psFresh) (fvVals ++ doneVals) body
            (by simp [hfrFvLen, hfrPsLen]) (by simp [hfvLen, htotLen]) hfrNodup hfrDisjOrig
            (fun y hy => safeFreshFor_of_mentions_false body (hfrFreshBody y hy)) hfvDoneCl,
          ← substMany_lam_apply_eq_flat_capturesFirst fvs ps fvVals doneVals body hfvLen]
    have hsubDom : exprInDom dom (substMany (zipParams ps doneVals) (substMany (zipParams fvs fvVals) body)) = true := by
      apply substMany_exprInDom
      · intro q hq; exact hdoneDom q.2 (zipParams_snd_subset hq)
      · apply substMany_exprInDom
        · intro q hq; exact hfvDom q.2 (zipParams_snd_subset hq)
        · exact hbodyDom
    rw [(obsEquiv_of_det_step hbeta1) σ σ' out hout,
        (obsEquiv_of_det_step hbeta2) σ σ' out hout, hclone_eq]
    exact steps_funEnv_agree_iff hagree hΦ1dom hσDom hsubDom
  | cons e er ih =>
    have hfvDoneVal : ∀ v ∈ fvVals ++ doneVals, IsValue v := by
      intro v hv; rcases List.mem_append.mp hv with h1 | h2
      · exact hfvVal v h1
      · exact hdoneVal v h2
    have heCl : freeVars e = [] := hremCl e (List.mem_cons_self ..)
    have heDom : exprInDom dom e = true := hremDom e (List.mem_cons_self ..)
    have herCl : ∀ a ∈ er, freeVars a = [] := fun a ha => hremCl a (List.mem_cons_of_mem _ ha)
    have herDom : ∀ a ∈ er, exprInDom dom a = true := fun a ha => hremDom a (List.mem_cons_of_mem _ ha)
    rw [steps_apply_next_arg_iff hout (.lam _ _ _ _) hdoneVal,
        steps_applyDir_next_arg_iff hout hfvDoneVal]
    have htrap_iff :
        (∃ t, out = .trap t ∧ Steps Δ Φ1 e σ (.trap t) σ') ↔
          (∃ t, out = .trap t ∧ Steps Δ Φ2 e σ (.trap t) σ') := by
      constructor <;> (rintro ⟨t, rfl, htr⟩; exact ⟨t, rfl,
        by first | exact (steps_funEnv_agree_iff hagree hΦ1dom hσDom heDom).mp htr
                 | exact (steps_funEnv_agree_iff hagree hΦ1dom hσDom heDom).mpr htr⟩)
    apply or_congr htrap_iff
    constructor
    · rintro ⟨v, σ1, hv, hs1, hs_rest⟩
      rcases steps_preserves_closed hΦ1cl hσCl heCl hs1 with ⟨hvCl, hσ1Cl⟩
      rcases steps_funEnv_agree_forward hagree hΦ1dom hσDom heDom hs1 with ⟨hs2, hvDom, hσ1Dom⟩
      have hdoneVal' : ∀ w ∈ doneVals ++ [v], IsValue w := by
        intro w hw; rcases List.mem_append.mp hw with h1 | h2
        · exact hdoneVal w h1
        · simp at h2; subst h2; exact hv
      have hdoneCl' : ∀ w ∈ doneVals ++ [v], freeVars w = [] := by
        intro w hw; rcases List.mem_append.mp hw with h1 | h2
        · exact hdoneCl w h1
        · simp at h2; subst h2; exact hvCl
      have hdoneDom' : ∀ w ∈ doneVals ++ [v], exprInDom dom w = true := by
        intro w hw; rcases List.mem_append.mp hw with h1 | h2
        · exact hdoneDom w h1
        · simp at h2; subst h2; exact hvDom
      have htot' : ((doneVals ++ [v]) ++ er).length = ps.length := by simpa using htotLen
      have h2 := (ih hσ1Cl hσ1Dom hdoneVal' hdoneCl' hdoneDom' herCl herDom htot').mp hs_rest
      exact ⟨v, σ1, hv, hs2, by simpa [List.append_assoc] using h2⟩
    · rintro ⟨v, σ1, hv, hs2, hs_rest⟩
      have hs1 : Steps Δ Φ1 e σ v σ1 := (steps_funEnv_agree_iff hagree hΦ1dom hσDom heDom).mpr hs2
      rcases steps_preserves_closed hΦ1cl hσCl heCl hs1 with ⟨hvCl, hσ1Cl⟩
      rcases steps_funEnv_agree_forward hagree hΦ1dom hσDom heDom hs1 with ⟨_, hvDom, hσ1Dom⟩
      have hdoneVal' : ∀ w ∈ doneVals ++ [v], IsValue w := by
        intro w hw; rcases List.mem_append.mp hw with h1 | h2
        · exact hdoneVal w h1
        · simp at h2; subst h2; exact hv
      have hdoneCl' : ∀ w ∈ doneVals ++ [v], freeVars w = [] := by
        intro w hw; rcases List.mem_append.mp hw with h1 | h2
        · exact hdoneCl w h1
        · simp at h2; subst h2; exact hvCl
      have hdoneDom' : ∀ w ∈ doneVals ++ [v], exprInDom dom w = true := by
        intro w hw; rcases List.mem_append.mp hw with h1 | h2
        · exact hdoneDom w h1
        · simp at h2; subst h2; exact hvDom
      have htot' : ((doneVals ++ [v]) ++ er).length = ps.length := by simpa using htotLen
      have h1 := (ih hσ1Cl hσ1Dom hdoneVal' hdoneCl' hdoneDom' herCl herDom htot').mpr
        (by simpa [List.append_assoc] using hs_rest)
      exact ⟨v, σ1, hv, hs1, h1⟩

/-- **Main Captures-First `$flat$` Devirtualization Soundness (`coGetOrCreateFlatClsFn`, `src/core.gsa:5989-6030,7379`)**:
    Matches the compiler's exact ABI (`params = fvsFresh ++ psFresh`, call `fvVals ++ args`),
    fresh parameter cloning, non-value argument evaluation (`args`), and `Φ ↦ Φ'` extension! -/
theorem flat_closure_devirt_capturesFirst_full_obsEquiv {Δ : AdtEnv} {Φ1 Φ2 : FunEnv}
    {dom : Ident → Bool}
    (hagree : FunEnvAgreesOn dom Φ1 Φ2) (hΦ1dom : ClosedDomEnv dom Φ1) (hΦ1cl : ClosedFunEnv Φ1)
    {flatName : Ident} {m : Mode} {fvs ps fvsFresh psFresh : List (Ident × Ty)}
    {ret : Ty} {body : Expr} {fvVals args : List Expr}
    {σ σ' : Store} {out : Expr}
    (hσCl : ClosedStore σ) (hσDom : StoreInDom dom σ) (hout : IsTerminal out)
    (hflat : Φ2 flatName = some {
      name := flatName,
      params := fvsFresh ++ psFresh,
      retTy := ret,
      body := cloneRenameParams (fvs ++ ps) (fvsFresh ++ psFresh) body })
    (hfvVal : ∀ v ∈ fvVals, IsValue v) (hfvCl : ∀ v ∈ fvVals, freeVars v = [])
    (hfvDom : ∀ v ∈ fvVals, exprInDom dom v = true)
    (hargsCl : ∀ e ∈ args, freeVars e = []) (hargsDom : ∀ e ∈ args, exprInDom dom e = true)
    (hfvLen : fvVals.length = fvs.length) (hargsLen : args.length = ps.length)
    (hfrFvLen : fvsFresh.length = fvs.length) (hfrPsLen : psFresh.length = ps.length)
    (hdisjPsFvs : ∀ x ∈ ps.map Prod.fst, x ∉ fvs.map Prod.fst)
    (hfrNodup : ((fvsFresh ++ psFresh).map Prod.fst).Nodup)
    (hfrDisjOrig : ∀ y ∈ (fvsFresh ++ psFresh).map Prod.fst, y ∉ (fvs ++ ps).map Prod.fst)
    (hfrFreshBody : ∀ y ∈ (fvsFresh ++ psFresh).map Prod.fst, exprMentionsIdent y body = false)
    (hbodyDom : exprInDom dom body = true) :
    Steps Δ Φ1 (.apply (substMany (zipParams fvs fvVals) (.lam m ps ret body)) args) σ out σ' ↔
      Steps Δ Φ2 (.applyDir flatName (fvVals ++ args)) σ out σ' := by
  have hd : ∀ x ∈ ps.map Prod.fst, x ∉ (zipParams fvs fvVals).map Prod.fst := by
    rw [zipParams_fst_eq hfvLen]; exact hdisjPsFvs
  rw [substMany_lam_disjoint m ps ret body (zipParams fvs fvVals) hd]
  simpa using steps_apply_vs_applyDir_capturesFirst (doneVals := []) hagree hΦ1dom hΦ1cl hσCl hσDom hout hflat
    hfvVal hfvCl hfvDom (fun _ h => by cases h) (fun _ h => by cases h) (fun _ h => by cases h)
    hargsCl hargsDom hfvLen (by simpa using hargsLen) hfrFvLen hfrPsLen hdisjPsFvs
    hfrNodup hfrDisjOrig hfrFreshBody hbodyDom

/-- Concrete witness of captures-first `$flat$44($co$45$q, $co$46$u)` matching `adv.gscore:16`
    with non-value heap-mutating call argument. -/
theorem actual_adv_flat44_witness :
    let body : Expr := .bin .add (.bin .mul (.var "q") (.lit (.int 10))) (.var "u")
    let fvs : List (Ident × Ty) := [("q", .int)]
    let ps : List (Ident × Ty) := [("u", .int)]
    let fvsFresh : List (Ident × Ty) := [("$co$45$q", .int)]
    let psFresh : List (Ident × Ty) := [("$co$46$u", .int)]
    let Φ1 : FunEnv := fun _ => none
    let Φ2 : FunEnv := fun nm =>
      if nm == "fn$flat$44" then
        some { name := "fn$flat$44",
               params := fvsFresh ++ psFresh,
               retTy := .int,
               body := cloneRenameParams (fvs ++ ps) (fvsFresh ++ psFresh) body }
      else none
    let fvVals : List Expr := [.lit (.int 7)]
    let args : List Expr := [.block [.cellSet (.loc 0) (.lit (.int 99)), .lit (.int 8)]]
    Steps (fun _ => none) Φ1 (.apply (substMany (zipParams fvs fvVals) (.lam .local ps .int body)) args)
      [.lit (.int 0)] (.lit (.int 78)) [.lit (.int 99)] ∧
    Steps (fun _ => none) Φ2 (.applyDir "fn$flat$44" (fvVals ++ args))
      [.lit (.int 0)] (.lit (.int 78)) [.lit (.int 99)] := by
  let body : Expr := .bin .add (.bin .mul (.var "q") (.lit (.int 10))) (.var "u")
  let fvs : List (Ident × Ty) := [("q", .int)]
  let ps : List (Ident × Ty) := [("u", .int)]
  let fvsFresh : List (Ident × Ty) := [("$co$45$q", .int)]
  let psFresh : List (Ident × Ty) := [("$co$46$u", .int)]
  let Φ1 : FunEnv := fun _ => none
  let Φ2 : FunEnv := fun nm =>
    if nm == "fn$flat$44" then
      some { name := "fn$flat$44",
             params := fvsFresh ++ psFresh,
             retTy := .int,
             body := cloneRenameParams (fvs ++ ps) (fvsFresh ++ psFresh) body }
    else none
  let fvVals : List Expr := [.lit (.int 7)]
  let args : List Expr := [.block [.cellSet (.loc 0) (.lit (.int 99)), .lit (.int 8)]]
  have h1 : Steps (fun _ => none) Φ1 (.apply (substMany (zipParams fvs fvVals) (.lam .local ps .int body)) args)
      [.lit (.int 0)] (.lit (.int 78)) [.lit (.int 99)] := by
    refine .trans (.applyArgs (.lam _ _ _ _) (.head (.blockConsStep (.cellSetVal (by decide) (.lit _))))) ?_
    refine .trans (.applyArgs (.lam _ _ _ _) (.head (.blockConsVal (.lit _)))) ?_
    refine .trans (.applyArgs (.lam _ _ _ _) (.head .blockSingle)) ?_
    refine .trans (.applyBeta (fun v hv => by simp at hv; subst hv; exact .lit _) rfl) ?_
    refine .trans (.binLeft (.binVal rfl)) ?_
    exact .single (.binVal rfl)
  have h2 := (flat_closure_devirt_capturesFirst_full_obsEquiv
    (Φ1 := Φ1) (Φ2 := Φ2) (dom := fun _ => false)
    (fvsFresh := fvsFresh) (psFresh := psFresh)
    (fun _ h => by cases h)
    (fun _ _ h => by cases h)
    (fun _ _ h => by cases h)
    (fun v hv => by simp at hv; subst hv; rfl)
    (fun v hv => by simp at hv; subst hv; rfl)
    (Or.inl (.lit _))
    (flatName := "fn$flat$44") rfl
    (fun v hv => by simp [fvVals] at hv; subst hv; exact .lit _)
    (fun v hv => by simp [fvVals] at hv; subst hv; rfl)
    (fun v hv => by simp [fvVals] at hv; subst hv; rfl)
    (fun e he => by simp [args] at he; subst he; rfl)
    (fun e he => by simp [args] at he; subst he; rfl)
    rfl rfl rfl rfl
    (by decide) (by decide) (by decide)
    (by decide)
    rfl).mp h1
  exact ⟨h1, h2⟩

/-! ## Part 8: Positional Multi-Callback `$spec$` (`PositionalLoopSpec` covering `foldSepLoop`, `listFold` & `specLoopColl`) -/

inductive CbLowerKind where
  | flatDir (flatName : Ident)
  | inline1 (inlParam : Ident)

structure CbSlotSpec where
  fParam   : Ident
  fnTy     : Ty
  cbMode   : Mode
  cbParams : List (Ident × Ty)
  cbRet    : Ty
  cbBody   : Expr
  fvs      : List (Ident × Ty)
  fvVals   : List Expr
  lowering : CbLowerKind

def CbSlotSpec.cls (c : CbSlotSpec) : Expr :=
  substMany (zipParams c.fvs c.fvVals) (.lam c.cbMode c.cbParams c.cbRet c.cbBody)

inductive PosSpecSlot where
  | state (param : Ident × Ty)
  | callback (cb : CbSlotSpec)

def posOrigParams : List PosSpecSlot → List (Ident × Ty)
  | [] => []
  | .state p :: r => p :: posOrigParams r
  | .callback c :: r => (c.fParam, c.fnTy) :: posOrigParams r

def posSpecParams : List PosSpecSlot → List (Ident × Ty)
  | [] => []
  | .state p :: r => p :: posSpecParams r
  | .callback c :: r => c.fvs ++ posSpecParams r

def cbSlotsOf : List PosSpecSlot → List CbSlotSpec
  | [] => []
  | .state _ :: r => cbSlotsOf r
  | .callback c :: r => c :: cbSlotsOf r

def slotExpansionMask : List PosSpecSlot → List (Option (List Expr))
  | [] => []
  | .state _ :: r => none :: slotExpansionMask r
  | .callback c :: r => some ((c.fvs.map Prod.fst).map .var) :: slotExpansionMask r

def expandArgsByMask : List (Option (List Expr)) → List Expr → List Expr
  | none :: mr, a :: ar => a :: expandArgsByMask mr ar
  | some fvs :: mr, _ :: ar => fvs ++ expandArgsByMask mr ar
  | _, _ => []

def findCbSlot? (f : Ident) : List PosSpecSlot → Option CbSlotSpec
  | [] => none
  | .state _ :: r => findCbSlot? f r
  | .callback c :: r => if c.fParam == f then some c else findCbSlot? f r

def lowerCbCallExpr (c : CbSlotSpec) (cbArgs' : List Expr) : Expr :=
  match c.lowering, c.cbParams, cbArgs' with
  | .flatDir flatName, _, _ =>
    .applyDir flatName ((c.fvs.map Prod.fst).map .var ++ cbArgs')
  | .inline1 inlP, [(origP, _)], [arg'] =>
    .let_ inlP arg' (subst origP (.var inlP) c.cbBody)
  | _, _, _ => .apply (.var c.fParam) cbArgs'

/- Exact positional multi-callback loop body rewriter matching `coRewriteSelfCallsInSpecBody`
   (`src/core.gsa:6407` `nm == origFn && args.length == slots.length`) + callback lowering (`$flat$` or inline). -/
mutual
def posSpecializeLoopExpr (origFn specFn : Ident) (slots : List PosSpecSlot) : Expr → Expr
  | .lit l => .lit l
  | .var x => .var x
  | .loc l => .loc l
  | .taskRef tid => .taskRef tid
  | .syncRef k id => .syncRef k id
  | .tuple es => .tuple (posSpecializeLoopList origFn specFn slots es)
  | .block es => .block (posSpecializeLoopList origFn specFn slots es)
  | .lam m ps ret body => .lam m ps ret body
  | .apply fn args =>
    let fn' := posSpecializeLoopExpr origFn specFn slots fn
    let args' := posSpecializeLoopList origFn specFn slots args
    match fn with
    | .var f =>
      match findCbSlot? f slots with
      | some c => lowerCbCallExpr c args'
      | none => .apply (.var f) args'
    | _ => .apply fn' args'
  | .applyDir nm args =>
    let args' := posSpecializeLoopList origFn specFn slots args
    if nm == origFn && args.length == slots.length then
      .applyDir specFn (expandArgsByMask (slotExpansionMask slots) args')
    else
      .applyDir nm args'
  | .bin op a b =>
    .bin op (posSpecializeLoopExpr origFn specFn slots a)
      (posSpecializeLoopExpr origFn specFn slots b)
  | .un op a => .un op (posSpecializeLoopExpr origFn specFn slots a)
  | .let_ x a b =>
    .let_ x (posSpecializeLoopExpr origFn specFn slots a)
      (posSpecializeLoopExpr origFn specFn slots b)
  | .if_ c t e2 =>
    .if_ (posSpecializeLoopExpr origFn specFn slots c)
      (posSpecializeLoopExpr origFn specFn slots t)
      (posSpecializeLoopExpr origFn specFn slots e2)
  | .while_ c b =>
    .while_ (posSpecializeLoopExpr origFn specFn slots c)
      (posSpecializeLoopExpr origFn specFn slots b)
  | .match_ s arms =>
    .match_ (posSpecializeLoopExpr origFn specFn slots s)
      (posSpecializeLoopArms origFn specFn slots arms)
  | .makeData adt tag es =>
    .makeData adt tag (posSpecializeLoopList origFn specFn slots es)
  | .getTag a => .getTag (posSpecializeLoopExpr origFn specFn slots a)
  | .cellNew a => .cellNew (posSpecializeLoopExpr origFn specFn slots a)
  | .cellGet a => .cellGet (posSpecializeLoopExpr origFn specFn slots a)
  | .cellSet a b =>
    .cellSet (posSpecializeLoopExpr origFn specFn slots a)
      (posSpecializeLoopExpr origFn specFn slots b)
  | .spawn a => .spawn (posSpecializeLoopExpr origFn specFn slots a)
  | .await a => .await (posSpecializeLoopExpr origFn specFn slots a)
  | .concPrim op es => .concPrim op (posSpecializeLoopList origFn specFn slots es)
  | .trap t => .trap t

def posSpecializeLoopList (origFn specFn : Ident) (slots : List PosSpecSlot) : List Expr → List Expr
  | [] => []
  | e :: es => posSpecializeLoopExpr origFn specFn slots e :: posSpecializeLoopList origFn specFn slots es

def posSpecializeLoopArms (origFn specFn : Ident) (slots : List PosSpecSlot) :
    List (Pat × Expr) → List (Pat × Expr)
  | [] => []
  | (p, b) :: r => (p, posSpecializeLoopExpr origFn specFn slots b) :: posSpecializeLoopArms origFn specFn slots r
end

/-- **Non-Vacuity Counterexample (`unguarded_posSpecialize_varyLoop_counterexample`)**:
    Demonstrates directly on `posSpecializeLoopExpr` (which mirrors `coRewriteSelfCallsInSpecBody`
    at `src/core.gsa:6407`) that if `coParamInvariantAndOnlyCalledInTerm` (`src/core.gsa:6253,6275`)
    is omitted on `varyLoop(f, n)` (whose self-call passes `x ↦ x + 100` instead of `f`),
    `posSpecializeLoopExpr` itself produces a specialized body returning `1` instead of `100`! -/
theorem unguarded_posSpecialize_varyLoop_counterexample :
    let origBody : Expr :=
      .if_ (.bin .leInt (.var "n") (.lit (.int 0)))
        (.apply (.var "f") [.lit (.int 0)])
        (.applyDir "varyLoop"
          [.lam .local [("x", .int)] .int (.bin .add (.var "x") (.lit (.int 100))),
           .bin .sub (.var "n") (.lit (.int 1))])
    let cb : CbSlotSpec := {
      fParam := "f", fnTy := .fn .local [.int] .int, cbMode := .local,
      cbParams := [("x", .int)], cbRet := .int,
      cbBody := .bin .add (.var "x") (.lit (.int 1)),
      fvs := [], fvVals := [], lowering := .inline1 "$co$0$x"
    }
    let slots : List PosSpecSlot := [.callback cb, .state ("n", .int)]
    let badSpecBody : Expr := posSpecializeLoopExpr "varyLoop" "varyLoop$badSpec" slots origBody
    let Φ : FunEnv := fun nm =>
      if nm == "varyLoop" then
        some { name := "varyLoop", params := posOrigParams slots, retTy := .int, body := origBody }
      else if nm == "varyLoop$badSpec" then
        some { name := "varyLoop$badSpec", params := posSpecParams slots, retTy := .int, body := badSpecBody }
      else none
    Steps (fun _ => none) Φ (.applyDir "varyLoop" [cb.cls, .lit (.int 1)]) [] (.lit (.int 100)) [] ∧
    Steps (fun _ => none) Φ (.applyDir "varyLoop$badSpec" [.lit (.int 1)]) [] (.lit (.int 1)) [] ∧
    ¬ ObsEquiv (fun _ => none) Φ Φ
        (.applyDir "varyLoop" [cb.cls, .lit (.int 1)])
        (.applyDir "varyLoop$badSpec" [.lit (.int 1)]) := by
  let origBody : Expr :=
    .if_ (.bin .leInt (.var "n") (.lit (.int 0)))
      (.apply (.var "f") [.lit (.int 0)])
      (.applyDir "varyLoop"
        [.lam .local [("x", .int)] .int (.bin .add (.var "x") (.lit (.int 100))),
         .bin .sub (.var "n") (.lit (.int 1))])
  let cb : CbSlotSpec := {
    fParam := "f", fnTy := .fn .local [.int] .int, cbMode := .local,
    cbParams := [("x", .int)], cbRet := .int,
    cbBody := .bin .add (.var "x") (.lit (.int 1)),
    fvs := [], fvVals := [], lowering := .inline1 "$co$0$x"
  }
  let slots : List PosSpecSlot := [.callback cb, .state ("n", .int)]
  let badSpecBody : Expr := posSpecializeLoopExpr "varyLoop" "varyLoop$badSpec" slots origBody
  let Φ : FunEnv := fun nm =>
    if nm == "varyLoop" then
      some { name := "varyLoop", params := posOrigParams slots, retTy := .int, body := origBody }
    else if nm == "varyLoop$badSpec" then
      some { name := "varyLoop$badSpec", params := posSpecParams slots, retTy := .int, body := badSpecBody }
    else none
  have hbad_eq : badSpecBody =
      .if_ (.bin .leInt (.var "n") (.lit (.int 0)))
        (.let_ "$co$0$x" (.lit (.int 0)) (.bin .add (.var "$co$0$x") (.lit (.int 1))))
        (.applyDir "varyLoop$badSpec" [.bin .sub (.var "n") (.lit (.int 1))]) := by
    simp [badSpecBody, origBody, slots, cb, posSpecializeLoopExpr, posSpecializeLoopList,
      findCbSlot?, lowerCbCallExpr, slotExpansionMask, expandArgsByMask, subst]
  have hv_init : ∀ v ∈ ([cb.cls, .lit (.int 1)] : List Expr), IsValue v := by
    intro v hv; rcases List.mem_cons.mp hv with rfl | h2
    · exact .lam _ _ _ _
    · rcases List.mem_cons.mp h2 with rfl | h3
      · exact .lit _
      · cases h3
  have hv_rec : ∀ v ∈ ([.lam .local [("x", .int)] .int (.bin .add (.var "x") (.lit (.int 100))), .lit (.int 0)] : List Expr), IsValue v := by
    intro v hv; rcases List.mem_cons.mp hv with rfl | h2
    · exact .lam _ _ _ _
    · rcases List.mem_cons.mp h2 with rfl | h3
      · exact .lit _
      · cases h3
  have hv_1 : ∀ v ∈ ([.lit (.int 1)] : List Expr), IsValue v := by
    intro v hv; rcases List.mem_cons.mp hv with rfl | h
    · exact .lit _
    · cases h
  have hv_0 : ∀ v ∈ ([.lit (.int 0)] : List Expr), IsValue v := by
    intro v hv; rcases List.mem_cons.mp hv with rfl | h
    · exact .lit _
    · cases h
  have h1 : Steps (fun _ => none) Φ (.applyDir "varyLoop" [cb.cls, .lit (.int 1)]) [] (.lit (.int 100)) [] := by
    refine .trans (.applyDirBeta rfl hv_init rfl) ?_
    refine .trans (.ifStep (.binVal rfl)) ?_
    refine .trans .ifFalse ?_
    refine .trans (.applyDirArgs (.tail (.lam _ _ _ _) (.head (.binVal rfl)))) ?_
    refine .trans (.applyDirBeta rfl hv_rec rfl) ?_
    refine .trans (.ifStep (.binVal rfl)) ?_
    refine .trans .ifTrue ?_
    refine .trans (.applyBeta hv_0 rfl) ?_
    exact .single (.binVal rfl)
  have hfd_bad : Φ "varyLoop$badSpec" = some {
      name := "varyLoop$badSpec", params := [("n", .int)], retTy := .int,
      body := .if_ (.bin .leInt (.var "n") (.lit (.int 0)))
        (.let_ "$co$0$x" (.lit (.int 0)) (.bin .add (.var "$co$0$x") (.lit (.int 1))))
        (.applyDir "varyLoop$badSpec" [.bin .sub (.var "n") (.lit (.int 1))]) } := by
    simp [Φ, posSpecParams, slots, cb, hbad_eq]
  have h2 : Steps (fun _ => none) Φ (.applyDir "varyLoop$badSpec" [.lit (.int 1)]) [] (.lit (.int 1)) [] := by
    refine .trans (.applyDirBeta hfd_bad hv_1 rfl) ?_
    refine .trans (.ifStep (.binVal rfl)) ?_
    refine .trans .ifFalse ?_
    refine .trans (.applyDirArgs (.head (.binVal rfl))) ?_
    refine .trans (.applyDirBeta hfd_bad hv_0 rfl) ?_
    refine .trans (.ifStep (.binVal rfl)) ?_
    refine .trans .ifTrue ?_
    refine .trans (.letVal (.lit _)) ?_
    exact .single (.binVal rfl)
  exact ⟨h1, h2, not_obsEquiv_of_distinct_terminals h1 (Or.inl (.lit _)) h2 (Or.inl (.lit _))
    (Or.inl (by rintro ⟨⟩))⟩

/- Eligibility predicate `PosSpecEligible` mirroring `coParamInvariantAndOnlyCalledInTerm`
   (`src/core.gsa:6253,6275`) across arbitrary callback positions and multiplicities! -/
mutual
inductive PosSpecEligible (origFn : Ident) (slots : List PosSpecSlot) (avoid : List Ident) :
    Expr → Prop where
  | lit (l : Lit) : PosSpecEligible origFn slots avoid (.lit l)
  | var {x : Ident} :
      findCbSlot? x slots = none →
      PosSpecEligible origFn slots avoid (.var x)
  | loc (l : Loc) : PosSpecEligible origFn slots avoid (.loc l)
  | taskRef (tid : TaskId) : PosSpecEligible origFn slots avoid (.taskRef tid)
  | syncRef (k : SyncKind) (id : Nat) : PosSpecEligible origFn slots avoid (.syncRef k id)
  | trap (t : Trap) : PosSpecEligible origFn slots avoid (.trap t)
  | lam {m : Mode} {ps : List (Ident × Ty)} {ret : Ty} {body : Expr} :
      (∀ c ∈ cbSlotsOf slots, c.fParam ∉ freeVars (.lam m ps ret body)) →
      (∀ z ∈ ps.map Prod.fst, z ∉ avoid) →
      PosSpecEligible origFn slots avoid (.lam m ps ret body)
  | tuple {es : List Expr} :
      PosSpecEligibleList origFn slots avoid es →
      PosSpecEligible origFn slots avoid (.tuple es)
  | block {es : List Expr} :
      PosSpecEligibleList origFn slots avoid es →
      PosSpecEligible origFn slots avoid (.block es)
  | cbCallFlat {f : Ident} {c : CbSlotSpec} {flatName : Ident} {cbArgs : List Expr} :
      findCbSlot? f slots = some c →
      c.lowering = .flatDir flatName →
      cbArgs.length = c.cbParams.length →
      PosSpecEligibleList origFn slots avoid cbArgs →
      PosSpecEligible origFn slots avoid (.apply (.var f) cbArgs)
  | cbCallInline1 {f : Ident} {c : CbSlotSpec} {inlP origP : Ident} {pTy : Ty} {arg : Expr} :
      findCbSlot? f slots = some c →
      c.lowering = .inline1 inlP →
      c.cbParams = [(origP, pTy)] →
      PosSpecEligible origFn slots avoid arg →
      PosSpecEligible origFn slots avoid (.apply (.var f) [arg])
  | applyGen {fn : Expr} {args : List Expr} :
      (∀ z, fn = .var z → findCbSlot? z slots = none) →
      PosSpecEligible origFn slots avoid fn →
      PosSpecEligibleList origFn slots avoid args →
      PosSpecEligible origFn slots avoid (.apply fn args)
  | selfCall {recArgs : List Expr} :
      PosSelfCallArgs origFn slots avoid slots recArgs →
      PosSpecEligible origFn slots avoid (.applyDir origFn recArgs)
  | applyDirOther {nm : Ident} {args : List Expr} :
      nm ≠ origFn →
      PosSpecEligibleList origFn slots avoid args →
      PosSpecEligible origFn slots avoid (.applyDir nm args)
  | bin {op : BinOp} {a b : Expr} :
      PosSpecEligible origFn slots avoid a →
      PosSpecEligible origFn slots avoid b →
      PosSpecEligible origFn slots avoid (.bin op a b)
  | un {op : UnOp} {a : Expr} :
      PosSpecEligible origFn slots avoid a →
      PosSpecEligible origFn slots avoid (.un op a)
  | let_ {y : Ident} {a b : Expr} :
      y ∉ avoid →
      PosSpecEligible origFn slots avoid a →
      PosSpecEligible origFn slots avoid b →
      PosSpecEligible origFn slots avoid (.let_ y a b)
  | if_ {c t e2 : Expr} :
      PosSpecEligible origFn slots avoid c →
      PosSpecEligible origFn slots avoid t →
      PosSpecEligible origFn slots avoid e2 →
      PosSpecEligible origFn slots avoid (.if_ c t e2)
  | while_ {c b : Expr} :
      PosSpecEligible origFn slots avoid c →
      PosSpecEligible origFn slots avoid b →
      PosSpecEligible origFn slots avoid (.while_ c b)
  | match_ {s : Expr} {arms : List (Pat × Expr)} :
      PosSpecEligible origFn slots avoid s →
      PosSpecEligibleArms origFn slots avoid arms →
      PosSpecEligible origFn slots avoid (.match_ s arms)
  | makeData {adt : Ident} {tag : Nat} {es : List Expr} :
      PosSpecEligibleList origFn slots avoid es →
      PosSpecEligible origFn slots avoid (.makeData adt tag es)
  | getTag {a : Expr} : PosSpecEligible origFn slots avoid a → PosSpecEligible origFn slots avoid (.getTag a)
  | cellNew {a : Expr} : PosSpecEligible origFn slots avoid a → PosSpecEligible origFn slots avoid (.cellNew a)
  | cellGet {a : Expr} : PosSpecEligible origFn slots avoid a → PosSpecEligible origFn slots avoid (.cellGet a)
  | cellSet {a b : Expr} :
      PosSpecEligible origFn slots avoid a →
      PosSpecEligible origFn slots avoid b →
      PosSpecEligible origFn slots avoid (.cellSet a b)

inductive PosSpecEligibleList (origFn : Ident) (slots : List PosSpecSlot) (avoid : List Ident) :
    List Expr → Prop where
  | nil : PosSpecEligibleList origFn slots avoid []
  | cons {e : Expr} {es : List Expr} :
      PosSpecEligible origFn slots avoid e →
      PosSpecEligibleList origFn slots avoid es →
      PosSpecEligibleList origFn slots avoid (e :: es)

inductive PosSpecEligibleArms (origFn : Ident) (slots : List PosSpecSlot) (avoid : List Ident) :
    List (Pat × Expr) → Prop where
  | nil : PosSpecEligibleArms origFn slots avoid []
  | cons {p : Pat} {b : Expr} {r : List (Pat × Expr)} :
      (∀ z ∈ patBoundNames p, z ∉ avoid) →
      PosSpecEligible origFn slots avoid b →
      PosSpecEligibleArms origFn slots avoid r →
      PosSpecEligibleArms origFn slots avoid ((p, b) :: r)

inductive PosSelfCallArgs (origFn : Ident) (slots : List PosSpecSlot) (avoid : List Ident) :
    List PosSpecSlot → List Expr → Prop where
  | nil : PosSelfCallArgs origFn slots avoid [] []
  | state (p : Ident × Ty) {rem : List PosSpecSlot} {e : Expr} {rest : List Expr} :
      PosSpecEligible origFn slots avoid e →
      PosSelfCallArgs origFn slots avoid rem rest →
      PosSelfCallArgs origFn slots avoid (.state p :: rem) (e :: rest)
  | callback (c : CbSlotSpec) {rem : List PosSpecSlot} {rest : List Expr} :
      PosSelfCallArgs origFn slots avoid rem rest →
      PosSelfCallArgs origFn slots avoid (.callback c :: rem) (.var c.fParam :: rest)
end

/- Lockstep bisimulation relation `PosSpecRel` across arbitrary callback positions,
   multiple callbacks, captures-first `.flatDir` calls, and `.inline1` inlined callbacks. -/
mutual
inductive PosSpecRel (origFn specFn : Ident) (slots : List PosSpecSlot) : Expr → Expr → Prop where
  | lit (l : Lit) : PosSpecRel origFn specFn slots (.lit l) (.lit l)
  | var (x : Ident) : PosSpecRel origFn specFn slots (.var x) (.var x)
  | loc (l : Loc) : PosSpecRel origFn specFn slots (.loc l) (.loc l)
  | taskRef (tid : TaskId) : PosSpecRel origFn specFn slots (.taskRef tid) (.taskRef tid)
  | syncRef (k : SyncKind) (id : Nat) : PosSpecRel origFn specFn slots (.syncRef k id) (.syncRef k id)
  | lam (m : Mode) (ps : List (Ident × Ty)) (ret : Ty) (body : Expr) :
      PosSpecRel origFn specFn slots (.lam m ps ret body) (.lam m ps ret body)
  | trap (t : Trap) : PosSpecRel origFn specFn slots (.trap t) (.trap t)
  | tuple {es1 es2 : List Expr} :
      PosSpecRelList origFn specFn slots es1 es2 →
      PosSpecRel origFn specFn slots (.tuple es1) (.tuple es2)
  | block {es1 es2 : List Expr} :
      PosSpecRelList origFn specFn slots es1 es2 →
      PosSpecRel origFn specFn slots (.block es1) (.block es2)
  | specCbFlat {c : CbSlotSpec} {flatName : Ident} {args1 args2 : List Expr} :
      c ∈ cbSlotsOf slots →
      c.lowering = .flatDir flatName →
      args1.length = c.cbParams.length →
      PosSpecRelList origFn specFn slots args1 args2 →
      PosSpecRel origFn specFn slots (.apply c.cls args1) (.applyDir flatName (c.fvVals ++ args2))
  | specCbInline1 {c : CbSlotSpec} {inlP origP : Ident} {pTy : Ty} {arg1 arg2 : Expr} :
      c ∈ cbSlotsOf slots →
      c.lowering = .inline1 inlP →
      c.cbParams = [(origP, pTy)] →
      PosSpecRel origFn specFn slots arg1 arg2 →
      PosSpecRel origFn specFn slots (.apply c.cls [arg1])
        (.let_ inlP arg2 (substMany (zipParams c.fvs c.fvVals) (subst origP (.var inlP) c.cbBody)))
  | apply {fn1 fn2 : Expr} {args1 args2 : List Expr} :
      PosSpecRel origFn specFn slots fn1 fn2 →
      PosSpecRelList origFn specFn slots args1 args2 →
      PosSpecRel origFn specFn slots (.apply fn1 args1) (.apply fn2 args2)
  | specSelfCall {args1 args2 : List Expr} :
      PosCallArgsRel origFn specFn slots slots args1 args2 →
      PosSpecRel origFn specFn slots (.applyDir origFn args1) (.applyDir specFn args2)
  | applyDir {nm : Ident} {args1 args2 : List Expr} :
      PosSpecRelList origFn specFn slots args1 args2 →
      PosSpecRel origFn specFn slots (.applyDir nm args1) (.applyDir nm args2)
  | bin {op : BinOp} {a1 a2 b1 b2 : Expr} :
      PosSpecRel origFn specFn slots a1 a2 →
      PosSpecRel origFn specFn slots b1 b2 →
      PosSpecRel origFn specFn slots (.bin op a1 b1) (.bin op a2 b2)
  | un {op : UnOp} {a1 a2 : Expr} :
      PosSpecRel origFn specFn slots a1 a2 →
      PosSpecRel origFn specFn slots (.un op a1) (.un op a2)
  | let_ {x : Ident} {a1 a2 b1 b2 : Expr} :
      PosSpecRel origFn specFn slots a1 a2 →
      PosSpecRel origFn specFn slots b1 b2 →
      PosSpecRel origFn specFn slots (.let_ x a1 b1) (.let_ x a2 b2)
  | if_ {c1 c2 t1 t2 e1 e2 : Expr} :
      PosSpecRel origFn specFn slots c1 c2 →
      PosSpecRel origFn specFn slots t1 t2 →
      PosSpecRel origFn specFn slots e1 e2 →
      PosSpecRel origFn specFn slots (.if_ c1 t1 e1) (.if_ c2 t2 e2)
  | while_ {c1 c2 b1 b2 : Expr} :
      PosSpecRel origFn specFn slots c1 c2 →
      PosSpecRel origFn specFn slots b1 b2 →
      PosSpecRel origFn specFn slots (.while_ c1 b1) (.while_ c2 b2)
  | match_ {s1 s2 : Expr} {arms1 arms2 : List (Pat × Expr)} :
      PosSpecRel origFn specFn slots s1 s2 →
      PosSpecRelArms origFn specFn slots arms1 arms2 →
      PosSpecRel origFn specFn slots (.match_ s1 arms1) (.match_ s2 arms2)
  | makeData {adt : Ident} {tag : Nat} {es1 es2 : List Expr} :
      PosSpecRelList origFn specFn slots es1 es2 →
      PosSpecRel origFn specFn slots (.makeData adt tag es1) (.makeData adt tag es2)
  | getTag {a1 a2 : Expr} :
      PosSpecRel origFn specFn slots a1 a2 →
      PosSpecRel origFn specFn slots (.getTag a1) (.getTag a2)
  | cellNew {a1 a2 : Expr} :
      PosSpecRel origFn specFn slots a1 a2 →
      PosSpecRel origFn specFn slots (.cellNew a1) (.cellNew a2)
  | cellGet {a1 a2 : Expr} :
      PosSpecRel origFn specFn slots a1 a2 →
      PosSpecRel origFn specFn slots (.cellGet a1) (.cellGet a2)
  | cellSet {a1 a2 b1 b2 : Expr} :
      PosSpecRel origFn specFn slots a1 a2 →
      PosSpecRel origFn specFn slots b1 b2 →
      PosSpecRel origFn specFn slots (.cellSet a1 b1) (.cellSet a2 b2)
  | spawn {a1 a2 : Expr} :
      PosSpecRel origFn specFn slots a1 a2 →
      PosSpecRel origFn specFn slots (.spawn a1) (.spawn a2)
  | await {a1 a2 : Expr} :
      PosSpecRel origFn specFn slots a1 a2 →
      PosSpecRel origFn specFn slots (.await a1) (.await a2)
  | concPrim {op : ConcPrim} {es1 es2 : List Expr} :
      PosSpecRelList origFn specFn slots es1 es2 →
      PosSpecRel origFn specFn slots (.concPrim op es1) (.concPrim op es2)

inductive PosSpecRelList (origFn specFn : Ident) (slots : List PosSpecSlot) :
    List Expr → List Expr → Prop where
  | nil : PosSpecRelList origFn specFn slots [] []
  | cons {e1 e2 : Expr} {es1 es2 : List Expr} :
      PosSpecRel origFn specFn slots e1 e2 →
      PosSpecRelList origFn specFn slots es1 es2 →
      PosSpecRelList origFn specFn slots (e1 :: es1) (e2 :: es2)

inductive PosSpecRelArms (origFn specFn : Ident) (slots : List PosSpecSlot) :
    List (Pat × Expr) → List (Pat × Expr) → Prop where
  | nil : PosSpecRelArms origFn specFn slots [] []
  | cons {p : Pat} {b1 b2 : Expr} {r1 r2 : List (Pat × Expr)} :
      PosSpecRel origFn specFn slots b1 b2 →
      PosSpecRelArms origFn specFn slots r1 r2 →
      PosSpecRelArms origFn specFn slots ((p, b1) :: r1) ((p, b2) :: r2)

inductive PosCallArgsRel (origFn specFn : Ident) (slots : List PosSpecSlot) :
    List PosSpecSlot → List Expr → List Expr → Prop where
  | nil : PosCallArgsRel origFn specFn slots [] [] []
  | state (p : Ident × Ty) {rem : List PosSpecSlot} {e1 e2 : Expr} {r1 r2 : List Expr} :
      PosSpecRel origFn specFn slots e1 e2 →
      PosCallArgsRel origFn specFn slots rem r1 r2 →
      PosCallArgsRel origFn specFn slots (.state p :: rem) (e1 :: r1) (e2 :: r2)
  | callback (c : CbSlotSpec) {rem : List PosSpecSlot} {r1 r2 : List Expr} :
      PosCallArgsRel origFn specFn slots rem r1 r2 →
      PosCallArgsRel origFn specFn slots (.callback c :: rem) (c.cls :: r1) (c.fvVals ++ r2)
end

mutual
theorem PosSpecRel.refl (origFn specFn : Ident) (slots : List PosSpecSlot) :
    (e : Expr) → PosSpecRel origFn specFn slots e e
  | .lit l => .lit l
  | .var x => .var x
  | .loc l => .loc l
  | .taskRef tid => .taskRef tid
  | .syncRef k id => .syncRef k id
  | .lam m ps ret body => .lam m ps ret body
  | .trap t => .trap t
  | .tuple es => .tuple (PosSpecRelList.refl origFn specFn slots es)
  | .block es => .block (PosSpecRelList.refl origFn specFn slots es)
  | .apply fn args =>
    .apply (PosSpecRel.refl origFn specFn slots fn) (PosSpecRelList.refl origFn specFn slots args)
  | .applyDir nm args => .applyDir (PosSpecRelList.refl origFn specFn slots args)
  | .bin _ a b => .bin (PosSpecRel.refl origFn specFn slots a) (PosSpecRel.refl origFn specFn slots b)
  | .un _ a => .un (PosSpecRel.refl origFn specFn slots a)
  | .let_ _ a b => .let_ (PosSpecRel.refl origFn specFn slots a) (PosSpecRel.refl origFn specFn slots b)
  | .if_ c t e2 =>
    .if_ (PosSpecRel.refl origFn specFn slots c)
      (PosSpecRel.refl origFn specFn slots t) (PosSpecRel.refl origFn specFn slots e2)
  | .while_ c b =>
    .while_ (PosSpecRel.refl origFn specFn slots c) (PosSpecRel.refl origFn specFn slots b)
  | .match_ s arms =>
    .match_ (PosSpecRel.refl origFn specFn slots s) (PosSpecRelArms.refl origFn specFn slots arms)
  | .makeData _ _ es => .makeData (PosSpecRelList.refl origFn specFn slots es)
  | .getTag a => .getTag (PosSpecRel.refl origFn specFn slots a)
  | .cellNew a => .cellNew (PosSpecRel.refl origFn specFn slots a)
  | .cellGet a => .cellGet (PosSpecRel.refl origFn specFn slots a)
  | .cellSet a b =>
    .cellSet (PosSpecRel.refl origFn specFn slots a) (PosSpecRel.refl origFn specFn slots b)
  | .spawn a => .spawn (PosSpecRel.refl origFn specFn slots a)
  | .await a => .await (PosSpecRel.refl origFn specFn slots a)
  | .concPrim _ es => .concPrim (PosSpecRelList.refl origFn specFn slots es)
termination_by e => sizeOf e

theorem PosSpecRelList.refl (origFn specFn : Ident) (slots : List PosSpecSlot) :
    (es : List Expr) → PosSpecRelList origFn specFn slots es es
  | [] => .nil
  | e :: r => .cons (PosSpecRel.refl origFn specFn slots e) (PosSpecRelList.refl origFn specFn slots r)
termination_by es => sizeOf es

theorem PosSpecRelArms.refl (origFn specFn : Ident) (slots : List PosSpecSlot) :
    (arms : List (Pat × Expr)) → PosSpecRelArms origFn specFn slots arms arms
  | [] => .nil
  | (_, b) :: r => .cons (PosSpecRel.refl origFn specFn slots b) (PosSpecRelArms.refl origFn specFn slots r)
termination_by arms => sizeOf arms
end

mutual
theorem posSpecRel_val_left {origFn specFn : Ident} {slots : List PosSpecSlot} {e1 e2 : Expr}
    (hr : PosSpecRel origFn specFn slots e1 e2) (hv1 : IsValue e1) : e1 = e2 ∧ IsValue e2 := by
  cases hr with
  | lit _ | loc _ | taskRef _ | syncRef _ _ | lam _ _ _ _ => exact ⟨rfl, hv1⟩
  | tuple hrl =>
    cases hv1 with
    | tuple hvs1 =>
      rcases posSpecRelList_val_left hrl hvs1 with ⟨rfl, hvs2⟩
      exact ⟨rfl, .tuple hvs2⟩
  | @makeData adt tag _ _ hrl =>
    cases hv1 with
    | makeData _ _ hvs1 =>
      rcases posSpecRelList_val_left hrl hvs1 with ⟨rfl, hvs2⟩
      exact ⟨rfl, .makeData adt tag hvs2⟩
  | var _ | trap _ | block _ | specCbFlat _ _ _ _ | specCbInline1 _ _ _ _
  | apply _ _ | specSelfCall _ | applyDir _ | bin _ _ | un _ | let_ _ _
  | if_ _ _ _ | while_ _ _ | match_ _ _ | getTag _ | cellNew _ | cellGet _
  | cellSet _ _ | spawn _ | await _ | concPrim _ => cases hv1
termination_by sizeOf e1

theorem posSpecRelList_val_left {origFn specFn : Ident} {slots : List PosSpecSlot} {es1 es2 : List Expr}
    (hrl : PosSpecRelList origFn specFn slots es1 es2)
    (hvs1 : ∀ v ∈ es1, IsValue v) : es1 = es2 ∧ (∀ v ∈ es2, IsValue v) := by
  cases hrl with
  | nil => exact ⟨rfl, fun _ h => by cases h⟩
  | cons hr hrs =>
    rcases posSpecRel_val_left hr (hvs1 _ (List.mem_cons_self ..)) with ⟨rfl, hv2⟩
    rcases posSpecRelList_val_left hrs (fun x hx => hvs1 x (List.mem_cons_of_mem _ hx)) with ⟨rfl, hvs2⟩
    exact ⟨rfl, fun x hx => by rcases List.mem_cons.mp hx with rfl | hxr; exact hv2; exact hvs2 x hxr⟩
termination_by sizeOf es1
end

mutual
theorem posSpecRel_val_right {origFn specFn : Ident} {slots : List PosSpecSlot} {e1 e2 : Expr}
    (hr : PosSpecRel origFn specFn slots e1 e2) (hv2 : IsValue e2) : e1 = e2 ∧ IsValue e1 := by
  cases hr with
  | lit _ | loc _ | taskRef _ | syncRef _ _ | lam _ _ _ _ => exact ⟨rfl, hv2⟩
  | tuple hrl =>
    cases hv2 with
    | tuple hvs2 =>
      rcases posSpecRelList_val_right hrl hvs2 with ⟨rfl, hvs1⟩
      exact ⟨rfl, .tuple hvs1⟩
  | @makeData adt tag _ _ hrl =>
    cases hv2 with
    | makeData _ _ hvs2 =>
      rcases posSpecRelList_val_right hrl hvs2 with ⟨rfl, hvs1⟩
      exact ⟨rfl, .makeData adt tag hvs1⟩
  | var _ | trap _ | block _ | specCbFlat _ _ _ _ | specCbInline1 _ _ _ _
  | apply _ _ | specSelfCall _ | applyDir _ | bin _ _ | un _ | let_ _ _
  | if_ _ _ _ | while_ _ _ | match_ _ _ | getTag _ | cellNew _ | cellGet _
  | cellSet _ _ | spawn _ | await _ | concPrim _ => cases hv2
termination_by sizeOf e2

theorem posSpecRelList_val_right {origFn specFn : Ident} {slots : List PosSpecSlot} {es1 es2 : List Expr}
    (hrl : PosSpecRelList origFn specFn slots es1 es2)
    (hvs2 : ∀ v ∈ es2, IsValue v) : es1 = es2 ∧ (∀ v ∈ es1, IsValue v) := by
  cases hrl with
  | nil => exact ⟨rfl, fun _ h => by cases h⟩
  | cons hr hrs =>
    rcases posSpecRel_val_right hr (hvs2 _ (List.mem_cons_self ..)) with ⟨rfl, hv1⟩
    rcases posSpecRelList_val_right hrs (fun x hx => hvs2 x (List.mem_cons_of_mem _ hx)) with ⟨rfl, hvs1⟩
    exact ⟨rfl, fun x hx => by rcases List.mem_cons.mp hx with rfl | hxr; exact hv1; exact hvs1 x hxr⟩
termination_by sizeOf es2
end

theorem posSpecRel_trap_left {origFn specFn : Ident} {slots : List PosSpecSlot} {e2 : Expr} {t : Trap}
    (hr : PosSpecRel origFn specFn slots (.trap t) e2) : e2 = .trap t := by
  cases hr; rfl

theorem posSpecRel_trap_right {origFn specFn : Ident} {slots : List PosSpecSlot} {e1 : Expr} {t : Trap}
    (hr : PosSpecRel origFn specFn slots e1 (.trap t)) : e1 = .trap t := by
  cases hr; rfl

theorem posSpecRelList_firstTrap_iff {origFn specFn : Ident} {slots : List PosSpecSlot}
    {es1 es2 : List Expr} {t : Trap}
    (hrl : PosSpecRelList origFn specFn slots es1 es2) :
    ListFirstTrap es1 t ↔ ListFirstTrap es2 t := by
  induction es1 generalizing es2 with
  | nil =>
    cases hrl; constructor <;> (intro h; cases h)
  | cons _ _ ih =>
    cases hrl with
    | cons hr hrs =>
      constructor
      · intro h; cases h with
        | head _ _ => rw [posSpecRel_trap_left hr]; exact .head _ _
        | tail hv1 htr1 =>
          rcases posSpecRel_val_left hr hv1 with ⟨rfl, hv2⟩
          exact .tail hv2 ((ih hrs).mp htr1)
      · intro h; cases h with
        | head _ _ => rw [posSpecRel_trap_right hr]; exact .head _ _
        | tail hv2 htr2 =>
          rcases posSpecRel_val_right hr hv2 with ⟨rfl, hv1⟩
          exact .tail hv1 ((ih hrs).mpr htr2)

def CbSlotWF (dom : Ident → Bool) (Φ2 : FunEnv) (c : CbSlotSpec) : Prop :=
  (∀ v ∈ c.fvVals, IsValue v) ∧
  (∀ v ∈ c.fvVals, freeVars v = []) ∧
  (∀ v ∈ c.fvVals, exprInDom dom v = true) ∧
  c.fvVals.length = c.fvs.length ∧
  (∀ x ∈ c.cbParams.map Prod.fst, x ∉ c.fvs.map Prod.fst) ∧
  (∀ z ∈ freeVars c.cbBody, z ∈ c.cbParams.map Prod.fst ++ c.fvs.map Prod.fst) ∧
  exprInDom dom c.cbBody = true ∧
  match c.lowering with
  | .flatDir flatName =>
    Φ2 flatName = some { name := flatName, params := c.fvs ++ c.cbParams,
                         retTy := c.cbRet, body := c.cbBody }
  | .inline1 inlP =>
    ∃ origP pTy, c.cbParams = [(origP, pTy)] ∧
      inlP ∉ c.fvs.map Prod.fst ∧
      exprMentionsIdent inlP c.cbBody = false

theorem CbSlotSpec.cls_eq_lam {dom : Ident → Bool} {Φ2 : FunEnv} {c : CbSlotSpec}
    (hwf : CbSlotWF dom Φ2 c) :
    c.cls = .lam c.cbMode c.cbParams c.cbRet (substMany (zipParams c.fvs c.fvVals) c.cbBody) := by
  unfold CbSlotSpec.cls
  apply substMany_lam_disjoint
  rw [zipParams_fst_eq hwf.2.2.2.1]
  exact hwf.2.2.2.2.1

theorem CbSlotSpec.cls_isValue {dom : Ident → Bool} {Φ2 : FunEnv} {c : CbSlotSpec}
    (hwf : CbSlotWF dom Φ2 c) : IsValue c.cls := by
  rw [c.cls_eq_lam hwf]; exact .lam _ _ _ _

theorem CbSlotSpec.cls_closed {dom : Ident → Bool} {Φ2 : FunEnv} {c : CbSlotSpec}
    (hwf : CbSlotWF dom Φ2 c) : freeVars c.cls = [] := by
  rw [c.cls_eq_lam hwf]
  apply List.eq_nil_iff_forall_not_mem.mpr
  intro z hz
  simp only [freeVars, List.mem_filter, Bool.not_eq_true'] at hz
  rcases substMany_freeVars_subset (zipParams c.fvs c.fvVals) (zipParams_closed hwf.2.1) c.cbBody z hz.1 with ⟨hnot, hzb⟩
  rw [zipParams_fst_eq hwf.2.2.2.1] at hnot
  rcases List.mem_append.mp (hwf.2.2.2.2.2.1 z hzb) with hcp | hfv
  · rcases List.mem_map.mp hcp with ⟨p, hp, rfl⟩
    have hany : c.cbParams.any (fun q => q.1 == p.1) = true :=
      List.any_eq_true.mpr ⟨p, hp, beq_self_eq_true _⟩
    rw [hany] at hz; cases hz.2
  · exact hnot hfv

theorem CbSlotSpec.cls_inDom {dom : Ident → Bool} {Φ2 : FunEnv} {c : CbSlotSpec}
    (hwf : CbSlotWF dom Φ2 c) : exprInDom dom c.cls = true := by
  rw [c.cls_eq_lam hwf]
  simp only [exprInDom]
  apply substMany_exprInDom
  · intro q hq; exact hwf.2.2.1 q.2 (zipParams_snd_subset hq)
  · exact hwf.2.2.2.2.2.2.1

def allCbFvNames : List PosSpecSlot → List Ident
  | [] => []
  | .state _ :: r => allCbFvNames r
  | .callback c :: r => c.fvs.map Prod.fst ++ allCbFvNames r

def allCbOrigNames : List PosSpecSlot → List Ident
  | [] => []
  | .state _ :: r => allCbOrigNames r
  | .callback c :: r => c.fParam :: allCbOrigNames r

theorem posCallArgsRel_firstTrap_iff {origFn specFn : Ident} {allSlots rem : List PosSpecSlot}
    {dom : Ident → Bool} {Φ2 : FunEnv}
    (hcbs : ∀ c ∈ cbSlotsOf rem, CbSlotWF dom Φ2 c)
    {args1 args2 : List Expr} {t : Trap}
    (hrel : PosCallArgsRel origFn specFn allSlots rem args1 args2) :
    ListFirstTrap args1 t ↔ ListFirstTrap args2 t := by
  induction rem generalizing args1 args2 with
  | nil =>
    cases hrel; constructor <;> (intro h; cases h)
  | cons sl sr ih =>
    cases hrel with
    | state _ hr hrest =>
      have hcbs_r : ∀ c ∈ cbSlotsOf sr, CbSlotWF dom Φ2 c := hcbs
      constructor
      · intro h; cases h with
        | head _ _ => rw [posSpecRel_trap_left hr]; exact .head _ _
        | tail hv1 htr1 =>
          rcases posSpecRel_val_left hr hv1 with ⟨rfl, hv2⟩
          exact .tail hv2 ((ih hcbs_r hrest).mp htr1)
      · intro h; cases h with
        | head _ _ => rw [posSpecRel_trap_right hr]; exact .head _ _
        | tail hv2 htr2 =>
          rcases posSpecRel_val_right hr hv2 with ⟨rfl, hv1⟩
          exact .tail hv1 ((ih hcbs_r hrest).mpr htr2)
    | @callback c _ r1 r2 hrest =>
      have hcwf : CbSlotWF dom Φ2 c := hcbs c (List.mem_cons_self ..)
      have hcbs_r : ∀ c' ∈ cbSlotsOf sr, CbSlotWF dom Φ2 c' :=
        fun c' hm => hcbs c' (List.mem_cons_of_mem _ hm)
      have hcls_val : IsValue c.cls := c.cls_isValue hcwf
      have hc1 : ListFirstTrap (c.cls :: r1) t ↔ ListFirstTrap r1 t :=
        listFirstTrap_prepend_vals_iff (vs := [c.cls])
          (fun v hv => by simp at hv; subst hv; exact hcls_val)
      have hc2 : ListFirstTrap (c.fvVals ++ r2) t ↔ ListFirstTrap r2 t :=
        listFirstTrap_prepend_vals_iff hcwf.1
      exact hc1.trans ((ih hcbs_r hrest).trans hc2.symm)

theorem posCallArgsRel_allVal_left {origFn specFn : Ident} {allSlots rem : List PosSpecSlot}
    {dom : Ident → Bool} {Φ2 : FunEnv}
    (hcbs : ∀ c ∈ cbSlotsOf rem, CbSlotWF dom Φ2 c)
    {args1 args2 : List Expr}
    (hrel : PosCallArgsRel origFn specFn allSlots rem args1 args2)
    (hvs1 : ∀ v ∈ args1, IsValue v) :
    (∀ v ∈ args2, IsValue v) ∧
    args1.length = (posOrigParams rem).length ∧
    args2.length = (posSpecParams rem).length := by
  induction rem generalizing args1 args2 with
  | nil =>
    cases hrel
    exact ⟨fun _ h => (by cases h), rfl, rfl⟩
  | cons sl sr ih =>
    cases hrel with
    | state _ hr hrest =>
      rcases posSpecRel_val_left hr (hvs1 _ (List.mem_cons_self ..)) with ⟨rfl, hv2⟩
      rcases ih hcbs hrest (fun v hv => hvs1 v (List.mem_cons_of_mem _ hv)) with ⟨hvs2_r, hl1, hl2⟩
      refine ⟨?_, by simp [posOrigParams, hl1], by simp [posSpecParams, hl2]⟩
      intro v hv; rcases List.mem_cons.mp hv with rfl | hvr
      · exact hv2
      · exact hvs2_r v hvr
    | @callback c _ r1 r2 hrest =>
      have hcwf : CbSlotWF dom Φ2 c := hcbs c (List.mem_cons_self ..)
      have hcbs_r : ∀ c' ∈ cbSlotsOf sr, CbSlotWF dom Φ2 c' :=
        fun c' hm => hcbs c' (List.mem_cons_of_mem _ hm)
      rcases ih hcbs_r hrest (fun v hv => hvs1 v (List.mem_cons_of_mem _ hv)) with ⟨hvs2_r, hl1, hl2⟩
      refine ⟨?_, by simp [posOrigParams, hl1], by simp [posSpecParams, hcwf.2.2.2.1, hl2]⟩
      intro v hv; rcases List.mem_append.mp hv with h1 | h2
      · exact hcwf.1 v h1
      · exact hvs2_r v h2

theorem posCallArgsRel_allVal_right {origFn specFn : Ident} {allSlots rem : List PosSpecSlot}
    {dom : Ident → Bool} {Φ2 : FunEnv}
    (hcbs : ∀ c ∈ cbSlotsOf rem, CbSlotWF dom Φ2 c)
    {args1 args2 : List Expr}
    (hrel : PosCallArgsRel origFn specFn allSlots rem args1 args2)
    (hvs2 : ∀ v ∈ args2, IsValue v) :
    ∀ v ∈ args1, IsValue v := by
  induction rem generalizing args1 args2 with
  | nil => cases hrel; intro _ h; cases h
  | cons sl sr ih =>
    cases hrel with
    | state _ hr hrest =>
      rcases posSpecRel_val_right hr (hvs2 _ (List.mem_cons_self ..)) with ⟨rfl, hv1⟩
      have hvs1_r := ih hcbs hrest (fun v hv => hvs2 v (List.mem_cons_of_mem _ hv))
      intro v hv; rcases List.mem_cons.mp hv with rfl | hvr
      · exact hv1
      · exact hvs1_r v hvr
    | @callback c _ r1 r2 hrest =>
      have hcwf : CbSlotWF dom Φ2 c := hcbs c (List.mem_cons_self ..)
      have hcbs_r : ∀ c' ∈ cbSlotsOf sr, CbSlotWF dom Φ2 c' :=
        fun c' hm => hcbs c' (List.mem_cons_of_mem _ hm)
      have hvs1_r := ih hcbs_r hrest (fun v hv => hvs2 v (List.mem_append_right _ hv))
      intro v hv; rcases List.mem_cons.mp hv with rfl | hvr
      · exact c.cls_isValue hcwf
      · exact hvs1_r v hvr

mutual
theorem freeVars_subst_var_subset (origP inlP : Ident) :
    (e : Expr) → ∀ z ∈ freeVars (subst origP (.var inlP) e), z = inlP ∨ (z ∈ freeVars e ∧ z ≠ origP)
  | .lit _ | .loc _ | .taskRef _ | .syncRef _ _ | .trap _ => by simp [subst, freeVars]
  | .var w => by
    intro z hz
    simp only [subst] at hz
    cases hwo : (w == origP) <;> simp only [hwo, Bool.false_eq_true, ↓reduceIte, freeVars, List.mem_singleton] at hz
    · subst hz; exact Or.inr ⟨by simp [freeVars], fun heq => by subst heq; rw [beq_self_eq_true] at hwo; cases hwo⟩
    · exact Or.inl hz
  | .tuple es => fun z hz => freeVarsList_subst_var_subset origP inlP es z hz
  | .block es => fun z hz => freeVarsList_subst_var_subset origP inlP es z hz
  | .lam m ps ret body => by
    intro z hz
    simp only [subst] at hz
    cases hap : ps.any (fun p => p.1 == origP) <;> simp only [hap, Bool.false_eq_true, ↓reduceIte, freeVars, List.mem_filter, Bool.not_eq_true'] at hz
    · rcases freeVars_subst_var_subset origP inlP body z hz.1 with rfl | ⟨hb, hne⟩
      · exact Or.inl rfl
      · exact Or.inr ⟨by simp [freeVars, hb, hz.2], hne⟩
    · refine Or.inr ⟨by simp [freeVars, hz.1, hz.2], ?_⟩
      intro heq; subst heq; rw [hap] at hz; cases hz.2
  | .apply fn args => by
    intro z hz; simp only [subst, freeVars, List.mem_append] at hz
    rcases hz with h1 | h2
    · rcases freeVars_subst_var_subset origP inlP fn z h1 with rfl | ⟨hf, hne⟩
      · exact Or.inl rfl
      · exact Or.inr ⟨by simp [freeVars, hf], hne⟩
    · rcases freeVarsList_subst_var_subset origP inlP args z h2 with rfl | ⟨ha, hne⟩
      · exact Or.inl rfl
      · exact Or.inr ⟨by simp [freeVars, ha], hne⟩
  | .applyDir _ args => fun z hz => freeVarsList_subst_var_subset origP inlP args z hz
  | .bin _ a b | .while_ a b | .cellSet a b => by
    intro z hz; simp only [subst, freeVars, List.mem_append] at hz
    rcases hz with h1 | h2
    · rcases freeVars_subst_var_subset origP inlP a z h1 with rfl | ⟨ha, hne⟩
      · exact Or.inl rfl
      · exact Or.inr ⟨by simp [freeVars, ha], hne⟩
    · rcases freeVars_subst_var_subset origP inlP b z h2 with rfl | ⟨hb, hne⟩
      · exact Or.inl rfl
      · exact Or.inr ⟨by simp [freeVars, hb], hne⟩
  | .un _ a | .getTag a | .cellNew a | .cellGet a | .spawn a | .await a =>
    fun z hz => freeVars_subst_var_subset origP inlP a z hz
  | .let_ y a b => by
    intro z hz; simp only [subst] at hz
    cases hyo : (y == origP) <;> simp only [hyo, Bool.false_eq_true, ↓reduceIte, freeVars, List.mem_append, List.mem_filter] at hz
    · rcases hz with h1 | ⟨h2, hzy⟩
      · rcases freeVars_subst_var_subset origP inlP a z h1 with rfl | ⟨ha, hne⟩
        · exact Or.inl rfl
        · exact Or.inr ⟨by simp [freeVars, ha], hne⟩
      · rcases freeVars_subst_var_subset origP inlP b z h2 with rfl | ⟨hb, hne⟩
        · exact Or.inl rfl
        · exact Or.inr ⟨by simp [freeVars]; exact Or.inr ⟨hb, by simpa using hzy⟩, hne⟩
    · have hy_eq := eq_of_beq hyo; subst hy_eq
      rcases hz with h1 | ⟨h2, hzy⟩
      · rcases freeVars_subst_var_subset y inlP a z h1 with rfl | ⟨ha, hne⟩
        · exact Or.inl rfl
        · exact Or.inr ⟨by simp [freeVars, ha], hne⟩
      · exact Or.inr ⟨by simp [freeVars]; exact Or.inr ⟨h2, by simpa using hzy⟩,
          fun heq => by subst heq; simp at hzy⟩
  | .if_ c t e2 => by
    intro z hz; simp only [subst, freeVars, List.mem_append] at hz
    rcases hz with (h1 | h2) | h3
    · rcases freeVars_subst_var_subset origP inlP c z h1 with rfl | ⟨hc, hne⟩
      · exact Or.inl rfl
      · exact Or.inr ⟨by simp [freeVars, hc], hne⟩
    · rcases freeVars_subst_var_subset origP inlP t z h2 with rfl | ⟨ht, hne⟩
      · exact Or.inl rfl
      · exact Or.inr ⟨by simp [freeVars, ht], hne⟩
    · rcases freeVars_subst_var_subset origP inlP e2 z h3 with rfl | ⟨he, hne⟩
      · exact Or.inl rfl
      · exact Or.inr ⟨by simp [freeVars, he], hne⟩
  | .match_ s arms => by
    intro z hz; simp only [subst, freeVars, List.mem_append] at hz
    rcases hz with h1 | h2
    · rcases freeVars_subst_var_subset origP inlP s z h1 with rfl | ⟨hs, hne⟩
      · exact Or.inl rfl
      · exact Or.inr ⟨by simp [freeVars, hs], hne⟩
    · rcases freeVarsArms_subst_var_subset origP inlP arms z h2 with rfl | ⟨ha, hne⟩
      · exact Or.inl rfl
      · exact Or.inr ⟨by simp [freeVars, ha], hne⟩
  | .makeData _ _ es => fun z hz => freeVarsList_subst_var_subset origP inlP es z hz
  | .concPrim _ es => fun z hz => freeVarsList_subst_var_subset origP inlP es z hz
termination_by e => sizeOf e

theorem freeVarsList_subst_var_subset (origP inlP : Ident) :
    (es : List Expr) → ∀ z ∈ freeVarsList (substList origP (.var inlP) es),
      z = inlP ∨ (z ∈ freeVarsList es ∧ z ≠ origP)
  | [] => by simp [substList, freeVarsList]
  | e :: r => by
    intro z hz; simp only [substList, freeVarsList, List.mem_append] at hz
    rcases hz with h1 | h2
    · rcases freeVars_subst_var_subset origP inlP e z h1 with rfl | ⟨he, hne⟩
      · exact Or.inl rfl
      · exact Or.inr ⟨by simp [freeVarsList, he], hne⟩
    · rcases freeVarsList_subst_var_subset origP inlP r z h2 with rfl | ⟨hr, hne⟩
      · exact Or.inl rfl
      · exact Or.inr ⟨by simp [freeVarsList, hr], hne⟩
termination_by es => sizeOf es

theorem freeVarsArms_subst_var_subset (origP inlP : Ident) :
    (arms : List (Pat × Expr)) → ∀ z ∈ freeVarsArms (substArms origP (.var inlP) arms),
      z = inlP ∨ (z ∈ freeVarsArms arms ∧ z ≠ origP)
  | [] => by simp [substArms, freeVarsArms]
  | (p, b) :: r => by
    intro z hz; simp only [substArms, freeVarsArms, List.mem_append, List.mem_filter] at hz
    rcases hz with ⟨h1, hnotp⟩ | h2
    · split at h1
      · rename_i hp_orig
        refine Or.inr ⟨by simp [freeVarsArms]; exact Or.inl ⟨h1, by simpa using hnotp⟩, ?_⟩
        intro heq; subst heq
        rw [hp_orig] at hnotp; cases hnotp
      · rcases freeVars_subst_var_subset origP inlP b z h1 with rfl | ⟨hb, hne⟩
        · exact Or.inl rfl
        · exact Or.inr ⟨by simp [freeVarsArms]; exact Or.inl ⟨hb, by simpa using hnotp⟩, hne⟩
    · rcases freeVarsArms_subst_var_subset origP inlP r z h2 with rfl | ⟨hr, hne⟩
      · exact Or.inl rfl
      · exact Or.inr ⟨by simp [freeVarsArms, hr], hne⟩
termination_by arms => sizeOf arms
end

/- Substitution preservation of `PosSpecRel`. -/
mutual
theorem posSpecRel_subst {origFn specFn : Ident} {slots : List PosSpecSlot}
    {dom : Ident → Bool} {Φ2 : FunEnv}
    (hcbs : ∀ c ∈ cbSlotsOf slots, CbSlotWF dom Φ2 c)
    (x : Ident) {v : Expr} (hv : freeVars v = [])
    {e1 e2 : Expr} (hr : PosSpecRel origFn specFn slots e1 e2) :
    PosSpecRel origFn specFn slots (subst x v e1) (subst x v e2) := by
  cases hr with
  | lit l => exact .lit l
  | var z =>
    simp only [subst]; split
    · exact PosSpecRel.refl _ _ _ v
    · exact .var z
  | loc l => exact .loc l
  | taskRef tid => exact .taskRef tid
  | syncRef k id => exact .syncRef k id
  | lam m ps ret body =>
    simp only [subst]; split
    · exact .lam m ps ret body
    · exact .lam m ps ret (subst x v body)
  | trap t => exact .trap t
  | tuple hrl => exact .tuple (posSpecRelList_subst hcbs x hv hrl)
  | block hrl => exact .block (posSpecRelList_subst hcbs x hv hrl)
  | @specCbFlat c flatName args1 args2 hmem hlow hlen hrl =>
    have hcwf := hcbs c hmem
    have hx_cls : x ∉ freeVars c.cls := by simp [c.cls_closed hcwf]
    simp only [subst, subst_not_mem_freeVars c.cls hx_cls, substList_append_eq,
      substList_closed_id x v c.fvVals hcwf.2.1]
    exact .specCbFlat hmem hlow (by rw [substList_length_eq, hlen])
      (posSpecRelList_subst hcbs x hv hrl)
  | @specCbInline1 c inlP origP pTy arg1 arg2 hmem hlow hcp hr_arg =>
    have hcwf := hcbs c hmem
    have hx_cls : x ∉ freeVars c.cls := by simp [c.cls_closed hcwf]
    have hbody_fv : ∀ z ∈ freeVars (substMany (zipParams c.fvs c.fvVals) (subst origP (.var inlP) c.cbBody)),
        z = inlP := by
      intro z hz
      rcases substMany_freeVars_subset (zipParams c.fvs c.fvVals) (zipParams_closed hcwf.2.1)
        (subst origP (.var inlP) c.cbBody) z hz with ⟨hnotFv, hz_sub⟩
      rw [zipParams_fst_eq hcwf.2.2.2.1] at hnotFv
      rcases freeVars_subst_var_subset origP inlP c.cbBody z hz_sub with rfl | ⟨hz_cb, hne_orig⟩
      · rfl
      · have hin := hcwf.2.2.2.2.2.1 z hz_cb
        rw [hcp] at hin
        simp only [List.map_cons, List.map_nil, List.cons_append, List.mem_cons] at hin
        rcases hin with rfl | hfv
        · exact False.elim (hne_orig rfl)
        · exact False.elim (hnotFv hfv)
    simp only [subst, substList, subst_not_mem_freeVars c.cls hx_cls]
    cases hxi : (inlP == x)
    · have hne : x ≠ inlP := fun heq => by subst heq; rw [beq_self_eq_true] at hxi; cases hxi
      have hx_not : x ∉ freeVars (substMany (zipParams c.fvs c.fvVals) (subst origP (.var inlP) c.cbBody)) :=
        fun hm => hne (hbody_fv x hm)
      simp only [Bool.false_eq_true, ↓reduceIte, subst_not_mem_freeVars _ hx_not]
      exact .specCbInline1 hmem hlow hcp (posSpecRel_subst hcbs x hv hr_arg)
    · simp only [↓reduceIte]
      exact .specCbInline1 hmem hlow hcp (posSpecRel_subst hcbs x hv hr_arg)
  | apply hfn hrl =>
    exact .apply (posSpecRel_subst hcbs x hv hfn) (posSpecRelList_subst hcbs x hv hrl)
  | specSelfCall hcall =>
    exact .specSelfCall (posCallArgsRel_subst hcbs x hv slots hcall (fun _ h => h))
  | applyDir hrl => exact .applyDir (posSpecRelList_subst hcbs x hv hrl)
  | bin ha hb => exact .bin (posSpecRel_subst hcbs x hv ha) (posSpecRel_subst hcbs x hv hb)
  | un ha => exact .un (posSpecRel_subst hcbs x hv ha)
  | let_ ha hb =>
    simp only [subst]; split
    · exact .let_ (posSpecRel_subst hcbs x hv ha) hb
    · exact .let_ (posSpecRel_subst hcbs x hv ha) (posSpecRel_subst hcbs x hv hb)
  | if_ hc ht he =>
    exact .if_ (posSpecRel_subst hcbs x hv hc)
      (posSpecRel_subst hcbs x hv ht) (posSpecRel_subst hcbs x hv he)
  | while_ hc hb =>
    exact .while_ (posSpecRel_subst hcbs x hv hc) (posSpecRel_subst hcbs x hv hb)
  | match_ hs ha =>
    exact .match_ (posSpecRel_subst hcbs x hv hs) (posSpecRelArms_subst hcbs x hv ha)
  | makeData hrl => exact .makeData (posSpecRelList_subst hcbs x hv hrl)
  | getTag ha => exact .getTag (posSpecRel_subst hcbs x hv ha)
  | cellNew ha => exact .cellNew (posSpecRel_subst hcbs x hv ha)
  | cellGet ha => exact .cellGet (posSpecRel_subst hcbs x hv ha)
  | cellSet ha hb =>
    exact .cellSet (posSpecRel_subst hcbs x hv ha) (posSpecRel_subst hcbs x hv hb)
  | spawn ha => exact .spawn (posSpecRel_subst hcbs x hv ha)
  | await ha => exact .await (posSpecRel_subst hcbs x hv ha)
  | concPrim hrl => exact .concPrim (posSpecRelList_subst hcbs x hv hrl)
termination_by sizeOf e1

theorem posSpecRelList_subst {origFn specFn : Ident} {slots : List PosSpecSlot}
    {dom : Ident → Bool} {Φ2 : FunEnv}
    (hcbs : ∀ c ∈ cbSlotsOf slots, CbSlotWF dom Φ2 c)
    (x : Ident) {v : Expr} (hv : freeVars v = [])
    {es1 es2 : List Expr} (hrl : PosSpecRelList origFn specFn slots es1 es2) :
    PosSpecRelList origFn specFn slots (substList x v es1) (substList x v es2) := by
  cases hrl with
  | nil => exact .nil
  | cons hr hrs =>
    exact .cons (posSpecRel_subst hcbs x hv hr) (posSpecRelList_subst hcbs x hv hrs)
termination_by sizeOf es1

theorem posSpecRelArms_subst {origFn specFn : Ident} {slots : List PosSpecSlot}
    {dom : Ident → Bool} {Φ2 : FunEnv}
    (hcbs : ∀ c ∈ cbSlotsOf slots, CbSlotWF dom Φ2 c)
    (x : Ident) {v : Expr} (hv : freeVars v = [])
    {arms1 arms2 : List (Pat × Expr)} (harms : PosSpecRelArms origFn specFn slots arms1 arms2) :
    PosSpecRelArms origFn specFn slots (substArms x v arms1) (substArms x v arms2) := by
  cases harms with
  | nil => exact .nil
  | cons hb hrs =>
    simp only [substArms]; split
    · exact .cons hb (posSpecRelArms_subst hcbs x hv hrs)
    · exact .cons (posSpecRel_subst hcbs x hv hb) (posSpecRelArms_subst hcbs x hv hrs)
termination_by sizeOf arms1

theorem posCallArgsRel_subst {origFn specFn : Ident} {slots : List PosSpecSlot}
    {dom : Ident → Bool} {Φ2 : FunEnv}
    (hcbs : ∀ c ∈ cbSlotsOf slots, CbSlotWF dom Φ2 c)
    (x : Ident) {v : Expr} (hv : freeVars v = [])
    (rem : List PosSpecSlot)
    {args1 args2 : List Expr} (hcall : PosCallArgsRel origFn specFn slots rem args1 args2) :
    (∀ c ∈ cbSlotsOf rem, c ∈ cbSlotsOf slots) →
    PosCallArgsRel origFn specFn slots rem (substList x v args1) (substList x v args2) := by
  intro hsub
  cases hcall with
  | nil => exact .nil
  | state p hr hrest =>
    exact .state p (posSpecRel_subst hcbs x hv hr)
      (posCallArgsRel_subst hcbs x hv _ hrest hsub)
  | @callback c rem' r1 r2 hrest =>
    have hcwf := hcbs c (hsub c (List.mem_cons_self ..))
    have hx_cls : x ∉ freeVars c.cls := by simp [c.cls_closed hcwf]
    simp only [substList, subst_not_mem_freeVars c.cls hx_cls, substList_append_eq,
      substList_closed_id x v c.fvVals hcwf.2.1]
    exact .callback c (posCallArgsRel_subst hcbs x hv rem' hrest
      (fun c' hm => hsub c' (List.mem_cons_of_mem _ hm)))
termination_by sizeOf args1
end

theorem posSpecRel_substMany {origFn specFn : Ident} {slots : List PosSpecSlot}
    {dom : Ident → Bool} {Φ2 : FunEnv}
    (hcbs : ∀ c ∈ cbSlotsOf slots, CbSlotWF dom Φ2 c)
    {ρ : List (Ident × Expr)} (hρ : ∀ p ∈ ρ, freeVars p.2 = [])
    {e1 e2 : Expr} (hr : PosSpecRel origFn specFn slots e1 e2) :
    PosSpecRel origFn specFn slots (substMany ρ e1) (substMany ρ e2) := by
  induction ρ generalizing e1 e2 with
  | nil => exact hr
  | cons p rest ih =>
    exact ih (fun q hq => hρ q (List.mem_cons_of_mem _ hq))
      (posSpecRel_subst hcbs p.1 (hρ p (List.mem_cons_self ..)) hr)

/- Positional substitution lookup lemmas (`L1`, `L2`, `L3`, `L4`) for arbitrary slot layouts. -/
theorem findCbSlot_mem {f : Ident} {slots : List PosSpecSlot} {c : CbSlotSpec}
    (h : findCbSlot? f slots = some c) : c ∈ cbSlotsOf slots ∧ c.fParam = f := by
  induction slots with
  | nil => simp [findCbSlot?] at h
  | cons sl sr ih =>
    cases sl with
    | state _ => exact ih h
    | callback c0 =>
      simp only [findCbSlot?] at h
      cases hcf : (c0.fParam == f) <;> simp only [hcf, Bool.false_eq_true, ↓reduceIte] at h
      · rcases ih h with ⟨hm, heq⟩
        exact ⟨List.mem_cons_of_mem _ hm, heq⟩
      · injection h with h; subst h
        exact ⟨List.mem_cons_self .., eq_of_beq hcf⟩

theorem findCbSlot_mem_origParams {f : Ident} {slots : List PosSpecSlot} {c : CbSlotSpec}
    (h : findCbSlot? f slots = some c) : f ∈ (posOrigParams slots).map Prod.fst := by
  induction slots with
  | nil => simp [findCbSlot?] at h
  | cons sl sr ih =>
    cases sl with
    | state p => exact List.mem_cons_of_mem _ (ih h)
    | callback c0 =>
      simp only [findCbSlot?] at h
      cases hcf : (c0.fParam == f) <;> simp only [hcf, Bool.false_eq_true, ↓reduceIte] at h
      · exact List.mem_cons_of_mem _ (ih h)
      · rw [← eq_of_beq hcf]; exact List.mem_cons_self ..

theorem substMany_var_not_mem {ρ : List (Ident × Expr)} {x : Ident}
    (hnot : x ∉ ρ.map Prod.fst) : substMany ρ (.var x) = .var x := by
  induction ρ with
  | nil => rfl
  | cons q qr ih =>
    simp only [List.map_cons, List.mem_cons, not_or] at hnot
    simp [substMany, subst, beq_false_of_ne hnot.1, ih hnot.2]

theorem cbSlotsOf_fvs_subset_specParams {sr : List PosSpecSlot} {c : CbSlotSpec}
    (hmem : c ∈ cbSlotsOf sr) :
    ∀ z ∈ c.fvs.map Prod.fst, z ∈ (posSpecParams sr).map Prod.fst := by
  induction sr with
  | nil => cases hmem
  | cons s2 sr2 ihs =>
    cases s2 with
    | state _ =>
      simp only [cbSlotsOf] at hmem
      simp only [posSpecParams, List.map_cons]
      exact fun z hz => List.mem_cons_of_mem _ (ihs hmem z hz)
    | callback _ =>
      simp only [cbSlotsOf, List.mem_cons] at hmem
      simp only [posSpecParams, List.map_append]
      rcases hmem with rfl | hmr
      · exact fun z hz => List.mem_append_left _ hz
      · exact fun z hz => List.mem_append_right _ (ihs hmr z hz)

theorem posCallArgs_subst_nonCbVar {origFn specFn : Ident} {allSlots rem : List PosSpecSlot}
    {dom : Ident → Bool} {Φ2 : FunEnv}
    (hcbs : ∀ c ∈ cbSlotsOf rem, CbSlotWF dom Φ2 c)
    {args1 args2 : List Expr}
    (hrel : PosCallArgsRel origFn specFn allSlots rem args1 args2)
    (hvs1 : ∀ v ∈ args1, IsValue v) (hcl1 : ∀ v ∈ args1, freeVars v = [])
    {x : Ident} (hnotCb : findCbSlot? x rem = none) (hnotFv : x ∉ allCbFvNames rem) :
    substMany (zipParams (posOrigParams rem) args1) (.var x) =
      substMany (zipParams (posSpecParams rem) args2) (.var x) := by
  induction rem generalizing args1 args2 with
  | nil => cases hrel; rfl
  | cons sl sr ih =>
    cases hrel with
    | @state p _ v _ r1 r2 hr hrest =>
      rcases posSpecRel_val_left hr (hvs1 v (List.mem_cons_self ..)) with ⟨rfl, _⟩
      have hv_cl : freeVars v = [] := hcl1 v (List.mem_cons_self ..)
      simp only [posOrigParams, posSpecParams, zipParams, List.map_cons, List.zip_cons_cons,
        substMany, subst]
      cases hxp : (x == p.1)
      · simp only [Bool.false_eq_true, ↓reduceIte]
        exact ih hcbs hrest
          (fun u hu => hvs1 u (List.mem_cons_of_mem _ hu))
          (fun u hu => hcl1 u (List.mem_cons_of_mem _ hu)) hnotCb hnotFv
      · simp only [↓reduceIte, substMany_closed_val_id _ hv_cl]
    | @callback c _ r1 r2 hrest =>
      have hcwf := hcbs c (List.mem_cons_self ..)
      have hcbs_r : ∀ c' ∈ cbSlotsOf sr, CbSlotWF dom Φ2 c' :=
        fun c' hm => hcbs c' (List.mem_cons_of_mem _ hm)
      simp only [findCbSlot?] at hnotCb
      have hcf : (c.fParam == x) = false := by
        cases h : (c.fParam == x)
        · rfl
        · simp [h] at hnotCb
      rw [hcf] at hnotCb; simp only [Bool.false_eq_true, ↓reduceIte] at hnotCb
      have hxc : (x == c.fParam) = false :=
        beq_false_of_ne (fun heq => by subst heq; rw [beq_self_eq_true] at hcf; cases hcf)
      simp only [allCbFvNames, List.mem_append, not_or] at hnotFv
      have hx_sub_fvs : substMany (zipParams c.fvs c.fvVals) (.var x) = .var x :=
        substMany_var_not_mem (by rw [zipParams_fst_eq hcwf.2.2.2.1]; exact hnotFv.1)
      simp only [posOrigParams, posSpecParams]
      rw [zipParams_append hcwf.2.2.2.1, substMany_append, hx_sub_fvs]
      simp only [zipParams, List.map_cons, List.zip_cons_cons, substMany, subst, hxc,
        Bool.false_eq_true, ↓reduceIte]
      exact ih hcbs_r hrest
        (fun u hu => hvs1 u (List.mem_cons_of_mem _ hu))
        (fun u hu => hcl1 u (List.mem_cons_of_mem _ hu)) hnotCb hnotFv.2

theorem posCallArgs_subst_cbVar {origFn specFn : Ident} {allSlots rem : List PosSpecSlot}
    {dom : Ident → Bool} {Φ2 : FunEnv}
    (hcbs : ∀ c ∈ cbSlotsOf rem, CbSlotWF dom Φ2 c)
    {args1 args2 : List Expr}
    (hrel : PosCallArgsRel origFn specFn allSlots rem args1 args2)
    (hnodupOrig : ((posOrigParams rem).map Prod.fst).Nodup)
    {f : Ident} {c : CbSlotSpec} (hfind : findCbSlot? f rem = some c) :
    substMany (zipParams (posOrigParams rem) args1) (.var f) = c.cls := by
  induction rem generalizing args1 args2 with
  | nil => simp [findCbSlot?] at hfind
  | cons sl sr ih =>
    cases hrel with
    | @state p _ e1 _ _ _ _ hrest =>
      simp only [posOrigParams, List.map_cons] at hnodupOrig
      rcases List.nodup_cons.mp hnodupOrig with ⟨hp_not, hnodup_r⟩
      have hf_in : f ∈ (posOrigParams sr).map Prod.fst := findCbSlot_mem_origParams hfind
      have hfp : (f == p.1) = false := beq_false_of_ne (fun heq => by subst heq; exact hp_not hf_in)
      simp only [posOrigParams, zipParams, List.map_cons, List.zip_cons_cons, substMany, subst,
        hfp, Bool.false_eq_true, ↓reduceIte]
      exact ih hcbs hrest hnodup_r hfind
    | @callback c0 _ r1 r2 hrest =>
      have hc0wf := hcbs c0 (List.mem_cons_self ..)
      have hcbs_r : ∀ c' ∈ cbSlotsOf sr, CbSlotWF dom Φ2 c' :=
        fun c' hm => hcbs c' (List.mem_cons_of_mem _ hm)
      simp only [posOrigParams, List.map_cons] at hnodupOrig
      rcases List.nodup_cons.mp hnodupOrig with ⟨_, hnodup_r⟩
      simp only [findCbSlot?] at hfind
      cases hcf : (c0.fParam == f) <;> simp only [hcf, Bool.false_eq_true, ↓reduceIte] at hfind
      · have hfc : (f == c0.fParam) = false :=
          beq_false_of_ne (fun heq => by subst heq; rw [beq_self_eq_true] at hcf; cases hcf)
        simp only [posOrigParams, zipParams, List.map_cons, List.zip_cons_cons, substMany, subst,
          hfc, Bool.false_eq_true, ↓reduceIte]
        exact ih hcbs_r hrest hnodup_r hfind
      · injection hfind with hfind; subst hfind
        have hfc : (f == c0.fParam) = true := beq_iff_eq.mpr (eq_of_beq hcf).symm
        simp only [posOrigParams, zipParams, List.map_cons, List.zip_cons_cons, substMany, subst,
          hfc, ↓reduceIte]
        exact substMany_closed_val_id _ (c0.cls_closed hc0wf)

theorem posCallArgs_subst_cbFvs {origFn specFn : Ident} {allSlots rem : List PosSpecSlot}
    {dom : Ident → Bool} {Φ2 : FunEnv}
    (hcbs : ∀ c ∈ cbSlotsOf rem, CbSlotWF dom Φ2 c)
    {args1 args2 : List Expr}
    (hrel : PosCallArgsRel origFn specFn allSlots rem args1 args2)
    (hvs1 : ∀ v ∈ args1, IsValue v) (hcl1 : ∀ v ∈ args1, freeVars v = [])
    (hnodupSpec : ((posSpecParams rem).map Prod.fst).Nodup)
    {c : CbSlotSpec} (hmem : c ∈ cbSlotsOf rem) :
    ((c.fvs.map Prod.fst).map Expr.var).map
      (substMany (zipParams (posSpecParams rem) args2)) = c.fvVals := by
  induction rem generalizing args1 args2 with
  | nil => cases hmem
  | cons sl sr ih =>
    cases hrel with
    | @state p _ v _ r1 r2 hr hrest =>
      rcases posSpecRel_val_left hr (hvs1 v (List.mem_cons_self ..)) with ⟨rfl, _⟩
      simp only [posSpecParams, List.map_cons] at hnodupSpec
      rcases List.nodup_cons.mp hnodupSpec with ⟨hp_not, hnodup_r⟩
      have hcfv_sub := cbSlotsOf_fvs_subset_specParams (sr := sr) hmem
      have hstep_map :
          ((c.fvs.map Prod.fst).map Expr.var).map (substMany (zipParams (p :: posSpecParams sr) (v :: r2))) =
          ((c.fvs.map Prod.fst).map Expr.var).map (substMany (zipParams (posSpecParams sr) r2)) := by
        apply List.map_congr_left
        intro e he
        rcases List.mem_map.mp he with ⟨z, hz, rfl⟩
        have hzp : (z == p.1) = false :=
          beq_false_of_ne (fun heq => hp_not (heq ▸ hcfv_sub z hz))
        simp [zipParams, substMany, subst, hzp]
      simp only [posSpecParams]; rw [hstep_map]
      exact ih hcbs hrest
        (fun u hu => hvs1 u (List.mem_cons_of_mem _ hu))
        (fun u hu => hcl1 u (List.mem_cons_of_mem _ hu)) hnodup_r hmem
    | @callback c0 _ r1 r2 hrest =>
      have hc0wf := hcbs c0 (List.mem_cons_self ..)
      have hcbs_r : ∀ c' ∈ cbSlotsOf sr, CbSlotWF dom Φ2 c' :=
        fun c' hm => hcbs c' (List.mem_cons_of_mem _ hm)
      simp only [posSpecParams, List.map_append] at hnodupSpec
      simp only [cbSlotsOf, List.mem_cons] at hmem
      rcases hmem with rfl | hmr
      · exact map_substMany_zipParams_vars hnodupSpec hc0wf.2.2.2.1 hc0wf.2.1
      · have hnodup_r : ((posSpecParams sr).map Prod.fst).Nodup :=
          (List.nodup_append.mp hnodupSpec).2.1
        have hdisj_c0 : ∀ x ∈ c0.fvs.map Prod.fst, x ∉ (posSpecParams sr).map Prod.fst :=
          fun x hx hm => (List.nodup_append.mp hnodupSpec).2.2 x hx x hm rfl
        have hcfv_sub := cbSlotsOf_fvs_subset_specParams hmr
        have hskip_c0 :
            ((c.fvs.map Prod.fst).map Expr.var).map
              (substMany (zipParams (c0.fvs ++ posSpecParams sr) (c0.fvVals ++ r2))) =
            ((c.fvs.map Prod.fst).map Expr.var).map
              (substMany (zipParams (posSpecParams sr) r2)) := by
          rw [zipParams_append hc0wf.2.2.2.1]
          apply List.map_congr_left
          intro e he
          rcases List.mem_map.mp he with ⟨z, hz, rfl⟩
          rw [substMany_append]
          have hnot_c0 : z ∉ (zipParams c0.fvs c0.fvVals).map Prod.fst := by
            rw [zipParams_fst_eq hc0wf.2.2.2.1]
            exact fun hm => hdisj_c0 z hm (hcfv_sub z hz)
          rw [substMany_var_not_mem hnot_c0]
        simp only [posSpecParams]; rw [hskip_c0]
        exact ih hcbs_r hrest
          (fun u hu => hvs1 u (List.mem_cons_of_mem _ hu))
          (fun u hu => hcl1 u (List.mem_cons_of_mem _ hu)) hnodup_r hmr

theorem posCallArgs_subst_inlineBody {origFn specFn : Ident} {allSlots rem : List PosSpecSlot}
    {dom : Ident → Bool} {Φ2 : FunEnv}
    (hcbs : ∀ c ∈ cbSlotsOf rem, CbSlotWF dom Φ2 c)
    {args1 args2 : List Expr}
    (hrel : PosCallArgsRel origFn specFn allSlots rem args1 args2)
    (hvs1 : ∀ v ∈ args1, IsValue v) (hcl1 : ∀ v ∈ args1, freeVars v = [])
    (hnodupSpec : ((posSpecParams rem).map Prod.fst).Nodup)
    {c : CbSlotSpec} {inlP origP : Ident} {pTy : Ty} {rhs : Expr}
    (hmem : c ∈ cbSlotsOf rem) (hcp : c.cbParams = [(origP, pTy)])
    (hinlNotSpec : inlP ∉ (posSpecParams rem).map Prod.fst) :
    substMany (zipParams (posSpecParams rem) args2)
      (.let_ inlP rhs (subst origP (.var inlP) c.cbBody)) =
    .let_ inlP (substMany (zipParams (posSpecParams rem) args2) rhs)
      (substMany (zipParams c.fvs c.fvVals) (subst origP (.var inlP) c.cbBody)) := by
  have hinlNotZip : inlP ∉ (zipParams (posSpecParams rem) args2).map Prod.fst := by
    rw [zipParams_fst_eq (posCallArgsRel_allVal_left hcbs hrel hvs1).2.2]
    exact hinlNotSpec
  rw [substMany_let_not_mem _ hinlNotZip]
  clear hinlNotZip
  congr 1
  have hcwf := hcbs c hmem
  have hEfvs : ∀ z ∈ freeVars (subst origP (.var inlP) c.cbBody), z = inlP ∨ z ∈ c.fvs.map Prod.fst := by
    intro z hz
    rcases freeVars_subst_var_subset origP inlP c.cbBody z hz with rfl | ⟨hz_cb, hne⟩
    · exact Or.inl rfl
    · have hin := hcwf.2.2.2.2.2.1 z hz_cb
      rw [hcp] at hin
      simp only [List.map_cons, List.map_nil, List.cons_append, List.mem_cons] at hin
      rcases hin with rfl | hfv
      · exact False.elim (hne rfl)
      · exact Or.inr hfv
  clear hcwf
  induction rem generalizing args1 args2 with
  | nil => cases hmem
  | cons sl sr ih =>
    cases hrel with
    | @state p _ v _ r1 r2 hr hrest =>
      rcases posSpecRel_val_left hr (hvs1 v (List.mem_cons_self ..)) with ⟨rfl, _⟩
      simp only [posSpecParams, List.map_cons, List.mem_cons, not_or] at hnodupSpec hinlNotSpec
      rcases List.nodup_cons.mp hnodupSpec with ⟨hp_not, hnodup_r⟩
      have hcfv_sub := cbSlotsOf_fvs_subset_specParams (sr := sr) hmem
      have hp_not_E : p.1 ∉ freeVars (subst origP (.var inlP) c.cbBody) := by
        intro hm
        rcases hEfvs p.1 hm with heq | hfv
        · exact hinlNotSpec.1 heq.symm
        · exact hp_not (hcfv_sub p.1 hfv)
      simp only [posSpecParams, zipParams, List.map_cons, List.zip_cons_cons, substMany,
        subst_not_mem_freeVars _ hp_not_E]
      exact ih hcbs hrest
        (fun u hu => hvs1 u (List.mem_cons_of_mem _ hu))
        (fun u hu => hcl1 u (List.mem_cons_of_mem _ hu))
        hnodup_r hmem hinlNotSpec.2
    | @callback c0 _ r1 r2 hrest =>
      have hc0wf := hcbs c0 (List.mem_cons_self ..)
      have hcbs_r : ∀ c' ∈ cbSlotsOf sr, CbSlotWF dom Φ2 c' :=
        fun c' hm => hcbs c' (List.mem_cons_of_mem _ hm)
      simp only [posSpecParams, List.map_append, List.mem_append, not_or] at hnodupSpec hinlNotSpec
      simp only [cbSlotsOf, List.mem_cons] at hmem
      rcases hmem with rfl | hmr
      · simp only [posSpecParams]
        rw [zipParams_append hc0wf.2.2.2.1, substMany_append]
        have hclosed_after : ∀ z ∈ freeVars (substMany (zipParams c.fvs c.fvVals) (subst origP (.var inlP) c.cbBody)),
            z = inlP := by
          intro z hz
          rcases substMany_freeVars_subset (zipParams c.fvs c.fvVals) (zipParams_closed hc0wf.2.1)
            (subst origP (.var inlP) c.cbBody) z hz with ⟨hnz, hzs⟩
          rw [zipParams_fst_eq hc0wf.2.2.2.1] at hnz
          rcases hEfvs z hzs with rfl | hfv
          · rfl
          · exact False.elim (hnz hfv)
        have hlen2_r := (posCallArgsRel_allVal_left (rem := sr) hcbs_r hrest
          (fun u hu => hvs1 u (List.mem_cons_of_mem _ hu))).2.2
        have hid_rest : ∀ ρ, inlP ∉ ρ.map Prod.fst →
            substMany ρ (substMany (zipParams c.fvs c.fvVals) (subst origP (.var inlP) c.cbBody)) =
            substMany (zipParams c.fvs c.fvVals) (subst origP (.var inlP) c.cbBody) := by
          intro ρ hn; induction ρ with
          | nil => rfl
          | cons q qr ihq =>
            simp only [List.map_cons, List.mem_cons, not_or] at hn
            have hq_not : q.1 ∉ freeVars (substMany (zipParams c.fvs c.fvVals) (subst origP (.var inlP) c.cbBody)) :=
              fun hm => hn.1 (hclosed_after q.1 hm).symm
            simp only [substMany, subst_not_mem_freeVars _ hq_not]
            exact ihq hn.2
        exact hid_rest _ (by rw [zipParams_fst_eq hlen2_r]; exact hinlNotSpec.2)
      · have hnodup_r : ((posSpecParams sr).map Prod.fst).Nodup :=
          (List.nodup_append.mp hnodupSpec).2.1
        have hdisj_c0 : ∀ x ∈ c0.fvs.map Prod.fst, x ∉ (posSpecParams sr).map Prod.fst :=
          fun x hx hm => (List.nodup_append.mp hnodupSpec).2.2 x hx x hm rfl
        have hcfv_sub := cbSlotsOf_fvs_subset_specParams hmr
        simp only [posSpecParams]
        rw [zipParams_append hc0wf.2.2.2.1, substMany_append]
        have hid_c0 : ∀ ρ, (∀ x ∈ ρ.map Prod.fst, x ≠ inlP ∧ x ∉ c.fvs.map Prod.fst) →
            substMany ρ (subst origP (.var inlP) c.cbBody) = subst origP (.var inlP) c.cbBody := by
          intro ρ hcond; induction ρ with
          | nil => rfl
          | cons q qr ihq =>
            rcases hcond q.1 (List.mem_cons_self ..) with ⟨hne, hnf⟩
            have hq_not : q.1 ∉ freeVars (subst origP (.var inlP) c.cbBody) := by
              intro hm; rcases hEfvs q.1 hm with heq | hfv
              · exact hne heq
              · exact hnf hfv
            simp only [substMany, subst_not_mem_freeVars _ hq_not]
            exact ihq (fun x hx => hcond x (List.mem_cons_of_mem _ hx))
        rw [hid_c0 (zipParams c0.fvs c0.fvVals) (by
          rw [zipParams_fst_eq hc0wf.2.2.2.1]
          intro x hx
          exact ⟨fun heq => hinlNotSpec.1 (heq ▸ hx), fun hm => hdisj_c0 x hx (hcfv_sub x hm)⟩)]
        exact ih hcbs_r hrest
          (fun u hu => hvs1 u (List.mem_cons_of_mem _ hu))
          (fun u hu => hcl1 u (List.mem_cons_of_mem _ hu))
          hnodup_r hmr hinlNotSpec.2

theorem posSelfCallArgs_length_eq {origFn : Ident} {allSlots rem : List PosSpecSlot}
    {avoid : List Ident} {recArgs : List Expr}
    (h : PosSelfCallArgs origFn allSlots avoid rem recArgs) :
    recArgs.length = rem.length := by
  induction rem generalizing recArgs with
  | nil => cases h; rfl
  | cons sl sr ih =>
    cases h with
    | state _ _ hr => simp [ih hr]
    | callback _ hr => simp [ih hr]

theorem posSpecializeLoopList_length {origFn specFn : Ident} {slots : List PosSpecSlot}
    (es : List Expr) :
    (posSpecializeLoopList origFn specFn slots es).length = es.length := by
  induction es with
  | nil => simp [posSpecializeLoopList]
  | cons _ r ih => simp [posSpecializeLoopList, ih]

theorem cbSlotsOf_fParam_mem_orig {rem : List PosSpecSlot} {c : CbSlotSpec}
    (h : c ∈ cbSlotsOf rem) : c.fParam ∈ (posOrigParams rem).map Prod.fst := by
  induction rem with
  | nil => cases h
  | cons sl sr ih =>
    cases sl with
    | state _ => exact List.mem_cons_of_mem _ (ih h)
    | callback c0 =>
      simp only [cbSlotsOf, List.mem_cons] at h
      rcases h with rfl | hmr
      · exact List.mem_cons_self ..
      · exact List.mem_cons_of_mem _ (ih hmr)

theorem findCbSlot_of_mem_nodup {rem : List PosSpecSlot} {c : CbSlotSpec}
    (hnodup : ((posOrigParams rem).map Prod.fst).Nodup)
    (hmem : c ∈ cbSlotsOf rem) : findCbSlot? c.fParam rem = some c := by
  induction rem with
  | nil => cases hmem
  | cons sl sr ih =>
    cases sl with
    | state _ =>
      simp only [posOrigParams, List.map_cons] at hnodup
      exact ih (List.nodup_cons.mp hnodup).2 hmem
    | callback c0 =>
      simp only [posOrigParams, List.map_cons] at hnodup
      rcases List.nodup_cons.mp hnodup with ⟨hc0_not, hnodup_r⟩
      simp only [cbSlotsOf, List.mem_cons] at hmem
      rcases hmem with rfl | hmr
      · simp [findCbSlot?]
      · have hne : c0.fParam ≠ c.fParam :=
          fun heq => hc0_not (heq ▸ cbSlotsOf_fParam_mem_orig hmr)
        simp [findCbSlot?, beq_false_of_ne hne, ih hnodup_r hmr]

theorem posOrigParams_subset_avoid (slots : List PosSpecSlot) :
    ∀ z ∈ (posOrigParams slots).map Prod.fst,
      z ∈ allCbOrigNames slots ++ (posSpecParams slots).map Prod.fst := by
  induction slots with
  | nil => intro _ h; cases h
  | cons sl sr ih =>
    cases sl with
    | state p =>
      simp only [posOrigParams, posSpecParams, allCbOrigNames, List.map_cons, List.mem_cons, List.mem_append]
      rintro z (rfl | hmr)
      · exact Or.inr (Or.inl rfl)
      · rcases List.mem_append.mp (ih z hmr) with h1 | h2
        · exact Or.inl h1
        · exact Or.inr (Or.inr h2)
    | callback c =>
      simp only [posOrigParams, posSpecParams, allCbOrigNames, List.map_cons, List.map_append,
        List.cons_append, List.mem_cons, List.mem_append]
      rintro z (rfl | hmr)
      · exact Or.inl rfl
      · rcases List.mem_append.mp (ih z hmr) with h1 | h2
        · exact Or.inr (Or.inl h1)
        · exact Or.inr (Or.inr (Or.inr h2))

theorem posCallArgs_subst_expr_noCb {origFn specFn : Ident} {allSlots rem : List PosSpecSlot}
    {dom : Ident → Bool} {Φ2 : FunEnv}
    (hcbs : ∀ c ∈ cbSlotsOf rem, CbSlotWF dom Φ2 c)
    {args1 args2 : List Expr}
    (hrel : PosCallArgsRel origFn specFn allSlots rem args1 args2)
    (hvs1 : ∀ v ∈ args1, IsValue v) (hcl1 : ∀ v ∈ args1, freeVars v = [])
    {e : Expr}
    (hnoCb : ∀ c ∈ cbSlotsOf rem, c.fParam ∉ freeVars e)
    (hnoFv : ∀ z ∈ freeVars e, z ∉ allCbFvNames rem) :
    substMany (zipParams (posOrigParams rem) args1) e =
      substMany (zipParams (posSpecParams rem) args2) e := by
  induction rem generalizing args1 args2 e with
  | nil => cases hrel; rfl
  | cons sl sr ih =>
    cases hrel with
    | @state p _ v _ r1 r2 hr hrest =>
      rcases posSpecRel_val_left hr (hvs1 v (List.mem_cons_self ..)) with ⟨rfl, _⟩
      have hv_cl : freeVars v = [] := hcl1 v (List.mem_cons_self ..)
      have hsub_fv : ∀ z ∈ freeVars (subst p.1 v e), z ∈ freeVars e := fun z hz =>
        (substMany_freeVars_subset [(p.1, v)]
          (fun q hq => by simp at hq; rcases hq with ⟨_, rfl⟩; exact hv_cl)
          e z (by simpa [substMany] using hz)).2
      simp only [posOrigParams, posSpecParams, zipParams, List.map_cons, List.zip_cons_cons, substMany]
      exact ih hcbs hrest
        (fun u hu => hvs1 u (List.mem_cons_of_mem _ hu))
        (fun u hu => hcl1 u (List.mem_cons_of_mem _ hu))
        (fun c hc hm => hnoCb c hc (hsub_fv _ hm))
        (fun z hz => hnoFv z (hsub_fv z hz))
    | @callback c _ r1 r2 hrest =>
      have hcwf := hcbs c (List.mem_cons_self ..)
      have hcbs_r : ∀ c' ∈ cbSlotsOf sr, CbSlotWF dom Φ2 c' :=
        fun c' hm => hcbs c' (List.mem_cons_of_mem _ hm)
      have hcf_not : c.fParam ∉ freeVars e := hnoCb c (List.mem_cons_self ..)
      simp only [allCbFvNames, List.mem_append] at hnoFv
      have hid_fvs : ∀ ρ, (∀ x ∈ ρ.map Prod.fst, x ∉ freeVars e) → substMany ρ e = e := by
        intro ρ hdisj; induction ρ with
        | nil => rfl
        | cons q qr ihq =>
          have hqn : q.1 ∉ freeVars e := hdisj q.1 (List.mem_cons_self ..)
          simp only [substMany, subst_not_mem_freeVars e hqn]
          exact ihq (fun x hx => hdisj x (List.mem_cons_of_mem _ hx))
      simp only [posOrigParams, posSpecParams]
      rw [zipParams_append hcwf.2.2.2.1, substMany_append,
          hid_fvs (zipParams c.fvs c.fvVals) (by
            rw [zipParams_fst_eq hcwf.2.2.2.1]
            exact fun x hx hm => hnoFv x hm (Or.inl hx))]
      simp only [zipParams, List.map_cons, List.zip_cons_cons, substMany,
        subst_not_mem_freeVars e hcf_not]
      exact ih hcbs_r hrest
        (fun u hu => hvs1 u (List.mem_cons_of_mem _ hu))
        (fun u hu => hcl1 u (List.mem_cons_of_mem _ hu))
        (fun c' hc' => hnoCb c' (List.mem_cons_of_mem _ hc'))
        (fun z hz hm => hnoFv z hz (Or.inr hm))

/- Positional Loop Body Specialization Substitution Theorem (`posSpecEligible_subst_rel`). -/
mutual
theorem posSpecEligible_subst_rel
    (origFn specFn : Ident) (slots : List PosSpecSlot)
    {dom : Ident → Bool} {Φ2 : FunEnv}
    (hcbs : ∀ c ∈ cbSlotsOf slots, CbSlotWF dom Φ2 c)
    {initArgs1 initArgs2 : List Expr}
    (hinitRel : PosCallArgsRel origFn specFn slots slots initArgs1 initArgs2)
    (hinitVal : ∀ v ∈ initArgs1, IsValue v)
    (hinitCl : ∀ v ∈ initArgs1, freeVars v = [])
    (hnodupOrig : ((posOrigParams slots).map Prod.fst).Nodup)
    (hnodupSpec : ((posSpecParams slots).map Prod.fst).Nodup)
    (hinlDisjSpec : ∀ c ∈ cbSlotsOf slots, ∀ inlP, c.lowering = .inline1 inlP →
      inlP ∉ (posSpecParams slots).map Prod.fst)
    {e : Expr}
    (hnoFv : ∀ z ∈ freeVars e, z ∉ allCbFvNames slots)
    (helig : PosSpecEligible origFn slots
      (allCbOrigNames slots ++ (posSpecParams slots).map Prod.fst) e) :
    PosSpecRel origFn specFn slots
      (substMany (zipParams (posOrigParams slots) initArgs1) e)
      (substMany (zipParams (posSpecParams slots) initArgs2)
        (posSpecializeLoopExpr origFn specFn slots e)) := by
  have hlen1 := (posCallArgsRel_allVal_left hcbs hinitRel hinitVal).2.1
  have hlen2 := (posCallArgsRel_allVal_left hcbs hinitRel hinitVal).2.2
  cases helig with
  | lit l =>
    have h1 : ∀ ρ, substMany ρ (.lit l) = .lit l := fun ρ => by
      induction ρ with | nil => rfl | cons _ _ ih => exact ih
    rw [posSpecializeLoopExpr, h1, h1]; exact .lit l
  | loc l =>
    have h1 : ∀ ρ, substMany ρ (.loc l) = .loc l := fun ρ => by
      induction ρ with | nil => rfl | cons _ _ ih => exact ih
    rw [posSpecializeLoopExpr, h1, h1]; exact .loc l
  | taskRef tid =>
    have h1 : ∀ ρ, substMany ρ (.taskRef tid) = .taskRef tid := fun ρ => by
      induction ρ with | nil => rfl | cons _ _ ih => exact ih
    rw [posSpecializeLoopExpr, h1, h1]; exact .taskRef tid
  | syncRef k id =>
    have h1 : ∀ ρ, substMany ρ (.syncRef k id) = .syncRef k id := fun ρ => by
      induction ρ with | nil => rfl | cons _ _ ih => exact ih
    rw [posSpecializeLoopExpr, h1, h1]; exact .syncRef k id
  | trap t =>
    have h1 : ∀ ρ, substMany ρ (.trap t) = .trap t := fun ρ => by
      induction ρ with | nil => rfl | cons _ _ ih => exact ih
    rw [posSpecializeLoopExpr, h1, h1]; exact .trap t
  | @var x hnotCb =>
    rw [posSpecializeLoopExpr,
        posCallArgs_subst_nonCbVar hcbs hinitRel hinitVal hinitCl hnotCb
          (hnoFv x (by simp [freeVars]))]
    exact PosSpecRel.refl _ _ _ _
  | @lam m ps ret body hnoCb _ =>
    rw [posSpecializeLoopExpr,
        posCallArgs_subst_expr_noCb hcbs hinitRel hinitVal hinitCl hnoCb hnoFv]
    exact PosSpecRel.refl _ _ _ _
  | tuple hes =>
    rcases substMany_map_helper (zipParams (posOrigParams slots) initArgs1) with ⟨ht1, _, _, _, _⟩
    rcases substMany_map_helper (zipParams (posSpecParams slots) initArgs2) with ⟨ht2, _, _, _, _⟩
    simp only [posSpecializeLoopExpr, ht1, ht2]
    exact .tuple (posSpecEligibleList_subst_rel origFn specFn slots hcbs hinitRel hinitVal hinitCl
      hnodupOrig hnodupSpec hinlDisjSpec hnoFv hes)
  | block hes =>
    rcases substMany_map_helper (zipParams (posOrigParams slots) initArgs1) with ⟨_, hb1, _, _, _⟩
    rcases substMany_map_helper (zipParams (posSpecParams slots) initArgs2) with ⟨_, hb2, _, _, _⟩
    simp only [posSpecializeLoopExpr, hb1, hb2]
    exact .block (posSpecEligibleList_subst_rel origFn specFn slots hcbs hinitRel hinitVal hinitCl
      hnodupOrig hnodupSpec hinlDisjSpec hnoFv hes)
  | @cbCallFlat f c flatName cbArgs hfind hlow hcbLen hargs =>
    rcases substMany_map_helper (zipParams (posOrigParams slots) initArgs1) with ⟨_, _, ha1, _, _⟩
    rcases substMany_map_helper (zipParams (posSpecParams slots) initArgs2) with ⟨_, _, _, hd2, _⟩
    rcases findCbSlot_mem hfind with ⟨hc_mem, _⟩
    have hf_lhs := posCallArgs_subst_cbVar hcbs hinitRel hnodupOrig hfind
    have hfvs_rhs := posCallArgs_subst_cbFvs hcbs hinitRel hinitVal hinitCl hnodupSpec hc_mem
    have hnoFvArgs : ∀ z ∈ freeVarsList cbArgs, z ∉ allCbFvNames slots :=
      fun z hz => hnoFv z (by simp [freeVars, hz])
    simp only [posSpecializeLoopExpr, hfind, lowerCbCallExpr, hlow, ha1, hd2, hf_lhs, List.map_append]
    rw [hfvs_rhs]
    exact .specCbFlat hc_mem hlow (by simp [hcbLen])
      (posSpecEligibleList_subst_rel origFn specFn slots hcbs hinitRel hinitVal hinitCl
        hnodupOrig hnodupSpec hinlDisjSpec hnoFvArgs hargs)
  | @cbCallInline1 f c inlP origP pTy arg hfind hlow hcp harg =>
    rcases substMany_map_helper (zipParams (posOrigParams slots) initArgs1) with ⟨_, _, ha1, _, _⟩
    rcases findCbSlot_mem hfind with ⟨hc_mem, _⟩
    have hf_lhs := posCallArgs_subst_cbVar hcbs hinitRel hnodupOrig hfind
    have hinlNot := hinlDisjSpec c hc_mem inlP hlow
    have hnoFvArg : ∀ z ∈ freeVars arg, z ∉ allCbFvNames slots :=
      fun z hz => hnoFv z (by simp [freeVars, freeVarsList, hz])
    simp only [posSpecializeLoopExpr, posSpecializeLoopList, hfind, lowerCbCallExpr, hlow, hcp,
      ha1, List.map_cons, List.map_nil, hf_lhs]
    rw [posCallArgs_subst_inlineBody hcbs hinitRel hinitVal hinitCl hnodupSpec hc_mem hcp hinlNot]
    exact .specCbInline1 hc_mem hlow hcp
      (posSpecEligible_subst_rel origFn specFn slots hcbs hinitRel hinitVal hinitCl
        hnodupOrig hnodupSpec hinlDisjSpec hnoFvArg harg)
  | @applyGen fn args hnotVar hfn hargs =>
    rcases substMany_map_helper (zipParams (posOrigParams slots) initArgs1) with ⟨_, _, ha1, _, _⟩
    rcases substMany_map_helper (zipParams (posSpecParams slots) initArgs2) with ⟨_, _, ha2, _, _⟩
    have hspec : posSpecializeLoopExpr origFn specFn slots (.apply fn args) =
        .apply (posSpecializeLoopExpr origFn specFn slots fn)
          (posSpecializeLoopList origFn specFn slots args) := by
      cases fn with
      | var z => simp [posSpecializeLoopExpr, hnotVar z rfl]
      | _ => simp [posSpecializeLoopExpr]
    rw [hspec, ha1, ha2]
    exact .apply
      (posSpecEligible_subst_rel origFn specFn slots hcbs hinitRel hinitVal hinitCl
        hnodupOrig hnodupSpec hinlDisjSpec (fun z hz => hnoFv z (by simp [freeVars, hz])) hfn)
      (posSpecEligibleList_subst_rel origFn specFn slots hcbs hinitRel hinitVal hinitCl
        hnodupOrig hnodupSpec hinlDisjSpec (fun z hz => hnoFv z (by simp [freeVars, hz])) hargs)
  | @selfCall recArgs hargs =>
    rcases substMany_map_helper (zipParams (posOrigParams slots) initArgs1) with ⟨_, _, _, hd1, _⟩
    rcases substMany_map_helper (zipParams (posSpecParams slots) initArgs2) with ⟨_, _, _, hd2, _⟩
    have hrecLen : recArgs.length = slots.length := posSelfCallArgs_length_eq hargs
    have hcond : (origFn == origFn && recArgs.length == slots.length) = true := by simp [hrecLen]
    simp only [posSpecializeLoopExpr, hcond, ↓reduceIte, hd1, hd2]
    exact .specSelfCall
      (posSelfCallArgs_subst_rel origFn specFn slots hcbs hinitRel hinitVal hinitCl
        hnodupOrig hnodupSpec hinlDisjSpec slots (fun _ h => h)
        (fun z hz => hnoFv z (by simp [freeVars, hz])) hargs)
  | @applyDirOther nm args hne hargs =>
    rcases substMany_map_helper (zipParams (posOrigParams slots) initArgs1) with ⟨_, _, _, hd1, _⟩
    rcases substMany_map_helper (zipParams (posSpecParams slots) initArgs2) with ⟨_, _, _, hd2, _⟩
    have hnm : (nm == origFn) = false := beq_false_of_ne hne
    simp only [posSpecializeLoopExpr, hnm, Bool.false_and, Bool.false_eq_true, ↓reduceIte, hd1, hd2]
    exact .applyDir
      (posSpecEligibleList_subst_rel origFn specFn slots hcbs hinitRel hinitVal hinitCl
        hnodupOrig hnodupSpec hinlDisjSpec hnoFv hargs)
  | @bin op _ _ ha hb =>
    have hbin : ∀ ρ x y, substMany ρ (.bin op x y) = .bin op (substMany ρ x) (substMany ρ y) :=
      fun ρ x y => by induction ρ generalizing x y with | nil => rfl | cons _ _ ih => exact ih _ _
    simp only [posSpecializeLoopExpr, hbin]
    exact .bin
      (posSpecEligible_subst_rel origFn specFn slots hcbs hinitRel hinitVal hinitCl
        hnodupOrig hnodupSpec hinlDisjSpec (fun z hz => hnoFv z (by simp [freeVars, hz])) ha)
      (posSpecEligible_subst_rel origFn specFn slots hcbs hinitRel hinitVal hinitCl
        hnodupOrig hnodupSpec hinlDisjSpec (fun z hz => hnoFv z (by simp [freeVars, hz])) hb)
  | @un op _ ha =>
    have hun : ∀ ρ x, substMany ρ (.un op x) = .un op (substMany ρ x) :=
      fun ρ x => by induction ρ generalizing x with | nil => rfl | cons _ _ ih => exact ih _
    simp only [posSpecializeLoopExpr, hun]
    exact .un (posSpecEligible_subst_rel origFn specFn slots hcbs hinitRel hinitVal hinitCl
      hnodupOrig hnodupSpec hinlDisjSpec hnoFv ha)
  | @let_ y a b hyAvoid ha hb =>
    have hy1 : y ∉ (zipParams (posOrigParams slots) initArgs1).map Prod.fst := by
      rw [zipParams_fst_eq hlen1]
      exact fun hm => hyAvoid (posOrigParams_subset_avoid slots y hm)
    have hy2 : y ∉ (zipParams (posSpecParams slots) initArgs2).map Prod.fst := by
      rw [zipParams_fst_eq hlen2]
      exact fun hm => hyAvoid (List.mem_append_right _ hm)
    have hsub_fv : ∀ x ∈ allCbFvNames slots, x ∈ (posSpecParams slots).map Prod.fst := by
      clear hinitRel hinitVal hinitCl hnodupOrig hnodupSpec hinlDisjSpec hnoFv hyAvoid ha hb hy1 hy2 hlen1 hlen2 hcbs
      induction slots with
      | nil => intro _ h; cases h
      | cons sl sr ihs =>
        cases sl with
        | state q => simp only [allCbFvNames, posSpecParams, List.map_cons]; intro x hx; exact List.mem_cons_of_mem _ (ihs x hx)
        | callback c =>
          simp only [allCbFvNames, posSpecParams, List.map_append, List.mem_append]
          rintro x (h1 | h2)
          · exact Or.inl h1
          · exact Or.inr (ihs x h2)
    have hnoFvB : ∀ z ∈ freeVars b, z ∉ allCbFvNames slots := by
      intro z hz hmem
      by_cases hzy : z = y
      · subst hzy; exact hyAvoid (List.mem_append_right _ (hsub_fv z hmem))
      · exact hnoFv z (by simp [freeVars, hz, hzy]) hmem
    simp only [posSpecializeLoopExpr, substMany_let_not_mem _ hy1, substMany_let_not_mem _ hy2]
    exact .let_
      (posSpecEligible_subst_rel origFn specFn slots hcbs hinitRel hinitVal hinitCl
        hnodupOrig hnodupSpec hinlDisjSpec (fun z hz => hnoFv z (by simp [freeVars, hz])) ha)
      (posSpecEligible_subst_rel origFn specFn slots hcbs hinitRel hinitVal hinitCl
        hnodupOrig hnodupSpec hinlDisjSpec hnoFvB hb)
  | if_ hc ht he2 =>
    have hif : ∀ ρ c t e, substMany ρ (.if_ c t e) = .if_ (substMany ρ c) (substMany ρ t) (substMany ρ e) :=
      fun ρ c t e => by induction ρ generalizing c t e with | nil => rfl | cons _ _ ih => exact ih _ _ _
    simp only [posSpecializeLoopExpr, hif]
    exact .if_
      (posSpecEligible_subst_rel origFn specFn slots hcbs hinitRel hinitVal hinitCl
        hnodupOrig hnodupSpec hinlDisjSpec (fun z hz => hnoFv z (by simp [freeVars, hz])) hc)
      (posSpecEligible_subst_rel origFn specFn slots hcbs hinitRel hinitVal hinitCl
        hnodupOrig hnodupSpec hinlDisjSpec (fun z hz => hnoFv z (by simp [freeVars, hz])) ht)
      (posSpecEligible_subst_rel origFn specFn slots hcbs hinitRel hinitVal hinitCl
        hnodupOrig hnodupSpec hinlDisjSpec (fun z hz => hnoFv z (by simp [freeVars, hz])) he2)
  | while_ hc hb =>
    have hwh : ∀ ρ c b, substMany ρ (.while_ c b) = .while_ (substMany ρ c) (substMany ρ b) :=
      fun ρ c b => by induction ρ generalizing c b with | nil => rfl | cons _ _ ih => exact ih _ _
    simp only [posSpecializeLoopExpr, hwh]
    exact .while_
      (posSpecEligible_subst_rel origFn specFn slots hcbs hinitRel hinitVal hinitCl
        hnodupOrig hnodupSpec hinlDisjSpec (fun z hz => hnoFv z (by simp [freeVars, hz])) hc)
      (posSpecEligible_subst_rel origFn specFn slots hcbs hinitRel hinitVal hinitCl
        hnodupOrig hnodupSpec hinlDisjSpec (fun z hz => hnoFv z (by simp [freeVars, hz])) hb)
  | @match_ s arms hs harms =>
    have hdisj : ∀ a ∈ arms, ∀ z ∈ patBoundNames a.1,
        z ∉ allCbOrigNames slots ++ (posSpecParams slots).map Prod.fst := by
      clear hs hnoFv
      induction arms with
      | nil => intro _ h; cases h
      | cons a0 ar iha =>
        cases harms with
        | cons hp _ hrs =>
          intro a ha; rcases List.mem_cons.mp ha with rfl | har
          · exact hp
          · exact iha hrs a har
    have hdisj1 : ∀ a ∈ arms, ∀ z ∈ patBoundNames a.1,
        z ∉ (zipParams (posOrigParams slots) initArgs1).map Prod.fst := by
      rw [zipParams_fst_eq hlen1]
      exact fun a ha z hz hm => hdisj a ha z hz (posOrigParams_subset_avoid slots z hm)
    have hdisj2 : ∀ a ∈ posSpecializeLoopArms origFn specFn slots arms, ∀ z ∈ patBoundNames a.1,
        z ∉ (zipParams (posSpecParams slots) initArgs2).map Prod.fst := by
      rw [zipParams_fst_eq hlen2]
      have hfst : ∀ as, (posSpecializeLoopArms origFn specFn slots as).map Prod.fst = as.map Prod.fst := by
        intro as; induction as with
        | nil => simp [posSpecializeLoopArms]
        | cons a0 ar iha => rcases a0 with ⟨p0, b0⟩; simp [posSpecializeLoopArms, iha]
      intro a ha z hz hm
      have ha1 : a.1 ∈ arms.map Prod.fst := by rw [← hfst]; exact List.mem_map.mpr ⟨a, ha, rfl⟩
      rcases List.mem_map.mp ha1 with ⟨orig, horig, heq1⟩
      rw [← heq1] at hz
      exact hdisj orig horig z hz (List.mem_append_right _ hm)
    simp only [posSpecializeLoopExpr, substMany_match_disjoint _ _ _ hdisj1,
      substMany_match_disjoint _ _ _ hdisj2]
    exact .match_
      (posSpecEligible_subst_rel origFn specFn slots hcbs hinitRel hinitVal hinitCl
        hnodupOrig hnodupSpec hinlDisjSpec (fun z hz => hnoFv z (by simp [freeVars, hz])) hs)
      (posSpecEligibleArms_subst_rel origFn specFn slots hcbs hinitRel hinitVal hinitCl
        hnodupOrig hnodupSpec hinlDisjSpec (fun z hz => hnoFv z (by simp [freeVars, hz])) harms)
  | makeData hes =>
    rcases substMany_map_helper (zipParams (posOrigParams slots) initArgs1) with ⟨_, _, _, _, hm1⟩
    rcases substMany_map_helper (zipParams (posSpecParams slots) initArgs2) with ⟨_, _, _, _, hm2⟩
    simp only [posSpecializeLoopExpr, hm1, hm2]
    exact .makeData (posSpecEligibleList_subst_rel origFn specFn slots hcbs hinitRel hinitVal hinitCl
      hnodupOrig hnodupSpec hinlDisjSpec hnoFv hes)
  | getTag ha =>
    have hgt : ∀ ρ x, substMany ρ (.getTag x) = .getTag (substMany ρ x) :=
      fun ρ x => by induction ρ generalizing x with | nil => rfl | cons _ _ ih => exact ih _
    simp only [posSpecializeLoopExpr, hgt]
    exact .getTag (posSpecEligible_subst_rel origFn specFn slots hcbs hinitRel hinitVal hinitCl
      hnodupOrig hnodupSpec hinlDisjSpec hnoFv ha)
  | cellNew ha =>
    have hcn : ∀ ρ x, substMany ρ (.cellNew x) = .cellNew (substMany ρ x) :=
      fun ρ x => by induction ρ generalizing x with | nil => rfl | cons _ _ ih => exact ih _
    simp only [posSpecializeLoopExpr, hcn]
    exact .cellNew (posSpecEligible_subst_rel origFn specFn slots hcbs hinitRel hinitVal hinitCl
      hnodupOrig hnodupSpec hinlDisjSpec hnoFv ha)
  | cellGet ha =>
    have hcg : ∀ ρ x, substMany ρ (.cellGet x) = .cellGet (substMany ρ x) :=
      fun ρ x => by induction ρ generalizing x with | nil => rfl | cons _ _ ih => exact ih _
    simp only [posSpecializeLoopExpr, hcg]
    exact .cellGet (posSpecEligible_subst_rel origFn specFn slots hcbs hinitRel hinitVal hinitCl
      hnodupOrig hnodupSpec hinlDisjSpec hnoFv ha)
  | cellSet ha hb =>
    have hcs : ∀ ρ x y, substMany ρ (.cellSet x y) = .cellSet (substMany ρ x) (substMany ρ y) :=
      fun ρ x y => by induction ρ generalizing x y with | nil => rfl | cons _ _ ih => exact ih _ _
    simp only [posSpecializeLoopExpr, hcs]
    exact .cellSet
      (posSpecEligible_subst_rel origFn specFn slots hcbs hinitRel hinitVal hinitCl
        hnodupOrig hnodupSpec hinlDisjSpec (fun z hz => hnoFv z (by simp [freeVars, hz])) ha)
      (posSpecEligible_subst_rel origFn specFn slots hcbs hinitRel hinitVal hinitCl
        hnodupOrig hnodupSpec hinlDisjSpec (fun z hz => hnoFv z (by simp [freeVars, hz])) hb)
termination_by sizeOf e

theorem posSpecEligibleList_subst_rel
    (origFn specFn : Ident) (slots : List PosSpecSlot)
    {dom : Ident → Bool} {Φ2 : FunEnv}
    (hcbs : ∀ c ∈ cbSlotsOf slots, CbSlotWF dom Φ2 c)
    {initArgs1 initArgs2 : List Expr}
    (hinitRel : PosCallArgsRel origFn specFn slots slots initArgs1 initArgs2)
    (hinitVal : ∀ v ∈ initArgs1, IsValue v)
    (hinitCl : ∀ v ∈ initArgs1, freeVars v = [])
    (hnodupOrig : ((posOrigParams slots).map Prod.fst).Nodup)
    (hnodupSpec : ((posSpecParams slots).map Prod.fst).Nodup)
    (hinlDisjSpec : ∀ c ∈ cbSlotsOf slots, ∀ inlP, c.lowering = .inline1 inlP →
      inlP ∉ (posSpecParams slots).map Prod.fst)
    {es : List Expr}
    (hnoFv : ∀ z ∈ freeVarsList es, z ∉ allCbFvNames slots)
    (helig : PosSpecEligibleList origFn slots
      (allCbOrigNames slots ++ (posSpecParams slots).map Prod.fst) es) :
    PosSpecRelList origFn specFn slots
      (es.map (substMany (zipParams (posOrigParams slots) initArgs1)))
      ((posSpecializeLoopList origFn specFn slots es).map
        (substMany (zipParams (posSpecParams slots) initArgs2))) := by
  cases helig with
  | nil => simp only [posSpecializeLoopList, List.map_nil]; exact .nil
  | cons he hes =>
    simp only [posSpecializeLoopList, List.map_cons]
    exact .cons
      (posSpecEligible_subst_rel origFn specFn slots hcbs hinitRel hinitVal hinitCl
        hnodupOrig hnodupSpec hinlDisjSpec (fun z hz => hnoFv z (by simp [freeVarsList, hz])) he)
      (posSpecEligibleList_subst_rel origFn specFn slots hcbs hinitRel hinitVal hinitCl
        hnodupOrig hnodupSpec hinlDisjSpec (fun z hz => hnoFv z (by simp [freeVarsList, hz])) hes)
termination_by sizeOf es

theorem posSpecEligibleArms_subst_rel
    (origFn specFn : Ident) (slots : List PosSpecSlot)
    {dom : Ident → Bool} {Φ2 : FunEnv}
    (hcbs : ∀ c ∈ cbSlotsOf slots, CbSlotWF dom Φ2 c)
    {initArgs1 initArgs2 : List Expr}
    (hinitRel : PosCallArgsRel origFn specFn slots slots initArgs1 initArgs2)
    (hinitVal : ∀ v ∈ initArgs1, IsValue v)
    (hinitCl : ∀ v ∈ initArgs1, freeVars v = [])
    (hnodupOrig : ((posOrigParams slots).map Prod.fst).Nodup)
    (hnodupSpec : ((posSpecParams slots).map Prod.fst).Nodup)
    (hinlDisjSpec : ∀ c ∈ cbSlotsOf slots, ∀ inlP, c.lowering = .inline1 inlP →
      inlP ∉ (posSpecParams slots).map Prod.fst)
    {arms : List (Pat × Expr)}
    (hnoFv : ∀ z ∈ freeVarsArms arms, z ∉ allCbFvNames slots)
    (helig : PosSpecEligibleArms origFn slots
      (allCbOrigNames slots ++ (posSpecParams slots).map Prod.fst) arms) :
    PosSpecRelArms origFn specFn slots
      (arms.map fun a => (a.1, substMany (zipParams (posOrigParams slots) initArgs1) a.2))
      ((posSpecializeLoopArms origFn specFn slots arms).map
        fun a => (a.1, substMany (zipParams (posSpecParams slots) initArgs2) a.2)) := by
  cases helig with
  | nil => simp only [posSpecializeLoopArms, List.map_nil]; exact .nil
  | @cons p body rest hpAvoid hb hrs =>
    simp only [posSpecializeLoopArms, List.map_cons]
    have hsub_fv : ∀ x ∈ allCbFvNames slots, x ∈ (posSpecParams slots).map Prod.fst := by
      clear hinitRel hinitVal hinitCl hnodupOrig hnodupSpec hinlDisjSpec hnoFv hpAvoid hb hrs hcbs
      induction slots with
      | nil => intro _ h; cases h
      | cons sl sr ihs =>
        cases sl with
        | state q => simp only [allCbFvNames, posSpecParams, List.map_cons]; intro x hx; exact List.mem_cons_of_mem _ (ihs x hx)
        | callback c =>
          simp only [allCbFvNames, posSpecParams, List.map_append, List.mem_append]
          rintro x (h1 | h2)
          · exact Or.inl h1
          · exact Or.inr (ihs x h2)
    have hnoFvBody : ∀ z ∈ freeVars body, z ∉ allCbFvNames slots := by
      intro z hz hmem
      by_cases hzp : z ∈ patBoundNames p
      · exact hpAvoid z hzp (List.mem_append_right _ (hsub_fv z hmem))
      · exact hnoFv z (by simp [freeVarsArms, hz, hzp]) hmem
    exact .cons
      (posSpecEligible_subst_rel origFn specFn slots hcbs hinitRel hinitVal hinitCl
        hnodupOrig hnodupSpec hinlDisjSpec hnoFvBody hb)
      (posSpecEligibleArms_subst_rel origFn specFn slots hcbs hinitRel hinitVal hinitCl
        hnodupOrig hnodupSpec hinlDisjSpec (fun z hz => hnoFv z (by simp [freeVarsArms, hz])) hrs)
termination_by sizeOf arms

theorem posSelfCallArgs_subst_rel
    (origFn specFn : Ident) (slots : List PosSpecSlot)
    {dom : Ident → Bool} {Φ2 : FunEnv}
    (hcbs : ∀ c ∈ cbSlotsOf slots, CbSlotWF dom Φ2 c)
    {initArgs1 initArgs2 : List Expr}
    (hinitRel : PosCallArgsRel origFn specFn slots slots initArgs1 initArgs2)
    (hinitVal : ∀ v ∈ initArgs1, IsValue v)
    (hinitCl : ∀ v ∈ initArgs1, freeVars v = [])
    (hnodupOrig : ((posOrigParams slots).map Prod.fst).Nodup)
    (hnodupSpec : ((posSpecParams slots).map Prod.fst).Nodup)
    (hinlDisjSpec : ∀ c ∈ cbSlotsOf slots, ∀ inlP, c.lowering = .inline1 inlP →
      inlP ∉ (posSpecParams slots).map Prod.fst)
    (rem : List PosSpecSlot)
    (hsub : ∀ c ∈ cbSlotsOf rem, c ∈ cbSlotsOf slots)
    {rArgs : List Expr}
    (hnoFv : ∀ z ∈ freeVarsList rArgs, z ∉ allCbFvNames slots)
    (hargs : PosSelfCallArgs origFn slots
      (allCbOrigNames slots ++ (posSpecParams slots).map Prod.fst) rem rArgs) :
    PosCallArgsRel origFn specFn slots rem
      (rArgs.map (substMany (zipParams (posOrigParams slots) initArgs1)))
      ((expandArgsByMask (slotExpansionMask rem)
        (posSpecializeLoopList origFn specFn slots rArgs)).map
        (substMany (zipParams (posSpecParams slots) initArgs2))) := by
  cases hargs with
  | nil =>
    simp only [posSpecializeLoopList, slotExpansionMask, expandArgsByMask, List.map_nil]
    exact .nil
  | @state p rem' _ _ ha hrest =>
    simp only [posSpecializeLoopList, slotExpansionMask, expandArgsByMask, List.map_cons]
    exact .state p
      (posSpecEligible_subst_rel origFn specFn slots hcbs hinitRel hinitVal hinitCl
        hnodupOrig hnodupSpec hinlDisjSpec (fun z hz => hnoFv z (by simp [freeVarsList, hz])) ha)
      (posSelfCallArgs_subst_rel origFn specFn slots hcbs hinitRel hinitVal hinitCl
        hnodupOrig hnodupSpec hinlDisjSpec rem' hsub
        (fun z hz => hnoFv z (by simp [freeVarsList, hz])) hrest)
  | callback c hrest =>
    have hc_mem : c ∈ cbSlotsOf slots := hsub c (List.mem_cons_self ..)
    have hfind := findCbSlot_of_mem_nodup hnodupOrig hc_mem
    have hf_lhs := posCallArgs_subst_cbVar hcbs hinitRel hnodupOrig hfind
    have hfvs_rhs := posCallArgs_subst_cbFvs hcbs hinitRel hinitVal hinitCl hnodupSpec hc_mem
    simp only [posSpecializeLoopList, slotExpansionMask, expandArgsByMask,
      List.map_cons, List.map_append, hf_lhs, hfvs_rhs]
    exact .callback c
      (posSelfCallArgs_subst_rel origFn specFn slots hcbs hinitRel hinitVal hinitCl
        hnodupOrig hnodupSpec hinlDisjSpec _
        (fun c' hm => hsub c' (List.mem_cons_of_mem _ hm))
        (fun z hz => hnoFv z (by simp [freeVarsList, hz])) hrest)
termination_by sizeOf rArgs
end

mutual
theorem subst_comm_closed {x y : Ident} {vx vy : Expr}
    (hne : x ≠ y) (hvx : freeVars vx = []) (hvy : freeVars vy = []) :
    (e : Expr) → subst x vx (subst y vy e) = subst y vy (subst x vx e)
  | .lit _ | .loc _ | .taskRef _ | .syncRef _ _ | .trap _ => rfl
  | .var z => by
    simp only [subst]
    cases hzy : (z == y)
    · cases hzx : (z == x)
      · simp [subst, hzy, hzx]
      · simp only [Bool.false_eq_true, ↓reduceIte, subst, hzx]
        exact (subst_not_mem_freeVars vx (by simp [hvx])).symm
    · have hzx : (z == x) = false := by
        have := eq_of_beq hzy; subst this; exact beq_false_of_ne hne.symm
      simp only [↓reduceIte, hzx, Bool.false_eq_true, subst, hzy]
      exact subst_not_mem_freeVars vy (by simp [hvy])
  | .tuple es => by simp [subst, substList_comm_closed hne hvx hvy es]
  | .block es => by simp [subst, substList_comm_closed hne hvx hvy es]
  | .lam _ ps _ body => by
    simp only [subst]
    cases h1 : ps.any (fun p => p.1 == y) <;> cases h2 : ps.any (fun p => p.1 == x) <;>
      simp [subst, h1, h2, subst_comm_closed hne hvx hvy body]
  | .apply fn args => by
    simp [subst, subst_comm_closed hne hvx hvy fn, substList_comm_closed hne hvx hvy args]
  | .applyDir _ args => by simp [subst, substList_comm_closed hne hvx hvy args]
  | .bin _ a b => by
    simp [subst, subst_comm_closed hne hvx hvy a, subst_comm_closed hne hvx hvy b]
  | .un _ a => by simp [subst, subst_comm_closed hne hvx hvy a]
  | .let_ z a b => by
    simp only [subst]
    cases h1 : (z == y) <;> cases h2 : (z == x) <;>
      simp [subst, h1, h2, subst_comm_closed hne hvx hvy a, subst_comm_closed hne hvx hvy b]
  | .if_ c t e2 => by
    simp [subst, subst_comm_closed hne hvx hvy c, subst_comm_closed hne hvx hvy t,
      subst_comm_closed hne hvx hvy e2]
  | .while_ c b => by
    simp [subst, subst_comm_closed hne hvx hvy c, subst_comm_closed hne hvx hvy b]
  | .match_ s arms => by
    simp [subst, subst_comm_closed hne hvx hvy s, substArms_comm_closed hne hvx hvy arms]
  | .makeData _ _ es => by simp [subst, substList_comm_closed hne hvx hvy es]
  | .getTag a => by simp [subst, subst_comm_closed hne hvx hvy a]
  | .cellNew a => by simp [subst, subst_comm_closed hne hvx hvy a]
  | .cellGet a => by simp [subst, subst_comm_closed hne hvx hvy a]
  | .cellSet a b => by
    simp [subst, subst_comm_closed hne hvx hvy a, subst_comm_closed hne hvx hvy b]
  | .spawn a => by simp [subst, subst_comm_closed hne hvx hvy a]
  | .await a => by simp [subst, subst_comm_closed hne hvx hvy a]
  | .concPrim _ es => by simp [subst, substList_comm_closed hne hvx hvy es]
termination_by e => sizeOf e

theorem substList_comm_closed {x y : Ident} {vx vy : Expr}
    (hne : x ≠ y) (hvx : freeVars vx = []) (hvy : freeVars vy = []) :
    (es : List Expr) → substList x vx (substList y vy es) = substList y vy (substList x vx es)
  | [] => rfl
  | e :: r => by
    simp [substList, subst_comm_closed hne hvx hvy e, substList_comm_closed hne hvx hvy r]
termination_by es => sizeOf es

theorem substArms_comm_closed {x y : Ident} {vx vy : Expr}
    (hne : x ≠ y) (hvx : freeVars vx = []) (hvy : freeVars vy = []) :
    (arms : List (Pat × Expr)) → substArms x vx (substArms y vy arms) =
      substArms y vy (substArms x vx arms)
  | [] => rfl
  | (p, b) :: r => by
    simp only [substArms, substArms_comm_closed hne hvx hvy r]
    cases h1 : (patBoundNames p).contains y <;> cases h2 : (patBoundNames p).contains x <;>
      simp [subst_comm_closed hne hvx hvy b]
termination_by arms => sizeOf arms
end

theorem subst_substMany_closed_comm {x : Ident} {vx : Expr}
    (ρ : List (Ident × Expr)) (e : Expr)
    (hx : x ∉ ρ.map Prod.fst) (hvx : freeVars vx = [])
    (hρ : ∀ p ∈ ρ, freeVars p.2 = []) :
    subst x vx (substMany ρ e) = substMany ρ (subst x vx e) := by
  induction ρ generalizing e with
  | nil => rfl
  | cons p r ih =>
    simp only [List.map_cons, List.mem_cons, not_or] at hx
    simp only [substMany]
    rw [ih _ hx.2 (fun q hq => hρ q (List.mem_cons_of_mem _ hq)),
        subst_comm_closed hx.1 hvx (hρ p (List.mem_cons_self ..)) e]

theorem inline1_beta_let_eq {dom : Ident → Bool} {Φ : FunEnv} {c : CbSlotSpec}
    {inlP origP : Ident} {pTy : Ty} {v : Expr}
    (hcwf : CbSlotWF dom Φ c) (hlow : c.lowering = .inline1 inlP)
    (hcp : c.cbParams = [(origP, pTy)]) (hvCl : freeVars v = []) :
    substMany (zipParams [(origP, pTy)] [v]) (substMany (zipParams c.fvs c.fvVals) c.cbBody) =
      subst inlP v (substMany (zipParams c.fvs c.fvVals) (subst origP (.var inlP) c.cbBody)) := by
  have hlow_wf := hcwf.2.2.2.2.2.2.2
  rw [hlow] at hlow_wf
  rcases hlow_wf with ⟨origP', pTy', hcp', hinlNotFvs, hinlFresh⟩
  rw [hcp] at hcp'
  injection hcp' with hhead _
  injection hhead with horigEq _
  subst horigEq
  have hinlNotZip : inlP ∉ (zipParams c.fvs c.fvVals).map Prod.fst := by
    rw [zipParams_fst_eq hcwf.2.2.2.1]; exact hinlNotFvs
  have horigNotFvs : origP ∉ c.fvs.map Prod.fst := by
    apply hcwf.2.2.2.2.1 origP
    rw [hcp]; exact List.mem_cons_self ..
  have horigNotZip : origP ∉ (zipParams c.fvs c.fvVals).map Prod.fst := by
    rw [zipParams_fst_eq hcwf.2.2.2.1]; exact horigNotFvs
  rw [subst_substMany_closed_comm _ _ hinlNotZip hvCl (zipParams_closed hcwf.2.1),
      subst_fresh_var_cancel c.cbBody (safeFreshFor_of_mentions_false c.cbBody hinlFresh),
      ← subst_substMany_closed_comm _ _ horigNotZip hvCl (zipParams_closed hcwf.2.1)]
  rfl

theorem posSpecRelList_length_eq {origFn specFn : Ident} {slots : List PosSpecSlot}
    {es1 es2 : List Expr} (hrl : PosSpecRelList origFn specFn slots es1 es2) :
    es1.length = es2.length := by
  induction es1 generalizing es2 with
  | nil => cases hrl; rfl
  | cons _ _ ih => cases hrl with | cons _ hrs => simp [ih hrs]

/-- Bundled configuration of a valid positional multi-callback `$spec$` specialization
    (`coTrySpecializeHofLoop`, `src/core.gsa:6383-6735`), supporting callbacks at arbitrary
    parameter indices (`0`, middle, last), multiple callbacks, and both captures-first
    `.flatDir` and `.inline1` callback lowerings. -/
structure PositionalLoopSpec (Δ : AdtEnv) (Φ : FunEnv) where
  origFn       : Ident
  specFn       : Ident
  slots        : List PosSpecSlot
  loopRet      : Ty
  loopBody     : Expr
  dom          : Ident → Bool
  hΦcl         : ClosedFunEnv Φ
  hLoop        : Φ origFn = some { name := origFn, params := posOrigParams slots,
                                   retTy := loopRet, body := loopBody }
  hSpec        : Φ specFn = some { name := specFn, params := posSpecParams slots,
                                   retTy := loopRet,
                                   body := posSpecializeLoopExpr origFn specFn slots loopBody }
  hcbs         : ∀ c ∈ cbSlotsOf slots, CbSlotWF dom Φ c
  hOrigNodup   : ((posOrigParams slots).map Prod.fst).Nodup
  hSpecNodup   : ((posSpecParams slots).map Prod.fst).Nodup
  hinlDisjSpec : ∀ c ∈ cbSlotsOf slots, ∀ inlP, c.lowering = .inline1 inlP →
                   inlP ∉ (posSpecParams slots).map Prod.fst
  hLoopNoFv    : ∀ z ∈ freeVars loopBody, z ∉ allCbFvNames slots
  hEligible    : PosSpecEligible origFn slots
                   (allCbOrigNames slots ++ (posSpecParams slots).map Prod.fst) loopBody

/- 1-to-1 Lockstep Forward Simulation (`posSpecRel_step_forward`) for Positional Multi-Callback `$spec$`. -/
mutual
theorem posSpecRel_step_forward {Δ : AdtEnv} {Φ : FunEnv} (S : PositionalLoopSpec Δ Φ)
    {e1 e2 e1' : Expr} {σ σ' : Store}
    (hσ : ClosedStore σ) (he1 : freeVars e1 = [])
    (hr : PosSpecRel S.origFn S.specFn S.slots e1 e2)
    (hs : Step Δ Φ emptyPool e1 σ e1' σ' .none) :
    ∃ e2', PosSpecRel S.origFn S.specFn S.slots e1' e2' ∧
           Step Δ Φ emptyPool e2 σ e2' σ' .none := by
  cases hr with
  | lit _ | var _ | loc _ | taskRef _ | syncRef _ _ | lam _ _ _ _ | trap _ =>
    cases hs
  | tuple hrl =>
    simp only [freeVars] at he1
    cases hs with
    | tupleStep hsl =>
      rcases posSpecRelList_step_forward S hσ he1 hrl hsl with ⟨es2', hrl', hsl2⟩
      exact ⟨.tuple es2', .tuple hrl', .tupleStep hsl2⟩
    | tupleTrap htr =>
      exact ⟨.trap _, .trap _, .tupleTrap ((posSpecRelList_firstTrap_iff hrl).mp htr)⟩
  | block hrl =>
    cases hrl with
    | nil => cases hs; exact ⟨.lit .unit, .lit .unit, .blockEmpty⟩
    | cons hr1 hrs =>
      cases hrs with
      | nil => cases hs; exact ⟨_, hr1, .blockSingle⟩
      | cons hr2 hrs' =>
        simp only [freeVars, freeVarsList, List.append_eq_nil_iff] at he1
        cases hs with
        | blockConsStep hs1 =>
          rcases posSpecRel_step_forward S hσ he1.1 hr1 hs1 with ⟨e2', hr1', hs2⟩
          exact ⟨.block (e2' :: _), .block (.cons hr1' (.cons hr2 hrs')), .blockConsStep hs2⟩
        | blockConsVal hv1 =>
          rcases posSpecRel_val_left hr1 hv1 with ⟨rfl, hv2⟩
          exact ⟨.block _, .block (.cons hr2 hrs'), .blockConsVal hv2⟩
        | blockConsTrap =>
          rw [posSpecRel_trap_left hr1]
          exact ⟨.trap _, .trap _, .blockConsTrap⟩
  | @specCbFlat c flatName args1 args2 hmem hlow hlen hrl =>
    have hcwf := S.hcbs c hmem
    simp only [freeVars, List.append_eq_nil_iff] at he1
    rw [c.cls_eq_lam hcwf] at hs
    cases hs with
    | applyFn hs_fn => cases hs_fn
    | applyArgs _ hsl =>
      rcases posSpecRelList_step_forward S hσ he1.2 hrl hsl with ⟨args2', hrl', hsl2⟩
      have hr' : PosSpecRel S.origFn S.specFn S.slots (.apply c.cls _)
          (.applyDir flatName (c.fvVals ++ args2')) :=
        .specCbFlat hmem hlow (by rw [stepList_length_eq hsl, hlen]) hrl'
      rw [c.cls_eq_lam hcwf] at hr'
      exact ⟨.applyDir flatName (c.fvVals ++ args2'), hr',
        .applyDirArgs (stepList_prepend_vals_forward hcwf.1 hsl2)⟩
    | applyArgsTrap _ htr =>
      have htr2 := (posSpecRelList_firstTrap_iff hrl).mp htr
      exact ⟨.trap _, .trap _, .applyDirTrap ((listFirstTrap_prepend_vals_iff hcwf.1).mpr htr2)⟩
    | applyBeta hvs1 _ =>
      rcases posSpecRelList_val_left hrl hvs1 with ⟨rfl, _⟩
      have hflat : Φ flatName = some { name := flatName, params := c.fvs ++ c.cbParams,
                                       retTy := c.cbRet, body := c.cbBody } := by
        have h := hcwf.2.2.2.2.2.2.2; rwa [hlow] at h
      have hvs_all : ∀ v ∈ c.fvVals ++ args1, IsValue v := by
        intro v hv; rcases List.mem_append.mp hv with h1 | h2
        · exact hcwf.1 v h1
        · exact hvs1 v h2
      refine ⟨_, ?_, .applyDirBeta hflat hvs_all (by simp [hcwf.2.2.2.1, hlen])⟩
      rw [← substMany_lam_apply_eq_flat_capturesFirst c.fvs c.cbParams c.fvVals args1 c.cbBody hcwf.2.2.2.1]
      exact PosSpecRel.refl _ _ _ _
  | @specCbInline1 c inlP origP pTy arg1 arg2 hmem hlow hcp hr_arg =>
    have hcwf := S.hcbs c hmem
    simp only [freeVars, freeVarsList, List.append_eq_nil_iff, List.append_nil] at he1
    rw [c.cls_eq_lam hcwf, hcp] at hs
    cases hs with
    | applyFn hs_fn => cases hs_fn
    | applyArgs _ hsl =>
      cases hsl with
      | head hs1 =>
        rcases posSpecRel_step_forward S hσ he1.2 hr_arg hs1 with ⟨arg2', hr_arg', hs2⟩
        have hr' : PosSpecRel S.origFn S.specFn S.slots (.apply c.cls [_]) _ :=
          .specCbInline1 hmem hlow hcp hr_arg'
        rw [c.cls_eq_lam hcwf, hcp] at hr'
        exact ⟨_, hr', .letStep hs2⟩
      | tail _ hsl_nil => cases hsl_nil
    | applyArgsTrap _ htr =>
      cases htr with
      | head _ _ =>
        rw [posSpecRel_trap_left hr_arg]
        exact ⟨.trap _, .trap _, .letTrap⟩
      | tail _ htr_nil => cases htr_nil
    | applyBeta hvs1 _ =>
      have hv1 : IsValue arg1 := hvs1 arg1 (List.mem_cons_self ..)
      rcases posSpecRel_val_left hr_arg hv1 with ⟨rfl, hv2⟩
      refine ⟨_, ?_, .letVal hv2⟩
      rw [← inline1_beta_let_eq hcwf hlow hcp he1.2]
      exact PosSpecRel.refl _ _ _ _
  | apply hfn hrl =>
    simp only [freeVars, List.append_eq_nil_iff] at he1
    cases hs with
    | applyFn hs1 =>
      rcases posSpecRel_step_forward S hσ he1.1 hfn hs1 with ⟨fn2', hfn', hs2⟩
      exact ⟨.apply fn2' _, .apply hfn' hrl, .applyFn hs2⟩
    | applyFnTrap =>
      rw [posSpecRel_trap_left hfn]
      exact ⟨.trap _, .trap _, .applyFnTrap⟩
    | applyArgs hv1 hsl =>
      rcases posSpecRel_val_left hfn hv1 with ⟨rfl, hv2⟩
      rcases posSpecRelList_step_forward S hσ he1.2 hrl hsl with ⟨args2', hrl', hsl2⟩
      exact ⟨.apply _ args2', .apply hfn hrl', .applyArgs hv2 hsl2⟩
    | applyArgsTrap hv1 htr =>
      rcases posSpecRel_val_left hfn hv1 with ⟨rfl, hv2⟩
      exact ⟨.trap _, .trap _, .applyArgsTrap hv2 ((posSpecRelList_firstTrap_iff hrl).mp htr)⟩
    | @applyBeta m ps ret body args1 _ hvs1 hlen =>
      rcases posSpecRel_val_left hfn (.lam m ps ret body) with ⟨heq_fn, _⟩
      rw [← heq_fn]
      rcases posSpecRelList_val_left hrl hvs1 with ⟨rfl, _⟩
      exact ⟨_, PosSpecRel.refl _ _ _ _, .applyBeta hvs1 hlen⟩
  | @specSelfCall args1 args2 hcall =>
    simp only [freeVars] at he1
    generalize hnm_eq : S.origFn = nm at hs
    cases hs with
    | applyDirArgs hsl =>
      subst hnm_eq
      rcases posCallArgsRel_step_forward S hσ he1 S.slots (fun _ h => h) hcall hsl with ⟨args2', hcall', hsl2⟩
      exact ⟨.applyDir S.specFn args2', .specSelfCall hcall', .applyDirArgs hsl2⟩
    | applyDirTrap htr =>
      subst hnm_eq
      exact ⟨.trap _, .trap _, .applyDirTrap ((posCallArgsRel_firstTrap_iff S.hcbs hcall).mp htr)⟩
    | applyDirBeta hfd hvs1 _ =>
      subst hnm_eq
      rw [S.hLoop] at hfd
      injection hfd with hfd; subst hfd
      rcases posCallArgsRel_allVal_left S.hcbs hcall hvs1 with ⟨hvs2, _, hlen2⟩
      have hcl1 := freeVarsList_eq_nil_iff.mp he1
      have hr' := posSpecEligible_subst_rel S.origFn S.specFn S.slots S.hcbs hcall hvs1 hcl1
        S.hOrigNodup S.hSpecNodup S.hinlDisjSpec S.hLoopNoFv S.hEligible
      exact ⟨_, hr', .applyDirBeta S.hSpec hvs2 hlen2⟩
  | applyDir hrl =>
    simp only [freeVars] at he1
    cases hs with
    | applyDirArgs hsl =>
      rcases posSpecRelList_step_forward S hσ he1 hrl hsl with ⟨args2', hrl', hsl2⟩
      exact ⟨.applyDir _ args2', .applyDir hrl', .applyDirArgs hsl2⟩
    | applyDirTrap htr =>
      exact ⟨.trap _, .trap _, .applyDirTrap ((posSpecRelList_firstTrap_iff hrl).mp htr)⟩
    | applyDirBeta hfd hvs1 hlen =>
      rcases posSpecRelList_val_left hrl hvs1 with ⟨rfl, _⟩
      exact ⟨_, PosSpecRel.refl _ _ _ _, .applyDirBeta hfd hvs1 hlen⟩
  | bin ha hb =>
    simp only [freeVars, List.append_eq_nil_iff] at he1
    cases hs with
    | binLeft hs1 =>
      rcases posSpecRel_step_forward S hσ he1.1 ha hs1 with ⟨a2', ha', hs2⟩
      exact ⟨.bin _ a2' _, .bin ha' hb, .binLeft hs2⟩
    | binLeftTrap => rw [posSpecRel_trap_left ha]; exact ⟨.trap _, .trap _, .binLeftTrap⟩
    | binAndFalse =>
      rcases posSpecRel_val_left ha (.lit (.bool false)) with ⟨heq, _⟩; rw [← heq]
      exact ⟨.lit (.bool false), .lit _, .binAndFalse⟩
    | binAndTrue =>
      rcases posSpecRel_val_left ha (.lit (.bool true)) with ⟨heq, _⟩; rw [← heq]
      exact ⟨_, hb, .binAndTrue⟩
    | binOrTrue =>
      rcases posSpecRel_val_left ha (.lit (.bool true)) with ⟨heq, _⟩; rw [← heq]
      exact ⟨.lit (.bool true), .lit _, .binOrTrue⟩
    | binOrFalse =>
      rcases posSpecRel_val_left ha (.lit (.bool false)) with ⟨heq, _⟩; rw [← heq]
      exact ⟨_, hb, .binOrFalse⟩
    | binRight hna hno hv1 hs1 =>
      rcases posSpecRel_val_left ha hv1 with ⟨rfl, hv2⟩
      rcases posSpecRel_step_forward S hσ he1.2 hb hs1 with ⟨b2', hb', hs2⟩
      exact ⟨.bin _ _ b2', .bin ha hb', .binRight hna hno hv2 hs2⟩
    | binRightTrap hna hno hv1 =>
      rcases posSpecRel_val_left ha hv1 with ⟨rfl, hv2⟩
      rw [posSpecRel_trap_left hb]
      exact ⟨.trap _, .trap _, .binRightTrap hna hno hv2⟩
    | binVal hev =>
      rcases posSpecRel_val_left ha (.lit _) with ⟨heq1, _⟩
      rcases posSpecRel_val_left hb (.lit _) with ⟨heq2, _⟩
      rw [← heq1, ← heq2]
      exact ⟨.lit _, .lit _, .binVal hev⟩
    | binTrap hev =>
      rcases posSpecRel_val_left ha (.lit _) with ⟨heq1, _⟩
      rcases posSpecRel_val_left hb (.lit _) with ⟨heq2, _⟩
      rw [← heq1, ← heq2]
      exact ⟨.trap _, .trap _, .binTrap hev⟩
  | un ha =>
    simp only [freeVars] at he1
    cases hs with
    | unStep hs1 =>
      rcases posSpecRel_step_forward S hσ he1 ha hs1 with ⟨a2', ha', hs2⟩
      exact ⟨.un _ a2', .un ha', .unStep hs2⟩
    | unTrap => rw [posSpecRel_trap_left ha]; exact ⟨.trap _, .trap _, .unTrap⟩
    | unVal hev =>
      rcases posSpecRel_val_left ha (.lit _) with ⟨heq, _⟩; rw [← heq]
      exact ⟨.lit _, .lit _, .unVal hev⟩
  | let_ ha hb =>
    simp only [freeVars, List.append_eq_nil_iff] at he1
    cases hs with
    | letStep hs1 =>
      rcases posSpecRel_step_forward S hσ he1.1 ha hs1 with ⟨a2', ha', hs2⟩
      exact ⟨.let_ _ a2' _, .let_ ha' hb, .letStep hs2⟩
    | letTrap => rw [posSpecRel_trap_left ha]; exact ⟨.trap _, .trap _, .letTrap⟩
    | letVal hv1 =>
      rcases posSpecRel_val_left ha hv1 with ⟨rfl, hv2⟩
      exact ⟨_, posSpecRel_subst S.hcbs _ he1.1 hb, .letVal hv2⟩
  | if_ hc ht he =>
    simp only [freeVars, List.append_eq_nil_iff] at he1
    cases hs with
    | ifStep hs1 =>
      rcases posSpecRel_step_forward S hσ he1.1.1 hc hs1 with ⟨c2', hc', hs2⟩
      exact ⟨.if_ c2' _ _, .if_ hc' ht he, .ifStep hs2⟩
    | ifTrap => rw [posSpecRel_trap_left hc]; exact ⟨.trap _, .trap _, .ifTrap⟩
    | ifTrue =>
      rcases posSpecRel_val_left hc (.lit (.bool true)) with ⟨heq, _⟩; rw [← heq]
      exact ⟨_, ht, .ifTrue⟩
    | ifFalse =>
      rcases posSpecRel_val_left hc (.lit (.bool false)) with ⟨heq, _⟩; rw [← heq]
      exact ⟨_, he, .ifFalse⟩
  | while_ hc hb =>
    cases hs with
    | whileUnfold =>
      exact ⟨_, .if_ hc (.block (.cons hb (.cons (.while_ hc hb) .nil))) (.lit .unit), .whileUnfold⟩
  | match_ hs_r harms =>
    simp only [freeVars, List.append_eq_nil_iff] at he1
    cases hs with
    | matchScrut hs1 =>
      rcases posSpecRel_step_forward S hσ he1.1 hs_r hs1 with ⟨s2', hs_r', hs2⟩
      exact ⟨.match_ s2' _, .match_ hs_r' harms, .matchScrut hs2⟩
    | matchScrutTrap => rw [posSpecRel_trap_left hs_r]; exact ⟨.trap _, .trap _, .matchScrutTrap⟩
    | matchEmpty hv1 =>
      cases harms with
      | nil =>
        rcases posSpecRel_val_left hs_r hv1 with ⟨rfl, hv2⟩
        exact ⟨.trap .matchFailure, .trap _, .matchEmpty hv2⟩
    | matchHit hv1 hm =>
      cases harms with
      | cons hb _ =>
        rcases posSpecRel_val_left hs_r hv1 with ⟨rfl, hv2⟩
        rcases matchPat_closed he1.1 hm with ⟨henv, _⟩
        exact ⟨_, posSpecRel_substMany S.hcbs henv hb, .matchHit hv2 hm⟩
    | matchMiss hv1 hm =>
      cases harms with
      | cons _ hrs =>
        rcases posSpecRel_val_left hs_r hv1 with ⟨rfl, hv2⟩
        exact ⟨_, .match_ hs_r hrs, .matchMiss hv2 hm⟩
  | makeData hrl =>
    simp only [freeVars] at he1
    cases hs with
    | makeDataStep hsl =>
      rcases posSpecRelList_step_forward S hσ he1 hrl hsl with ⟨es2', hrl', hsl2⟩
      exact ⟨.makeData _ _ es2', .makeData hrl', .makeDataStep hsl2⟩
    | makeDataTrap htr =>
      exact ⟨.trap _, .trap _, .makeDataTrap ((posSpecRelList_firstTrap_iff hrl).mp htr)⟩
  | getTag ha =>
    simp only [freeVars] at he1
    cases hs with
    | getTagStep hs1 =>
      rcases posSpecRel_step_forward S hσ he1 ha hs1 with ⟨a2', ha', hs2⟩
      exact ⟨.getTag a2', .getTag ha', .getTagStep hs2⟩
    | getTagTrap => rw [posSpecRel_trap_left ha]; exact ⟨.trap _, .trap _, .getTagTrap⟩
    | getTagVal hvs1 =>
      rcases posSpecRel_val_left ha (.makeData _ _ hvs1) with ⟨heq, _⟩; rw [← heq]
      exact ⟨.lit _, .lit _, .getTagVal hvs1⟩
  | cellNew ha =>
    simp only [freeVars] at he1
    cases hs with
    | cellNewStep hs1 =>
      rcases posSpecRel_step_forward S hσ he1 ha hs1 with ⟨a2', ha', hs2⟩
      exact ⟨.cellNew a2', .cellNew ha', .cellNewStep hs2⟩
    | cellNewTrap => rw [posSpecRel_trap_left ha]; exact ⟨.trap _, .trap _, .cellNewTrap⟩
    | cellNewVal hv1 =>
      rcases posSpecRel_val_left ha hv1 with ⟨rfl, hv2⟩
      exact ⟨.loc _, .loc _, .cellNewVal hv2⟩
  | cellGet ha =>
    simp only [freeVars] at he1
    cases hs with
    | cellGetStep hs1 =>
      rcases posSpecRel_step_forward S hσ he1 ha hs1 with ⟨a2', ha', hs2⟩
      exact ⟨.cellGet a2', .cellGet ha', .cellGetStep hs2⟩
    | cellGetTrap => rw [posSpecRel_trap_left ha]; exact ⟨.trap _, .trap _, .cellGetTrap⟩
    | cellGetVal hl =>
      rcases posSpecRel_val_left ha (.loc _) with ⟨heq, _⟩; rw [← heq]
      exact ⟨_, PosSpecRel.refl _ _ _ _, .cellGetVal hl⟩
  | cellSet ha hb =>
    simp only [freeVars, List.append_eq_nil_iff] at he1
    cases hs with
    | cellSetLeft hs1 =>
      rcases posSpecRel_step_forward S hσ he1.1 ha hs1 with ⟨a2', ha', hs2⟩
      exact ⟨.cellSet a2' _, .cellSet ha' hb, .cellSetLeft hs2⟩
    | cellSetLeftTrap => rw [posSpecRel_trap_left ha]; exact ⟨.trap _, .trap _, .cellSetLeftTrap⟩
    | cellSetRight hv1 hs1 =>
      rcases posSpecRel_val_left ha hv1 with ⟨rfl, hv2⟩
      rcases posSpecRel_step_forward S hσ he1.2 hb hs1 with ⟨b2', hb', hs2⟩
      exact ⟨.cellSet _ b2', .cellSet ha hb', .cellSetRight hv2 hs2⟩
    | cellSetRightTrap hv1 =>
      rcases posSpecRel_val_left ha hv1 with ⟨rfl, hv2⟩
      rw [posSpecRel_trap_left hb]
      exact ⟨.trap _, .trap _, .cellSetRightTrap hv2⟩
    | cellSetVal hlt hv1 =>
      rcases posSpecRel_val_left ha (.loc _) with ⟨heq, _⟩; rw [← heq]
      rcases posSpecRel_val_left hb hv1 with ⟨rfl, hv2⟩
      exact ⟨.lit .unit, .lit .unit, .cellSetVal hlt hv2⟩
  | spawn ha =>
    simp only [freeVars] at he1
    cases hs with
    | spawnStep hs1 =>
      rcases posSpecRel_step_forward S hσ he1 ha hs1 with ⟨a2', ha', hs2⟩
      exact ⟨.spawn a2', .spawn ha', .spawnStep hs2⟩
    | spawnTrap => rw [posSpecRel_trap_left ha]; exact ⟨.trap _, .trap _, .spawnTrap⟩
  | await ha =>
    simp only [freeVars] at he1
    cases hs with
    | awaitStep hs1 =>
      rcases posSpecRel_step_forward S hσ he1 ha hs1 with ⟨a2', ha', hs2⟩
      exact ⟨.await a2', .await ha', .awaitStep hs2⟩
    | awaitTrap => rw [posSpecRel_trap_left ha]; exact ⟨.trap _, .trap _, .awaitTrap⟩
    | awaitVal h _ | awaitTaskTrap h => simp [emptyPool] at h
  | concPrim hrl =>
    simp only [freeVars] at he1
    cases hs with
    | concPrimArgs hsl =>
      rcases posSpecRelList_step_forward S hσ he1 hrl hsl with ⟨args2', hrl', hsl2⟩
      exact ⟨.concPrim _ args2', .concPrim hrl', .concPrimArgs hsl2⟩
    | concPrimTrap htr =>
      exact ⟨.trap _, .trap _, .concPrimTrap ((posSpecRelList_firstTrap_iff hrl).mp htr)⟩
    | concPrimVal hc => exact False.elim (stepConcPrim_emptyPool_none_false hc)
termination_by sizeOf e1

theorem posSpecRelList_step_forward {Δ : AdtEnv} {Φ : FunEnv} (S : PositionalLoopSpec Δ Φ)
    {es1 es2 es1' : List Expr} {σ σ' : Store}
    (hσ : ClosedStore σ) (hes1 : freeVarsList es1 = [])
    (hrl : PosSpecRelList S.origFn S.specFn S.slots es1 es2)
    (hsl : StepList Δ Φ emptyPool es1 σ es1' σ' .none) :
    ∃ es2', PosSpecRelList S.origFn S.specFn S.slots es1' es2' ∧
            StepList Δ Φ emptyPool es2 σ es2' σ' .none := by
  cases hrl with
  | nil => cases hsl
  | cons hr hrs =>
    simp only [freeVarsList, List.append_eq_nil_iff] at hes1
    cases hsl with
    | head hs1 =>
      rcases posSpecRel_step_forward S hσ hes1.1 hr hs1 with ⟨e2', hr', hs2⟩
      exact ⟨e2' :: _, .cons hr' hrs, .head hs2⟩
    | tail hv1 hsl1 =>
      rcases posSpecRel_val_left hr hv1 with ⟨rfl, hv2⟩
      rcases posSpecRelList_step_forward S hσ hes1.2 hrs hsl1 with ⟨es2', hrs', hsl2⟩
      exact ⟨_ :: es2', .cons hr hrs', .tail hv2 hsl2⟩
termination_by sizeOf es1

theorem posCallArgsRel_step_forward {Δ : AdtEnv} {Φ : FunEnv} (S : PositionalLoopSpec Δ Φ)
    {args1 args2 args1' : List Expr} {σ σ' : Store}
    (hσ : ClosedStore σ) (hes1 : freeVarsList args1 = [])
    (rem : List PosSpecSlot) (hsub : ∀ c ∈ cbSlotsOf rem, c ∈ cbSlotsOf S.slots)
    (hcall : PosCallArgsRel S.origFn S.specFn S.slots rem args1 args2)
    (hsl : StepList Δ Φ emptyPool args1 σ args1' σ' .none) :
    ∃ args2', PosCallArgsRel S.origFn S.specFn S.slots rem args1' args2' ∧
              StepList Δ Φ emptyPool args2 σ args2' σ' .none := by
  cases hcall with
  | nil => cases hsl
  | @state p rem' _ _ _ _ hr hrest =>
    simp only [freeVarsList, List.append_eq_nil_iff] at hes1
    cases hsl with
    | head hs1 =>
      rcases posSpecRel_step_forward S hσ hes1.1 hr hs1 with ⟨e2', hr', hs2⟩
      exact ⟨e2' :: _, .state p hr' hrest, .head hs2⟩
    | tail hv1 hsl1 =>
      rcases posSpecRel_val_left hr hv1 with ⟨rfl, hv2⟩
      rcases posCallArgsRel_step_forward S hσ hes1.2 rem' hsub hrest hsl1 with ⟨r2', hrest', hsl2⟩
      exact ⟨_ :: r2', .state p hr hrest', .tail hv2 hsl2⟩
  | @callback c rem' r1 r2 hrest =>
    have hcwf := S.hcbs c (hsub c (List.mem_cons_self ..))
    simp only [freeVarsList, List.append_eq_nil_iff] at hes1
    cases hsl with
    | head hs_cls => exact False.elim (isValue_no_step (c.cls_isValue hcwf) hs_cls)
    | tail _ hsl1 =>
      rcases posCallArgsRel_step_forward S hσ hes1.2 rem'
        (fun c' hm => hsub c' (List.mem_cons_of_mem _ hm)) hrest hsl1 with ⟨r2', hrest', hsl2⟩
      exact ⟨c.fvVals ++ r2', .callback c hrest', stepList_prepend_vals_forward hcwf.1 hsl2⟩
termination_by sizeOf args1
end

/- 1-to-1 Lockstep Backward Simulation (`posSpecRel_step_backward`) for Positional Multi-Callback `$spec$`. -/
mutual
theorem posSpecRel_step_backward {Δ : AdtEnv} {Φ : FunEnv} (S : PositionalLoopSpec Δ Φ)
    {e1 e2 e2' : Expr} {σ σ' : Store}
    (hσ : ClosedStore σ) (he1 : freeVars e1 = [])
    (hr : PosSpecRel S.origFn S.specFn S.slots e1 e2)
    (hs2 : Step Δ Φ emptyPool e2 σ e2' σ' .none) :
    ∃ e1', PosSpecRel S.origFn S.specFn S.slots e1' e2' ∧
           Step Δ Φ emptyPool e1 σ e1' σ' .none := by
  cases hr with
  | lit _ | var _ | loc _ | taskRef _ | syncRef _ _ | lam _ _ _ _ | trap _ =>
    cases hs2
  | tuple hrl =>
    simp only [freeVars] at he1
    cases hs2 with
    | tupleStep hsl2 =>
      rcases posSpecRelList_step_backward S hσ he1 hrl hsl2 with ⟨es1', hrl', hsl1⟩
      exact ⟨.tuple es1', .tuple hrl', .tupleStep hsl1⟩
    | tupleTrap htr2 =>
      exact ⟨.trap _, .trap _, .tupleTrap ((posSpecRelList_firstTrap_iff hrl).mpr htr2)⟩
  | block hrl =>
    cases hrl with
    | nil => cases hs2; exact ⟨.lit .unit, .lit .unit, .blockEmpty⟩
    | cons hr1 hrs =>
      cases hrs with
      | nil => cases hs2; exact ⟨_, hr1, .blockSingle⟩
      | cons hr2 hrs' =>
        simp only [freeVars, freeVarsList, List.append_eq_nil_iff] at he1
        cases hs2 with
        | blockConsStep hs_b2 =>
          rcases posSpecRel_step_backward S hσ he1.1 hr1 hs_b2 with ⟨e1', hr1', hs_b1⟩
          exact ⟨.block (e1' :: _), .block (.cons hr1' (.cons hr2 hrs')), .blockConsStep hs_b1⟩
        | blockConsVal hv2 =>
          rcases posSpecRel_val_right hr1 hv2 with ⟨rfl, hv1⟩
          exact ⟨.block _, .block (.cons hr2 hrs'), .blockConsVal hv1⟩
        | blockConsTrap =>
          rw [posSpecRel_trap_right hr1]
          exact ⟨.trap _, .trap _, .blockConsTrap⟩
  | @specCbFlat c flatName args1 args2 hmem hlow hlen hrl =>
    have hcwf := S.hcbs c hmem
    simp only [freeVars, List.append_eq_nil_iff] at he1
    generalize hfull : c.fvVals ++ args2 = fullArgs2 at hs2
    cases hs2 with
    | applyDirArgs hsl_full =>
      rw [← hfull] at hsl_full
      rcases stepList_prepend_vals_inv hcwf.1 hsl_full with ⟨args2', rfl, hsl2⟩
      rcases posSpecRelList_step_backward S hσ he1.2 hrl hsl2 with ⟨args1', hrl', hsl1⟩
      exact ⟨.apply c.cls args1',
        .specCbFlat hmem hlow (by rw [stepList_length_eq hsl1, hlen]) hrl',
        .applyArgs (c.cls_isValue hcwf) hsl1⟩
    | applyDirTrap htr_full =>
      rw [← hfull] at htr_full
      have htr2 := (listFirstTrap_prepend_vals_iff hcwf.1).mp htr_full
      exact ⟨.trap _, .trap _,
        .applyArgsTrap (c.cls_isValue hcwf) ((posSpecRelList_firstTrap_iff hrl).mpr htr2)⟩
    | applyDirBeta hfd hvs_full _ =>
      have hflat : Φ flatName = some { name := flatName, params := c.fvs ++ c.cbParams,
                                       retTy := c.cbRet, body := c.cbBody } := by
        have h := hcwf.2.2.2.2.2.2.2; rwa [hlow] at h
      rw [hflat] at hfd
      injection hfd with hfd; subst hfd
      rw [← hfull] at hvs_full ⊢
      have hvs2 : ∀ v ∈ args2, IsValue v := fun v hv => hvs_full v (List.mem_append_right _ hv)
      rcases posSpecRelList_val_right hrl hvs2 with ⟨rfl, hvs1⟩
      refine ⟨substMany (zipParams c.cbParams args1) (substMany (zipParams c.fvs c.fvVals) c.cbBody), ?_, ?_⟩
      · dsimp only
        rw [← substMany_lam_apply_eq_flat_capturesFirst c.fvs c.cbParams c.fvVals args1 c.cbBody hcwf.2.2.2.1]
        exact PosSpecRel.refl _ _ _ _
      · rw [c.cls_eq_lam hcwf]
        exact .applyBeta hvs1 hlen
  | @specCbInline1 c inlP origP pTy arg1 arg2 hmem hlow hcp hr_arg =>
    have hcwf := S.hcbs c hmem
    simp only [freeVars, freeVarsList, List.append_eq_nil_iff, List.append_nil] at he1
    cases hs2 with
    | letStep hs_a2 =>
      rcases posSpecRel_step_backward S hσ he1.2 hr_arg hs_a2 with ⟨arg1', hr_arg', hs_a1⟩
      exact ⟨.apply c.cls [arg1'], .specCbInline1 hmem hlow hcp hr_arg',
        .applyArgs (c.cls_isValue hcwf) (.head hs_a1)⟩
    | letTrap =>
      rw [posSpecRel_trap_right hr_arg]
      exact ⟨.trap _, .trap _, .applyArgsTrap (c.cls_isValue hcwf) (.head _ [])⟩
    | letVal hv2 =>
      rcases posSpecRel_val_right hr_arg hv2 with ⟨rfl, hv1⟩
      refine ⟨substMany (zipParams [(origP, pTy)] [arg1]) (substMany (zipParams c.fvs c.fvVals) c.cbBody), ?_, ?_⟩
      · rw [← inline1_beta_let_eq hcwf hlow hcp he1.2]
        exact PosSpecRel.refl _ _ _ _
      · rw [c.cls_eq_lam hcwf, hcp]
        exact .applyBeta (fun v hv => by simp at hv; subst hv; exact hv1) rfl
  | apply hfn hrl =>
    simp only [freeVars, List.append_eq_nil_iff] at he1
    cases hs2 with
    | applyFn hs_f2 =>
      rcases posSpecRel_step_backward S hσ he1.1 hfn hs_f2 with ⟨fn1', hfn', hs_f1⟩
      exact ⟨.apply fn1' _, .apply hfn' hrl, .applyFn hs_f1⟩
    | applyFnTrap =>
      rw [posSpecRel_trap_right hfn]
      exact ⟨.trap _, .trap _, .applyFnTrap⟩
    | applyArgs hv2 hsl2 =>
      rcases posSpecRel_val_right hfn hv2 with ⟨rfl, hv1⟩
      rcases posSpecRelList_step_backward S hσ he1.2 hrl hsl2 with ⟨args1', hrl', hsl1⟩
      exact ⟨.apply _ args1', .apply hfn hrl', .applyArgs hv1 hsl1⟩
    | applyArgsTrap hv2 htr2 =>
      rcases posSpecRel_val_right hfn hv2 with ⟨rfl, hv1⟩
      exact ⟨.trap _, .trap _, .applyArgsTrap hv1 ((posSpecRelList_firstTrap_iff hrl).mpr htr2)⟩
    | @applyBeta m ps ret body args2 _ hvs2 hlen2 =>
      rcases posSpecRel_val_right hfn (.lam m ps ret body) with ⟨heq_fn, _⟩
      rw [heq_fn]
      rcases posSpecRelList_val_right hrl hvs2 with ⟨rfl, hvs1⟩
      exact ⟨_, PosSpecRel.refl _ _ _ _, .applyBeta hvs1 hlen2⟩
  | @specSelfCall args1 args2 hcall =>
    simp only [freeVars] at he1
    generalize hnm_eq : S.specFn = nm at hs2
    cases hs2 with
    | applyDirArgs hsl2 =>
      subst hnm_eq
      rcases posCallArgsRel_step_backward S hσ he1 S.slots (fun _ h => h) hcall hsl2 with ⟨args1', hcall', hsl1⟩
      exact ⟨.applyDir S.origFn args1', .specSelfCall hcall', .applyDirArgs hsl1⟩
    | applyDirTrap htr2 =>
      subst hnm_eq
      exact ⟨.trap _, .trap _, .applyDirTrap ((posCallArgsRel_firstTrap_iff S.hcbs hcall).mpr htr2)⟩
    | applyDirBeta hfd hvs2 _ =>
      subst hnm_eq
      rw [S.hSpec] at hfd
      injection hfd with hfd; subst hfd
      have hvs1 := posCallArgsRel_allVal_right S.hcbs hcall hvs2
      have hlen1 := (posCallArgsRel_allVal_left S.hcbs hcall hvs1).2.1
      have hcl1 := freeVarsList_eq_nil_iff.mp he1
      have hr' := posSpecEligible_subst_rel S.origFn S.specFn S.slots S.hcbs hcall hvs1 hcl1
        S.hOrigNodup S.hSpecNodup S.hinlDisjSpec S.hLoopNoFv S.hEligible
      exact ⟨_, hr', .applyDirBeta S.hLoop hvs1 hlen1⟩
  | applyDir hrl =>
    simp only [freeVars] at he1
    cases hs2 with
    | applyDirArgs hsl2 =>
      rcases posSpecRelList_step_backward S hσ he1 hrl hsl2 with ⟨args1', hrl', hsl1⟩
      exact ⟨.applyDir _ args1', .applyDir hrl', .applyDirArgs hsl1⟩
    | applyDirTrap htr2 =>
      exact ⟨.trap _, .trap _, .applyDirTrap ((posSpecRelList_firstTrap_iff hrl).mpr htr2)⟩
    | applyDirBeta hfd hvs2 hlen2 =>
      rcases posSpecRelList_val_right hrl hvs2 with ⟨rfl, hvs1⟩
      exact ⟨_, PosSpecRel.refl _ _ _ _, .applyDirBeta hfd hvs1 hlen2⟩
  | bin ha hb =>
    simp only [freeVars, List.append_eq_nil_iff] at he1
    cases hs2 with
    | binLeft hs_a2 =>
      rcases posSpecRel_step_backward S hσ he1.1 ha hs_a2 with ⟨a1', ha', hs_a1⟩
      exact ⟨.bin _ a1' _, .bin ha' hb, .binLeft hs_a1⟩
    | binLeftTrap => rw [posSpecRel_trap_right ha]; exact ⟨.trap _, .trap _, .binLeftTrap⟩
    | binAndFalse =>
      rcases posSpecRel_val_right ha (.lit (.bool false)) with ⟨heq, _⟩; rw [heq]
      exact ⟨.lit (.bool false), .lit _, .binAndFalse⟩
    | binAndTrue =>
      rcases posSpecRel_val_right ha (.lit (.bool true)) with ⟨heq, _⟩; rw [heq]
      exact ⟨_, hb, .binAndTrue⟩
    | binOrTrue =>
      rcases posSpecRel_val_right ha (.lit (.bool true)) with ⟨heq, _⟩; rw [heq]
      exact ⟨.lit (.bool true), .lit _, .binOrTrue⟩
    | binOrFalse =>
      rcases posSpecRel_val_right ha (.lit (.bool false)) with ⟨heq, _⟩; rw [heq]
      exact ⟨_, hb, .binOrFalse⟩
    | binRight hna hno hv2 hs_b2 =>
      rcases posSpecRel_val_right ha hv2 with ⟨rfl, hv1⟩
      rcases posSpecRel_step_backward S hσ he1.2 hb hs_b2 with ⟨b1', hb', hs_b1⟩
      exact ⟨.bin _ _ b1', .bin ha hb', .binRight hna hno hv1 hs_b1⟩
    | binRightTrap hna hno hv2 =>
      rcases posSpecRel_val_right ha hv2 with ⟨rfl, hv1⟩
      rw [posSpecRel_trap_right hb]
      exact ⟨.trap _, .trap _, .binRightTrap hna hno hv1⟩
    | binVal hev =>
      rcases posSpecRel_val_right ha (.lit _) with ⟨heq1, _⟩
      rcases posSpecRel_val_right hb (.lit _) with ⟨heq2, _⟩
      rw [heq1, heq2]
      exact ⟨.lit _, .lit _, .binVal hev⟩
    | binTrap hev =>
      rcases posSpecRel_val_right ha (.lit _) with ⟨heq1, _⟩
      rcases posSpecRel_val_right hb (.lit _) with ⟨heq2, _⟩
      rw [heq1, heq2]
      exact ⟨.trap _, .trap _, .binTrap hev⟩
  | un ha =>
    simp only [freeVars] at he1
    cases hs2 with
    | unStep hs_a2 =>
      rcases posSpecRel_step_backward S hσ he1 ha hs_a2 with ⟨a1', ha', hs_a1⟩
      exact ⟨.un _ a1', .un ha', .unStep hs_a1⟩
    | unTrap => rw [posSpecRel_trap_right ha]; exact ⟨.trap _, .trap _, .unTrap⟩
    | unVal hev =>
      rcases posSpecRel_val_right ha (.lit _) with ⟨heq, _⟩; rw [heq]
      exact ⟨.lit _, .lit _, .unVal hev⟩
  | let_ ha hb =>
    simp only [freeVars, List.append_eq_nil_iff] at he1
    cases hs2 with
    | letStep hs_a2 =>
      rcases posSpecRel_step_backward S hσ he1.1 ha hs_a2 with ⟨a1', ha', hs_a1⟩
      exact ⟨.let_ _ a1' _, .let_ ha' hb, .letStep hs_a1⟩
    | letTrap => rw [posSpecRel_trap_right ha]; exact ⟨.trap _, .trap _, .letTrap⟩
    | letVal hv2 =>
      rcases posSpecRel_val_right ha hv2 with ⟨rfl, hv1⟩
      exact ⟨_, posSpecRel_subst S.hcbs _ he1.1 hb, .letVal hv1⟩
  | if_ hc ht he =>
    simp only [freeVars, List.append_eq_nil_iff] at he1
    cases hs2 with
    | ifStep hs_c2 =>
      rcases posSpecRel_step_backward S hσ he1.1.1 hc hs_c2 with ⟨c1', hc', hs_c1⟩
      exact ⟨.if_ c1' _ _, .if_ hc' ht he, .ifStep hs_c1⟩
    | ifTrap => rw [posSpecRel_trap_right hc]; exact ⟨.trap _, .trap _, .ifTrap⟩
    | ifTrue =>
      rcases posSpecRel_val_right hc (.lit (.bool true)) with ⟨heq, _⟩; rw [heq]
      exact ⟨_, ht, .ifTrue⟩
    | ifFalse =>
      rcases posSpecRel_val_right hc (.lit (.bool false)) with ⟨heq, _⟩; rw [heq]
      exact ⟨_, he, .ifFalse⟩
  | while_ hc hb =>
    cases hs2 with
    | whileUnfold =>
      exact ⟨_, .if_ hc (.block (.cons hb (.cons (.while_ hc hb) .nil))) (.lit .unit), .whileUnfold⟩
  | match_ hs_r harms =>
    simp only [freeVars, List.append_eq_nil_iff] at he1
    cases hs2 with
    | matchScrut hs_s2 =>
      rcases posSpecRel_step_backward S hσ he1.1 hs_r hs_s2 with ⟨s1', hs_r', hs_s1⟩
      exact ⟨.match_ s1' _, .match_ hs_r' harms, .matchScrut hs_s1⟩
    | matchScrutTrap => rw [posSpecRel_trap_right hs_r]; exact ⟨.trap _, .trap _, .matchScrutTrap⟩
    | matchEmpty hv2 =>
      cases harms with
      | nil =>
        rcases posSpecRel_val_right hs_r hv2 with ⟨rfl, hv1⟩
        exact ⟨.trap .matchFailure, .trap _, .matchEmpty hv1⟩
    | matchHit hv2 hm =>
      cases harms with
      | cons hb _ =>
        rcases posSpecRel_val_right hs_r hv2 with ⟨rfl, hv1⟩
        rcases matchPat_closed he1.1 hm with ⟨henv, _⟩
        exact ⟨_, posSpecRel_substMany S.hcbs henv hb, .matchHit hv1 hm⟩
    | matchMiss hv2 hm =>
      cases harms with
      | cons _ hrs =>
        rcases posSpecRel_val_right hs_r hv2 with ⟨rfl, hv1⟩
        exact ⟨_, .match_ hs_r hrs, .matchMiss hv1 hm⟩
  | makeData hrl =>
    simp only [freeVars] at he1
    cases hs2 with
    | makeDataStep hsl2 =>
      rcases posSpecRelList_step_backward S hσ he1 hrl hsl2 with ⟨es1', hrl', hsl1⟩
      exact ⟨.makeData _ _ es1', .makeData hrl', .makeDataStep hsl1⟩
    | makeDataTrap htr2 =>
      exact ⟨.trap _, .trap _, .makeDataTrap ((posSpecRelList_firstTrap_iff hrl).mpr htr2)⟩
  | getTag ha =>
    simp only [freeVars] at he1
    cases hs2 with
    | getTagStep hs_a2 =>
      rcases posSpecRel_step_backward S hσ he1 ha hs_a2 with ⟨a1', ha', hs_a1⟩
      exact ⟨.getTag a1', .getTag ha', .getTagStep hs_a1⟩
    | getTagTrap => rw [posSpecRel_trap_right ha]; exact ⟨.trap _, .trap _, .getTagTrap⟩
    | getTagVal hvs2 =>
      rcases posSpecRel_val_right ha (.makeData _ _ hvs2) with ⟨heq, _⟩; rw [heq]
      exact ⟨.lit _, .lit _, .getTagVal hvs2⟩
  | cellNew ha =>
    simp only [freeVars] at he1
    cases hs2 with
    | cellNewStep hs_a2 =>
      rcases posSpecRel_step_backward S hσ he1 ha hs_a2 with ⟨a1', ha', hs_a1⟩
      exact ⟨.cellNew a1', .cellNew ha', .cellNewStep hs_a1⟩
    | cellNewTrap => rw [posSpecRel_trap_right ha]; exact ⟨.trap _, .trap _, .cellNewTrap⟩
    | cellNewVal hv2 =>
      rcases posSpecRel_val_right ha hv2 with ⟨rfl, hv1⟩
      exact ⟨.loc _, .loc _, .cellNewVal hv1⟩
  | cellGet ha =>
    simp only [freeVars] at he1
    cases hs2 with
    | cellGetStep hs_a2 =>
      rcases posSpecRel_step_backward S hσ he1 ha hs_a2 with ⟨a1', ha', hs_a1⟩
      exact ⟨.cellGet a1', .cellGet ha', .cellGetStep hs_a1⟩
    | cellGetTrap => rw [posSpecRel_trap_right ha]; exact ⟨.trap _, .trap _, .cellGetTrap⟩
    | cellGetVal hl =>
      rcases posSpecRel_val_right ha (.loc _) with ⟨heq, _⟩; rw [heq]
      exact ⟨_, PosSpecRel.refl _ _ _ _, .cellGetVal hl⟩
  | cellSet ha hb =>
    simp only [freeVars, List.append_eq_nil_iff] at he1
    cases hs2 with
    | cellSetLeft hs_a2 =>
      rcases posSpecRel_step_backward S hσ he1.1 ha hs_a2 with ⟨a1', ha', hs_a1⟩
      exact ⟨.cellSet a1' _, .cellSet ha' hb, .cellSetLeft hs_a1⟩
    | cellSetLeftTrap => rw [posSpecRel_trap_right ha]; exact ⟨.trap _, .trap _, .cellSetLeftTrap⟩
    | cellSetRight hv2 hs_b2 =>
      rcases posSpecRel_val_right ha hv2 with ⟨rfl, hv1⟩
      rcases posSpecRel_step_backward S hσ he1.2 hb hs_b2 with ⟨b1', hb', hs_b1⟩
      exact ⟨.cellSet _ b1', .cellSet ha hb', .cellSetRight hv1 hs_b1⟩
    | cellSetRightTrap hv2 =>
      rcases posSpecRel_val_right ha hv2 with ⟨rfl, hv1⟩
      rw [posSpecRel_trap_right hb]
      exact ⟨.trap _, .trap _, .cellSetRightTrap hv1⟩
    | cellSetVal hlt hv2 =>
      rcases posSpecRel_val_right ha (.loc _) with ⟨heq, _⟩; rw [heq]
      rcases posSpecRel_val_right hb hv2 with ⟨rfl, hv1⟩
      exact ⟨.lit .unit, .lit .unit, .cellSetVal hlt hv1⟩
  | spawn ha =>
    simp only [freeVars] at he1
    cases hs2 with
    | spawnStep hs_a2 =>
      rcases posSpecRel_step_backward S hσ he1 ha hs_a2 with ⟨a1', ha', hs_a1⟩
      exact ⟨.spawn a1', .spawn ha', .spawnStep hs_a1⟩
    | spawnTrap => rw [posSpecRel_trap_right ha]; exact ⟨.trap _, .trap _, .spawnTrap⟩
  | await ha =>
    simp only [freeVars] at he1
    cases hs2 with
    | awaitStep hs_a2 =>
      rcases posSpecRel_step_backward S hσ he1 ha hs_a2 with ⟨a1', ha', hs_a1⟩
      exact ⟨.await a1', .await ha', .awaitStep hs_a1⟩
    | awaitTrap => rw [posSpecRel_trap_right ha]; exact ⟨.trap _, .trap _, .awaitTrap⟩
    | awaitVal h _ | awaitTaskTrap h => simp [emptyPool] at h
  | concPrim hrl =>
    simp only [freeVars] at he1
    cases hs2 with
    | concPrimArgs hsl2 =>
      rcases posSpecRelList_step_backward S hσ he1 hrl hsl2 with ⟨args1', hrl', hsl1⟩
      exact ⟨.concPrim _ args1', .concPrim hrl', .concPrimArgs hsl1⟩
    | concPrimTrap htr2 =>
      exact ⟨.trap _, .trap _, .concPrimTrap ((posSpecRelList_firstTrap_iff hrl).mpr htr2)⟩
    | concPrimVal hc => exact False.elim (stepConcPrim_emptyPool_none_false hc)
termination_by sizeOf e1

theorem posSpecRelList_step_backward {Δ : AdtEnv} {Φ : FunEnv} (S : PositionalLoopSpec Δ Φ)
    {es1 es2 es2' : List Expr} {σ σ' : Store}
    (hσ : ClosedStore σ) (hes1 : freeVarsList es1 = [])
    (hrl : PosSpecRelList S.origFn S.specFn S.slots es1 es2)
    (hsl2 : StepList Δ Φ emptyPool es2 σ es2' σ' .none) :
    ∃ es1', PosSpecRelList S.origFn S.specFn S.slots es1' es2' ∧
            StepList Δ Φ emptyPool es1 σ es1' σ' .none := by
  cases hrl with
  | nil => cases hsl2
  | cons hr hrs =>
    simp only [freeVarsList, List.append_eq_nil_iff] at hes1
    cases hsl2 with
    | head hs2 =>
      rcases posSpecRel_step_backward S hσ hes1.1 hr hs2 with ⟨e1', hr', hs1⟩
      exact ⟨e1' :: _, .cons hr' hrs, .head hs1⟩
    | tail hv2 hsl_r2 =>
      rcases posSpecRel_val_right hr hv2 with ⟨rfl, hv1⟩
      rcases posSpecRelList_step_backward S hσ hes1.2 hrs hsl_r2 with ⟨es1', hrs', hsl1⟩
      exact ⟨_ :: es1', .cons hr hrs', .tail hv1 hsl1⟩
termination_by sizeOf es1

theorem posCallArgsRel_step_backward {Δ : AdtEnv} {Φ : FunEnv} (S : PositionalLoopSpec Δ Φ)
    {args1 args2 args2' : List Expr} {σ σ' : Store}
    (hσ : ClosedStore σ) (hes1 : freeVarsList args1 = [])
    (rem : List PosSpecSlot) (hsub : ∀ c ∈ cbSlotsOf rem, c ∈ cbSlotsOf S.slots)
    (hcall : PosCallArgsRel S.origFn S.specFn S.slots rem args1 args2)
    (hsl2 : StepList Δ Φ emptyPool args2 σ args2' σ' .none) :
    ∃ args1', PosCallArgsRel S.origFn S.specFn S.slots rem args1' args2' ∧
              StepList Δ Φ emptyPool args1 σ args1' σ' .none := by
  cases hcall with
  | nil => cases hsl2
  | @state p rem' _ _ _ _ hr hrest =>
    simp only [freeVarsList, List.append_eq_nil_iff] at hes1
    cases hsl2 with
    | head hs2 =>
      rcases posSpecRel_step_backward S hσ hes1.1 hr hs2 with ⟨e1', hr', hs1⟩
      exact ⟨e1' :: _, .state p hr' hrest, .head hs1⟩
    | tail hv2 hsl_r2 =>
      rcases posSpecRel_val_right hr hv2 with ⟨rfl, hv1⟩
      rcases posCallArgsRel_step_backward S hσ hes1.2 rem' hsub hrest hsl_r2 with ⟨r1', hrest', hsl1⟩
      exact ⟨_ :: r1', .state p hr hrest', .tail hv1 hsl1⟩
  | @callback c rem' r1 r2 hrest =>
    have hcwf := S.hcbs c (hsub c (List.mem_cons_self ..))
    simp only [freeVarsList, List.append_eq_nil_iff] at hes1
    rcases stepList_prepend_vals_inv hcwf.1 hsl2 with ⟨r2', rfl, hsl_r2⟩
    rcases posCallArgsRel_step_backward S hσ hes1.2 rem'
      (fun c' hm => hsub c' (List.mem_cons_of_mem _ hm)) hrest hsl_r2 with ⟨r1', hrest', hsl1⟩
    exact ⟨c.cls :: r1', .callback c hrest', .tail (c.cls_isValue hcwf) hsl1⟩
termination_by sizeOf args1
end

theorem posSpecRel_terminal_left {origFn specFn : Ident} {slots : List PosSpecSlot} {e1 e2 : Expr}
    (hr : PosSpecRel origFn specFn slots e1 e2) (ht : IsTerminal e1) : e1 = e2 := by
  rcases ht with hv | ⟨t, rfl⟩
  · exact (posSpecRel_val_left hr hv).1
  · exact (posSpecRel_trap_left hr).symm

theorem posSpecRel_terminal_right {origFn specFn : Ident} {slots : List PosSpecSlot} {e1 e2 : Expr}
    (hr : PosSpecRel origFn specFn slots e1 e2) (ht : IsTerminal e2) : e1 = e2 := by
  rcases ht with hv | ⟨t, rfl⟩
  · exact (posSpecRel_val_right hr hv).1
  · exact posSpecRel_trap_right hr

theorem posSpecRel_steps_forward {Δ : AdtEnv} {Φ : FunEnv} (S : PositionalLoopSpec Δ Φ)
    {e1 e2 e1' : Expr} {σ σ' : Store}
    (hσ : ClosedStore σ) (he1 : freeVars e1 = [])
    (hr : PosSpecRel S.origFn S.specFn S.slots e1 e2)
    (hsteps : Steps Δ Φ e1 σ e1' σ') :
    ∃ e2', PosSpecRel S.origFn S.specFn S.slots e1' e2' ∧ Steps Δ Φ e2 σ e2' σ' := by
  induction hsteps generalizing e2 with
  | refl => exact ⟨e2, hr, .refl _ _⟩
  | trans hs1 _ ih =>
    rcases posSpecRel_step_forward S hσ he1 hr hs1 with ⟨e2_mid, hr_mid, hs2⟩
    rcases step_preserves_closed S.hΦcl hσ he1 hs1 with ⟨he1_mid, hσ_mid⟩
    rcases ih hσ_mid he1_mid hr_mid with ⟨e2', hr', hsteps2⟩
    exact ⟨e2', hr', .trans hs2 hsteps2⟩

theorem posSpecRel_steps_backward {Δ : AdtEnv} {Φ : FunEnv} (S : PositionalLoopSpec Δ Φ)
    {e1 e2 e2' : Expr} {σ σ' : Store}
    (hσ : ClosedStore σ) (he1 : freeVars e1 = [])
    (hr : PosSpecRel S.origFn S.specFn S.slots e1 e2)
    (hsteps : Steps Δ Φ e2 σ e2' σ') :
    ∃ e1', PosSpecRel S.origFn S.specFn S.slots e1' e2' ∧ Steps Δ Φ e1 σ e1' σ' := by
  induction hsteps generalizing e1 with
  | refl => exact ⟨e1, hr, .refl _ _⟩
  | trans hs2 _ ih =>
    rcases posSpecRel_step_backward S hσ he1 hr hs2 with ⟨e1_mid, hr_mid, hs1⟩
    rcases step_preserves_closed S.hΦcl hσ he1 hs1 with ⟨he1_mid, hσ_mid⟩
    rcases ih hσ_mid he1_mid hr_mid with ⟨e1', hr', hsteps1⟩
    exact ⟨e1', hr', .trans hs1 hsteps1⟩

/-- **Main Positional Multi-Callback `$spec$` Soundness (`coTrySpecializeHofLoop`, `src/core.gsa:6383-6735`)**:
    Covers arbitrary callback positions (`0`, middle, last), multiple callbacks, captures-first
    `.flatDir` and `.inline1` callback lowerings, non-value initial state argument evaluation,
    and `Φ1 ↦ Φ2` function-table extension! -/
theorem positional_hof_loop_spec_obsEquiv {Δ : AdtEnv} {Φ1 Φ2 : FunEnv}
    (S : PositionalLoopSpec Δ Φ2)
    (hagree : FunEnvAgreesOn S.dom Φ1 Φ2)
    (hΦ1dom : ClosedDomEnv S.dom Φ1)
    (horigDom : S.dom S.origFn = true)
    {initArgs1 initArgs2 : List Expr} {σ σ' : Store} {out : Expr}
    (hσCl : ClosedStore σ) (hσDom : StoreInDom S.dom σ) (hout : IsTerminal out)
    (hinitRel : PosCallArgsRel S.origFn S.specFn S.slots S.slots initArgs1 initArgs2)
    (hargsCl : ∀ e ∈ initArgs1, freeVars e = [])
    (hargsDom : ∀ e ∈ initArgs1, exprInDom S.dom e = true) :
    Steps Δ Φ1 (.applyDir S.origFn initArgs1) σ out σ' ↔
      Steps Δ Φ2 (.applyDir S.specFn initArgs2) σ out σ' := by
  have he1Dom : exprInDom S.dom (.applyDir S.origFn initArgs1) = true := by
    simp only [exprInDom, Bool.and_eq_true]
    exact ⟨horigDom, exprListInDom_iff.mpr hargsDom⟩
  rw [steps_funEnv_agree_iff hagree hΦ1dom hσDom he1Dom]
  have he1Cl : freeVars (.applyDir S.origFn initArgs1) = [] := by
    simp [freeVars, freeVarsList_eq_nil_iff.mpr hargsCl]
  have hr0 : PosSpecRel S.origFn S.specFn S.slots
      (.applyDir S.origFn initArgs1) (.applyDir S.specFn initArgs2) :=
    .specSelfCall hinitRel
  constructor
  · intro h1
    rcases posSpecRel_steps_forward S hσCl he1Cl hr0 h1 with ⟨e2', hr', h2⟩
    rwa [← posSpecRel_terminal_left hr' hout] at h2
  · intro h2
    rcases posSpecRel_steps_backward S hσCl he1Cl hr0 h2 with ⟨e1', hr', h1⟩
    rwa [posSpecRel_terminal_right hr' hout] at h1

/-- **Soundness of `TmMakeCls` Entry Wrapper (`src/core.gsa:6688-6702`)**:
    Binding `let clsVar = c.cls` (for `TmMakeCls` reconstruction at the specialized entry/wrapper)
    and calling `origFn` has the exact same terminal behavior as calling `specFn` directly! -/
theorem spec_makeCls_wrapper_obsEquiv {Δ : AdtEnv} {Φ1 Φ2 : FunEnv}
    (S : PositionalLoopSpec Δ Φ2)
    (hagree : FunEnvAgreesOn S.dom Φ1 Φ2)
    (hΦ1dom : ClosedDomEnv S.dom Φ1)
    (horigDom : S.dom S.origFn = true)
    {clsVar : Ident} {c : CbSlotSpec}
    {preArgs postArgs initArgs2 : List Expr} {σ σ' : Store} {out : Expr}
    (hcMem : c ∈ cbSlotsOf S.slots)
    (hσCl : ClosedStore σ) (hσDom : StoreInDom S.dom σ) (hout : IsTerminal out)
    (hpre : ∀ e ∈ preArgs, freeVars e = [] ∧ exprInDom S.dom e = true)
    (hpost : ∀ e ∈ postArgs, freeVars e = [] ∧ exprInDom S.dom e = true)
    (hinitRel : PosCallArgsRel S.origFn S.specFn S.slots S.slots
      (preArgs ++ (c.cls :: postArgs)) initArgs2) :
    Steps Δ Φ1 (.let_ clsVar c.cls
        (.applyDir S.origFn (preArgs ++ (.var clsVar :: postArgs)))) σ out σ' ↔
      Steps Δ Φ2 (.applyDir S.specFn initArgs2) σ out σ' := by
  have hcwf := S.hcbs c hcMem
  have hclsVal := c.cls_isValue hcwf
  have hclsCl := c.cls_closed hcwf
  have hclsDom := c.cls_inDom hcwf
  have hpre_sub : substList clsVar c.cls preArgs = preArgs :=
    substList_closed_id clsVar c.cls preArgs (fun e he => (hpre e he).1)
  have hpost_sub : substList clsVar c.cls postArgs = postArgs :=
    substList_closed_id clsVar c.cls postArgs (fun e he => (hpost e he).1)
  have hstep : ObsEquiv Δ Φ1 Φ1
      (.let_ clsVar c.cls (.applyDir S.origFn (preArgs ++ (.var clsVar :: postArgs))))
      (.applyDir S.origFn (preArgs ++ (c.cls :: postArgs))) := by
    apply obsEquiv_of_det_step
    intro σ0
    have hs := Step.letVal (Δ := Δ) (Φ := Φ1) (pool := emptyPool)
      (x := clsVar) (e2 := .applyDir S.origFn (preArgs ++ (.var clsVar :: postArgs))) (σ := σ0) hclsVal
    simpa [subst, substList_append_eq, substList, hpre_sub, hpost_sub] using hs
  rw [hstep σ σ' out hout]
  apply positional_hof_loop_spec_obsEquiv S hagree hΦ1dom horigDom hσCl hσDom hout hinitRel
  · intro e he
    rcases List.mem_append.mp he with h1 | h2
    · exact (hpre e h1).1
    · rcases List.mem_cons.mp h2 with rfl | h3
      · exact hclsCl
      · exact (hpost e h3).1
  · intro e he
    rcases List.mem_append.mp he with h1 | h2
    · exact (hpre e h1).2
    · rcases List.mem_cons.mp h2 with rfl | h3
      · exact hclsDom
      · exact (hpost e h3).2

/-- **Concrete Positive Witness 1 (`nonfirst_inlined_specLoopColl_witness`, matching `adv.gscore:15`)**:
    `specLoopColl(n, f, acc)` has its callback `f = (u => q * u)` at **non-first index 1**
    (capturing `q = 5`) and lowers `f(n)` via `.inline1 "$co$20$u"` into inline multiplication,
    producing `specLoopColl$spec$19(n, q, acc)` directly via `posSpecializeLoopExpr` across `Φ1 ↦ Φ2`. -/
theorem nonfirst_inlined_specLoopColl_witness :
    let loopBody : Expr :=
      .if_ (.bin .leInt (.var "n") (.lit (.int 0)))
        (.var "acc")
        (.applyDir "specLoopColl"
          [.bin .sub (.var "n") (.lit (.int 1)),
           .var "f",
           .bin .add (.var "acc") (.apply (.var "f") [.var "n"])])
    let cbMul : CbSlotSpec := {
      fParam := "f", fnTy := .fn .local [.int] .int, cbMode := .local,
      cbParams := [("u", .int)], cbRet := .int,
      cbBody := .bin .mul (.var "q") (.var "u"),
      fvs := [("q", .int)], fvVals := [.lit (.int 5)],
      lowering := .inline1 "$co$20$u"
    }
    let slots : List PosSpecSlot := [.state ("n", .int), .callback cbMul, .state ("acc", .int)]
    let Φ1 : FunEnv := fun nm =>
      if nm == "specLoopColl" then
        some { name := "specLoopColl", params := posOrigParams slots, retTy := .int, body := loopBody }
      else none
    let Φ2 : FunEnv := fun nm =>
      if nm == "specLoopColl" then
        some { name := "specLoopColl", params := posOrigParams slots, retTy := .int, body := loopBody }
      else if nm == "specLoopColl$spec$19" then
        some { name := "specLoopColl$spec$19", params := posSpecParams slots, retTy := .int,
               body := posSpecializeLoopExpr "specLoopColl" "specLoopColl$spec$19" slots loopBody }
      else none
    Steps (fun _ => none) Φ1 (.applyDir "specLoopColl" [.lit (.int 2), cbMul.cls, .lit (.int 0)])
      [] (.lit (.int 15)) [] ∧
    Steps (fun _ => none) Φ2 (.applyDir "specLoopColl$spec$19" [.lit (.int 2), .lit (.int 5), .lit (.int 0)])
      [] (.lit (.int 15)) [] := by
  let loopBody : Expr :=
    .if_ (.bin .leInt (.var "n") (.lit (.int 0)))
      (.var "acc")
      (.applyDir "specLoopColl"
        [.bin .sub (.var "n") (.lit (.int 1)),
         .var "f",
         .bin .add (.var "acc") (.apply (.var "f") [.var "n"])])
  let cbMul : CbSlotSpec := {
    fParam := "f", fnTy := .fn .local [.int] .int, cbMode := .local,
    cbParams := [("u", .int)], cbRet := .int,
    cbBody := .bin .mul (.var "q") (.var "u"),
    fvs := [("q", .int)], fvVals := [.lit (.int 5)],
    lowering := .inline1 "$co$20$u"
  }
  let slots : List PosSpecSlot := [.state ("n", .int), .callback cbMul, .state ("acc", .int)]
  let dom : Ident → Bool := fun nm => nm == "specLoopColl"
  let Φ1 : FunEnv := fun nm =>
    if nm == "specLoopColl" then
      some { name := "specLoopColl", params := posOrigParams slots, retTy := .int, body := loopBody }
    else none
  let Φ2 : FunEnv := fun nm =>
    if nm == "specLoopColl" then
      some { name := "specLoopColl", params := posOrigParams slots, retTy := .int, body := loopBody }
    else if nm == "specLoopColl$spec$19" then
      some { name := "specLoopColl$spec$19", params := posSpecParams slots, retTy := .int,
             body := posSpecializeLoopExpr "specLoopColl" "specLoopColl$spec$19" slots loopBody }
    else none
  have hΦ2cl : ClosedFunEnv Φ2 := by
    intro nm fd hfd
    simp only [Φ2] at hfd
    split at hfd
    · injection hfd with hfd; subst hfd; decide
    · split at hfd
      · injection hfd with hfd; subst hfd; decide
      · cases hfd
  have hcbWf : CbSlotWF dom Φ2 cbMul := by
    refine ⟨?_, ?_, ?_, rfl, by decide, ?_, rfl, ⟨"u", .int, rfl, by decide, rfl⟩⟩
    · intro v hv; simp [cbMul] at hv; subst hv; exact .lit _
    · intro v hv; simp [cbMul] at hv; subst hv; rfl
    · intro v hv; simp [cbMul] at hv; subst hv; rfl
    · intro z hz; simp [cbMul, freeVars] at hz ⊢; rcases hz with rfl | rfl <;> simp
  let S : PositionalLoopSpec (fun _ => none) Φ2 := {
    origFn := "specLoopColl"
    specFn := "specLoopColl$spec$19"
    slots := slots
    loopRet := .int
    loopBody := loopBody
    dom := dom
    hΦcl := hΦ2cl
    hLoop := rfl
    hSpec := rfl
    hcbs := fun c hc => by simp [slots, cbSlotsOf] at hc; subst hc; exact hcbWf
    hOrigNodup := by decide
    hSpecNodup := by decide
    hinlDisjSpec := by
      intro c hc inlP hlow
      simp [slots, cbSlotsOf] at hc; subst hc
      simp [cbMul] at hlow; subst hlow; decide
    hLoopNoFv := by decide
    hEligible := .if_
      (.bin (.var rfl) (.lit _))
      (.var rfl)
      (.selfCall (.state ("n", .int) (.bin (.var rfl) (.lit _))
        (.callback cbMul
          (.state ("acc", .int)
            (.bin (.var rfl) (.cbCallInline1 rfl rfl rfl (.var rfl)))
            .nil))))
  }
  have hv3 : ∀ v ∈ ([.lit (.int 2), .lit (.int 5), .lit (.int 0)] : List Expr), IsValue v := by
    intro v hv; simp at hv; rcases hv with rfl | rfl | rfl <;> exact .lit _
  have hv3_1 : ∀ v ∈ ([.lit (.int 1), .lit (.int 5), .lit (.int 10)] : List Expr), IsValue v := by
    intro v hv; simp at hv; rcases hv with rfl | rfl | rfl <;> exact .lit _
  have hv3_0 : ∀ v ∈ ([.lit (.int 0), .lit (.int 5), .lit (.int 15)] : List Expr), IsValue v := by
    intro v hv; simp at hv; rcases hv with rfl | rfl | rfl <;> exact .lit _
  have hSpecSteps : Steps (fun _ => none) Φ2
      (.applyDir "specLoopColl$spec$19" [.lit (.int 2), .lit (.int 5), .lit (.int 0)])
      [] (.lit (.int 15)) [] := by
    refine .trans (.applyDirBeta rfl hv3 rfl) ?_
    refine .trans (.ifStep (.binVal rfl)) ?_
    refine .trans .ifFalse ?_
    refine .trans (.applyDirArgs (.head (.binVal rfl))) ?_
    refine .trans (.applyDirArgs (.tail (.lit _) (.tail (.lit _)
      (.head (.binRight (by decide) (by decide) (.lit _) (.letVal (.lit _))))))) ?_
    refine .trans (.applyDirArgs (.tail (.lit _) (.tail (.lit _)
      (.head (.binRight (by decide) (by decide) (.lit _) (.binVal rfl)))))) ?_
    refine .trans (.applyDirArgs (.tail (.lit _) (.tail (.lit _) (.head (.binVal rfl))))) ?_
    refine .trans (.applyDirBeta rfl hv3_1 rfl) ?_
    refine .trans (.ifStep (.binVal rfl)) ?_
    refine .trans .ifFalse ?_
    refine .trans (.applyDirArgs (.head (.binVal rfl))) ?_
    refine .trans (.applyDirArgs (.tail (.lit _) (.tail (.lit _)
      (.head (.binRight (by decide) (by decide) (.lit _) (.letVal (.lit _))))))) ?_
    refine .trans (.applyDirArgs (.tail (.lit _) (.tail (.lit _)
      (.head (.binRight (by decide) (by decide) (.lit _) (.binVal rfl)))))) ?_
    refine .trans (.applyDirArgs (.tail (.lit _) (.tail (.lit _) (.head (.binVal rfl))))) ?_
    refine .trans (.applyDirBeta rfl hv3_0 rfl) ?_
    refine .trans (.ifStep (.binVal rfl)) ?_
    exact .single .ifTrue
  have hagree : FunEnvAgreesOn S.dom Φ1 Φ2 := by
    intro nm hnm; simp [S, dom] at hnm; subst hnm; rfl
  have hΦ1dom : ClosedDomEnv S.dom Φ1 := by
    intro nm fd hnm hfd
    simp [S, dom] at hnm; subst hnm
    simp [Φ1] at hfd; subst hfd; rfl
  have hinitRel : PosCallArgsRel S.origFn S.specFn S.slots S.slots
      [.lit (.int 2), cbMul.cls, .lit (.int 0)]
      [.lit (.int 2), .lit (.int 5), .lit (.int 0)] :=
    .state ("n", .int) (.lit _) (.callback cbMul (.state ("acc", .int) (.lit _) .nil))
  have hOrigSteps := (positional_hof_loop_spec_obsEquiv S hagree hΦ1dom rfl
    (fun _ h => by cases h) (fun _ h => by cases h) (Or.inl (.lit _)) hinitRel
    (by intro e he; simp at he; rcases he with rfl | rfl | rfl; rfl; exact cbMul.cls_closed hcbWf; rfl)
    (by intro e he; simp at he; rcases he with rfl | rfl | rfl; rfl; exact cbMul.cls_inDom hcbWf; rfl)).mpr hSpecSteps
  exact ⟨hOrigSteps, hSpecSteps⟩

/-- **Concrete Positive Witness 2 (`two_callback_foldSepLoop_witness`, matching `foldSepLoop(pos, itemFn, sepFn, acc)`)**:
    Specializes **two** non-first callbacks (`itemFn` at index 1 via captures-first `.flatDir`,
    `sepFn` at index 2 via `.inline1`) with state parameters `pos` (index 0) and `acc` (index 3)! -/
theorem two_callback_foldSepLoop_witness :
    let loopBody : Expr :=
      .if_ (.bin .leInt (.var "pos") (.lit (.int 0)))
        (.var "acc")
        (.applyDir "foldSepLoop"
          [.bin .sub (.var "pos") (.lit (.int 1)),
           .var "itemFn",
           .var "sepFn",
           .bin .add (.apply (.var "itemFn") [.var "pos"])
                     (.apply (.var "sepFn") [.var "acc"])])
    let cbItem : CbSlotSpec := {
      fParam := "itemFn", fnTy := .fn .local [.int] .int, cbMode := .local,
      cbParams := [("x", .int)], cbRet := .int,
      cbBody := .bin .mul (.var "kItem") (.var "x"),
      fvs := [("kItem", .int)], fvVals := [.lit (.int 10)],
      lowering := .flatDir "item$flat"
    }
    let cbSep : CbSlotSpec := {
      fParam := "sepFn", fnTy := .fn .local [.int] .int, cbMode := .local,
      cbParams := [("s", .int)], cbRet := .int,
      cbBody := .bin .add (.var "s") (.var "kSep"),
      fvs := [("kSep", .int)], fvVals := [.lit (.int 1)],
      lowering := .inline1 "$co$30$s"
    }
    let slots : List PosSpecSlot :=
      [.state ("pos", .int), .callback cbItem, .callback cbSep, .state ("acc", .int)]
    let Φ1 : FunEnv := fun nm =>
      if nm == "foldSepLoop" then
        some { name := "foldSepLoop", params := posOrigParams slots, retTy := .int, body := loopBody }
      else none
    let Φ2 : FunEnv := fun nm =>
      if nm == "foldSepLoop" then
        some { name := "foldSepLoop", params := posOrigParams slots, retTy := .int, body := loopBody }
      else if nm == "item$flat" then
        some { name := "item$flat", params := cbItem.fvs ++ cbItem.cbParams, retTy := .int, body := cbItem.cbBody }
      else if nm == "foldSepLoop$spec" then
        some { name := "foldSepLoop$spec", params := posSpecParams slots, retTy := .int,
               body := posSpecializeLoopExpr "foldSepLoop" "foldSepLoop$spec" slots loopBody }
      else none
    Steps (fun _ => none) Φ1 (.applyDir "foldSepLoop" [.lit (.int 1), cbItem.cls, cbSep.cls, .lit (.int 5)])
      [] (.lit (.int 16)) [] ∧
    Steps (fun _ => none) Φ2 (.applyDir "foldSepLoop$spec" [.lit (.int 1), .lit (.int 10), .lit (.int 1), .lit (.int 5)])
      [] (.lit (.int 16)) [] := by
  let loopBody : Expr :=
    .if_ (.bin .leInt (.var "pos") (.lit (.int 0)))
      (.var "acc")
      (.applyDir "foldSepLoop"
        [.bin .sub (.var "pos") (.lit (.int 1)),
         .var "itemFn",
         .var "sepFn",
         .bin .add (.apply (.var "itemFn") [.var "pos"])
                   (.apply (.var "sepFn") [.var "acc"])])
  let cbItem : CbSlotSpec := {
    fParam := "itemFn", fnTy := .fn .local [.int] .int, cbMode := .local,
    cbParams := [("x", .int)], cbRet := .int,
    cbBody := .bin .mul (.var "kItem") (.var "x"),
    fvs := [("kItem", .int)], fvVals := [.lit (.int 10)],
    lowering := .flatDir "item$flat"
  }
  let cbSep : CbSlotSpec := {
    fParam := "sepFn", fnTy := .fn .local [.int] .int, cbMode := .local,
    cbParams := [("s", .int)], cbRet := .int,
    cbBody := .bin .add (.var "s") (.var "kSep"),
    fvs := [("kSep", .int)], fvVals := [.lit (.int 1)],
    lowering := .inline1 "$co$30$s"
  }
  let slots : List PosSpecSlot :=
    [.state ("pos", .int), .callback cbItem, .callback cbSep, .state ("acc", .int)]
  let dom : Ident → Bool := fun nm => nm == "foldSepLoop"
  let Φ1 : FunEnv := fun nm =>
    if nm == "foldSepLoop" then
      some { name := "foldSepLoop", params := posOrigParams slots, retTy := .int, body := loopBody }
    else none
  let Φ2 : FunEnv := fun nm =>
    if nm == "foldSepLoop" then
      some { name := "foldSepLoop", params := posOrigParams slots, retTy := .int, body := loopBody }
    else if nm == "item$flat" then
      some { name := "item$flat", params := cbItem.fvs ++ cbItem.cbParams, retTy := .int, body := cbItem.cbBody }
    else if nm == "foldSepLoop$spec" then
      some { name := "foldSepLoop$spec", params := posSpecParams slots, retTy := .int,
             body := posSpecializeLoopExpr "foldSepLoop" "foldSepLoop$spec" slots loopBody }
    else none
  have hΦ2cl : ClosedFunEnv Φ2 := by
    intro nm fd hfd
    simp only [Φ2] at hfd
    split at hfd
    · injection hfd with hfd; subst hfd; decide
    · split at hfd
      · injection hfd with hfd; subst hfd; decide
      · split at hfd
        · injection hfd with hfd; subst hfd; decide
        · cases hfd
  have hItemWf : CbSlotWF dom Φ2 cbItem := by
    refine ⟨?_, ?_, ?_, rfl, by decide, ?_, rfl, rfl⟩
    · intro v hv; simp [cbItem] at hv; subst hv; exact .lit _
    · intro v hv; simp [cbItem] at hv; subst hv; rfl
    · intro v hv; simp [cbItem] at hv; subst hv; rfl
    · intro z hz; simp [cbItem, freeVars] at hz ⊢; rcases hz with rfl | rfl <;> simp
  have hSepWf : CbSlotWF dom Φ2 cbSep := by
    refine ⟨?_, ?_, ?_, rfl, by decide, ?_, rfl, ⟨"s", .int, rfl, by decide, rfl⟩⟩
    · intro v hv; simp [cbSep] at hv; subst hv; exact .lit _
    · intro v hv; simp [cbSep] at hv; subst hv; rfl
    · intro v hv; simp [cbSep] at hv; subst hv; rfl
    · intro z hz; simp [cbSep, freeVars] at hz ⊢; rcases hz with rfl | rfl <;> simp
  let S : PositionalLoopSpec (fun _ => none) Φ2 := {
    origFn := "foldSepLoop"
    specFn := "foldSepLoop$spec"
    slots := slots
    loopRet := .int
    loopBody := loopBody
    dom := dom
    hΦcl := hΦ2cl
    hLoop := rfl
    hSpec := rfl
    hcbs := fun c hc => by
      simp [slots, cbSlotsOf] at hc
      rcases hc with rfl | rfl
      · exact hItemWf
      · exact hSepWf
    hOrigNodup := by decide
    hSpecNodup := by decide
    hinlDisjSpec := by
      intro c hc inlP hlow
      simp [slots, cbSlotsOf] at hc
      rcases hc with rfl | rfl
      · simp [cbItem] at hlow
      · simp [cbSep] at hlow; subst hlow; decide
    hLoopNoFv := by decide
    hEligible := .if_
      (.bin (.var rfl) (.lit _))
      (.var rfl)
      (.selfCall (.state ("pos", .int) (.bin (.var rfl) (.lit _))
        (.callback cbItem
          (.callback cbSep
            (.state ("acc", .int)
              (.bin
                (.cbCallFlat rfl rfl rfl (.cons (.var rfl) .nil))
                (.cbCallInline1 rfl rfl rfl (.var rfl)))
              .nil)))))
  }
  have hv4_init : ∀ v ∈ ([.lit (.int 1), .lit (.int 10), .lit (.int 1), .lit (.int 5)] : List Expr), IsValue v := by
    intro v hv; simp at hv; rcases hv with rfl | rfl | rfl | rfl <;> exact .lit _
  have hv2_item : ∀ v ∈ ([.lit (.int 10), .lit (.int 1)] : List Expr), IsValue v := by
    intro v hv; simp at hv; rcases hv with rfl | rfl <;> exact .lit _
  have hv4_done : ∀ v ∈ ([.lit (.int 0), .lit (.int 10), .lit (.int 1), .lit (.int 16)] : List Expr), IsValue v := by
    intro v hv; simp at hv; rcases hv with rfl | rfl | rfl | rfl <;> exact .lit _
  have hSpecSteps : Steps (fun _ => none) Φ2
      (.applyDir "foldSepLoop$spec" [.lit (.int 1), .lit (.int 10), .lit (.int 1), .lit (.int 5)])
      [] (.lit (.int 16)) [] := by
    refine .trans (.applyDirBeta rfl hv4_init rfl) ?_
    refine .trans (.ifStep (.binVal rfl)) ?_
    refine .trans .ifFalse ?_
    refine .trans (.applyDirArgs (.head (.binVal rfl))) ?_
    refine .trans (.applyDirArgs (.tail (.lit _) (.tail (.lit _) (.tail (.lit _)
      (.head (.binLeft (.applyDirBeta rfl hv2_item rfl))))))) ?_
    refine .trans (.applyDirArgs (.tail (.lit _) (.tail (.lit _) (.tail (.lit _)
      (.head (.binLeft (.binVal rfl))))))) ?_
    refine .trans (.applyDirArgs (.tail (.lit _) (.tail (.lit _) (.tail (.lit _)
      (.head (.binRight (by decide) (by decide) (.lit _) (.letVal (.lit _)))))))) ?_
    refine .trans (.applyDirArgs (.tail (.lit _) (.tail (.lit _) (.tail (.lit _)
      (.head (.binRight (by decide) (by decide) (.lit _) (.binVal rfl))))))) ?_
    refine .trans (.applyDirArgs (.tail (.lit _) (.tail (.lit _) (.tail (.lit _)
      (.head (.binVal rfl)))))) ?_
    refine .trans (.applyDirBeta rfl hv4_done rfl) ?_
    refine .trans (.ifStep (.binVal rfl)) ?_
    exact .single .ifTrue
  have hagree : FunEnvAgreesOn S.dom Φ1 Φ2 := by
    intro nm hnm; simp [S, dom] at hnm; subst hnm; rfl
  have hΦ1dom : ClosedDomEnv S.dom Φ1 := by
    intro nm fd hnm hfd
    simp [S, dom] at hnm; subst hnm
    simp [Φ1] at hfd; subst hfd; rfl
  have hinitRel : PosCallArgsRel S.origFn S.specFn S.slots S.slots
      [.lit (.int 1), cbItem.cls, cbSep.cls, .lit (.int 5)]
      [.lit (.int 1), .lit (.int 10), .lit (.int 1), .lit (.int 5)] :=
    .state ("pos", .int) (.lit _)
      (.callback cbItem (.callback cbSep (.state ("acc", .int) (.lit _) .nil)))
  have hOrigSteps := (positional_hof_loop_spec_obsEquiv S hagree hΦ1dom rfl
    (fun _ h => by cases h) (fun _ h => by cases h) (Or.inl (.lit _)) hinitRel
    (by intro e he; simp at he; rcases he with rfl | rfl | rfl | rfl
        · rfl
        · exact cbItem.cls_closed hItemWf
        · exact cbSep.cls_closed hSepWf
        · rfl)
    (by intro e he; simp at he; rcases he with rfl | rfl | rfl | rfl
        · rfl
        · exact cbItem.cls_inDom hItemWf
        · exact cbSep.cls_inDom hSepWf
        · rfl)).mpr hSpecSteps
  exact ⟨hOrigSteps, hSpecSteps⟩

/-! ## Part 9: Contextual Observational Equivalence (`CtxObsEquiv`) Across Returned Closures -/

/-- **Counterexample (`obsEquiv_not_lam_congr_counterexample`)**:
    Raw `ObsEquiv` compares terminal `Expr` syntax, and `.lam` is already `IsValue`.
    Hence `let unused = (); 1` and `1` satisfy `ObsEquiv`, yet wrapping them in zero-arg
    closures `() => { let unused = (); 1 }` and `() => 1` violates `ObsEquiv`! -/
theorem obsEquiv_not_lam_congr_counterexample :
    let e1 : Expr := .let_ "unused" (.lit .unit) (.lit (.int 1))
    let e2 : Expr := .lit (.int 1)
    ObsEquiv (fun _ => none) (fun _ => none) (fun _ => none) e1 e2 ∧
    ¬ ObsEquiv (fun _ => none) (fun _ => none) (fun _ => none)
        (.lam .local [] .int e1) (.lam .local [] .int e2) := by
  let e1 : Expr := .let_ "unused" (.lit .unit) (.lit (.int 1))
  let e2 : Expr := .lit (.int 1)
  refine ⟨dead_val_let_obsEquiv _ _ (.lit _) (by decide), ?_⟩
  intro h
  have hsteps := (h [] [] (.lam .local [] .int e1) (Or.inl (.lam _ _ _ _))).mp (.refl _ _)
  rcases steps_of_isTerminal (Or.inl (.lam _ _ _ _)) hsteps with ⟨heq, _⟩
  dsimp [e1, e2] at heq
  cases heq

/-- Strict left-to-right evaluation contexts `EvalCtx`: any `ObsEquiv` (Parts 2–8) lifts
    directly through `EvalCtx` while preserving exact `ObsEquiv`. -/
inductive EvalCtx where
  | hole
  | letLhs (x : Ident) (E : EvalCtx) (body : Expr)
  | applyCallee (E : EvalCtx) (args : List Expr)
  | applyArg (vf : Expr) (vs : List Expr) (E : EvalCtx) (rest : List Expr)
  | applyDirArg (fn : Ident) (vs : List Expr) (E : EvalCtx) (rest : List Expr)

def EvalCtx.fill : EvalCtx → Expr → Expr
  | .hole, e => e
  | .letLhs x E b, e => .let_ x (E.fill e) b
  | .applyCallee E args, e => .apply (E.fill e) args
  | .applyArg vf vs E rest, e => .apply vf (vs ++ E.fill e :: rest)
  | .applyDirArg fn vs E rest, e => .applyDir fn (vs ++ E.fill e :: rest)

def EvalCtxWF : EvalCtx → Prop
  | .hole => True
  | .letLhs _ E _ => EvalCtxWF E
  | .applyCallee E _ => EvalCtxWF E
  | .applyArg vf vs E _ => IsValue vf ∧ (∀ v ∈ vs, IsValue v) ∧ EvalCtxWF E
  | .applyDirArg _ vs E _ => (∀ v ∈ vs, IsValue v) ∧ EvalCtxWF E

theorem evalCtx_obsEquiv_congr {Δ : AdtEnv} {Φ : FunEnv} (E : EvalCtx) (hwf : EvalCtxWF E)
    {e1 e2 : Expr} (heq : ObsEquiv Δ Φ Φ e1 e2) :
    ObsEquiv Δ Φ Φ (E.fill e1) (E.fill e2) := by
  induction E with
  | hole => exact heq
  | letLhs x E' b ih =>
    intro σ σ' out hout
    simp only [EvalCtx.fill, steps_let_terminal_iff hout]
    have ih' := ih hwf
    constructor
    · rintro (⟨t, rfl, htr⟩ | ⟨v, σ1, hv, hsv, hsrest⟩)
      · exact Or.inl ⟨t, rfl, (ih' σ σ' (.trap t) (Or.inr ⟨t, rfl⟩)).mp htr⟩
      · exact Or.inr ⟨v, σ1, hv, (ih' σ σ1 v (Or.inl hv)).mp hsv, hsrest⟩
    · rintro (⟨t, rfl, htr⟩ | ⟨v, σ1, hv, hsv, hsrest⟩)
      · exact Or.inl ⟨t, rfl, (ih' σ σ' (.trap t) (Or.inr ⟨t, rfl⟩)).mpr htr⟩
      · exact Or.inr ⟨v, σ1, hv, (ih' σ σ1 v (Or.inl hv)).mpr hsv, hsrest⟩
  | applyCallee E' args ih =>
    intro σ σ' out hout
    dsimp only [EvalCtx.fill]
    rw [steps_apply_callee_iff hout, steps_apply_callee_iff hout]
    have ih' := ih hwf
    constructor
    · rintro (⟨t, rfl, htr⟩ | ⟨v, σ1, hv, hsv, hsrest⟩)
      · exact Or.inl ⟨t, rfl, (ih' σ σ' (.trap t) (Or.inr ⟨t, rfl⟩)).mp htr⟩
      · exact Or.inr ⟨v, σ1, hv, (ih' σ σ1 v (Or.inl hv)).mp hsv, hsrest⟩
    · rintro (⟨t, rfl, htr⟩ | ⟨v, σ1, hv, hsv, hsrest⟩)
      · exact Or.inl ⟨t, rfl, (ih' σ σ' (.trap t) (Or.inr ⟨t, rfl⟩)).mpr htr⟩
      · exact Or.inr ⟨v, σ1, hv, (ih' σ σ1 v (Or.inl hv)).mpr hsv, hsrest⟩
  | applyArg vf vs E' rest ih =>
    rcases hwf with ⟨hvf, hvs, hwf'⟩
    intro σ σ' out hout
    dsimp only [EvalCtx.fill]
    rw [steps_apply_next_arg_iff hout hvf hvs, steps_apply_next_arg_iff hout hvf hvs]
    have ih' := ih hwf'
    constructor
    · rintro (⟨t, rfl, htr⟩ | ⟨v, σ1, hv, hsv, hsrest⟩)
      · exact Or.inl ⟨t, rfl, (ih' σ σ' (.trap t) (Or.inr ⟨t, rfl⟩)).mp htr⟩
      · exact Or.inr ⟨v, σ1, hv, (ih' σ σ1 v (Or.inl hv)).mp hsv, hsrest⟩
    · rintro (⟨t, rfl, htr⟩ | ⟨v, σ1, hv, hsv, hsrest⟩)
      · exact Or.inl ⟨t, rfl, (ih' σ σ' (.trap t) (Or.inr ⟨t, rfl⟩)).mpr htr⟩
      · exact Or.inr ⟨v, σ1, hv, (ih' σ σ1 v (Or.inl hv)).mpr hsv, hsrest⟩
  | applyDirArg fn vs E' rest ih =>
    rcases hwf with ⟨hvs, hwf'⟩
    intro σ σ' out hout
    dsimp only [EvalCtx.fill]
    rw [steps_applyDir_next_arg_iff hout hvs, steps_applyDir_next_arg_iff hout hvs]
    have ih' := ih hwf'
    constructor
    · rintro (⟨t, rfl, htr⟩ | ⟨v, σ1, hv, hsv, hsrest⟩)
      · exact Or.inl ⟨t, rfl, (ih' σ σ' (.trap t) (Or.inr ⟨t, rfl⟩)).mp htr⟩
      · exact Or.inr ⟨v, σ1, hv, (ih' σ σ1 v (Or.inl hv)).mp hsv, hsrest⟩
    · rintro (⟨t, rfl, htr⟩ | ⟨v, σ1, hv, hsv, hsrest⟩)
      · exact Or.inl ⟨t, rfl, (ih' σ σ' (.trap t) (Or.inr ⟨t, rfl⟩)).mpr htr⟩
      · exact Or.inr ⟨v, σ1, hv, (ih' σ σ1 v (Or.inl hv)).mpr hsv, hsrest⟩

/-- First-order observable ground values (excluding closure syntax `.lam`). -/
inductive IsGroundValue : Expr → Prop where
  | lit (l : Lit) : IsGroundValue (.lit l)
  | tuple {vs : List Expr} : (∀ v ∈ vs, IsGroundValue v) → IsGroundValue (.tuple vs)
  | makeData (adt : Ident) (tag : Nat) {vs : List Expr} :
      (∀ v ∈ vs, IsGroundValue v) → IsGroundValue (.makeData adt tag vs)

theorem isGroundValue_isValue {v : Expr} (hg : IsGroundValue v) : IsValue v := by
  induction hg with
  | lit l => exact .lit l
  | tuple _ ih => exact .tuple ih
  | makeData adt tag _ ih => exact .makeData adt tag ih

def IsGroundOutcome (e : Expr) : Prop :=
  IsGroundValue e ∨ ∃ t, e = .trap t

theorem isGroundOutcome_isTerminal {e : Expr} (ho : IsGroundOutcome e) : IsTerminal e := by
  rcases ho with hg | ht
  · exact Or.inl (isGroundValue_isValue hg)
  · exact Or.inr ht

/-- General 1-hole expression contexts `ExprCtx` covering all recursive `Expr` constructors,
    **including `ExprCtx.lam`, `while_`, `match_` (scrutinee & arms), `getTag`, `spawn`, `await`, and `concPrim`**. -/
inductive ExprCtx where
  | hole
  | lam (m : Mode) (ps : List (Ident × Ty)) (ret : Ty) (C : ExprCtx)
  | letLhs (x : Ident) (C : ExprCtx) (b : Expr)
  | letRhs (x : Ident) (a : Expr) (C : ExprCtx)
  | applyFn (C : ExprCtx) (args : List Expr)
  | applyArg (fn : Expr) (pre : List Expr) (C : ExprCtx) (post : List Expr)
  | applyDirArg (nm : Ident) (pre : List Expr) (C : ExprCtx) (post : List Expr)
  | binL (op : BinOp) (C : ExprCtx) (b : Expr)
  | binR (op : BinOp) (a : Expr) (C : ExprCtx)
  | un (op : UnOp) (C : ExprCtx)
  | ifC (C : ExprCtx) (t e2 : Expr)
  | ifT (c : Expr) (C : ExprCtx) (e2 : Expr)
  | ifE (c t : Expr) (C : ExprCtx)
  | whileCond (C : ExprCtx) (b : Expr)
  | whileBody (c : Expr) (C : ExprCtx)
  | matchScrut (C : ExprCtx) (arms : List (Pat × Expr))
  | matchArm (scrut : Expr) (pre : List (Pat × Expr)) (pat : Pat) (C : ExprCtx) (post : List (Pat × Expr))
  | tupleElem (pre : List Expr) (C : ExprCtx) (post : List Expr)
  | blockElem (pre : List Expr) (C : ExprCtx) (post : List Expr)
  | makeDataElem (adt : Ident) (tag : Nat) (pre : List Expr) (C : ExprCtx) (post : List Expr)
  | getTag (C : ExprCtx)
  | cellNew (C : ExprCtx)
  | cellGet (C : ExprCtx)
  | cellSetL (C : ExprCtx) (b : Expr)
  | cellSetR (a : Expr) (C : ExprCtx)
  | spawn (C : ExprCtx)
  | await (C : ExprCtx)
  | concPrimElem (op : ConcPrim) (pre : List Expr) (C : ExprCtx) (post : List Expr)

def ExprCtx.fill : ExprCtx → Expr → Expr
  | .hole, e => e
  | .lam m ps ret C, e => .lam m ps ret (C.fill e)
  | .letLhs x C b, e => .let_ x (C.fill e) b
  | .letRhs x a C, e => .let_ x a (C.fill e)
  | .applyFn C args, e => .apply (C.fill e) args
  | .applyArg fn pre C post, e => .apply fn (pre ++ C.fill e :: post)
  | .applyDirArg nm pre C post, e => .applyDir nm (pre ++ C.fill e :: post)
  | .binL op C b, e => .bin op (C.fill e) b
  | .binR op a C, e => .bin op a (C.fill e)
  | .un op C, e => .un op (C.fill e)
  | .ifC C t e2, e => .if_ (C.fill e) t e2
  | .ifT c C e2, e => .if_ c (C.fill e) e2
  | .ifE c t C, e => .if_ c t (C.fill e)
  | .whileCond C b, e => .while_ (C.fill e) b
  | .whileBody c C, e => .while_ c (C.fill e)
  | .matchScrut C arms, e => .match_ (C.fill e) arms
  | .matchArm scrut pre pat C post, e => .match_ scrut (pre ++ (pat, C.fill e) :: post)
  | .tupleElem pre C post, e => .tuple (pre ++ C.fill e :: post)
  | .blockElem pre C post, e => .block (pre ++ C.fill e :: post)
  | .makeDataElem adt tag pre C post, e => .makeData adt tag (pre ++ C.fill e :: post)
  | .getTag C, e => .getTag (C.fill e)
  | .cellNew C, e => .cellNew (C.fill e)
  | .cellGet C, e => .cellGet (C.fill e)
  | .cellSetL C b, e => .cellSet (C.fill e) b
  | .cellSetR a C, e => .cellSet a (C.fill e)
  | .spawn C, e => .spawn (C.fill e)
  | .await C, e => .await (C.fill e)
  | .concPrimElem op pre C post, e => .concPrim op (pre ++ C.fill e :: post)

def ExprCtx.comp : ExprCtx → ExprCtx → ExprCtx
  | .hole, C2 => C2
  | .lam m ps ret C1, C2 => .lam m ps ret (C1.comp C2)
  | .letLhs x C1 b, C2 => .letLhs x (C1.comp C2) b
  | .letRhs x a C1, C2 => .letRhs x a (C1.comp C2)
  | .applyFn C1 args, C2 => .applyFn (C1.comp C2) args
  | .applyArg fn pre C1 post, C2 => .applyArg fn pre (C1.comp C2) post
  | .applyDirArg nm pre C1 post, C2 => .applyDirArg nm pre (C1.comp C2) post
  | .binL op C1 b, C2 => .binL op (C1.comp C2) b
  | .binR op a C1, C2 => .binR op a (C1.comp C2)
  | .un op C1, C2 => .un op (C1.comp C2)
  | .ifC C1 t e2, C2 => .ifC (C1.comp C2) t e2
  | .ifT c C1 e2, C2 => .ifT c (C1.comp C2) e2
  | .ifE c t C1, C2 => .ifE c t (C1.comp C2)
  | .whileCond C1 b, C2 => .whileCond (C1.comp C2) b
  | .whileBody c C1, C2 => .whileBody c (C1.comp C2)
  | .matchScrut C1 arms, C2 => .matchScrut (C1.comp C2) arms
  | .matchArm scrut pre pat C1 post, C2 => .matchArm scrut pre pat (C1.comp C2) post
  | .tupleElem pre C1 post, C2 => .tupleElem pre (C1.comp C2) post
  | .blockElem pre C1 post, C2 => .blockElem pre (C1.comp C2) post
  | .makeDataElem adt tag pre C1 post, C2 => .makeDataElem adt tag pre (C1.comp C2) post
  | .getTag C1, C2 => .getTag (C1.comp C2)
  | .cellNew C1, C2 => .cellNew (C1.comp C2)
  | .cellGet C1, C2 => .cellGet (C1.comp C2)
  | .cellSetL C1 b, C2 => .cellSetL (C1.comp C2) b
  | .cellSetR a C1, C2 => .cellSetR a (C1.comp C2)
  | .spawn C1, C2 => .spawn (C1.comp C2)
  | .await C1, C2 => .await (C1.comp C2)
  | .concPrimElem op pre C1 post, C2 => .concPrimElem op pre (C1.comp C2) post

theorem ExprCtx.comp_fill (C1 C2 : ExprCtx) (e : Expr) :
    (C1.comp C2).fill e = C1.fill (C2.fill e) := by
  induction C1 with
  | hole => rfl
  | lam _ _ _ C ih | letLhs _ C _ ih | letRhs _ _ C ih | applyFn C _ ih
  | applyArg _ _ C _ ih | applyDirArg _ _ C _ ih | binL _ C _ ih | binR _ _ C ih
  | un _ C ih | ifC C _ _ ih | ifT _ C _ ih | ifE _ _ C ih
  | whileCond C _ ih | whileBody _ C ih | matchScrut C _ ih | matchArm _ _ _ C _ ih
  | tupleElem _ C _ ih | blockElem _ C _ ih | makeDataElem _ _ _ C _ ih
  | getTag C ih | cellNew C ih | cellGet C ih | cellSetL C _ ih | cellSetR _ C ih
  | spawn C ih | await C ih | concPrimElem _ _ C _ ih =>
    simp [ExprCtx.comp, ExprCtx.fill, ih]

def CtxCloses (Γ : List Ident) (C : ExprCtx) : Prop :=
  ∀ e : Expr, (∀ z ∈ freeVars e, z ∈ Γ) → freeVars (C.fill e) = []

/-- **Higher-Order Contextual Observational Equivalence (`CtxObsEquiv`)**:
    Observes ground values (`IsGroundValue`) and runtime `Trap`s across all closing
    contexts `C : ExprCtx` (which may invoke returned closures, store closures in `Cell`s,
    pass closures to loops, and inspect `Cell` contents). -/
def CtxObsEquiv (Γ : List Ident) (Δ : AdtEnv) (Φ1 Φ2 : FunEnv) (e1 e2 : Expr) : Prop :=
  (∀ z ∈ freeVars e1, z ∈ Γ) ∧
  (∀ z ∈ freeVars e2, z ∈ Γ) ∧
  ∀ (C : ExprCtx) (σ : Store) (out : Expr),
    CtxCloses Γ C →
    ClosedStore σ →
    (∀ v ∈ σ, IsGroundValue v) →
    IsGroundOutcome out →
    ((∃ σ', Steps Δ Φ1 (C.fill e1) σ out σ') ↔
     (∃ σ', Steps Δ Φ2 (C.fill e2) σ out σ'))

theorem CtxObsEquiv.refl {Γ : List Ident} {Δ : AdtEnv} {Φ : FunEnv} {e : Expr}
    (hΓ : ∀ z ∈ freeVars e, z ∈ Γ) : CtxObsEquiv Γ Δ Φ Φ e e :=
  ⟨hΓ, hΓ, fun _ _ _ _ _ _ _ => Iff.rfl⟩

theorem CtxObsEquiv.symm {Γ : List Ident} {Δ : AdtEnv} {Φ1 Φ2 : FunEnv} {e1 e2 : Expr}
    (h : CtxObsEquiv Γ Δ Φ1 Φ2 e1 e2) : CtxObsEquiv Γ Δ Φ2 Φ1 e2 e1 :=
  ⟨h.2.1, h.1, fun C σ out hC hσ hσg hout => (h.2.2 C σ out hC hσ hσg hout).symm⟩

theorem CtxObsEquiv.trans {Γ : List Ident} {Δ : AdtEnv} {Φ1 Φ2 Φ3 : FunEnv} {e1 e2 e3 : Expr}
    (h12 : CtxObsEquiv Γ Δ Φ1 Φ2 e1 e2) (h23 : CtxObsEquiv Γ Δ Φ2 Φ3 e2 e3) :
    CtxObsEquiv Γ Δ Φ1 Φ3 e1 e3 :=
  ⟨h12.1, h23.2.1, fun C σ out hC hσ hσg hout =>
    (h12.2.2 C σ out hC hσ hσg hout).trans (h23.2.2 C σ out hC hσ hσg hout)⟩

/-- **Congruence of `CtxObsEquiv` Inside `.lam` Bodies (`src/core.gsa:7523,7535`)**:
    Unlike raw `ObsEquiv` (`obsEquiv_not_lam_congr_counterexample`), `CtxObsEquiv`
    composes directly across closure bodies! -/
theorem CtxObsEquiv.congr_lam {Γ : List Ident} {Δ : AdtEnv} {Φ1 Φ2 : FunEnv}
    (m : Mode) (ps : List (Ident × Ty)) (ret : Ty) {b1 b2 : Expr}
    (hb : CtxObsEquiv (ps.map Prod.fst ++ Γ) Δ Φ1 Φ2 b1 b2) :
    CtxObsEquiv Γ Δ Φ1 Φ2 (.lam m ps ret b1) (.lam m ps ret b2) := by
  have hlam_fv : ∀ b : Expr, (∀ z ∈ freeVars b, z ∈ ps.map Prod.fst ++ Γ) →
      ∀ z ∈ freeVars (.lam m ps ret b), z ∈ Γ := by
    intro b hsub z hz
    simp only [freeVars, List.mem_filter, Bool.not_eq_true'] at hz
    rcases List.mem_append.mp (hsub z hz.1) with hps | hΓ
    · rcases List.mem_map.mp hps with ⟨p, hp, rfl⟩
      have hany : ps.any (fun q => q.1 == p.1) = true :=
        List.any_eq_true.mpr ⟨p, hp, beq_self_eq_true _⟩
      rw [hany] at hz; cases hz.2
    · exact hΓ
  refine ⟨hlam_fv b1 hb.1, hlam_fv b2 hb.2.1, ?_⟩
  intro C σ out hC hσ hσg hout
  have hC' : CtxCloses (ps.map Prod.fst ++ Γ) (C.comp (.lam m ps ret .hole)) := by
    intro b hsub
    rw [ExprCtx.comp_fill]
    exact hC (.lam m ps ret b) (hlam_fv b hsub)
  have heq := hb.2.2 (C.comp (.lam m ps ret .hole)) σ out hC' hσ hσg hout
  simpa [ExprCtx.comp_fill, ExprCtx.fill] using heq

/-- **Congruence of `CtxObsEquiv` Under Any Scope-Mapping Context `C0 : ExprCtx`**. -/
theorem CtxObsEquiv.congr_ctx {ΓInner ΓOuter : List Ident} {Δ : AdtEnv} {Φ1 Φ2 : FunEnv}
    (C0 : ExprCtx)
    (hscope : ∀ e : Expr, (∀ z ∈ freeVars e, z ∈ ΓInner) → ∀ z ∈ freeVars (C0.fill e), z ∈ ΓOuter)
    {e1 e2 : Expr} (he : CtxObsEquiv ΓInner Δ Φ1 Φ2 e1 e2) :
    CtxObsEquiv ΓOuter Δ Φ1 Φ2 (C0.fill e1) (C0.fill e2) := by
  refine ⟨hscope e1 he.1, hscope e2 he.2.1, ?_⟩
  intro C σ out hC hσ hσg hout
  have hC' : CtxCloses ΓInner (C.comp C0) := by
    intro e hsub
    rw [ExprCtx.comp_fill]
    exact hC (C0.fill e) (hscope e hsub)
  simpa [ExprCtx.comp_fill] using he.2.2 (C.comp C0) σ out hC' hσ hσg hout

/- Open pure/closure expressions (`coTermIsPure` on open Core IR terms: literals, variables,
   closures `.lam` with arbitrary captures, and recursive `.tuple` / `.makeData` aggregates)
   and their full higher-order congruence bisimulation `PureLetDropRel`. -/
mutual
inductive OpenPureVal : Expr → Prop where
  | lit (l : Lit) : OpenPureVal (.lit l)
  | var (z : Ident) : OpenPureVal (.var z)
  | loc (l : Loc) : OpenPureVal (.loc l)
  | taskRef (tid : TaskId) : OpenPureVal (.taskRef tid)
  | syncRef (k : SyncKind) (id : Nat) : OpenPureVal (.syncRef k id)
  | lam (m : Mode) (ps : List (Ident × Ty)) (ret : Ty) (body : Expr) :
      OpenPureVal (.lam m ps ret body)
  | tuple {es : List Expr} : OpenPureValList es → OpenPureVal (.tuple es)
  | makeData (adt : Ident) (tag : Nat) {es : List Expr} :
      OpenPureValList es → OpenPureVal (.makeData adt tag es)

inductive OpenPureValList : List Expr → Prop where
  | nil : OpenPureValList []
  | cons {e : Expr} {es : List Expr} :
      OpenPureVal e → OpenPureValList es → OpenPureValList (e :: es)
end

mutual
theorem openPureVal_of_isValue : {v : Expr} → IsValue v → OpenPureVal v
  | _, .lit l => .lit l
  | _, .loc l => .loc l
  | _, .taskRef tid => .taskRef tid
  | _, .syncRef k id => .syncRef k id
  | _, .lam m ps ret body => .lam m ps ret body
  | .tuple vs, .tuple hvs => .tuple (openPureValList_of_isValue vs hvs)
  | .makeData adt tag vs, .makeData _ _ hvs => .makeData adt tag (openPureValList_of_isValue vs hvs)
termination_by v => sizeOf v

theorem openPureValList_of_isValue : (vs : List Expr) → (∀ v ∈ vs, IsValue v) → OpenPureValList vs
  | [], _ => .nil
  | v :: vr, hvs => .cons (openPureVal_of_isValue (hvs v (List.mem_cons_self ..)))
      (openPureValList_of_isValue vr (fun w hw => hvs w (List.mem_cons_of_mem _ hw)))
termination_by vs => sizeOf vs
end

mutual
theorem openPureVal_subst {y : Ident} {w : Expr} (hw : IsValue w) :
    {e : Expr} → OpenPureVal e → OpenPureVal (subst y w e)
  | _, .lit l => .lit l
  | .var z, .var _ => by
    simp only [subst]; split
    · exact openPureVal_of_isValue hw
    · exact .var z
  | _, .loc l => .loc l
  | _, .taskRef tid => .taskRef tid
  | _, .syncRef k id => .syncRef k id
  | .lam m ps ret body, .lam _ _ _ _ => by
    simp only [subst]; split <;> exact .lam _ _ _ _
  | .tuple es, .tuple hs => .tuple (openPureValList_subst hw es hs)
  | .makeData adt tag es, .makeData _ _ hs => .makeData adt tag (openPureValList_subst hw es hs)
termination_by e => sizeOf e

theorem openPureValList_subst {y : Ident} {w : Expr} (hw : IsValue w) :
    (es : List Expr) → OpenPureValList es → OpenPureValList (substList y w es)
  | [], .nil => .nil
  | e :: r, .cons he hr => .cons (openPureVal_subst hw he) (openPureValList_subst hw r hr)
termination_by es => sizeOf es
end

mutual
theorem openPureVal_closed_isValue : {e : Expr} → freeVars e = [] → OpenPureVal e → IsValue e
  | _, _, .lit l => .lit l
  | .var z, hcl, .var _ => by simp [freeVars] at hcl
  | _, _, .loc l => .loc l
  | _, _, .taskRef tid => .taskRef tid
  | _, _, .syncRef k id => .syncRef k id
  | _, _, .lam m ps ret body => .lam m ps ret body
  | .tuple es, hcl, .tuple hs => .tuple (openPureValList_closed_isValue es hcl hs)
  | .makeData adt tag es, hcl, .makeData _ _ hs =>
    .makeData adt tag (openPureValList_closed_isValue es hcl hs)
termination_by e => sizeOf e

theorem openPureValList_closed_isValue :
    (es : List Expr) → freeVarsList es = [] → OpenPureValList es → ∀ v ∈ es, IsValue v
  | [], _, .nil => fun _ h => by cases h
  | e :: r, hcl, .cons he hr => by
    simp only [freeVarsList, List.append_eq_nil_iff] at hcl
    have hv_e : IsValue e := openPureVal_closed_isValue hcl.1 he
    have hv_r : ∀ v ∈ r, IsValue v := openPureValList_closed_isValue r hcl.2 hr
    intro v hv; rcases List.mem_cons.mp hv with rfl | hvr
    · exact hv_e
    · exact hv_r v hvr
termination_by es => sizeOf es
end

/- Full syntactic congruence closure of dead pure/closure `let` elimination,
   including inside `.lam` bodies. -/
mutual
/-- Syntactic congruence closure of dead pure/closure `let` elimination, including `.lam`. -/
inductive PureLetDropRel : Expr → Expr → Prop where
  | dropPureLet {x : Ident} {rhs b1 e2 : Expr} :
      OpenPureVal rhs →
      x ∉ freeVars b1 →
      PureLetDropRel b1 e2 →
      PureLetDropRel (.let_ x rhs b1) e2
  | lit (l : Lit) : PureLetDropRel (.lit l) (.lit l)
  | var (x : Ident) : PureLetDropRel (.var x) (.var x)
  | loc (l : Loc) : PureLetDropRel (.loc l) (.loc l)
  | taskRef (tid : TaskId) : PureLetDropRel (.taskRef tid) (.taskRef tid)
  | syncRef (k : SyncKind) (id : Nat) : PureLetDropRel (.syncRef k id) (.syncRef k id)
  | trap (t : Trap) : PureLetDropRel (.trap t) (.trap t)
  | lam {m : Mode} {ps : List (Ident × Ty)} {ret : Ty} {b1 b2 : Expr} :
      PureLetDropRel b1 b2 →
      PureLetDropRel (.lam m ps ret b1) (.lam m ps ret b2)
  | tuple {es1 es2 : List Expr} :
      PureLetDropRelList es1 es2 → PureLetDropRel (.tuple es1) (.tuple es2)
  | block {es1 es2 : List Expr} :
      PureLetDropRelList es1 es2 → PureLetDropRel (.block es1) (.block es2)
  | apply {fn1 fn2 : Expr} {args1 args2 : List Expr} :
      PureLetDropRel fn1 fn2 → PureLetDropRelList args1 args2 →
      PureLetDropRel (.apply fn1 args1) (.apply fn2 args2)
  | applyDir {nm : Ident} {args1 args2 : List Expr} :
      PureLetDropRelList args1 args2 →
      PureLetDropRel (.applyDir nm args1) (.applyDir nm args2)
  | bin {op : BinOp} {a1 a2 b1 b2 : Expr} :
      PureLetDropRel a1 a2 → PureLetDropRel b1 b2 →
      PureLetDropRel (.bin op a1 b1) (.bin op a2 b2)
  | un {op : UnOp} {a1 a2 : Expr} :
      PureLetDropRel a1 a2 → PureLetDropRel (.un op a1) (.un op a2)
  | let_ {x : Ident} {a1 a2 b1 b2 : Expr} :
      PureLetDropRel a1 a2 → PureLetDropRel b1 b2 →
      PureLetDropRel (.let_ x a1 b1) (.let_ x a2 b2)
  | if_ {c1 c2 t1 t2 e1 e2 : Expr} :
      PureLetDropRel c1 c2 → PureLetDropRel t1 t2 → PureLetDropRel e1 e2 →
      PureLetDropRel (.if_ c1 t1 e1) (.if_ c2 t2 e2)
  | while_ {c1 c2 b1 b2 : Expr} :
      PureLetDropRel c1 c2 → PureLetDropRel b1 b2 →
      PureLetDropRel (.while_ c1 b1) (.while_ c2 b2)
  | match_ {s1 s2 : Expr} {arms1 arms2 : List (Pat × Expr)} :
      PureLetDropRel s1 s2 → PureLetDropRelArms arms1 arms2 →
      PureLetDropRel (.match_ s1 arms1) (.match_ s2 arms2)
  | makeData {adt : Ident} {tag : Nat} {es1 es2 : List Expr} :
      PureLetDropRelList es1 es2 → PureLetDropRel (.makeData adt tag es1) (.makeData adt tag es2)
  | getTag {a1 a2 : Expr} : PureLetDropRel a1 a2 → PureLetDropRel (.getTag a1) (.getTag a2)
  | cellNew {a1 a2 : Expr} : PureLetDropRel a1 a2 → PureLetDropRel (.cellNew a1) (.cellNew a2)
  | cellGet {a1 a2 : Expr} : PureLetDropRel a1 a2 → PureLetDropRel (.cellGet a1) (.cellGet a2)
  | cellSet {a1 a2 b1 b2 : Expr} :
      PureLetDropRel a1 a2 → PureLetDropRel b1 b2 → PureLetDropRel (.cellSet a1 b1) (.cellSet a2 b2)
  | spawn {a1 a2 : Expr} : PureLetDropRel a1 a2 → PureLetDropRel (.spawn a1) (.spawn a2)
  | await {a1 a2 : Expr} : PureLetDropRel a1 a2 → PureLetDropRel (.await a1) (.await a2)
  | concPrim {op : ConcPrim} {es1 es2 : List Expr} :
      PureLetDropRelList es1 es2 → PureLetDropRel (.concPrim op es1) (.concPrim op es2)

inductive PureLetDropRelList : List Expr → List Expr → Prop where
  | nil : PureLetDropRelList [] []
  | cons {e1 e2 : Expr} {es1 es2 : List Expr} :
      PureLetDropRel e1 e2 → PureLetDropRelList es1 es2 →
      PureLetDropRelList (e1 :: es1) (e2 :: es2)

inductive PureLetDropRelArms : List (Pat × Expr) → List (Pat × Expr) → Prop where
  | nil : PureLetDropRelArms [] []
  | cons {p : Pat} {b1 b2 : Expr} {r1 r2 : List (Pat × Expr)} :
      PureLetDropRel b1 b2 → PureLetDropRelArms r1 r2 →
      PureLetDropRelArms ((p, b1) :: r1) ((p, b2) :: r2)
end

def PureLetDropEnv (Φ1 Φ2 : FunEnv) : Prop :=
  ∀ nm, match Φ1 nm, Φ2 nm with
    | none, none => True
    | some fd1, some fd2 =>
        fd1.params = fd2.params ∧ PureLetDropRel fd1.body fd2.body
    | _, _ => False

inductive StoreDropRel : Store → Store → Prop where
  | nil : StoreDropRel [] []
  | cons {v1 v2 : Expr} {σ1 σ2 : Store} :
      PureLetDropRel v1 v2 → StoreDropRel σ1 σ2 → StoreDropRel (v1 :: σ1) (v2 :: σ2)

mutual
theorem PureLetDropRel.refl : (e : Expr) → PureLetDropRel e e
  | .lit l => .lit l
  | .var x => .var x
  | .loc l => .loc l
  | .taskRef tid => .taskRef tid
  | .syncRef k id => .syncRef k id
  | .trap t => .trap t
  | .lam _ _ _ b => .lam (PureLetDropRel.refl b)
  | .tuple es => .tuple (PureLetDropRelList.refl es)
  | .block es => .block (PureLetDropRelList.refl es)
  | .apply fn args => .apply (PureLetDropRel.refl fn) (PureLetDropRelList.refl args)
  | .applyDir _ args => .applyDir (PureLetDropRelList.refl args)
  | .bin _ a b => .bin (PureLetDropRel.refl a) (PureLetDropRel.refl b)
  | .un _ a => .un (PureLetDropRel.refl a)
  | .let_ _ a b => .let_ (PureLetDropRel.refl a) (PureLetDropRel.refl b)
  | .if_ c t e2 => .if_ (PureLetDropRel.refl c) (PureLetDropRel.refl t) (PureLetDropRel.refl e2)
  | .while_ c b => .while_ (PureLetDropRel.refl c) (PureLetDropRel.refl b)
  | .match_ s arms => .match_ (PureLetDropRel.refl s) (PureLetDropRelArms.refl arms)
  | .makeData _ _ es => .makeData (PureLetDropRelList.refl es)
  | .getTag a => .getTag (PureLetDropRel.refl a)
  | .cellNew a => .cellNew (PureLetDropRel.refl a)
  | .cellGet a => .cellGet (PureLetDropRel.refl a)
  | .cellSet a b => .cellSet (PureLetDropRel.refl a) (PureLetDropRel.refl b)
  | .spawn a => .spawn (PureLetDropRel.refl a)
  | .await a => .await (PureLetDropRel.refl a)
  | .concPrim _ es => .concPrim (PureLetDropRelList.refl es)
termination_by e => sizeOf e

theorem PureLetDropRelList.refl : (es : List Expr) → PureLetDropRelList es es
  | [] => .nil
  | e :: r => .cons (PureLetDropRel.refl e) (PureLetDropRelList.refl r)
termination_by es => sizeOf es

theorem PureLetDropRelArms.refl : (arms : List (Pat × Expr)) → PureLetDropRelArms arms arms
  | [] => .nil
  | (_, b) :: r => .cons (PureLetDropRel.refl b) (PureLetDropRelArms.refl r)
termination_by arms => sizeOf arms
end

theorem PureLetDropEnv.refl (Φ : FunEnv) : PureLetDropEnv Φ Φ := by
  intro nm; cases Φ nm with
  | none => trivial
  | some fd => exact ⟨rfl, PureLetDropRel.refl fd.body⟩

theorem StoreDropRel.refl (σ : Store) : StoreDropRel σ σ := by
  induction σ with
  | nil => exact .nil
  | cons v r ih => exact .cons (PureLetDropRel.refl v) ih

theorem storeDropRel_length {σ1 σ2 : Store} (h : StoreDropRel σ1 σ2) :
    σ1.length = σ2.length := by
  induction h with
  | nil => rfl
  | cons _ _ ih => simp [ih]

theorem storeDropRel_append {σ1 σ2 : Store} {v1 v2 : Expr}
    (h : StoreDropRel σ1 σ2) (hv : PureLetDropRel v1 v2) :
    StoreDropRel (σ1 ++ [v1]) (σ2 ++ [v2]) := by
  induction h with
  | nil => exact .cons hv .nil
  | cons hw _ ih => exact .cons hw ih

theorem storeDropRel_getElem_left {σ1 σ2 : Store} (h : StoreDropRel σ1 σ2)
    {l : Nat} {v1 : Expr} (hget : σ1[l]? = some v1) :
    ∃ v2, σ2[l]? = some v2 ∧ PureLetDropRel v1 v2 := by
  induction h generalizing l with
  | nil => simp at hget
  | cons hv _ ih =>
    cases l with
    | zero => simp at hget; subst hget; exact ⟨_, rfl, hv⟩
    | succ k => simp at hget ⊢; exact ih hget

theorem storeDropRel_getElem_right {σ1 σ2 : Store} (h : StoreDropRel σ1 σ2)
    {l : Nat} {v2 : Expr} (hget : σ2[l]? = some v2) :
    ∃ v1, σ1[l]? = some v1 ∧ PureLetDropRel v1 v2 := by
  induction h generalizing l with
  | nil => simp at hget
  | cons hv _ ih =>
    cases l with
    | zero => simp at hget; subst hget; exact ⟨_, rfl, hv⟩
    | succ k => simp at hget ⊢; exact ih hget

theorem storeDropRel_set {σ1 σ2 : Store} (h : StoreDropRel σ1 σ2)
    (l : Nat) {v1 v2 : Expr} (hv : PureLetDropRel v1 v2) :
    StoreDropRel (σ1.set l v1) (σ2.set l v2) := by
  induction h generalizing l with
  | nil => exact .nil
  | cons hw hrest ih =>
    cases l with
    | zero => exact .cons hv hrest
    | succ k => exact .cons hw (ih k)

theorem pureLetDropList_append {a1 a2 b1 b2 : List Expr}
    (ha : PureLetDropRelList a1 a2) (hb : PureLetDropRelList b1 b2) :
    PureLetDropRelList (a1 ++ b1) (a2 ++ b2) := by
  induction a1 generalizing a2 with
  | nil => cases ha; exact hb
  | cons _ _ ih =>
    cases ha with
    | cons h hrs => exact .cons h (ih hrs)

theorem pureLetDropArms_append {a1 a2 b1 b2 : List (Pat × Expr)}
    (ha : PureLetDropRelArms a1 a2) (hb : PureLetDropRelArms b1 b2) :
    PureLetDropRelArms (a1 ++ b1) (a2 ++ b2) := by
  induction a1 generalizing a2 with
  | nil => cases ha; exact hb
  | cons _ _ ih =>
    cases ha with
    | cons h hrs => exact .cons h (ih hrs)

theorem exprCtx_pureLetDrop_congr (C : ExprCtx) {e1 e2 : Expr} (hr : PureLetDropRel e1 e2) :
    PureLetDropRel (C.fill e1) (C.fill e2) := by
  induction C with
  | hole => exact hr
  | lam _ _ _ _ ih => exact .lam ih
  | letLhs _ _ b ih => exact .let_ ih (PureLetDropRel.refl b)
  | letRhs _ a _ ih => exact .let_ (PureLetDropRel.refl a) ih
  | applyFn _ args ih => exact .apply ih (PureLetDropRelList.refl args)
  | applyArg fn pre _ post ih =>
    exact .apply (PureLetDropRel.refl fn)
      (pureLetDropList_append (PureLetDropRelList.refl pre) (.cons ih (PureLetDropRelList.refl post)))
  | applyDirArg _ pre _ post ih =>
    exact .applyDir (pureLetDropList_append (PureLetDropRelList.refl pre) (.cons ih (PureLetDropRelList.refl post)))
  | binL _ _ b ih => exact .bin ih (PureLetDropRel.refl b)
  | binR _ a _ ih => exact .bin (PureLetDropRel.refl a) ih
  | un _ _ ih => exact .un ih
  | ifC _ t e2 ih => exact .if_ ih (PureLetDropRel.refl t) (PureLetDropRel.refl e2)
  | ifT c _ e2 ih => exact .if_ (PureLetDropRel.refl c) ih (PureLetDropRel.refl e2)
  | ifE c t _ ih => exact .if_ (PureLetDropRel.refl c) (PureLetDropRel.refl t) ih
  | whileCond _ b ih => exact .while_ ih (PureLetDropRel.refl b)
  | whileBody c _ ih => exact .while_ (PureLetDropRel.refl c) ih
  | matchScrut _ arms ih => exact .match_ ih (PureLetDropRelArms.refl arms)
  | matchArm scrut pre _ _ post ih =>
    exact .match_ (PureLetDropRel.refl scrut)
      (pureLetDropArms_append (PureLetDropRelArms.refl pre) (.cons ih (PureLetDropRelArms.refl post)))
  | tupleElem pre _ post ih =>
    exact .tuple (pureLetDropList_append (PureLetDropRelList.refl pre) (.cons ih (PureLetDropRelList.refl post)))
  | blockElem pre _ post ih =>
    exact .block (pureLetDropList_append (PureLetDropRelList.refl pre) (.cons ih (PureLetDropRelList.refl post)))
  | makeDataElem _ _ pre _ post ih =>
    exact .makeData (pureLetDropList_append (PureLetDropRelList.refl pre) (.cons ih (PureLetDropRelList.refl post)))
  | getTag _ ih => exact .getTag ih
  | cellNew _ ih => exact .cellNew ih
  | cellGet _ ih => exact .cellGet ih
  | cellSetL _ b ih => exact .cellSet ih (PureLetDropRel.refl b)
  | cellSetR a _ ih => exact .cellSet (PureLetDropRel.refl a) ih
  | spawn _ ih => exact .spawn ih
  | await _ ih => exact .await ih
  | concPrimElem _ pre _ post ih =>
    exact .concPrim (pureLetDropList_append (PureLetDropRelList.refl pre) (.cons ih (PureLetDropRelList.refl post)))

mutual
theorem pureLetDrop_freeVars_subset {e1 e2 : Expr}
    (hr : PureLetDropRel e1 e2) : ∀ z ∈ freeVars e2, z ∈ freeVars e1 := by
  cases hr with
  | @dropPureLet x _ b1 _ _ hxnot hb =>
    intro z hz
    have hb1 := pureLetDrop_freeVars_subset hb z hz
    have hzx : z ≠ x := fun heq => by subst heq; exact hxnot hb1
    simp [freeVars, hb1, hzx]
  | lit _ | var _ | loc _ | taskRef _ | syncRef _ _ | trap _ =>
    exact fun _ h => h
  | lam hb =>
    intro z hz
    simp only [freeVars, List.mem_filter] at hz ⊢
    exact ⟨pureLetDrop_freeVars_subset hb z hz.1, hz.2⟩
  | tuple hrl => exact fun z hz => pureLetDropList_freeVars_subset hrl z hz
  | block hrl => exact fun z hz => pureLetDropList_freeVars_subset hrl z hz
  | apply hf ha =>
    intro z hz
    simp only [freeVars, List.mem_append] at hz ⊢
    exact hz.elim (fun h => Or.inl (pureLetDrop_freeVars_subset hf z h))
      (fun h => Or.inr (pureLetDropList_freeVars_subset ha z h))
  | applyDir ha => exact fun z hz => pureLetDropList_freeVars_subset ha z hz
  | bin ha hb | while_ ha hb | cellSet ha hb =>
    intro z hz
    simp only [freeVars, List.mem_append] at hz ⊢
    exact hz.elim (fun h => Or.inl (pureLetDrop_freeVars_subset ha z h))
      (fun h => Or.inr (pureLetDrop_freeVars_subset hb z h))
  | un ha | getTag ha | cellNew ha | cellGet ha | spawn ha | await ha =>
    exact fun z hz => pureLetDrop_freeVars_subset ha z hz
  | let_ ha hb =>
    intro z hz
    simp only [freeVars, List.mem_append, List.mem_filter] at hz ⊢
    exact hz.elim (fun h => Or.inl (pureLetDrop_freeVars_subset ha z h))
      (fun h => Or.inr ⟨pureLetDrop_freeVars_subset hb z h.1, h.2⟩)
  | if_ hc ht he =>
    intro z hz
    simp only [freeVars, List.mem_append] at hz ⊢
    rcases hz with (h1 | h2) | h3
    · exact Or.inl (Or.inl (pureLetDrop_freeVars_subset hc z h1))
    · exact Or.inl (Or.inr (pureLetDrop_freeVars_subset ht z h2))
    · exact Or.inr (pureLetDrop_freeVars_subset he z h3)
  | match_ hs ha =>
    intro z hz
    simp only [freeVars, List.mem_append] at hz ⊢
    exact hz.elim (fun h => Or.inl (pureLetDrop_freeVars_subset hs z h))
      (fun h => Or.inr (pureLetDropArms_freeVars_subset ha z h))
  | makeData hrl => exact fun z hz => pureLetDropList_freeVars_subset hrl z hz
  | concPrim hrl => exact fun z hz => pureLetDropList_freeVars_subset hrl z hz
termination_by sizeOf e1

theorem pureLetDropList_freeVars_subset {es1 es2 : List Expr}
    (hrl : PureLetDropRelList es1 es2) : ∀ z ∈ freeVarsList es2, z ∈ freeVarsList es1 := by
  cases hrl with
  | nil => exact fun _ h => h
  | cons he hr =>
    intro z hz
    simp only [freeVarsList, List.mem_append] at hz ⊢
    exact hz.elim (fun h => Or.inl (pureLetDrop_freeVars_subset he z h))
      (fun h => Or.inr (pureLetDropList_freeVars_subset hr z h))
termination_by sizeOf es1

theorem pureLetDropArms_freeVars_subset {arms1 arms2 : List (Pat × Expr)}
    (harms : PureLetDropRelArms arms1 arms2) :
      ∀ z ∈ freeVarsArms arms2, z ∈ freeVarsArms arms1 := by
  cases harms with
  | nil => exact fun _ h => h
  | cons hb hr =>
    intro z hz
    simp only [freeVarsArms, List.mem_append, List.mem_filter] at hz ⊢
    exact hz.elim (fun h => Or.inl ⟨pureLetDrop_freeVars_subset hb z h.1, h.2⟩)
      (fun h => Or.inr (pureLetDropArms_freeVars_subset hr z h))
termination_by sizeOf arms1
end

theorem pureLetDropList_length_eq {es1 es2 : List Expr}
    (hrl : PureLetDropRelList es1 es2) : es1.length = es2.length := by
  induction es1 generalizing es2 with
  | nil => cases hrl; rfl
  | cons _ _ ih =>
    cases hrl with
    | cons _ hrs => simp [ih hrs]

mutual
theorem pureLetDrop_val_left {e1 e2 : Expr}
    (hr : PureLetDropRel e1 e2) (hv1 : IsValue e1) : IsValue e2 := by
  cases hr with
  | lit l => exact .lit l
  | loc l => exact .loc l
  | taskRef tid => exact .taskRef tid
  | syncRef k id => exact .syncRef k id
  | lam _ => exact .lam _ _ _ _
  | tuple hrl =>
    cases hv1 with
    | tuple hvs1 => exact .tuple (pureLetDropList_val_left hrl hvs1)
  | @makeData adt tag _ _ hrl =>
    cases hv1 with
    | makeData _ _ hvs1 => exact .makeData adt tag (pureLetDropList_val_left hrl hvs1)
  | dropPureLet _ _ _ | var _ | trap _ | block _ | apply _ _ | applyDir _
  | bin _ _ | un _ | let_ _ _ | if_ _ _ _ | while_ _ _ | match_ _ _
  | getTag _ | cellNew _ | cellGet _ | cellSet _ _ | spawn _ | await _ | concPrim _ =>
    cases hv1
termination_by sizeOf e1

theorem pureLetDropList_val_left {es1 es2 : List Expr}
    (hrl : PureLetDropRelList es1 es2) (hvs1 : ∀ v ∈ es1, IsValue v) :
      ∀ v ∈ es2, IsValue v := by
  cases hrl with
  | nil => exact fun _ h => by cases h
  | cons hr hrs =>
    intro v hv
    rcases List.mem_cons.mp hv with rfl | hvr
    · exact pureLetDrop_val_left hr (hvs1 _ (List.mem_cons_self ..))
    · exact pureLetDropList_val_left hrs (fun w hw => hvs1 w (List.mem_cons_of_mem _ hw)) v hvr
termination_by sizeOf es1
end

mutual
theorem pureLetDrop_ground_left {e1 e2 : Expr}
    (hr : PureLetDropRel e1 e2) (hg : IsGroundValue e1) : e1 = e2 := by
  cases hr with
  | lit _ => rfl
  | tuple hrl =>
    cases hg with
    | tuple hgs => rw [pureLetDropList_ground_left hrl hgs]
  | makeData hrl =>
    cases hg with
    | makeData _ _ hgs => rw [pureLetDropList_ground_left hrl hgs]
  | dropPureLet _ _ _ | var _ | loc _ | taskRef _ | syncRef _ _ | trap _
  | lam _ | block _ | apply _ _ | applyDir _ | bin _ _ | un _
  | let_ _ _ | if_ _ _ _ | while_ _ _ | match_ _ _ | getTag _
  | cellNew _ | cellGet _ | cellSet _ _ | spawn _ | await _ | concPrim _ =>
    cases hg
termination_by sizeOf e1

theorem pureLetDropList_ground_left {es1 es2 : List Expr}
    (hrl : PureLetDropRelList es1 es2) (hgs : ∀ v ∈ es1, IsGroundValue v) : es1 = es2 := by
  cases hrl with
  | nil => rfl
  | cons hr hrs =>
    rw [pureLetDrop_ground_left hr (hgs _ (List.mem_cons_self ..)),
        pureLetDropList_ground_left hrs (fun w hw => hgs w (List.mem_cons_of_mem _ hw))]
termination_by sizeOf es1
end

mutual
theorem pureLetDrop_isValue_ground_right {e1 e2 : Expr}
    (hv1 : IsValue e1) (hr : PureLetDropRel e1 e2) (hg : IsGroundValue e2) : e1 = e2 := by
  cases hr with
  | lit _ => rfl
  | tuple hrl =>
    cases hv1 with
    | tuple hvs1 =>
      cases hg with
      | tuple hgs2 => rw [pureLetDropList_isValue_ground_right hvs1 hrl hgs2]
  | makeData hrl =>
    cases hv1 with
    | makeData _ _ hvs1 =>
      cases hg with
      | makeData _ _ hgs2 => rw [pureLetDropList_isValue_ground_right hvs1 hrl hgs2]
  | dropPureLet _ _ _ => cases hv1
  | loc _ | taskRef _ | syncRef _ _ | lam _ | var _ | trap _
  | block _ | apply _ _ | applyDir _ | bin _ _ | un _ | let_ _ _
  | if_ _ _ _ | while_ _ _ | match_ _ _ | getTag _ | cellNew _
  | cellGet _ | cellSet _ _ | spawn _ | await _ | concPrim _ =>
    cases hg
termination_by sizeOf e1

theorem pureLetDropList_isValue_ground_right {es1 es2 : List Expr}
    (hvs1 : ∀ v ∈ es1, IsValue v) (hrl : PureLetDropRelList es1 es2)
    (hgs2 : ∀ v ∈ es2, IsGroundValue v) : es1 = es2 := by
  cases hrl with
  | nil => rfl
  | cons hr hrs =>
    rw [pureLetDrop_isValue_ground_right (hvs1 _ (List.mem_cons_self ..)) hr (hgs2 _ (List.mem_cons_self ..)),
        pureLetDropList_isValue_ground_right
          (fun w hw => hvs1 w (List.mem_cons_of_mem _ hw)) hrs
          (fun w hw => hgs2 w (List.mem_cons_of_mem _ hw))]
termination_by sizeOf es1
end

theorem pureLetDrop_trap_left {e2 : Expr} {t : Trap}
    (hr : PureLetDropRel (.trap t) e2) : e2 = .trap t := by
  cases hr; rfl

theorem pureLetDropList_firstTrap_left {es1 es2 : List Expr} {t : Trap}
    (hrl : PureLetDropRelList es1 es2) (htr : ListFirstTrap es1 t) :
    ListFirstTrap es2 t := by
  induction es1 generalizing es2 with
  | nil => cases htr
  | cons _ _ ih =>
    cases hrl with
    | cons hr hrs =>
      cases htr with
      | head _ _ => rw [pureLetDrop_trap_left hr]; exact .head _ _
      | tail hv1 htr1 => exact .tail (pureLetDrop_val_left hr hv1) (ih hrs htr1)

mutual
theorem pureLetDrop_subst (x : Ident) {v1 v2 : Expr}
    (hv1 : IsValue v1) (hcl1 : freeVars v1 = []) (hrv : PureLetDropRel v1 v2)
    {e1 e2 : Expr} (hr : PureLetDropRel e1 e2) :
    PureLetDropRel (subst x v1 e1) (subst x v2 e2) := by
  cases hr with
  | @dropPureLet y rhs b1 _ hpure hynot hb =>
    simp only [subst]
    cases hyx : (y == x)
    · simp only [Bool.false_eq_true, ↓reduceIte]
      have hynot' : y ∉ freeVars (subst x v1 b1) := by
        intro hm
        have hsub := (substMany_freeVars_subset [(x, v1)]
          (fun q hq => by simp at hq; rcases hq with ⟨_, rfl⟩; exact hcl1)
          b1 y (by simpa [substMany] using hm)).2
        exact hynot hsub
      exact .dropPureLet (openPureVal_subst hv1 hpure) hynot'
        (pureLetDrop_subst x hv1 hcl1 hrv hb)
    · simp only [↓reduceIte]
      have hyeq := eq_of_beq hyx; subst hyeq
      have hxnot2 : y ∉ freeVars e2 := fun hm => hynot (pureLetDrop_freeVars_subset hb y hm)
      rw [subst_not_mem_freeVars e2 hxnot2]
      exact .dropPureLet (openPureVal_subst hv1 hpure) hynot hb
  | lit l => exact .lit l
  | var z =>
    simp only [subst]; split
    · exact hrv
    · exact .var z
  | loc l => exact .loc l
  | taskRef tid => exact .taskRef tid
  | syncRef k id => exact .syncRef k id
  | trap t => exact .trap t
  | lam hb =>
    simp only [subst]; split
    · exact .lam hb
    · exact .lam (pureLetDrop_subst x hv1 hcl1 hrv hb)
  | tuple hrl => exact .tuple (pureLetDropList_subst x hv1 hcl1 hrv hrl)
  | block hrl => exact .block (pureLetDropList_subst x hv1 hcl1 hrv hrl)
  | apply hf ha =>
    exact .apply (pureLetDrop_subst x hv1 hcl1 hrv hf) (pureLetDropList_subst x hv1 hcl1 hrv ha)
  | applyDir ha => exact .applyDir (pureLetDropList_subst x hv1 hcl1 hrv ha)
  | bin ha hb =>
    exact .bin (pureLetDrop_subst x hv1 hcl1 hrv ha) (pureLetDrop_subst x hv1 hcl1 hrv hb)
  | un ha => exact .un (pureLetDrop_subst x hv1 hcl1 hrv ha)
  | let_ ha hb =>
    simp only [subst]; split
    · exact .let_ (pureLetDrop_subst x hv1 hcl1 hrv ha) hb
    · exact .let_ (pureLetDrop_subst x hv1 hcl1 hrv ha) (pureLetDrop_subst x hv1 hcl1 hrv hb)
  | if_ hc ht he =>
    exact .if_ (pureLetDrop_subst x hv1 hcl1 hrv hc)
      (pureLetDrop_subst x hv1 hcl1 hrv ht) (pureLetDrop_subst x hv1 hcl1 hrv he)
  | while_ hc hb =>
    exact .while_ (pureLetDrop_subst x hv1 hcl1 hrv hc) (pureLetDrop_subst x hv1 hcl1 hrv hb)
  | match_ hs ha =>
    exact .match_ (pureLetDrop_subst x hv1 hcl1 hrv hs) (pureLetDropArms_subst x hv1 hcl1 hrv ha)
  | makeData hrl => exact .makeData (pureLetDropList_subst x hv1 hcl1 hrv hrl)
  | getTag ha => exact .getTag (pureLetDrop_subst x hv1 hcl1 hrv ha)
  | cellNew ha => exact .cellNew (pureLetDrop_subst x hv1 hcl1 hrv ha)
  | cellGet ha => exact .cellGet (pureLetDrop_subst x hv1 hcl1 hrv ha)
  | cellSet ha hb =>
    exact .cellSet (pureLetDrop_subst x hv1 hcl1 hrv ha) (pureLetDrop_subst x hv1 hcl1 hrv hb)
  | spawn ha => exact .spawn (pureLetDrop_subst x hv1 hcl1 hrv ha)
  | await ha => exact .await (pureLetDrop_subst x hv1 hcl1 hrv ha)
  | concPrim hrl => exact .concPrim (pureLetDropList_subst x hv1 hcl1 hrv hrl)
termination_by sizeOf e1

theorem pureLetDropList_subst (x : Ident) {v1 v2 : Expr}
    (hv1 : IsValue v1) (hcl1 : freeVars v1 = []) (hrv : PureLetDropRel v1 v2)
    {es1 es2 : List Expr} (hrl : PureLetDropRelList es1 es2) :
      PureLetDropRelList (substList x v1 es1) (substList x v2 es2) := by
  cases hrl with
  | nil => exact .nil
  | cons he hr =>
    exact .cons (pureLetDrop_subst x hv1 hcl1 hrv he) (pureLetDropList_subst x hv1 hcl1 hrv hr)
termination_by sizeOf es1

theorem pureLetDropArms_subst (x : Ident) {v1 v2 : Expr}
    (hv1 : IsValue v1) (hcl1 : freeVars v1 = []) (hrv : PureLetDropRel v1 v2)
    {arms1 arms2 : List (Pat × Expr)} (harms : PureLetDropRelArms arms1 arms2) :
      PureLetDropRelArms (substArms x v1 arms1) (substArms x v2 arms2) := by
  cases harms with
  | nil => exact .nil
  | cons hb hr =>
    simp only [substArms]; split
    · exact .cons hb (pureLetDropArms_subst x hv1 hcl1 hrv hr)
    · exact .cons (pureLetDrop_subst x hv1 hcl1 hrv hb) (pureLetDropArms_subst x hv1 hcl1 hrv hr)
termination_by sizeOf arms1
end

theorem pureLetDrop_substMany_zip (ks : List Ident) {vs1 vs2 : List Expr}
    (hvs1 : ∀ v ∈ vs1, IsValue v) (hcl1 : ∀ v ∈ vs1, freeVars v = [])
    (hrl : PureLetDropRelList vs1 vs2)
    {b1 b2 : Expr} (hb : PureLetDropRel b1 b2) :
    PureLetDropRel (substMany (ks.zip vs1) b1) (substMany (ks.zip vs2) b2) := by
  induction ks generalizing vs1 vs2 b1 b2 with
  | nil => exact hb
  | cons k kr ih =>
    cases hrl with
    | nil => exact hb
    | cons hv hrs =>
      exact ih
        (fun w hw => hvs1 w (List.mem_cons_of_mem _ hw))
        (fun w hw => hcl1 w (List.mem_cons_of_mem _ hw))
        hrs
        (pureLetDrop_subst k (hvs1 _ (List.mem_cons_self ..)) (hcl1 _ (List.mem_cons_self ..)) hv hb)

mutual
theorem pureLetDrop_matchPat :
    (p : Pat) → {v1 v2 : Expr} → IsValue v1 → PureLetDropRel v1 v2 →
      match matchPat p v1, matchPat p v2 with
      | none, none => True
      | some env1, some env2 =>
          env1.map Prod.fst = env2.map Prod.fst ∧
          PureLetDropRelList (env1.map Prod.snd) (env2.map Prod.snd)
      | _, _ => False
  | .wild, _, _, _, _ => by simp [matchPat]; exact .nil
  | .var x, _, _, _, hr => by simp [matchPat]; exact .cons hr .nil
  | .lit l, v1, v2, hv1, hr => by
    cases hr with
    | dropPureLet _ _ _ => cases hv1
    | lit l' =>
      simp only [matchPat]
      cases (l == l') <;> simp
      exact .nil
    | _ => cases hv1 <;> simp [matchPat]
  | .tuple ps, v1, v2, hv1, hr => by
    cases hr with
    | dropPureLet _ _ _ => cases hv1
    | tuple hrl =>
      cases hv1 with
      | tuple hvs1 => simpa [matchPat] using pureLetDrop_matchPats ps hvs1 hrl
    | _ => cases hv1 <;> simp [matchPat]
  | .ctor adt tag ps, v1, v2, hv1, hr => by
    cases hr with
    | dropPureLet _ _ _ => cases hv1
    | @makeData adt' tag' _ _ hrl =>
      cases hv1 with
      | makeData _ _ hvs1 =>
        simp only [matchPat]
        cases hcond : (adt == adt' && tag == tag')
        · simp
        · simpa using pureLetDrop_matchPats ps hvs1 hrl
    | _ => cases hv1 <;> simp [matchPat]
termination_by p => sizeOf p

theorem pureLetDrop_matchPats :
    (ps : List Pat) → {vs1 vs2 : List Expr} → (∀ v ∈ vs1, IsValue v) →
      PureLetDropRelList vs1 vs2 →
      match matchPats ps vs1, matchPats ps vs2 with
      | none, none => True
      | some env1, some env2 =>
          env1.map Prod.fst = env2.map Prod.fst ∧
          PureLetDropRelList (env1.map Prod.snd) (env2.map Prod.snd)
      | _, _ => False
  | [], _, _, _, hrl => by
    cases hrl with
    | nil => simp [matchPats]; exact .nil
    | cons _ _ => simp [matchPats]
  | p :: pr, _, _, hvs1, hrl => by
    cases hrl with
    | nil => simp [matchPats]
    | cons hr hrs =>
      have hm1 := pureLetDrop_matchPat p (hvs1 _ (List.mem_cons_self ..)) hr
      have hm2 := pureLetDrop_matchPats pr (fun w hw => hvs1 w (List.mem_cons_of_mem _ hw)) hrs
      simp only [matchPats]
      cases h1a : matchPat p _ <;> cases h1b : matchPat p _ <;> rw [h1a, h1b] at hm1
      · trivial
      · cases hm1
      · cases hm1
      · cases h2a : matchPats pr _ <;> cases h2b : matchPats pr _ <;> rw [h2a, h2b] at hm2
        · trivial
        · cases hm2
        · cases hm2
        · simp only [List.map_append]
          exact ⟨by rw [hm1.1, hm2.1], pureLetDropList_append hm1.2 hm2.2⟩
termination_by ps => sizeOf ps
end

theorem zip_fst_snd_eq (env : List (Ident × Expr)) :
    (env.map Prod.fst).zip (env.map Prod.snd) = env := by
  induction env with
  | nil => rfl
  | cons p r ih => rcases p with ⟨k, v⟩; simp [ih]

mutual
theorem matchPat_isValue :
    (p : Pat) → {v : Expr} → {env : List (Ident × Expr)} →
      IsValue v → matchPat p v = some env → ∀ q ∈ env, IsValue q.2
  | .wild, _, _, _, hm => by
    simp only [matchPat, Option.some.injEq] at hm; subst hm
    intro _ h; cases h
  | .var _, _, _, hv, hm => by
    simp only [matchPat, Option.some.injEq] at hm; subst hm
    intro q hq; simp at hq; rcases hq with ⟨_, rfl⟩; exact hv
  | .lit _, v, _, _, hm => by
    cases v <;> simp [matchPat] at hm
    rcases hm with ⟨_, rfl⟩; intro _ h; cases h
  | .tuple ps, v, _, hv, hm => by
    cases hv with
    | tuple hvs => exact matchPats_isValue ps hvs hm
    | _ => simp [matchPat] at hm
  | .ctor _ _ ps, v, _, hv, hm => by
    cases hv with
    | makeData _ _ hvs =>
      simp only [matchPat] at hm
      split at hm
      · exact matchPats_isValue ps hvs hm
      · cases hm
    | _ => simp [matchPat] at hm

theorem matchPats_isValue :
    (ps : List Pat) → {vs : List Expr} → {env : List (Ident × Expr)} →
      (∀ v ∈ vs, IsValue v) → matchPats ps vs = some env → ∀ q ∈ env, IsValue q.2
  | [], vs, _, _, hm => by
    cases vs <;> simp [matchPats] at hm
    subst hm; intro _ h; cases h
  | p :: pr, vs, _, hvs, hm => by
    cases vs with
    | nil => simp [matchPats] at hm
    | cons v vr =>
      simp only [matchPats] at hm
      cases h1 : matchPat p v with
      | none => rw [h1] at hm; cases hm
      | some b1 =>
        cases h2 : matchPats pr vr with
        | none => rw [h1, h2] at hm; cases hm
        | some b2 =>
          rw [h1, h2] at hm; injection hm with hm; subst hm
          intro q hq; rcases List.mem_append.mp hq with hq1 | hq2
          · exact matchPat_isValue p (hvs _ (List.mem_cons_self ..)) h1 q hq1
          · exact matchPats_isValue pr (fun w hw => hvs w (List.mem_cons_of_mem _ hw)) h2 q hq2
end

/- Forward stuttering simulation (`pureLetDrop_step_forward`): 1 step of `(Φ1, e1, σ1)`
   is matched by **0 or 1 step** of `(Φ2, e2, σ2)`! -/
mutual
theorem pureLetDrop_step_forward {Δ : AdtEnv} {Φ1 Φ2 : FunEnv}
    (hΦenv : PureLetDropEnv Φ1 Φ2)
    {e1 e2 e1' : Expr} {σ1 σ2 σ1' : Store}
    (hσCl : ClosedStore σ1) (he1 : freeVars e1 = [])
    (hσRel : StoreDropRel σ1 σ2)
    (hr : PureLetDropRel e1 e2)
    (hs1 : Step Δ Φ1 emptyPool e1 σ1 e1' σ1' .none) :
    ∃ e2' σ2', PureLetDropRel e1' e2' ∧ StoreDropRel σ1' σ2' ∧
      ((e2' = e2 ∧ σ2' = σ2) ∨ Step Δ Φ2 emptyPool e2 σ2 e2' σ2' .none) := by
  cases hr with
  | @dropPureLet x rhs b1 _ hpure hxnot hb =>
    simp only [freeVars, List.append_eq_nil_iff] at he1
    have hv_rhs : IsValue rhs := openPureVal_closed_isValue he1.1 hpure
    cases hs1 with
    | letStep hs_r => exact False.elim (isValue_no_step hv_rhs hs_r)
    | letTrap => exact False.elim (isValue_ne_trap hv_rhs _ rfl)
    | letVal _ =>
      rw [subst_not_mem_freeVars b1 hxnot]
      exact ⟨e2, σ2, hb, hσRel, Or.inl ⟨rfl, rfl⟩⟩
  | lit _ | var _ | loc _ | taskRef _ | syncRef _ _ | lam _ | trap _ => cases hs1
  | tuple hrl =>
    simp only [freeVars] at he1
    cases hs1 with
    | tupleStep hsl1 =>
      rcases pureLetDropList_step_forward hΦenv hσCl he1 hσRel hrl hsl1 with ⟨es2', σ2', hrl', hσ', hst⟩
      rcases hst with ⟨rfl, rfl⟩ | hsl2
      · exact ⟨_, _, .tuple hrl', hσ', Or.inl ⟨rfl, rfl⟩⟩
      · exact ⟨_, _, .tuple hrl', hσ', Or.inr (.tupleStep hsl2)⟩
    | tupleTrap htr =>
      exact ⟨.trap _, σ2, .trap _, hσRel, Or.inr (.tupleTrap (pureLetDropList_firstTrap_left hrl htr))⟩
  | block hrl =>
    cases hrl with
    | nil => cases hs1; exact ⟨.lit .unit, σ2, .lit .unit, hσRel, Or.inr .blockEmpty⟩
    | cons hr1 hrs =>
      cases hrs with
      | nil => cases hs1; exact ⟨_, σ2, hr1, hσRel, Or.inr .blockSingle⟩
      | cons hr2 hrs' =>
        simp only [freeVars, freeVarsList, List.append_eq_nil_iff] at he1
        cases hs1 with
        | blockConsStep hs_a =>
          rcases pureLetDrop_step_forward hΦenv hσCl he1.1 hσRel hr1 hs_a with ⟨a2', σ2', hr1', hσ', hst⟩
          rcases hst with ⟨rfl, rfl⟩ | hs2
          · exact ⟨_, _, .block (.cons hr1' (.cons hr2 hrs')), hσ', Or.inl ⟨rfl, rfl⟩⟩
          · exact ⟨_, _, .block (.cons hr1' (.cons hr2 hrs')), hσ', Or.inr (.blockConsStep hs2)⟩
        | blockConsVal hv1 =>
          exact ⟨_, σ2, .block (.cons hr2 hrs'), hσRel, Or.inr (.blockConsVal (pureLetDrop_val_left hr1 hv1))⟩
        | blockConsTrap =>
          rw [pureLetDrop_trap_left hr1]
          exact ⟨.trap _, σ2, .trap _, hσRel, Or.inr .blockConsTrap⟩
  | @apply fn1 fn2 args1 args2 hfn hrl =>
    simp only [freeVars, List.append_eq_nil_iff] at he1
    cases hs1 with
    | applyFn hs_f =>
      rcases pureLetDrop_step_forward hΦenv hσCl he1.1 hσRel hfn hs_f with ⟨fn2', σ2', hfn', hσ', hst⟩
      rcases hst with ⟨rfl, rfl⟩ | hs2
      · exact ⟨_, _, .apply hfn' hrl, hσ', Or.inl ⟨rfl, rfl⟩⟩
      · exact ⟨_, _, .apply hfn' hrl, hσ', Or.inr (.applyFn hs2)⟩
    | applyFnTrap =>
      rw [pureLetDrop_trap_left hfn]
      exact ⟨.trap _, σ2, .trap _, hσRel, Or.inr .applyFnTrap⟩
    | applyArgs hv1 hsl1 =>
      have hv2 := pureLetDrop_val_left hfn hv1
      rcases pureLetDropList_step_forward hΦenv hσCl he1.2 hσRel hrl hsl1 with ⟨args2', σ2', hrl', hσ', hst⟩
      rcases hst with ⟨rfl, rfl⟩ | hsl2
      · exact ⟨_, _, .apply hfn hrl', hσ', Or.inl ⟨rfl, rfl⟩⟩
      · exact ⟨_, _, .apply hfn hrl', hσ', Or.inr (.applyArgs hv2 hsl2)⟩
    | applyArgsTrap hv1 htr =>
      exact ⟨.trap _, σ2, .trap _, hσRel,
        Or.inr (.applyArgsTrap (pureLetDrop_val_left hfn hv1) (pureLetDropList_firstTrap_left hrl htr))⟩
    | @applyBeta m ps ret b1 _ _ hvs1 hlen1 =>
      cases hfn with
      | lam hb =>
        have hvs2 := pureLetDropList_val_left hrl hvs1
        have hlen2 : args2.length = ps.length := by rw [← pureLetDropList_length_eq hrl, hlen1]
        have hcl1 := freeVarsList_eq_nil_iff.mp he1.2
        exact ⟨_, σ2,
          pureLetDrop_substMany_zip (ps.map Prod.fst) hvs1 hcl1 hrl hb,
          hσRel, Or.inr (.applyBeta hvs2 hlen2)⟩
  | @applyDir nm args1 args2 hrl =>
    simp only [freeVars] at he1
    cases hs1 with
    | applyDirArgs hsl1 =>
      rcases pureLetDropList_step_forward hΦenv hσCl he1 hσRel hrl hsl1 with ⟨args2', σ2', hrl', hσ', hst⟩
      rcases hst with ⟨rfl, rfl⟩ | hsl2
      · exact ⟨_, _, .applyDir hrl', hσ', Or.inl ⟨rfl, rfl⟩⟩
      · exact ⟨_, _, .applyDir hrl', hσ', Or.inr (.applyDirArgs hsl2)⟩
    | applyDirTrap htr =>
      exact ⟨.trap _, σ2, .trap _, hσRel, Or.inr (.applyDirTrap (pureLetDropList_firstTrap_left hrl htr))⟩
    | @applyDirBeta _ fd1 _ _ hfd1 hvs1 hlen1 =>
      have henv := hΦenv nm
      rw [hfd1] at henv
      cases hfd2 : Φ2 nm <;> rw [hfd2] at henv
      · cases henv
      · rename_i fd2
        rcases henv with ⟨hparams, hbody⟩
        have hvs2 := pureLetDropList_val_left hrl hvs1
        have hlen2 : args2.length = fd2.params.length := by
          rw [← pureLetDropList_length_eq hrl, hlen1, hparams]
        have hcl1 := freeVarsList_eq_nil_iff.mp he1
        refine ⟨_, σ2, ?_, hσRel, Or.inr (.applyDirBeta hfd2 hvs2 hlen2)⟩
        unfold zipParams; rw [← hparams]
        exact pureLetDrop_substMany_zip (fd1.params.map Prod.fst) hvs1 hcl1 hrl hbody
  | bin ha hb =>
    simp only [freeVars, List.append_eq_nil_iff] at he1
    cases hs1 with
    | binLeft hs_a =>
      rcases pureLetDrop_step_forward hΦenv hσCl he1.1 hσRel ha hs_a with ⟨a2', σ2', ha', hσ', hst⟩
      rcases hst with ⟨rfl, rfl⟩ | hs2
      · exact ⟨_, _, .bin ha' hb, hσ', Or.inl ⟨rfl, rfl⟩⟩
      · exact ⟨_, _, .bin ha' hb, hσ', Or.inr (.binLeft hs2)⟩
    | binLeftTrap => rw [pureLetDrop_trap_left ha]; exact ⟨.trap _, σ2, .trap _, hσRel, Or.inr .binLeftTrap⟩
    | binAndFalse => cases ha; exact ⟨.lit (.bool false), σ2, .lit _, hσRel, Or.inr .binAndFalse⟩
    | binAndTrue => cases ha; exact ⟨_, σ2, hb, hσRel, Or.inr .binAndTrue⟩
    | binOrTrue => cases ha; exact ⟨.lit (.bool true), σ2, .lit _, hσRel, Or.inr .binOrTrue⟩
    | binOrFalse => cases ha; exact ⟨_, σ2, hb, hσRel, Or.inr .binOrFalse⟩
    | binRight hna hno hv1 hs_b =>
      have hv2 := pureLetDrop_val_left ha hv1
      rcases pureLetDrop_step_forward hΦenv hσCl he1.2 hσRel hb hs_b with ⟨b2', σ2', hb', hσ', hst⟩
      rcases hst with ⟨rfl, rfl⟩ | hs2
      · exact ⟨_, _, .bin ha hb', hσ', Or.inl ⟨rfl, rfl⟩⟩
      · exact ⟨_, _, .bin ha hb', hσ', Or.inr (.binRight hna hno hv2 hs2)⟩
    | binRightTrap hna hno hv1 =>
      rw [pureLetDrop_trap_left hb]
      exact ⟨.trap _, σ2, .trap _, hσRel, Or.inr (.binRightTrap hna hno (pureLetDrop_val_left ha hv1))⟩
    | binVal hev => cases ha; cases hb; exact ⟨.lit _, σ2, .lit _, hσRel, Or.inr (.binVal hev)⟩
    | binTrap hev => cases ha; cases hb; exact ⟨.trap _, σ2, .trap _, hσRel, Or.inr (.binTrap hev)⟩
  | un ha =>
    simp only [freeVars] at he1
    cases hs1 with
    | unStep hs_a =>
      rcases pureLetDrop_step_forward hΦenv hσCl he1 hσRel ha hs_a with ⟨a2', σ2', ha', hσ', hst⟩
      rcases hst with ⟨rfl, rfl⟩ | hs2
      · exact ⟨_, _, .un ha', hσ', Or.inl ⟨rfl, rfl⟩⟩
      · exact ⟨_, _, .un ha', hσ', Or.inr (.unStep hs2)⟩
    | unTrap => rw [pureLetDrop_trap_left ha]; exact ⟨.trap _, σ2, .trap _, hσRel, Or.inr .unTrap⟩
    | unVal hev => cases ha; exact ⟨.lit _, σ2, .lit _, hσRel, Or.inr (.unVal hev)⟩
  | let_ ha hb =>
    simp only [freeVars, List.append_eq_nil_iff] at he1
    cases hs1 with
    | letStep hs_a =>
      rcases pureLetDrop_step_forward hΦenv hσCl he1.1 hσRel ha hs_a with ⟨a2', σ2', ha', hσ', hst⟩
      rcases hst with ⟨rfl, rfl⟩ | hs2
      · exact ⟨_, _, .let_ ha' hb, hσ', Or.inl ⟨rfl, rfl⟩⟩
      · exact ⟨_, _, .let_ ha' hb, hσ', Or.inr (.letStep hs2)⟩
    | letTrap => rw [pureLetDrop_trap_left ha]; exact ⟨.trap _, σ2, .trap _, hσRel, Or.inr .letTrap⟩
    | letVal hv1 =>
      exact ⟨_, σ2, pureLetDrop_subst _ hv1 he1.1 ha hb, hσRel,
        Or.inr (.letVal (pureLetDrop_val_left ha hv1))⟩
  | if_ hc ht he =>
    simp only [freeVars, List.append_eq_nil_iff] at he1
    cases hs1 with
    | ifStep hs_c =>
      rcases pureLetDrop_step_forward hΦenv hσCl he1.1.1 hσRel hc hs_c with ⟨c2', σ2', hc', hσ', hst⟩
      rcases hst with ⟨rfl, rfl⟩ | hs2
      · exact ⟨_, _, .if_ hc' ht he, hσ', Or.inl ⟨rfl, rfl⟩⟩
      · exact ⟨_, _, .if_ hc' ht he, hσ', Or.inr (.ifStep hs2)⟩
    | ifTrap => rw [pureLetDrop_trap_left hc]; exact ⟨.trap _, σ2, .trap _, hσRel, Or.inr .ifTrap⟩
    | ifTrue => cases hc; exact ⟨_, σ2, ht, hσRel, Or.inr .ifTrue⟩
    | ifFalse => cases hc; exact ⟨_, σ2, he, hσRel, Or.inr .ifFalse⟩
  | while_ hc hb =>
    cases hs1 with
    | whileUnfold =>
      exact ⟨_, σ2, .if_ hc (.block (.cons hb (.cons (.while_ hc hb) .nil))) (.lit .unit),
        hσRel, Or.inr .whileUnfold⟩
  | match_ hs_r harms =>
    simp only [freeVars, List.append_eq_nil_iff] at he1
    cases hs1 with
    | matchScrut hs_s =>
      rcases pureLetDrop_step_forward hΦenv hσCl he1.1 hσRel hs_r hs_s with ⟨s2', σ2', hs_r', hσ', hst⟩
      rcases hst with ⟨rfl, rfl⟩ | hs2
      · exact ⟨_, _, .match_ hs_r' harms, hσ', Or.inl ⟨rfl, rfl⟩⟩
      · exact ⟨_, _, .match_ hs_r' harms, hσ', Or.inr (.matchScrut hs2)⟩
    | matchScrutTrap => rw [pureLetDrop_trap_left hs_r]; exact ⟨.trap _, σ2, .trap _, hσRel, Or.inr .matchScrutTrap⟩
    | matchEmpty hv1 =>
      cases harms with
      | nil => exact ⟨.trap .matchFailure, σ2, .trap _, hσRel, Or.inr (.matchEmpty (pureLetDrop_val_left hs_r hv1))⟩
    | @matchHit _ p _ _ env1 _ hv1 hm1 =>
      cases harms with
      | cons hb _ =>
        have hmp := pureLetDrop_matchPat p hv1 hs_r
        rw [hm1] at hmp
        cases hm2 : matchPat p _ <;> rw [hm2] at hmp
        · cases hmp
        · rename_i env2
          have henv1_cl := (matchPat_closed he1.1 hm1).1
          have henv1_val := matchPat_isValue p hv1 hm1
          refine ⟨_, σ2, ?_, hσRel, Or.inr (.matchHit (pureLetDrop_val_left hs_r hv1) hm2)⟩
          rw [← zip_fst_snd_eq env1, ← zip_fst_snd_eq env2, ← hmp.1]
          exact pureLetDrop_substMany_zip (env1.map Prod.fst)
            (fun w hw => by rcases List.mem_map.mp hw with ⟨q, hq, rfl⟩; exact henv1_val q hq)
            (fun w hw => by rcases List.mem_map.mp hw with ⟨q, hq, rfl⟩; exact henv1_cl q hq)
            hmp.2 hb
    | @matchMiss _ p _ _ _ hv1 hm1 =>
      cases harms with
      | cons _ hrs =>
        have hmp := pureLetDrop_matchPat p hv1 hs_r
        rw [hm1] at hmp
        cases hm2 : matchPat p _ <;> rw [hm2] at hmp
        · exact ⟨_, σ2, .match_ hs_r hrs, hσRel, Or.inr (.matchMiss (pureLetDrop_val_left hs_r hv1) hm2)⟩
        · cases hmp
  | makeData hrl =>
    simp only [freeVars] at he1
    cases hs1 with
    | makeDataStep hsl1 =>
      rcases pureLetDropList_step_forward hΦenv hσCl he1 hσRel hrl hsl1 with ⟨es2', σ2', hrl', hσ', hst⟩
      rcases hst with ⟨rfl, rfl⟩ | hsl2
      · exact ⟨_, _, .makeData hrl', hσ', Or.inl ⟨rfl, rfl⟩⟩
      · exact ⟨_, _, .makeData hrl', hσ', Or.inr (.makeDataStep hsl2)⟩
    | makeDataTrap htr =>
      exact ⟨.trap _, σ2, .trap _, hσRel, Or.inr (.makeDataTrap (pureLetDropList_firstTrap_left hrl htr))⟩
  | getTag ha =>
    simp only [freeVars] at he1
    cases hs1 with
    | getTagStep hs_a =>
      rcases pureLetDrop_step_forward hΦenv hσCl he1 hσRel ha hs_a with ⟨a2', σ2', ha', hσ', hst⟩
      rcases hst with ⟨rfl, rfl⟩ | hs2
      · exact ⟨_, _, .getTag ha', hσ', Or.inl ⟨rfl, rfl⟩⟩
      · exact ⟨_, _, .getTag ha', hσ', Or.inr (.getTagStep hs2)⟩
    | getTagTrap => rw [pureLetDrop_trap_left ha]; exact ⟨.trap _, σ2, .trap _, hσRel, Or.inr .getTagTrap⟩
    | getTagVal hvs1 =>
      cases ha with
      | makeData hrl =>
        exact ⟨.lit _, σ2, .lit _, hσRel, Or.inr (.getTagVal (pureLetDropList_val_left hrl hvs1))⟩
  | cellNew ha =>
    simp only [freeVars] at he1
    cases hs1 with
    | cellNewStep hs_a =>
      rcases pureLetDrop_step_forward hΦenv hσCl he1 hσRel ha hs_a with ⟨a2', σ2', ha', hσ', hst⟩
      rcases hst with ⟨rfl, rfl⟩ | hs2
      · exact ⟨_, _, .cellNew ha', hσ', Or.inl ⟨rfl, rfl⟩⟩
      · exact ⟨_, _, .cellNew ha', hσ', Or.inr (.cellNewStep hs2)⟩
    | cellNewTrap => rw [pureLetDrop_trap_left ha]; exact ⟨.trap _, σ2, .trap _, hσRel, Or.inr .cellNewTrap⟩
    | cellNewVal hv1 =>
      rw [storeDropRel_length hσRel]
      exact ⟨.loc _, _, .loc _, storeDropRel_append hσRel ha,
        Or.inr (.cellNewVal (pureLetDrop_val_left ha hv1))⟩
  | cellGet ha =>
    simp only [freeVars] at he1
    cases hs1 with
    | cellGetStep hs_a =>
      rcases pureLetDrop_step_forward hΦenv hσCl he1 hσRel ha hs_a with ⟨a2', σ2', ha', hσ', hst⟩
      rcases hst with ⟨rfl, rfl⟩ | hs2
      · exact ⟨_, _, .cellGet ha', hσ', Or.inl ⟨rfl, rfl⟩⟩
      · exact ⟨_, _, .cellGet ha', hσ', Or.inr (.cellGetStep hs2)⟩
    | cellGetTrap => rw [pureLetDrop_trap_left ha]; exact ⟨.trap _, σ2, .trap _, hσRel, Or.inr .cellGetTrap⟩
    | cellGetVal hl1 =>
      cases ha
      rcases storeDropRel_getElem_left hσRel hl1 with ⟨v2, hl2, hvRel⟩
      exact ⟨v2, σ2, hvRel, hσRel, Or.inr (.cellGetVal hl2)⟩
  | cellSet ha hb =>
    simp only [freeVars, List.append_eq_nil_iff] at he1
    cases hs1 with
    | cellSetLeft hs_a =>
      rcases pureLetDrop_step_forward hΦenv hσCl he1.1 hσRel ha hs_a with ⟨a2', σ2', ha', hσ', hst⟩
      rcases hst with ⟨rfl, rfl⟩ | hs2
      · exact ⟨_, _, .cellSet ha' hb, hσ', Or.inl ⟨rfl, rfl⟩⟩
      · exact ⟨_, _, .cellSet ha' hb, hσ', Or.inr (.cellSetLeft hs2)⟩
    | cellSetLeftTrap => rw [pureLetDrop_trap_left ha]; exact ⟨.trap _, σ2, .trap _, hσRel, Or.inr .cellSetLeftTrap⟩
    | cellSetRight hv1 hs_b =>
      have hv2 := pureLetDrop_val_left ha hv1
      rcases pureLetDrop_step_forward hΦenv hσCl he1.2 hσRel hb hs_b with ⟨b2', σ2', hb', hσ', hst⟩
      rcases hst with ⟨rfl, rfl⟩ | hs2
      · exact ⟨_, _, .cellSet ha hb', hσ', Or.inl ⟨rfl, rfl⟩⟩
      · exact ⟨_, _, .cellSet ha hb', hσ', Or.inr (.cellSetRight hv2 hs2)⟩
    | cellSetRightTrap hv1 =>
      rw [pureLetDrop_trap_left hb]
      exact ⟨.trap _, σ2, .trap _, hσRel, Or.inr (.cellSetRightTrap (pureLetDrop_val_left ha hv1))⟩
    | @cellSetVal l _ _ hlt hv1 =>
      cases ha
      have hlt2 : l < σ2.length := by rwa [← storeDropRel_length hσRel]
      exact ⟨.lit .unit, _, .lit .unit, storeDropRel_set hσRel l hb,
        Or.inr (.cellSetVal hlt2 (pureLetDrop_val_left hb hv1))⟩
  | spawn ha =>
    simp only [freeVars] at he1
    cases hs1 with
    | spawnStep hs_a =>
      rcases pureLetDrop_step_forward hΦenv hσCl he1 hσRel ha hs_a with ⟨a2', σ2', ha', hσ', hst⟩
      rcases hst with ⟨rfl, rfl⟩ | hs2
      · exact ⟨_, _, .spawn ha', hσ', Or.inl ⟨rfl, rfl⟩⟩
      · exact ⟨_, _, .spawn ha', hσ', Or.inr (.spawnStep hs2)⟩
    | spawnTrap => rw [pureLetDrop_trap_left ha]; exact ⟨.trap _, σ2, .trap _, hσRel, Or.inr .spawnTrap⟩
  | await ha =>
    simp only [freeVars] at he1
    cases hs1 with
    | awaitStep hs_a =>
      rcases pureLetDrop_step_forward hΦenv hσCl he1 hσRel ha hs_a with ⟨a2', σ2', ha', hσ', hst⟩
      rcases hst with ⟨rfl, rfl⟩ | hs2
      · exact ⟨_, _, .await ha', hσ', Or.inl ⟨rfl, rfl⟩⟩
      · exact ⟨_, _, .await ha', hσ', Or.inr (.awaitStep hs2)⟩
    | awaitTrap => rw [pureLetDrop_trap_left ha]; exact ⟨.trap _, σ2, .trap _, hσRel, Or.inr .awaitTrap⟩
    | awaitVal h _ | awaitTaskTrap h => simp [emptyPool] at h
  | concPrim hrl =>
    simp only [freeVars] at he1
    cases hs1 with
    | concPrimArgs hsl1 =>
      rcases pureLetDropList_step_forward hΦenv hσCl he1 hσRel hrl hsl1 with ⟨es2', σ2', hrl', hσ', hst⟩
      rcases hst with ⟨rfl, rfl⟩ | hsl2
      · exact ⟨_, _, .concPrim hrl', hσ', Or.inl ⟨rfl, rfl⟩⟩
      · exact ⟨_, _, .concPrim hrl', hσ', Or.inr (.concPrimArgs hsl2)⟩
    | concPrimTrap htr =>
      exact ⟨.trap _, σ2, .trap _, hσRel, Or.inr (.concPrimTrap (pureLetDropList_firstTrap_left hrl htr))⟩
    | concPrimVal hc => exact False.elim (stepConcPrim_emptyPool_none_false hc)
termination_by sizeOf e1

theorem pureLetDropList_step_forward {Δ : AdtEnv} {Φ1 Φ2 : FunEnv}
    (hΦenv : PureLetDropEnv Φ1 Φ2)
    {es1 es2 es1' : List Expr} {σ1 σ2 σ1' : Store}
    (hσCl : ClosedStore σ1) (hes1 : freeVarsList es1 = [])
    (hσRel : StoreDropRel σ1 σ2)
    (hrl : PureLetDropRelList es1 es2)
    (hsl1 : StepList Δ Φ1 emptyPool es1 σ1 es1' σ1' .none) :
    ∃ es2' σ2', PureLetDropRelList es1' es2' ∧ StoreDropRel σ1' σ2' ∧
      ((es2' = es2 ∧ σ2' = σ2) ∨ StepList Δ Φ2 emptyPool es2 σ2 es2' σ2' .none) := by
  cases hrl with
  | nil => cases hsl1
  | cons hr hrs =>
    simp only [freeVarsList, List.append_eq_nil_iff] at hes1
    cases hsl1 with
    | head hs1 =>
      rcases pureLetDrop_step_forward hΦenv hσCl hes1.1 hσRel hr hs1 with ⟨e2', σ2', hr', hσ', hst⟩
      rcases hst with ⟨rfl, rfl⟩ | hs2
      · exact ⟨_, _, .cons hr' hrs, hσ', Or.inl ⟨rfl, rfl⟩⟩
      · exact ⟨_, _, .cons hr' hrs, hσ', Or.inr (.head hs2)⟩
    | tail hv1 hsl_r =>
      have hv2 := pureLetDrop_val_left hr hv1
      rcases pureLetDropList_step_forward hΦenv hσCl hes1.2 hσRel hrs hsl_r with ⟨es2', σ2', hrs', hσ', hst⟩
      rcases hst with ⟨rfl, rfl⟩ | hsl2
      · exact ⟨_, _, .cons hr hrs', hσ', Or.inl ⟨rfl, rfl⟩⟩
      · exact ⟨_, _, .cons hr hrs', hσ', Or.inr (.tail hv2 hsl2)⟩
termination_by sizeOf es1
end

theorem pureLetDrop_steps_forward {Δ : AdtEnv} {Φ1 Φ2 : FunEnv}
    (hΦenv : PureLetDropEnv Φ1 Φ2) (hΦ1cl : ClosedFunEnv Φ1)
    {e1 e2 e1' : Expr} {σ1 σ2 σ1' : Store}
    (hσCl : ClosedStore σ1) (he1 : freeVars e1 = [])
    (hσRel : StoreDropRel σ1 σ2) (hr : PureLetDropRel e1 e2)
    (hsteps : Steps Δ Φ1 e1 σ1 e1' σ1') :
    ∃ e2' σ2', PureLetDropRel e1' e2' ∧ StoreDropRel σ1' σ2' ∧ Steps Δ Φ2 e2 σ2 e2' σ2' := by
  induction hsteps generalizing e2 σ2 with
  | refl => exact ⟨e2, σ2, hr, hσRel, .refl _ _⟩
  | trans hs1 _ ih =>
    rcases pureLetDrop_step_forward hΦenv hσCl he1 hσRel hr hs1 with ⟨e2_m, σ2_m, hr_m, hσ_m, hst⟩
    rcases step_preserves_closed hΦ1cl hσCl he1 hs1 with ⟨he1_m, hσCl_m⟩
    rcases ih hσCl_m he1_m hσ_m hr_m with ⟨e2', σ2', hr', hσ', hsteps2⟩
    rcases hst with ⟨rfl, rfl⟩ | hs2
    · exact ⟨e2', σ2', hr', hσ', hsteps2⟩
    · exact ⟨e2', σ2', hr', hσ', .trans hs2 hsteps2⟩

/- Administrative size-decreasing redex peeling on `e1` when `e2` is already a value / trap. -/
mutual
theorem pureLetDrop_val_right_step_or_val {Δ : AdtEnv} {Φ1 : FunEnv} (σ1 : Store)
    {e1 e2 : Expr} (hcl : freeVars e1 = []) (hr : PureLetDropRel e1 e2) (hv2 : IsValue e2) :
      IsValue e1 ∨ ∃ e1', Step Δ Φ1 emptyPool e1 σ1 e1' σ1 .none ∧
        sizeOf e1' < sizeOf e1 ∧ PureLetDropRel e1' e2 := by
  cases hr with
  | @dropPureLet x rhs b1 _ hpure hxnot hb =>
    simp only [freeVars, List.append_eq_nil_iff] at hcl
    have hv_rhs : IsValue rhs := openPureVal_closed_isValue hcl.1 hpure
    refine Or.inr ⟨b1, ?_, by simp +arith, hb⟩
    have hs := Step.letVal (Δ := Δ) (Φ := Φ1) (pool := emptyPool) (x := x) (e2 := b1) (σ := σ1) hv_rhs
    rwa [subst_not_mem_freeVars b1 hxnot] at hs
  | lit l => exact Or.inl (.lit l)
  | loc l => exact Or.inl (.loc l)
  | taskRef tid => exact Or.inl (.taskRef tid)
  | syncRef k id => exact Or.inl (.syncRef k id)
  | lam _ => exact Or.inl (.lam _ _ _ _)
  | @tuple es1 _ hrl =>
    cases hv2 with
    | tuple hvs2 =>
      simp only [freeVars] at hcl
      rcases pureLetDropList_val_right_step_or_val σ1 hcl hrl hvs2 with hvs1 | ⟨es1', hsl, hsz, hrl'⟩
      · exact Or.inl (.tuple hvs1)
      · exact Or.inr ⟨.tuple es1', .tupleStep hsl, by simp +arith; omega, .tuple hrl'⟩
  | @makeData adt tag es1 _ hrl =>
    cases hv2 with
    | makeData _ _ hvs2 =>
      simp only [freeVars] at hcl
      rcases pureLetDropList_val_right_step_or_val σ1 hcl hrl hvs2 with hvs1 | ⟨es1', hsl, hsz, hrl'⟩
      · exact Or.inl (.makeData adt tag hvs1)
      · exact Or.inr ⟨.makeData adt tag es1', .makeDataStep hsl, by simp +arith; omega, .makeData hrl'⟩
  | var _ | trap _ | block _ | apply _ _ | applyDir _ | bin _ _ | un _
  | let_ _ _ | if_ _ _ _ | while_ _ _ | match_ _ _ | getTag _ | cellNew _
  | cellGet _ | cellSet _ _ | spawn _ | await _ | concPrim _ =>
    cases hv2
termination_by sizeOf e1

theorem pureLetDropList_val_right_step_or_val {Δ : AdtEnv} {Φ1 : FunEnv} (σ1 : Store)
    {es1 es2 : List Expr} (hcl : freeVarsList es1 = []) (hrl : PureLetDropRelList es1 es2)
    (hvs2 : ∀ v ∈ es2, IsValue v) :
      (∀ v ∈ es1, IsValue v) ∨ ∃ es1', StepList Δ Φ1 emptyPool es1 σ1 es1' σ1 .none ∧
        sizeOf es1' < sizeOf es1 ∧ PureLetDropRelList es1' es2 := by
  cases hrl with
  | nil => exact Or.inl (fun _ h => by cases h)
  | @cons a1 _ r1 _ hr hrs =>
    simp only [freeVarsList, List.append_eq_nil_iff] at hcl
    rcases pureLetDrop_val_right_step_or_val σ1 hcl.1 hr (hvs2 _ (List.mem_cons_self ..)) with
      hv1 | ⟨a1', hs, hsz, hr'⟩
    · rcases pureLetDropList_val_right_step_or_val σ1 hcl.2 hrs
        (fun w hw => hvs2 w (List.mem_cons_of_mem _ hw)) with hvs_r | ⟨r1', hsl, hsz, hrs'⟩
      · exact Or.inl (fun w hw => by rcases List.mem_cons.mp hw with rfl | hwr; exact hv1; exact hvs_r w hwr)
      · exact Or.inr ⟨a1 :: r1', .tail hv1 hsl, by simp +arith; omega, .cons hr hrs'⟩
    · exact Or.inr ⟨a1' :: r1, .head hs, by simp +arith; omega, .cons hr' hrs⟩
termination_by sizeOf es1
end

theorem pureLetDrop_trap_right_step_or_trap {Δ : AdtEnv} {Φ1 : FunEnv} (σ1 : Store)
    {e1 : Expr} {t : Trap} (hcl : freeVars e1 = []) (hr : PureLetDropRel e1 (.trap t)) :
    e1 = .trap t ∨ ∃ e1', Step Δ Φ1 emptyPool e1 σ1 e1' σ1 .none ∧
      sizeOf e1' < sizeOf e1 ∧ PureLetDropRel e1' (.trap t) := by
  cases hr with
  | trap _ => exact Or.inl rfl
  | @dropPureLet x rhs b1 _ hpure hxnot hb =>
    simp only [freeVars, List.append_eq_nil_iff] at hcl
    have hv_rhs : IsValue rhs := openPureVal_closed_isValue hcl.1 hpure
    refine Or.inr ⟨b1, ?_, by simp +arith, hb⟩
    have hs := Step.letVal (Δ := Δ) (Φ := Φ1) (pool := emptyPool) (x := x) (e2 := b1) (σ := σ1) hv_rhs
    rwa [subst_not_mem_freeVars b1 hxnot] at hs

theorem pureLetDropList_firstTrap_right_step_or_trap {Δ : AdtEnv} {Φ1 : FunEnv} (σ1 : Store)
    {es1 es2 : List Expr} {t : Trap}
    (hcl : freeVarsList es1 = []) (hrl : PureLetDropRelList es1 es2) (htr2 : ListFirstTrap es2 t) :
    ListFirstTrap es1 t ∨ ∃ es1', StepList Δ Φ1 emptyPool es1 σ1 es1' σ1 .none ∧
      sizeOf es1' < sizeOf es1 ∧ PureLetDropRelList es1' es2 := by
  induction es1 generalizing es2 with
  | nil => cases hrl; cases htr2
  | cons a1 r1 ih =>
    cases hrl with
    | cons hr hrs =>
      simp only [freeVarsList, List.append_eq_nil_iff] at hcl
      cases htr2 with
      | head _ _ =>
        rcases pureLetDrop_trap_right_step_or_trap σ1 hcl.1 hr with rfl | ⟨a1', hs, hsz, hr'⟩
        · exact Or.inl (.head t r1)
        · exact Or.inr ⟨a1' :: r1, .head hs, by simp +arith; omega, .cons hr' hrs⟩
      | tail hv2 htr_r2 =>
        rcases pureLetDrop_val_right_step_or_val σ1 hcl.1 hr hv2 with hv1 | ⟨a1', hs, hsz, hr'⟩
        · rcases ih hcl.2 hrs htr_r2 with htr_r1 | ⟨r1', hsl, hsz, hrs'⟩
          · exact Or.inl (.tail hv1 htr_r1)
          · exact Or.inr ⟨a1 :: r1', .tail hv1 hsl, by simp +arith; omega, .cons hr hrs'⟩
        · exact Or.inr ⟨a1' :: r1, .head hs, by simp +arith; omega, .cons hr' hrs⟩

theorem pureLetDrop_val_right_steps {Δ : AdtEnv} {Φ1 : FunEnv} (hΦ1cl : ClosedFunEnv Φ1)
    {e1 e2 : Expr} {σ1 : Store} (hσCl : ClosedStore σ1) (hcl : freeVars e1 = [])
    (hr : PureLetDropRel e1 e2) (hv2 : IsValue e2) :
    ∃ v1, Steps Δ Φ1 e1 σ1 v1 σ1 ∧ IsValue v1 ∧ PureLetDropRel v1 e2 := by
  rcases pureLetDrop_val_right_step_or_val σ1 hcl hr hv2 with hv1 | ⟨e1', hs, _, hr'⟩
  · exact ⟨e1, .refl _ _, hv1, hr⟩
  · rcases step_preserves_closed hΦ1cl hσCl hcl hs with ⟨hcl', _⟩
    rcases pureLetDrop_val_right_steps hΦ1cl hσCl hcl' hr' hv2 with ⟨v1, hsteps, hv1, hrv⟩
    exact ⟨v1, .trans hs hsteps, hv1, hrv⟩
termination_by sizeOf e1

theorem pureLetDrop_trap_right_steps {Δ : AdtEnv} {Φ1 : FunEnv} (hΦ1cl : ClosedFunEnv Φ1)
    {e1 : Expr} {t : Trap} {σ1 : Store} (hσCl : ClosedStore σ1) (hcl : freeVars e1 = [])
    (hr : PureLetDropRel e1 (.trap t)) :
    Steps Δ Φ1 e1 σ1 (.trap t) σ1 := by
  rcases pureLetDrop_trap_right_step_or_trap σ1 hcl hr with rfl | ⟨e1', hs, _, hr'⟩
  · exact .refl _ _
  · rcases step_preserves_closed hΦ1cl hσCl hcl hs with ⟨hcl', _⟩
    exact .trans hs (pureLetDrop_trap_right_steps hΦ1cl hσCl hcl' hr')
termination_by sizeOf e1

/- Backward simulation (`pureLetDrop_step_backward`) by well-founded induction on `sizeOf e1`:
   1 step of `(Φ2, e2, σ2)` is matched by `1+` steps (`Steps`) of `(Φ1, e1, σ1)`! -/
mutual
theorem pureLetDrop_step_backward {Δ : AdtEnv} {Φ1 Φ2 : FunEnv}
    (hΦenv : PureLetDropEnv Φ1 Φ2) (hΦ1cl : ClosedFunEnv Φ1)
    {e1 e2 e2' : Expr} {σ1 σ2 σ2' : Store}
    (hσCl : ClosedStore σ1) (he1 : freeVars e1 = [])
    (hσRel : StoreDropRel σ1 σ2)
    (hr : PureLetDropRel e1 e2)
    (hs2 : Step Δ Φ2 emptyPool e2 σ2 e2' σ2' .none) :
    ∃ e1' σ1', PureLetDropRel e1' e2' ∧ StoreDropRel σ1' σ2' ∧
      Steps Δ Φ1 e1 σ1 e1' σ1' := by
  cases hr with
  | @dropPureLet x rhs b1 _ hpure hxnot hb =>
    simp only [freeVars, List.append_eq_nil_iff] at he1
    have hv_rhs : IsValue rhs := openPureVal_closed_isValue he1.1 hpure
    have hs_drop : Step Δ Φ1 emptyPool (.let_ x rhs b1) σ1 b1 σ1 .none := by
      have hs := Step.letVal (Δ := Δ) (Φ := Φ1) (pool := emptyPool) (x := x) (e2 := b1) (σ := σ1) hv_rhs
      rwa [subst_not_mem_freeVars b1 hxnot] at hs
    rcases step_preserves_closed hΦ1cl hσCl (by simp [freeVars, he1.1, he1.2]) hs_drop with ⟨hb1_cl, _⟩
    have _ : sizeOf b1 < sizeOf (Expr.let_ x rhs b1) := by simp +arith
    rcases pureLetDrop_step_backward hΦenv hΦ1cl hσCl hb1_cl hσRel hb hs2 with ⟨e1', σ1', hr', hσ', hsteps⟩
    exact ⟨e1', σ1', hr', hσ', .trans hs_drop hsteps⟩
  | lit _ | var _ | loc _ | taskRef _ | syncRef _ _ | lam _ | trap _ => cases hs2
  | @tuple es1 es2 hrl =>
    simp only [freeVars] at he1
    cases hs2 with
    | tupleStep hsl2 =>
      rcases pureLetDropList_step_backward hΦenv hΦ1cl hσCl he1 hσRel hrl hsl2 with ⟨es1', σ1', hrl', hσ', hsteps_l⟩
      exact ⟨.tuple es1', σ1', .tuple hrl', hσ', hsteps_l .tupleStep⟩
    | tupleTrap htr2 =>
      rcases pureLetDropList_firstTrap_right_step_or_trap σ1 he1 hrl htr2 with htr1 | ⟨es1_m, hsl_m, hsz, hrl_m⟩
      · exact ⟨.trap _, σ1, .trap _, hσRel, .single (.tupleTrap htr1)⟩
      · have hs_m : Step Δ Φ1 emptyPool (.tuple es1) σ1 (.tuple es1_m) σ1 .none := .tupleStep hsl_m
        rcases step_preserves_closed hΦ1cl hσCl (by simpa [freeVars] using he1) hs_m with ⟨hcl_m, _⟩
        have _ : sizeOf (Expr.tuple es1_m) < sizeOf (Expr.tuple es1) := by simp +arith; omega
        rcases pureLetDrop_step_backward hΦenv hΦ1cl hσCl hcl_m hσRel (.tuple hrl_m) (.tupleTrap htr2) with
          ⟨e1', σ1', hr', hσ', hsteps⟩
        exact ⟨e1', σ1', hr', hσ', .trans hs_m hsteps⟩
  | @block es1 es2 hrl =>
    cases hrl with
    | nil => cases hs2; exact ⟨.lit .unit, σ1, .lit .unit, hσRel, .single .blockEmpty⟩
    | @cons a1 a2 r1 r2 hr1 hrs =>
      cases hrs with
      | nil => cases hs2; exact ⟨a1, σ1, hr1, hσRel, .single .blockSingle⟩
      | @cons b1 b2 rr1 rr2 hr2 hrs' =>
        simp only [freeVars, freeVarsList, List.append_eq_nil_iff] at he1
        cases hs2 with
        | blockConsStep hs_a2 =>
          rcases pureLetDrop_step_backward hΦenv hΦ1cl hσCl he1.1 hσRel hr1 hs_a2 with
            ⟨a1', σ1', hr1', hσ', hsteps_a⟩
          exact ⟨.block (a1' :: b1 :: rr1), σ1', .block (.cons hr1' (.cons hr2 hrs')), hσ',
            Steps.liftCongr (fun x => .block (x :: b1 :: rr1)) (fun hs => .blockConsStep hs) hsteps_a⟩
        | blockConsVal hv2 =>
          rcases pureLetDrop_val_right_step_or_val σ1 he1.1 hr1 hv2 with hv1 | ⟨a1_m, hs_m, hsz, hr1_m⟩
          · exact ⟨.block (b1 :: rr1), σ1, .block (.cons hr2 hrs'), hσRel, .single (.blockConsVal hv1)⟩
          · have hs_blk : Step Δ Φ1 emptyPool (.block (a1 :: b1 :: rr1)) σ1 (.block (a1_m :: b1 :: rr1)) σ1 .none :=
              .blockConsStep hs_m
            rcases step_preserves_closed hΦ1cl hσCl (by simp [freeVars, freeVarsList, he1.1, he1.2.1, he1.2.2]) hs_blk with ⟨hcl_m, _⟩
            have _ : sizeOf (Expr.block (a1_m :: b1 :: rr1)) < sizeOf (Expr.block (a1 :: b1 :: rr1)) := by simp +arith; omega
            rcases pureLetDrop_step_backward hΦenv hΦ1cl hσCl hcl_m hσRel
              (.block (.cons hr1_m (.cons hr2 hrs'))) (.blockConsVal hv2) with ⟨e1', σ1', hr', hσ', hsteps⟩
            exact ⟨e1', σ1', hr', hσ', .trans hs_blk hsteps⟩
        | blockConsTrap =>
          rcases pureLetDrop_trap_right_step_or_trap σ1 he1.1 hr1 with rfl | ⟨a1_m, hs_m, hsz, hr1_m⟩
          · exact ⟨.trap _, σ1, .trap _, hσRel, .single .blockConsTrap⟩
          · have hs_blk : Step Δ Φ1 emptyPool (.block (a1 :: b1 :: rr1)) σ1 (.block (a1_m :: b1 :: rr1)) σ1 .none :=
              .blockConsStep hs_m
            rcases step_preserves_closed hΦ1cl hσCl (by simp [freeVars, freeVarsList, he1.1, he1.2.1, he1.2.2]) hs_blk with ⟨hcl_m, _⟩
            have _ : sizeOf (Expr.block (a1_m :: b1 :: rr1)) < sizeOf (Expr.block (a1 :: b1 :: rr1)) := by simp +arith; omega
            rcases pureLetDrop_step_backward hΦenv hΦ1cl hσCl hcl_m hσRel
              (.block (.cons hr1_m (.cons hr2 hrs'))) .blockConsTrap with ⟨e1', σ1', hr', hσ', hsteps⟩
            exact ⟨e1', σ1', hr', hσ', .trans hs_blk hsteps⟩
  | @apply fn1 fn2 args1 args2 hfn hrl =>
    simp only [freeVars, List.append_eq_nil_iff] at he1
    cases hs2 with
    | applyFn hs_f2 =>
      rcases pureLetDrop_step_backward hΦenv hΦ1cl hσCl he1.1 hσRel hfn hs_f2 with ⟨fn1', σ1', hfn', hσ', hsteps_f⟩
      exact ⟨.apply fn1' args1, σ1', .apply hfn' hrl, hσ',
        Steps.liftCongr (fun x => .apply x args1) (fun hs => .applyFn hs) hsteps_f⟩
    | applyFnTrap =>
      rcases pureLetDrop_trap_right_step_or_trap σ1 he1.1 hfn with rfl | ⟨fn1_m, hs_m, hsz, hfn_m⟩
      · exact ⟨.trap _, σ1, .trap _, hσRel, .single .applyFnTrap⟩
      · have hs_app : Step Δ Φ1 emptyPool (.apply fn1 args1) σ1 (.apply fn1_m args1) σ1 .none := .applyFn hs_m
        rcases step_preserves_closed hΦ1cl hσCl (by simp [freeVars, he1.1, he1.2]) hs_app with ⟨hcl_m, _⟩
        have _ : sizeOf (Expr.apply fn1_m args1) < sizeOf (Expr.apply fn1 args1) := by simp +arith; omega
        rcases pureLetDrop_step_backward hΦenv hΦ1cl hσCl hcl_m hσRel (.apply hfn_m hrl) .applyFnTrap with
          ⟨e1', σ1', hr', hσ', hsteps⟩
        exact ⟨e1', σ1', hr', hσ', .trans hs_app hsteps⟩
    | applyArgs hv2 hsl2 =>
      rcases pureLetDrop_val_right_step_or_val σ1 he1.1 hfn hv2 with hv1 | ⟨fn1_m, hs_m, hsz, hfn_m⟩
      · rcases pureLetDropList_step_backward hΦenv hΦ1cl hσCl he1.2 hσRel hrl hsl2 with
          ⟨args1', σ1', hrl', hσ', hsteps_l⟩
        exact ⟨.apply fn1 args1', σ1', .apply hfn hrl', hσ', hsteps_l (fun hsl => .applyArgs hv1 hsl)⟩
      · have hs_app : Step Δ Φ1 emptyPool (.apply fn1 args1) σ1 (.apply fn1_m args1) σ1 .none := .applyFn hs_m
        rcases step_preserves_closed hΦ1cl hσCl (by simp [freeVars, he1.1, he1.2]) hs_app with ⟨hcl_m, _⟩
        have _ : sizeOf (Expr.apply fn1_m args1) < sizeOf (Expr.apply fn1 args1) := by simp +arith; omega
        rcases pureLetDrop_step_backward hΦenv hΦ1cl hσCl hcl_m hσRel (.apply hfn_m hrl) (.applyArgs hv2 hsl2) with
          ⟨e1', σ1', hr', hσ', hsteps⟩
        exact ⟨e1', σ1', hr', hσ', .trans hs_app hsteps⟩
    | applyArgsTrap hv2 htr2 =>
      rcases pureLetDrop_val_right_step_or_val σ1 he1.1 hfn hv2 with hv1 | ⟨fn1_m, hs_m, hsz, hfn_m⟩
      · rcases pureLetDropList_firstTrap_right_step_or_trap σ1 he1.2 hrl htr2 with htr1 | ⟨args1_m, hsl_m, hsz, hrl_m⟩
        · exact ⟨.trap _, σ1, .trap _, hσRel, .single (.applyArgsTrap hv1 htr1)⟩
        · have hs_app : Step Δ Φ1 emptyPool (.apply fn1 args1) σ1 (.apply fn1 args1_m) σ1 .none := .applyArgs hv1 hsl_m
          rcases step_preserves_closed hΦ1cl hσCl (by simp [freeVars, he1.1, he1.2]) hs_app with ⟨hcl_m, _⟩
          have _ : sizeOf (Expr.apply fn1 args1_m) < sizeOf (Expr.apply fn1 args1) := by simp +arith; omega
          rcases pureLetDrop_step_backward hΦenv hΦ1cl hσCl hcl_m hσRel (.apply hfn hrl_m) (.applyArgsTrap hv2 htr2) with
            ⟨e1', σ1', hr', hσ', hsteps⟩
          exact ⟨e1', σ1', hr', hσ', .trans hs_app hsteps⟩
      · have hs_app : Step Δ Φ1 emptyPool (.apply fn1 args1) σ1 (.apply fn1_m args1) σ1 .none := .applyFn hs_m
        rcases step_preserves_closed hΦ1cl hσCl (by simp [freeVars, he1.1, he1.2]) hs_app with ⟨hcl_m, _⟩
        have _ : sizeOf (Expr.apply fn1_m args1) < sizeOf (Expr.apply fn1 args1) := by simp +arith; omega
        rcases pureLetDrop_step_backward hΦenv hΦ1cl hσCl hcl_m hσRel (.apply hfn_m hrl) (.applyArgsTrap hv2 htr2) with
          ⟨e1', σ1', hr', hσ', hsteps⟩
        exact ⟨e1', σ1', hr', hσ', .trans hs_app hsteps⟩
    | @applyBeta m ps ret b2 _ _ hvs2 hlen2 =>
      rcases pureLetDrop_val_right_step_or_val σ1 he1.1 hfn (.lam m ps ret b2) with hv1 | ⟨fn1_m, hs_m, hsz, hfn_m⟩
      · rcases pureLetDropList_val_right_step_or_val σ1 he1.2 hrl hvs2 with hvs1 | ⟨args1_m, hsl_m, hsz, hrl_m⟩
        · cases hfn with
          | dropPureLet _ _ _ => cases hv1
          | lam hb =>
            have hlen1 : args1.length = ps.length := by rw [pureLetDropList_length_eq hrl, hlen2]
            have hcl1 := freeVarsList_eq_nil_iff.mp he1.2
            exact ⟨_, σ1, pureLetDrop_substMany_zip (ps.map Prod.fst) hvs1 hcl1 hrl hb,
              hσRel, .single (.applyBeta hvs1 hlen1)⟩
        · have hs_app : Step Δ Φ1 emptyPool (.apply fn1 args1) σ1 (.apply fn1 args1_m) σ1 .none := .applyArgs hv1 hsl_m
          rcases step_preserves_closed hΦ1cl hσCl (by simp [freeVars, he1.1, he1.2]) hs_app with ⟨hcl_m, _⟩
          have _ : sizeOf (Expr.apply fn1 args1_m) < sizeOf (Expr.apply fn1 args1) := by simp +arith; omega
          rcases pureLetDrop_step_backward hΦenv hΦ1cl hσCl hcl_m hσRel (.apply hfn hrl_m) (.applyBeta hvs2 hlen2) with
            ⟨e1', σ1', hr', hσ', hsteps⟩
          exact ⟨e1', σ1', hr', hσ', .trans hs_app hsteps⟩
      · have hs_app : Step Δ Φ1 emptyPool (.apply fn1 args1) σ1 (.apply fn1_m args1) σ1 .none := .applyFn hs_m
        rcases step_preserves_closed hΦ1cl hσCl (by simp [freeVars, he1.1, he1.2]) hs_app with ⟨hcl_m, _⟩
        have _ : sizeOf (Expr.apply fn1_m args1) < sizeOf (Expr.apply fn1 args1) := by simp +arith; omega
        rcases pureLetDrop_step_backward hΦenv hΦ1cl hσCl hcl_m hσRel (.apply hfn_m hrl) (.applyBeta hvs2 hlen2) with
          ⟨e1', σ1', hr', hσ', hsteps⟩
        exact ⟨e1', σ1', hr', hσ', .trans hs_app hsteps⟩
  | @applyDir nm args1 args2 hrl =>
    simp only [freeVars] at he1
    cases hs2 with
    | applyDirArgs hsl2 =>
      rcases pureLetDropList_step_backward hΦenv hΦ1cl hσCl he1 hσRel hrl hsl2 with
        ⟨args1', σ1', hrl', hσ', hsteps_l⟩
      exact ⟨.applyDir nm args1', σ1', .applyDir hrl', hσ', hsteps_l (fun hsl => .applyDirArgs hsl)⟩
    | applyDirTrap htr2 =>
      rcases pureLetDropList_firstTrap_right_step_or_trap σ1 he1 hrl htr2 with htr1 | ⟨args1_m, hsl_m, hsz, hrl_m⟩
      · exact ⟨.trap _, σ1, .trap _, hσRel, .single (.applyDirTrap htr1)⟩
      · have hs_app : Step Δ Φ1 emptyPool (.applyDir nm args1) σ1 (.applyDir nm args1_m) σ1 .none := .applyDirArgs hsl_m
        rcases step_preserves_closed hΦ1cl hσCl (by simpa [freeVars] using he1) hs_app with ⟨hcl_m, _⟩
        have _ : sizeOf (Expr.applyDir nm args1_m) < sizeOf (Expr.applyDir nm args1) := by simp +arith; omega
        rcases pureLetDrop_step_backward hΦenv hΦ1cl hσCl hcl_m hσRel (.applyDir hrl_m) (.applyDirTrap htr2) with
          ⟨e1', σ1', hr', hσ', hsteps⟩
        exact ⟨e1', σ1', hr', hσ', .trans hs_app hsteps⟩
    | applyDirBeta hfd2 hvs2 hlen2 =>
      rcases pureLetDropList_val_right_step_or_val σ1 he1 hrl hvs2 with hvs1 | ⟨args1_m, hsl_m, hsz, hrl_m⟩
      · have henv := hΦenv nm
        rw [hfd2] at henv
        cases hfd1 : Φ1 nm <;> rw [hfd1] at henv
        · cases henv
        · rename_i fd1
          rcases henv with ⟨hparams, hbody⟩
          have hlen1 : args1.length = fd1.params.length := by
            rw [pureLetDropList_length_eq hrl, hlen2, ← hparams]
          have hcl1 := freeVarsList_eq_nil_iff.mp he1
          refine ⟨_, σ1, ?_, hσRel, .single (.applyDirBeta hfd1 hvs1 hlen1)⟩
          unfold zipParams; rw [← hparams]
          exact pureLetDrop_substMany_zip (fd1.params.map Prod.fst) hvs1 hcl1 hrl hbody
      · have hs_app : Step Δ Φ1 emptyPool (.applyDir nm args1) σ1 (.applyDir nm args1_m) σ1 .none := .applyDirArgs hsl_m
        rcases step_preserves_closed hΦ1cl hσCl (by simpa [freeVars] using he1) hs_app with ⟨hcl_m, _⟩
        have _ : sizeOf (Expr.applyDir nm args1_m) < sizeOf (Expr.applyDir nm args1) := by simp +arith; omega
        rcases pureLetDrop_step_backward hΦenv hΦ1cl hσCl hcl_m hσRel (.applyDir hrl_m) (.applyDirBeta hfd2 hvs2 hlen2) with
          ⟨e1', σ1', hr', hσ', hsteps⟩
        exact ⟨e1', σ1', hr', hσ', .trans hs_app hsteps⟩
  | @bin op a1 a2 b1 b2 ha hb =>
    simp only [freeVars, List.append_eq_nil_iff] at he1
    cases hs2 with
    | binLeft hs_a2 =>
      rcases pureLetDrop_step_backward hΦenv hΦ1cl hσCl he1.1 hσRel ha hs_a2 with ⟨a1', σ1', ha', hσ', hsteps_a⟩
      exact ⟨.bin op a1' b1, σ1', .bin ha' hb, hσ',
        Steps.liftCongr (fun x => .bin op x b1) (fun hs => .binLeft hs) hsteps_a⟩
    | binLeftTrap =>
      rcases pureLetDrop_trap_right_step_or_trap σ1 he1.1 ha with rfl | ⟨a1_m, hs_m, hsz, ha_m⟩
      · exact ⟨.trap _, σ1, .trap _, hσRel, .single .binLeftTrap⟩
      · have hs_b : Step Δ Φ1 emptyPool (.bin op a1 b1) σ1 (.bin op a1_m b1) σ1 .none := .binLeft hs_m
        rcases step_preserves_closed hΦ1cl hσCl (by simp [freeVars, he1.1, he1.2]) hs_b with ⟨hcl_m, _⟩
        have _ : sizeOf (Expr.bin op a1_m b1) < sizeOf (Expr.bin op a1 b1) := by simp +arith; omega
        rcases pureLetDrop_step_backward hΦenv hΦ1cl hσCl hcl_m hσRel (.bin ha_m hb) .binLeftTrap with
          ⟨e1', σ1', hr', hσ', hsteps⟩
        exact ⟨e1', σ1', hr', hσ', .trans hs_b hsteps⟩
    | binAndFalse =>
      rcases pureLetDrop_val_right_step_or_val σ1 he1.1 ha (.lit _) with hv1 | ⟨a1_m, hs_m, hsz, ha_m⟩
      · cases ha with | dropPureLet _ _ _ => cases hv1 | lit _ => exact ⟨.lit (.bool false), σ1, .lit _, hσRel, .single .binAndFalse⟩
      · have hs_b : Step Δ Φ1 emptyPool (.bin .and a1 b1) σ1 (.bin .and a1_m b1) σ1 .none := .binLeft hs_m
        rcases step_preserves_closed hΦ1cl hσCl (by simp [freeVars, he1.1, he1.2]) hs_b with ⟨hcl_m, _⟩
        have _ : sizeOf (Expr.bin .and a1_m b1) < sizeOf (Expr.bin .and a1 b1) := by simp +arith; omega
        rcases pureLetDrop_step_backward hΦenv hΦ1cl hσCl hcl_m hσRel (.bin ha_m hb) .binAndFalse with
          ⟨e1', σ1', hr', hσ', hsteps⟩
        exact ⟨e1', σ1', hr', hσ', .trans hs_b hsteps⟩
    | binAndTrue =>
      rcases pureLetDrop_val_right_step_or_val σ1 he1.1 ha (.lit _) with hv1 | ⟨a1_m, hs_m, hsz, ha_m⟩
      · cases ha with | dropPureLet _ _ _ => cases hv1 | lit _ => exact ⟨b1, σ1, hb, hσRel, .single .binAndTrue⟩
      · have hs_b : Step Δ Φ1 emptyPool (.bin .and a1 b1) σ1 (.bin .and a1_m b1) σ1 .none := .binLeft hs_m
        rcases step_preserves_closed hΦ1cl hσCl (by simp [freeVars, he1.1, he1.2]) hs_b with ⟨hcl_m, _⟩
        have _ : sizeOf (Expr.bin .and a1_m b1) < sizeOf (Expr.bin .and a1 b1) := by simp +arith; omega
        rcases pureLetDrop_step_backward hΦenv hΦ1cl hσCl hcl_m hσRel (.bin ha_m hb) .binAndTrue with
          ⟨e1', σ1', hr', hσ', hsteps⟩
        exact ⟨e1', σ1', hr', hσ', .trans hs_b hsteps⟩
    | binOrTrue =>
      rcases pureLetDrop_val_right_step_or_val σ1 he1.1 ha (.lit _) with hv1 | ⟨a1_m, hs_m, hsz, ha_m⟩
      · cases ha with | dropPureLet _ _ _ => cases hv1 | lit _ => exact ⟨.lit (.bool true), σ1, .lit _, hσRel, .single .binOrTrue⟩
      · have hs_b : Step Δ Φ1 emptyPool (.bin .or a1 b1) σ1 (.bin .or a1_m b1) σ1 .none := .binLeft hs_m
        rcases step_preserves_closed hΦ1cl hσCl (by simp [freeVars, he1.1, he1.2]) hs_b with ⟨hcl_m, _⟩
        have _ : sizeOf (Expr.bin .or a1_m b1) < sizeOf (Expr.bin .or a1 b1) := by simp +arith; omega
        rcases pureLetDrop_step_backward hΦenv hΦ1cl hσCl hcl_m hσRel (.bin ha_m hb) .binOrTrue with
          ⟨e1', σ1', hr', hσ', hsteps⟩
        exact ⟨e1', σ1', hr', hσ', .trans hs_b hsteps⟩
    | binOrFalse =>
      rcases pureLetDrop_val_right_step_or_val σ1 he1.1 ha (.lit _) with hv1 | ⟨a1_m, hs_m, hsz, ha_m⟩
      · cases ha with | dropPureLet _ _ _ => cases hv1 | lit _ => exact ⟨b1, σ1, hb, hσRel, .single .binOrFalse⟩
      · have hs_b : Step Δ Φ1 emptyPool (.bin .or a1 b1) σ1 (.bin .or a1_m b1) σ1 .none := .binLeft hs_m
        rcases step_preserves_closed hΦ1cl hσCl (by simp [freeVars, he1.1, he1.2]) hs_b with ⟨hcl_m, _⟩
        have _ : sizeOf (Expr.bin .or a1_m b1) < sizeOf (Expr.bin .or a1 b1) := by simp +arith; omega
        rcases pureLetDrop_step_backward hΦenv hΦ1cl hσCl hcl_m hσRel (.bin ha_m hb) .binOrFalse with
          ⟨e1', σ1', hr', hσ', hsteps⟩
        exact ⟨e1', σ1', hr', hσ', .trans hs_b hsteps⟩
    | binRight hna hno hv2 hs_b2 =>
      rcases pureLetDrop_val_right_step_or_val σ1 he1.1 ha hv2 with hv1 | ⟨a1_m, hs_m, hsz, ha_m⟩
      · rcases pureLetDrop_step_backward hΦenv hΦ1cl hσCl he1.2 hσRel hb hs_b2 with ⟨b1', σ1', hb', hσ', hsteps_b⟩
        exact ⟨.bin op a1 b1', σ1', .bin ha hb', hσ',
          Steps.liftCongr (fun x => .bin op a1 x) (fun hs => .binRight hna hno hv1 hs) hsteps_b⟩
      · have hs_b : Step Δ Φ1 emptyPool (.bin op a1 b1) σ1 (.bin op a1_m b1) σ1 .none := .binLeft hs_m
        rcases step_preserves_closed hΦ1cl hσCl (by simp [freeVars, he1.1, he1.2]) hs_b with ⟨hcl_m, _⟩
        have _ : sizeOf (Expr.bin op a1_m b1) < sizeOf (Expr.bin op a1 b1) := by simp +arith; omega
        rcases pureLetDrop_step_backward hΦenv hΦ1cl hσCl hcl_m hσRel (.bin ha_m hb) (.binRight hna hno hv2 hs_b2) with
          ⟨e1', σ1', hr', hσ', hsteps⟩
        exact ⟨e1', σ1', hr', hσ', .trans hs_b hsteps⟩
    | binRightTrap hna hno hv2 =>
      rcases pureLetDrop_val_right_step_or_val σ1 he1.1 ha hv2 with hv1 | ⟨a1_m, hs_m, hsz, ha_m⟩
      · rcases pureLetDrop_trap_right_step_or_trap σ1 he1.2 hb with rfl | ⟨b1_m, hs_bm, hsz, hb_m⟩
        · exact ⟨.trap _, σ1, .trap _, hσRel, .single (.binRightTrap hna hno hv1)⟩
        · have hs_b : Step Δ Φ1 emptyPool (.bin op a1 b1) σ1 (.bin op a1 b1_m) σ1 .none := .binRight hna hno hv1 hs_bm
          rcases step_preserves_closed hΦ1cl hσCl (by simp [freeVars, he1.1, he1.2]) hs_b with ⟨hcl_m, _⟩
          have _ : sizeOf (Expr.bin op a1 b1_m) < sizeOf (Expr.bin op a1 b1) := by simp +arith; omega
          rcases pureLetDrop_step_backward hΦenv hΦ1cl hσCl hcl_m hσRel (.bin ha hb_m) (.binRightTrap hna hno hv2) with
            ⟨e1', σ1', hr', hσ', hsteps⟩
          exact ⟨e1', σ1', hr', hσ', .trans hs_b hsteps⟩
      · have hs_b : Step Δ Φ1 emptyPool (.bin op a1 b1) σ1 (.bin op a1_m b1) σ1 .none := .binLeft hs_m
        rcases step_preserves_closed hΦ1cl hσCl (by simp [freeVars, he1.1, he1.2]) hs_b with ⟨hcl_m, _⟩
        have _ : sizeOf (Expr.bin op a1_m b1) < sizeOf (Expr.bin op a1 b1) := by simp +arith; omega
        rcases pureLetDrop_step_backward hΦenv hΦ1cl hσCl hcl_m hσRel (.bin ha_m hb) (.binRightTrap hna hno hv2) with
          ⟨e1', σ1', hr', hσ', hsteps⟩
        exact ⟨e1', σ1', hr', hσ', .trans hs_b hsteps⟩
    | binVal hev =>
      have hna : op ≠ .and := by intro h; subst h; simp [evalBinOp] at hev
      have hno : op ≠ .or := by intro h; subst h; simp [evalBinOp] at hev
      rcases pureLetDrop_val_right_step_or_val σ1 he1.1 ha (.lit _) with hv1 | ⟨a1_m, hs_m, hsz, ha_m⟩
      · rcases pureLetDrop_val_right_step_or_val σ1 he1.2 hb (.lit _) with hvb1 | ⟨b1_m, hs_bm, hsz, hb_m⟩
        · cases ha with
          | dropPureLet _ _ _ => cases hv1
          | lit _ =>
            cases hb with
            | dropPureLet _ _ _ => cases hvb1
            | lit _ => exact ⟨.lit _, σ1, .lit _, hσRel, .single (.binVal hev)⟩
        · have hs_b : Step Δ Φ1 emptyPool (.bin op a1 b1) σ1 (.bin op a1 b1_m) σ1 .none := .binRight hna hno hv1 hs_bm
          rcases step_preserves_closed hΦ1cl hσCl (by simp [freeVars, he1.1, he1.2]) hs_b with ⟨hcl_m, _⟩
          have _ : sizeOf (Expr.bin op a1 b1_m) < sizeOf (Expr.bin op a1 b1) := by simp +arith; omega
          rcases pureLetDrop_step_backward hΦenv hΦ1cl hσCl hcl_m hσRel (.bin ha hb_m) (.binVal hev) with
            ⟨e1', σ1', hr', hσ', hsteps⟩
          exact ⟨e1', σ1', hr', hσ', .trans hs_b hsteps⟩
      · have hs_b : Step Δ Φ1 emptyPool (.bin op a1 b1) σ1 (.bin op a1_m b1) σ1 .none := .binLeft hs_m
        rcases step_preserves_closed hΦ1cl hσCl (by simp [freeVars, he1.1, he1.2]) hs_b with ⟨hcl_m, _⟩
        have _ : sizeOf (Expr.bin op a1_m b1) < sizeOf (Expr.bin op a1 b1) := by simp +arith; omega
        rcases pureLetDrop_step_backward hΦenv hΦ1cl hσCl hcl_m hσRel (.bin ha_m hb) (.binVal hev) with
          ⟨e1', σ1', hr', hσ', hsteps⟩
        exact ⟨e1', σ1', hr', hσ', .trans hs_b hsteps⟩
    | binTrap hev =>
      have hna : op ≠ .and := by intro h; subst h; simp [evalBinOp] at hev
      have hno : op ≠ .or := by intro h; subst h; simp [evalBinOp] at hev
      rcases pureLetDrop_val_right_step_or_val σ1 he1.1 ha (.lit _) with hv1 | ⟨a1_m, hs_m, hsz, ha_m⟩
      · rcases pureLetDrop_val_right_step_or_val σ1 he1.2 hb (.lit _) with hvb1 | ⟨b1_m, hs_bm, hsz, hb_m⟩
        · cases ha with
          | dropPureLet _ _ _ => cases hv1
          | lit _ =>
            cases hb with
            | dropPureLet _ _ _ => cases hvb1
            | lit _ => exact ⟨.trap _, σ1, .trap _, hσRel, .single (.binTrap hev)⟩
        · have hs_b : Step Δ Φ1 emptyPool (.bin op a1 b1) σ1 (.bin op a1 b1_m) σ1 .none := .binRight hna hno hv1 hs_bm
          rcases step_preserves_closed hΦ1cl hσCl (by simp [freeVars, he1.1, he1.2]) hs_b with ⟨hcl_m, _⟩
          have _ : sizeOf (Expr.bin op a1 b1_m) < sizeOf (Expr.bin op a1 b1) := by simp +arith; omega
          rcases pureLetDrop_step_backward hΦenv hΦ1cl hσCl hcl_m hσRel (.bin ha hb_m) (.binTrap hev) with
            ⟨e1', σ1', hr', hσ', hsteps⟩
          exact ⟨e1', σ1', hr', hσ', .trans hs_b hsteps⟩
      · have hs_b : Step Δ Φ1 emptyPool (.bin op a1 b1) σ1 (.bin op a1_m b1) σ1 .none := .binLeft hs_m
        rcases step_preserves_closed hΦ1cl hσCl (by simp [freeVars, he1.1, he1.2]) hs_b with ⟨hcl_m, _⟩
        have _ : sizeOf (Expr.bin op a1_m b1) < sizeOf (Expr.bin op a1 b1) := by simp +arith; omega
        rcases pureLetDrop_step_backward hΦenv hΦ1cl hσCl hcl_m hσRel (.bin ha_m hb) (.binTrap hev) with
          ⟨e1', σ1', hr', hσ', hsteps⟩
        exact ⟨e1', σ1', hr', hσ', .trans hs_b hsteps⟩
  | @un op a1 a2 ha =>
    simp only [freeVars] at he1
    cases hs2 with
    | unStep hs_a2 =>
      rcases pureLetDrop_step_backward hΦenv hΦ1cl hσCl he1 hσRel ha hs_a2 with ⟨a1', σ1', ha', hσ', hsteps_a⟩
      exact ⟨.un op a1', σ1', .un ha', hσ',
        Steps.liftCongr (fun x => .un op x) (fun hs => .unStep hs) hsteps_a⟩
    | unTrap =>
      rcases pureLetDrop_trap_right_step_or_trap σ1 he1 ha with rfl | ⟨a1_m, hs_m, hsz, ha_m⟩
      · exact ⟨.trap _, σ1, .trap _, hσRel, .single .unTrap⟩
      · have hs_u : Step Δ Φ1 emptyPool (.un op a1) σ1 (.un op a1_m) σ1 .none := .unStep hs_m
        rcases step_preserves_closed hΦ1cl hσCl (by simpa [freeVars] using he1) hs_u with ⟨hcl_m, _⟩
        have _ : sizeOf (Expr.un op a1_m) < sizeOf (Expr.un op a1) := by simp +arith; omega
        rcases pureLetDrop_step_backward hΦenv hΦ1cl hσCl hcl_m hσRel (.un ha_m) .unTrap with
          ⟨e1', σ1', hr', hσ', hsteps⟩
        exact ⟨e1', σ1', hr', hσ', .trans hs_u hsteps⟩
    | unVal hev =>
      rcases pureLetDrop_val_right_step_or_val σ1 he1 ha (.lit _) with hv1 | ⟨a1_m, hs_m, hsz, ha_m⟩
      · cases ha with | dropPureLet _ _ _ => cases hv1 | lit _ => exact ⟨.lit _, σ1, .lit _, hσRel, .single (.unVal hev)⟩
      · have hs_u : Step Δ Φ1 emptyPool (.un op a1) σ1 (.un op a1_m) σ1 .none := .unStep hs_m
        rcases step_preserves_closed hΦ1cl hσCl (by simpa [freeVars] using he1) hs_u with ⟨hcl_m, _⟩
        have _ : sizeOf (Expr.un op a1_m) < sizeOf (Expr.un op a1) := by simp +arith; omega
        rcases pureLetDrop_step_backward hΦenv hΦ1cl hσCl hcl_m hσRel (.un ha_m) (.unVal hev) with
          ⟨e1', σ1', hr', hσ', hsteps⟩
        exact ⟨e1', σ1', hr', hσ', .trans hs_u hsteps⟩
  | @let_ x a1 a2 b1 b2 ha hb =>
    simp only [freeVars, List.append_eq_nil_iff] at he1
    cases hs2 with
    | letStep hs_a2 =>
      rcases pureLetDrop_step_backward hΦenv hΦ1cl hσCl he1.1 hσRel ha hs_a2 with ⟨a1', σ1', ha', hσ', hsteps_a⟩
      exact ⟨.let_ x a1' b1, σ1', .let_ ha' hb, hσ',
        Steps.liftCongr (fun u => .let_ x u b1) (fun hs => .letStep hs) hsteps_a⟩
    | letTrap =>
      rcases pureLetDrop_trap_right_step_or_trap σ1 he1.1 ha with rfl | ⟨a1_m, hs_m, hsz, ha_m⟩
      · exact ⟨.trap _, σ1, .trap _, hσRel, .single .letTrap⟩
      · have hs_l : Step Δ Φ1 emptyPool (.let_ x a1 b1) σ1 (.let_ x a1_m b1) σ1 .none := .letStep hs_m
        rcases step_preserves_closed hΦ1cl hσCl (by simp [freeVars, he1.1, he1.2]) hs_l with ⟨hcl_m, _⟩
        have _ : sizeOf (Expr.let_ x a1_m b1) < sizeOf (Expr.let_ x a1 b1) := by simp +arith; omega
        rcases pureLetDrop_step_backward hΦenv hΦ1cl hσCl hcl_m hσRel (.let_ ha_m hb) .letTrap with
          ⟨e1', σ1', hr', hσ', hsteps⟩
        exact ⟨e1', σ1', hr', hσ', .trans hs_l hsteps⟩
    | letVal hv2 =>
      rcases pureLetDrop_val_right_step_or_val σ1 he1.1 ha hv2 with hv1 | ⟨a1_m, hs_m, hsz, ha_m⟩
      · exact ⟨_, σ1, pureLetDrop_subst x hv1 he1.1 ha hb, hσRel, .single (.letVal hv1)⟩
      · have hs_l : Step Δ Φ1 emptyPool (.let_ x a1 b1) σ1 (.let_ x a1_m b1) σ1 .none := .letStep hs_m
        rcases step_preserves_closed hΦ1cl hσCl (by simp [freeVars, he1.1, he1.2]) hs_l with ⟨hcl_m, _⟩
        have _ : sizeOf (Expr.let_ x a1_m b1) < sizeOf (Expr.let_ x a1 b1) := by simp +arith; omega
        rcases pureLetDrop_step_backward hΦenv hΦ1cl hσCl hcl_m hσRel (.let_ ha_m hb) (.letVal hv2) with
          ⟨e1', σ1', hr', hσ', hsteps⟩
        exact ⟨e1', σ1', hr', hσ', .trans hs_l hsteps⟩
  | @if_ c1 c2 t1 t2 f1 f2 hc ht hf =>
    simp only [freeVars, List.append_eq_nil_iff] at he1
    cases hs2 with
    | ifStep hs_c2 =>
      rcases pureLetDrop_step_backward hΦenv hΦ1cl hσCl he1.1.1 hσRel hc hs_c2 with ⟨c1', σ1', hc', hσ', hsteps_c⟩
      exact ⟨.if_ c1' t1 f1, σ1', .if_ hc' ht hf, hσ',
        Steps.liftCongr (fun u => .if_ u t1 f1) (fun hs => .ifStep hs) hsteps_c⟩
    | ifTrap =>
      rcases pureLetDrop_trap_right_step_or_trap σ1 he1.1.1 hc with rfl | ⟨c1_m, hs_m, hsz, hc_m⟩
      · exact ⟨.trap _, σ1, .trap _, hσRel, .single .ifTrap⟩
      · have hs_i : Step Δ Φ1 emptyPool (.if_ c1 t1 f1) σ1 (.if_ c1_m t1 f1) σ1 .none := .ifStep hs_m
        rcases step_preserves_closed hΦ1cl hσCl (by simp [freeVars, he1.1.1, he1.1.2, he1.2]) hs_i with ⟨hcl_m, _⟩
        have _ : sizeOf (Expr.if_ c1_m t1 f1) < sizeOf (Expr.if_ c1 t1 f1) := by simp +arith; omega
        rcases pureLetDrop_step_backward hΦenv hΦ1cl hσCl hcl_m hσRel (.if_ hc_m ht hf) .ifTrap with
          ⟨e1', σ1', hr', hσ', hsteps⟩
        exact ⟨e1', σ1', hr', hσ', .trans hs_i hsteps⟩
    | ifTrue =>
      rcases pureLetDrop_val_right_step_or_val σ1 he1.1.1 hc (.lit _) with hv1 | ⟨c1_m, hs_m, hsz, hc_m⟩
      · cases hc with | dropPureLet _ _ _ => cases hv1 | lit _ => exact ⟨t1, σ1, ht, hσRel, .single .ifTrue⟩
      · have hs_i : Step Δ Φ1 emptyPool (.if_ c1 t1 f1) σ1 (.if_ c1_m t1 f1) σ1 .none := .ifStep hs_m
        rcases step_preserves_closed hΦ1cl hσCl (by simp [freeVars, he1.1.1, he1.1.2, he1.2]) hs_i with ⟨hcl_m, _⟩
        have _ : sizeOf (Expr.if_ c1_m t1 f1) < sizeOf (Expr.if_ c1 t1 f1) := by simp +arith; omega
        rcases pureLetDrop_step_backward hΦenv hΦ1cl hσCl hcl_m hσRel (.if_ hc_m ht hf) .ifTrue with
          ⟨e1', σ1', hr', hσ', hsteps⟩
        exact ⟨e1', σ1', hr', hσ', .trans hs_i hsteps⟩
    | ifFalse =>
      rcases pureLetDrop_val_right_step_or_val σ1 he1.1.1 hc (.lit _) with hv1 | ⟨c1_m, hs_m, hsz, hc_m⟩
      · cases hc with | dropPureLet _ _ _ => cases hv1 | lit _ => exact ⟨f1, σ1, hf, hσRel, .single .ifFalse⟩
      · have hs_i : Step Δ Φ1 emptyPool (.if_ c1 t1 f1) σ1 (.if_ c1_m t1 f1) σ1 .none := .ifStep hs_m
        rcases step_preserves_closed hΦ1cl hσCl (by simp [freeVars, he1.1.1, he1.1.2, he1.2]) hs_i with ⟨hcl_m, _⟩
        have _ : sizeOf (Expr.if_ c1_m t1 f1) < sizeOf (Expr.if_ c1 t1 f1) := by simp +arith; omega
        rcases pureLetDrop_step_backward hΦenv hΦ1cl hσCl hcl_m hσRel (.if_ hc_m ht hf) .ifFalse with
          ⟨e1', σ1', hr', hσ', hsteps⟩
        exact ⟨e1', σ1', hr', hσ', .trans hs_i hsteps⟩
  | while_ hc hb =>
    cases hs2 with
    | whileUnfold =>
      exact ⟨_, σ1, .if_ hc (.block (.cons hb (.cons (.while_ hc hb) .nil))) (.lit .unit),
        hσRel, .single .whileUnfold⟩
  | @match_ s1 s2 arms1 arms2 hs_r harms =>
    simp only [freeVars, List.append_eq_nil_iff] at he1
    cases hs2 with
    | matchScrut hs_s2 =>
      rcases pureLetDrop_step_backward hΦenv hΦ1cl hσCl he1.1 hσRel hs_r hs_s2 with ⟨s1', σ1', hs_r', hσ', hsteps_s⟩
      exact ⟨.match_ s1' arms1, σ1', .match_ hs_r' harms, hσ',
        Steps.liftCongr (fun u => .match_ u arms1) (fun hs => .matchScrut hs) hsteps_s⟩
    | matchScrutTrap =>
      rcases pureLetDrop_trap_right_step_or_trap σ1 he1.1 hs_r with rfl | ⟨s1_m, hs_m, hsz, hs_rm⟩
      · exact ⟨.trap _, σ1, .trap _, hσRel, .single .matchScrutTrap⟩
      · have hs_mt : Step Δ Φ1 emptyPool (.match_ s1 arms1) σ1 (.match_ s1_m arms1) σ1 .none := .matchScrut hs_m
        rcases step_preserves_closed hΦ1cl hσCl (by simp [freeVars, he1.1, he1.2]) hs_mt with ⟨hcl_m, _⟩
        have _ : sizeOf (Expr.match_ s1_m arms1) < sizeOf (Expr.match_ s1 arms1) := by simp +arith; omega
        rcases pureLetDrop_step_backward hΦenv hΦ1cl hσCl hcl_m hσRel (.match_ hs_rm harms) .matchScrutTrap with
          ⟨e1', σ1', hr', hσ', hsteps⟩
        exact ⟨e1', σ1', hr', hσ', .trans hs_mt hsteps⟩
    | matchEmpty hv2 =>
      cases harms with
      | nil =>
        rcases pureLetDrop_val_right_step_or_val σ1 he1.1 hs_r hv2 with hv1 | ⟨s1_m, hs_m, hsz, hs_rm⟩
        · exact ⟨.trap .matchFailure, σ1, .trap _, hσRel, .single (.matchEmpty hv1)⟩
        · have hs_mt : Step Δ Φ1 emptyPool (.match_ s1 []) σ1 (.match_ s1_m []) σ1 .none := .matchScrut hs_m
          rcases step_preserves_closed hΦ1cl hσCl (by simp [freeVars, freeVarsArms, he1.1]) hs_mt with ⟨hcl_m, _⟩
          have _ : sizeOf (Expr.match_ s1_m []) < sizeOf (Expr.match_ s1 []) := by simp +arith; omega
          rcases pureLetDrop_step_backward hΦenv hΦ1cl hσCl hcl_m hσRel (.match_ hs_rm .nil) (.matchEmpty hv2) with
            ⟨e1', σ1', hr', hσ', hsteps⟩
          exact ⟨e1', σ1', hr', hσ', .trans hs_mt hsteps⟩
    | @matchHit _ p _ _ env2 _ hv2 hm2 =>
      cases harms with
      | @cons _ b1 _ r1 _ hb hrs =>
        rcases pureLetDrop_val_right_step_or_val σ1 he1.1 hs_r hv2 with hv1 | ⟨s1_m, hs_m, hsz, hs_rm⟩
        · have hmp := pureLetDrop_matchPat p hv1 hs_r
          rw [hm2] at hmp
          cases hm1 : matchPat p s1 <;> rw [hm1] at hmp
          · cases hmp
          · rename_i env1
            have henv1_cl := (matchPat_closed he1.1 hm1).1
            have henv1_val := matchPat_isValue p hv1 hm1
            refine ⟨_, σ1, ?_, hσRel, .single (.matchHit hv1 hm1)⟩
            rw [← zip_fst_snd_eq env1, ← zip_fst_snd_eq env2, ← hmp.1]
            exact pureLetDrop_substMany_zip (env1.map Prod.fst)
              (fun w hw => by rcases List.mem_map.mp hw with ⟨q, hq, rfl⟩; exact henv1_val q hq)
              (fun w hw => by rcases List.mem_map.mp hw with ⟨q, hq, rfl⟩; exact henv1_cl q hq)
              hmp.2 hb
        · have hs_mt : Step Δ Φ1 emptyPool (.match_ s1 ((p, b1) :: r1)) σ1 (.match_ s1_m ((p, b1) :: r1)) σ1 .none :=
            .matchScrut hs_m
          rcases step_preserves_closed hΦ1cl hσCl (by simp [freeVars, he1.1, he1.2]) hs_mt with ⟨hcl_m, _⟩
          have _ : sizeOf (Expr.match_ s1_m ((p, b1) :: r1)) < sizeOf (Expr.match_ s1 ((p, b1) :: r1)) := by
            simp +arith; omega
          rcases pureLetDrop_step_backward hΦenv hΦ1cl hσCl hcl_m hσRel (.match_ hs_rm (.cons hb hrs))
            (.matchHit hv2 hm2) with ⟨e1', σ1', hr', hσ', hsteps⟩
          exact ⟨e1', σ1', hr', hσ', .trans hs_mt hsteps⟩
    | @matchMiss _ p _ _ _ hv2 hm2 =>
      cases harms with
      | @cons _ b1 _ r1 _ hb hrs =>
        rcases pureLetDrop_val_right_step_or_val σ1 he1.1 hs_r hv2 with hv1 | ⟨s1_m, hs_m, hsz, hs_rm⟩
        · have hmp := pureLetDrop_matchPat p hv1 hs_r
          rw [hm2] at hmp
          cases hm1 : matchPat p s1 <;> rw [hm1] at hmp
          · exact ⟨_, σ1, .match_ hs_r hrs, hσRel, .single (.matchMiss hv1 hm1)⟩
          · cases hmp
        · have hs_mt : Step Δ Φ1 emptyPool (.match_ s1 ((p, b1) :: r1)) σ1 (.match_ s1_m ((p, b1) :: r1)) σ1 .none :=
            .matchScrut hs_m
          rcases step_preserves_closed hΦ1cl hσCl (by simp [freeVars, he1.1, he1.2]) hs_mt with ⟨hcl_m, _⟩
          have _ : sizeOf (Expr.match_ s1_m ((p, b1) :: r1)) < sizeOf (Expr.match_ s1 ((p, b1) :: r1)) := by
            simp +arith; omega
          rcases pureLetDrop_step_backward hΦenv hΦ1cl hσCl hcl_m hσRel (.match_ hs_rm (.cons hb hrs))
            (.matchMiss hv2 hm2) with ⟨e1', σ1', hr', hσ', hsteps⟩
          exact ⟨e1', σ1', hr', hσ', .trans hs_mt hsteps⟩
  | @makeData adt tag es1 es2 hrl =>
    simp only [freeVars] at he1
    cases hs2 with
    | makeDataStep hsl2 =>
      rcases pureLetDropList_step_backward hΦenv hΦ1cl hσCl he1 hσRel hrl hsl2 with
        ⟨es1', σ1', hrl', hσ', hsteps_l⟩
      exact ⟨.makeData adt tag es1', σ1', .makeData hrl', hσ', hsteps_l (fun hsl => .makeDataStep hsl)⟩
    | makeDataTrap htr2 =>
      rcases pureLetDropList_firstTrap_right_step_or_trap σ1 he1 hrl htr2 with htr1 | ⟨es1_m, hsl_m, hsz, hrl_m⟩
      · exact ⟨.trap _, σ1, .trap _, hσRel, .single (.makeDataTrap htr1)⟩
      · have hs_md : Step Δ Φ1 emptyPool (.makeData adt tag es1) σ1 (.makeData adt tag es1_m) σ1 .none :=
          .makeDataStep hsl_m
        rcases step_preserves_closed hΦ1cl hσCl (by simpa [freeVars] using he1) hs_md with ⟨hcl_m, _⟩
        have _ : sizeOf (Expr.makeData adt tag es1_m) < sizeOf (Expr.makeData adt tag es1) := by simp +arith; omega
        rcases pureLetDrop_step_backward hΦenv hΦ1cl hσCl hcl_m hσRel (.makeData hrl_m) (.makeDataTrap htr2) with
          ⟨e1', σ1', hr', hσ', hsteps⟩
        exact ⟨e1', σ1', hr', hσ', .trans hs_md hsteps⟩
  | @getTag a1 a2 ha =>
    simp only [freeVars] at he1
    cases hs2 with
    | getTagStep hs_a2 =>
      rcases pureLetDrop_step_backward hΦenv hΦ1cl hσCl he1 hσRel ha hs_a2 with ⟨a1', σ1', ha', hσ', hsteps_a⟩
      exact ⟨.getTag a1', σ1', .getTag ha', hσ',
        Steps.liftCongr (fun u => .getTag u) (fun hs => .getTagStep hs) hsteps_a⟩
    | getTagTrap =>
      rcases pureLetDrop_trap_right_step_or_trap σ1 he1 ha with rfl | ⟨a1_m, hs_m, hsz, ha_m⟩
      · exact ⟨.trap _, σ1, .trap _, hσRel, .single .getTagTrap⟩
      · have hs_gt : Step Δ Φ1 emptyPool (.getTag a1) σ1 (.getTag a1_m) σ1 .none := .getTagStep hs_m
        rcases step_preserves_closed hΦ1cl hσCl (by simpa [freeVars] using he1) hs_gt with ⟨hcl_m, _⟩
        have _ : sizeOf (Expr.getTag a1_m) < sizeOf (Expr.getTag a1) := by simp +arith; omega
        rcases pureLetDrop_step_backward hΦenv hΦ1cl hσCl hcl_m hσRel (.getTag ha_m) .getTagTrap with
          ⟨e1', σ1', hr', hσ', hsteps⟩
        exact ⟨e1', σ1', hr', hσ', .trans hs_gt hsteps⟩
    | getTagVal hvs2 =>
      rcases pureLetDrop_val_right_step_or_val σ1 he1 ha (.makeData _ _ hvs2) with hv1 | ⟨a1_m, hs_m, hsz, ha_m⟩
      · cases ha with
        | dropPureLet _ _ _ => cases hv1
        | makeData _ =>
          cases hv1 with
          | makeData _ _ hvs1 => exact ⟨.lit _, σ1, .lit _, hσRel, .single (.getTagVal hvs1)⟩
      · have hs_gt : Step Δ Φ1 emptyPool (.getTag a1) σ1 (.getTag a1_m) σ1 .none := .getTagStep hs_m
        rcases step_preserves_closed hΦ1cl hσCl (by simpa [freeVars] using he1) hs_gt with ⟨hcl_m, _⟩
        have _ : sizeOf (Expr.getTag a1_m) < sizeOf (Expr.getTag a1) := by simp +arith; omega
        rcases pureLetDrop_step_backward hΦenv hΦ1cl hσCl hcl_m hσRel (.getTag ha_m) (.getTagVal hvs2) with
          ⟨e1', σ1', hr', hσ', hsteps⟩
        exact ⟨e1', σ1', hr', hσ', .trans hs_gt hsteps⟩
  | @cellNew a1 a2 ha =>
    simp only [freeVars] at he1
    cases hs2 with
    | cellNewStep hs_a2 =>
      rcases pureLetDrop_step_backward hΦenv hΦ1cl hσCl he1 hσRel ha hs_a2 with ⟨a1', σ1', ha', hσ', hsteps_a⟩
      exact ⟨.cellNew a1', σ1', .cellNew ha', hσ',
        Steps.liftCongr (fun u => .cellNew u) (fun hs => .cellNewStep hs) hsteps_a⟩
    | cellNewTrap =>
      rcases pureLetDrop_trap_right_step_or_trap σ1 he1 ha with rfl | ⟨a1_m, hs_m, hsz, ha_m⟩
      · exact ⟨.trap _, σ1, .trap _, hσRel, .single .cellNewTrap⟩
      · have hs_cn : Step Δ Φ1 emptyPool (.cellNew a1) σ1 (.cellNew a1_m) σ1 .none := .cellNewStep hs_m
        rcases step_preserves_closed hΦ1cl hσCl (by simpa [freeVars] using he1) hs_cn with ⟨hcl_m, _⟩
        have _ : sizeOf (Expr.cellNew a1_m) < sizeOf (Expr.cellNew a1) := by simp +arith; omega
        rcases pureLetDrop_step_backward hΦenv hΦ1cl hσCl hcl_m hσRel (.cellNew ha_m) .cellNewTrap with
          ⟨e1', σ1', hr', hσ', hsteps⟩
        exact ⟨e1', σ1', hr', hσ', .trans hs_cn hsteps⟩
    | cellNewVal hv2 =>
      rcases pureLetDrop_val_right_step_or_val σ1 he1 ha hv2 with hv1 | ⟨a1_m, hs_m, hsz, ha_m⟩
      · rw [← storeDropRel_length hσRel]
        exact ⟨.loc _, _, .loc _, storeDropRel_append hσRel ha, .single (.cellNewVal hv1)⟩
      · have hs_cn : Step Δ Φ1 emptyPool (.cellNew a1) σ1 (.cellNew a1_m) σ1 .none := .cellNewStep hs_m
        rcases step_preserves_closed hΦ1cl hσCl (by simpa [freeVars] using he1) hs_cn with ⟨hcl_m, _⟩
        have _ : sizeOf (Expr.cellNew a1_m) < sizeOf (Expr.cellNew a1) := by simp +arith; omega
        rcases pureLetDrop_step_backward hΦenv hΦ1cl hσCl hcl_m hσRel (.cellNew ha_m) (.cellNewVal hv2) with
          ⟨e1', σ1', hr', hσ', hsteps⟩
        exact ⟨e1', σ1', hr', hσ', .trans hs_cn hsteps⟩
  | @cellGet a1 a2 ha =>
    simp only [freeVars] at he1
    cases hs2 with
    | cellGetStep hs_a2 =>
      rcases pureLetDrop_step_backward hΦenv hΦ1cl hσCl he1 hσRel ha hs_a2 with ⟨a1', σ1', ha', hσ', hsteps_a⟩
      exact ⟨.cellGet a1', σ1', .cellGet ha', hσ',
        Steps.liftCongr (fun u => .cellGet u) (fun hs => .cellGetStep hs) hsteps_a⟩
    | cellGetTrap =>
      rcases pureLetDrop_trap_right_step_or_trap σ1 he1 ha with rfl | ⟨a1_m, hs_m, hsz, ha_m⟩
      · exact ⟨.trap _, σ1, .trap _, hσRel, .single .cellGetTrap⟩
      · have hs_cg : Step Δ Φ1 emptyPool (.cellGet a1) σ1 (.cellGet a1_m) σ1 .none := .cellGetStep hs_m
        rcases step_preserves_closed hΦ1cl hσCl (by simpa [freeVars] using he1) hs_cg with ⟨hcl_m, _⟩
        have _ : sizeOf (Expr.cellGet a1_m) < sizeOf (Expr.cellGet a1) := by simp +arith; omega
        rcases pureLetDrop_step_backward hΦenv hΦ1cl hσCl hcl_m hσRel (.cellGet ha_m) .cellGetTrap with
          ⟨e1', σ1', hr', hσ', hsteps⟩
        exact ⟨e1', σ1', hr', hσ', .trans hs_cg hsteps⟩
    | cellGetVal hl2 =>
      rcases pureLetDrop_val_right_step_or_val σ1 he1 ha (.loc _) with hv1 | ⟨a1_m, hs_m, hsz, ha_m⟩
      · cases ha with
        | dropPureLet _ _ _ => cases hv1
        | loc l =>
          rcases storeDropRel_getElem_right hσRel hl2 with ⟨v1, hl1, hvRel⟩
          exact ⟨v1, σ1, hvRel, hσRel, .single (.cellGetVal hl1)⟩
      · have hs_cg : Step Δ Φ1 emptyPool (.cellGet a1) σ1 (.cellGet a1_m) σ1 .none := .cellGetStep hs_m
        rcases step_preserves_closed hΦ1cl hσCl (by simpa [freeVars] using he1) hs_cg with ⟨hcl_m, _⟩
        have _ : sizeOf (Expr.cellGet a1_m) < sizeOf (Expr.cellGet a1) := by simp +arith; omega
        rcases pureLetDrop_step_backward hΦenv hΦ1cl hσCl hcl_m hσRel (.cellGet ha_m) (.cellGetVal hl2) with
          ⟨e1', σ1', hr', hσ', hsteps⟩
        exact ⟨e1', σ1', hr', hσ', .trans hs_cg hsteps⟩
  | @cellSet a1 a2 b1 b2 ha hb =>
    simp only [freeVars, List.append_eq_nil_iff] at he1
    cases hs2 with
    | cellSetLeft hs_a2 =>
      rcases pureLetDrop_step_backward hΦenv hΦ1cl hσCl he1.1 hσRel ha hs_a2 with ⟨a1', σ1', ha', hσ', hsteps_a⟩
      exact ⟨.cellSet a1' b1, σ1', .cellSet ha' hb, hσ',
        Steps.liftCongr (fun u => .cellSet u b1) (fun hs => .cellSetLeft hs) hsteps_a⟩
    | cellSetLeftTrap =>
      rcases pureLetDrop_trap_right_step_or_trap σ1 he1.1 ha with rfl | ⟨a1_m, hs_m, hsz, ha_m⟩
      · exact ⟨.trap _, σ1, .trap _, hσRel, .single .cellSetLeftTrap⟩
      · have hs_cs : Step Δ Φ1 emptyPool (.cellSet a1 b1) σ1 (.cellSet a1_m b1) σ1 .none := .cellSetLeft hs_m
        rcases step_preserves_closed hΦ1cl hσCl (by simp [freeVars, he1.1, he1.2]) hs_cs with ⟨hcl_m, _⟩
        have _ : sizeOf (Expr.cellSet a1_m b1) < sizeOf (Expr.cellSet a1 b1) := by simp +arith; omega
        rcases pureLetDrop_step_backward hΦenv hΦ1cl hσCl hcl_m hσRel (.cellSet ha_m hb) .cellSetLeftTrap with
          ⟨e1', σ1', hr', hσ', hsteps⟩
        exact ⟨e1', σ1', hr', hσ', .trans hs_cs hsteps⟩
    | cellSetRight hv2 hs_b2 =>
      rcases pureLetDrop_val_right_step_or_val σ1 he1.1 ha hv2 with hv1 | ⟨a1_m, hs_m, hsz, ha_m⟩
      · rcases pureLetDrop_step_backward hΦenv hΦ1cl hσCl he1.2 hσRel hb hs_b2 with ⟨b1', σ1', hb', hσ', hsteps_b⟩
        exact ⟨.cellSet a1 b1', σ1', .cellSet ha hb', hσ',
          Steps.liftCongr (fun u => .cellSet a1 u) (fun hs => .cellSetRight hv1 hs) hsteps_b⟩
      · have hs_cs : Step Δ Φ1 emptyPool (.cellSet a1 b1) σ1 (.cellSet a1_m b1) σ1 .none := .cellSetLeft hs_m
        rcases step_preserves_closed hΦ1cl hσCl (by simp [freeVars, he1.1, he1.2]) hs_cs with ⟨hcl_m, _⟩
        have _ : sizeOf (Expr.cellSet a1_m b1) < sizeOf (Expr.cellSet a1 b1) := by simp +arith; omega
        rcases pureLetDrop_step_backward hΦenv hΦ1cl hσCl hcl_m hσRel (.cellSet ha_m hb) (.cellSetRight hv2 hs_b2) with
          ⟨e1', σ1', hr', hσ', hsteps⟩
        exact ⟨e1', σ1', hr', hσ', .trans hs_cs hsteps⟩
    | cellSetRightTrap hv2 =>
      rcases pureLetDrop_val_right_step_or_val σ1 he1.1 ha hv2 with hv1 | ⟨a1_m, hs_m, hsz, ha_m⟩
      · rcases pureLetDrop_trap_right_step_or_trap σ1 he1.2 hb with rfl | ⟨b1_m, hs_bm, hsz, hb_m⟩
        · exact ⟨.trap _, σ1, .trap _, hσRel, .single (.cellSetRightTrap hv1)⟩
        · have hs_cs : Step Δ Φ1 emptyPool (.cellSet a1 b1) σ1 (.cellSet a1 b1_m) σ1 .none := .cellSetRight hv1 hs_bm
          rcases step_preserves_closed hΦ1cl hσCl (by simp [freeVars, he1.1, he1.2]) hs_cs with ⟨hcl_m, _⟩
          have _ : sizeOf (Expr.cellSet a1 b1_m) < sizeOf (Expr.cellSet a1 b1) := by simp +arith; omega
          rcases pureLetDrop_step_backward hΦenv hΦ1cl hσCl hcl_m hσRel (.cellSet ha hb_m) (.cellSetRightTrap hv2) with
            ⟨e1', σ1', hr', hσ', hsteps⟩
          exact ⟨e1', σ1', hr', hσ', .trans hs_cs hsteps⟩
      · have hs_cs : Step Δ Φ1 emptyPool (.cellSet a1 b1) σ1 (.cellSet a1_m b1) σ1 .none := .cellSetLeft hs_m
        rcases step_preserves_closed hΦ1cl hσCl (by simp [freeVars, he1.1, he1.2]) hs_cs with ⟨hcl_m, _⟩
        have _ : sizeOf (Expr.cellSet a1_m b1) < sizeOf (Expr.cellSet a1 b1) := by simp +arith; omega
        rcases pureLetDrop_step_backward hΦenv hΦ1cl hσCl hcl_m hσRel (.cellSet ha_m hb) (.cellSetRightTrap hv2) with
          ⟨e1', σ1', hr', hσ', hsteps⟩
        exact ⟨e1', σ1', hr', hσ', .trans hs_cs hsteps⟩
    | @cellSetVal l _ _ hlt2 hv2 =>
      rcases pureLetDrop_val_right_step_or_val σ1 he1.1 ha (.loc _) with hv1 | ⟨a1_m, hs_m, hsz, ha_m⟩
      · rcases pureLetDrop_val_right_step_or_val σ1 he1.2 hb hv2 with hvb1 | ⟨b1_m, hs_bm, hsz, hb_m⟩
        · cases ha with
          | dropPureLet _ _ _ => cases hv1
          | loc _ =>
            have hlt1 : l < σ1.length := by rwa [storeDropRel_length hσRel]
            exact ⟨.lit .unit, _, .lit .unit, storeDropRel_set hσRel l hb,
              .single (.cellSetVal hlt1 hvb1)⟩
        · have hs_cs : Step Δ Φ1 emptyPool (.cellSet a1 b1) σ1 (.cellSet a1 b1_m) σ1 .none := .cellSetRight hv1 hs_bm
          rcases step_preserves_closed hΦ1cl hσCl (by simp [freeVars, he1.1, he1.2]) hs_cs with ⟨hcl_m, _⟩
          have _ : sizeOf (Expr.cellSet a1 b1_m) < sizeOf (Expr.cellSet a1 b1) := by simp +arith; omega
          rcases pureLetDrop_step_backward hΦenv hΦ1cl hσCl hcl_m hσRel (.cellSet ha hb_m) (.cellSetVal hlt2 hv2) with
            ⟨e1', σ1', hr', hσ', hsteps⟩
          exact ⟨e1', σ1', hr', hσ', .trans hs_cs hsteps⟩
      · have hs_cs : Step Δ Φ1 emptyPool (.cellSet a1 b1) σ1 (.cellSet a1_m b1) σ1 .none := .cellSetLeft hs_m
        rcases step_preserves_closed hΦ1cl hσCl (by simp [freeVars, he1.1, he1.2]) hs_cs with ⟨hcl_m, _⟩
        have _ : sizeOf (Expr.cellSet a1_m b1) < sizeOf (Expr.cellSet a1 b1) := by simp +arith; omega
        rcases pureLetDrop_step_backward hΦenv hΦ1cl hσCl hcl_m hσRel (.cellSet ha_m hb) (.cellSetVal hlt2 hv2) with
          ⟨e1', σ1', hr', hσ', hsteps⟩
        exact ⟨e1', σ1', hr', hσ', .trans hs_cs hsteps⟩
  | @spawn a1 a2 ha =>
    simp only [freeVars] at he1
    cases hs2 with
    | spawnStep hs_a2 =>
      rcases pureLetDrop_step_backward hΦenv hΦ1cl hσCl he1 hσRel ha hs_a2 with ⟨a1', σ1', ha', hσ', hsteps_a⟩
      exact ⟨.spawn a1', σ1', .spawn ha', hσ',
        Steps.liftCongr (fun u => .spawn u) (fun hs => .spawnStep hs) hsteps_a⟩
    | spawnTrap =>
      rcases pureLetDrop_trap_right_step_or_trap σ1 he1 ha with rfl | ⟨a1_m, hs_m, hsz, ha_m⟩
      · exact ⟨.trap _, σ1, .trap _, hσRel, .single .spawnTrap⟩
      · have hs_sp : Step Δ Φ1 emptyPool (.spawn a1) σ1 (.spawn a1_m) σ1 .none := .spawnStep hs_m
        rcases step_preserves_closed hΦ1cl hσCl (by simpa [freeVars] using he1) hs_sp with ⟨hcl_m, _⟩
        have _ : sizeOf (Expr.spawn a1_m) < sizeOf (Expr.spawn a1) := by simp +arith; omega
        rcases pureLetDrop_step_backward hΦenv hΦ1cl hσCl hcl_m hσRel (.spawn ha_m) .spawnTrap with
          ⟨e1', σ1', hr', hσ', hsteps⟩
        exact ⟨e1', σ1', hr', hσ', .trans hs_sp hsteps⟩
  | @await a1 a2 ha =>
    simp only [freeVars] at he1
    cases hs2 with
    | awaitStep hs_a2 =>
      rcases pureLetDrop_step_backward hΦenv hΦ1cl hσCl he1 hσRel ha hs_a2 with ⟨a1', σ1', ha', hσ', hsteps_a⟩
      exact ⟨.await a1', σ1', .await ha', hσ',
        Steps.liftCongr (fun u => .await u) (fun hs => .awaitStep hs) hsteps_a⟩
    | awaitTrap =>
      rcases pureLetDrop_trap_right_step_or_trap σ1 he1 ha with rfl | ⟨a1_m, hs_m, hsz, ha_m⟩
      · exact ⟨.trap _, σ1, .trap _, hσRel, .single .awaitTrap⟩
      · have hs_aw : Step Δ Φ1 emptyPool (.await a1) σ1 (.await a1_m) σ1 .none := .awaitStep hs_m
        rcases step_preserves_closed hΦ1cl hσCl (by simpa [freeVars] using he1) hs_aw with ⟨hcl_m, _⟩
        have _ : sizeOf (Expr.await a1_m) < sizeOf (Expr.await a1) := by simp +arith; omega
        rcases pureLetDrop_step_backward hΦenv hΦ1cl hσCl hcl_m hσRel (.await ha_m) .awaitTrap with
          ⟨e1', σ1', hr', hσ', hsteps⟩
        exact ⟨e1', σ1', hr', hσ', .trans hs_aw hsteps⟩
    | awaitVal h _ | awaitTaskTrap h => simp [emptyPool] at h
  | @concPrim op es1 es2 hrl =>
    simp only [freeVars] at he1
    cases hs2 with
    | concPrimArgs hsl2 =>
      rcases pureLetDropList_step_backward hΦenv hΦ1cl hσCl he1 hσRel hrl hsl2 with
        ⟨es1', σ1', hrl', hσ', hsteps_l⟩
      exact ⟨.concPrim op es1', σ1', .concPrim hrl', hσ', hsteps_l (fun hsl => .concPrimArgs hsl)⟩
    | concPrimTrap htr2 =>
      rcases pureLetDropList_firstTrap_right_step_or_trap σ1 he1 hrl htr2 with htr1 | ⟨es1_m, hsl_m, hsz, hrl_m⟩
      · exact ⟨.trap _, σ1, .trap _, hσRel, .single (.concPrimTrap htr1)⟩
      · have hs_cp : Step Δ Φ1 emptyPool (.concPrim op es1) σ1 (.concPrim op es1_m) σ1 .none := .concPrimArgs hsl_m
        rcases step_preserves_closed hΦ1cl hσCl (by simpa [freeVars] using he1) hs_cp with ⟨hcl_m, _⟩
        have _ : sizeOf (Expr.concPrim op es1_m) < sizeOf (Expr.concPrim op es1) := by simp +arith; omega
        rcases pureLetDrop_step_backward hΦenv hΦ1cl hσCl hcl_m hσRel (.concPrim hrl_m) (.concPrimTrap htr2) with
          ⟨e1', σ1', hr', hσ', hsteps⟩
        exact ⟨e1', σ1', hr', hσ', .trans hs_cp hsteps⟩
    | concPrimVal hc => exact False.elim (stepConcPrim_emptyPool_none_false hc)
termination_by sizeOf e1
decreasing_by
  all_goals (subst_vars; simp_wf; (try simp +arith); try omega)

theorem pureLetDropList_step_backward {Δ : AdtEnv} {Φ1 Φ2 : FunEnv}
    (hΦenv : PureLetDropEnv Φ1 Φ2) (hΦ1cl : ClosedFunEnv Φ1)
    {es1 es2 es2' : List Expr} {σ1 σ2 σ2' : Store}
    (hσCl : ClosedStore σ1) (hes1 : freeVarsList es1 = [])
    (hσRel : StoreDropRel σ1 σ2)
    (hrl : PureLetDropRelList es1 es2)
    (hsl2 : StepList Δ Φ2 emptyPool es2 σ2 es2' σ2' .none) :
    ∃ es1' σ1', PureLetDropRelList es1' es2' ∧ StoreDropRel σ1' σ2' ∧
      (∀ {F : List Expr → Expr},
        (∀ {l1 l1' : List Expr} {s s' : Store},
          StepList Δ Φ1 emptyPool l1 s l1' s' .none → Step Δ Φ1 emptyPool (F l1) s (F l1') s' .none) →
        Steps Δ Φ1 (F es1) σ1 (F es1') σ1') := by
  cases hrl with
  | nil => cases hsl2
  | @cons a1 a2 r1 r2 hr hrs =>
    simp only [freeVarsList, List.append_eq_nil_iff] at hes1
    cases hsl2 with
    | head hs_a2 =>
      rcases pureLetDrop_step_backward hΦenv hΦ1cl hσCl hes1.1 hσRel hr hs_a2 with ⟨a1', σ1', hr', hσ', hsteps_a⟩
      refine ⟨a1' :: r1, σ1', .cons hr' hrs, hσ', ?_⟩
      intro F hF
      exact Steps.liftCongr (fun x => F (x :: r1)) (fun hs => hF (.head hs)) hsteps_a
    | tail hv2 hsl_r2 =>
      rcases pureLetDrop_val_right_step_or_val σ1 hes1.1 hr hv2 with hv1 | ⟨a1_m, hs_m, hsz, hr_m⟩
      · rcases pureLetDropList_step_backward hΦenv hΦ1cl hσCl hes1.2 hσRel hrs hsl_r2 with
          ⟨r1', σ1', hrs', hσ', hsteps_r⟩
        refine ⟨a1 :: r1', σ1', .cons hr hrs', hσ', ?_⟩
        intro F hF
        exact hsteps_r (F := fun l => F (a1 :: l)) (fun hsl => hF (.tail hv1 hsl))
      · rcases step_preserves_closed hΦ1cl hσCl hes1.1 hs_m with ⟨hcl_am, _⟩
        have _ : sizeOf (a1_m :: r1) < sizeOf (a1 :: r1) := by simp +arith; omega
        rcases pureLetDropList_step_backward hΦenv hΦ1cl hσCl
          (by simp [freeVarsList, hcl_am, hes1.2]) hσRel (.cons hr_m hrs) (.tail hv2 hsl_r2) with
          ⟨es1', σ1', hrl', hσ', hsteps_rest⟩
        refine ⟨es1', σ1', hrl', hσ', ?_⟩
        intro F hF
        exact .trans (hF (.head hs_m)) (hsteps_rest hF)
termination_by sizeOf es1
decreasing_by
  all_goals (subst_vars; simp_wf; (try simp +arith); try omega)
end

theorem pureLetDrop_steps_backward {Δ : AdtEnv} {Φ1 Φ2 : FunEnv}
    (hΦenv : PureLetDropEnv Φ1 Φ2) (hΦ1cl : ClosedFunEnv Φ1)
    {e1 e2 e2' : Expr} {σ1 σ2 σ2' : Store}
    (hσCl : ClosedStore σ1) (he1 : freeVars e1 = [])
    (hσRel : StoreDropRel σ1 σ2) (hr : PureLetDropRel e1 e2)
    (hsteps2 : Steps Δ Φ2 e2 σ2 e2' σ2') :
    ∃ e1' σ1', PureLetDropRel e1' e2' ∧ StoreDropRel σ1' σ2' ∧
      freeVars e1' = [] ∧ ClosedStore σ1' ∧ Steps Δ Φ1 e1 σ1 e1' σ1' := by
  induction hsteps2 generalizing e1 σ1 with
  | refl => exact ⟨e1, σ1, hr, hσRel, he1, hσCl, .refl _ _⟩
  | trans hs2 _ ih =>
    rcases pureLetDrop_step_backward hΦenv hΦ1cl hσCl he1 hσRel hr hs2 with ⟨e1_m, σ1_m, hr_m, hσ_m, hsteps1_m⟩
    rcases steps_preserves_closed hΦ1cl hσCl he1 hsteps1_m with ⟨he1_m, hσCl_m⟩
    rcases ih hσCl_m he1_m hσ_m hr_m with ⟨e1', σ1', hr', hσ', he1', hσCl', hsteps1_rest⟩
    exact ⟨e1', σ1', hr', hσ', he1', hσCl', Steps.append hsteps1_m hsteps1_rest⟩

/-- **Main Higher-Order Contextual Soundness (`pureLetDrop_implies_ctxObsEquiv`)**:
    Any open expression rewrite in `PureLetDropRel` (eliminating dead pure/variable/closure/tuple/ADT
    `let` bindings anywhere in an expression, **including inside `.lam` bodies** and across top-level
    function tables `PureLetDropEnv Φ1 Φ2`) establishes full contextual equivalence `CtxObsEquiv`! -/
theorem pureLetDrop_implies_ctxObsEquiv {Γ : List Ident} {Δ : AdtEnv} {Φ1 Φ2 : FunEnv}
    (hΦenv : PureLetDropEnv Φ1 Φ2) (hΦ1cl : ClosedFunEnv Φ1)
    {e1 e2 : Expr} (hΓ1 : ∀ z ∈ freeVars e1, z ∈ Γ)
    (hr : PureLetDropRel e1 e2) :
    CtxObsEquiv Γ Δ Φ1 Φ2 e1 e2 := by
  have hΓ2 : ∀ z ∈ freeVars e2, z ∈ Γ :=
    fun z hz => hΓ1 z (pureLetDrop_freeVars_subset hr z hz)
  refine ⟨hΓ1, hΓ2, ?_⟩
  intro C σ out hC hσ _ hout
  have hcl1 : freeVars (C.fill e1) = [] := hC e1 hΓ1
  have hrC : PureLetDropRel (C.fill e1) (C.fill e2) := exprCtx_pureLetDrop_congr C hr
  constructor
  · rintro ⟨σ1', hsteps1⟩
    rcases pureLetDrop_steps_forward hΦenv hΦ1cl hσ hcl1 (StoreDropRel.refl σ) hrC hsteps1 with
      ⟨e2', σ2', hr', _, hsteps2⟩
    rcases hout with hg | ⟨t, rfl⟩
    · rw [← pureLetDrop_ground_left hr' hg] at hsteps2
      exact ⟨σ2', hsteps2⟩
    · rw [pureLetDrop_trap_left hr'] at hsteps2
      exact ⟨σ2', hsteps2⟩
  · rintro ⟨σ2', hsteps2⟩
    rcases pureLetDrop_steps_backward hΦenv hΦ1cl hσ hcl1 (StoreDropRel.refl σ) hrC hsteps2 with
      ⟨e1', σ1', hr', _, he1', hσ1', hsteps1⟩
    rcases hout with hg | ⟨t, rfl⟩
    · rcases pureLetDrop_val_right_steps hΦ1cl hσ1' he1' hr' (isGroundValue_isValue hg) with
        ⟨v1, hvSteps, hv1, hrv⟩
      rw [pureLetDrop_isValue_ground_right hv1 hrv hg] at hvSteps
      exact ⟨σ1', Steps.append hsteps1 hvSteps⟩
    · exact ⟨σ1', Steps.append hsteps1 (pureLetDrop_trap_right_steps hΦ1cl hσ1' he1' hr')⟩

/-- **Returned-Closure Positive Witness (`returned_closure_dead_let_ctxObsEquiv`)**:
    Whereas `() => { let unused = (); 1 }` and `() => 1` fail raw syntactic `ObsEquiv`
    (`obsEquiv_not_lam_congr_counterexample`), they satisfy full `CtxObsEquiv []` across
    all closing contexts `C`, and invoking either returned closure evaluates to `1`! -/
theorem returned_closure_dead_let_ctxObsEquiv :
    let cls1 : Expr := .lam .local [] .int (.let_ "unused" (.lit .unit) (.lit (.int 1)))
    let cls2 : Expr := .lam .local [] .int (.lit (.int 1))
    CtxObsEquiv [] (fun _ => none) (fun _ => none) (fun _ => none) cls1 cls2 ∧
    Steps (fun _ => none) (fun _ => none) (.apply cls1 []) [] (.lit (.int 1)) [] ∧
    Steps (fun _ => none) (fun _ => none) (.apply cls2 []) [] (.lit (.int 1)) [] := by
  let cls1 : Expr := .lam .local [] .int (.let_ "unused" (.lit .unit) (.lit (.int 1)))
  let cls2 : Expr := .lam .local [] .int (.lit (.int 1))
  have hctx : CtxObsEquiv [] (fun _ => none) (fun _ => none) (fun _ => none) cls1 cls2 :=
    pureLetDrop_implies_ctxObsEquiv (PureLetDropEnv.refl _) (fun _ _ h => by cases h)
      (by simp [cls1, freeVars])
      (.lam (.dropPureLet (.lit .unit) (by decide) (.lit (.int 1))))
  have hs1 : Steps (fun _ => none) (fun _ => none) (.apply cls1 []) [] (.lit (.int 1)) [] :=
    .trans (.applyBeta (fun _ h => by cases h) rfl) (.single (.letVal (.lit .unit)))
  have hs2 : Steps (fun _ => none) (fun _ => none) (.apply cls2 []) [] (.lit (.int 1)) [] :=
    .single (.applyBeta (fun _ h => by cases h) rfl)
  exact ⟨hctx, hs1, hs2⟩


/-! ## Part 10: Real-Artifact Alpha/Wrapper/Multi-Callback Bridge, `CoEnv` Match State & Interface-Scoped `ScopedCtxObsEquiv` -/

/-! ### 10.1 Active Evaluation Contexts & Recursive Function-Body `ObsEquiv` Congruence (`recFunBody_obsEquiv_congr`) -/

/-- General 1-hole deterministic active evaluation context `K : Expr → Expr`. -/
structure IsActiveCtx (Δ : AdtEnv) (K : Expr → Expr) : Prop where
  notTerm : ∀ {x : Expr}, ¬ IsTerminal x → ¬ IsTerminal (K x)
  step    : ∀ {Φ : FunEnv} {a a' : Expr} {s s' : Store},
              Step Δ Φ emptyPool a s a' s' .none → Step Δ Φ emptyPool (K a) s (K a') s' .none
  invert  : ∀ {Φ : FunEnv} {x y : Expr} {s s' : Store},
              ¬ IsTerminal x → Step Δ Φ emptyPool (K x) s y s' .none →
              ∃ x', y = K x' ∧ Step Δ Φ emptyPool x s x' s' .none
  trap    : ∀ (Φ : FunEnv) (t : Trap) (s : Store), Steps Δ Φ (K (.trap t)) s (.trap t) s
  fvSub   : ∀ (x : Expr) (z : Ident), z ∈ freeVars x → z ∈ freeVars (K x)

theorem IsActiveCtx.id (Δ : AdtEnv) : IsActiveCtx Δ (fun x => x) where
  notTerm h := h
  step hs := hs
  invert _ hs := ⟨_, rfl, hs⟩
  trap _ t s := .refl (.trap t) s
  fvSub _ _ hz := hz

theorem IsActiveCtx.comp {Δ : AdtEnv} {K1 K2 : Expr → Expr}
    (h1 : IsActiveCtx Δ K1) (h2 : IsActiveCtx Δ K2) :
    IsActiveCtx Δ (fun x => K1 (K2 x)) where
  notTerm hnt := h1.notTerm (h2.notTerm hnt)
  step hs := h1.step (h2.step hs)
  invert hnt hs := by
    rcases h1.invert (h2.notTerm hnt) hs with ⟨m, rfl, hsm⟩
    rcases h2.invert hnt hsm with ⟨x', rfl, hsx⟩
    exact ⟨x', rfl, hsx⟩
  trap Φ t s :=
    Steps.append (Steps.liftCongr K1 h1.step (h2.trap Φ t s)) (h1.trap Φ t s)
  fvSub x z hz := h1.fvSub (K2 x) z (h2.fvSub x z hz)

theorem activeCtx_steps_terminal_iff {Δ : AdtEnv} {Φ : FunEnv} {K : Expr → Expr}
    (hK : IsActiveCtx Δ K) {x out : Expr} {s s' : Store} (hout : IsTerminal out) :
    Steps Δ Φ (K x) s out s' ↔
      (∃ t, out = .trap t ∧ Steps Δ Φ x s (.trap t) s') ∨
      (∃ v sm, IsValue v ∧ Steps Δ Φ x s v sm ∧ Steps Δ Φ (K v) sm out s') := by
  constructor
  · intro h
    generalize heq : K x = kx at h
    induction h generalizing x with
    | refl =>
      rename_i _ s0
      subst heq
      by_cases htx : IsTerminal x
      · rcases htx with hv | ⟨t, rfl⟩
        · exact Or.inr ⟨x, s0, hv, .refl _ _, .refl _ _⟩
        · rcases steps_terminal_det (Steps.refl (K (.trap t)) s0) hout (hK.trap Φ t s0) (Or.inr ⟨t, rfl⟩) with ⟨hout_eq, _⟩
          exact Or.inl ⟨t, hout_eq, .refl _ _⟩
      · exact False.elim (hK.notTerm htx hout)
    | trans hs hrest ih =>
      rename_i _ _ out0 s0 _ _
      subst heq
      by_cases htx : IsTerminal x
      · rcases htx with hv | ⟨t, rfl⟩
        · exact Or.inr ⟨x, s0, hv, .refl _ _, .trans hs hrest⟩
        · rcases steps_terminal_det (.trans hs hrest) hout (hK.trap Φ t s0) (Or.inr ⟨t, rfl⟩) with ⟨hout_eq, hs_eq⟩
          subst hs_eq
          exact Or.inl ⟨t, hout_eq, .refl _ _⟩
      · rcases hK.invert htx hs with ⟨x', rfl, hsx⟩
        rcases ih hout rfl with ⟨t, rfl, htr⟩ | ⟨v, sm, hv, hsv, hkv⟩
        · exact Or.inl ⟨t, rfl, .trans hsx htr⟩
        · exact Or.inr ⟨v, sm, hv, .trans hsx hsv, hkv⟩
  · rintro (⟨t, rfl, htr⟩ | ⟨v, sm, hv, hsv, hkv⟩)
    · exact Steps.append (Steps.liftCongr K hK.step htr) (hK.trap Φ t s')
    · exact Steps.append (Steps.liftCongr K hK.step hsv) hkv

/-- Observational equivalence on closed heaps (`ClosedStore σ`, preserved across all `Steps`
    under `ClosedFunEnv Φ`). Required for binder α-renaming so `cellGet` never yields open closures. -/
def ClosedObsEquiv (Δ : AdtEnv) (Φ1 Φ2 : FunEnv) (e1 e2 : Expr) : Prop :=
  ∀ σ σ' out, ClosedStore σ → IsTerminal out →
    (Steps Δ Φ1 e1 σ out σ' ↔ Steps Δ Φ2 e2 σ out σ')

theorem ClosedObsEquiv.of_obsEquiv {Δ : AdtEnv} {Φ1 Φ2 : FunEnv} {e1 e2 : Expr}
    (h : ObsEquiv Δ Φ1 Φ2 e1 e2) : ClosedObsEquiv Δ Φ1 Φ2 e1 e2 :=
  fun σ σ' out _ hout => h σ σ' out hout

theorem ClosedObsEquiv.refl (Δ : AdtEnv) (Φ : FunEnv) (e : Expr) : ClosedObsEquiv Δ Φ Φ e e :=
  fun _ _ _ _ _ => Iff.rfl

theorem ClosedObsEquiv.symm {Δ : AdtEnv} {Φ1 Φ2 : FunEnv} {e1 e2 : Expr}
    (h : ClosedObsEquiv Δ Φ1 Φ2 e1 e2) : ClosedObsEquiv Δ Φ2 Φ1 e2 e1 :=
  fun σ σ' out hσ hout => (h σ σ' out hσ hout).symm

theorem ClosedObsEquiv.trans {Δ : AdtEnv} {Φ1 Φ2 Φ3 : FunEnv} {e1 e2 e3 : Expr}
    (h12 : ClosedObsEquiv Δ Φ1 Φ2 e1 e2) (h23 : ClosedObsEquiv Δ Φ2 Φ3 e2 e3) :
    ClosedObsEquiv Δ Φ1 Φ3 e1 e3 :=
  fun σ σ' out hσ hout => (h12 σ σ' out hσ hout).trans (h23 σ σ' out hσ hout)

theorem activeCtx_closedObsEquiv_congr {Δ : AdtEnv} {Φ : FunEnv} {K : Expr → Expr}
    (hK : IsActiveCtx Δ K) {e1 e2 : Expr} (heq : ClosedObsEquiv Δ Φ Φ e1 e2) :
    ClosedObsEquiv Δ Φ Φ (K e1) (K e2) := by
  intro s s' out hs hout
  rw [activeCtx_steps_terminal_iff hK hout, activeCtx_steps_terminal_iff hK hout]
  constructor
  · rintro (⟨t, rfl, htr⟩ | ⟨v, sm, hv, hsv, hkv⟩)
    · exact Or.inl ⟨t, rfl, (heq s s' (.trap t) hs (Or.inr ⟨t, rfl⟩)).mp htr⟩
    · exact Or.inr ⟨v, sm, hv, (heq s sm v hs (Or.inl hv)).mp hsv, hkv⟩
  · rintro (⟨t, rfl, htr⟩ | ⟨v, sm, hv, hsv, hkv⟩)
    · exact Or.inl ⟨t, rfl, (heq s s' (.trap t) hs (Or.inr ⟨t, rfl⟩)).mpr htr⟩
    · exact Or.inr ⟨v, sm, hv, (heq s sm v hs (Or.inl hv)).mpr hsv, hkv⟩

theorem activeCtx_obsEquiv_congr {Δ : AdtEnv} {Φ : FunEnv} {K : Expr → Expr}
    (hK : IsActiveCtx Δ K) {e1 e2 : Expr} (heq : ObsEquiv Δ Φ Φ e1 e2) :
    ObsEquiv Δ Φ Φ (K e1) (K e2) := by
  intro s s' out hout
  rw [activeCtx_steps_terminal_iff hK hout, activeCtx_steps_terminal_iff hK hout]
  constructor
  · rintro (⟨t, rfl, htr⟩ | ⟨v, sm, hv, hsv, hkv⟩)
    · exact Or.inl ⟨t, rfl, (heq s s' (.trap t) (Or.inr ⟨t, rfl⟩)).mp htr⟩
    · exact Or.inr ⟨v, sm, hv, (heq s sm v (Or.inl hv)).mp hsv, hkv⟩
  · rintro (⟨t, rfl, htr⟩ | ⟨v, sm, hv, hsv, hkv⟩)
    · exact Or.inl ⟨t, rfl, (heq s s' (.trap t) (Or.inr ⟨t, rfl⟩)).mpr htr⟩
    · exact Or.inr ⟨v, sm, hv, (heq s sm v (Or.inl hv)).mpr hsv, hkv⟩

private theorem stepList_vals_mid {Δ : AdtEnv} {Φ : FunEnv}
    {vs : List Expr} (hvs : ∀ v ∈ vs, IsValue v) {a a' : Expr} (rest : List Expr) {s s' : Store}
    (hs : Step Δ Φ emptyPool a s a' s' .none) :
    StepList Δ Φ emptyPool (vs ++ a :: rest) s (vs ++ a' :: rest) s' .none := by
  induction vs with
  | nil => exact .head hs
  | cons v vr ih =>
    exact .tail (hvs v (List.mem_cons_self ..)) (ih (fun w hw => hvs w (List.mem_cons_of_mem _ hw)))

private theorem stepList_vals_mid_inv {Δ : AdtEnv} {Φ : FunEnv}
    {vs : List Expr} (hvs : ∀ v ∈ vs, IsValue v) {x : Expr} {rest ys : List Expr} {s s' : Store}
    (hnt : ¬ IsTerminal x)
    (hsl : StepList Δ Φ emptyPool (vs ++ x :: rest) s ys s' .none) :
    ∃ x', ys = vs ++ x' :: rest ∧ Step Δ Φ emptyPool x s x' s' .none := by
  induction vs generalizing ys with
  | nil =>
    cases hsl with
    | head hs => exact ⟨_, rfl, hs⟩
    | tail hv _ => exact False.elim (hnt (Or.inl hv))
  | cons v vr ih =>
    cases hsl with
    | head hs => exact False.elim (isValue_no_step (hvs v (List.mem_cons_self ..)) hs)
    | tail _ hsl' =>
      rcases ih (fun w hw => hvs w (List.mem_cons_of_mem _ hw)) hsl' with ⟨x', rfl, hsx⟩
      exact ⟨x', rfl, hsx⟩

private theorem listFirstTrap_vals_mid {vs : List Expr} (hvs : ∀ v ∈ vs, IsValue v)
    (t : Trap) (rest : List Expr) : ListFirstTrap (vs ++ .trap t :: rest) t := by
  induction vs with
  | nil => exact .head t rest
  | cons v vr ih =>
    exact .tail (hvs v (List.mem_cons_self ..)) (ih (fun w hw => hvs w (List.mem_cons_of_mem _ hw)))

private theorem listFirstTrap_vals_mid_false {vs : List Expr} (hvs : ∀ v ∈ vs, IsValue v)
    {x : Expr} {rest : List Expr} {t : Trap} (hnt : ¬ IsTerminal x)
    (htr : ListFirstTrap (vs ++ x :: rest) t) : False := by
  induction vs with
  | nil =>
    cases htr with
    | head _ _ => exact hnt (Or.inr ⟨t, rfl⟩)
    | tail hv _ => exact hnt (Or.inl hv)
  | cons v vr ih =>
    cases htr with
    | head _ _ => cases hvs (.trap _) (List.mem_cons_self ..)
    | tail _ htr' => exact ih (fun w hw => hvs w (List.mem_cons_of_mem _ hw)) htr'

private theorem mem_freeVarsList_mid (vs : List Expr) (x : Expr) (rest : List Expr)
    {z : Ident} (hz : z ∈ freeVars x) : z ∈ freeVarsList (vs ++ x :: rest) := by
  induction vs with
  | nil => simp [freeVarsList, hz]
  | cons _ vr ih => simp [freeVarsList, ih]

private theorem isActiveCtx_tupleElem (Δ : AdtEnv) {vs : List Expr} (hvs : ∀ v ∈ vs, IsValue v)
    (rest : List Expr) : IsActiveCtx Δ (fun x => .tuple (vs ++ x :: rest)) where
  notTerm hnt ht := by
    rcases ht with hv | ⟨_, htr⟩
    · cases hv with | tuple hall => exact hnt (Or.inl (hall _ (by simp)))
    · cases htr
  step hs := .tupleStep (stepList_vals_mid hvs rest hs)
  invert hnt hs := by
    cases hs with
    | tupleStep hsl =>
      rcases stepList_vals_mid_inv hvs hnt hsl with ⟨x', rfl, hsx⟩
      exact ⟨x', rfl, hsx⟩
    | tupleTrap htr => exact False.elim (listFirstTrap_vals_mid_false hvs hnt htr)
  trap _ t s := .single (.tupleTrap (listFirstTrap_vals_mid hvs t rest))
  fvSub x z hz := by simp [freeVars, mem_freeVarsList_mid vs x rest hz]

private theorem isActiveCtx_makeDataElem (Δ : AdtEnv) (adt : Ident) (tag : Nat)
    {vs : List Expr} (hvs : ∀ v ∈ vs, IsValue v) (rest : List Expr) :
    IsActiveCtx Δ (fun x => .makeData adt tag (vs ++ x :: rest)) where
  notTerm hnt ht := by
    rcases ht with hv | ⟨_, htr⟩
    · cases hv with | makeData _ _ hall => exact hnt (Or.inl (hall _ (by simp)))
    · cases htr
  step hs := .makeDataStep (stepList_vals_mid hvs rest hs)
  invert hnt hs := by
    cases hs with
    | makeDataStep hsl =>
      rcases stepList_vals_mid_inv hvs hnt hsl with ⟨x', rfl, hsx⟩
      exact ⟨x', rfl, hsx⟩
    | makeDataTrap htr => exact False.elim (listFirstTrap_vals_mid_false hvs hnt htr)
  trap _ t s := .single (.makeDataTrap (listFirstTrap_vals_mid hvs t rest))
  fvSub x z hz := by simp [freeVars, mem_freeVarsList_mid vs x rest hz]

private theorem isActiveCtx_applyFn (Δ : AdtEnv) (args : List Expr) :
    IsActiveCtx Δ (fun x => .apply x args) where
  notTerm _ ht := by
    cases ht with
    | inl hv => cases hv
    | inr htr => rcases htr with ⟨_, h⟩; cases h
  step hs := .applyFn hs
  invert hnt hs := by
    cases hs with
    | applyFn hs1 => exact ⟨_, rfl, hs1⟩
    | applyFnTrap => exact False.elim (hnt (Or.inr ⟨_, rfl⟩))
    | applyArgs hv _ => exact False.elim (hnt (Or.inl hv))
    | applyArgsTrap hv _ => exact False.elim (hnt (Or.inl hv))
    | applyBeta _ _ => exact False.elim (hnt (Or.inl (.lam _ _ _ _)))
  trap _ _ s := .single .applyFnTrap
  fvSub _ _ hz := by simp [freeVars, hz]

private theorem isActiveCtx_applyArg (Δ : AdtEnv) {vf : Expr} (hvf : IsValue vf)
    {vs : List Expr} (hvs : ∀ v ∈ vs, IsValue v) (rest : List Expr) :
    IsActiveCtx Δ (fun x => .apply vf (vs ++ x :: rest)) where
  notTerm _ ht := by
    cases ht with
    | inl hv => cases hv
    | inr htr => rcases htr with ⟨_, h⟩; cases h
  step hs := .applyArgs hvf (stepList_vals_mid hvs rest hs)
  invert hnt hs := by
    cases hs with
    | applyFn hsf => exact False.elim (isValue_no_step hvf hsf)
    | applyFnTrap => cases hvf
    | applyArgs _ hsl =>
      rcases stepList_vals_mid_inv hvs hnt hsl with ⟨x', rfl, hsx⟩
      exact ⟨x', rfl, hsx⟩
    | applyArgsTrap _ htr => exact False.elim (listFirstTrap_vals_mid_false hvs hnt htr)
    | applyBeta hall _ => exact False.elim (hnt (Or.inl (hall _ (by simp))))
  trap _ t s := .single (.applyArgsTrap hvf (listFirstTrap_vals_mid hvs t rest))
  fvSub x z hz := by simp [freeVars, mem_freeVarsList_mid vs x rest hz]

private theorem isActiveCtx_applyDirArg (Δ : AdtEnv) (nm : Ident)
    {vs : List Expr} (hvs : ∀ v ∈ vs, IsValue v) (rest : List Expr) :
    IsActiveCtx Δ (fun x => .applyDir nm (vs ++ x :: rest)) where
  notTerm _ ht := by
    cases ht with
    | inl hv => cases hv
    | inr htr => rcases htr with ⟨_, h⟩; cases h
  step hs := .applyDirArgs (stepList_vals_mid hvs rest hs)
  invert hnt hs := by
    cases hs with
    | applyDirArgs hsl =>
      rcases stepList_vals_mid_inv hvs hnt hsl with ⟨x', rfl, hsx⟩
      exact ⟨x', rfl, hsx⟩
    | applyDirTrap htr => exact False.elim (listFirstTrap_vals_mid_false hvs hnt htr)
    | applyDirBeta _ hall _ => exact False.elim (hnt (Or.inl (hall _ (by simp))))
  trap _ t s := .single (.applyDirTrap (listFirstTrap_vals_mid hvs t rest))
  fvSub x z hz := by simp [freeVars, mem_freeVarsList_mid vs x rest hz]

private theorem isActiveCtx_concPrimElem (Δ : AdtEnv) (op : ConcPrim)
    {vs : List Expr} (hvs : ∀ v ∈ vs, IsValue v) (rest : List Expr) :
    IsActiveCtx Δ (fun x => .concPrim op (vs ++ x :: rest)) where
  notTerm _ ht := by
    cases ht with
    | inl hv => cases hv
    | inr htr => rcases htr with ⟨_, h⟩; cases h
  step hs := .concPrimArgs (stepList_vals_mid hvs rest hs)
  invert hnt hs := by
    cases hs with
    | concPrimArgs hsl =>
      rcases stepList_vals_mid_inv hvs hnt hsl with ⟨x', rfl, hsx⟩
      exact ⟨x', rfl, hsx⟩
    | concPrimTrap htr => exact False.elim (listFirstTrap_vals_mid_false hvs hnt htr)
    | concPrimVal hc => exact False.elim (stepConcPrim_emptyPool_none_false hc)
  trap _ t s := .single (.concPrimTrap (listFirstTrap_vals_mid hvs t rest))
  fvSub x z hz := by simp [freeVars, mem_freeVarsList_mid vs x rest hz]

private theorem isActiveCtx_blockHead (Δ : AdtEnv) (e2 : Expr) (es : List Expr) :
    IsActiveCtx Δ (fun x => .block (x :: e2 :: es)) where
  notTerm _ ht := by
    cases ht with
    | inl hv => cases hv
    | inr htr => rcases htr with ⟨_, h⟩; cases h
  step hs := .blockConsStep hs
  invert hnt hs := by
    cases hs with
    | blockConsStep hs1 => exact ⟨_, rfl, hs1⟩
    | blockConsVal hv => exact False.elim (hnt (Or.inl hv))
    | blockConsTrap => exact False.elim (hnt (Or.inr ⟨_, rfl⟩))
  trap _ _ s := .single .blockConsTrap
  fvSub _ _ hz := by simp [freeVars, freeVarsList, hz]

private theorem isActiveCtx_un (Δ : AdtEnv) (op : UnOp) :
    IsActiveCtx Δ (fun x => .un op x) where
  notTerm _ ht := by
    cases ht with
    | inl hv => cases hv
    | inr htr => rcases htr with ⟨_, h⟩; cases h
  step hs := .unStep hs
  invert hnt hs := by
    cases hs with
    | unStep hs1 => exact ⟨_, rfl, hs1⟩
    | unTrap => exact False.elim (hnt (Or.inr ⟨_, rfl⟩))
    | unVal _ => exact False.elim (hnt (Or.inl (.lit _)))
  trap _ _ s := .single .unTrap
  fvSub _ _ hz := by simp [freeVars, hz]

private theorem isActiveCtx_binLeft (Δ : AdtEnv) (op : BinOp) (e2 : Expr) :
    IsActiveCtx Δ (fun x => .bin op x e2) where
  notTerm _ ht := by
    cases ht with
    | inl hv => cases hv
    | inr htr => rcases htr with ⟨_, h⟩; cases h
  step hs := .binLeft hs
  invert hnt hs := by
    cases hs with
    | binLeft hs1 => exact ⟨_, rfl, hs1⟩
    | binLeftTrap => exact False.elim (hnt (Or.inr ⟨_, rfl⟩))
    | binAndFalse | binAndTrue | binOrTrue | binOrFalse | binVal _ | binTrap _ =>
      exact False.elim (hnt (Or.inl (.lit _)))
    | binRight _ _ hv _ | binRightTrap _ _ hv =>
      exact False.elim (hnt (Or.inl hv))
  trap _ _ s := .single .binLeftTrap
  fvSub _ _ hz := by simp [freeVars, hz]

private theorem isActiveCtx_binRight (Δ : AdtEnv) {op : BinOp} (hnoAnd : op ≠ .and) (hnoOr : op ≠ .or)
    {v1 : Expr} (hv1 : IsValue v1) :
    IsActiveCtx Δ (fun x => .bin op v1 x) where
  notTerm _ ht := by
    cases ht with
    | inl hv => cases hv
    | inr htr => rcases htr with ⟨_, h⟩; cases h
  step hs := .binRight hnoAnd hnoOr hv1 hs
  invert hnt hs := by
    cases hs with
    | binLeft hs1 => exact False.elim (isValue_no_step hv1 hs1)
    | binLeftTrap => cases hv1
    | binAndFalse | binAndTrue => exact False.elim (hnoAnd rfl)
    | binOrTrue | binOrFalse => exact False.elim (hnoOr rfl)
    | binRight _ _ _ hs2 => exact ⟨_, rfl, hs2⟩
    | binRightTrap _ _ _ => exact False.elim (hnt (Or.inr ⟨_, rfl⟩))
    | binVal _ | binTrap _ => exact False.elim (hnt (Or.inl (.lit _)))
  trap _ _ s := .single (.binRightTrap hnoAnd hnoOr hv1)
  fvSub _ _ hz := by simp [freeVars, hz]

private theorem isActiveCtx_letLhs (Δ : AdtEnv) (nm : Ident) (e2 : Expr) :
    IsActiveCtx Δ (fun x => .let_ nm x e2) where
  notTerm _ ht := by
    cases ht with
    | inl hv => cases hv
    | inr htr => rcases htr with ⟨_, h⟩; cases h
  step hs := .letStep hs
  invert hnt hs := by
    cases hs with
    | letStep hs1 => exact ⟨_, rfl, hs1⟩
    | letTrap => exact False.elim (hnt (Or.inr ⟨_, rfl⟩))
    | letVal hv => exact False.elim (hnt (Or.inl hv))
  trap _ _ s := .single .letTrap
  fvSub _ _ hz := by simp [freeVars, hz]

private theorem isActiveCtx_ifCond (Δ : AdtEnv) (t e2 : Expr) :
    IsActiveCtx Δ (fun x => .if_ x t e2) where
  notTerm _ ht := by
    cases ht with
    | inl hv => cases hv
    | inr htr => rcases htr with ⟨_, h⟩; cases h
  step hs := .ifStep hs
  invert hnt hs := by
    cases hs with
    | ifStep hs1 => exact ⟨_, rfl, hs1⟩
    | ifTrap => exact False.elim (hnt (Or.inr ⟨_, rfl⟩))
    | ifTrue | ifFalse => exact False.elim (hnt (Or.inl (.lit _)))
  trap _ _ s := .single .ifTrap
  fvSub _ _ hz := by simp [freeVars, hz]

private theorem isActiveCtx_matchScrut (Δ : AdtEnv) (arms : List (Pat × Expr)) :
    IsActiveCtx Δ (fun x => .match_ x arms) where
  notTerm _ ht := by
    cases ht with
    | inl hv => cases hv
    | inr htr => rcases htr with ⟨_, h⟩; cases h
  step hs := .matchScrut hs
  invert hnt hs := by
    cases hs with
    | matchScrut hs1 => exact ⟨_, rfl, hs1⟩
    | matchScrutTrap => exact False.elim (hnt (Or.inr ⟨_, rfl⟩))
    | matchEmpty hv | matchHit hv _ | matchMiss hv _ => exact False.elim (hnt (Or.inl hv))
  trap _ _ s := .single .matchScrutTrap
  fvSub _ _ hz := by simp [freeVars, hz]

private theorem isActiveCtx_getTag (Δ : AdtEnv) : IsActiveCtx Δ (fun x => .getTag x) where
  notTerm _ ht := by
    cases ht with
    | inl hv => cases hv
    | inr htr => rcases htr with ⟨_, h⟩; cases h
  step hs := .getTagStep hs
  invert hnt hs := by
    cases hs with
    | getTagStep hs1 => exact ⟨_, rfl, hs1⟩
    | getTagTrap => exact False.elim (hnt (Or.inr ⟨_, rfl⟩))
    | getTagVal hvs => exact False.elim (hnt (Or.inl (.makeData _ _ hvs)))
  trap _ _ s := .single .getTagTrap
  fvSub _ _ hz := by simp [freeVars, hz]

private theorem isActiveCtx_cellNew (Δ : AdtEnv) : IsActiveCtx Δ (fun x => .cellNew x) where
  notTerm _ ht := by
    cases ht with
    | inl hv => cases hv
    | inr htr => rcases htr with ⟨_, h⟩; cases h
  step hs := .cellNewStep hs
  invert hnt hs := by
    cases hs with
    | cellNewStep hs1 => exact ⟨_, rfl, hs1⟩
    | cellNewTrap => exact False.elim (hnt (Or.inr ⟨_, rfl⟩))
    | cellNewVal hv => exact False.elim (hnt (Or.inl hv))
  trap _ _ s := .single .cellNewTrap
  fvSub _ _ hz := by simp [freeVars, hz]

private theorem isActiveCtx_cellGet (Δ : AdtEnv) : IsActiveCtx Δ (fun x => .cellGet x) where
  notTerm _ ht := by
    cases ht with
    | inl hv => cases hv
    | inr htr => rcases htr with ⟨_, h⟩; cases h
  step hs := .cellGetStep hs
  invert hnt hs := by
    cases hs with
    | cellGetStep hs1 => exact ⟨_, rfl, hs1⟩
    | cellGetTrap => exact False.elim (hnt (Or.inr ⟨_, rfl⟩))
    | cellGetVal _ => exact False.elim (hnt (Or.inl (.loc _)))
  trap _ _ s := .single .cellGetTrap
  fvSub _ _ hz := by simp [freeVars, hz]

private theorem isActiveCtx_cellSetLeft (Δ : AdtEnv) (e2 : Expr) :
    IsActiveCtx Δ (fun x => .cellSet x e2) where
  notTerm _ ht := by
    cases ht with
    | inl hv => cases hv
    | inr htr => rcases htr with ⟨_, h⟩; cases h
  step hs := .cellSetLeft hs
  invert hnt hs := by
    cases hs with
    | cellSetLeft hs1 => exact ⟨_, rfl, hs1⟩
    | cellSetLeftTrap => exact False.elim (hnt (Or.inr ⟨_, rfl⟩))
    | cellSetRight hv _ | cellSetRightTrap hv => exact False.elim (hnt (Or.inl hv))
    | cellSetVal _ _ => exact False.elim (hnt (Or.inl (.loc _)))
  trap _ _ s := .single .cellSetLeftTrap
  fvSub _ _ hz := by simp [freeVars, hz]

private theorem isActiveCtx_cellSetRight (Δ : AdtEnv) {v1 : Expr} (hv1 : IsValue v1) :
    IsActiveCtx Δ (fun x => .cellSet v1 x) where
  notTerm _ ht := by
    cases ht with
    | inl hv => cases hv
    | inr htr => rcases htr with ⟨_, h⟩; cases h
  step hs := .cellSetRight hv1 hs
  invert hnt hs := by
    cases hs with
    | cellSetLeft hs1 => exact False.elim (isValue_no_step hv1 hs1)
    | cellSetLeftTrap => cases hv1
    | cellSetRight _ hs2 => exact ⟨_, rfl, hs2⟩
    | cellSetRightTrap _ => exact False.elim (hnt (Or.inr ⟨_, rfl⟩))
    | cellSetVal _ hv2 => exact False.elim (hnt (Or.inl hv2))
  trap _ _ s := .single (.cellSetRightTrap hv1)
  fvSub _ _ hz := by simp [freeVars, hz]

private theorem isActiveCtx_spawn (Δ : AdtEnv) : IsActiveCtx Δ (fun x => .spawn x) where
  notTerm _ ht := by
    cases ht with
    | inl hv => cases hv
    | inr htr => rcases htr with ⟨_, h⟩; cases h
  step hs := .spawnStep hs
  invert hnt hs := by
    cases hs with
    | spawnStep hs1 => exact ⟨_, rfl, hs1⟩
    | spawnTrap => exact False.elim (hnt (Or.inr ⟨_, rfl⟩))
  trap _ _ s := .single .spawnTrap
  fvSub _ _ hz := by simp [freeVars, hz]

private theorem isActiveCtx_await (Δ : AdtEnv) : IsActiveCtx Δ (fun x => .await x) where
  notTerm _ ht := by
    cases ht with
    | inl hv => cases hv
    | inr htr => rcases htr with ⟨_, h⟩; cases h
  step hs := .awaitStep hs
  invert hnt hs := by
    cases hs with
    | awaitStep hs1 => exact ⟨_, rfl, hs1⟩
    | awaitTrap => exact False.elim (hnt (Or.inr ⟨_, rfl⟩))
    | awaitVal h _ | awaitTaskTrap h => simp [emptyPool] at h
  trap _ _ s := .single .awaitTrap
  fvSub _ _ hz := by simp [freeVars, hz]

mutual
private theorem step_decompose_target {Δ : AdtEnv} {Φa : FunEnv} {f : Ident} {fd : FunDef}
    (hfa : Φa f = some fd) {e e' : Expr} {σ σ' : Store}
    (hs : Step Δ Φa emptyPool e σ e' σ' .none) :
    (∀ Φb, (∀ g, g ≠ f → Φb g = Φa g) → Step Δ Φb emptyPool e σ e' σ' .none) ∨
    (σ' = σ ∧ ∃ (K : Expr → Expr) (vs : List Expr),
      IsActiveCtx Δ K ∧ (∀ v ∈ vs, IsValue v) ∧ vs.length = fd.params.length ∧
      e = K (.applyDir f vs) ∧ e' = K (substMany (zipParams fd.params vs) fd.body)) := by
  cases hs with
  | @applyDirBeta nm fd0 vs _ hlu hvs hlen =>
    by_cases hnm : nm = f
    · subst hnm
      rw [hfa] at hlu; injection hlu with hfd; subst hfd
      exact Or.inr ⟨rfl, fun x => x, vs, IsActiveCtx.id Δ, hvs, hlen, rfl, rfl⟩
    · exact Or.inl (fun Φb hag => .applyDirBeta (by rw [hag nm hnm]; exact hlu) hvs hlen)
  | tupleStep hsl =>
    rcases stepList_decompose_target hfa hsl with h1 | ⟨rfl, vs0, rest0, hvs0, K, vs, hK, hvs, hlen, rfl, rfl⟩
    · exact Or.inl (fun Φb hag => .tupleStep (h1 Φb hag))
    · exact Or.inr ⟨rfl, _, vs, (isActiveCtx_tupleElem Δ hvs0 rest0).comp hK, hvs, hlen, rfl, rfl⟩
  | blockConsStep hs1 =>
    rcases step_decompose_target hfa hs1 with h1 | ⟨rfl, K, vs, hK, hvs, hlen, rfl, rfl⟩
    · exact Or.inl (fun Φb hag => .blockConsStep (h1 Φb hag))
    · exact Or.inr ⟨rfl, _, vs, (isActiveCtx_blockHead Δ _ _).comp hK, hvs, hlen, rfl, rfl⟩
  | applyFn hs1 =>
    rcases step_decompose_target hfa hs1 with h1 | ⟨rfl, K, vs, hK, hvs, hlen, rfl, rfl⟩
    · exact Or.inl (fun Φb hag => .applyFn (h1 Φb hag))
    · exact Or.inr ⟨rfl, _, vs, (isActiveCtx_applyFn Δ _).comp hK, hvs, hlen, rfl, rfl⟩
  | applyArgs hvf hsl =>
    rcases stepList_decompose_target hfa hsl with h1 | ⟨rfl, vs0, rest0, hvs0, K, vs, hK, hvs, hlen, rfl, rfl⟩
    · exact Or.inl (fun Φb hag => .applyArgs hvf (h1 Φb hag))
    · exact Or.inr ⟨rfl, _, vs, (isActiveCtx_applyArg Δ hvf hvs0 rest0).comp hK, hvs, hlen, rfl, rfl⟩
  | applyDirArgs hsl =>
    rcases stepList_decompose_target hfa hsl with h1 | ⟨rfl, vs0, rest0, hvs0, K, vs, hK, hvs, hlen, rfl, rfl⟩
    · exact Or.inl (fun Φb hag => .applyDirArgs (h1 Φb hag))
    · exact Or.inr ⟨rfl, _, vs, (isActiveCtx_applyDirArg Δ _ hvs0 rest0).comp hK, hvs, hlen, rfl, rfl⟩
  | unStep hs1 =>
    rcases step_decompose_target hfa hs1 with h1 | ⟨rfl, K, vs, hK, hvs, hlen, rfl, rfl⟩
    · exact Or.inl (fun Φb hag => .unStep (h1 Φb hag))
    · exact Or.inr ⟨rfl, _, vs, (isActiveCtx_un Δ _).comp hK, hvs, hlen, rfl, rfl⟩
  | binLeft hs1 =>
    rcases step_decompose_target hfa hs1 with h1 | ⟨rfl, K, vs, hK, hvs, hlen, rfl, rfl⟩
    · exact Or.inl (fun Φb hag => .binLeft (h1 Φb hag))
    · exact Or.inr ⟨rfl, _, vs, (isActiveCtx_binLeft Δ _ _).comp hK, hvs, hlen, rfl, rfl⟩
  | binRight hna hno hv1 hs2 =>
    rcases step_decompose_target hfa hs2 with h1 | ⟨rfl, K, vs, hK, hvs, hlen, rfl, rfl⟩
    · exact Or.inl (fun Φb hag => .binRight hna hno hv1 (h1 Φb hag))
    · exact Or.inr ⟨rfl, _, vs, (isActiveCtx_binRight Δ hna hno hv1).comp hK, hvs, hlen, rfl, rfl⟩
  | letStep hs1 =>
    rcases step_decompose_target hfa hs1 with h1 | ⟨rfl, K, vs, hK, hvs, hlen, rfl, rfl⟩
    · exact Or.inl (fun Φb hag => .letStep (h1 Φb hag))
    · exact Or.inr ⟨rfl, _, vs, (isActiveCtx_letLhs Δ _ _).comp hK, hvs, hlen, rfl, rfl⟩
  | ifStep hs1 =>
    rcases step_decompose_target hfa hs1 with h1 | ⟨rfl, K, vs, hK, hvs, hlen, rfl, rfl⟩
    · exact Or.inl (fun Φb hag => .ifStep (h1 Φb hag))
    · exact Or.inr ⟨rfl, _, vs, (isActiveCtx_ifCond Δ _ _).comp hK, hvs, hlen, rfl, rfl⟩
  | matchScrut hs1 =>
    rcases step_decompose_target hfa hs1 with h1 | ⟨rfl, K, vs, hK, hvs, hlen, rfl, rfl⟩
    · exact Or.inl (fun Φb hag => .matchScrut (h1 Φb hag))
    · exact Or.inr ⟨rfl, _, vs, (isActiveCtx_matchScrut Δ _).comp hK, hvs, hlen, rfl, rfl⟩
  | makeDataStep hsl =>
    rcases stepList_decompose_target hfa hsl with h1 | ⟨rfl, vs0, rest0, hvs0, K, vs, hK, hvs, hlen, rfl, rfl⟩
    · exact Or.inl (fun Φb hag => .makeDataStep (h1 Φb hag))
    · exact Or.inr ⟨rfl, _, vs, (isActiveCtx_makeDataElem Δ _ _ hvs0 rest0).comp hK, hvs, hlen, rfl, rfl⟩
  | getTagStep hs1 =>
    rcases step_decompose_target hfa hs1 with h1 | ⟨rfl, K, vs, hK, hvs, hlen, rfl, rfl⟩
    · exact Or.inl (fun Φb hag => .getTagStep (h1 Φb hag))
    · exact Or.inr ⟨rfl, _, vs, (isActiveCtx_getTag Δ).comp hK, hvs, hlen, rfl, rfl⟩
  | cellNewStep hs1 =>
    rcases step_decompose_target hfa hs1 with h1 | ⟨rfl, K, vs, hK, hvs, hlen, rfl, rfl⟩
    · exact Or.inl (fun Φb hag => .cellNewStep (h1 Φb hag))
    · exact Or.inr ⟨rfl, _, vs, (isActiveCtx_cellNew Δ).comp hK, hvs, hlen, rfl, rfl⟩
  | cellGetStep hs1 =>
    rcases step_decompose_target hfa hs1 with h1 | ⟨rfl, K, vs, hK, hvs, hlen, rfl, rfl⟩
    · exact Or.inl (fun Φb hag => .cellGetStep (h1 Φb hag))
    · exact Or.inr ⟨rfl, _, vs, (isActiveCtx_cellGet Δ).comp hK, hvs, hlen, rfl, rfl⟩
  | cellSetLeft hs1 =>
    rcases step_decompose_target hfa hs1 with h1 | ⟨rfl, K, vs, hK, hvs, hlen, rfl, rfl⟩
    · exact Or.inl (fun Φb hag => .cellSetLeft (h1 Φb hag))
    · exact Or.inr ⟨rfl, _, vs, (isActiveCtx_cellSetLeft Δ _).comp hK, hvs, hlen, rfl, rfl⟩
  | cellSetRight hv1 hs2 =>
    rcases step_decompose_target hfa hs2 with h1 | ⟨rfl, K, vs, hK, hvs, hlen, rfl, rfl⟩
    · exact Or.inl (fun Φb hag => .cellSetRight hv1 (h1 Φb hag))
    · exact Or.inr ⟨rfl, _, vs, (isActiveCtx_cellSetRight Δ hv1).comp hK, hvs, hlen, rfl, rfl⟩
  | spawnStep hs1 =>
    rcases step_decompose_target hfa hs1 with h1 | ⟨rfl, K, vs, hK, hvs, hlen, rfl, rfl⟩
    · exact Or.inl (fun Φb hag => .spawnStep (h1 Φb hag))
    · exact Or.inr ⟨rfl, _, vs, (isActiveCtx_spawn Δ).comp hK, hvs, hlen, rfl, rfl⟩
  | awaitStep hs1 =>
    rcases step_decompose_target hfa hs1 with h1 | ⟨rfl, K, vs, hK, hvs, hlen, rfl, rfl⟩
    · exact Or.inl (fun Φb hag => .awaitStep (h1 Φb hag))
    · exact Or.inr ⟨rfl, _, vs, (isActiveCtx_await Δ).comp hK, hvs, hlen, rfl, rfl⟩
  | concPrimArgs hsl =>
    rcases stepList_decompose_target hfa hsl with h1 | ⟨rfl, vs0, rest0, hvs0, K, vs, hK, hvs, hlen, rfl, rfl⟩
    · exact Or.inl (fun Φb hag => .concPrimArgs (h1 Φb hag))
    · exact Or.inr ⟨rfl, _, vs, (isActiveCtx_concPrimElem Δ _ hvs0 rest0).comp hK, hvs, hlen, rfl, rfl⟩
  | tupleTrap htr => exact Or.inl (fun _ _ => .tupleTrap htr)
  | blockEmpty => exact Or.inl (fun _ _ => .blockEmpty)
  | blockSingle => exact Or.inl (fun _ _ => .blockSingle)
  | blockConsVal hv => exact Or.inl (fun _ _ => .blockConsVal hv)
  | blockConsTrap => exact Or.inl (fun _ _ => .blockConsTrap)
  | applyFnTrap => exact Or.inl (fun _ _ => .applyFnTrap)
  | applyArgsTrap hvf htr => exact Or.inl (fun _ _ => .applyArgsTrap hvf htr)
  | applyBeta hvs hlen => exact Or.inl (fun _ _ => .applyBeta hvs hlen)
  | applyDirTrap htr => exact Or.inl (fun _ _ => .applyDirTrap htr)
  | unTrap => exact Or.inl (fun _ _ => .unTrap)
  | unVal hev => exact Or.inl (fun _ _ => .unVal hev)
  | binLeftTrap => exact Or.inl (fun _ _ => .binLeftTrap)
  | binAndFalse => exact Or.inl (fun _ _ => .binAndFalse)
  | binAndTrue => exact Or.inl (fun _ _ => .binAndTrue)
  | binOrTrue => exact Or.inl (fun _ _ => .binOrTrue)
  | binOrFalse => exact Or.inl (fun _ _ => .binOrFalse)
  | binRightTrap hna hno hv1 => exact Or.inl (fun _ _ => .binRightTrap hna hno hv1)
  | binVal hev => exact Or.inl (fun _ _ => .binVal hev)
  | binTrap hev => exact Or.inl (fun _ _ => .binTrap hev)
  | letTrap => exact Or.inl (fun _ _ => .letTrap)
  | letVal hv => exact Or.inl (fun _ _ => .letVal hv)
  | ifTrap => exact Or.inl (fun _ _ => .ifTrap)
  | ifTrue => exact Or.inl (fun _ _ => .ifTrue)
  | ifFalse => exact Or.inl (fun _ _ => .ifFalse)
  | whileUnfold => exact Or.inl (fun _ _ => .whileUnfold)
  | matchScrutTrap => exact Or.inl (fun _ _ => .matchScrutTrap)
  | matchEmpty hv => exact Or.inl (fun _ _ => .matchEmpty hv)
  | matchHit hv hm => exact Or.inl (fun _ _ => .matchHit hv hm)
  | matchMiss hv hm => exact Or.inl (fun _ _ => .matchMiss hv hm)
  | makeDataTrap htr => exact Or.inl (fun _ _ => .makeDataTrap htr)
  | getTagTrap => exact Or.inl (fun _ _ => .getTagTrap)
  | getTagVal hvs => exact Or.inl (fun _ _ => .getTagVal hvs)
  | cellNewTrap => exact Or.inl (fun _ _ => .cellNewTrap)
  | cellNewVal hv => exact Or.inl (fun _ _ => .cellNewVal hv)
  | cellGetTrap => exact Or.inl (fun _ _ => .cellGetTrap)
  | cellGetVal hl => exact Or.inl (fun _ _ => .cellGetVal hl)
  | cellSetLeftTrap => exact Or.inl (fun _ _ => .cellSetLeftTrap)
  | cellSetRightTrap hv1 => exact Or.inl (fun _ _ => .cellSetRightTrap hv1)
  | cellSetVal hlt hv => exact Or.inl (fun _ _ => .cellSetVal hlt hv)
  | spawnTrap => exact Or.inl (fun _ _ => .spawnTrap)
  | awaitTrap => exact Or.inl (fun _ _ => .awaitTrap)
  | awaitVal h _ | awaitTaskTrap h => simp [emptyPool] at h
  | concPrimTrap htr => exact Or.inl (fun _ _ => .concPrimTrap htr)
  | concPrimVal hc => exact False.elim (stepConcPrim_emptyPool_none_false hc)
termination_by sizeOf e

private theorem stepList_decompose_target {Δ : AdtEnv} {Φa : FunEnv} {f : Ident} {fd : FunDef}
    (hfa : Φa f = some fd) {es es' : List Expr} {σ σ' : Store}
    (hsl : StepList Δ Φa emptyPool es σ es' σ' .none) :
    (∀ Φb, (∀ g, g ≠ f → Φb g = Φa g) → StepList Δ Φb emptyPool es σ es' σ' .none) ∨
    (σ' = σ ∧ ∃ (vs0 rest0 : List Expr), (∀ v ∈ vs0, IsValue v) ∧
      ∃ (K : Expr → Expr) (vs : List Expr),
        IsActiveCtx Δ K ∧ (∀ v ∈ vs, IsValue v) ∧ vs.length = fd.params.length ∧
        es = vs0 ++ K (.applyDir f vs) :: rest0 ∧
        es' = vs0 ++ K (substMany (zipParams fd.params vs) fd.body) :: rest0) := by
  cases hsl with
  | head hs =>
    rcases step_decompose_target hfa hs with h1 | ⟨rfl, K, vs, hK, hvs, hlen, rfl, rfl⟩
    · exact Or.inl (fun Φb hag => .head (h1 Φb hag))
    · exact Or.inr ⟨rfl, [], _, (fun _ h => by cases h), K, vs, hK, hvs, hlen, rfl, rfl⟩
  | tail hv hsl' =>
    rcases stepList_decompose_target hfa hsl' with h1 | ⟨rfl, vs0, rest0, hvs0, K, vs, hK, hvs, hlen, rfl, rfl⟩
    · exact Or.inl (fun Φb hag => .tail hv (h1 Φb hag))
    · refine Or.inr ⟨rfl, _ :: vs0, rest0, ?_, K, vs, hK, hvs, hlen, rfl, rfl⟩
      intro w hw; rcases List.mem_cons.mp hw with rfl | hwr
      · exact hv
      · exact hvs0 w hwr
termination_by sizeOf es
end

private theorem recFunBody_steps_forward {Δ : AdtEnv} {Φa Φb : FunEnv} {f : Ident}
    {fda fdb : FunDef}
    (hΦa_cl : ClosedFunEnv Φa)
    (hfa : Φa f = some fda) (hfb : Φb f = some fdb)
    (hagree : ∀ g, g ≠ f → Φb g = Φa g)
    (hlen : fda.params.length = fdb.params.length)
    (hbody : ∀ vs, (∀ v ∈ vs, IsValue v) → (∀ v ∈ vs, freeVars v = []) →
      vs.length = fda.params.length →
      ClosedObsEquiv Δ Φb Φb (substMany (zipParams fda.params vs) fda.body)
                             (substMany (zipParams fdb.params vs) fdb.body))
    {e out : Expr} {σ σ' : Store}
    (hsteps : Steps Δ Φa e σ out σ')
    (hσ : ClosedStore σ) (he : freeVars e = []) (hout : IsTerminal out) :
    Steps Δ Φb e σ out σ' := by
  induction hsteps with
  | refl => exact .refl _ _
  | trans hs _ ih =>
    rcases step_preserves_closed hΦa_cl hσ he hs with ⟨he1, hσ1⟩
    have hrest_b := ih hσ1 he1 hout
    rcases step_decompose_target hfa hs with hother | ⟨rfl, K, vs, hK, hvs, hvslen, rfl, rfl⟩
    · exact .trans (hother Φb hagree) hrest_b
    · have hcall_cl : freeVars (Expr.applyDir f vs) = [] := by
        apply List.eq_nil_iff_forall_not_mem.mpr
        intro z hz
        have hmem := hK.fvSub (.applyDir f vs) z hz
        rw [he] at hmem; cases hmem
      have hvs_cl : ∀ v ∈ vs, freeVars v = [] := by
        simp only [freeVars] at hcall_cl
        exact freeVarsList_eq_nil_iff.mp hcall_cl
      have heqvK := activeCtx_closedObsEquiv_congr hK (hbody vs hvs hvs_cl hvslen)
      have hstep_b_body := (heqvK _ _ _ hσ1 hout).mp hrest_b
      exact .trans (hK.step (.applyDirBeta hfb hvs (hvslen.trans hlen))) hstep_b_body

/-- **Recursive Function-Body `ClosedObsEquiv` Congruence (`recFunBody_obsEquiv_congr`)**:
    Replacing a recursive function `f`'s parameter names & body `(ps_a, body_a)` with
    `(ps_b, body_b)` (where `ps_a.length = ps_b.length` and their closed-value instantiations
    are `ClosedObsEquiv` in both `Φa` and `Φb`) preserves exact multi-iteration `Steps` across
    arbitrary recursive call trees! -/
theorem recFunBody_obsEquiv_congr {Δ : AdtEnv} {Φa Φb : FunEnv} {f : Ident}
    {fda fdb : FunDef}
    (hΦa_cl : ClosedFunEnv Φa) (hΦb_cl : ClosedFunEnv Φb)
    (hfa : Φa f = some fda) (hfb : Φb f = some fdb)
    (hagree : ∀ g, g ≠ f → Φa g = Φb g)
    (hlen : fda.params.length = fdb.params.length)
    (hbody_a : ∀ vs, (∀ v ∈ vs, IsValue v) → (∀ v ∈ vs, freeVars v = []) →
      vs.length = fda.params.length →
      ClosedObsEquiv Δ Φa Φa (substMany (zipParams fda.params vs) fda.body)
                             (substMany (zipParams fdb.params vs) fdb.body))
    (hbody_b : ∀ vs, (∀ v ∈ vs, IsValue v) → (∀ v ∈ vs, freeVars v = []) →
      vs.length = fda.params.length →
      ClosedObsEquiv Δ Φb Φb (substMany (zipParams fda.params vs) fda.body)
                             (substMany (zipParams fdb.params vs) fdb.body))
    {e out : Expr} {σ σ' : Store}
    (hσ : ClosedStore σ) (he : freeVars e = []) (hout : IsTerminal out) :
    Steps Δ Φa e σ out σ' ↔ Steps Δ Φb e σ out σ' := by
  constructor
  · intro h
    exact recFunBody_steps_forward hΦa_cl hfa hfb (fun g hg => (hagree g hg).symm) hlen hbody_b h hσ he hout
  · intro h
    exact recFunBody_steps_forward hΦb_cl hfb hfa hagree hlen.symm
      (fun vs hvs hcl hvl => ClosedObsEquiv.symm (hbody_a vs hvs hcl (hvl.trans hlen.symm))) h hσ he hout

/-! ### 10.2 Full `coTermIsPure` (`src/core.gsa:5363`) Including Nested `TmMakeCls` Continuations -/

mutual
def coExprIsPure : Expr → Bool
  | .lit _ => true
  | .var _ => true
  | .loc _ => true
  | .taskRef _ => true
  | .syncRef _ _ => true
  | .lam _ _ _ _ => true
  | .let_ _ (.lam _ _ _ _) body => coExprIsPure body
  | .tuple es => coExprListIsPure es
  | .makeData _ _ es => coExprListIsPure es
  | _ => false

def coExprListIsPure : List Expr → Bool
  | [] => true
  | e :: r => coExprIsPure e && coExprListIsPure r
end

mutual
private def pureEvalMeasure : Expr → Nat
  | .let_ _ (.lam _ _ _ _) body => 1 + pureEvalMeasure body
  | .tuple es => 1 + pureEvalListMeasure es
  | .makeData _ _ es => 1 + pureEvalListMeasure es
  | _ => 0

private def pureEvalListMeasure : List Expr → Nat
  | [] => 0
  | e :: r => 1 + pureEvalMeasure e + pureEvalListMeasure r
end

mutual
private theorem coExprIsPure_subst_lam (y : Ident) (m : Mode) (ps : List (Ident × Ty))
    (ret : Ty) (cb : Expr) :
    (e : Expr) → coExprIsPure e = true →
      coExprIsPure (subst y (.lam m ps ret cb) e) = true ∧
      pureEvalMeasure (subst y (.lam m ps ret cb) e) = pureEvalMeasure e
  | .lit _, _ => ⟨rfl, rfl⟩
  | .var z, _ => by
    simp only [subst]; split <;> exact ⟨rfl, rfl⟩
  | .loc _, _ => ⟨rfl, rfl⟩
  | .taskRef _, _ => ⟨rfl, rfl⟩
  | .syncRef _ _, _ => ⟨rfl, rfl⟩
  | .lam _ _ _ _, _ => by
    simp only [subst]; split <;> exact ⟨rfl, rfl⟩
  | .let_ x e1 body, hp => by
    cases e1 with
    | lam m2 ps2 ret2 cb2 =>
      simp only [coExprIsPure] at hp
      have hlam : ∃ b', (if ps2.any (fun p => p.1 == y) then Expr.lam m2 ps2 ret2 cb2
                         else Expr.lam m2 ps2 ret2 (subst y (.lam m ps ret cb) cb2)) = .lam m2 ps2 ret2 b' := by
        split <;> exact ⟨_, rfl⟩
      rcases hlam with ⟨b', hb'⟩
      simp only [subst]
      rw [hb']
      split
      · exact ⟨hp, rfl⟩
      · rcases coExprIsPure_subst_lam y m ps ret cb body hp with ⟨hp2, hm2⟩
        exact ⟨hp2, by simp [pureEvalMeasure, hm2]⟩
    | _ => simp [coExprIsPure] at hp
  | .tuple es, hp => by
    simp only [coExprIsPure] at hp
    rcases coExprListIsPure_subst_lam y m ps ret cb es hp with ⟨hp2, hm2⟩
    exact ⟨hp2, by simp [subst, pureEvalMeasure, hm2]⟩
  | .makeData adt tag es, hp => by
    simp only [coExprIsPure] at hp
    rcases coExprListIsPure_subst_lam y m ps ret cb es hp with ⟨hp2, hm2⟩
    exact ⟨hp2, by simp [subst, pureEvalMeasure, hm2]⟩
  | .block _, hp | .apply _ _, hp | .applyDir _ _, hp | .bin _ _ _, hp | .un _ _, hp
  | .if_ _ _ _, hp | .while_ _ _, hp | .match_ _ _, hp | .getTag _, hp
  | .cellNew _, hp | .cellGet _, hp | .cellSet _ _, hp | .spawn _, hp
  | .await _, hp | .concPrim _ _, hp | .trap _, hp => by
    simp [coExprIsPure] at hp
termination_by e => sizeOf e

private theorem coExprListIsPure_subst_lam (y : Ident) (m : Mode) (ps : List (Ident × Ty))
    (ret : Ty) (cb : Expr) :
    (es : List Expr) → coExprListIsPure es = true →
      coExprListIsPure (substList y (.lam m ps ret cb) es) = true ∧
      pureEvalListMeasure (substList y (.lam m ps ret cb) es) = pureEvalListMeasure es
  | [], _ => ⟨rfl, rfl⟩
  | e :: r, hp => by
    simp only [coExprListIsPure, Bool.and_eq_true] at hp
    rcases coExprIsPure_subst_lam y m ps ret cb e hp.1 with ⟨hp_e, hm_e⟩
    rcases coExprListIsPure_subst_lam y m ps ret cb r hp.2 with ⟨hp_r, hm_r⟩
    refine ⟨?_, ?_⟩
    · simp only [substList, coExprListIsPure, Bool.and_eq_true]; exact ⟨hp_e, hp_r⟩
    · simp only [substList, pureEvalListMeasure, hm_e, hm_r]
termination_by es => sizeOf es
end

private theorem coExprIsPure_fuel (Δ : AdtEnv) (Φ : FunEnv) (σ : Store) :
    (fuel : Nat) →
    (∀ e : Expr, pureEvalMeasure e ≤ fuel → freeVars e = [] → coExprIsPure e = true →
      ∃ v, IsValue v ∧ Steps Δ Φ e σ v σ) ∧
    (∀ es : List Expr, pureEvalListMeasure es ≤ fuel → freeVarsList es = [] → coExprListIsPure es = true →
      ∃ vs, (∀ v ∈ vs, IsValue v) ∧
        (∀ (F : List Expr → Expr),
          (∀ {l1 l2 : List Expr} {s1 s2 : Store},
            StepList Δ Φ emptyPool l1 s1 l2 s2 .none → Step Δ Φ emptyPool (F l1) s1 (F l2) s2 .none) →
          Steps Δ Φ (F es) σ (F vs) σ))
  | 0 => by
    refine ⟨?_, ?_⟩
    · intro e hm hcl hp
      cases e with
      | lit l => exact ⟨.lit l, .lit l, .refl _ _⟩
      | var z => simp [freeVars] at hcl
      | loc l => exact ⟨.loc l, .loc l, .refl _ _⟩
      | taskRef tid => exact ⟨.taskRef tid, .taskRef tid, .refl _ _⟩
      | syncRef k id => exact ⟨.syncRef k id, .syncRef k id, .refl _ _⟩
      | lam m ps ret b => exact ⟨.lam m ps ret b, .lam m ps ret b, .refl _ _⟩
      | let_ x e1 body =>
        cases e1 <;> simp [coExprIsPure, pureEvalMeasure] at hp hm
      | tuple es => simp [pureEvalMeasure] at hm
      | makeData adt tag es => simp [pureEvalMeasure] at hm
      | _ => simp [coExprIsPure] at hp
    · intro es hm _ _
      cases es with
      | nil => exact ⟨[], (fun _ h => by cases h), (fun _ _ => Steps.refl _ _)⟩
      | cons e r => simp [pureEvalListMeasure] at hm
  | fuel + 1 => by
    rcases coExprIsPure_fuel Δ Φ σ fuel with ⟨ihE, ihL⟩
    refine ⟨?_, ?_⟩
    · intro e hm hcl hp
      cases e with
      | lit l => exact ⟨.lit l, .lit l, .refl _ _⟩
      | var z => simp [freeVars] at hcl
      | loc l => exact ⟨.loc l, .loc l, .refl _ _⟩
      | taskRef tid => exact ⟨.taskRef tid, .taskRef tid, .refl _ _⟩
      | syncRef k id => exact ⟨.syncRef k id, .syncRef k id, .refl _ _⟩
      | lam m ps ret b => exact ⟨.lam m ps ret b, .lam m ps ret b, .refl _ _⟩
      | let_ x e1 body =>
        cases e1 with
        | lam m ps ret cb =>
          simp only [coExprIsPure] at hp
          simp only [pureEvalMeasure] at hm
          have hlam_cl : freeVars (Expr.lam m ps ret cb) = [] := by
            simp only [freeVars, List.append_eq_nil_iff] at hcl; exact hcl.1
          have hsub_cl : freeVars (subst x (.lam m ps ret cb) body) = [] := by
            apply List.eq_nil_iff_forall_not_mem.mpr
            intro z hz
            rcases subst_freeVars_subset x (.lam m ps ret cb) hlam_cl body z hz with ⟨hne, hmem⟩
            have hmem_let : z ∈ freeVars (.let_ x (.lam m ps ret cb) body) := by
              simp [freeVars, hmem, hne]
            rw [hcl] at hmem_let; cases hmem_let
          rcases coExprIsPure_subst_lam x m ps ret cb body hp with ⟨hp_sub, hm_sub⟩
          have hm_le : pureEvalMeasure (subst x (.lam m ps ret cb) body) ≤ fuel := by omega
          rcases ihE _ hm_le hsub_cl hp_sub with ⟨v, hv, hsteps⟩
          exact ⟨v, hv, .trans (.letVal (.lam m ps ret cb)) hsteps⟩
        | _ => simp [coExprIsPure] at hp
      | tuple es =>
        simp only [freeVars] at hcl
        simp only [coExprIsPure] at hp
        simp only [pureEvalMeasure] at hm
        rcases ihL es (by omega) hcl hp with ⟨vs, hvs, hsteps⟩
        exact ⟨.tuple vs, .tuple hvs, hsteps Expr.tuple (fun hsl => .tupleStep hsl)⟩
      | makeData adt tag es =>
        simp only [freeVars] at hcl
        simp only [coExprIsPure] at hp
        simp only [pureEvalMeasure] at hm
        rcases ihL es (by omega) hcl hp with ⟨vs, hvs, hsteps⟩
        exact ⟨.makeData adt tag vs, .makeData adt tag hvs,
          hsteps (Expr.makeData adt tag) (fun hsl => .makeDataStep hsl)⟩
      | _ => simp [coExprIsPure] at hp
    · intro es hm hcl hp
      cases es with
      | nil => exact ⟨[], (fun _ h => by cases h), (fun _ _ => Steps.refl _ _)⟩
      | cons e r =>
        simp only [freeVarsList, List.append_eq_nil_iff] at hcl
        simp only [coExprListIsPure, Bool.and_eq_true] at hp
        simp only [pureEvalListMeasure] at hm
        rcases ihE e (by omega) hcl.1 hp.1 with ⟨ve, hve, hs_e⟩
        rcases ihL r (by omega) hcl.2 hp.2 with ⟨vr, hvr, hs_r⟩
        refine ⟨ve :: vr, ?_, ?_⟩
        · intro w hw; rcases List.mem_cons.mp hw with rfl | hwr
          · exact hve
          · exact hvr w hwr
        · intro F hF
          have h1 : Steps Δ Φ (F (e :: r)) σ (F (ve :: r)) σ :=
            Steps.liftCongr (fun z => F (z :: r)) (fun hs => hF (.head hs)) hs_e
          have h2 : Steps Δ Φ (F (ve :: r)) σ (F (ve :: vr)) σ :=
            hs_r (fun l => F (ve :: l)) (fun hsl => hF (.tail hve hsl))
          exact Steps.append h1 h2

/-- **Exact Termination & Heap-Invariance of `coTermIsPure` (`coExprIsPure_closed_steps_to_val`)**:
    Every closed expression accepted by `coTermIsPure` (`src/core.gsa:5363`, including arbitrarily
    nested `TmMakeCls(_, _, continuation)` chains inside tuples and ADTs) evaluates deterministically
    in finite steps to a value `v` with unchanged `Store` `σ` and zero traps! -/
theorem coExprIsPure_closed_steps_to_val (Δ : AdtEnv) (Φ : FunEnv) (σ : Store)
    (e : Expr) (hcl : freeVars e = []) (hp : coExprIsPure e = true) :
    ∃ v, IsValue v ∧ Steps Δ Φ e σ v σ :=
  (coExprIsPure_fuel Δ Φ σ (pureEvalMeasure e)).1 e (Nat.le_refl _) hcl hp

/-- **Full `coFinishLetWithDeadElim` Soundness on All `coExprIsPure` RHS Terms**:
    Covers nested `TmMakeCls` continuations (`let x = (let f = lam ... in (f, 1)) in body`)! -/
theorem coFinishLetWithDeadElim_coExprIsPure_obsEquiv (Δ : AdtEnv) (Φ : FunEnv)
    {x : Ident} {rhs body : Expr}
    (hrhs_cl : freeVars rhs = []) (hrhs_pure : coExprIsPure rhs = true)
    (hxnot : x ∉ freeVars body) :
    ObsEquiv Δ Φ Φ (.let_ x rhs body) body := by
  intro σ σ' out hout
  rw [steps_let_terminal_iff hout]
  rcases coExprIsPure_closed_steps_to_val Δ Φ σ rhs hrhs_cl hrhs_pure with ⟨vr, hvr, hs_rhs⟩
  constructor
  · rintro (⟨t, rfl, htr⟩ | ⟨v1, σ1, hv1, hsv1, hs_body⟩)
    · rcases steps_terminal_det htr (Or.inr ⟨t, rfl⟩) hs_rhs (Or.inl hvr) with ⟨heq, _⟩
      cases hvr <;> cases heq
    · rcases steps_terminal_det hsv1 (Or.inl hv1) hs_rhs (Or.inl hvr) with ⟨rfl, rfl⟩
      rwa [subst_not_mem_freeVars body hxnot] at hs_body
  · intro hbody
    refine Or.inr ⟨vr, σ, hvr, hs_rhs, ?_⟩
    rwa [subst_not_mem_freeVars body hxnot]

mutual
theorem coExprIsPure_of_isValue : {v : Expr} → IsValue v → coExprIsPure v = true
  | _, .lit _ => rfl
  | _, .loc _ => rfl
  | _, .taskRef _ => rfl
  | _, .syncRef _ _ => rfl
  | _, .lam _ _ _ _ => rfl
  | .tuple vs, .tuple hvs => coExprListIsPure_of_isValue vs hvs
  | .makeData _ _ vs, .makeData _ _ hvs => coExprListIsPure_of_isValue vs hvs
termination_by v => sizeOf v

theorem coExprListIsPure_of_isValue : (vs : List Expr) → (∀ v ∈ vs, IsValue v) → coExprListIsPure vs = true
  | [], _ => rfl
  | v :: vr, hvs => by
    simp only [coExprListIsPure, Bool.and_eq_true]
    exact ⟨coExprIsPure_of_isValue (hvs v (List.mem_cons_self ..)),
           coExprListIsPure_of_isValue vr (fun w hw => hvs w (List.mem_cons_of_mem _ hw))⟩
termination_by vs => sizeOf vs
end

mutual
theorem coExprIsPure_subst_val (y : Ident) {w : Expr} (hw : IsValue w) :
    (e : Expr) → coExprIsPure e = true → coExprIsPure (subst y w e) = true
  | .lit _, _ => rfl
  | .var z, _ => by
    simp only [subst]; split
    · exact coExprIsPure_of_isValue hw
    · rfl
  | .loc _, _ => rfl
  | .taskRef _, _ => rfl
  | .syncRef _ _, _ => rfl
  | .lam _ _ _ _, _ => by
    simp only [subst]; split <;> rfl
  | .let_ x e1 body, hp => by
    cases e1 with
    | lam m2 ps2 ret2 cb2 =>
      simp only [coExprIsPure] at hp
      have hlam : ∃ b', (if ps2.any (fun p => p.1 == y) then Expr.lam m2 ps2 ret2 cb2
                         else Expr.lam m2 ps2 ret2 (subst y w cb2)) = .lam m2 ps2 ret2 b' := by
        split <;> exact ⟨_, rfl⟩
      rcases hlam with ⟨b', hb'⟩
      simp only [subst]; rw [hb']
      split
      · exact hp
      · exact coExprIsPure_subst_val y hw body hp
    | _ => simp [coExprIsPure] at hp
  | .tuple es, hp => by
    simp only [coExprIsPure] at hp
    exact coExprListIsPure_subst_val y hw es hp
  | .makeData _ _ es, hp => by
    simp only [coExprIsPure] at hp
    exact coExprListIsPure_subst_val y hw es hp
  | .block _, hp | .apply _ _, hp | .applyDir _ _, hp | .bin _ _ _, hp | .un _ _, hp
  | .if_ _ _ _, hp | .while_ _ _, hp | .match_ _ _, hp | .getTag _, hp
  | .cellNew _, hp | .cellGet _, hp | .cellSet _ _, hp | .spawn _, hp
  | .await _, hp | .concPrim _ _, hp | .trap _, hp => by
    simp [coExprIsPure] at hp
termination_by e => sizeOf e

theorem coExprListIsPure_subst_val (y : Ident) {w : Expr} (hw : IsValue w) :
    (es : List Expr) → coExprListIsPure es = true → coExprListIsPure (substList y w es) = true
  | [], _ => rfl
  | e :: r, hp => by
    simp only [coExprListIsPure, Bool.and_eq_true] at hp
    simp only [substList, coExprListIsPure, Bool.and_eq_true]
    exact ⟨coExprIsPure_subst_val y hw e hp.1, coExprListIsPure_subst_val y hw r hp.2⟩
termination_by es => sizeOf es
end

theorem coExprIsPure_substMany_vals :
    (env : List (Ident × Expr)) → (∀ p ∈ env, IsValue p.2) →
    {e : Expr} → coExprIsPure e = true → coExprIsPure (substMany env e) = true
  | [], _, _, hp => hp
  | (k, v) :: r, henv, _, hp =>
    coExprIsPure_substMany_vals r (fun q hq => henv q (List.mem_cons_of_mem _ hq))
      (coExprIsPure_subst_val k (henv (k, v) (List.mem_cons_self ..)) _ hp)

/-! ### 10.3 `while` Congruence, Lookup-Congruent `substMany`, `AlphaOptRel` (`coCloneTerm` + `coOptTerm`), `$flat$` OptBody & Exact `$flat$44` Artifact Proof -/

private inductive StepsN (Δ : AdtEnv) (Φ : FunEnv) : Nat → Expr → Store → Expr → Store → Prop where
  | zero (e : Expr) (σ : Store) : StepsN Δ Φ 0 e σ e σ
  | succ {n : Nat} {e1 e2 e3 : Expr} {σ1 σ2 σ3 : Store} :
      Step Δ Φ emptyPool e1 σ1 e2 σ2 .none →
      StepsN Δ Φ n e2 σ2 e3 σ3 →
      StepsN Δ Φ (n + 1) e1 σ1 e3 σ3

private theorem steps_to_stepsN {Δ : AdtEnv} {Φ : FunEnv} {e1 e2 : Expr} {σ1 σ2 : Store}
    (h : Steps Δ Φ e1 σ1 e2 σ2) : ∃ n, StepsN Δ Φ n e1 σ1 e2 σ2 := by
  induction h with
  | refl => exact ⟨0, .zero _ _⟩
  | trans hs _ ih => rcases ih with ⟨n, hn⟩; exact ⟨n + 1, .succ hs hn⟩

private theorem stepsN_to_steps {Δ : AdtEnv} {Φ : FunEnv} {n : Nat} {e1 e2 : Expr} {σ1 σ2 : Store}
    (h : StepsN Δ Φ n e1 σ1 e2 σ2) : Steps Δ Φ e1 σ1 e2 σ2 := by
  induction h with
  | zero => exact .refl _ _
  | succ hs _ ih => exact .trans hs ih

private theorem activeCtx_stepsN_decomp {Δ : AdtEnv} {Φ : FunEnv} {K : Expr → Expr}
    (hK : IsActiveCtx Δ K) {n : Nat} {x out : Expr} {s s' : Store} (hout : IsTerminal out)
    (h : StepsN Δ Φ n (K x) s out s') :
    (∃ t, out = .trap t ∧ Steps Δ Φ x s (.trap t) s') ∨
    (∃ v sm k, k ≤ n ∧ IsValue v ∧ Steps Δ Φ x s v sm ∧ StepsN Δ Φ k (K v) sm out s') := by
  generalize heq : K x = kx at h
  induction h generalizing x with
  | zero _ s0 =>
    subst heq
    by_cases htx : IsTerminal x
    · rcases htx with hv | ⟨t, rfl⟩
      · exact Or.inr ⟨x, s0, 0, Nat.le_refl _, hv, .refl _ _, .zero _ _⟩
      · rcases steps_terminal_det (Steps.refl (K (.trap t)) s0) hout (hK.trap Φ t s0) (Or.inr ⟨t, rfl⟩) with ⟨hout_eq, _⟩
        exact Or.inl ⟨t, hout_eq, .refl _ _⟩
    · exact False.elim (hK.notTerm htx hout)
  | @succ m _ _ _ s0 _ _ hs hrest ih =>
    subst heq
    by_cases htx : IsTerminal x
    · rcases htx with hv | ⟨t, rfl⟩
      · exact Or.inr ⟨x, s0, m + 1, Nat.le_refl _, hv, .refl _ _, .succ hs hrest⟩
      · rcases steps_terminal_det (.trans hs (stepsN_to_steps hrest)) hout (hK.trap Φ t s0) (Or.inr ⟨t, rfl⟩) with
          ⟨hout_eq, hs_eq⟩
        subst hs_eq
        exact Or.inl ⟨t, hout_eq, .refl _ _⟩
    · rcases hK.invert htx hs with ⟨x', rfl, hsx⟩
      rcases ih hout rfl with ⟨t, rfl, htr⟩ | ⟨v, sm, k, hkle, hv, hsv, hkv⟩
      · exact Or.inl ⟨t, rfl, .trans hsx htr⟩
      · exact Or.inr ⟨v, sm, k, Nat.le_trans hkle (Nat.le_succ m), hv, .trans hsx hsv, hkv⟩

private theorem while_obsEquiv_forward {Δ : AdtEnv} {Φ : FunEnv} {c1 c2 b1 b2 : Expr}
    (hc : ObsEquiv Δ Φ Φ c1 c2) (hb : ObsEquiv Δ Φ Φ b1 b2) :
    ∀ (fuel : Nat) {n : Nat} {σ σ' : Store} {out : Expr},
      n ≤ fuel → IsTerminal out → StepsN Δ Φ n (.while_ c1 b1) σ out σ' →
      Steps Δ Φ (.while_ c2 b2) σ out σ'
  | 0, _, _, _, _, hle, hout, hn => by
    have hz : _ = 0 := Nat.eq_zero_of_le_zero hle
    subst hz
    cases hn
    cases hout with
    | inl hv => cases hv
    | inr htr => rcases htr with ⟨_, h⟩; cases h
  | fuel + 1, _, σ, σ', out, hle, hout, hn => by
    cases hn with
    | zero =>
      cases hout with
      | inl hv => cases hv
      | inr htr => rcases htr with ⟨_, h⟩; cases h
    | @succ m _ _ _ _ _ _ hs hrest =>
      cases hs with
      | whileUnfold =>
        have hle_m : m ≤ fuel := Nat.le_of_succ_le_succ hle
        rcases activeCtx_stepsN_decomp (isActiveCtx_ifCond Δ (.block [b1, .while_ c1 b1]) (.lit .unit)) hout hrest with
          ⟨t, rfl, htr_c1⟩ | ⟨vc, sm1, k1, hk1, hvc, hs_c1, hk_if⟩
        · have htr_c2 := (hc σ σ' (.trap t) (Or.inr ⟨t, rfl⟩)).mp htr_c1
          exact .trans .whileUnfold
            (Steps.append (Steps.liftCongr _ (fun hs => .ifStep hs) htr_c2) (.single .ifTrap))
        · have hs_c2 := (hc σ sm1 vc (Or.inl hvc)).mp hs_c1
          cases hk_if with
          | zero => cases hout with | inl hv => cases hv | inr htr => rcases htr with ⟨_, h⟩; cases h
          | @succ m2 _ _ _ _ _ _ hs_if hrest2 =>
            cases hs_if with
            | ifStep hs_vc => exact False.elim (isValue_no_step hvc hs_vc)
            | ifTrap => cases hvc
            | ifFalse =>
              rcases steps_terminal_det (stepsN_to_steps hrest2) hout (.refl _ _) (Or.inl (.lit .unit)) with ⟨rfl, rfl⟩
              exact .trans .whileUnfold
                (Steps.append (Steps.liftCongr _ (fun hs => .ifStep hs) hs_c2) (.single .ifFalse))
            | ifTrue =>
              rcases activeCtx_stepsN_decomp (isActiveCtx_blockHead Δ (.while_ c1 b1) []) hout hrest2 with
                ⟨t, rfl, htr_b1⟩ | ⟨vb, sm2, k2, hk2, hvb, hs_b1, hk_blk⟩
              · have htr_b2 := (hb sm1 σ' (.trap t) (Or.inr ⟨t, rfl⟩)).mp htr_b1
                exact .trans .whileUnfold
                  (Steps.append (Steps.liftCongr _ (fun hs => .ifStep hs) hs_c2)
                    (.trans .ifTrue
                      (Steps.append (Steps.liftCongr _ (fun hs => .blockConsStep hs) htr_b2)
                        (.single .blockConsTrap))))
              · have hs_b2 := (hb sm1 sm2 vb (Or.inl hvb)).mp hs_b1
                cases hk_blk with
                | zero => cases hout with | inl hv => cases hv | inr htr => rcases htr with ⟨_, h⟩; cases h
                | @succ m3 _ _ _ _ _ _ hs_blk1 hk_blk2 =>
                  cases hs_blk1 with
                  | blockConsStep hs_vb => exact False.elim (isValue_no_step hvb hs_vb)
                  | blockConsTrap => cases hvb
                  | blockConsVal _ =>
                    cases hk_blk2 with
                    | zero => cases hout with | inl hv => cases hv | inr htr => rcases htr with ⟨_, h⟩; cases h
                    | @succ m4 _ _ _ _ _ _ hs_blk2 hk_w =>
                      cases hs_blk2 with
                      | blockSingle =>
                        have hm4_le : m4 ≤ fuel := by omega
                        have hw2 := while_obsEquiv_forward hc hb fuel hm4_le hout hk_w
                        exact .trans .whileUnfold
                          (Steps.append (Steps.liftCongr _ (fun hs => .ifStep hs) hs_c2)
                            (.trans .ifTrue
                              (Steps.append (Steps.liftCongr _ (fun hs => .blockConsStep hs) hs_b2)
                                (.trans (.blockConsVal hvb) (.trans .blockSingle hw2)))))

theorem while_obsEquiv_congr {Δ : AdtEnv} {Φ : FunEnv} {c1 c2 b1 b2 : Expr}
    (hc : ObsEquiv Δ Φ Φ c1 c2) (hb : ObsEquiv Δ Φ Φ b1 b2) :
    ObsEquiv Δ Φ Φ (.while_ c1 b1) (.while_ c2 b2) := by
  intro σ σ' out hout
  constructor
  · intro h1
    rcases steps_to_stepsN h1 with ⟨n, hn⟩
    exact while_obsEquiv_forward hc hb n (Nat.le_refl n) hout hn
  · intro h2
    rcases steps_to_stepsN h2 with ⟨n, hn⟩
    exact while_obsEquiv_forward (ObsEquiv.symm hc) (ObsEquiv.symm hb) n (Nat.le_refl n) hout hn

private theorem activeList_obsEquiv_congr {Δ : AdtEnv} {Φ : FunEnv} (F : List Expr → Expr)
    (hF : ∀ (vs : List Expr), (∀ v ∈ vs, IsValue v) → ∀ (rest : List Expr),
      IsActiveCtx Δ (fun x => F (vs ++ x :: rest))) :
    ∀ {es1 es2 : List Expr} (vs : List Expr),
      (∀ v ∈ vs, IsValue v) →
      es1.length = es2.length →
      (∀ i (h1 : i < es1.length) (h2 : i < es2.length), ObsEquiv Δ Φ Φ es1[i] es2[i]) →
      ObsEquiv Δ Φ Φ (F (vs ++ es1)) (F (vs ++ es2))
  | [], [], _, _, _, _ => ObsEquiv.refl _ _ _
  | _ :: _, [], _, _, hlen, _ => by simp at hlen
  | [], _ :: _, _, _, hlen, _ => by simp at hlen
  | a1 :: r1, a2 :: r2, vs, hvs, hlen, heq => by
    have ha : ObsEquiv Δ Φ Φ a1 a2 := heq 0 (by simp) (by simp)
    have hstep1 : ObsEquiv Δ Φ Φ (F (vs ++ a1 :: r1)) (F (vs ++ a2 :: r1)) :=
      activeCtx_obsEquiv_congr (hF vs hvs r1) ha
    refine ObsEquiv.trans hstep1 ?_
    intro σ σ' out hout
    rw [activeCtx_steps_terminal_iff (hF vs hvs r1) hout,
        activeCtx_steps_terminal_iff (hF vs hvs r2) hout]
    have hrest : ∀ v, IsValue v → ObsEquiv Δ Φ Φ (F ((vs ++ [v]) ++ r1)) (F ((vs ++ [v]) ++ r2)) := by
      intro v hv
      apply activeList_obsEquiv_congr F hF (vs ++ [v])
      · intro w hw
        rcases List.mem_append.mp hw with hw1 | hw2
        · exact hvs w hw1
        · simp at hw2; subst hw2; exact hv
      · simp at hlen; exact hlen
      · intro i hi1 hi2
        exact heq (i + 1) (Nat.succ_lt_succ hi1) (Nat.succ_lt_succ hi2)
    constructor
    · rintro (⟨t, rfl, htr⟩ | ⟨v, sm, hv, hsv, hkv⟩)
      · exact Or.inl ⟨t, rfl, htr⟩
      · refine Or.inr ⟨v, sm, hv, hsv, ?_⟩
        have hkv' : Steps Δ Φ (F ((vs ++ [v]) ++ r1)) sm out σ' := by simpa [List.append_assoc] using hkv
        have hkv2 := ((hrest v hv) sm σ' out hout).mp hkv'
        simpa [List.append_assoc] using hkv2
    · rintro (⟨t, rfl, htr⟩ | ⟨v, sm, hv, hsv, hkv⟩)
      · exact Or.inl ⟨t, rfl, htr⟩
      · refine Or.inr ⟨v, sm, hv, hsv, ?_⟩
        have hkv' : Steps Δ Φ (F ((vs ++ [v]) ++ r2)) sm out σ' := by simpa [List.append_assoc] using hkv
        have hkv1 := ((hrest v hv) sm σ' out hout).mpr hkv'
        simpa [List.append_assoc] using hkv1

def lookupSubstEnv (x : Ident) : List (Ident × Expr) → Option Expr
  | [] => none
  | (k, v) :: r => if x == k then some v else lookupSubstEnv x r

def lookupRename : List (Ident × Ident) → Ident → Ident
  | [], x => x
  | (k, y) :: r, x => if x == k then y else lookupRename r x

theorem lookupSubstEnv_isSome_val_cl {x : Ident} {v : Expr} {env : List (Ident × Expr)}
    (henv : ∀ p ∈ env, IsValue p.2 ∧ freeVars p.2 = [])
    (hlu : lookupSubstEnv x env = some v) : IsValue v ∧ freeVars v = [] := by
  induction env with
  | nil => simp [lookupSubstEnv] at hlu
  | cons p r ih =>
    rcases p with ⟨k, w⟩
    simp only [lookupSubstEnv] at hlu
    split at hlu
    · injection hlu with hlu; subst hlu; exact henv (k, w) (List.mem_cons_self ..)
    · exact ih (fun q hq => henv q (List.mem_cons_of_mem _ hq)) hlu

theorem lookupSubstEnv_filter_true {z : Ident} {env : List (Ident × Expr)} {pred : Ident × Expr → Bool}
    (hp : ∀ p ∈ env, (z == p.1) = true → pred p = true) :
    lookupSubstEnv z (env.filter pred) = lookupSubstEnv z env := by
  induction env with
  | nil => rfl
  | cons p r ih =>
    rcases p with ⟨k, v⟩
    have ihr := ih (fun q hq => hp q (List.mem_cons_of_mem _ hq))
    by_cases hzk : (z == k) = true
    · have hpk : pred (k, v) = true := hp (k, v) (List.mem_cons_self ..) hzk
      simp only [List.filter, hpk, lookupSubstEnv, hzk, ↓reduceIte]
    · simp only [Bool.not_eq_true] at hzk
      simp only [List.filter]
      cases hpk : pred (k, v)
      · simpa [lookupSubstEnv, hzk] using ihr
      · simpa [lookupSubstEnv, hzk] using ihr

theorem lookupSubstEnv_filter_false {z : Ident} {env : List (Ident × Expr)} {pred : Ident × Expr → Bool}
    (hp : ∀ p ∈ env, (z == p.1) = true → pred p = false) :
    lookupSubstEnv z (env.filter pred) = none := by
  induction env with
  | nil => rfl
  | cons p r ih =>
    rcases p with ⟨k, v⟩
    have ihr := ih (fun q hq => hp q (List.mem_cons_of_mem _ hq))
    by_cases hzk : (z == k) = true
    · have hpk : pred (k, v) = false := hp (k, v) (List.mem_cons_self ..) hzk
      simpa [List.filter, hpk] using ihr
    · simp only [Bool.not_eq_true] at hzk
      simp only [List.filter]
      cases hpk : pred (k, v)
      · exact ihr
      · simpa [lookupSubstEnv, hzk] using ihr

private theorem substMany_closed_self (env : List (Ident × Expr)) {v : Expr} (hv : freeVars v = []) :
    substMany env v = v := by
  induction env with
  | nil => rfl
  | cons p r ih =>
    rcases p with ⟨k, w⟩
    have hsub : subst k w v = v := subst_not_mem_freeVars v (by rw [hv]; intro h; cases h)
    rw [substMany, hsub, ih]

theorem substMany_var_lookup {env : List (Ident × Expr)}
    (hcl : ∀ p ∈ env, freeVars p.2 = []) (x : Ident) :
    substMany env (.var x) = match lookupSubstEnv x env with
      | some v => v
      | none => .var x := by
  induction env with
  | nil => rfl
  | cons p r ih =>
    rcases p with ⟨k, v⟩
    simp only [substMany, subst, lookupSubstEnv]
    split
    · exact substMany_closed_self r (hcl (k, v) (List.mem_cons_self ..))
    · exact ih (fun q hq => hcl q (List.mem_cons_of_mem _ hq))

def substManyList (env : List (Ident × Expr)) (es : List Expr) : List Expr :=
  es.map (substMany env)

def substManyArms (env : List (Ident × Expr)) (arms : List (Pat × Expr)) : List (Pat × Expr) :=
  arms.map (fun a => (a.1, substMany (env.filter (fun p => !((patBoundNames a.1).contains p.1))) a.2))

private theorem substList_map_eq (k : Ident) (v : Expr) (es : List Expr) :
    substList k v es = es.map (subst k v) := by
  induction es with
  | nil => rfl
  | cons e r ih => simp [substList, ih]

private theorem substMany_tuple_eq (env : List (Ident × Expr)) (es : List Expr) :
    substMany env (.tuple es) = .tuple (substManyList env es) := by
  induction env generalizing es with
  | nil => simp [substMany, substManyList]
  | cons p r ih =>
    rcases p with ⟨k, v⟩
    simp [substMany, subst, substList_map_eq, ih, substManyList, List.map_map, Function.comp]

private theorem substMany_block_eq (env : List (Ident × Expr)) (es : List Expr) :
    substMany env (.block es) = .block (substManyList env es) := by
  induction env generalizing es with
  | nil => simp [substMany, substManyList]
  | cons p r ih =>
    rcases p with ⟨k, v⟩
    simp [substMany, subst, substList_map_eq, ih, substManyList, List.map_map, Function.comp]

private theorem substMany_makeData_eq (env : List (Ident × Expr)) (adt : Ident) (tag : Nat) (es : List Expr) :
    substMany env (.makeData adt tag es) = .makeData adt tag (substManyList env es) := by
  induction env generalizing es with
  | nil => simp [substMany, substManyList]
  | cons p r ih =>
    rcases p with ⟨k, v⟩
    simp [substMany, subst, substList_map_eq, ih, substManyList, List.map_map, Function.comp]

private theorem substMany_concPrim_eq (env : List (Ident × Expr)) (op : ConcPrim) (es : List Expr) :
    substMany env (.concPrim op es) = .concPrim op (substManyList env es) := by
  induction env generalizing es with
  | nil => simp [substMany, substManyList]
  | cons p r ih =>
    rcases p with ⟨k, v⟩
    simp [substMany, subst, substList_map_eq, ih, substManyList, List.map_map, Function.comp]

private theorem substMany_apply_eq (env : List (Ident × Expr)) (fn : Expr) (args : List Expr) :
    substMany env (.apply fn args) = .apply (substMany env fn) (substManyList env args) := by
  induction env generalizing fn args with
  | nil => simp [substMany, substManyList]
  | cons p r ih =>
    rcases p with ⟨k, v⟩
    simp [substMany, subst, substList_map_eq, ih, substManyList, List.map_map, Function.comp]

private theorem substMany_applyDir_eq (env : List (Ident × Expr)) (nm : Ident) (args : List Expr) :
    substMany env (.applyDir nm args) = .applyDir nm (substManyList env args) := by
  induction env generalizing args with
  | nil => simp [substMany, substManyList]
  | cons p r ih =>
    rcases p with ⟨k, v⟩
    simp [substMany, subst, substList_map_eq, ih, substManyList, List.map_map, Function.comp]

private theorem substMany_bin_eq (env : List (Ident × Expr)) (op : BinOp) (a b : Expr) :
    substMany env (.bin op a b) = .bin op (substMany env a) (substMany env b) := by
  induction env generalizing a b with
  | nil => rfl
  | cons p r ih => rcases p with ⟨k, v⟩; simp [substMany, subst, ih]

private theorem substMany_un_eq (env : List (Ident × Expr)) (op : UnOp) (a : Expr) :
    substMany env (.un op a) = .un op (substMany env a) := by
  induction env generalizing a with
  | nil => rfl
  | cons p r ih => rcases p with ⟨k, v⟩; simp [substMany, subst, ih]

private theorem substMany_if_eq (env : List (Ident × Expr)) (c t e : Expr) :
    substMany env (.if_ c t e) = .if_ (substMany env c) (substMany env t) (substMany env e) := by
  induction env generalizing c t e with
  | nil => rfl
  | cons p r ih => rcases p with ⟨k, v⟩; simp [substMany, subst, ih]

private theorem substMany_while_eq (env : List (Ident × Expr)) (c b : Expr) :
    substMany env (.while_ c b) = .while_ (substMany env c) (substMany env b) := by
  induction env generalizing c b with
  | nil => rfl
  | cons p r ih => rcases p with ⟨k, v⟩; simp [substMany, subst, ih]

private theorem substMany_getTag_eq (env : List (Ident × Expr)) (a : Expr) :
    substMany env (.getTag a) = .getTag (substMany env a) := by
  induction env generalizing a with
  | nil => rfl
  | cons p r ih => rcases p with ⟨k, v⟩; simp [substMany, subst, ih]

private theorem substMany_cellNew_eq (env : List (Ident × Expr)) (a : Expr) :
    substMany env (.cellNew a) = .cellNew (substMany env a) := by
  induction env generalizing a with
  | nil => rfl
  | cons p r ih => rcases p with ⟨k, v⟩; simp [substMany, subst, ih]

private theorem substMany_cellGet_eq (env : List (Ident × Expr)) (a : Expr) :
    substMany env (.cellGet a) = .cellGet (substMany env a) := by
  induction env generalizing a with
  | nil => rfl
  | cons p r ih => rcases p with ⟨k, v⟩; simp [substMany, subst, ih]

private theorem substMany_cellSet_eq (env : List (Ident × Expr)) (a b : Expr) :
    substMany env (.cellSet a b) = .cellSet (substMany env a) (substMany env b) := by
  induction env generalizing a b with
  | nil => rfl
  | cons p r ih => rcases p with ⟨k, v⟩; simp [substMany, subst, ih]

private theorem substMany_spawn_eq (env : List (Ident × Expr)) (a : Expr) :
    substMany env (.spawn a) = .spawn (substMany env a) := by
  induction env generalizing a with
  | nil => rfl
  | cons p r ih => rcases p with ⟨k, v⟩; simp [substMany, subst, ih]

private theorem substMany_await_eq (env : List (Ident × Expr)) (a : Expr) :
    substMany env (.await a) = .await (substMany env a) := by
  induction env generalizing a with
  | nil => rfl
  | cons p r ih => rcases p with ⟨k, v⟩; simp [substMany, subst, ih]

private theorem substMany_let_eq (env : List (Ident × Expr)) (y : Ident) (a b : Expr) :
    substMany env (.let_ y a b) =
      .let_ y (substMany env a) (substMany (env.filter (fun p => !(y == p.1))) b) := by
  induction env generalizing a b with
  | nil => rfl
  | cons p r ih =>
    rcases p with ⟨k, v⟩
    simp only [substMany, subst, List.filter]
    cases hyk : (y == k) <;> simp [ih, substMany]

private theorem substMany_lam_eq (env : List (Ident × Expr)) (m : Mode) (ps : List (Ident × Ty))
    (ret : Ty) (b : Expr) :
    substMany env (.lam m ps ret b) =
      .lam m ps ret (substMany (env.filter (fun q => !(ps.any (fun p => p.1 == q.1)))) b) := by
  induction env generalizing b with
  | nil => rfl
  | cons p r ih =>
    rcases p with ⟨k, v⟩
    simp only [substMany, subst, List.filter]
    cases hpk : ps.any (fun q => q.1 == k) <;> simp [ih, substMany]

private theorem substArms_map_eq (k : Ident) (v : Expr) (arms : List (Pat × Expr)) :
    substArms k v arms =
      arms.map (fun a => (a.1, if (patBoundNames a.1).contains k then a.2 else subst k v a.2)) := by
  induction arms with
  | nil => rfl
  | cons a r ih => rcases a with ⟨p, b⟩; simp [substArms, ih]

private theorem substMany_match_eq (env : List (Ident × Expr)) (s : Expr) (arms : List (Pat × Expr)) :
    substMany env (.match_ s arms) = .match_ (substMany env s) (substManyArms env arms) := by
  induction env generalizing s arms with
  | nil =>
    simp only [substMany, substManyArms]
    have hid : arms.map (fun a => (a.1, a.2)) = arms := by
      induction arms with | nil => rfl | cons a r ih => cases a; simp [ih]
    exact congrArg (Expr.match_ s) hid.symm
  | cons p r ih =>
    rcases p with ⟨k, v⟩
    simp only [substMany, subst, ih, substArms_map_eq, substManyArms, List.map_map]
    congr 1
    apply List.map_congr_left
    intro a _
    rcases a with ⟨pat, body⟩
    simp only [Function.comp, List.filter]
    cases hck : (patBoundNames pat).contains k <;> simp [substMany]

private theorem substMany_atom_eq (env : List (Ident × Expr)) :
    (∀ l, substMany env (.lit l) = .lit l) ∧
    (∀ l, substMany env (.loc l) = .loc l) ∧
    (∀ t, substMany env (.taskRef t) = .taskRef t) ∧
    (∀ k n, substMany env (.syncRef k n) = .syncRef k n) ∧
    (∀ t, substMany env (.trap t) = .trap t) := by
  induction env with
  | nil => exact ⟨fun _ => rfl, fun _ => rfl, fun _ => rfl, fun _ _ => rfl, fun _ => rfl⟩
  | cons p r ih =>
    rcases p with ⟨k, v⟩
    exact ⟨fun l => ih.1 l, fun l => ih.2.1 l, fun t => ih.2.2.1 t,
           fun k' n => ih.2.2.2.1 k' n, fun t => ih.2.2.2.2 t⟩

mutual
theorem substMany_congr_lookup {enva envb : List (Ident × Expr)}
    (ha : ∀ p ∈ enva, freeVars p.2 = []) (hb : ∀ p ∈ envb, freeVars p.2 = []) :
    (e : Expr) → (∀ z ∈ freeVars e, lookupSubstEnv z enva = lookupSubstEnv z envb) →
    substMany enva e = substMany envb e
  | .lit l, _ => by rw [(substMany_atom_eq enva).1 l, (substMany_atom_eq envb).1 l]
  | .loc l, _ => by rw [(substMany_atom_eq enva).2.1 l, (substMany_atom_eq envb).2.1 l]
  | .taskRef t, _ => by rw [(substMany_atom_eq enva).2.2.1 t, (substMany_atom_eq envb).2.2.1 t]
  | .syncRef k n, _ => by rw [(substMany_atom_eq enva).2.2.2.1 k n, (substMany_atom_eq envb).2.2.2.1 k n]
  | .trap t, _ => by rw [(substMany_atom_eq enva).2.2.2.2 t, (substMany_atom_eq envb).2.2.2.2 t]
  | .var z, hlu => by
    rw [substMany_var_lookup ha z, substMany_var_lookup hb z, hlu z (by simp [freeVars])]
  | .tuple es, hlu => by
    rw [substMany_tuple_eq, substMany_tuple_eq]
    exact congrArg Expr.tuple (substManyList_congr_lookup ha hb es hlu)
  | .block es, hlu => by
    rw [substMany_block_eq, substMany_block_eq]
    exact congrArg Expr.block (substManyList_congr_lookup ha hb es hlu)
  | .makeData adt tag es, hlu => by
    rw [substMany_makeData_eq, substMany_makeData_eq]
    exact congrArg (Expr.makeData adt tag) (substManyList_congr_lookup ha hb es hlu)
  | .concPrim op es, hlu => by
    rw [substMany_concPrim_eq, substMany_concPrim_eq]
    exact congrArg (Expr.concPrim op) (substManyList_congr_lookup ha hb es hlu)
  | .apply fn args, hlu => by
    rw [substMany_apply_eq, substMany_apply_eq]
    have h1 := substMany_congr_lookup ha hb fn (fun z hz => hlu z (by simp [freeVars, hz]))
    have h2 := substManyList_congr_lookup ha hb args (fun z hz => hlu z (by simp [freeVars, hz]))
    rw [h1, h2]
  | .applyDir nm args, hlu => by
    rw [substMany_applyDir_eq, substMany_applyDir_eq]
    exact congrArg (Expr.applyDir nm) (substManyList_congr_lookup ha hb args hlu)
  | .bin op a b, hlu => by
    rw [substMany_bin_eq, substMany_bin_eq,
        substMany_congr_lookup ha hb a (fun z hz => hlu z (by simp [freeVars, hz])),
        substMany_congr_lookup ha hb b (fun z hz => hlu z (by simp [freeVars, hz]))]
  | .un op a, hlu => by
    rw [substMany_un_eq, substMany_un_eq, substMany_congr_lookup ha hb a hlu]
  | .if_ c t e, hlu => by
    rw [substMany_if_eq, substMany_if_eq,
        substMany_congr_lookup ha hb c (fun z hz => hlu z (by simp [freeVars, hz])),
        substMany_congr_lookup ha hb t (fun z hz => hlu z (by simp [freeVars, hz])),
        substMany_congr_lookup ha hb e (fun z hz => hlu z (by simp [freeVars, hz]))]
  | .while_ c b, hlu => by
    rw [substMany_while_eq, substMany_while_eq,
        substMany_congr_lookup ha hb c (fun z hz => hlu z (by simp [freeVars, hz])),
        substMany_congr_lookup ha hb b (fun z hz => hlu z (by simp [freeVars, hz]))]
  | .getTag a, hlu => by
    rw [substMany_getTag_eq, substMany_getTag_eq, substMany_congr_lookup ha hb a hlu]
  | .cellNew a, hlu => by
    rw [substMany_cellNew_eq, substMany_cellNew_eq, substMany_congr_lookup ha hb a hlu]
  | .cellGet a, hlu => by
    rw [substMany_cellGet_eq, substMany_cellGet_eq, substMany_congr_lookup ha hb a hlu]
  | .cellSet a b, hlu => by
    rw [substMany_cellSet_eq, substMany_cellSet_eq,
        substMany_congr_lookup ha hb a (fun z hz => hlu z (by simp [freeVars, hz])),
        substMany_congr_lookup ha hb b (fun z hz => hlu z (by simp [freeVars, hz]))]
  | .spawn a, hlu => by
    rw [substMany_spawn_eq, substMany_spawn_eq, substMany_congr_lookup ha hb a hlu]
  | .await a, hlu => by
    rw [substMany_await_eq, substMany_await_eq, substMany_congr_lookup ha hb a hlu]
  | .let_ y a b, hlu => by
    rw [substMany_let_eq, substMany_let_eq]
    have h1 := substMany_congr_lookup ha hb a (fun z hz => hlu z (by simp [freeVars, hz]))
    have ha_f : ∀ p ∈ enva.filter (fun p => !(y == p.1)), freeVars p.2 = [] :=
      fun p hp => ha p (List.mem_filter.mp hp).1
    have hb_f : ∀ p ∈ envb.filter (fun p => !(y == p.1)), freeVars p.2 = [] :=
      fun p hp => hb p (List.mem_filter.mp hp).1
    have h2 := substMany_congr_lookup ha_f hb_f b (by
      intro z hz
      by_cases hzy : z = y
      · subst hzy
        rw [lookupSubstEnv_filter_false (fun p _ heq => by simp [heq]),
            lookupSubstEnv_filter_false (fun p _ heq => by simp [heq])]
      · have hne : (y == z) = false := beq_false_of_ne (Ne.symm hzy)
        rw [lookupSubstEnv_filter_true (fun p _ heq => by have := eq_of_beq heq; subst this; simp [hne]),
            lookupSubstEnv_filter_true (fun p _ heq => by have := eq_of_beq heq; subst this; simp [hne])]
        exact hlu z (by simp [freeVars, hz, hzy]))
    rw [h1, h2]
  | .lam m ps ret b, hlu => by
    rw [substMany_lam_eq, substMany_lam_eq]
    have ha_f : ∀ p ∈ enva.filter (fun q => !(ps.any (fun p => p.1 == q.1))), freeVars p.2 = [] :=
      fun p hp => ha p (List.mem_filter.mp hp).1
    have hb_f : ∀ p ∈ envb.filter (fun q => !(ps.any (fun p => p.1 == q.1))), freeVars p.2 = [] :=
      fun p hp => hb p (List.mem_filter.mp hp).1
    congr 1
    exact substMany_congr_lookup ha_f hb_f b (by
      intro z hz
      cases hps : ps.any (fun p => p.1 == z)
      · rw [lookupSubstEnv_filter_true (fun q _ heq => by have := eq_of_beq heq; subst this; simp [hps]),
            lookupSubstEnv_filter_true (fun q _ heq => by have := eq_of_beq heq; subst this; simp [hps])]
        exact hlu z (by simp [freeVars, hz, hps])
      · rw [lookupSubstEnv_filter_false (fun q _ heq => by have := eq_of_beq heq; subst this; simp [hps]),
            lookupSubstEnv_filter_false (fun q _ heq => by have := eq_of_beq heq; subst this; simp [hps])])
  | .match_ s arms, hlu => by
    rw [substMany_match_eq, substMany_match_eq,
        substMany_congr_lookup ha hb s (fun z hz => hlu z (by simp [freeVars, hz])),
        substManyArms_congr_lookup ha hb arms (fun z hz => hlu z (by simp [freeVars, hz]))]
termination_by e => sizeOf e

theorem substManyList_congr_lookup {enva envb : List (Ident × Expr)}
    (ha : ∀ p ∈ enva, freeVars p.2 = []) (hb : ∀ p ∈ envb, freeVars p.2 = []) :
    (es : List Expr) → (∀ z ∈ freeVarsList es, lookupSubstEnv z enva = lookupSubstEnv z envb) →
    substManyList enva es = substManyList envb es
  | [], _ => rfl
  | e :: r, hlu => by
    have h1 := substMany_congr_lookup ha hb e (fun z hz => hlu z (by simp [freeVarsList, hz]))
    have h2 := substManyList_congr_lookup ha hb r (fun z hz => hlu z (by simp [freeVarsList, hz]))
    simp only [substManyList, List.map] at h2 ⊢
    rw [h1, h2]
termination_by es => sizeOf es

theorem substManyArms_congr_lookup {enva envb : List (Ident × Expr)}
    (ha : ∀ p ∈ enva, freeVars p.2 = []) (hb : ∀ p ∈ envb, freeVars p.2 = []) :
    (arms : List (Pat × Expr)) → (∀ z ∈ freeVarsArms arms, lookupSubstEnv z enva = lookupSubstEnv z envb) →
    substManyArms enva arms = substManyArms envb arms
  | [], _ => rfl
  | (pat, body) :: r, hlu => by
    have ha_f : ∀ p ∈ enva.filter (fun q => !((patBoundNames pat).contains q.1)), freeVars p.2 = [] :=
      fun p hp => ha p (List.mem_filter.mp hp).1
    have hb_f : ∀ p ∈ envb.filter (fun q => !((patBoundNames pat).contains q.1)), freeVars p.2 = [] :=
      fun p hp => hb p (List.mem_filter.mp hp).1
    have hbody := substMany_congr_lookup ha_f hb_f body (by
      intro z hz
      cases hbd : (patBoundNames pat).contains z
      · rw [lookupSubstEnv_filter_true (fun q _ heq => by have := eq_of_beq heq; subst this; rw [hbd]; rfl),
            lookupSubstEnv_filter_true (fun q _ heq => by have := eq_of_beq heq; subst this; rw [hbd]; rfl)]
        exact hlu z (by simp only [freeVarsArms, List.mem_append, List.mem_filter]; exact Or.inl ⟨hz, by rw [hbd]; rfl⟩)
      · rw [lookupSubstEnv_filter_false (fun q _ heq => by have := eq_of_beq heq; subst this; rw [hbd]; rfl),
            lookupSubstEnv_filter_false (fun q _ heq => by have := eq_of_beq heq; subst this; rw [hbd]; rfl)])
    have hr := substManyArms_congr_lookup ha hb r
      (fun z hz => hlu z (by simp only [freeVarsArms, List.mem_append]; exact Or.inr hz))
    simp only [substManyArms, List.map] at hr ⊢
    rw [hbody, hr]
termination_by arms => sizeOf arms
end

theorem substMany_append_eq (env1 env2 : List (Ident × Expr)) (e : Expr) :
    substMany (env1 ++ env2) e = substMany env2 (substMany env1 e) := by
  induction env1 generalizing e with
  | nil => rfl
  | cons p r ih => simp [substMany, ih]

theorem subst_substMany_filter_eq (x : Ident) {va : Expr} (hva : freeVars va = [])
    {env : List (Ident × Expr)} (henv : ∀ p ∈ env, freeVars p.2 = []) (b : Expr) :
    subst x va (substMany (env.filter (fun p => !(x == p.1))) b) =
      substMany ((x, va) :: env) b := by
  have h1 : subst x va (substMany (env.filter (fun p => !(x == p.1))) b) =
      substMany (env.filter (fun p => !(x == p.1)) ++ [(x, va)]) b := by
    rw [substMany_append_eq]; rfl
  rw [h1]
  apply substMany_congr_lookup
  · intro p hp
    rcases List.mem_append.mp hp with hp1 | hp2
    · exact henv p (List.mem_filter.mp hp1).1
    · simp at hp2; rcases hp2 with ⟨_, rfl⟩; exact hva
  · intro p hp
    rcases List.mem_cons.mp hp with rfl | hp2
    · exact hva
    · exact henv p hp2
  · intro z _
    have hlu_app : ∀ (l1 l2 : List (Ident × Expr)),
        lookupSubstEnv z (l1 ++ l2) = match lookupSubstEnv z l1 with
          | some w => some w
          | none => lookupSubstEnv z l2 := by
      intro l1 l2
      induction l1 with
      | nil => rfl
      | cons q r ih =>
        rcases q with ⟨k, w⟩
        simp only [List.cons_append, lookupSubstEnv]
        split
        · rfl
        · exact ih
    rw [hlu_app]
    by_cases hzx : (z == x) = true
    · have heq := eq_of_beq hzx; subst heq
      rw [lookupSubstEnv_filter_false (fun p _ heq => by simp [heq])]
      simp [lookupSubstEnv]
    · simp only [Bool.not_eq_true] at hzx
      have hne : (x == z) = false := beq_false_of_ne (fun h => by subst h; simp at hzx)
      rw [lookupSubstEnv_filter_true (fun p _ heq => by have := eq_of_beq heq; subst this; simp [hne])]
      simp [lookupSubstEnv, hzx]
      cases lookupSubstEnv z env <;> rfl

mutual
theorem matchPat_fst_eq_patBoundNames :
    (p : Pat) → {v : Expr} → {binds : List (Ident × Expr)} →
      matchPat p v = some binds → binds.map Prod.fst = patBoundNames p
  | .wild, _, _, hm => by simp [matchPat] at hm; subst hm; simp [patBoundNames]
  | .var x, _, _, hm => by simp [matchPat] at hm; subst hm; simp [patBoundNames]
  | .lit _, v, _, hm => by
    cases v <;> simp [matchPat] at hm
    rcases hm with ⟨_, rfl⟩; simp [patBoundNames]
  | .tuple ps, v, _, hm => by
    cases v <;> simp [matchPat] at hm
    simpa [patBoundNames] using matchPats_fst_eq_patBoundNames ps hm
  | .ctor _ _ ps, v, _, hm => by
    cases v <;> simp [matchPat] at hm
    simpa [patBoundNames] using matchPats_fst_eq_patBoundNames ps hm.2
termination_by p => sizeOf p

theorem matchPats_fst_eq_patBoundNames :
    (ps : List Pat) → {vs : List Expr} → {binds : List (Ident × Expr)} →
      matchPats ps vs = some binds →
      binds.map Prod.fst = ps.foldr (fun p acc => patBoundNames p ++ acc) []
  | [], vs, _, hm => by cases vs <;> simp [matchPats] at hm; subst hm; rfl
  | p :: pr, vs, _, hm => by
    cases vs with
    | nil => simp [matchPats] at hm
    | cons v vr =>
      simp only [matchPats] at hm
      cases h1 : matchPat p v <;> rw [h1] at hm
      · cases hm
      · cases h2 : matchPats pr vr <;> rw [h2] at hm
        · cases hm
        · injection hm with hm; subst hm
          simp [List.foldr, matchPat_fst_eq_patBoundNames p h1, matchPats_fst_eq_patBoundNames pr h2]
termination_by ps => sizeOf ps
end

theorem lookupSubstEnv_append (z : Ident) (l1 l2 : List (Ident × Expr)) :
    lookupSubstEnv z (l1 ++ l2) = match lookupSubstEnv z l1 with
      | some w => some w
      | none => lookupSubstEnv z l2 := by
  induction l1 with
  | nil => rfl
  | cons q r ih =>
    rcases q with ⟨k, w⟩
    simp only [List.cons_append, lookupSubstEnv]
    split
    · rfl
    · exact ih

theorem lookupSubstEnv_isSome_iff_contains (z : Ident) (l : List (Ident × Expr)) :
    (lookupSubstEnv z l).isSome = (l.map Prod.fst).contains z := by
  induction l with
  | nil => rfl
  | cons q r ih =>
    rcases q with ⟨k, w⟩
    simp only [lookupSubstEnv, List.map, List.contains_cons]
    cases hzk : (z == k) <;> simp [ih]

theorem substMany_binds_filter_eq {p : Pat} {binds env : List (Ident × Expr)}
    (hbinds : ∀ q ∈ binds, freeVars q.2 = [])
    (henv : ∀ q ∈ env, freeVars q.2 = [])
    (hfst : binds.map Prod.fst = patBoundNames p) (b : Expr) :
    substMany binds (substMany (env.filter (fun q => !((patBoundNames p).contains q.1))) b) =
      substMany (binds ++ env) b := by
  rw [← substMany_append_eq]
  apply substMany_congr_lookup
  · intro q hq
    rcases List.mem_append.mp hq with h1 | h2
    · exact henv q (List.mem_filter.mp h1).1
    · exact hbinds q h2
  · intro q hq
    rcases List.mem_append.mp hq with h1 | h2
    · exact hbinds q h1
    · exact henv q h2
  · intro z _
    rw [lookupSubstEnv_append, lookupSubstEnv_append]
    cases hcont : (patBoundNames p).contains z
    · rw [lookupSubstEnv_filter_true (fun q _ heq => by have := eq_of_beq heq; subst this; rw [hcont]; rfl)]
      have hnone : lookupSubstEnv z binds = none := by
        have his := lookupSubstEnv_isSome_iff_contains z binds
        rw [hfst, hcont] at his
        cases h : lookupSubstEnv z binds
        · rfl
        · rw [h] at his; simp at his
      rw [hnone]
      cases lookupSubstEnv z env <;> rfl
    · rw [lookupSubstEnv_filter_false (fun q _ heq => by have := eq_of_beq heq; subst this; rw [hcont]; rfl)]
      have hsome : ∃ w, lookupSubstEnv z binds = some w := by
        have his := lookupSubstEnv_isSome_iff_contains z binds
        rw [hfst, hcont] at his
        cases h : lookupSubstEnv z binds
        · rw [h] at his; simp at his
        · exact ⟨_, rfl⟩
      rcases hsome with ⟨w, hw⟩
      rw [hw]

theorem substMany_closed_freeVars_nil {env : List (Ident × Expr)}
    (henv : ∀ p ∈ env, freeVars p.2 = []) {e : Expr}
    (hdom : ∀ z ∈ freeVars e, (lookupSubstEnv z env).isSome = true) :
    freeVars (substMany env e) = [] := by
  induction env generalizing e with
  | nil =>
    apply List.eq_nil_iff_forall_not_mem.mpr
    intro z hz
    have := hdom z hz
    simp [lookupSubstEnv] at this
  | cons p r ih =>
    rcases p with ⟨k, v⟩
    apply ih (fun q hq => henv q (List.mem_cons_of_mem _ hq))
    intro z hz
    rcases subst_freeVars_subset k v (henv (k, v) (List.mem_cons_self ..)) e z hz with ⟨hne, hmem⟩
    have hd := hdom z hmem
    have hzk : (z == k) = false := beq_false_of_ne hne
    simpa [lookupSubstEnv, hzk] using hd

mutual
inductive PatAlphaRel : Pat → Pat → List (Ident × Ident) → Prop where
  | wild : PatAlphaRel .wild .wild []
  | lit (l : Lit) : PatAlphaRel (.lit l) (.lit l) []
  | var (x y : Ident) : PatAlphaRel (.var x) (.var y) [(x, y)]
  | tuple {ps1 ps2 : List Pat} {pairs : List (Ident × Ident)} :
      PatAlphaRelList ps1 ps2 pairs → PatAlphaRel (.tuple ps1) (.tuple ps2) pairs
  | ctor (adt : Ident) (tag : Nat) {ps1 ps2 : List Pat} {pairs : List (Ident × Ident)} :
      PatAlphaRelList ps1 ps2 pairs → PatAlphaRel (.ctor adt tag ps1) (.ctor adt tag ps2) pairs

inductive PatAlphaRelList : List Pat → List Pat → List (Ident × Ident) → Prop where
  | nil : PatAlphaRelList [] [] []
  | cons {p1 p2 : Pat} {r1 r2 : List Pat} {b1 b2 : List (Ident × Ident)} :
      PatAlphaRel p1 p2 b1 → PatAlphaRelList r1 r2 b2 →
      PatAlphaRelList (p1 :: r1) (p2 :: r2) (b1 ++ b2)
end

mutual
theorem patAlphaRel_boundNames :
    {p1 p2 : Pat} → {pairs : List (Ident × Ident)} →
      PatAlphaRel p1 p2 pairs →
      pairs.map Prod.fst = patBoundNames p1 ∧ pairs.map Prod.snd = patBoundNames p2
  | _, _, _, .wild => by simp [patBoundNames]
  | _, _, _, .lit _ => by simp [patBoundNames]
  | _, _, _, .var _ _ => by simp [patBoundNames]
  | _, _, _, .tuple hrl => by simpa [patBoundNames] using patAlphaRelList_boundNames hrl
  | _, _, _, .ctor _ _ hrl => by simpa [patBoundNames] using patAlphaRelList_boundNames hrl

theorem patAlphaRelList_boundNames :
    {ps1 ps2 : List Pat} → {pairs : List (Ident × Ident)} →
      PatAlphaRelList ps1 ps2 pairs →
      pairs.map Prod.fst = ps1.foldr (fun p acc => patBoundNames p ++ acc) [] ∧
      pairs.map Prod.snd = ps2.foldr (fun p acc => patBoundNames p ++ acc) []
  | _, _, _, .nil => ⟨rfl, rfl⟩
  | _, _, _, .cons hp hr => by
    rcases patAlphaRel_boundNames hp with ⟨h1, h2⟩
    rcases patAlphaRelList_boundNames hr with ⟨r1, r2⟩
    simp [List.map_append, List.foldr, h1, h2, r1, r2]
end

mutual
theorem patAlphaRel_matchPat :
    {p1 p2 : Pat} → {pairs : List (Ident × Ident)} →
      PatAlphaRel p1 p2 pairs → (v : Expr) →
      ((matchPat p1 v = none ∧ matchPat p2 v = none) ∨
       (∃ vs : List Expr, vs.length = pairs.length ∧
          matchPat p1 v = some ((pairs.map Prod.fst).zip vs) ∧
          matchPat p2 v = some ((pairs.map Prod.snd).zip vs)))
  | _, _, _, .wild, v => Or.inr ⟨[], rfl, rfl, rfl⟩
  | _, _, _, .var x y, v => Or.inr ⟨[v], rfl, rfl, rfl⟩
  | _, _, _, .lit l, v => by
    cases v with
    | lit l2 =>
      simp only [matchPat]
      cases (l == l2)
      · exact Or.inl ⟨rfl, rfl⟩
      · exact Or.inr ⟨[], rfl, rfl, rfl⟩
    | _ => exact Or.inl ⟨rfl, rfl⟩
  | _, _, _, .tuple hrl, v => by
    cases v with
    | tuple vs => simpa [matchPat] using patAlphaRelList_matchPats hrl vs
    | _ => exact Or.inl ⟨rfl, rfl⟩
  | _, _, _, .ctor adt tag hrl, v => by
    cases v with
    | makeData adt2 tag2 vs =>
      simp only [matchPat]
      cases (adt == adt2 && tag == tag2)
      · exact Or.inl ⟨rfl, rfl⟩
      · simpa using patAlphaRelList_matchPats hrl vs
    | _ => exact Or.inl ⟨rfl, rfl⟩

theorem patAlphaRelList_matchPats :
    {ps1 ps2 : List Pat} → {pairs : List (Ident × Ident)} →
      PatAlphaRelList ps1 ps2 pairs → (vs : List Expr) →
      ((matchPats ps1 vs = none ∧ matchPats ps2 vs = none) ∨
       (∃ ws : List Expr, ws.length = pairs.length ∧
          matchPats ps1 vs = some ((pairs.map Prod.fst).zip ws) ∧
          matchPats ps2 vs = some ((pairs.map Prod.snd).zip ws)))
  | _, _, _, .nil, vs => by
    cases vs with
    | nil => exact Or.inr ⟨[], rfl, rfl, rfl⟩
    | cons _ _ => exact Or.inl ⟨rfl, rfl⟩
  | _, _, _, @PatAlphaRelList.cons _ _ _ _ b1 b2 hp hr, vs => by
    cases vs with
    | nil => exact Or.inl ⟨rfl, rfl⟩
    | cons v vr =>
      simp only [matchPats]
      rcases patAlphaRel_matchPat hp v with ⟨hn1, hn2⟩ | ⟨ws1, hlen1, hs1, hs2⟩
      · rw [hn1, hn2]; exact Or.inl ⟨rfl, rfl⟩
      · rw [hs1, hs2]
        rcases patAlphaRelList_matchPats hr vr with ⟨rn1, rn2⟩ | ⟨ws2, hlen2, rs1, rs2⟩
        · rw [rn1, rn2]; exact Or.inl ⟨rfl, rfl⟩
        · rw [rs1, rs2]
          refine Or.inr ⟨ws1 ++ ws2, by simp [hlen1, hlen2], ?_, ?_⟩
          · rw [List.map_append, List.zip_append (by simp [hlen1])]
          · rw [List.map_append, List.zip_append (by simp [hlen1])]
end

/- General Alpha-Cloning + Post-Clone Simplification & Multi-Argument Direct Inlining Relation
   (`coCloneTerm` + `coOptTerm` singleton block unwrapping, dead `coExprIsPure` `let` elimination,
   `TmMakeCls` pure wrapper introduction, fresh `let`/`match` binder renaming, and N-ary direct
   `TmVar` inlining `coBuildCallArgsInline`). -/
mutual
inductive AlphaOptRel (Φ : FunEnv) : List (Ident × Ident) → Expr → Expr → Prop where
  | lit (ρ : List (Ident × Ident)) (l : Lit) : AlphaOptRel Φ ρ (.lit l) (.lit l)
  | var (ρ : List (Ident × Ident)) (x : Ident) :
      AlphaOptRel Φ ρ (.var x) (.var (lookupRename ρ x))
  | loc (ρ : List (Ident × Ident)) (l : Loc) : AlphaOptRel Φ ρ (.loc l) (.loc l)
  | taskRef (ρ : List (Ident × Ident)) (t : TaskId) : AlphaOptRel Φ ρ (.taskRef t) (.taskRef t)
  | syncRef (ρ : List (Ident × Ident)) (k : SyncKind) (n : Nat) :
      AlphaOptRel Φ ρ (.syncRef k n) (.syncRef k n)
  | trap (ρ : List (Ident × Ident)) (t : Trap) : AlphaOptRel Φ ρ (.trap t) (.trap t)
  | unwrapBlock1 {ρ : List (Ident × Ident)} {a1 e2 : Expr} :
      AlphaOptRel Φ ρ a1 e2 → AlphaOptRel Φ ρ (.block [a1]) e2
  | dropPureLet {ρ : List (Ident × Ident)} {x : Ident} {rhs1 b1 e2 : Expr} :
      coExprIsPure rhs1 = true →
      x ∉ freeVars b1 →
      AlphaOptRel Φ ρ b1 e2 →
      AlphaOptRel Φ ρ (.let_ x rhs1 b1) e2
  | introPureLetRight {ρ : List (Ident × Ident)} {y : Ident} {e1 rhs2 b2 : Expr} :
      coExprIsPure rhs2 = true →
      y ∉ freeVars b2 →
      (∀ w ∈ freeVars rhs2, ∃ z ∈ freeVars e1, lookupRename ρ z = w) →
      AlphaOptRel Φ ρ e1 b2 →
      AlphaOptRel Φ ρ e1 (.let_ y rhs2 b2)
  | inlineDirVars {ρ : List (Ident × Ident)} {fn : Ident} {fd : FunDef}
      {srcVars : List Ident} {e2 : Expr} :
      Φ fn = some fd →
      srcVars.length = fd.params.length →
      (fd.params.map Prod.fst).Nodup →
      (∀ z ∈ freeVars fd.body, z ∈ fd.params.map Prod.fst) →
      AlphaOptRel Φ ((fd.params.map Prod.fst).zip (srcVars.map (lookupRename ρ))) fd.body e2 →
      AlphaOptRel Φ ρ (.applyDir fn (srcVars.map .var)) e2
  | letAlpha {ρ : List (Ident × Ident)} {x y : Ident} {a1 a2 b1 b2 : Expr} :
      AlphaOptRel Φ ρ a1 a2 →
      (∀ z ∈ freeVars b1, z ≠ x → lookupRename ρ z ≠ y) →
      AlphaOptRel Φ ((x, y) :: ρ) b1 b2 →
      AlphaOptRel Φ ρ (.let_ x a1 b1) (.let_ y a2 b2)
  | tuple {ρ : List (Ident × Ident)} {es1 es2 : List Expr} :
      AlphaOptRelList Φ ρ es1 es2 → AlphaOptRel Φ ρ (.tuple es1) (.tuple es2)
  | block {ρ : List (Ident × Ident)} {es1 es2 : List Expr} :
      AlphaOptRelList Φ ρ es1 es2 → AlphaOptRel Φ ρ (.block es1) (.block es2)
  | makeData {ρ : List (Ident × Ident)} (adt : Ident) (tag : Nat) {es1 es2 : List Expr} :
      AlphaOptRelList Φ ρ es1 es2 → AlphaOptRel Φ ρ (.makeData adt tag es1) (.makeData adt tag es2)
  | concPrim {ρ : List (Ident × Ident)} (op : ConcPrim) {es1 es2 : List Expr} :
      AlphaOptRelList Φ ρ es1 es2 → AlphaOptRel Φ ρ (.concPrim op es1) (.concPrim op es2)
  | apply {ρ : List (Ident × Ident)} {fn1 fn2 : Expr} {args1 args2 : List Expr} :
      AlphaOptRel Φ ρ fn1 fn2 → AlphaOptRelList Φ ρ args1 args2 →
      AlphaOptRel Φ ρ (.apply fn1 args1) (.apply fn2 args2)
  | applyDir {ρ : List (Ident × Ident)} (nm : Ident) {args1 args2 : List Expr} :
      AlphaOptRelList Φ ρ args1 args2 →
      AlphaOptRel Φ ρ (.applyDir nm args1) (.applyDir nm args2)
  | bin {ρ : List (Ident × Ident)} (op : BinOp) {a1 a2 b1 b2 : Expr} :
      AlphaOptRel Φ ρ a1 a2 → AlphaOptRel Φ ρ b1 b2 →
      AlphaOptRel Φ ρ (.bin op a1 b1) (.bin op a2 b2)
  | un {ρ : List (Ident × Ident)} (op : UnOp) {a1 a2 : Expr} :
      AlphaOptRel Φ ρ a1 a2 → AlphaOptRel Φ ρ (.un op a1) (.un op a2)
  | if_ {ρ : List (Ident × Ident)} {c1 c2 t1 t2 e1 e2 : Expr} :
      AlphaOptRel Φ ρ c1 c2 → AlphaOptRel Φ ρ t1 t2 → AlphaOptRel Φ ρ e1 e2 →
      AlphaOptRel Φ ρ (.if_ c1 t1 e1) (.if_ c2 t2 e2)
  | while_ {ρ : List (Ident × Ident)} {c1 c2 b1 b2 : Expr} :
      AlphaOptRel Φ ρ c1 c2 → AlphaOptRel Φ ρ b1 b2 →
      AlphaOptRel Φ ρ (.while_ c1 b1) (.while_ c2 b2)
  | matchAlpha {ρ : List (Ident × Ident)} {s1 s2 : Expr} {arms1 arms2 : List (Pat × Expr)} :
      AlphaOptRel Φ ρ s1 s2 → AlphaOptRelArms Φ ρ arms1 arms2 →
      AlphaOptRel Φ ρ (.match_ s1 arms1) (.match_ s2 arms2)
  | getTag {ρ : List (Ident × Ident)} {a1 a2 : Expr} :
      AlphaOptRel Φ ρ a1 a2 → AlphaOptRel Φ ρ (.getTag a1) (.getTag a2)
  | cellNew {ρ : List (Ident × Ident)} {a1 a2 : Expr} :
      AlphaOptRel Φ ρ a1 a2 → AlphaOptRel Φ ρ (.cellNew a1) (.cellNew a2)
  | cellGet {ρ : List (Ident × Ident)} {a1 a2 : Expr} :
      AlphaOptRel Φ ρ a1 a2 → AlphaOptRel Φ ρ (.cellGet a1) (.cellGet a2)
  | cellSet {ρ : List (Ident × Ident)} {a1 a2 b1 b2 : Expr} :
      AlphaOptRel Φ ρ a1 a2 → AlphaOptRel Φ ρ b1 b2 →
      AlphaOptRel Φ ρ (.cellSet a1 b1) (.cellSet a2 b2)
  | spawn {ρ : List (Ident × Ident)} {a1 a2 : Expr} :
      AlphaOptRel Φ ρ a1 a2 → AlphaOptRel Φ ρ (.spawn a1) (.spawn a2)
  | await {ρ : List (Ident × Ident)} {a1 a2 : Expr} :
      AlphaOptRel Φ ρ a1 a2 → AlphaOptRel Φ ρ (.await a1) (.await a2)

inductive AlphaOptRelList (Φ : FunEnv) : List (Ident × Ident) → List Expr → List Expr → Prop where
  | nil (ρ : List (Ident × Ident)) : AlphaOptRelList Φ ρ [] []
  | cons {ρ : List (Ident × Ident)} {e1 e2 : Expr} {r1 r2 : List Expr} :
      AlphaOptRel Φ ρ e1 e2 → AlphaOptRelList Φ ρ r1 r2 →
      AlphaOptRelList Φ ρ (e1 :: r1) (e2 :: r2)

inductive AlphaOptRelArms (Φ : FunEnv) : List (Ident × Ident) → List (Pat × Expr) → List (Pat × Expr) → Prop where
  | nil (ρ : List (Ident × Ident)) : AlphaOptRelArms Φ ρ [] []
  | cons {ρ : List (Ident × Ident)} {p1 p2 : Pat} {pairs : List (Ident × Ident)}
      {b1 b2 : Expr} {r1 r2 : List (Pat × Expr)} :
      PatAlphaRel p1 p2 pairs →
      (pairs.map Prod.fst).Nodup →
      (pairs.map Prod.snd).Nodup →
      (∀ z ∈ freeVars b1, z ∉ pairs.map Prod.fst → lookupRename ρ z ∉ pairs.map Prod.snd) →
      AlphaOptRel Φ (pairs ++ ρ) b1 b2 →
      AlphaOptRelArms Φ ρ r1 r2 →
      AlphaOptRelArms Φ ρ ((p1, b1) :: r1) ((p2, b2) :: r2)
end

def AlphaEnvRel (ρ : List (Ident × Ident)) (env1 env2 : List (Ident × Expr)) (vars : List Ident) : Prop :=
  (∀ p ∈ env1, IsValue p.2 ∧ freeVars p.2 = []) ∧
  (∀ p ∈ env2, IsValue p.2 ∧ freeVars p.2 = []) ∧
  (∀ z ∈ vars, ∃ v, lookupSubstEnv z env1 = some v ∧ lookupSubstEnv (lookupRename ρ z) env2 = some v)

private theorem alphaEnvRel_mono {ρ : List (Ident × Ident)} {env1 env2 : List (Ident × Expr)}
    {s1 s2 : List Ident} (h : AlphaEnvRel ρ env1 env2 s2) (hsub : ∀ z ∈ s1, z ∈ s2) :
    AlphaEnvRel ρ env1 env2 s1 :=
  ⟨h.1, h.2.1, fun z hz => h.2.2 z (hsub z hz)⟩

private theorem lookupRename_append (pairs ρ : List (Ident × Ident)) (z : Ident) :
    lookupRename (pairs ++ ρ) z = match lookupSubstEnv z (pairs.map (fun p => (p.1, .var p.2))) with
      | some (.var y) => y
      | _ => lookupRename ρ z := by
  induction pairs with
  | nil => rfl
  | cons q r ih =>
    rcases q with ⟨k, y⟩
    simp only [List.cons_append, lookupRename, List.map, lookupSubstEnv]
    split
    · rfl
    · exact ih

private theorem lookupSubstEnv_nodup_zip {ks : List Ident} {vs : List Expr}
    (hnodup : ks.Nodup) (hlen : ks.length = vs.length) :
    ∀ i (hi : i < ks.length), lookupSubstEnv ks[i] (ks.zip vs) = some (vs[i]'(hlen ▸ hi)) := by
  induction ks generalizing vs with
  | nil => intro i hi; simp at hi
  | cons k kr ih =>
    cases vs with
    | nil => simp at hlen
    | cons v vr =>
      rcases List.nodup_cons.mp hnodup with ⟨hknot, hnodup_r⟩
      intro i hi
      cases i with
      | zero => simp [lookupSubstEnv]
      | succ j =>
        have hj : j < kr.length := Nat.lt_of_succ_lt_succ hi
        have hjk : (kr[j] == k) = false :=
          beq_false_of_ne (fun heq => hknot (heq ▸ List.getElem_mem hj))
        simp [lookupSubstEnv, hjk, ih hnodup_r (by simp at hlen; exact hlen) j hj]

private theorem lookupRename_nodup_zip {ks ys : List Ident}
    (hnodup : ks.Nodup) (hlen : ks.length = ys.length) (ρ : List (Ident × Ident)) :
    ∀ i (hi : i < ks.length), lookupRename (ks.zip ys ++ ρ) ks[i] = ys[i]'(hlen ▸ hi) := by
  induction ks generalizing ys with
  | nil => intro i hi; simp at hi
  | cons k kr ih =>
    cases ys with
    | nil => simp at hlen
    | cons y yr =>
      rcases List.nodup_cons.mp hnodup with ⟨hknot, hnodup_r⟩
      intro i hi
      cases i with
      | zero => simp [lookupRename]
      | succ j =>
        have hj : j < kr.length := Nat.lt_of_succ_lt_succ hi
        have hjk : (kr[j] == k) = false :=
          beq_false_of_ne (fun heq => hknot (heq ▸ List.getElem_mem hj))
        simp [lookupRename, hjk, ih hnodup_r (by simp at hlen; exact hlen) j hj]

private theorem lookupRename_not_mem_fst {pairs ρ : List (Ident × Ident)} {z : Ident}
    (hnot : z ∉ pairs.map Prod.fst) :
    lookupRename (pairs ++ ρ) z = lookupRename ρ z := by
  induction pairs with
  | nil => rfl
  | cons q r ih =>
    rcases q with ⟨k, y⟩
    have hzk : (z == k) = false :=
      beq_false_of_ne (fun heq => hnot (by simp [heq]))
    simp [lookupRename, hzk, ih (fun hm => hnot (List.mem_cons_of_mem _ hm))]

private theorem lookupSubstEnv_not_mem_fst {binds env : List (Ident × Expr)} {z : Ident}
    (hnot : z ∉ binds.map Prod.fst) :
    lookupSubstEnv z (binds ++ env) = lookupSubstEnv z env := by
  induction binds with
  | nil => rfl
  | cons q r ih =>
    rcases q with ⟨k, w⟩
    have hzk : (z == k) = false :=
      beq_false_of_ne (fun heq => hnot (by simp [heq]))
    simp [lookupSubstEnv, hzk, ih (fun hm => hnot (List.mem_cons_of_mem _ hm))]

private theorem zip_fst_eq_of_eq_len {α β : Type} {ks : List α} {vs : List β}
    (hlen : ks.length = vs.length) : (ks.zip vs).map Prod.fst = ks := by
  induction ks generalizing vs with
  | nil => rfl
  | cons k kr ih =>
    cases vs with
    | nil => simp at hlen
    | cons v vr => simp [ih (by simp at hlen; exact hlen)]

private theorem pairs_zip_eq (pairs : List (Ident × Ident)) :
    (pairs.map Prod.fst).zip (pairs.map Prod.snd) = pairs := by
  induction pairs with
  | nil => rfl
  | cons p r ih => rcases p with ⟨a, b⟩; simp [ih]

mutual
theorem alphaOptRel_freeVars_bound {Φ : FunEnv} :
    {ρ : List (Ident × Ident)} → {e1 e2 : Expr} →
      AlphaOptRel Φ ρ e1 e2 →
      ∀ w ∈ freeVars e2, ∃ z ∈ freeVars e1, lookupRename ρ z = w
  | _, _, _, .lit _ _, _, hw => by simp [freeVars] at hw
  | _, _, _, .var ρ x, _, hw => by
    simp [freeVars] at hw; subst hw; exact ⟨x, by simp [freeVars], rfl⟩
  | _, _, _, .loc _ _, _, hw => by simp [freeVars] at hw
  | _, _, _, .taskRef _ _, _, hw => by simp [freeVars] at hw
  | _, _, _, .syncRef _ _ _, _, hw => by simp [freeVars] at hw
  | _, _, _, .trap _ _, _, hw => by simp [freeVars] at hw
  | _, _, _, .unwrapBlock1 ha, w, hw => by
    rcases alphaOptRel_freeVars_bound ha w hw with ⟨z, hz, heq⟩
    exact ⟨z, by simp [freeVars, freeVarsList, hz], heq⟩
  | _, _, _, @AlphaOptRel.dropPureLet _ _ x _ _ _ _ hxnot hb, w, hw => by
    rcases alphaOptRel_freeVars_bound hb w hw with ⟨z, hz, heq⟩
    have hzx : z ≠ x := fun h => by subst h; exact hxnot hz
    exact ⟨z, by simp [freeVars, hz, hzx], heq⟩
  | _, _, _, .introPureLetRight _ _ hfvrhs hb, w, hw => by
    simp only [freeVars, List.mem_append, List.mem_filter] at hw
    rcases hw with hr | ⟨hb2, _⟩
    · exact hfvrhs w hr
    · exact alphaOptRel_freeVars_bound hb w hb2
  | ρ, _, _, @AlphaOptRel.inlineDirVars _ _ fn fd srcVars _ _ hlen hnodup hclosed hb, w, hw => by
    rcases alphaOptRel_freeVars_bound hb w hw with ⟨p, hp, heq⟩
    have hpmem : p ∈ fd.params.map Prod.fst := hclosed p hp
    rcases List.mem_iff_getElem.mp hpmem with ⟨i, hi, rfl⟩
    have hi_src : i < srcVars.length := by simp at hi; omega
    have hren : lookupRename ((fd.params.map Prod.fst).zip (srcVars.map (lookupRename ρ))) (fd.params.map Prod.fst)[i] =
        lookupRename ρ srcVars[i] := by
      have h := lookupRename_nodup_zip hnodup (ys := srcVars.map (lookupRename ρ))
        (by simp [hlen]) [] i hi
      simpa using h
    rw [hren] at heq
    refine ⟨srcVars[i], ?_, heq⟩
    have hmem_src : Expr.var srcVars[i] ∈ srcVars.map Expr.var :=
      List.mem_map.mpr ⟨srcVars[i], List.getElem_mem hi_src, rfl⟩
    have hfv_list : ∀ l : List Expr, ∀ e ∈ l, ∀ z ∈ freeVars e, z ∈ freeVarsList l := by
      intro l; induction l with
      | nil => intro _ h; cases h
      | cons hd tl ih =>
        intro e he z hz; rcases List.mem_cons.mp he with rfl | het
        · simp [freeVarsList, hz]
        · simp [freeVarsList, ih e het z hz]
    exact hfv_list (srcVars.map Expr.var) (.var srcVars[i]) hmem_src srcVars[i] (by simp [freeVars])
  | ρ, _, _, @AlphaOptRel.letAlpha _ _ x y a1 a2 b1 b2 ha _ hb, w, hw => by
    simp only [freeVars, List.mem_append, List.mem_filter] at hw
    rcases hw with ha2 | ⟨hb2, hwy⟩
    · rcases alphaOptRel_freeVars_bound ha w ha2 with ⟨z, hz, heq⟩
      exact ⟨z, by simp [freeVars, hz], heq⟩
    · rcases alphaOptRel_freeVars_bound hb w hb2 with ⟨z, hz, heq⟩
      by_cases hzx : z = x
      · subst hzx; simp [lookupRename] at heq; subst heq; simp at hwy
      · have hzx' : (z == x) = false := beq_false_of_ne hzx
        simp only [lookupRename, hzx', Bool.false_eq_true, ↓reduceIte] at heq
        exact ⟨z, by simp [freeVars, hz, hzx], heq⟩
  | _, _, _, .tuple hrl, w, hw => alphaOptRelList_freeVars_bound hrl w hw
  | _, _, _, .block hrl, w, hw => alphaOptRelList_freeVars_bound hrl w hw
  | _, _, _, .makeData _ _ hrl, w, hw => alphaOptRelList_freeVars_bound hrl w hw
  | _, _, _, .concPrim _ hrl, w, hw => alphaOptRelList_freeVars_bound hrl w hw
  | _, _, _, .apply hf ha, w, hw => by
    simp only [freeVars, List.mem_append] at hw
    rcases hw with h1 | h2
    · rcases alphaOptRel_freeVars_bound hf w h1 with ⟨z, hz, heq⟩
      exact ⟨z, by simp [freeVars, hz], heq⟩
    · rcases alphaOptRelList_freeVars_bound ha w h2 with ⟨z, hz, heq⟩
      exact ⟨z, by simp [freeVars, hz], heq⟩
  | _, _, _, .applyDir _ ha, w, hw => alphaOptRelList_freeVars_bound ha w hw
  | _, _, _, .bin _ ha hb, w, hw | _, _, _, .while_ ha hb, w, hw | _, _, _, .cellSet ha hb, w, hw => by
    simp only [freeVars, List.mem_append] at hw
    rcases hw with h1 | h2
    · rcases alphaOptRel_freeVars_bound ha w h1 with ⟨z, hz, heq⟩
      exact ⟨z, by simp [freeVars, hz], heq⟩
    · rcases alphaOptRel_freeVars_bound hb w h2 with ⟨z, hz, heq⟩
      exact ⟨z, by simp [freeVars, hz], heq⟩
  | _, _, _, .un _ ha, w, hw | _, _, _, .getTag ha, w, hw | _, _, _, .cellNew ha, w, hw
  | _, _, _, .cellGet ha, w, hw | _, _, _, .spawn ha, w, hw | _, _, _, .await ha, w, hw =>
    alphaOptRel_freeVars_bound ha w hw
  | _, _, _, .if_ hc ht he, w, hw => by
    simp only [freeVars, List.mem_append] at hw
    rcases hw with (h1 | h2) | h3
    · rcases alphaOptRel_freeVars_bound hc w h1 with ⟨z, hz, heq⟩
      exact ⟨z, by simp [freeVars, hz], heq⟩
    · rcases alphaOptRel_freeVars_bound ht w h2 with ⟨z, hz, heq⟩
      exact ⟨z, by simp [freeVars, hz], heq⟩
    · rcases alphaOptRel_freeVars_bound he w h3 with ⟨z, hz, heq⟩
      exact ⟨z, by simp [freeVars, hz], heq⟩
  | _, _, _, .matchAlpha hs ha, w, hw => by
    simp only [freeVars, List.mem_append] at hw
    rcases hw with h1 | h2
    · rcases alphaOptRel_freeVars_bound hs w h1 with ⟨z, hz, heq⟩
      exact ⟨z, by simp [freeVars, hz], heq⟩
    · rcases alphaOptRelArms_freeVars_bound ha w h2 with ⟨z, hz, heq⟩
      exact ⟨z, by simp [freeVars, hz], heq⟩

theorem alphaOptRelList_freeVars_bound {Φ : FunEnv} :
    {ρ : List (Ident × Ident)} → {es1 es2 : List Expr} →
      AlphaOptRelList Φ ρ es1 es2 →
      ∀ w ∈ freeVarsList es2, ∃ z ∈ freeVarsList es1, lookupRename ρ z = w
  | _, _, _, .nil _, _, hw => by simp [freeVarsList] at hw
  | _, _, _, .cons he hr, w, hw => by
    simp only [freeVarsList, List.mem_append] at hw
    rcases hw with h1 | h2
    · rcases alphaOptRel_freeVars_bound he w h1 with ⟨z, hz, heq⟩
      exact ⟨z, by simp [freeVarsList, hz], heq⟩
    · rcases alphaOptRelList_freeVars_bound hr w h2 with ⟨z, hz, heq⟩
      exact ⟨z, by simp [freeVarsList, hz], heq⟩

theorem alphaOptRelArms_freeVars_bound {Φ : FunEnv} :
    {ρ : List (Ident × Ident)} → {arms1 arms2 : List (Pat × Expr)} →
      AlphaOptRelArms Φ ρ arms1 arms2 →
      ∀ w ∈ freeVarsArms arms2, ∃ z ∈ freeVarsArms arms1, lookupRename ρ z = w
  | _, _, _, .nil _, _, hw => by simp [freeVarsArms] at hw
  | ρ, _, _, @AlphaOptRelArms.cons _ _ p1 p2 pairs b1 b2 r1 r2 hp hnd1 _ _ hb hr, w, hw => by
    simp only [freeVarsArms, List.mem_append, List.mem_filter] at hw
    rcases hw with ⟨hb2, hwnot2⟩ | hr2
    · rcases patAlphaRel_boundNames hp with ⟨hbn1, hbn2⟩
      rcases alphaOptRel_freeVars_bound hb w hb2 with ⟨z, hz, heq⟩
      by_cases hzp : z ∈ pairs.map Prod.fst
      · rcases List.mem_iff_getElem.mp hzp with ⟨i, hi, rfl⟩
        have hi2 : i < (pairs.map Prod.snd).length := by simp at hi ⊢; exact hi
        have hren := lookupRename_nodup_zip hnd1 (ys := pairs.map Prod.snd) (by simp) ρ i hi
        rw [pairs_zip_eq] at hren
        rw [hren] at heq; subst heq
        have hmem2 : (pairs.map Prod.snd)[i] ∈ patBoundNames p2 := by
          rw [← hbn2]; exact List.getElem_mem hi2
        have hct2 : (patBoundNames p2).contains (pairs.map Prod.snd)[i] = true :=
          List.contains_iff_mem.mpr hmem2
        rw [hct2] at hwnot2; simp at hwnot2
      · rw [lookupRename_not_mem_fst hzp] at heq
        have hct1 : (patBoundNames p1).contains z = false := by
          cases h : (patBoundNames p1).contains z
          · rfl
          · exfalso; exact hzp (hbn1 ▸ List.contains_iff_mem.mp h)
        refine ⟨z, ?_, heq⟩
        simp only [freeVarsArms, List.mem_append, List.mem_filter]
        exact Or.inl ⟨hz, by rw [hct1]; rfl⟩
    · rcases alphaOptRelArms_freeVars_bound hr w hr2 with ⟨z, hz, heq⟩
      exact ⟨z, by simp [freeVarsArms, hz], heq⟩
end

private theorem while_closedObsEquiv_forward {Δ : AdtEnv} {Φ : FunEnv}
    (hΦ : ClosedFunEnv Φ) {c1 c2 b1 b2 : Expr}
    (hc1 : freeVars c1 = []) (hb1 : freeVars b1 = [])
    (hc : ClosedObsEquiv Δ Φ Φ c1 c2) (hb : ClosedObsEquiv Δ Φ Φ b1 b2) :
    ∀ (fuel : Nat) {n : Nat} {σ σ' : Store} {out : Expr},
      n ≤ fuel → ClosedStore σ → IsTerminal out → StepsN Δ Φ n (.while_ c1 b1) σ out σ' →
      Steps Δ Φ (.while_ c2 b2) σ out σ'
  | 0, _, _, _, _, hle, _, hout, hn => by
    have hz : _ = 0 := Nat.eq_zero_of_le_zero hle
    subst hz; cases hn
    cases hout with | inl hv => cases hv | inr htr => rcases htr with ⟨_, h⟩; cases h
  | fuel + 1, _, σ, σ', out, hle, hσ, hout, hn => by
    cases hn with
    | zero => cases hout with | inl hv => cases hv | inr htr => rcases htr with ⟨_, h⟩; cases h
    | @succ m _ _ _ _ _ _ hs hrest =>
      cases hs with
      | whileUnfold =>
        rcases activeCtx_stepsN_decomp (isActiveCtx_ifCond Δ (.block [b1, .while_ c1 b1]) (.lit .unit)) hout hrest with
          ⟨t, rfl, htr_c1⟩ | ⟨vc, sm1, k1, hk1, hvc, hs_c1, hk_if⟩
        · have htr_c2 := (hc σ σ' (.trap t) hσ (Or.inr ⟨t, rfl⟩)).mp htr_c1
          exact .trans .whileUnfold
            (Steps.append (Steps.liftCongr _ (fun hs => .ifStep hs) htr_c2) (.single .ifTrap))
        · rcases steps_preserves_closed hΦ hσ hc1 hs_c1 with ⟨_, hsm1⟩
          have hs_c2 := (hc σ sm1 vc hσ (Or.inl hvc)).mp hs_c1
          cases hk_if with
          | zero => cases hout with | inl hv => cases hv | inr htr => rcases htr with ⟨_, h⟩; cases h
          | @succ m2 _ _ _ _ _ _ hs_if hrest2 =>
            cases hs_if with
            | ifStep hs_vc => exact False.elim (isValue_no_step hvc hs_vc)
            | ifTrap => cases hvc
            | ifFalse =>
              rcases steps_terminal_det (stepsN_to_steps hrest2) hout (.refl _ _) (Or.inl (.lit .unit)) with ⟨rfl, rfl⟩
              exact .trans .whileUnfold
                (Steps.append (Steps.liftCongr _ (fun hs => .ifStep hs) hs_c2) (.single .ifFalse))
            | ifTrue =>
              rcases activeCtx_stepsN_decomp (isActiveCtx_blockHead Δ (.while_ c1 b1) []) hout hrest2 with
                ⟨t, rfl, htr_b1⟩ | ⟨vb, sm2, k2, hk2, hvb, hs_b1, hk_blk⟩
              · have htr_b2 := (hb sm1 σ' (.trap t) hsm1 (Or.inr ⟨t, rfl⟩)).mp htr_b1
                exact .trans .whileUnfold
                  (Steps.append (Steps.liftCongr _ (fun hs => .ifStep hs) hs_c2)
                    (.trans .ifTrue
                      (Steps.append (Steps.liftCongr _ (fun hs => .blockConsStep hs) htr_b2)
                        (.single .blockConsTrap))))
              · rcases steps_preserves_closed hΦ hsm1 hb1 hs_b1 with ⟨_, hsm2⟩
                have hs_b2 := (hb sm1 sm2 vb hsm1 (Or.inl hvb)).mp hs_b1
                cases hk_blk with
                | zero => cases hout with | inl hv => cases hv | inr htr => rcases htr with ⟨_, h⟩; cases h
                | @succ m3 _ _ _ _ _ _ hs_blk1 hk_blk2 =>
                  cases hs_blk1 with
                  | blockConsStep hs_vb => exact False.elim (isValue_no_step hvb hs_vb)
                  | blockConsTrap => cases hvb
                  | blockConsVal _ =>
                    cases hk_blk2 with
                    | zero => cases hout with | inl hv => cases hv | inr htr => rcases htr with ⟨_, h⟩; cases h
                    | @succ m4 _ _ _ _ _ _ hs_blk2 hk_w =>
                      cases hs_blk2 with
                      | blockSingle =>
                        have hm4_le : m4 ≤ fuel := by omega
                        have hw2 := while_closedObsEquiv_forward hΦ hc1 hb1 hc hb fuel hm4_le hsm2 hout hk_w
                        exact .trans .whileUnfold
                          (Steps.append (Steps.liftCongr _ (fun hs => .ifStep hs) hs_c2)
                            (.trans .ifTrue
                              (Steps.append (Steps.liftCongr _ (fun hs => .blockConsStep hs) hs_b2)
                                (.trans (.blockConsVal hvb) (.trans .blockSingle hw2)))))

private theorem while_closedObsEquiv_congr {Δ : AdtEnv} {Φ : FunEnv} (hΦ : ClosedFunEnv Φ)
    {c1 c2 b1 b2 : Expr}
    (hc1 : freeVars c1 = []) (hc2 : freeVars c2 = [])
    (hb1 : freeVars b1 = []) (hb2 : freeVars b2 = [])
    (hc : ClosedObsEquiv Δ Φ Φ c1 c2) (hb : ClosedObsEquiv Δ Φ Φ b1 b2) :
    ClosedObsEquiv Δ Φ Φ (.while_ c1 b1) (.while_ c2 b2) := by
  intro σ σ' out hσ hout
  constructor
  · intro h1
    rcases steps_to_stepsN h1 with ⟨n, hn⟩
    exact while_closedObsEquiv_forward hΦ hc1 hb1 hc hb n (Nat.le_refl n) hσ hout hn
  · intro h2
    rcases steps_to_stepsN h2 with ⟨n, hn⟩
    exact while_closedObsEquiv_forward hΦ hc2 hb2 (ClosedObsEquiv.symm hc) (ClosedObsEquiv.symm hb)
      n (Nat.le_refl n) hσ hout hn

private theorem activeList_closedObsEquiv_congr {Δ : AdtEnv} {Φ : FunEnv} (hΦ : ClosedFunEnv Φ)
    (F : List Expr → Expr)
    (hF : ∀ (vs : List Expr), (∀ v ∈ vs, IsValue v) → ∀ (rest : List Expr),
      IsActiveCtx Δ (fun x => F (vs ++ x :: rest))) :
    ∀ {es1 es2 : List Expr} (vs : List Expr),
      (∀ v ∈ vs, IsValue v) →
      (∀ e ∈ es2, freeVars e = []) →
      es1.length = es2.length →
      (∀ i (h1 : i < es1.length) (h2 : i < es2.length), ClosedObsEquiv Δ Φ Φ es1[i] es2[i]) →
      ClosedObsEquiv Δ Φ Φ (F (vs ++ es1)) (F (vs ++ es2))
  | [], [], _, _, _, _, _ => ClosedObsEquiv.refl _ _ _
  | _ :: _, [], _, _, _, hlen, _ => by simp at hlen
  | [], _ :: _, _, _, _, hlen, _ => by simp at hlen
  | a1 :: r1, a2 :: r2, vs, hvs, hcl2, hlen, heq => by
    have ha : ClosedObsEquiv Δ Φ Φ a1 a2 := heq 0 (by simp) (by simp)
    have hstep1 : ClosedObsEquiv Δ Φ Φ (F (vs ++ a1 :: r1)) (F (vs ++ a2 :: r1)) :=
      activeCtx_closedObsEquiv_congr (hF vs hvs r1) ha
    refine ClosedObsEquiv.trans hstep1 ?_
    intro σ σ' out hσ hout
    rw [activeCtx_steps_terminal_iff (hF vs hvs r1) hout,
        activeCtx_steps_terminal_iff (hF vs hvs r2) hout]
    have ha2_cl : freeVars a2 = [] := hcl2 a2 (List.mem_cons_self ..)
    have hr2_cl : ∀ e ∈ r2, freeVars e = [] := fun e he => hcl2 e (List.mem_cons_of_mem _ he)
    have hrest : ∀ v, IsValue v → ClosedObsEquiv Δ Φ Φ (F ((vs ++ [v]) ++ r1)) (F ((vs ++ [v]) ++ r2)) := by
      intro v hv
      apply activeList_closedObsEquiv_congr hΦ F hF (vs ++ [v])
      · intro w hw
        rcases List.mem_append.mp hw with hw1 | hw2
        · exact hvs w hw1
        · simp at hw2; subst hw2; exact hv
      · exact hr2_cl
      · simp at hlen; exact hlen
      · intro i hi1 hi2
        exact heq (i + 1) (Nat.succ_lt_succ hi1) (Nat.succ_lt_succ hi2)
    constructor
    · rintro (⟨t, rfl, htr⟩ | ⟨v, sm, hv, hsv, hkv⟩)
      · exact Or.inl ⟨t, rfl, htr⟩
      · rcases steps_preserves_closed hΦ hσ ha2_cl hsv with ⟨_, hsm⟩
        refine Or.inr ⟨v, sm, hv, hsv, ?_⟩
        have hkv' : Steps Δ Φ (F ((vs ++ [v]) ++ r1)) sm out σ' := by simpa [List.append_assoc] using hkv
        have hkv2 := ((hrest v hv) sm σ' out hsm hout).mp hkv'
        simpa [List.append_assoc] using hkv2
    · rintro (⟨t, rfl, htr⟩ | ⟨v, sm, hv, hsv, hkv⟩)
      · exact Or.inl ⟨t, rfl, htr⟩
      · rcases steps_preserves_closed hΦ hσ ha2_cl hsv with ⟨_, hsm⟩
        refine Or.inr ⟨v, sm, hv, hsv, ?_⟩
        have hkv' : Steps Δ Φ (F ((vs ++ [v]) ++ r2)) sm out σ' := by simpa [List.append_assoc] using hkv
        have hkv1 := ((hrest v hv) sm σ' out hsm hout).mpr hkv'
        simpa [List.append_assoc] using hkv1

private theorem block_closedObsEquiv_congr {Δ : AdtEnv} {Φ : FunEnv} (hΦ : ClosedFunEnv Φ) :
    ∀ {es1 es2 : List Expr},
      (∀ e ∈ es2, freeVars e = []) →
      es1.length = es2.length →
      (∀ i (h1 : i < es1.length) (h2 : i < es2.length), ClosedObsEquiv Δ Φ Φ es1[i] es2[i]) →
      ClosedObsEquiv Δ Φ Φ (.block es1) (.block es2)
  | [], [], _, _, _ => ClosedObsEquiv.refl _ _ _
  | _ :: _, [], _, hlen, _ => by simp at hlen
  | [], _ :: _, _, hlen, _ => by simp at hlen
  | [a1], [a2], _, _, heq => by
    have hs1 : ClosedObsEquiv Δ Φ Φ (.block [a1]) a1 :=
      ClosedObsEquiv.of_obsEquiv (obsEquiv_of_det_step (fun _ => .blockSingle))
    have hs2 : ClosedObsEquiv Δ Φ Φ (.block [a2]) a2 :=
      ClosedObsEquiv.of_obsEquiv (obsEquiv_of_det_step (fun _ => .blockSingle))
    exact ClosedObsEquiv.trans hs1 (ClosedObsEquiv.trans (heq 0 (by simp) (by simp)) (ClosedObsEquiv.symm hs2))
  | _ :: _ :: _, [_], _, hlen, _ => by simp at hlen
  | [_], _ :: _ :: _, _, hlen, _ => by simp at hlen
  | a1 :: b1 :: r1, a2 :: b2 :: r2, hcl2, hlen, heq => by
    have ha : ClosedObsEquiv Δ Φ Φ a1 a2 := heq 0 (by simp) (by simp)
    have hstep1 : ClosedObsEquiv Δ Φ Φ (.block (a1 :: b1 :: r1)) (.block (a2 :: b1 :: r1)) :=
      activeCtx_closedObsEquiv_congr (isActiveCtx_blockHead Δ b1 r1) ha
    refine ClosedObsEquiv.trans hstep1 ?_
    have ha2_cl : freeVars a2 = [] := hcl2 a2 (List.mem_cons_self ..)
    have hr2_cl : ∀ e ∈ (b2 :: r2), freeVars e = [] := fun e he => hcl2 e (List.mem_cons_of_mem _ he)
    have hrest : ClosedObsEquiv Δ Φ Φ (.block (b1 :: r1)) (.block (b2 :: r2)) :=
      block_closedObsEquiv_congr hΦ hr2_cl (by simp at hlen ⊢; exact hlen)
        (fun i hi1 hi2 => heq (i + 1) (Nat.succ_lt_succ hi1) (Nat.succ_lt_succ hi2))
    intro σ σ' out hσ hout
    rw [activeCtx_steps_terminal_iff (isActiveCtx_blockHead Δ b1 r1) hout,
        activeCtx_steps_terminal_iff (isActiveCtx_blockHead Δ b2 r2) hout]
    constructor
    · rintro (⟨t, rfl, htr⟩ | ⟨v, sm, hv, hsv, hkv⟩)
      · exact Or.inl ⟨t, rfl, htr⟩
      · rcases steps_preserves_closed hΦ hσ ha2_cl hsv with ⟨_, hsm⟩
        refine Or.inr ⟨v, sm, hv, hsv, ?_⟩
        cases hkv with
        | refl => cases hout with | inl hvv => cases hvv | inr htr => rcases htr with ⟨_, h⟩; cases h
        | trans hs_b hrest_b =>
          cases hs_b with
          | blockConsStep hs_v => exact False.elim (isValue_no_step hv hs_v)
          | blockConsTrap => cases hv
          | blockConsVal _ =>
            exact .trans (.blockConsVal hv) ((hrest sm σ' out hsm hout).mp hrest_b)
    · rintro (⟨t, rfl, htr⟩ | ⟨v, sm, hv, hsv, hkv⟩)
      · exact Or.inl ⟨t, rfl, htr⟩
      · rcases steps_preserves_closed hΦ hσ ha2_cl hsv with ⟨_, hsm⟩
        refine Or.inr ⟨v, sm, hv, hsv, ?_⟩
        cases hkv with
        | refl => cases hout with | inl hvv => cases hvv | inr htr => rcases htr with ⟨_, h⟩; cases h
        | trans hs_b hrest_b =>
          cases hs_b with
          | blockConsStep hs_v => exact False.elim (isValue_no_step hv hs_v)
          | blockConsTrap => cases hv
          | blockConsVal _ =>
            exact .trans (.blockConsVal hv) ((hrest sm σ' out hsm hout).mpr hrest_b)

private theorem bin_closedObsEquiv_congr {Δ : AdtEnv} {Φ : FunEnv} (hΦ : ClosedFunEnv Φ)
    (op : BinOp) {a1 a2 b1 b2 : Expr} (ha2_cl : freeVars a2 = [])
    (ha : ClosedObsEquiv Δ Φ Φ a1 a2) (hb : ClosedObsEquiv Δ Φ Φ b1 b2) :
    ClosedObsEquiv Δ Φ Φ (.bin op a1 b1) (.bin op a2 b2) := by
  refine ClosedObsEquiv.trans (activeCtx_closedObsEquiv_congr (isActiveCtx_binLeft Δ op b1) ha) ?_
  intro σ σ' out hσ hout
  rw [activeCtx_steps_terminal_iff (isActiveCtx_binLeft Δ op b1) hout,
      activeCtx_steps_terminal_iff (isActiveCtx_binLeft Δ op b2) hout]
  have hval_step : ∀ (v : Expr) (sm : Store), IsValue v → ClosedStore sm →
      (Steps Δ Φ (.bin op v b1) sm out σ' ↔ Steps Δ Φ (.bin op v b2) sm out σ') := by
    intro v sm hv hsm
    by_cases h_and : op = .and
    · subst h_and
      constructor
      · intro hs
        cases hs with
        | refl => cases hout with | inl hvv => cases hvv | inr htr => rcases htr with ⟨_, h⟩; cases h
        | trans h1 hr1 =>
          cases h1 with
          | binLeft hsv => exact False.elim (isValue_no_step hv hsv)
          | binLeftTrap => cases hv
          | binAndFalse => exact .trans .binAndFalse hr1
          | binAndTrue => exact .trans .binAndTrue ((hb sm σ' out hsm hout).mp hr1)
          | binRight hna _ _ _ | binRightTrap hna _ _ => exact False.elim (hna rfl)
          | binVal hev | binTrap hev => simp [evalBinOp] at hev
      · intro hs
        cases hs with
        | refl => cases hout with | inl hvv => cases hvv | inr htr => rcases htr with ⟨_, h⟩; cases h
        | trans h1 hr1 =>
          cases h1 with
          | binLeft hsv => exact False.elim (isValue_no_step hv hsv)
          | binLeftTrap => cases hv
          | binAndFalse => exact .trans .binAndFalse hr1
          | binAndTrue => exact .trans .binAndTrue ((hb sm σ' out hsm hout).mpr hr1)
          | binRight hna _ _ _ | binRightTrap hna _ _ => exact False.elim (hna rfl)
          | binVal hev | binTrap hev => simp [evalBinOp] at hev
    · by_cases h_or : op = .or
      · subst h_or
        constructor
        · intro hs
          cases hs with
          | refl => cases hout with | inl hvv => cases hvv | inr htr => rcases htr with ⟨_, h⟩; cases h
          | trans h1 hr1 =>
            cases h1 with
            | binLeft hsv => exact False.elim (isValue_no_step hv hsv)
            | binLeftTrap => cases hv
            | binOrTrue => exact .trans .binOrTrue hr1
            | binOrFalse => exact .trans .binOrFalse ((hb sm σ' out hsm hout).mp hr1)
            | binRight _ hno _ _ | binRightTrap _ hno _ => exact False.elim (hno rfl)
            | binVal hev | binTrap hev => simp [evalBinOp] at hev
        · intro hs
          cases hs with
          | refl => cases hout with | inl hvv => cases hvv | inr htr => rcases htr with ⟨_, h⟩; cases h
          | trans h1 hr1 =>
            cases h1 with
            | binLeft hsv => exact False.elim (isValue_no_step hv hsv)
            | binLeftTrap => cases hv
            | binOrTrue => exact .trans .binOrTrue hr1
            | binOrFalse => exact .trans .binOrFalse ((hb sm σ' out hsm hout).mpr hr1)
            | binRight _ hno _ _ | binRightTrap _ hno _ => exact False.elim (hno rfl)
            | binVal hev | binTrap hev => simp [evalBinOp] at hev
      · exact activeCtx_closedObsEquiv_congr (isActiveCtx_binRight Δ h_and h_or hv) hb sm σ' out hsm hout
  constructor
  · rintro (⟨t, rfl, htr⟩ | ⟨v, sm, hv, hsv, hkv⟩)
    · exact Or.inl ⟨t, rfl, htr⟩
    · rcases steps_preserves_closed hΦ hσ ha2_cl hsv with ⟨_, hsm⟩
      exact Or.inr ⟨v, sm, hv, hsv, (hval_step v sm hv hsm).mp hkv⟩
  · rintro (⟨t, rfl, htr⟩ | ⟨v, sm, hv, hsv, hkv⟩)
    · exact Or.inl ⟨t, rfl, htr⟩
    · rcases steps_preserves_closed hΦ hσ ha2_cl hsv with ⟨_, hsm⟩
      exact Or.inr ⟨v, sm, hv, hsv, (hval_step v sm hv hsm).mpr hkv⟩

private theorem apply_closedObsEquiv_congr {Δ : AdtEnv} {Φ : FunEnv} (hΦ : ClosedFunEnv Φ)
    {fn1 fn2 : Expr} {args1 args2 : List Expr}
    (hfn2_cl : freeVars fn2 = []) (hargs2_cl : ∀ e ∈ args2, freeVars e = [])
    (hfn : ClosedObsEquiv Δ Φ Φ fn1 fn2)
    (hlen : args1.length = args2.length)
    (hargs : ∀ i (h1 : i < args1.length) (h2 : i < args2.length), ClosedObsEquiv Δ Φ Φ args1[i] args2[i]) :
    ClosedObsEquiv Δ Φ Φ (.apply fn1 args1) (.apply fn2 args2) := by
  refine ClosedObsEquiv.trans (activeCtx_closedObsEquiv_congr (isActiveCtx_applyFn Δ args1) hfn) ?_
  intro σ σ' out hσ hout
  rw [activeCtx_steps_terminal_iff (isActiveCtx_applyFn Δ args1) hout,
      activeCtx_steps_terminal_iff (isActiveCtx_applyFn Δ args2) hout]
  constructor
  · rintro (⟨t, rfl, htr⟩ | ⟨vf, sm, hvf, hsv, hkv⟩)
    · exact Or.inl ⟨t, rfl, htr⟩
    · rcases steps_preserves_closed hΦ hσ hfn2_cl hsv with ⟨_, hsm⟩
      have hlist := activeList_closedObsEquiv_congr hΦ (Expr.apply vf)
        (fun vs hvs rest => isActiveCtx_applyArg Δ hvf hvs rest) [] (fun _ h => by cases h)
        hargs2_cl hlen hargs
      exact Or.inr ⟨vf, sm, hvf, hsv, (hlist sm σ' out hsm hout).mp hkv⟩
  · rintro (⟨t, rfl, htr⟩ | ⟨vf, sm, hvf, hsv, hkv⟩)
    · exact Or.inl ⟨t, rfl, htr⟩
    · rcases steps_preserves_closed hΦ hσ hfn2_cl hsv with ⟨_, hsm⟩
      have hlist := activeList_closedObsEquiv_congr hΦ (Expr.apply vf)
        (fun vs hvs rest => isActiveCtx_applyArg Δ hvf hvs rest) [] (fun _ h => by cases h)
        hargs2_cl hlen hargs
      exact Or.inr ⟨vf, sm, hvf, hsv, (hlist sm σ' out hsm hout).mpr hkv⟩

private theorem cellSet_closedObsEquiv_congr {Δ : AdtEnv} {Φ : FunEnv} (hΦ : ClosedFunEnv Φ)
    {a1 a2 b1 b2 : Expr} (ha2_cl : freeVars a2 = [])
    (ha : ClosedObsEquiv Δ Φ Φ a1 a2) (hb : ClosedObsEquiv Δ Φ Φ b1 b2) :
    ClosedObsEquiv Δ Φ Φ (.cellSet a1 b1) (.cellSet a2 b2) := by
  refine ClosedObsEquiv.trans (activeCtx_closedObsEquiv_congr (isActiveCtx_cellSetLeft Δ b1) ha) ?_
  intro σ σ' out hσ hout
  rw [activeCtx_steps_terminal_iff (isActiveCtx_cellSetLeft Δ b1) hout,
      activeCtx_steps_terminal_iff (isActiveCtx_cellSetLeft Δ b2) hout]
  constructor
  · rintro (⟨t, rfl, htr⟩ | ⟨va, sm, hva, hsv, hkv⟩)
    · exact Or.inl ⟨t, rfl, htr⟩
    · rcases steps_preserves_closed hΦ hσ ha2_cl hsv with ⟨_, hsm⟩
      exact Or.inr ⟨va, sm, hva, hsv,
        (activeCtx_closedObsEquiv_congr (isActiveCtx_cellSetRight Δ hva) hb sm σ' out hsm hout).mp hkv⟩
  · rintro (⟨t, rfl, htr⟩ | ⟨va, sm, hva, hsv, hkv⟩)
    · exact Or.inl ⟨t, rfl, htr⟩
    · rcases steps_preserves_closed hΦ hσ ha2_cl hsv with ⟨_, hsm⟩
      exact Or.inr ⟨va, sm, hva, hsv,
        (activeCtx_closedObsEquiv_congr (isActiveCtx_cellSetRight Δ hva) hb sm σ' out hsm hout).mpr hkv⟩

private theorem if_closedObsEquiv_congr {Δ : AdtEnv} {Φ : FunEnv} (hΦ : ClosedFunEnv Φ)
    {c1 c2 t1 t2 e1 e2 : Expr} (hc2_cl : freeVars c2 = [])
    (hc : ClosedObsEquiv Δ Φ Φ c1 c2) (ht : ClosedObsEquiv Δ Φ Φ t1 t2) (he : ClosedObsEquiv Δ Φ Φ e1 e2) :
    ClosedObsEquiv Δ Φ Φ (.if_ c1 t1 e1) (.if_ c2 t2 e2) := by
  refine ClosedObsEquiv.trans (activeCtx_closedObsEquiv_congr (isActiveCtx_ifCond Δ t1 e1) hc) ?_
  intro σ σ' out hσ hout
  rw [activeCtx_steps_terminal_iff (isActiveCtx_ifCond Δ t1 e1) hout,
      activeCtx_steps_terminal_iff (isActiveCtx_ifCond Δ t2 e2) hout]
  have hbranch : ∀ (vc : Expr) (sm : Store), IsValue vc → ClosedStore sm →
      (Steps Δ Φ (.if_ vc t1 e1) sm out σ' ↔ Steps Δ Φ (.if_ vc t2 e2) sm out σ') := by
    intro vc sm hvc hsm
    constructor
    · intro hs
      cases hs with
      | refl => cases hout with | inl hvv => cases hvv | inr htr => rcases htr with ⟨_, h⟩; cases h
      | trans h1 hr1 =>
        cases h1 with
        | ifStep hsv => exact False.elim (isValue_no_step hvc hsv)
        | ifTrap => cases hvc
        | ifTrue => exact .trans .ifTrue ((ht sm σ' out hsm hout).mp hr1)
        | ifFalse => exact .trans .ifFalse ((he sm σ' out hsm hout).mp hr1)
    · intro hs
      cases hs with
      | refl => cases hout with | inl hvv => cases hvv | inr htr => rcases htr with ⟨_, h⟩; cases h
      | trans h1 hr1 =>
        cases h1 with
        | ifStep hsv => exact False.elim (isValue_no_step hvc hsv)
        | ifTrap => cases hvc
        | ifTrue => exact .trans .ifTrue ((ht sm σ' out hsm hout).mpr hr1)
        | ifFalse => exact .trans .ifFalse ((he sm σ' out hsm hout).mpr hr1)
  constructor
  · rintro (⟨t, rfl, htr⟩ | ⟨vc, sm, hvc, hsv, hkv⟩)
    · exact Or.inl ⟨t, rfl, htr⟩
    · rcases steps_preserves_closed hΦ hσ hc2_cl hsv with ⟨_, hsm⟩
      exact Or.inr ⟨vc, sm, hvc, hsv, (hbranch vc sm hvc hsm).mp hkv⟩
  · rintro (⟨t, rfl, htr⟩ | ⟨vc, sm, hvc, hsv, hkv⟩)
    · exact Or.inl ⟨t, rfl, htr⟩
    · rcases steps_preserves_closed hΦ hσ hc2_cl hsv with ⟨_, hsm⟩
      exact Or.inr ⟨vc, sm, hvc, hsv, (hbranch vc sm hvc hsm).mpr hkv⟩

private theorem alphaEnvRel_closed_left {ρ : List (Ident × Ident)} {env1 env2 : List (Ident × Expr)}
    {e1 : Expr} (henv : AlphaEnvRel ρ env1 env2 (freeVars e1)) :
    freeVars (substMany env1 e1) = [] := by
  apply substMany_closed_freeVars_nil (fun p hp => (henv.1 p hp).2)
  intro z hz
  rcases henv.2.2 z hz with ⟨v, hlu, _⟩
  rw [hlu]; rfl

private theorem alphaEnvRel_closed_right {Φ : FunEnv} {ρ : List (Ident × Ident)}
    {env1 env2 : List (Ident × Expr)} {e1 e2 : Expr}
    (hr : AlphaOptRel Φ ρ e1 e2) (henv : AlphaEnvRel ρ env1 env2 (freeVars e1)) :
    freeVars (substMany env2 e2) = [] := by
  apply substMany_closed_freeVars_nil (fun p hp => (henv.2.1 p hp).2)
  intro w hw
  rcases alphaOptRel_freeVars_bound hr w hw with ⟨z, hz, heq⟩
  rcases henv.2.2 z hz with ⟨v, _, hlu2⟩
  rw [← heq, hlu2]; rfl

private theorem mem_snd_of_mem_zip {α β : Type} {ks : List α} {vs : List β} {p : α × β}
    (hp : p ∈ ks.zip vs) : p.2 ∈ vs := by
  induction ks generalizing vs with
  | nil => simp at hp
  | cons k kr ih =>
    cases vs with
    | nil => simp at hp
    | cons v vr =>
      rcases List.mem_cons.mp hp with rfl | hpr
      · exact List.mem_cons_self ..
      · exact List.mem_cons_of_mem _ (ih hpr)

mutual
/-- **Main Soundness of `AlphaOptRel` (`alphaOptRel_subst_closedObsEquiv`)**:
    Alpha-cloning (`coCloneTerm`), singleton block unwrapping, dead `coExprIsPure` `let` elimination,
    `TmMakeCls` wrapper introduction, fresh `let`/`match` binder renaming, and N-ary direct `TmVar`
    inlining (`coBuildCallArgsInline`) preserve exact closed-heap observational equivalence! -/
theorem alphaOptRel_subst_closedObsEquiv (Δ : AdtEnv) {Φ : FunEnv} (hΦ : ClosedFunEnv Φ) :
    {ρ : List (Ident × Ident)} → {e1 e2 : Expr} →
      AlphaOptRel Φ ρ e1 e2 →
      ∀ {env1 env2 : List (Ident × Expr)},
        AlphaEnvRel ρ env1 env2 (freeVars e1) →
        ClosedObsEquiv Δ Φ Φ (substMany env1 e1) (substMany env2 e2)
  | _, _, _, .lit _ l, env1, env2, _ => by
    rw [(substMany_atom_eq env1).1 l, (substMany_atom_eq env2).1 l]
    exact ClosedObsEquiv.refl _ _ _
  | _, _, _, .loc _ l, env1, env2, _ => by
    rw [(substMany_atom_eq env1).2.1 l, (substMany_atom_eq env2).2.1 l]
    exact ClosedObsEquiv.refl _ _ _
  | _, _, _, .taskRef _ t, env1, env2, _ => by
    rw [(substMany_atom_eq env1).2.2.1 t, (substMany_atom_eq env2).2.2.1 t]
    exact ClosedObsEquiv.refl _ _ _
  | _, _, _, .syncRef _ k n, env1, env2, _ => by
    rw [(substMany_atom_eq env1).2.2.2.1 k n, (substMany_atom_eq env2).2.2.2.1 k n]
    exact ClosedObsEquiv.refl _ _ _
  | _, _, _, .trap _ t, env1, env2, _ => by
    rw [(substMany_atom_eq env1).2.2.2.2 t, (substMany_atom_eq env2).2.2.2.2 t]
    exact ClosedObsEquiv.refl _ _ _
  | _, _, _, .var ρ x, env1, env2, henv => by
    rw [substMany_var_lookup (fun p hp => (henv.1 p hp).2) x,
        substMany_var_lookup (fun p hp => (henv.2.1 p hp).2) (lookupRename ρ x)]
    rcases henv.2.2 x (by simp [freeVars]) with ⟨v, h1, h2⟩
    rw [h1, h2]
    exact ClosedObsEquiv.refl _ _ _
  | _, .block [a1], _, .unwrapBlock1 ha, env1, env2, henv => by
    rw [substMany_block_eq]
    simp only [substManyList, List.map]
    have hblk : ClosedObsEquiv Δ Φ Φ (.block [substMany env1 a1]) (substMany env1 a1) :=
      ClosedObsEquiv.of_obsEquiv (obsEquiv_of_det_step (fun _ => .blockSingle))
    exact ClosedObsEquiv.trans hblk
      (alphaOptRel_subst_closedObsEquiv Δ hΦ ha
        (alphaEnvRel_mono (s1 := freeVars a1) henv (fun z hz => by simp [freeVars, freeVarsList, hz])))
  | ρ, _, _, @AlphaOptRel.dropPureLet _ _ x rhs1 b1 _ hpure hxnot hb, env1, env2, henv => by
    rw [substMany_let_eq]
    have henv_rhs : AlphaEnvRel ρ env1 env2 (freeVars rhs1) :=
      alphaEnvRel_mono henv (fun z hz => by simp [freeVars, hz])
    have henv_b : AlphaEnvRel ρ env1 env2 (freeVars b1) :=
      alphaEnvRel_mono henv (fun z hz => by
        have hzx : z ≠ x := fun h => by subst h; exact hxnot hz
        simp [freeVars, hz, hzx])
    have hrhs_cl : freeVars (substMany env1 rhs1) = [] := alphaEnvRel_closed_left henv_rhs
    have hrhs_p : coExprIsPure (substMany env1 rhs1) = true :=
      coExprIsPure_substMany_vals env1 (fun p hp => (henv.1 p hp).1) hpure
    have hb_flt : substMany (env1.filter (fun p => !(x == p.1))) b1 = substMany env1 b1 := by
      apply substMany_congr_lookup
      · exact fun p hp => (henv.1 p (List.mem_filter.mp hp).1).2
      · exact fun p hp => (henv.1 p hp).2
      · intro z hz
        have hzx : z ≠ x := fun h => by subst h; exact hxnot hz
        have hxz : (x == z) = false := beq_false_of_ne (Ne.symm hzx)
        exact lookupSubstEnv_filter_true (fun p _ heq => by have := eq_of_beq heq; subst this; simp [hxz])
    rw [hb_flt]
    have hb_cl : freeVars (substMany env1 b1) = [] := alphaEnvRel_closed_left henv_b
    have hxnot' : x ∉ freeVars (substMany env1 b1) := by rw [hb_cl]; intro h; cases h
    have hdrop : ClosedObsEquiv Δ Φ Φ (.let_ x (substMany env1 rhs1) (substMany env1 b1)) (substMany env1 b1) :=
      ClosedObsEquiv.of_obsEquiv (coFinishLetWithDeadElim_coExprIsPure_obsEquiv Δ Φ hrhs_cl hrhs_p hxnot')
    exact ClosedObsEquiv.trans hdrop (alphaOptRel_subst_closedObsEquiv Δ hΦ hb henv_b)
  | ρ, e1, _, @AlphaOptRel.introPureLetRight _ _ y _ rhs2 b2 hpure2 hynot2 hfvrhs2 hb, env1, env2, henv => by
    rw [substMany_let_eq]
    have hrhs2_cl : freeVars (substMany env2 rhs2) = [] := by
      apply substMany_closed_freeVars_nil (fun p hp => (henv.2.1 p hp).2)
      intro w hw
      rcases hfvrhs2 w hw with ⟨z, hz, heq⟩
      rcases henv.2.2 z hz with ⟨v, _, hlu2⟩
      rw [← heq, hlu2]; rfl
    have hrhs2_p : coExprIsPure (substMany env2 rhs2) = true :=
      coExprIsPure_substMany_vals env2 (fun p hp => (henv.2.1 p hp).1) hpure2
    have hb2_flt : substMany (env2.filter (fun p => !(y == p.1))) b2 = substMany env2 b2 := by
      apply substMany_congr_lookup
      · exact fun p hp => (henv.2.1 p (List.mem_filter.mp hp).1).2
      · exact fun p hp => (henv.2.1 p hp).2
      · intro w hw
        have hwy : w ≠ y := fun h => by subst h; exact hynot2 hw
        have hyw : (y == w) = false := beq_false_of_ne (Ne.symm hwy)
        exact lookupSubstEnv_filter_true (fun p _ heq => by have := eq_of_beq heq; subst this; simp [hyw])
    rw [hb2_flt]
    have hb2_cl : freeVars (substMany env2 b2) = [] := alphaEnvRel_closed_right hb henv
    have hynot2' : y ∉ freeVars (substMany env2 b2) := by rw [hb2_cl]; intro h; cases h
    have hdrop2 : ClosedObsEquiv Δ Φ Φ (.let_ y (substMany env2 rhs2) (substMany env2 b2)) (substMany env2 b2) :=
      ClosedObsEquiv.of_obsEquiv (coFinishLetWithDeadElim_coExprIsPure_obsEquiv Δ Φ hrhs2_cl hrhs2_p hynot2')
    exact ClosedObsEquiv.trans (alphaOptRel_subst_closedObsEquiv Δ hΦ hb henv) (ClosedObsEquiv.symm hdrop2)
  | ρ, _, _, @AlphaOptRel.inlineDirVars _ _ fn fd srcVars e2 hfd hlen hnodup hclosed hb, env1, env2, henv => by
    rw [substMany_applyDir_eq]
    have hsrc_mem : ∀ x ∈ srcVars, x ∈ freeVars (.applyDir fn (srcVars.map Expr.var)) := by
      intro x hx
      have hfv_vars : ∀ l : List Ident, ∀ u ∈ l, u ∈ freeVarsList (l.map Expr.var) := by
        intro l; induction l with
        | nil => intro _ h; cases h
        | cons hd tl ih =>
          intro u hu; rcases List.mem_cons.mp hu with rfl | hut
          · simp [freeVarsList, freeVars]
          · simp [freeVarsList, ih u hut]
      exact hfv_vars srcVars x hx
    let vs := substManyList env1 (srcVars.map Expr.var)
    have hvs_val_cl : ∀ v ∈ vs, IsValue v ∧ freeVars v = [] := by
      intro v hv
      simp only [vs, substManyList, List.map_map, List.mem_map, Function.comp] at hv
      rcases hv with ⟨x, hx, rfl⟩
      rcases henv.2.2 x (hsrc_mem x hx) with ⟨w, hlu1, _⟩
      rw [substMany_var_lookup (fun p hp => (henv.1 p hp).2) x, hlu1]
      exact lookupSubstEnv_isSome_val_cl henv.1 hlu1
    have hvs_len : vs.length = fd.params.length := by simp [vs, substManyList, hlen]
    have hbeta : ClosedObsEquiv Δ Φ Φ (.applyDir fn vs) (substMany (zipParams fd.params vs) fd.body) :=
      ClosedObsEquiv.of_obsEquiv (obsEquiv_of_det_step (fun _ => .applyDirBeta hfd (fun v hv => (hvs_val_cl v hv).1) hvs_len))
    refine ClosedObsEquiv.trans hbeta (alphaOptRel_subst_closedObsEquiv Δ hΦ hb ?_)
    refine ⟨?_, henv.2.1, ?_⟩
    · intro p hp
      unfold zipParams at hp
      exact hvs_val_cl p.2 (mem_snd_of_mem_zip hp)
    · intro z hz
      have hz_mem : z ∈ fd.params.map Prod.fst := hclosed z hz
      rcases List.mem_iff_getElem.mp hz_mem with ⟨i, hi, rfl⟩
      have hi_src : i < srcVars.length := by simp at hi; omega
      have hlu_zip : lookupSubstEnv (fd.params.map Prod.fst)[i] (zipParams fd.params vs) =
          some (vs[i]'(by simp [hvs_len]; simp at hi; exact hi)) := by
        unfold zipParams
        exact lookupSubstEnv_nodup_zip (vs := vs) hnodup (by simp [hvs_len]) i hi
      have hren_zip : lookupRename ((fd.params.map Prod.fst).zip (srcVars.map (lookupRename ρ)))
          (fd.params.map Prod.fst)[i] = lookupRename ρ srcVars[i] := by
        simpa using lookupRename_nodup_zip hnodup (ys := srcVars.map (lookupRename ρ)) (by simp [hlen]) [] i hi
      rcases henv.2.2 srcVars[i] (hsrc_mem srcVars[i] (List.getElem_mem hi_src)) with ⟨vx, hlu_x1, hlu_x2⟩
      have hvs_i : vs[i]'(by simp [hvs_len]; simp at hi; exact hi) = vx := by
        simp only [vs, substManyList, List.getElem_map]
        rw [substMany_var_lookup (fun p hp => (henv.1 p hp).2) srcVars[i], hlu_x1]
      exact ⟨vx, by rw [hlu_zip, hvs_i], by rw [hren_zip, hlu_x2]⟩
  | ρ, _, _, @AlphaOptRel.letAlpha _ _ x y a1 a2 b1 b2 ha hfresh hb, env1, env2, henv => by
    rw [substMany_let_eq, substMany_let_eq]
    have henv_a : AlphaEnvRel ρ env1 env2 (freeVars a1) :=
      alphaEnvRel_mono henv (fun z hz => by simp [freeVars, hz])
    have ha_eq := alphaOptRel_subst_closedObsEquiv Δ hΦ ha henv_a
    have ha1_cl : freeVars (substMany env1 a1) = [] := alphaEnvRel_closed_left henv_a
    intro σ σ' out hσ hout
    rw [steps_let_terminal_iff hout, steps_let_terminal_iff hout]
    have hbody_eq : ∀ (va : Expr) (sm : Store), IsValue va → freeVars va = [] → ClosedStore sm →
        (Steps Δ Φ (subst x va (substMany (env1.filter (fun p => !(x == p.1))) b1)) sm out σ' ↔
         Steps Δ Φ (subst y va (substMany (env2.filter (fun p => !(y == p.1))) b2)) sm out σ') := by
      intro va sm hva hva_cl hsm
      rw [subst_substMany_filter_eq x hva_cl (fun p hp => (henv.1 p hp).2) b1,
          subst_substMany_filter_eq y hva_cl (fun p hp => (henv.2.1 p hp).2) b2]
      have henv_b : AlphaEnvRel ((x, y) :: ρ) ((x, va) :: env1) ((y, va) :: env2) (freeVars b1) := by
        refine ⟨?_, ?_, ?_⟩
        · intro p hp; rcases List.mem_cons.mp hp with rfl | hp'
          · exact ⟨hva, hva_cl⟩
          · exact henv.1 p hp'
        · intro p hp; rcases List.mem_cons.mp hp with rfl | hp'
          · exact ⟨hva, hva_cl⟩
          · exact henv.2.1 p hp'
        · intro z hz
          by_cases hzx : z = x
          · subst hzx
            exact ⟨va, by simp [lookupSubstEnv], by simp [lookupRename, lookupSubstEnv]⟩
          · have hzx_b : (z == x) = false := beq_false_of_ne hzx
            have hry : (lookupRename ρ z == y) = false := beq_false_of_ne (hfresh z hz hzx)
            rcases henv.2.2 z (by simp [freeVars, hz, hzx]) with ⟨vz, h1, h2⟩
            exact ⟨vz, by simp [lookupSubstEnv, hzx_b, h1],
                       by simp [lookupRename, hzx_b, lookupSubstEnv, hry, h2]⟩
      exact alphaOptRel_subst_closedObsEquiv Δ hΦ hb henv_b sm σ' out hsm hout
    constructor
    · rintro (⟨t, rfl, htr⟩ | ⟨va, sm, hva, hsv1, hkb1⟩)
      · exact Or.inl ⟨t, rfl, (ha_eq σ σ' (.trap t) hσ (Or.inr ⟨t, rfl⟩)).mp htr⟩
      · rcases steps_preserves_closed hΦ hσ ha1_cl hsv1 with ⟨hva_cl, hsm⟩
        have hsv2 := (ha_eq σ sm va hσ (Or.inl hva)).mp hsv1
        exact Or.inr ⟨va, sm, hva, hsv2, (hbody_eq va sm hva hva_cl hsm).mp hkb1⟩
    · rintro (⟨t, rfl, htr⟩ | ⟨va, sm, hva, hsv2, hkb2⟩)
      · exact Or.inl ⟨t, rfl, (ha_eq σ σ' (.trap t) hσ (Or.inr ⟨t, rfl⟩)).mpr htr⟩
      · have hsv1 := (ha_eq σ sm va hσ (Or.inl hva)).mpr hsv2
        rcases steps_preserves_closed hΦ hσ ha1_cl hsv1 with ⟨hva_cl, hsm⟩
        exact Or.inr ⟨va, sm, hva, hsv1, (hbody_eq va sm hva hva_cl hsm).mpr hkb2⟩
  | _, _, _, .tuple hrl, env1, env2, henv => by
    rw [substMany_tuple_eq, substMany_tuple_eq]
    rcases alphaOptRelList_subst_closedObsEquiv Δ hΦ hrl henv with ⟨hcl2, hlen, heq⟩
    exact activeList_closedObsEquiv_congr hΦ Expr.tuple
      (fun vs hvs rest => isActiveCtx_tupleElem Δ hvs rest) [] (fun _ h => by cases h)
      hcl2 hlen heq
  | _, _, _, .block hrl, env1, env2, henv => by
    rw [substMany_block_eq, substMany_block_eq]
    rcases alphaOptRelList_subst_closedObsEquiv Δ hΦ hrl henv with ⟨hcl2, hlen, heq⟩
    exact block_closedObsEquiv_congr hΦ hcl2 hlen heq
  | _, _, _, .makeData adt tag hrl, env1, env2, henv => by
    rw [substMany_makeData_eq, substMany_makeData_eq]
    rcases alphaOptRelList_subst_closedObsEquiv Δ hΦ hrl henv with ⟨hcl2, hlen, heq⟩
    exact activeList_closedObsEquiv_congr hΦ (Expr.makeData adt tag)
      (fun vs hvs rest => isActiveCtx_makeDataElem Δ adt tag hvs rest) [] (fun _ h => by cases h)
      hcl2 hlen heq
  | _, _, _, .concPrim op hrl, env1, env2, henv => by
    rw [substMany_concPrim_eq, substMany_concPrim_eq]
    rcases alphaOptRelList_subst_closedObsEquiv Δ hΦ hrl henv with ⟨hcl2, hlen, heq⟩
    exact activeList_closedObsEquiv_congr hΦ (Expr.concPrim op)
      (fun vs hvs rest => isActiveCtx_concPrimElem Δ op hvs rest) [] (fun _ h => by cases h)
      hcl2 hlen heq
  | _, .apply fn1 args1, _, .apply hf ha, env1, env2, henv => by
    rw [substMany_apply_eq, substMany_apply_eq]
    have henv_f := alphaEnvRel_mono (s1 := freeVars fn1) henv (fun z hz => by simp [freeVars, hz])
    have henv_a := alphaEnvRel_mono (s1 := freeVarsList args1) henv (fun z hz => by simp [freeVars, hz])
    rcases alphaOptRelList_subst_closedObsEquiv Δ hΦ ha henv_a with ⟨hcl2, hlen, heq⟩
    exact apply_closedObsEquiv_congr hΦ (alphaEnvRel_closed_right hf henv_f) hcl2
      (alphaOptRel_subst_closedObsEquiv Δ hΦ hf henv_f) hlen heq
  | _, _, _, .applyDir nm ha, env1, env2, henv => by
    rw [substMany_applyDir_eq, substMany_applyDir_eq]
    rcases alphaOptRelList_subst_closedObsEquiv Δ hΦ ha henv with ⟨hcl2, hlen, heq⟩
    exact activeList_closedObsEquiv_congr hΦ (Expr.applyDir nm)
      (fun vs hvs rest => isActiveCtx_applyDirArg Δ nm hvs rest) [] (fun _ h => by cases h)
      hcl2 hlen heq
  | _, .bin _ a1 b1, _, .bin op ha hb, env1, env2, henv => by
    rw [substMany_bin_eq, substMany_bin_eq]
    have henv_a := alphaEnvRel_mono (s1 := freeVars a1) henv (fun z hz => by simp [freeVars, hz])
    have henv_b := alphaEnvRel_mono (s1 := freeVars b1) henv (fun z hz => by simp [freeVars, hz])
    exact bin_closedObsEquiv_congr hΦ op (alphaEnvRel_closed_right ha henv_a)
      (alphaOptRel_subst_closedObsEquiv Δ hΦ ha henv_a)
      (alphaOptRel_subst_closedObsEquiv Δ hΦ hb henv_b)
  | _, _, _, .un op ha, env1, env2, henv => by
    rw [substMany_un_eq, substMany_un_eq]
    exact activeCtx_closedObsEquiv_congr (isActiveCtx_un Δ op)
      (alphaOptRel_subst_closedObsEquiv Δ hΦ ha henv)
  | _, .if_ c1 t1 e1, _, .if_ hc ht he, env1, env2, henv => by
    rw [substMany_if_eq, substMany_if_eq]
    have henv_c := alphaEnvRel_mono (s1 := freeVars c1) henv (fun z hz => by simp [freeVars, hz])
    have henv_t := alphaEnvRel_mono (s1 := freeVars t1) henv (fun z hz => by simp [freeVars, hz])
    have henv_e := alphaEnvRel_mono (s1 := freeVars e1) henv (fun z hz => by simp [freeVars, hz])
    exact if_closedObsEquiv_congr hΦ (alphaEnvRel_closed_right hc henv_c)
      (alphaOptRel_subst_closedObsEquiv Δ hΦ hc henv_c)
      (alphaOptRel_subst_closedObsEquiv Δ hΦ ht henv_t)
      (alphaOptRel_subst_closedObsEquiv Δ hΦ he henv_e)
  | _, .while_ c1 b1, _, .while_ hc hb, env1, env2, henv => by
    rw [substMany_while_eq, substMany_while_eq]
    have henv_c := alphaEnvRel_mono (s1 := freeVars c1) henv (fun z hz => by simp [freeVars, hz])
    have henv_b := alphaEnvRel_mono (s1 := freeVars b1) henv (fun z hz => by simp [freeVars, hz])
    exact while_closedObsEquiv_congr hΦ
      (alphaEnvRel_closed_left henv_c) (alphaEnvRel_closed_right hc henv_c)
      (alphaEnvRel_closed_left henv_b) (alphaEnvRel_closed_right hb henv_b)
      (alphaOptRel_subst_closedObsEquiv Δ hΦ hc henv_c)
      (alphaOptRel_subst_closedObsEquiv Δ hΦ hb henv_b)
  | _, .match_ s1 arms1, .match_ s2 arms2, .matchAlpha hs ha, env1, env2, henv => by
    rw [substMany_match_eq, substMany_match_eq]
    have henv_s := alphaEnvRel_mono (s1 := freeVars s1) henv (fun z hz => by simp [freeVars, hz])
    have henv_a := alphaEnvRel_mono (s1 := freeVarsArms arms1) henv (fun z hz => by simp [freeVars, hz])
    have hs_eq := alphaOptRel_subst_closedObsEquiv Δ hΦ hs henv_s
    refine ClosedObsEquiv.trans
      (activeCtx_closedObsEquiv_congr (isActiveCtx_matchScrut Δ (substManyArms env1 arms1)) hs_eq) ?_
    intro σ σ' out hσ hout
    rw [activeCtx_steps_terminal_iff (isActiveCtx_matchScrut Δ (substManyArms env1 arms1)) hout,
        activeCtx_steps_terminal_iff (isActiveCtx_matchScrut Δ (substManyArms env2 arms2)) hout]
    have hs2_cl : freeVars (substMany env2 s2) = [] := alphaEnvRel_closed_right hs henv_s
    constructor
    · rintro (⟨t, rfl, htr⟩ | ⟨vs, sm, hvs, hsv, hkv⟩)
      · exact Or.inl ⟨t, rfl, htr⟩
      · rcases steps_preserves_closed hΦ hσ hs2_cl hsv with ⟨hvs_cl, hsm⟩
        have har := alphaOptRelArms_subst_closedObsEquiv Δ hΦ ha henv_a vs hvs hvs_cl
        exact Or.inr ⟨vs, sm, hvs, hsv, (har sm σ' out hsm hout).mp hkv⟩
    · rintro (⟨t, rfl, htr⟩ | ⟨vs, sm, hvs, hsv, hkv⟩)
      · exact Or.inl ⟨t, rfl, htr⟩
      · rcases steps_preserves_closed hΦ hσ hs2_cl hsv with ⟨hvs_cl, hsm⟩
        have har := alphaOptRelArms_subst_closedObsEquiv Δ hΦ ha henv_a vs hvs hvs_cl
        exact Or.inr ⟨vs, sm, hvs, hsv, (har sm σ' out hsm hout).mpr hkv⟩
  | _, _, _, .getTag ha, env1, env2, henv => by
    rw [substMany_getTag_eq, substMany_getTag_eq]
    exact activeCtx_closedObsEquiv_congr (isActiveCtx_getTag Δ)
      (alphaOptRel_subst_closedObsEquiv Δ hΦ ha henv)
  | _, _, _, .cellNew ha, env1, env2, henv => by
    rw [substMany_cellNew_eq, substMany_cellNew_eq]
    exact activeCtx_closedObsEquiv_congr (isActiveCtx_cellNew Δ)
      (alphaOptRel_subst_closedObsEquiv Δ hΦ ha henv)
  | _, _, _, .cellGet ha, env1, env2, henv => by
    rw [substMany_cellGet_eq, substMany_cellGet_eq]
    exact activeCtx_closedObsEquiv_congr (isActiveCtx_cellGet Δ)
      (alphaOptRel_subst_closedObsEquiv Δ hΦ ha henv)
  | _, .cellSet a1 b1, _, .cellSet ha hb, env1, env2, henv => by
    rw [substMany_cellSet_eq, substMany_cellSet_eq]
    have henv_a := alphaEnvRel_mono (s1 := freeVars a1) henv (fun z hz => by simp [freeVars, hz])
    have henv_b := alphaEnvRel_mono (s1 := freeVars b1) henv (fun z hz => by simp [freeVars, hz])
    exact cellSet_closedObsEquiv_congr hΦ (alphaEnvRel_closed_right ha henv_a)
      (alphaOptRel_subst_closedObsEquiv Δ hΦ ha henv_a)
      (alphaOptRel_subst_closedObsEquiv Δ hΦ hb henv_b)
  | _, _, _, .spawn ha, env1, env2, henv => by
    rw [substMany_spawn_eq, substMany_spawn_eq]
    exact activeCtx_closedObsEquiv_congr (isActiveCtx_spawn Δ)
      (alphaOptRel_subst_closedObsEquiv Δ hΦ ha henv)
  | _, _, _, .await ha, env1, env2, henv => by
    rw [substMany_await_eq, substMany_await_eq]
    exact activeCtx_closedObsEquiv_congr (isActiveCtx_await Δ)
      (alphaOptRel_subst_closedObsEquiv Δ hΦ ha henv)

theorem alphaOptRelList_subst_closedObsEquiv (Δ : AdtEnv) {Φ : FunEnv} (hΦ : ClosedFunEnv Φ) :
    {ρ : List (Ident × Ident)} → {es1 es2 : List Expr} →
      AlphaOptRelList Φ ρ es1 es2 →
      ∀ {env1 env2 : List (Ident × Expr)},
        AlphaEnvRel ρ env1 env2 (freeVarsList es1) →
        (∀ e ∈ substManyList env2 es2, freeVars e = []) ∧
        (substManyList env1 es1).length = (substManyList env2 es2).length ∧
        (∀ i (h1 : i < (substManyList env1 es1).length) (h2 : i < (substManyList env2 es2).length),
          ClosedObsEquiv Δ Φ Φ (substManyList env1 es1)[i] (substManyList env2 es2)[i])
  | _, _, _, .nil _, _, _, _ =>
    ⟨fun _ h => by simp [substManyList] at h, rfl, fun i h1 _ => by simp [substManyList] at h1⟩
  | _, e1 :: r1, _, .cons he hr, env1, env2, henv => by
    have henv_e := alphaEnvRel_mono (s1 := freeVars e1) henv (fun z hz => by simp [freeVarsList, hz])
    have henv_r := alphaEnvRel_mono (s1 := freeVarsList r1) henv (fun z hz => by simp [freeVarsList, hz])
    have he_eq := alphaOptRel_subst_closedObsEquiv Δ hΦ he henv_e
    have he2_cl := alphaEnvRel_closed_right he henv_e
    rcases alphaOptRelList_subst_closedObsEquiv Δ hΦ hr henv_r with ⟨hr_cl, hr_len, hr_eq⟩
    refine ⟨?_, by simp [substManyList] at hr_len ⊢; exact hr_len, ?_⟩
    · intro e hm; simp only [substManyList, List.map] at hm
      rcases List.mem_cons.mp hm with rfl | hmr
      · exact he2_cl
      · exact hr_cl e hmr
    · intro i h1 h2
      cases i with
      | zero => simpa [substManyList] using he_eq
      | succ j =>
        exact hr_eq j (by simp [substManyList] at h1 ⊢; exact h1) (by simp [substManyList] at h2 ⊢; exact h2)

theorem alphaOptRelArms_subst_closedObsEquiv (Δ : AdtEnv) {Φ : FunEnv} (hΦ : ClosedFunEnv Φ) :
    {ρ : List (Ident × Ident)} → {arms1 arms2 : List (Pat × Expr)} →
      AlphaOptRelArms Φ ρ arms1 arms2 →
      ∀ {env1 env2 : List (Ident × Expr)},
        AlphaEnvRel ρ env1 env2 (freeVarsArms arms1) →
        ∀ (vs : Expr), IsValue vs → freeVars vs = [] →
        ClosedObsEquiv Δ Φ Φ (.match_ vs (substManyArms env1 arms1))
                             (.match_ vs (substManyArms env2 arms2))
  | _, _, _, .nil _, _, _, _, vs, _, _ => by
    simp only [substManyArms, List.map]
    exact ClosedObsEquiv.refl _ _ _
  | ρ, _, _, @AlphaOptRelArms.cons _ _ p1 p2 pairs b1 b2 r1 r2 hp hnd1 hnd2 hfresh hb hr,
    env1, env2, henv, vs, hvs, hvs_cl => by
    simp only [substManyArms, List.map]
    rcases patAlphaRel_matchPat hp vs with ⟨hn1, hn2⟩ | ⟨ws, hws_len, hm1, hm2⟩
    · have hs1 : ClosedObsEquiv Δ Φ Φ
          (.match_ vs ((p1, substMany (env1.filter (fun p => !((patBoundNames p1).contains p.1))) b1) :: substManyArms env1 r1))
          (.match_ vs (substManyArms env1 r1)) :=
        ClosedObsEquiv.of_obsEquiv (obsEquiv_of_det_step (fun _ => .matchMiss hvs hn1))
      have hs2 : ClosedObsEquiv Δ Φ Φ
          (.match_ vs ((p2, substMany (env2.filter (fun p => !((patBoundNames p2).contains p.1))) b2) :: substManyArms env2 r2))
          (.match_ vs (substManyArms env2 r2)) :=
        ClosedObsEquiv.of_obsEquiv (obsEquiv_of_det_step (fun _ => .matchMiss hvs hn2))
      have henv_r := alphaEnvRel_mono (s1 := freeVarsArms r1) henv (fun z hz => by simp [freeVarsArms, hz])
      exact ClosedObsEquiv.trans hs1
        (ClosedObsEquiv.trans (alphaOptRelArms_subst_closedObsEquiv Δ hΦ hr henv_r vs hvs hvs_cl)
          (ClosedObsEquiv.symm hs2))
    · rcases patAlphaRel_boundNames hp with ⟨hbn1, _⟩
      have hws_val_cl : ∀ w ∈ ws, IsValue w ∧ freeVars w = [] := by
        intro w hw
        have hmem_zip : ∃ k, (k, w) ∈ (pairs.map Prod.fst).zip ws := by
          rcases List.mem_iff_getElem.mp hw with ⟨i, hi, rfl⟩
          have hi_z : i < ((pairs.map Prod.fst).zip ws).length := by simp [← hws_len, hi]
          refine ⟨(pairs.map Prod.fst)[i]'(by simp [← hws_len, hi]), ?_⟩
          have hget : ((pairs.map Prod.fst).zip ws)[i]'hi_z =
              ((pairs.map Prod.fst)[i]'(by simp [← hws_len, hi]), ws[i]) := List.getElem_zip
          rw [← hget]
          exact List.getElem_mem hi_z
        rcases hmem_zip with ⟨k, hk⟩
        exact ⟨matchPat_isValue p1 hvs hm1 (k, w) hk, (matchPat_closed hvs_cl hm1).1 (k, w) hk⟩
      have hs1 : ClosedObsEquiv Δ Φ Φ
          (.match_ vs ((p1, substMany (env1.filter (fun p => !((patBoundNames p1).contains p.1))) b1) :: substManyArms env1 r1))
          (substMany ((pairs.map Prod.fst).zip ws) (substMany (env1.filter (fun p => !((patBoundNames p1).contains p.1))) b1)) :=
        ClosedObsEquiv.of_obsEquiv (obsEquiv_of_det_step (fun _ => .matchHit hvs hm1))
      have hs2 : ClosedObsEquiv Δ Φ Φ
          (.match_ vs ((p2, substMany (env2.filter (fun p => !((patBoundNames p2).contains p.1))) b2) :: substManyArms env2 r2))
          (substMany ((pairs.map Prod.snd).zip ws) (substMany (env2.filter (fun p => !((patBoundNames p2).contains p.1))) b2)) :=
        ClosedObsEquiv.of_obsEquiv (obsEquiv_of_det_step (fun _ => .matchHit hvs hm2))
      have hflt1 := substMany_binds_filter_eq (p := p1) (binds := (pairs.map Prod.fst).zip ws)
        (fun q hq => (hws_val_cl q.2 (mem_snd_of_mem_zip hq)).2)
        (fun q hq => (henv.1 q hq).2) (matchPat_fst_eq_patBoundNames p1 hm1) b1
      have hflt2 := substMany_binds_filter_eq (p := p2) (binds := (pairs.map Prod.snd).zip ws)
        (fun q hq => (hws_val_cl q.2 (mem_snd_of_mem_zip hq)).2)
        (fun q hq => (henv.2.1 q hq).2) (matchPat_fst_eq_patBoundNames p2 hm2) b2
      refine ClosedObsEquiv.trans hs1 (ClosedObsEquiv.trans ?_ (ClosedObsEquiv.symm hs2))
      rw [hflt1, hflt2]
      apply alphaOptRel_subst_closedObsEquiv Δ hΦ hb
      refine ⟨?_, ?_, ?_⟩
      · intro q hq; rcases List.mem_append.mp hq with h1 | h2
        · exact hws_val_cl q.2 (mem_snd_of_mem_zip h1)
        · exact henv.1 q h2
      · intro q hq; rcases List.mem_append.mp hq with h1 | h2
        · exact hws_val_cl q.2 (mem_snd_of_mem_zip h1)
        · exact henv.2.1 q h2
      · intro z hz
        by_cases hzp : z ∈ pairs.map Prod.fst
        · rcases List.mem_iff_getElem.mp hzp with ⟨i, hi, rfl⟩
          have hi2 : i < (pairs.map Prod.snd).length := by simp at hi ⊢; exact hi
          have hlu1 := lookupSubstEnv_nodup_zip (vs := ws) hnd1 (by simp [hws_len]) i hi
          have hlu2 := lookupSubstEnv_nodup_zip (vs := ws) hnd2 (by simp [hws_len]) i hi2
          have hren := lookupRename_nodup_zip hnd1 (ys := pairs.map Prod.snd) (by simp) ρ i hi
          rw [pairs_zip_eq] at hren
          exact ⟨ws[i]'(by simp [hws_len]; simp at hi; exact hi),
                 by rw [lookupSubstEnv_append, hlu1],
                 by rw [hren, lookupSubstEnv_append, hlu2]⟩
        · have hf1 : z ∉ ((pairs.map Prod.fst).zip ws).map Prod.fst := by
            rw [zip_fst_eq_of_eq_len (by simp [hws_len])]; exact hzp
          have hf2 : lookupRename ρ z ∉ ((pairs.map Prod.snd).zip ws).map Prod.fst := by
            rw [zip_fst_eq_of_eq_len (by simp [hws_len])]; exact hfresh z hz hzp
          have hct1 : (patBoundNames p1).contains z = false := by
            cases h : (patBoundNames p1).contains z
            · rfl
            · exfalso; exact hzp (hbn1 ▸ List.contains_iff_mem.mp h)
          have hz_arms : z ∈ freeVarsArms ((p1, b1) :: r1) := by
            simp only [freeVarsArms, List.mem_append, List.mem_filter]
            exact Or.inl ⟨hz, by rw [hct1]; rfl⟩
          rcases henv.2.2 z hz_arms with ⟨vz, hl1, hl2⟩
          exact ⟨vz, by rw [lookupSubstEnv_not_mem_fst hf1, hl1],
                     by rw [lookupRename_not_mem_fst hzp, lookupSubstEnv_not_mem_fst hf2, hl2]⟩
end

/- Executable decidable checker `checkAlphaOpt` for `AlphaOptRel` + executable `coCloneOptExpr`
   matching `coCloneTerm` + `coOptTerm` singleton block unwrapping on real `.gscore` artifacts. -/
def checkListNodup : List Ident → Bool
  | [] => true
  | x :: r => !(r.contains x) && checkListNodup r

private theorem checkListNodup_sound : {l : List Ident} → checkListNodup l = true → l.Nodup
  | [], _ => List.nodup_nil
  | x :: r, h => by
    simp only [checkListNodup, Bool.and_eq_true, Bool.not_eq_true'] at h
    refine List.nodup_cons.mpr ⟨?_, checkListNodup_sound h.2⟩
    intro hm
    have hct : r.contains x = true := List.contains_iff_mem.mpr hm
    rw [hct] at h; cases h.1

mutual
def checkPatAlpha : Pat → Pat → Option (List (Ident × Ident))
  | .wild, .wild => some []
  | .lit l1, .lit l2 => if l1 = l2 then some [] else none
  | .var x, .var y => some [(x, y)]
  | .tuple ps1, .tuple ps2 => checkPatAlphaList ps1 ps2
  | .ctor a1 t1 ps1, .ctor a2 t2 ps2 =>
    if a1 = a2 ∧ t1 = t2 then checkPatAlphaList ps1 ps2 else none
  | _, _ => none

def checkPatAlphaList : List Pat → List Pat → Option (List (Ident × Ident))
  | [], [] => some []
  | p1 :: r1, p2 :: r2 =>
    match checkPatAlpha p1 p2, checkPatAlphaList r1 r2 with
    | some b1, some b2 => some (b1 ++ b2)
    | _, _ => none
  | _, _ => none
end

mutual
private theorem checkPatAlpha_sound :
    (p1 p2 : Pat) → {pairs : List (Ident × Ident)} →
      checkPatAlpha p1 p2 = some pairs → PatAlphaRel p1 p2 pairs
  | .wild, p2, _, h => by cases p2 <;> simp [checkPatAlpha] at h; subst h; exact .wild
  | .lit l1, p2, _, h => by
    cases p2 <;> simp [checkPatAlpha] at h
    rcases h with ⟨rfl, rfl⟩; exact .lit l1
  | .var x, p2, _, h => by cases p2 <;> simp [checkPatAlpha] at h; subst h; exact .var x _
  | .tuple ps1, p2, _, h => by
    cases p2 <;> simp [checkPatAlpha] at h
    exact .tuple (checkPatAlphaList_sound ps1 _ h)
  | .ctor a1 t1 ps1, p2, _, h => by
    cases p2 <;> simp [checkPatAlpha] at h
    rcases h with ⟨⟨rfl, rfl⟩, hm⟩
    exact .ctor a1 t1 (checkPatAlphaList_sound ps1 _ hm)
termination_by p1 => sizeOf p1

private theorem checkPatAlphaList_sound :
    (ps1 ps2 : List Pat) → {pairs : List (Ident × Ident)} →
      checkPatAlphaList ps1 ps2 = some pairs → PatAlphaRelList ps1 ps2 pairs
  | [], ps2, _, h => by cases ps2 <;> simp [checkPatAlphaList] at h; subst h; exact .nil
  | p1 :: r1, ps2, _, h => by
    cases ps2 with
    | nil => simp [checkPatAlphaList] at h
    | cons p2 r2 =>
      simp only [checkPatAlphaList] at h
      cases h1 : checkPatAlpha p1 p2 <;> rw [h1] at h
      · cases h
      · cases h2 : checkPatAlphaList r1 r2 <;> rw [h2] at h
        · cases h
        · injection h with h; subst h
          exact .cons (checkPatAlpha_sound p1 p2 h1) (checkPatAlphaList_sound r1 r2 h2)
termination_by ps1 => sizeOf ps1
end

mutual
def checkAlphaOpt (ρ : List (Ident × Ident)) : Expr → Expr → Bool
  | .lit l1, .lit l2 => decide (l1 = l2)
  | .var x, .var y => decide (lookupRename ρ x = y)
  | .loc l1, .loc l2 => decide (l1 = l2)
  | .taskRef t1, .taskRef t2 => decide (t1 = t2)
  | .syncRef k1 n1, .syncRef k2 n2 => decide (k1 = k2 ∧ n1 = n2)
  | .trap t1, .trap t2 => decide (t1 = t2)
  | .block es1, e2 =>
    match es1 with
    | [a1] => checkAlphaOpt ρ a1 e2
    | _ => false
  | .let_ x a1 b1, .let_ y a2 b2 =>
    checkAlphaOpt ρ a1 a2 &&
    (freeVars b1).all (fun z => z == x || !(lookupRename ρ z == y)) &&
    checkAlphaOpt ((x, y) :: ρ) b1 b2
  | .bin op1 a1 b1, .bin op2 a2 b2 =>
    decide (op1 = op2) && checkAlphaOpt ρ a1 a2 && checkAlphaOpt ρ b1 b2
  | .un op1 a1, .un op2 a2 => decide (op1 = op2) && checkAlphaOpt ρ a1 a2
  | .if_ c1 t1 e1, .if_ c2 t2 e2 =>
    checkAlphaOpt ρ c1 c2 && checkAlphaOpt ρ t1 t2 && checkAlphaOpt ρ e1 e2
  | .applyDir nm1 args1, .applyDir nm2 args2 =>
    decide (nm1 = nm2) && checkAlphaOptList ρ args1 args2
  | .apply fn1 args1, .apply fn2 args2 =>
    checkAlphaOpt ρ fn1 fn2 && checkAlphaOptList ρ args1 args2
  | .tuple es1, .tuple es2 => checkAlphaOptList ρ es1 es2
  | .makeData a1 t1 es1, .makeData a2 t2 es2 =>
    decide (a1 = a2 ∧ t1 = t2) && checkAlphaOptList ρ es1 es2
  | .match_ s1 arms1, .match_ s2 arms2 =>
    checkAlphaOpt ρ s1 s2 && checkAlphaOptArms ρ arms1 arms2
  | _, _ => false

def checkAlphaOptList (ρ : List (Ident × Ident)) : List Expr → List Expr → Bool
  | [], [] => true
  | e1 :: r1, e2 :: r2 => checkAlphaOpt ρ e1 e2 && checkAlphaOptList ρ r1 r2
  | _, _ => false

def checkAlphaOptArms (ρ : List (Ident × Ident)) : List (Pat × Expr) → List (Pat × Expr) → Bool
  | [], [] => true
  | (p1, b1) :: r1, (p2, b2) :: r2 =>
    match checkPatAlpha p1 p2 with
    | none => false
    | some pairs =>
      checkListNodup (pairs.map Prod.fst) &&
      checkListNodup (pairs.map Prod.snd) &&
      (freeVars b1).all (fun z =>
        (pairs.map Prod.fst).contains z || !((pairs.map Prod.snd).contains (lookupRename ρ z))) &&
      checkAlphaOpt (pairs ++ ρ) b1 b2 &&
      checkAlphaOptArms ρ r1 r2
  | _, _ => false
end

mutual
theorem checkAlphaOpt_sound (Φ : FunEnv) (ρ : List (Ident × Ident)) :
    (e1 e2 : Expr) → checkAlphaOpt ρ e1 e2 = true → AlphaOptRel Φ ρ e1 e2
  | .lit l1, e2, h => by
    cases e2 <;> simp [checkAlphaOpt] at h; subst h; exact .lit ρ l1
  | .var x, e2, h => by
    cases e2 <;> simp [checkAlphaOpt] at h; subst h; exact .var ρ x
  | .loc l1, e2, h => by
    cases e2 <;> simp [checkAlphaOpt] at h; subst h; exact .loc ρ l1
  | .taskRef t1, e2, h => by
    cases e2 <;> simp [checkAlphaOpt] at h; subst h; exact .taskRef ρ t1
  | .syncRef k1 n1, e2, h => by
    cases e2 <;> simp [checkAlphaOpt] at h; rcases h with ⟨rfl, rfl⟩; exact .syncRef ρ k1 n1
  | .trap t1, e2, h => by
    cases e2 <;> simp [checkAlphaOpt] at h; subst h; exact .trap ρ t1
  | .block es1, e2, h => by
    cases es1 with
    | nil => simp [checkAlphaOpt] at h
    | cons a1 tl =>
      cases tl with
      | nil =>
        simp only [checkAlphaOpt] at h
        exact .unwrapBlock1 (checkAlphaOpt_sound Φ ρ a1 e2 h)
      | cons _ _ => simp [checkAlphaOpt] at h
  | .let_ x a1 b1, e2, h => by
    cases e2 with
    | let_ y a2 b2 =>
      simp only [checkAlphaOpt, Bool.and_eq_true] at h
      rcases h with ⟨⟨ha, hfr⟩, hb⟩
      refine .letAlpha (checkAlphaOpt_sound Φ ρ a1 a2 ha) ?_ (checkAlphaOpt_sound Φ ((x, y) :: ρ) b1 b2 hb)
      intro z hz hzx
      have hall := List.all_eq_true.mp hfr z hz
      have hzx_f : (z == x) = false := beq_false_of_ne hzx
      rw [hzx_f] at hall; simp at hall
      exact fun heq => by rw [heq] at hall; simp at hall
    | _ => simp [checkAlphaOpt] at h
  | .bin op1 a1 b1, e2, h => by
    cases e2 with
    | bin op2 a2 b2 =>
      simp only [checkAlphaOpt, Bool.and_eq_true] at h
      rcases h with ⟨⟨hop, ha⟩, hb⟩
      rcases of_decide_eq_true hop with rfl
      exact .bin op1 (checkAlphaOpt_sound Φ ρ a1 a2 ha) (checkAlphaOpt_sound Φ ρ b1 b2 hb)
    | _ => simp [checkAlphaOpt] at h
  | .un op1 a1, e2, h => by
    cases e2 with
    | un op2 a2 =>
      simp only [checkAlphaOpt, Bool.and_eq_true] at h
      rcases of_decide_eq_true h.1 with rfl
      exact .un op1 (checkAlphaOpt_sound Φ ρ a1 a2 h.2)
    | _ => simp [checkAlphaOpt] at h
  | .if_ c1 t1 f1, e2, h => by
    cases e2 with
    | if_ c2 t2 f2 =>
      simp only [checkAlphaOpt, Bool.and_eq_true] at h
      rcases h with ⟨⟨hc, ht⟩, hf⟩
      exact .if_ (checkAlphaOpt_sound Φ ρ c1 c2 hc)
        (checkAlphaOpt_sound Φ ρ t1 t2 ht) (checkAlphaOpt_sound Φ ρ f1 f2 hf)
    | _ => simp [checkAlphaOpt] at h
  | .applyDir nm1 args1, e2, h => by
    cases e2 with
    | applyDir nm2 args2 =>
      simp only [checkAlphaOpt, Bool.and_eq_true] at h
      rcases of_decide_eq_true h.1 with rfl
      exact .applyDir nm1 (checkAlphaOptList_sound Φ ρ args1 args2 h.2)
    | _ => simp [checkAlphaOpt] at h
  | .apply fn1 args1, e2, h => by
    cases e2 with
    | apply fn2 args2 =>
      simp only [checkAlphaOpt, Bool.and_eq_true] at h
      exact .apply (checkAlphaOpt_sound Φ ρ fn1 fn2 h.1) (checkAlphaOptList_sound Φ ρ args1 args2 h.2)
    | _ => simp [checkAlphaOpt] at h
  | .tuple es1, e2, h => by
    cases e2 with
    | tuple es2 => exact .tuple (checkAlphaOptList_sound Φ ρ es1 es2 h)
    | _ => simp [checkAlphaOpt] at h
  | .makeData a1 t1 es1, e2, h => by
    cases e2 with
    | makeData a2 t2 es2 =>
      simp only [checkAlphaOpt, Bool.and_eq_true] at h
      rcases of_decide_eq_true h.1 with ⟨rfl, rfl⟩
      exact .makeData a1 t1 (checkAlphaOptList_sound Φ ρ es1 es2 h.2)
    | _ => simp [checkAlphaOpt] at h
  | .match_ s1 arms1, e2, h => by
    cases e2 with
    | match_ s2 arms2 =>
      simp only [checkAlphaOpt, Bool.and_eq_true] at h
      exact .matchAlpha (checkAlphaOpt_sound Φ ρ s1 s2 h.1) (checkAlphaOptArms_sound Φ ρ arms1 arms2 h.2)
    | _ => simp [checkAlphaOpt] at h
  | .lam _ _ _ _, _, h | .while_ _ _, _, h | .getTag _, _, h | .cellNew _, _, h
  | .cellGet _, _, h | .cellSet _ _, _, h | .spawn _, _, h | .await _, _, h | .concPrim _ _, _, h => by
    simp [checkAlphaOpt] at h
termination_by e1 => sizeOf e1

theorem checkAlphaOptList_sound (Φ : FunEnv) (ρ : List (Ident × Ident)) :
    (es1 es2 : List Expr) → checkAlphaOptList ρ es1 es2 = true → AlphaOptRelList Φ ρ es1 es2
  | [], [], _ => .nil ρ
  | e1 :: r1, e2 :: r2, h => by
    simp only [checkAlphaOptList, Bool.and_eq_true] at h
    exact .cons (checkAlphaOpt_sound Φ ρ e1 e2 h.1) (checkAlphaOptList_sound Φ ρ r1 r2 h.2)
  | [], _ :: _, h | _ :: _, [], h => by simp [checkAlphaOptList] at h
termination_by es1 => sizeOf es1

theorem checkAlphaOptArms_sound (Φ : FunEnv) (ρ : List (Ident × Ident)) :
    (arms1 arms2 : List (Pat × Expr)) → checkAlphaOptArms ρ arms1 arms2 = true → AlphaOptRelArms Φ ρ arms1 arms2
  | [], [], _ => .nil ρ
  | (p1, b1) :: r1, (p2, b2) :: r2, h => by
    simp only [checkAlphaOptArms] at h
    cases hp : checkPatAlpha p1 p2 <;> rw [hp] at h
    · cases h
    · rename_i pairs
      simp only [Bool.and_eq_true] at h
      rcases h with ⟨⟨⟨⟨hnd1, hnd2⟩, hfr⟩, hb⟩, hr⟩
      refine .cons (checkPatAlpha_sound p1 p2 hp)
        (checkListNodup_sound hnd1) (checkListNodup_sound hnd2) ?_
        (checkAlphaOpt_sound Φ (pairs ++ ρ) b1 b2 hb)
        (checkAlphaOptArms_sound Φ ρ r1 r2 hr)
      intro z hz hzp
      have hall := List.all_eq_true.mp hfr z hz
      have hct1 : (pairs.map Prod.fst).contains z = false := by
        cases hc : (pairs.map Prod.fst).contains z
        · rfl
        · exfalso; exact hzp (List.contains_iff_mem.mp hc)
      rw [hct1, Bool.false_or, Bool.not_eq_true'] at hall
      intro hm2
      rw [List.contains_iff_mem.mpr hm2] at hall; cases hall
  | [], _ :: _, h | _ :: _, [], h => by simp [checkAlphaOptArms] at h
termination_by arms1 => sizeOf arms1
end

def coFreshIdent (id : Nat) (orig : Ident) : Ident :=
  "$co$" ++ toString id ++ "$" ++ orig

def coCloneOptExpr : Nat → List (Ident × Ident) → Expr → Nat × Expr
  | id, _, .lit l => (id, .lit l)
  | id, ρ, .var x => (id, .var (lookupRename ρ x))
  | id, _, .loc l => (id, .loc l)
  | id, _, .taskRef tid => (id, .taskRef tid)
  | id, _, .syncRef k n => (id, .syncRef k n)
  | id, _, .trap t => (id, .trap t)
  | id, ρ, .block [e] => coCloneOptExpr id ρ e
  | id, ρ, .let_ x e1 e2 =>
    let (id1, e1') := coCloneOptExpr id ρ e1
    let fv := coFreshIdent id1 x
    let (id2, e2') := coCloneOptExpr (id1 + 1) ((x, fv) :: ρ) e2
    (id2, .let_ fv e1' e2')
  | id, ρ, .bin op a b =>
    let (id1, a') := coCloneOptExpr id ρ a
    let (id2, b') := coCloneOptExpr id1 ρ b
    (id2, .bin op a' b')
  | id, ρ, .un op a =>
    let (id1, a') := coCloneOptExpr id ρ a
    (id1, .un op a')
  | id, ρ, .if_ c t e =>
    let (id1, c') := coCloneOptExpr id ρ c
    let (id2, t') := coCloneOptExpr id1 ρ t
    let (id3, e') := coCloneOptExpr id2 ρ e
    (id3, .if_ c' t' e')
  | id, _, e => (id, e)

private theorem steps_apply_vs_applyDir_optBody {Δ : AdtEnv} {Φ2 : FunEnv}
    (hΦ2cl : ClosedFunEnv Φ2)
    {flatName : Ident} {m : Mode} {fvs ps fvsFresh psFresh : List (Ident × Ty)}
    {ret : Ty} {body optBody : Expr} {fvVals : List Expr}
    (hflat : Φ2 flatName = some {
      name := flatName, params := fvsFresh ++ psFresh, retTy := ret, body := optBody })
    (hfvVal : ∀ v ∈ fvVals, IsValue v) (hfvCl : ∀ v ∈ fvVals, freeVars v = [])
    (hfvLen : fvVals.length = fvs.length)
    (hfrFvLen : fvsFresh.length = fvs.length) (hfrPsLen : psFresh.length = ps.length)
    (hfvsNodup : (fvs.map Prod.fst).Nodup) (hpsNodup : (ps.map Prod.fst).Nodup)
    (hdisjPsFvs : ∀ x ∈ ps.map Prod.fst, x ∉ fvs.map Prod.fst)
    (hfrNodup : ((fvsFresh ++ psFresh).map Prod.fst).Nodup)
    (hbodyFv : ∀ z ∈ freeVars body, z ∈ (ps ++ fvs).map Prod.fst)
    (hrel : AlphaOptRel Φ2 ((ps.map Prod.fst).zip (psFresh.map Prod.fst) ++
                            (fvs.map Prod.fst).zip (fvsFresh.map Prod.fst)) body optBody) :
    ∀ (doneVals remArgs : List Expr) {σ σ' : Store} {out : Expr},
      ClosedStore σ → IsTerminal out →
      (∀ v ∈ doneVals, IsValue v ∧ freeVars v = []) →
      (∀ e ∈ remArgs, freeVars e = []) →
      doneVals.length + remArgs.length = ps.length →
      (Steps Δ Φ2 (.apply (substMany (zipParams fvs fvVals) (.lam m ps ret body)) (doneVals ++ remArgs)) σ out σ' ↔
       Steps Δ Φ2 (.applyDir flatName (fvVals ++ doneVals ++ remArgs)) σ out σ')
  | doneVals, [], σ, σ', out, hσ, hout, hdone, _, htot0 => by
    have htot : doneVals.length = ps.length := by simpa using htot0
    simp only [List.append_nil]
    have hd : ∀ x ∈ ps.map Prod.fst, x ∉ (zipParams fvs fvVals).map Prod.fst := by
      rw [zipParams_fst_eq hfvLen]; exact hdisjPsFvs
    rw [substMany_lam_disjoint m ps ret body (zipParams fvs fvVals) hd]
    have hbeta1 : ClosedObsEquiv Δ Φ2 Φ2
        (.apply (.lam m ps ret (substMany (zipParams fvs fvVals) body)) doneVals)
        (substMany (zipParams ps doneVals) (substMany (zipParams fvs fvVals) body)) :=
      ClosedObsEquiv.of_obsEquiv (obsEquiv_of_det_step (fun _ =>
        .applyBeta (fun v hv => (hdone v hv).1) htot))
    have hfull_vs : ∀ v ∈ fvVals ++ doneVals, IsValue v := by
      intro v hv; rcases List.mem_append.mp hv with h1 | h2
      · exact hfvVal v h1
      · exact (hdone v h2).1
    have hfull_len : (fvVals ++ doneVals).length = (fvsFresh ++ psFresh).length := by
      simp [hfvLen, htot, hfrFvLen, hfrPsLen]
    have hbeta2 : ClosedObsEquiv Δ Φ2 Φ2
        (.applyDir flatName (fvVals ++ doneVals))
        (substMany (zipParams (fvsFresh ++ psFresh) (fvVals ++ doneVals)) optBody) :=
      ClosedObsEquiv.of_obsEquiv (obsEquiv_of_det_step (fun _ =>
        .applyDirBeta hflat hfull_vs hfull_len))
    rw [hbeta1 σ σ' out hσ hout, hbeta2 σ σ' out hσ hout]
    have hswap : substMany (zipParams ps doneVals) (substMany (zipParams fvs fvVals) body) =
        substMany (zipParams ps doneVals ++ zipParams fvs fvVals) body := by
      rw [← substMany_append_eq]
      apply substMany_congr_lookup
      · intro q hq; rcases List.mem_append.mp hq with h1 | h2
        · unfold zipParams at h1; exact hfvCl q.2 (mem_snd_of_mem_zip h1)
        · unfold zipParams at h2; exact (hdone q.2 (mem_snd_of_mem_zip h2)).2
      · intro q hq; rcases List.mem_append.mp hq with h1 | h2
        · unfold zipParams at h1; exact (hdone q.2 (mem_snd_of_mem_zip h1)).2
        · unfold zipParams at h2; exact hfvCl q.2 (mem_snd_of_mem_zip h2)
      · intro z _
        rw [lookupSubstEnv_append, lookupSubstEnv_append]
        by_cases hzp : z ∈ ps.map Prod.fst
        · have hzfv : z ∉ (zipParams fvs fvVals).map Prod.fst := hd z hzp
          have hnone_fv : lookupSubstEnv z (zipParams fvs fvVals) = none := by
            cases h : lookupSubstEnv z (zipParams fvs fvVals)
            · rfl
            · have his := lookupSubstEnv_isSome_iff_contains z (zipParams fvs fvVals)
              rw [h] at his
              exact False.elim (hzfv (List.contains_iff_mem.mp his.symm))
          have hsome_ps : ∃ w, lookupSubstEnv z (zipParams ps doneVals) = some w := by
            rcases List.mem_iff_getElem.mp hzp with ⟨i, hi, rfl⟩
            unfold zipParams
            exact ⟨_, lookupSubstEnv_nodup_zip (vs := doneVals) hpsNodup (by simp [htot]) i hi⟩
          rcases hsome_ps with ⟨w, hw⟩
          rw [hnone_fv, hw]
        · have hznot_ps : z ∉ (zipParams ps doneVals).map Prod.fst := by
            rw [zipParams_fst_eq htot]; exact hzp
          have hnone_ps : lookupSubstEnv z (zipParams ps doneVals) = none := by
            cases h : lookupSubstEnv z (zipParams ps doneVals)
            · rfl
            · have his := lookupSubstEnv_isSome_iff_contains z (zipParams ps doneVals)
              rw [h] at his
              exact False.elim (hznot_ps (List.contains_iff_mem.mp his.symm))
          rw [hnone_ps]
          cases lookupSubstEnv z (zipParams fvs fvVals) <;> rfl
    rw [hswap]
    apply alphaOptRel_subst_closedObsEquiv Δ hΦ2cl hrel ?_ σ σ' out hσ hout
    refine ⟨?_, ?_, ?_⟩
    · intro q hq; rcases List.mem_append.mp hq with h1 | h2
      · unfold zipParams at h1; exact hdone q.2 (mem_snd_of_mem_zip h1)
      · unfold zipParams at h2; exact ⟨hfvVal q.2 (mem_snd_of_mem_zip h2), hfvCl q.2 (mem_snd_of_mem_zip h2)⟩
    · intro q hq
      unfold zipParams at hq
      rcases List.mem_append.mp (mem_snd_of_mem_zip hq) with h1 | h2
      · exact ⟨hfvVal q.2 h1, hfvCl q.2 h1⟩
      · exact hdone q.2 h2
    · intro z hz
      have hz_all := hbodyFv z hz
      simp only [List.map_append, List.mem_append] at hz_all
      by_cases hzp : z ∈ ps.map Prod.fst
      · rcases List.mem_iff_getElem.mp hzp with ⟨i, hi, rfl⟩
        have hi_p : i < ps.length := by simp at hi; exact hi
        have hi_d : i < doneVals.length := by omega
        have hi_pf : i < psFresh.length := by omega
        have hlu1 := lookupSubstEnv_nodup_zip (vs := doneVals) hpsNodup (by simp [htot]) i hi
        have hren := lookupRename_nodup_zip hpsNodup (ys := psFresh.map Prod.fst)
          (by simp [hfrPsLen]) ((fvs.map Prod.fst).zip (fvsFresh.map Prod.fst)) i hi
        have idx_r : fvsFresh.length + i < ((fvsFresh ++ psFresh).map Prod.fst).length := by
          simp; omega
        have idx_rv : fvsFresh.length + i < (fvVals ++ doneVals).length := by
          simp; omega
        have hget_fr : ((fvsFresh ++ psFresh).map Prod.fst)[fvsFresh.length + i]'idx_r =
            (psFresh.map Prod.fst)[i]'(by simp [hi_pf]) := by
          simp only [List.map_append]
          rw [List.getElem_append_right (by simp)]
          simp
        have hget_val : (fvVals ++ doneVals)[fvsFresh.length + i]'idx_rv =
            doneVals[i]'hi_d := by
          have hfvEq : fvsFresh.length = fvVals.length := by omega
          rw [List.getElem_append_right (by omega)]
          congr 1; omega
        have hlu2 := lookupSubstEnv_nodup_zip (vs := fvVals ++ doneVals) hfrNodup
          (by simp; omega) (fvsFresh.length + i) idx_r
        refine ⟨doneVals[i]'hi_d, ?_, ?_⟩
        · rw [lookupSubstEnv_append]; unfold zipParams; rw [hlu1]
        · rw [hren, ← hget_fr]; unfold zipParams; rw [hlu2, hget_val]
      · rcases hz_all with hps_false | hzfv
        · exact False.elim (hzp hps_false)
        · rcases List.mem_iff_getElem.mp hzfv with ⟨j, hj, rfl⟩
          have hj_f : j < fvs.length := by simp at hj; exact hj
          have hj_fr : j < fvsFresh.length := by omega
          have hj_v : j < fvVals.length := by omega
          have hznot_ps : (fvs.map Prod.fst)[j] ∉ (zipParams ps doneVals).map Prod.fst := by
            rw [zipParams_fst_eq htot]; exact hzp
          have hznot_pair : (fvs.map Prod.fst)[j] ∉ ((ps.map Prod.fst).zip (psFresh.map Prod.fst)).map Prod.fst := by
            rw [zip_fst_eq_of_eq_len (by simp [hfrPsLen])]; exact hzp
          have hlu1 := lookupSubstEnv_nodup_zip (vs := fvVals) hfvsNodup (by simp [hfvLen]) j hj
          have hren := lookupRename_nodup_zip hfvsNodup (ys := fvsFresh.map Prod.fst)
            (by simp [hfrFvLen]) [] j hj
          have idx_l : j < ((fvsFresh ++ psFresh).map Prod.fst).length := by simp; omega
          have idx_lv : j < (fvVals ++ doneVals).length := by simp; omega
          have hget_fr : ((fvsFresh ++ psFresh).map Prod.fst)[j]'idx_l =
              (fvsFresh.map Prod.fst)[j]'(by simp [hj_fr]) := by
            simp only [List.map_append]
            exact List.getElem_append_left (by simp [hj_fr])
          have hget_val : (fvVals ++ doneVals)[j]'idx_lv = fvVals[j]'hj_v :=
            List.getElem_append_left hj_v
          have hlu2 := lookupSubstEnv_nodup_zip (vs := fvVals ++ doneVals) hfrNodup
            (by simp; omega) j idx_l
          refine ⟨fvVals[j]'hj_v, ?_, ?_⟩
          · rw [lookupSubstEnv_not_mem_fst hznot_ps]; unfold zipParams; exact hlu1
          · rw [lookupRename_not_mem_fst hznot_pair]; simp only [List.append_nil] at hren; rw [hren, ← hget_fr]
            unfold zipParams; rw [hlu2, hget_val]
  | doneVals, a :: rArgs, σ, σ', out, hσ, hout, hdone, hremCl, htot => by
    have hd : ∀ x ∈ ps.map Prod.fst, x ∉ (zipParams fvs fvVals).map Prod.fst := by
      rw [zipParams_fst_eq hfvLen]; exact hdisjPsFvs
    have hclsVal : IsValue (substMany (zipParams fvs fvVals) (.lam m ps ret body)) := by
      rw [substMany_lam_disjoint m ps ret body (zipParams fvs fvVals) hd]
      exact .lam _ _ _ _
    have hK1 := isActiveCtx_applyArg Δ hclsVal (vs := doneVals) (fun v hv => (hdone v hv).1) rArgs
    have hdoneFvVal : ∀ v ∈ fvVals ++ doneVals, IsValue v := by
      intro v hv; rcases List.mem_append.mp hv with h1 | h2
      · exact hfvVal v h1
      · exact (hdone v h2).1
    have hK2 := isActiveCtx_applyDirArg Δ flatName (vs := fvVals ++ doneVals) hdoneFvVal rArgs
    rw [activeCtx_steps_terminal_iff hK1 hout, activeCtx_steps_terminal_iff hK2 hout]
    have ha_cl : freeVars a = [] := hremCl a (List.mem_cons_self ..)
    have hr_cl : ∀ e ∈ rArgs, freeVars e = [] := fun e he => hremCl e (List.mem_cons_of_mem _ he)
    constructor
    · rintro (⟨t, rfl, htr⟩ | ⟨va, sm, hva, hsv, hkv⟩)
      · exact Or.inl ⟨t, rfl, htr⟩
      · rcases steps_preserves_closed hΦ2cl hσ ha_cl hsv with ⟨hva_cl, hsm⟩
        have hkv1 : Steps Δ Φ2 (.apply (substMany (zipParams fvs fvVals) (.lam m ps ret body)) ((doneVals ++ [va]) ++ rArgs)) sm out σ' := by
          simpa [List.append_assoc] using hkv
        have ih := steps_apply_vs_applyDir_optBody (Δ := Δ) (m := m) (σ' := σ') hΦ2cl hflat hfvVal hfvCl hfvLen hfrFvLen hfrPsLen
          hfvsNodup hpsNodup hdisjPsFvs hfrNodup hbodyFv hrel (doneVals ++ [va]) rArgs hsm hout
          (fun w hw => by rcases List.mem_append.mp hw with h1 | h2; exact hdone w h1; simp at h2; subst h2; exact ⟨hva, hva_cl⟩)
          hr_cl (by simp [List.length_append] at htot ⊢; omega)
        exact Or.inr ⟨va, sm, hva, hsv, by simpa [List.append_assoc] using ih.mp hkv1⟩
    · rintro (⟨t, rfl, htr⟩ | ⟨va, sm, hva, hsv, hkv⟩)
      · exact Or.inl ⟨t, rfl, htr⟩
      · rcases steps_preserves_closed hΦ2cl hσ ha_cl hsv with ⟨hva_cl, hsm⟩
        have hkv2 : Steps Δ Φ2 (.applyDir flatName (fvVals ++ (doneVals ++ [va]) ++ rArgs)) sm out σ' := by
          simpa [List.append_assoc] using hkv
        have ih := steps_apply_vs_applyDir_optBody (Δ := Δ) (m := m) (σ' := σ') hΦ2cl hflat hfvVal hfvCl hfvLen hfrFvLen hfrPsLen
          hfvsNodup hpsNodup hdisjPsFvs hfrNodup hbodyFv hrel (doneVals ++ [va]) rArgs hsm hout
          (fun w hw => by rcases List.mem_append.mp hw with h1 | h2; exact hdone w h1; simp at h2; subst h2; exact ⟨hva, hva_cl⟩)
          hr_cl (by simp [List.length_append] at htot ⊢; omega)
        exact Or.inr ⟨va, sm, hva, hsv, by simpa [List.append_assoc] using ih.mpr hkv2⟩

/-- **Main Captures-First `$flat$` Devirtualization Soundness With Cloned & Optimized Body
    (`flat_closure_devirt_optBody_obsEquiv`, `src/core.gsa:6426-6441`)**:
    Covers full `coCloneTerm` (renaming BOTH parameters AND internal `let`/`match` binders)
    followed by `coOptTerm` (`AlphaOptRel`: singleton `.block [e]` unwrapping, dead `coExprIsPure`
    `let` elimination, direct `TmVar` inlining) across `Φ1 ↦ Φ2`! -/
theorem flat_closure_devirt_optBody_obsEquiv {Δ : AdtEnv} {Φ1 Φ2 : FunEnv}
    {dom : Ident → Bool}
    (hagree : FunEnvAgreesOn dom Φ1 Φ2) (hΦ1dom : ClosedDomEnv dom Φ1)
    (hΦ2cl : ClosedFunEnv Φ2)
    {flatName : Ident} {m : Mode} {fvs ps fvsFresh psFresh : List (Ident × Ty)}
    {ret : Ty} {body optBody : Expr} {fvVals args : List Expr}
    {σ σ' : Store} {out : Expr}
    (hσCl : ClosedStore σ) (hσDom : StoreInDom dom σ) (hout : IsTerminal out)
    (hflat : Φ2 flatName = some {
      name := flatName, params := fvsFresh ++ psFresh, retTy := ret, body := optBody })
    (hfvVal : ∀ v ∈ fvVals, IsValue v) (hfvCl : ∀ v ∈ fvVals, freeVars v = [])
    (hfvDom : ∀ v ∈ fvVals, exprInDom dom v = true)
    (hargsCl : ∀ e ∈ args, freeVars e = []) (hargsDom : ∀ e ∈ args, exprInDom dom e = true)
    (hfvLen : fvVals.length = fvs.length) (hargsLen : args.length = ps.length)
    (hfrFvLen : fvsFresh.length = fvs.length) (hfrPsLen : psFresh.length = ps.length)
    (hfvsNodup : (fvs.map Prod.fst).Nodup) (hpsNodup : (ps.map Prod.fst).Nodup)
    (hdisjPsFvs : ∀ x ∈ ps.map Prod.fst, x ∉ fvs.map Prod.fst)
    (hfrNodup : ((fvsFresh ++ psFresh).map Prod.fst).Nodup)
    (hbodyDom : exprInDom dom body = true)
    (hbodyFv : ∀ z ∈ freeVars body, z ∈ (ps ++ fvs).map Prod.fst)
    (hrel : AlphaOptRel Φ2 ((ps.map Prod.fst).zip (psFresh.map Prod.fst) ++
                            (fvs.map Prod.fst).zip (fvsFresh.map Prod.fst)) body optBody) :
    Steps Δ Φ1 (.apply (substMany (zipParams fvs fvVals) (.lam m ps ret body)) args) σ out σ' ↔
      Steps Δ Φ2 (.applyDir flatName (fvVals ++ args)) σ out σ' := by
  have hd : ∀ x ∈ ps.map Prod.fst, x ∉ (zipParams fvs fvVals).map Prod.fst := by
    rw [zipParams_fst_eq hfvLen]; exact hdisjPsFvs
  have hclsDom : exprInDom dom (substMany (zipParams fvs fvVals) (.lam m ps ret body)) = true := by
    rw [substMany_lam_disjoint m ps ret body (zipParams fvs fvVals) hd]
    simp only [exprInDom]
    exact substMany_exprInDom
      (fun p hp => by unfold zipParams at hp; exact hfvDom p.2 (mem_snd_of_mem_zip hp)) hbodyDom
  have happDom : exprInDom dom (.apply (substMany (zipParams fvs fvVals) (.lam m ps ret body)) args) = true := by
    simp only [exprInDom, Bool.and_eq_true]
    exact ⟨hclsDom, exprListInDom_iff.mpr hargsDom⟩
  rw [steps_funEnv_agree_iff hagree hΦ1dom hσDom happDom]
  simpa using steps_apply_vs_applyDir_optBody hΦ2cl hflat hfvVal hfvCl hfvLen hfrFvLen hfrPsLen
    hfvsNodup hpsNodup hdisjPsFvs hfrNodup hbodyFv hrel [] args hσCl hout
    (fun _ h => by cases h) hargsCl (by simpa using hargsLen)

/-- Verbatim parsed pre-optimization `bigCls` body from `before.gs` (`makeLargeFlatRes`). -/
def beforeMakeLargeFlatClsBody : Expr :=
  .block [
    .let_ "fv_q" (.lit (.int 5))
      (.let_ "a1" (.bin .add (.var "u") (.lit (.int 1)))
        (.let_ "a2" (.bin .add (.var "a1") (.lit (.int 2)))
          (.let_ "a3" (.bin .add (.var "a2") (.lit (.int 3)))
            (.let_ "a4" (.bin .add (.var "a3") (.lit (.int 4)))
              (.let_ "a5" (.bin .add (.var "a4") (.lit (.int 5)))
                (.let_ "a6" (.bin .add (.var "a5") (.lit (.int 6)))
                  (.let_ "a7" (.bin .add (.var "a6") (.lit (.int 7)))
                    (.let_ "a8" (.bin .add (.var "a7") (.lit (.int 8)))
                      (.let_ "a9" (.bin .add (.var "a8") (.lit (.int 9)))
                        (.let_ "a10" (.bin .add (.var "a9") (.lit (.int 10)))
                          (.let_ "a11" (.bin .add (.var "a10") (.lit (.int 11)))
                            (.let_ "a12" (.bin .add (.var "a11") (.lit (.int 12)))
                              (.if_ (.bin .gtInt (.var "a12") (.lit (.int 0)))
                                (.bin .mul (.var "q") (.var "fv_q"))
                                (.lit (.int 0)))))))))))))))]

/-- Verbatim parsed `makeLargeFlatRes` `FunDef` from `before.gs`. -/
def beforeMakeLargeFlatResFd : FunDef := {
  name := "makeLargeFlatRes",
  params := [("q", .int)],
  retTy := .int,
  body := .block [
    .let_ "bigCls" (.lam .shared [("u", .int)] .int beforeMakeLargeFlatClsBody)
      (.apply (.var "bigCls") [.lit (.int 1)])]
}

/-- Verbatim parsed `makeLargeFlatRes.inner.closure.bigCls1$icls$29$flat$44` `FunDef` from `after.gs`. -/
def afterBigClsFlat44Fd : FunDef := {
  name := "makeLargeFlatRes.inner.closure.bigCls1$icls$29$flat$44",
  params := [("$co$45$q", .int), ("$co$46$u", .int)],
  retTy := .int,
  body :=
    .let_ "$co$47$fv_q" (.lit (.int 5))
      (.let_ "$co$48$a1" (.bin .add (.var "$co$46$u") (.lit (.int 1)))
        (.let_ "$co$49$a2" (.bin .add (.var "$co$48$a1") (.lit (.int 2)))
          (.let_ "$co$50$a3" (.bin .add (.var "$co$49$a2") (.lit (.int 3)))
            (.let_ "$co$51$a4" (.bin .add (.var "$co$50$a3") (.lit (.int 4)))
              (.let_ "$co$52$a5" (.bin .add (.var "$co$51$a4") (.lit (.int 5)))
                (.let_ "$co$53$a6" (.bin .add (.var "$co$52$a5") (.lit (.int 6)))
                  (.let_ "$co$54$a7" (.bin .add (.var "$co$53$a6") (.lit (.int 7)))
                    (.let_ "$co$55$a8" (.bin .add (.var "$co$54$a7") (.lit (.int 8)))
                      (.let_ "$co$56$a9" (.bin .add (.var "$co$55$a8") (.lit (.int 9)))
                        (.let_ "$co$57$a10" (.bin .add (.var "$co$56$a9") (.lit (.int 10)))
                          (.let_ "$co$58$a11" (.bin .add (.var "$co$57$a10") (.lit (.int 11)))
                            (.let_ "$co$59$a12" (.bin .add (.var "$co$58$a11") (.lit (.int 12)))
                              (.if_ (.bin .gtInt (.var "$co$59$a12") (.lit (.int 0)))
                                (.bin .mul (.var "$co$45$q") (.var "$co$47$fv_q"))
                                (.lit (.int 0)))))))))))))))
}

/-- **Exact AST Reproduction of `afterBigClsFlat44Fd.body` (`exact_artifact_bigCls_flat44_clone_eq`)**:
    Running `coCloneOptExpr` starting at fresh ID `47` on `beforeMakeLargeFlatClsBody` unwraps
    `.block [e]` and produces the exact 13-`let` `afterBigClsFlat44Fd.body` (`$co$47$fv_q`..`$co$59$a12`)! -/
theorem exact_artifact_bigCls_flat44_clone_eq :
    coCloneOptExpr 47 [("u", "$co$46$u"), ("q", "$co$45$q")] beforeMakeLargeFlatClsBody =
      (60, afterBigClsFlat44Fd.body) := rfl

/-- **Exact Real-Artifact Theorem 1 (`exact_artifact_bigCls_flat44_obsEquiv`)**:
    Proves full `Steps` equivalence between the verbatim parsed `before.gs` `bigCls` closure
    and the verbatim parsed `after.gs` `makeLargeFlatRes.inner.closure.bigCls1$icls$29$flat$44`
    for arbitrary closed `qVal` and arbitrary (potentially heap-mutating/trapping) argument `uExpr`! -/
theorem exact_artifact_bigCls_flat44_obsEquiv {Δ : AdtEnv} {Φ1 Φ2 : FunEnv}
    {dom : Ident → Bool}
    (hagree : FunEnvAgreesOn dom Φ1 Φ2) (hΦ1dom : ClosedDomEnv dom Φ1)
    (hΦ2cl : ClosedFunEnv Φ2)
    {qVal uExpr : Expr} {σ σ' : Store} {out : Expr}
    (hσCl : ClosedStore σ) (hσDom : StoreInDom dom σ) (hout : IsTerminal out)
    (hflat : Φ2 afterBigClsFlat44Fd.name = some afterBigClsFlat44Fd)
    (hqVal : IsValue qVal) (hqCl : freeVars qVal = []) (hqDom : exprInDom dom qVal = true)
    (huCl : freeVars uExpr = []) (huDom : exprInDom dom uExpr = true) :
    Steps Δ Φ1 (.apply (substMany [("q", qVal)] (.lam .shared [("u", .int)] .int beforeMakeLargeFlatClsBody)) [uExpr]) σ out σ' ↔
      Steps Δ Φ2 (.applyDir afterBigClsFlat44Fd.name [qVal, uExpr]) σ out σ' := by
  exact flat_closure_devirt_optBody_obsEquiv
    (fvs := [("q", .int)]) (ps := [("u", .int)])
    (fvsFresh := [("$co$45$q", .int)]) (psFresh := [("$co$46$u", .int)])
    (fvVals := [qVal]) (args := [uExpr])
    hagree hΦ1dom hΦ2cl hσCl hσDom hout hflat
    (fun v hv => by simp at hv; subst hv; exact hqVal)
    (fun v hv => by simp at hv; subst hv; exact hqCl)
    (fun v hv => by simp at hv; subst hv; exact hqDom)
    (fun e he => by simp at he; subst he; exact huCl)
    (fun e he => by simp at he; subst he; exact huDom)
    rfl rfl rfl rfl
    (by decide) (by decide) (by decide) (by decide)
    rfl
    (by decide)
    (checkAlphaOpt_sound Φ2 [("u", "$co$46$u"), ("q", "$co$45$q")]
      beforeMakeLargeFlatClsBody afterBigClsFlat44Fd.body (by decide))

/-! ### 10.4 `CoEnv` Match State (`ceAliases` + `ceKnownVals`, Shadow/Dependent Eviction & Alpha-Cloned Arm Reduction) -/

def coSimpleTerm : Expr → Bool
  | .lit _ | .var _ | .loc _ | .taskRef _ | .syncRef _ _ => true
  | _ => false

def coAllSimple : List Expr → Bool
  | [] => true
  | e :: r => coSimpleTerm e && coAllSimple r

theorem coSimpleTerm_substMany_isValue {σEnv : List (Ident × Expr)}
    (hvals : ∀ p ∈ σEnv, IsValue p.2 ∧ freeVars p.2 = []) {e : Expr}
    (hsimp : coSimpleTerm e = true)
    (hdom : ∀ z ∈ freeVars e, (lookupSubstEnv z σEnv).isSome = true) :
    IsValue (substMany σEnv e) := by
  cases e with
  | lit l => rw [(substMany_atom_eq σEnv).1 l]; exact .lit l
  | loc l => rw [(substMany_atom_eq σEnv).2.1 l]; exact .loc l
  | taskRef t => rw [(substMany_atom_eq σEnv).2.2.1 t]; exact .taskRef t
  | syncRef k n => rw [(substMany_atom_eq σEnv).2.2.2.1 k n]; exact .syncRef k n
  | var z =>
    rw [substMany_var_lookup (fun p hp => (hvals p hp).2) z]
    have hd := hdom z (by simp [freeVars])
    cases hlu : lookupSubstEnv z σEnv
    · rw [hlu] at hd; simp at hd
    · exact (lookupSubstEnv_isSome_val_cl hvals hlu).1
  | _ => simp [coSimpleTerm] at hsimp

theorem coAllSimple_substMany_isValues {σEnv : List (Ident × Expr)}
    (hvals : ∀ p ∈ σEnv, IsValue p.2 ∧ freeVars p.2 = []) :
    (es : List Expr) → coAllSimple es = true →
    (∀ z ∈ freeVarsList es, (lookupSubstEnv z σEnv).isSome = true) →
    ∀ w ∈ substManyList σEnv es, IsValue w
  | [], _, _, _, hw => by simp [substManyList] at hw
  | e :: r, hsimp, hdom, w, hw => by
    simp only [coAllSimple, Bool.and_eq_true] at hsimp
    simp only [substManyList, List.map] at hw
    rcases List.mem_cons.mp hw with rfl | hwr
    · exact coSimpleTerm_substMany_isValue hvals hsimp.1 (fun z hz => hdom z (by simp [freeVarsList, hz]))
    · exact coAllSimple_substMany_isValues hvals r hsimp.2
        (fun z hz => hdom z (by simp [freeVarsList, hz])) w hwr

inductive CoKnownValM where
  | lit (l : Lit)
  | tuple (es : List Expr)
  | data (adt : Ident) (tag : Nat) (fs : List Expr)

def CoKnownValM.toExpr : CoKnownValM → Expr
  | .lit l => .lit l
  | .tuple es => .tuple es
  | .data adt tag fs => .makeData adt tag fs

def CoKnownValM.allSimple : CoKnownValM → Bool
  | .lit _ => true
  | .tuple es => coAllSimple es
  | .data _ _ fs => coAllSimple fs

theorem CoKnownValM.substMany_isValue {σEnv : List (Ident × Expr)}
    (hvals : ∀ p ∈ σEnv, IsValue p.2 ∧ freeVars p.2 = []) (kv : CoKnownValM)
    (hsimp : kv.allSimple = true)
    (hdom : ∀ z ∈ freeVars kv.toExpr, (lookupSubstEnv z σEnv).isSome = true) :
    IsValue (substMany σEnv kv.toExpr) := by
  cases kv with
  | lit l => simp only [CoKnownValM.toExpr]; rw [(substMany_atom_eq σEnv).1 l]; exact .lit l
  | tuple es =>
    simp only [CoKnownValM.toExpr, substMany_tuple_eq]
    exact .tuple (coAllSimple_substMany_isValues hvals es hsimp hdom)
  | data adt tag fs =>
    simp only [CoKnownValM.toExpr, substMany_makeData_eq]
    exact .makeData adt tag (coAllSimple_substMany_isValues hvals fs hsimp hdom)

def coKnownValMentionsVar (kv : CoKnownValM) (v : Ident) : Bool :=
  (freeVars kv.toExpr).contains v

structure CoEnvM where
  ceAliases   : List (Ident × Ident)
  ceKnownVals : List (Ident × CoKnownValM)

def lookupEnvOptM {α : Type} : List (Ident × α) → Ident → Option α
  | [], _ => none
  | (k, val) :: r, key => if key == k then some val else lookupEnvOptM r key

def coFilterAliasesM (xs : List (Ident × Ident)) (v : Ident) : List (Ident × Ident) :=
  xs.filter (fun p => !(p.1 == v || p.2 == v))

def coFilterKnownValsM (xs : List (Ident × CoKnownValM)) (v : Ident) : List (Ident × CoKnownValM) :=
  xs.filter (fun p => !(p.1 == v || coKnownValMentionsVar p.2 v))

def coBindVarInEnvM (cenv : CoEnvM) (v : Ident) : CoEnvM :=
  { ceAliases := coFilterAliasesM cenv.ceAliases v,
    ceKnownVals := coFilterKnownValsM cenv.ceKnownVals v }

def coEvictPatVarsFromEnvM (pat : Pat) (cenv : CoEnvM) : CoEnvM :=
  (patBoundNames pat).foldl (fun acc v => coBindVarInEnvM acc v) cenv

def coResolveAliasFuel (aliases : List (Ident × Ident)) (name : Ident) : Nat → Ident
  | 0 => name
  | fuel + 1 =>
    match lookupEnvOptM aliases name with
    | some nxt => if nxt == name then name else coResolveAliasFuel aliases nxt fuel
    | none => name

def coResolveAliasM (aliases : List (Ident × Ident)) (name : Ident) : Ident :=
  coResolveAliasFuel aliases name 25

def coRecordLetBindingInEnvM (cenv : CoEnvM) (v : Ident) (rhs : Expr) : CoEnvM :=
  let base := coBindVarInEnvM cenv v
  match rhs with
  | .var src =>
    let rsrc := coResolveAliasM base.ceAliases src
    if rsrc == v then base else { base with ceAliases := (v, rsrc) :: base.ceAliases }
  | .lit l =>
    { base with ceKnownVals := (v, .lit l) :: base.ceKnownVals }
  | .tuple es =>
    if coAllSimple es && !((freeVars (.tuple es)).contains v) then
      { base with ceKnownVals := (v, .tuple es) :: base.ceKnownVals }
    else base
  | .makeData adt tag fs =>
    if coAllSimple fs && !((freeVars (.makeData adt tag fs)).contains v) then
      { base with ceKnownVals := (v, .data adt tag fs) :: base.ceKnownVals }
    else base
  | _ => base

def coResolveTermKnownValM (tm : Expr) (cenv : CoEnvM) : Option CoKnownValM :=
  match tm with
  | .lit l => some (.lit l)
  | .tuple es => if coAllSimple es then some (.tuple es) else none
  | .makeData adt tag fs => if coAllSimple fs then some (.data adt tag fs) else none
  | .var v => lookupEnvOptM cenv.ceKnownVals (coResolveAliasM cenv.ceAliases v)
  | _ => none

def coLitsEqualM : Lit → Lit → Bool
  | .int a, .int b => a == b
  | .int64 a, .int64 b => a == b
  | .bool a, .bool b => a == b
  | .char a, .char b => a == b
  | .str a, .str b => a == b
  | .unit, .unit => true
  | _, _ => false

def isFloatAnyLit : Lit → Bool
  | .floatBits _ | .float32Bits _ => true
  | _ => false

inductive CoPatMatchM where
  | yes (binds : List (Ident × Expr))
  | no
  | unknown

def coPatMatchStatusM : CoPatMatchM → Int32
  | .yes _ => 0
  | .no => 1
  | .unknown => 2

mutual
/-- Full `CoEnv`-aware 3-valued pattern matcher (`coMatchPatKnown`, `src/core.gsa:6457-6538`). -/
def coMatchPatKnownEnv (pat : Pat) (tm : Expr) (cenv : CoEnvM) : CoPatMatchM :=
  match pat with
  | .wild =>
    if coSimpleTerm tm then .yes []
    else match tm with
      | .tuple es => if coAllSimple es then .yes [] else .unknown
      | .makeData _ _ fs => if coAllSimple fs then .yes [] else .unknown
      | _ => .unknown
  | .var v =>
    if coSimpleTerm tm then .yes [(v, tm)]
    else match tm with
      | .tuple es => if coAllSimple es then .yes [(v, tm)] else .unknown
      | .makeData _ _ fs => if coAllSimple fs then .yes [(v, tm)] else .unknown
      | _ => .unknown
  | .lit pLit =>
    if isFloatAnyLit pLit then .unknown
    else match coResolveTermKnownValM tm cenv with
      | some (.lit tLit) =>
        if isFloatAnyLit tLit then .unknown
        else if coLitsEqualM pLit tLit then .yes [] else .no
      | _ => .unknown
  | .tuple subPats =>
    match coResolveTermKnownValM tm cenv with
    | some (.tuple elems) =>
      if subPats.length != elems.length then .unknown
      else coMatchPatListKnownEnv subPats elems cenv
    | _ => .unknown
  | .ctor patAdt patTag subPats =>
    match coResolveTermKnownValM tm cenv with
    | some (.data dataAdt dataTag fields) =>
      if patAdt != dataAdt then .unknown
      else if patTag != dataTag then .no
      else if subPats.length != fields.length then .unknown
      else coMatchPatListKnownEnv subPats fields cenv
    | _ => .unknown

def coMatchPatListKnownEnv : List Pat → List Expr → CoEnvM → CoPatMatchM
  | [], [], _ => .yes []
  | p :: rp, e :: re, cenv =>
    match coMatchPatKnownEnv p e cenv with
    | .no => .no
    | .unknown =>
      match coMatchPatListKnownEnv rp re cenv with
      | .no => .no
      | _ => .unknown
    | .yes b1 =>
      match coMatchPatListKnownEnv rp re cenv with
      | .no => .no
      | .yes b2 => .yes (b1 ++ b2)
      | .unknown => .unknown
  | _, _, _ => .unknown
end

/-- Semantic invariant relating `CoEnvM` (`ceAliases`, `ceKnownVals`) to closed runtime `σEnv`. -/
structure CoEnvConsistent (σEnv : List (Ident × Expr)) (cenv : CoEnvM) : Prop where
  valsCl     : ∀ p ∈ σEnv, IsValue p.2 ∧ freeVars p.2 = []
  aliasSound : ∀ p ∈ cenv.ceAliases,
    lookupSubstEnv p.1 σEnv = lookupSubstEnv p.2 σEnv
  knownSound : ∀ p ∈ cenv.ceKnownVals,
    p.2.allSimple = true ∧
    (∀ z ∈ freeVars p.2.toExpr, (lookupSubstEnv z σEnv).isSome = true) ∧
    lookupSubstEnv p.1 σEnv = some (substMany σEnv p.2.toExpr)

theorem coInitialEnvM_consistent {σEnv : List (Ident × Expr)}
    (hvals : ∀ p ∈ σEnv, IsValue p.2 ∧ freeVars p.2 = []) :
    CoEnvConsistent σEnv { ceAliases := [], ceKnownVals := [] } :=
  ⟨hvals, (fun _ h => by cases h), (fun _ h => by cases h)⟩

private theorem lookupEnvOptM_mem {α : Type} :
    {xs : List (Ident × α)} → {k : Ident} → {val : α} →
      lookupEnvOptM xs k = some val → (k, val) ∈ xs
  | [], _, _, h => by simp [lookupEnvOptM] at h
  | (k0, v0) :: r, k, val, h => by
    simp only [lookupEnvOptM] at h
    split at h
    · rename_i heq; injection h with h; subst h
      rw [eq_of_beq heq]; exact List.mem_cons_self ..
    · exact List.mem_cons_of_mem _ (lookupEnvOptM_mem h)

/-- **Shadow & Dependent-Entry Eviction Soundness (`coBindVarInEnvM_preserves_consistent`, `src/core.gsa:5856`)**:
    Binding `v` to any new closed value `wv` and filtering `ceAliases` (`k == v || tgt == v`)
    plus `ceKnownVals` (`k == v || coKnownValMentionsVar kv v`) preserves `CoEnvConsistent`! -/
theorem coBindVarInEnvM_preserves_consistent {σEnv : List (Ident × Expr)} {cenv : CoEnvM}
    (hcons : CoEnvConsistent σEnv cenv) (v : Ident) {wv : Expr}
    (hwv_val : IsValue wv) (hwv_cl : freeVars wv = []) :
    CoEnvConsistent ((v, wv) :: σEnv) (coBindVarInEnvM cenv v) where
  valsCl p hp := by
    rcases List.mem_cons.mp hp with rfl | hpr
    · exact ⟨hwv_val, hwv_cl⟩
    · exact hcons.valsCl p hpr
  aliasSound p hp := by
    rcases List.mem_filter.mp hp with ⟨hmem, hpred⟩
    rcases p with ⟨k, tgt⟩
    simp only [Bool.not_eq_true', Bool.or_eq_false_iff] at hpred
    simp only [lookupSubstEnv, hpred.1, hpred.2, Bool.false_eq_true, ↓reduceIte]
    exact hcons.aliasSound (k, tgt) hmem
  knownSound p hp := by
    rcases List.mem_filter.mp hp with ⟨hmem, hpred⟩
    rcases p with ⟨k, kv⟩
    simp only [Bool.not_eq_true', Bool.or_eq_false_iff, coKnownValMentionsVar] at hpred
    rcases hcons.knownSound (k, kv) hmem with ⟨hsimp, hdom, hlu⟩
    have hvnot : v ∉ freeVars kv.toExpr := fun hm => by
      rw [List.contains_iff_mem.mpr hm] at hpred; cases hpred.2
    have hsub_eq : substMany ((v, wv) :: σEnv) kv.toExpr = substMany σEnv kv.toExpr := by
      apply substMany_congr_lookup
      · intro q hq; rcases List.mem_cons.mp hq with rfl | hqr
        · exact hwv_cl
        · exact (hcons.valsCl q hqr).2
      · exact fun q hq => (hcons.valsCl q hq).2
      · intro z hz
        have hzv : (z == v) = false := beq_false_of_ne (fun h => by subst h; exact hvnot hz)
        simp [lookupSubstEnv, hzv]
    refine ⟨hsimp, ?_, ?_⟩
    · intro z hz
      have hzv : (z == v) = false := beq_false_of_ne (fun h => by subst h; exact hvnot hz)
      simpa [lookupSubstEnv, hzv] using hdom z hz
    · simp only [lookupSubstEnv, hpred.1, Bool.false_eq_true, ↓reduceIte, hsub_eq]
      exact hlu

/-- **Pattern Binder Eviction Soundness (`coEvictPatVarsFromEnvM_preserves_consistent`, `src/core.gsa:7521`)**:
    Evicting all bound variables of pattern `pat` preserves `CoEnvConsistent` when extending
    `σEnv` with the runtime pattern bindings! -/
theorem coEvictPatVarsFromEnvM_preserves_consistent {σEnv : List (Ident × Expr)} {cenv : CoEnvM}
    (hcons : CoEnvConsistent σEnv cenv) {pat : Pat} {binds : List (Ident × Expr)}
    (hb_vals : ∀ q ∈ binds, IsValue q.2 ∧ freeVars q.2 = [])
    (hfst : binds.map Prod.fst = patBoundNames pat) :
    CoEnvConsistent (binds.reverse ++ σEnv) (coEvictPatVarsFromEnvM pat cenv) := by
  unfold coEvictPatVarsFromEnvM
  rw [← hfst]
  have hgen : ∀ (bs : List (Ident × Expr)) (accEnv : List (Ident × Expr)) (accC : CoEnvM),
      CoEnvConsistent accEnv accC →
      (∀ q ∈ bs, IsValue q.2 ∧ freeVars q.2 = []) →
      CoEnvConsistent (bs.reverse ++ accEnv) ((bs.map Prod.fst).foldl (fun a v => coBindVarInEnvM a v) accC) := by
    intro bs
    induction bs with
    | nil => intro accEnv accC hc _; exact hc
    | cons b br ih =>
      intro accEnv accC hc hbs
      rcases b with ⟨v, wv⟩
      rcases hbs (v, wv) (List.mem_cons_self ..) with ⟨hwv_v, hwv_c⟩
      have hc' := coBindVarInEnvM_preserves_consistent hc v hwv_v hwv_c
      have res := ih ((v, wv) :: accEnv) (coBindVarInEnvM accC v) hc'
        (fun q hq => hbs q (List.mem_cons_of_mem _ hq))
      simpa [List.reverse_cons, List.append_assoc] using res
  exact hgen binds σEnv cenv hcons hb_vals

theorem coResolveAliasFuel_sound {σEnv : List (Ident × Expr)} {aliases : List (Ident × Ident)}
    (halias : ∀ p ∈ aliases, lookupSubstEnv p.1 σEnv = lookupSubstEnv p.2 σEnv) :
    ∀ (fuel : Nat) (name : Ident),
      lookupSubstEnv (coResolveAliasFuel aliases name fuel) σEnv = lookupSubstEnv name σEnv
  | 0, _ => rfl
  | fuel + 1, name => by
    simp only [coResolveAliasFuel]
    cases hlu : lookupEnvOptM aliases name
    · rfl
    · rename_i nxt
      dsimp only
      split
      · rfl
      · rw [coResolveAliasFuel_sound halias fuel nxt]
        exact (halias (name, nxt) (lookupEnvOptM_mem hlu)).symm

theorem coResolveAliasM_sound {σEnv : List (Ident × Expr)} {cenv : CoEnvM}
    (hcons : CoEnvConsistent σEnv cenv) (name : Ident) :
    lookupSubstEnv (coResolveAliasM cenv.ceAliases name) σEnv = lookupSubstEnv name σEnv :=
  coResolveAliasFuel_sound hcons.aliasSound 25 name

/-- **`let`-Binding Recording Soundness (`coRecordLetBindingInEnvM_preserves_consistent`, `src/core.gsa:7478`)**:
    Covers alias chains (`let v = src`, including self-alias guard `rsrc == v`), literals,
    and non-self-referencing simple `.tuple`/`.makeData` constructors! -/
theorem coRecordLetBindingInEnvM_preserves_consistent {σEnv : List (Ident × Expr)} {cenv : CoEnvM}
    (hcons : CoEnvConsistent σEnv cenv) (v : Ident) (rhs : Expr)
    (hrhs_dom : ∀ z ∈ freeVars rhs, (lookupSubstEnv z σEnv).isSome = true)
    {wv : Expr} (hwv_val : IsValue wv) (hwv_cl : freeVars wv = [])
    (hwv_eq : ((∃ src, rhs = .var src) ∨ (∃ l, rhs = .lit l) ∨
               (∃ es, rhs = .tuple es ∧ coAllSimple es = true) ∨
               (∃ adt tag fs, rhs = .makeData adt tag fs ∧ coAllSimple fs = true)) →
              wv = substMany σEnv rhs) :
    CoEnvConsistent ((v, wv) :: σEnv) (coRecordLetBindingInEnvM cenv v rhs) := by
  have hbase := coBindVarInEnvM_preserves_consistent hcons v hwv_val hwv_cl
  unfold coRecordLetBindingInEnvM
  cases rhs with
  | var src =>
    dsimp only
    split
    · exact hbase
    · rename_i hrsrc_ne
      have hwv := hwv_eq (Or.inl ⟨src, rfl⟩)
      rw [substMany_var_lookup (fun p hp => (hcons.valsCl p hp).2) src] at hwv
      have hd := hrhs_dom src (by simp [freeVars])
      cases hlu_src : lookupSubstEnv src σEnv
      · rw [hlu_src] at hd; simp at hd
      · rename_i w_src
        rw [hlu_src] at hwv; subst hwv
        refine ⟨hbase.valsCl, ?_, hbase.knownSound⟩
        intro p hp; rcases List.mem_cons.mp hp with rfl | hpr
        · simp only [Bool.not_eq_true] at hrsrc_ne
          let rsrc := coResolveAliasM (coBindVarInEnvM cenv v).ceAliases src
          have hr_v : (rsrc == v) = false := hrsrc_ne
          have hres := coResolveAliasM_sound hbase src
          by_cases hsrc_v : (src == v) = true
          · have heq_sv := eq_of_beq hsrc_v; subst heq_sv
            have hnone : lookupEnvOptM (coBindVarInEnvM cenv src).ceAliases src = none := by
              cases h : lookupEnvOptM (coBindVarInEnvM cenv src).ceAliases src
              · rfl
              · have hm := lookupEnvOptM_mem h
                rcases List.mem_filter.mp hm with ⟨_, hpr⟩
                simp at hpr
            have hrsrc_eq : rsrc = src := by simp [rsrc, coResolveAliasM, coResolveAliasFuel, hnone]
            rw [hrsrc_eq] at hr_v; simp at hr_v
          · simp only [Bool.not_eq_true] at hsrc_v
            have hlu1 : lookupSubstEnv v ((v, wv) :: σEnv) = some wv := by simp [lookupSubstEnv]
            have hlu2 : lookupSubstEnv rsrc ((v, wv) :: σEnv) = some wv := by
              rw [hres]
              simp [lookupSubstEnv, hsrc_v, hlu_src]
            rw [hlu1, hlu2]
        · exact hbase.aliasSound p hpr
  | lit l =>
    dsimp only
    have hwv := hwv_eq (Or.inr (Or.inl ⟨l, rfl⟩))
    rw [(substMany_atom_eq σEnv).1 l] at hwv; subst hwv
    refine ⟨hbase.valsCl, hbase.aliasSound, ?_⟩
    intro p hp; rcases List.mem_cons.mp hp with rfl | hpr
    · refine ⟨rfl, fun _ h => by simp [CoKnownValM.toExpr, freeVars] at h, ?_⟩
      simp [lookupSubstEnv, CoKnownValM.toExpr, (substMany_atom_eq _).1 l]
    · exact hbase.knownSound p hpr
  | tuple es =>
    dsimp only
    split
    · rename_i hcond
      simp only [Bool.and_eq_true, Bool.not_eq_true'] at hcond
      have hwv := hwv_eq (Or.inr (Or.inr (Or.inl ⟨es, rfl, hcond.1⟩)))
      subst hwv
      have hvnot : v ∉ freeVars (.tuple es) := fun hm => by
        rw [List.contains_iff_mem.mpr hm] at hcond; cases hcond.2
      have hsub_eq : substMany ((v, substMany σEnv (.tuple es)) :: σEnv) (.tuple es) =
          substMany σEnv (.tuple es) := by
        apply substMany_congr_lookup
        · exact fun q hq => (hbase.valsCl q hq).2
        · exact fun q hq => (hcons.valsCl q hq).2
        · intro z hz
          have hzv : (z == v) = false := beq_false_of_ne (fun h => by subst h; exact hvnot hz)
          simp [lookupSubstEnv, hzv]
      refine ⟨hbase.valsCl, hbase.aliasSound, ?_⟩
      intro p hp; rcases List.mem_cons.mp hp with rfl | hpr
      · refine ⟨hcond.1, ?_, ?_⟩
        · intro z hz
          have hzv : (z == v) = false := beq_false_of_ne (fun h => by subst h; exact hvnot hz)
          simpa [lookupSubstEnv, hzv] using hrhs_dom z hz
        · simp [lookupSubstEnv, CoKnownValM.toExpr, hsub_eq]
      · exact hbase.knownSound p hpr
    · exact hbase
  | makeData adt tag fs =>
    dsimp only
    split
    · rename_i hcond
      simp only [Bool.and_eq_true, Bool.not_eq_true'] at hcond
      have hwv := hwv_eq (Or.inr (Or.inr (Or.inr ⟨adt, tag, fs, rfl, hcond.1⟩)))
      subst hwv
      have hvnot : v ∉ freeVars (.makeData adt tag fs) := fun hm => by
        rw [List.contains_iff_mem.mpr hm] at hcond; cases hcond.2
      have hsub_eq : substMany ((v, substMany σEnv (.makeData adt tag fs)) :: σEnv) (.makeData adt tag fs) =
          substMany σEnv (.makeData adt tag fs) := by
        apply substMany_congr_lookup
        · exact fun q hq => (hbase.valsCl q hq).2
        · exact fun q hq => (hcons.valsCl q hq).2
        · intro z hz
          have hzv : (z == v) = false := beq_false_of_ne (fun h => by subst h; exact hvnot hz)
          simp [lookupSubstEnv, hzv]
      refine ⟨hbase.valsCl, hbase.aliasSound, ?_⟩
      intro p hp; rcases List.mem_cons.mp hp with rfl | hpr
      · refine ⟨hcond.1, ?_, ?_⟩
        · intro z hz
          have hzv : (z == v) = false := beq_false_of_ne (fun h => by subst h; exact hvnot hz)
          simpa [lookupSubstEnv, hzv] using hrhs_dom z hz
        · simp [lookupSubstEnv, CoKnownValM.toExpr, hsub_eq]
      · exact hbase.knownSound p hpr
    · exact hbase
  | _ => exact hbase

/-- **Known-Value Resolution Soundness (`coResolveTermKnownValM_sound`, `src/core.gsa:6445`)**:
    Resolves literals, simple tuples/constructors, and aliased variables from `CoEnvM` to exact
    runtime values! -/
theorem coResolveTermKnownValM_sound {σEnv : List (Ident × Expr)} {cenv : CoEnvM}
    (hcons : CoEnvConsistent σEnv cenv) {tm : Expr} {kv : CoKnownValM}
    (hdom : ∀ z ∈ freeVars tm, (lookupSubstEnv z σEnv).isSome = true)
    (hres : coResolveTermKnownValM tm cenv = some kv) :
    IsValue (substMany σEnv tm) ∧
    kv.allSimple = true ∧
    (∀ z ∈ freeVars kv.toExpr, (lookupSubstEnv z σEnv).isSome = true) ∧
    substMany σEnv tm = substMany σEnv kv.toExpr := by
  cases tm with
  | lit l =>
    simp [coResolveTermKnownValM] at hres; subst hres
    refine ⟨by rw [(substMany_atom_eq σEnv).1 l]; exact .lit l, rfl, ?_, rfl⟩
    intro _ h; simp [CoKnownValM.toExpr, freeVars] at h
  | tuple es =>
    simp only [coResolveTermKnownValM] at hres
    split at hres
    · rename_i hsimp; injection hres with hres; subst hres
      exact ⟨CoKnownValM.substMany_isValue hcons.valsCl (.tuple es) hsimp hdom, hsimp, hdom, rfl⟩
    · cases hres
  | makeData adt tag fs =>
    simp only [coResolveTermKnownValM] at hres
    split at hres
    · rename_i hsimp; injection hres with hres; subst hres
      exact ⟨CoKnownValM.substMany_isValue hcons.valsCl (.data adt tag fs) hsimp hdom, hsimp, hdom, rfl⟩
    · cases hres
  | var v =>
    simp only [coResolveTermKnownValM] at hres
    rcases hcons.knownSound _ (lookupEnvOptM_mem hres) with ⟨hsimp, hkv_dom, hlu_rv⟩
    have hal := coResolveAliasM_sound hcons v
    have hlu_v : lookupSubstEnv v σEnv = some (substMany σEnv kv.toExpr) := by
      rw [← hal]; exact hlu_rv
    have htm_eq : substMany σEnv (.var v) = substMany σEnv kv.toExpr := by
      rw [substMany_var_lookup (fun p hp => (hcons.valsCl p hp).2) v, hlu_v]
    rw [htm_eq]
    exact ⟨CoKnownValM.substMany_isValue hcons.valsCl kv hsimp hkv_dom, hsimp, hkv_dom, rfl⟩
  | _ => simp [coResolveTermKnownValM] at hres

private theorem coLitsEqualM_iff_beq {l1 l2 : Lit}
    (hf1 : isFloatAnyLit l1 = false) (hf2 : isFloatAnyLit l2 = false) :
    coLitsEqualM l1 l2 = (l1 == l2) := by
  cases l1 <;> cases l2 <;> dsimp [isFloatAnyLit] at hf1 hf2 <;>
    try cases hf1 <;> try cases hf2 <;> rfl

mutual
/-- **`CoPatYes` Soundness Under `CoEnvConsistent` (`coMatchPatKnownEnv_yes_sound`)**:
    Whenever `coMatchPatKnownEnv pat tm cenv = .yes binds`, `substMany σEnv tm` is already a closed
    value, every bound term evaluates in 0 steps to a closed value, and `matchPat` succeeds with
    exact bindings `binds.map (fun b => (b.1, substMany σEnv b.2))`! -/
theorem coMatchPatKnownEnv_yes_sound {σEnv : List (Ident × Expr)} {cenv : CoEnvM}
    (hcons : CoEnvConsistent σEnv cenv) :
    (pat : Pat) → (tm : Expr) → {binds : List (Ident × Expr)} →
      (∀ z ∈ freeVars tm, (lookupSubstEnv z σEnv).isSome = true) →
      coMatchPatKnownEnv pat tm cenv = .yes binds →
      IsValue (substMany σEnv tm) ∧
      (∀ b ∈ binds, IsValue (substMany σEnv b.2) ∧ freeVars (substMany σEnv b.2) = []) ∧
      matchPat pat (substMany σEnv tm) = some (binds.map (fun b => (b.1, substMany σEnv b.2)))
  | .wild, tm, binds, hdom, hm => by
    have hval : IsValue (substMany σEnv tm) ∧ binds = [] := by
      simp only [coMatchPatKnownEnv] at hm
      cases hs : coSimpleTerm tm <;> simp only [hs, Bool.false_eq_true, ↓reduceIte] at hm
      · cases tm with
        | tuple es =>
          cases ha : coAllSimple es <;> simp only [ha, Bool.false_eq_true, ↓reduceIte] at hm
          · cases hm
          · injection hm with hm
            exact ⟨CoKnownValM.substMany_isValue hcons.valsCl (.tuple es) ha hdom, hm.symm⟩
        | makeData adt tag fs =>
          cases ha : coAllSimple fs <;> simp only [ha, Bool.false_eq_true, ↓reduceIte] at hm
          · cases hm
          · injection hm with hm
            exact ⟨CoKnownValM.substMany_isValue hcons.valsCl (.data adt tag fs) ha hdom, hm.symm⟩
        | _ => cases hm
      · injection hm with hm
        exact ⟨coSimpleTerm_substMany_isValue hcons.valsCl hs hdom, hm.symm⟩
    rcases hval with ⟨hv, rfl⟩
    exact ⟨hv, (fun _ h => by cases h), rfl⟩
  | .var v, tm, binds, hdom, hm => by
    have hval : IsValue (substMany σEnv tm) ∧ binds = [(v, tm)] := by
      simp only [coMatchPatKnownEnv] at hm
      cases hs : coSimpleTerm tm <;> simp only [hs, Bool.false_eq_true, ↓reduceIte] at hm
      · cases tm with
        | tuple es =>
          cases ha : coAllSimple es <;> simp only [ha, Bool.false_eq_true, ↓reduceIte] at hm
          · cases hm
          · injection hm with hm
            exact ⟨CoKnownValM.substMany_isValue hcons.valsCl (.tuple es) ha hdom, hm.symm⟩
        | makeData adt tag fs =>
          cases ha : coAllSimple fs <;> simp only [ha, Bool.false_eq_true, ↓reduceIte] at hm
          · cases hm
          · injection hm with hm
            exact ⟨CoKnownValM.substMany_isValue hcons.valsCl (.data adt tag fs) ha hdom, hm.symm⟩
        | _ => cases hm
      · injection hm with hm
        exact ⟨coSimpleTerm_substMany_isValue hcons.valsCl hs hdom, hm.symm⟩
    rcases hval with ⟨hv, rfl⟩
    refine ⟨hv, ?_, rfl⟩
    intro b hb; simp at hb; rcases hb with ⟨rfl, rfl⟩
    exact ⟨hv, substMany_closed_freeVars_nil (fun p hp => (hcons.valsCl p hp).2) hdom⟩
  | .lit pLit, tm, _, hdom, hm => by
    simp only [coMatchPatKnownEnv] at hm
    cases hf1 : isFloatAnyLit pLit <;> simp only [hf1, Bool.false_eq_true, ↓reduceIte] at hm
    · cases hres : coResolveTermKnownValM tm cenv <;> simp only [hres] at hm
      · cases hm
      · rename_i kv
        cases kv with
        | lit tLit =>
          dsimp only at hm
          cases hf2 : isFloatAnyLit tLit <;> simp only [hf2, Bool.false_eq_true, ↓reduceIte] at hm
          · cases heq : coLitsEqualM pLit tLit <;> simp only [heq, Bool.false_eq_true, ↓reduceIte] at hm
            · cases hm
            · injection hm with hm; subst hm
              rcases coResolveTermKnownValM_sound hcons hdom hres with ⟨hv, _, _, htm_eq⟩
              rw [coLitsEqualM_iff_beq hf1 hf2] at heq
              refine ⟨hv, (fun _ h => by cases h), ?_⟩
              dsimp only [CoKnownValM.toExpr] at htm_eq
              rw [htm_eq, (substMany_atom_eq σEnv).1 tLit]
              simp [matchPat, heq]
          · cases hm
        | _ => cases hm
    · cases hm
  | .tuple subPats, tm, _, hdom, hm => by
    simp only [coMatchPatKnownEnv] at hm
    cases hres : coResolveTermKnownValM tm cenv <;> simp only [hres] at hm
    · cases hm
    · rename_i kv
      cases kv with
      | tuple elems =>
        dsimp only at hm
        split at hm
        · cases hm
        · rcases coResolveTermKnownValM_sound hcons hdom hres with ⟨hv, _, helems_dom, htm_eq⟩
          rcases coMatchPatListKnownEnv_yes_sound hcons subPats elems helems_dom hm with ⟨_, hb_cl, hmp⟩
          dsimp only [CoKnownValM.toExpr] at htm_eq
          refine ⟨hv, hb_cl, ?_⟩
          rw [htm_eq, substMany_tuple_eq]
          simpa [matchPat] using hmp
      | _ => cases hm
  | .ctor patAdt patTag subPats, tm, _, hdom, hm => by
    simp only [coMatchPatKnownEnv] at hm
    cases hres : coResolveTermKnownValM tm cenv <;> simp only [hres] at hm
    · cases hm
    · rename_i kv
      cases kv with
      | data dataAdt dataTag fields =>
        dsimp only at hm
        cases hadt : (patAdt != dataAdt) <;> simp only [hadt, Bool.false_eq_true, ↓reduceIte] at hm
        · cases htag : (patTag != dataTag) <;> simp only [htag, Bool.false_eq_true, ↓reduceIte] at hm
          · split at hm
            · cases hm
            · rcases coResolveTermKnownValM_sound hcons hdom hres with ⟨hv, _, hf_dom, htm_eq⟩
              rcases coMatchPatListKnownEnv_yes_sound hcons subPats fields hf_dom hm with ⟨_, hb_cl, hmp⟩
              simp only [bne_eq_false_iff_eq] at hadt htag
              subst hadt; subst htag
              dsimp only [CoKnownValM.toExpr] at htm_eq
              refine ⟨hv, hb_cl, ?_⟩
              rw [htm_eq, substMany_makeData_eq]
              simpa [matchPat] using hmp
          · cases hm
        · cases hm
      | _ => cases hm
termination_by pat => sizeOf pat

theorem coMatchPatListKnownEnv_yes_sound {σEnv : List (Ident × Expr)} {cenv : CoEnvM}
    (hcons : CoEnvConsistent σEnv cenv) :
    (ps : List Pat) → (es : List Expr) → {binds : List (Ident × Expr)} →
      (∀ z ∈ freeVarsList es, (lookupSubstEnv z σEnv).isSome = true) →
      coMatchPatListKnownEnv ps es cenv = .yes binds →
      (∀ v ∈ substManyList σEnv es, IsValue v) ∧
      (∀ b ∈ binds, IsValue (substMany σEnv b.2) ∧ freeVars (substMany σEnv b.2) = []) ∧
      matchPats ps (substManyList σEnv es) = some (binds.map (fun b => (b.1, substMany σEnv b.2)))
  | [], [], _, _, hm => by
    simp [coMatchPatListKnownEnv] at hm; subst hm
    exact ⟨(fun _ h => by simp [substManyList] at h), (fun _ h => by cases h), rfl⟩
  | p :: rp, e :: re, _, hdom, hm => by
    simp only [coMatchPatListKnownEnv] at hm
    cases h1 : coMatchPatKnownEnv p e cenv <;> rw [h1] at hm
    · rename_i b1
      cases h2 : coMatchPatListKnownEnv rp re cenv <;> rw [h2] at hm
      · rename_i b2
        injection hm with hm; subst hm
        rcases coMatchPatKnownEnv_yes_sound hcons p e (fun z hz => hdom z (by simp [freeVarsList, hz])) h1 with
          ⟨hve, hb1, hmp1⟩
        rcases coMatchPatListKnownEnv_yes_sound hcons rp re (fun z hz => hdom z (by simp [freeVarsList, hz])) h2 with
          ⟨hvre, hb2, hmp2⟩
        refine ⟨?_, ?_, ?_⟩
        · intro v hv; simp only [substManyList, List.map] at hv
          rcases List.mem_cons.mp hv with rfl | hvr
          · exact hve
          · exact hvre v hvr
        · intro b hb; rcases List.mem_append.mp hb with hba | hbb
          · exact hb1 b hba
          · exact hb2 b hbb
        · simp only [substManyList, List.map] at hmp2 ⊢
          simp [matchPats, hmp1, hmp2, List.map_append]
      · cases hm
      · cases hm
    · cases hm
    · cases h2 : coMatchPatListKnownEnv rp re cenv <;> rw [h2] at hm <;> cases hm
  | [], _ :: _, _, _, hm | _ :: _, [], _, _, hm => by simp [coMatchPatListKnownEnv] at hm
termination_by ps => sizeOf ps
end

mutual
/-- **`CoPatNo` Soundness Under `CoEnvConsistent` (`coMatchPatKnownEnv_no_sound`)**:
    Whenever `coMatchPatKnownEnv pat tm cenv = .no` (even on same-ADT/same-tag constructors whose
    nested subpattern mismatches!), `matchPat pat (substMany σEnv tm) = none`! -/
theorem coMatchPatKnownEnv_no_sound {σEnv : List (Ident × Expr)} {cenv : CoEnvM}
    (hcons : CoEnvConsistent σEnv cenv) :
    (pat : Pat) → (tm : Expr) →
      (∀ z ∈ freeVars tm, (lookupSubstEnv z σEnv).isSome = true) →
      IsValue (substMany σEnv tm) →
      coMatchPatKnownEnv pat tm cenv = .no →
      matchPat pat (substMany σEnv tm) = none
  | .wild, tm, _, _, hm => by
    simp only [coMatchPatKnownEnv] at hm
    split at hm
    · cases hm
    · cases tm <;> simp at hm
      all_goals (split at hm <;> cases hm)
  | .var _, tm, _, _, hm => by
    simp only [coMatchPatKnownEnv] at hm
    split at hm
    · cases hm
    · cases tm <;> simp at hm
      all_goals (split at hm <;> cases hm)
  | .lit pLit, tm, hdom, _, hm => by
    simp only [coMatchPatKnownEnv] at hm
    cases hf1 : isFloatAnyLit pLit <;> simp only [hf1, Bool.false_eq_true, ↓reduceIte] at hm
    · cases hres : coResolveTermKnownValM tm cenv <;> simp only [hres] at hm
      · cases hm
      · rename_i kv
        cases kv with
        | lit tLit =>
          dsimp only at hm
          cases hf2 : isFloatAnyLit tLit <;> simp only [hf2, Bool.false_eq_true, ↓reduceIte] at hm
          · cases heq : coLitsEqualM pLit tLit <;> simp only [heq, Bool.false_eq_true, ↓reduceIte] at hm
            · rcases coResolveTermKnownValM_sound hcons hdom hres with ⟨_, _, _, htm_eq⟩
              rw [coLitsEqualM_iff_beq hf1 hf2] at heq
              dsimp only [CoKnownValM.toExpr] at htm_eq
              rw [htm_eq, (substMany_atom_eq σEnv).1 tLit]
              simp [matchPat, heq]
            · cases hm
          · cases hm
        | _ => cases hm
    · cases hm
  | .tuple subPats, tm, hdom, _, hm => by
    simp only [coMatchPatKnownEnv] at hm
    cases hres : coResolveTermKnownValM tm cenv <;> simp only [hres] at hm
    · cases hm
    · rename_i kv
      cases kv with
      | tuple elems =>
        dsimp only at hm
        split at hm
        · cases hm
        · rename_i hlen
          simp only [bne_iff_ne, Decidable.not_not] at hlen
          rcases coResolveTermKnownValM_sound hcons hdom hres with ⟨hv, _, helems_dom, htm_eq⟩
          dsimp only [CoKnownValM.toExpr] at htm_eq
          rw [htm_eq, substMany_tuple_eq] at hv ⊢
          cases hv with
          | tuple hvs =>
            have hvs' : ∀ i (hi : i < elems.length), IsValue (substMany σEnv elems[i]) := by
              intro i hi
              apply hvs
              simp [substManyList]
              exact ⟨elems[i], List.getElem_mem hi, rfl⟩
            simpa [matchPat] using
              coMatchPatListKnownEnv_no_sound hcons subPats elems hlen helems_dom hvs' hm
      | _ => cases hm
  | .ctor patAdt patTag subPats, tm, hdom, _, hm => by
    simp only [coMatchPatKnownEnv] at hm
    cases hres : coResolveTermKnownValM tm cenv <;> simp only [hres] at hm
    · cases hm
    · rename_i kv
      cases kv with
      | data dataAdt dataTag fields =>
        dsimp only at hm
        rcases coResolveTermKnownValM_sound hcons hdom hres with ⟨hv, _, hf_dom, htm_eq⟩
        dsimp only [CoKnownValM.toExpr] at htm_eq
        cases hadt : (patAdt != dataAdt) <;> simp only [hadt, Bool.false_eq_true, ↓reduceIte] at hm
        · simp only [bne_eq_false_iff_eq] at hadt; subst hadt
          cases htag : (patTag != dataTag) <;> simp only [htag, Bool.false_eq_true, ↓reduceIte] at hm
          · simp only [bne_eq_false_iff_eq] at htag; subst htag
            split at hm
            · cases hm
            · rename_i hlen
              simp only [bne_iff_ne, Decidable.not_not] at hlen
              rw [htm_eq, substMany_makeData_eq] at hv ⊢
              cases hv with
              | makeData _ _ hvs =>
                have hvs' : ∀ i (hi : i < fields.length), IsValue (substMany σEnv fields[i]) := by
                  intro i hi
                  apply hvs
                  simp [substManyList]
                  exact ⟨fields[i], List.getElem_mem hi, rfl⟩
                simpa [matchPat] using
                  coMatchPatListKnownEnv_no_sound hcons subPats fields hlen hf_dom hvs' hm
          · simp only [bne_iff_ne] at htag
            have htag_beq : (patTag == dataTag) = false := beq_false_of_ne htag
            rw [htm_eq, substMany_makeData_eq]
            simp [matchPat, htag_beq]
        · cases hm
      | _ => cases hm
termination_by pat => sizeOf pat

theorem coMatchPatListKnownEnv_no_sound {σEnv : List (Ident × Expr)} {cenv : CoEnvM}
    (hcons : CoEnvConsistent σEnv cenv) :
    (ps : List Pat) → (es : List Expr) →
      ps.length = es.length →
      (∀ z ∈ freeVarsList es, (lookupSubstEnv z σEnv).isSome = true) →
      (∀ i (hi : i < es.length), IsValue (substMany σEnv es[i])) →
      coMatchPatListKnownEnv ps es cenv = .no →
      matchPats ps (substManyList σEnv es) = none
  | [], [], _, _, _, hm => by simp [coMatchPatListKnownEnv] at hm
  | p :: rp, e :: re, hlen, hdom, hvs, hm => by
    simp only [coMatchPatListKnownEnv] at hm
    have hve : IsValue (substMany σEnv e) := hvs 0 (by simp)
    have hvs_r : ∀ i (hi : i < re.length), IsValue (substMany σEnv re[i]) :=
      fun i hi => hvs (i + 1) (Nat.succ_lt_succ hi)
    cases h1 : coMatchPatKnownEnv p e cenv <;> rw [h1] at hm
    · cases h2 : coMatchPatListKnownEnv rp re cenv <;> rw [h2] at hm
      · cases hm
      · have hmp2 := coMatchPatListKnownEnv_no_sound hcons rp re (by simp at hlen; exact hlen)
          (fun z hz => hdom z (by simp [freeVarsList, hz])) hvs_r h2
        simp only [substManyList, List.map] at hmp2 ⊢
        simp only [matchPats, hmp2]
        cases matchPat p (substMany σEnv e) <;> rfl
      · cases hm
    · have hmp1 := coMatchPatKnownEnv_no_sound hcons p e
        (fun z hz => hdom z (by simp [freeVarsList, hz])) hve h1
      simp only [substManyList, List.map, matchPats, hmp1]
    · cases h2 : coMatchPatListKnownEnv rp re cenv <;> rw [h2] at hm
      · cases hm
      · have hmp2 := coMatchPatListKnownEnv_no_sound hcons rp re (by simp at hlen; exact hlen)
          (fun z hz => hdom z (by simp [freeVarsList, hz])) hvs_r h2
        simp only [substManyList, List.map] at hmp2 ⊢
        simp only [matchPats, hmp2]
        cases matchPat p (substMany σEnv e) <;> rfl
      · cases hm
  | [], _ :: _, hlen, _, _, _ | _ :: _, [], hlen, _, _, _ => by simp at hlen
termination_by ps => sizeOf ps
end

def wrapFreshLetBinds : List Ident → List Expr → Expr → Expr
  | f :: fr, rhs :: rr, body => .let_ f rhs (wrapFreshLetBinds fr rr body)
  | _, _, body => body

private theorem wrapFreshLetBinds_subst_closedObsEquiv (Δ : AdtEnv) (Φ : FunEnv) :
    (fvs : List Ident) → (rhss : List Expr) → {σEnv : List (Ident × Expr)} → (body : Expr) →
      fvs.length = rhss.length →
      fvs.Nodup →
      (∀ p ∈ σEnv, IsValue p.2 ∧ freeVars p.2 = []) →
      (∀ rhs ∈ rhss, IsValue (substMany σEnv rhs) ∧ freeVars (substMany σEnv rhs) = []) →
      (∀ f ∈ fvs, ∀ r ∈ rhss, f ∉ freeVars r) →
      ClosedObsEquiv Δ Φ Φ
        (substMany σEnv (wrapFreshLetBinds fvs rhss body))
        (substMany ((fvs.zip (rhss.map (substMany σEnv))) ++ σEnv) body)
  | [], [], _, body, _, _, _, _, _ => by
    simp [wrapFreshLetBinds]
    exact ClosedObsEquiv.refl _ _ _
  | f :: fr, rhs :: rr, σEnv, body, hlen, hnd, hvals, hrhss, hfr_not => by
    rcases List.nodup_cons.mp hnd with ⟨hf_not_fr, hnd_r⟩
    rcases hrhss rhs (List.mem_cons_self ..) with ⟨hvr, hcr⟩
    simp only [wrapFreshLetBinds, substMany_let_eq]
    have hstep1 : ClosedObsEquiv Δ Φ Φ
        (.let_ f (substMany σEnv rhs) (substMany (σEnv.filter (fun p => !(f == p.1))) (wrapFreshLetBinds fr rr body)))
        (subst f (substMany σEnv rhs) (substMany (σEnv.filter (fun p => !(f == p.1))) (wrapFreshLetBinds fr rr body))) :=
      ClosedObsEquiv.of_obsEquiv (obsEquiv_of_det_step (fun _ => .letVal hvr))
    refine ClosedObsEquiv.trans hstep1 ?_
    rw [subst_substMany_filter_eq f hcr (fun p hp => (hvals p hp).2) (wrapFreshLetBinds fr rr body)]
    let σEnv' := (f, substMany σEnv rhs) :: σEnv
    have hvals' : ∀ p ∈ σEnv', IsValue p.2 ∧ freeVars p.2 = [] := by
      intro p hp; rcases List.mem_cons.mp hp with rfl | hpr
      · exact ⟨hvr, hcr⟩
      · exact hvals p hpr
    have hrr_eq : ∀ r ∈ rr, substMany σEnv' r = substMany σEnv r := by
      intro r hr
      apply substMany_congr_lookup (fun p hp => (hvals' p hp).2) (fun p hp => (hvals p hp).2)
      intro z hz
      have hzf : (z == f) = false :=
        beq_false_of_ne (fun h => by rw [h] at hz; exact hfr_not f (List.mem_cons_self ..) r (List.mem_cons_of_mem _ hr) hz)
      simp [σEnv', lookupSubstEnv, hzf]
    have hrhss' : ∀ r ∈ rr, IsValue (substMany σEnv' r) ∧ freeVars (substMany σEnv' r) = [] := by
      intro r hr; rw [hrr_eq r hr]; exact hrhss r (List.mem_cons_of_mem _ hr)
    have ih := wrapFreshLetBinds_subst_closedObsEquiv Δ Φ fr rr (σEnv := σEnv') body
      (by simp at hlen; exact hlen) hnd_r hvals' hrhss'
      (fun g hg r hr => hfr_not g (List.mem_cons_of_mem _ hg) r (List.mem_cons_of_mem _ hr))
    refine ClosedObsEquiv.trans ih ?_
    have hmap_eq : rr.map (substMany σEnv') = rr.map (substMany σEnv) :=
      List.map_congr_left hrr_eq
    rw [hmap_eq]
    have hsub_eq : substMany ((fr.zip (rr.map (substMany σEnv))) ++ σEnv') body =
        substMany (((f :: fr).zip ((rhs :: rr).map (substMany σEnv))) ++ σEnv) body := by
      apply substMany_congr_lookup
      · intro q hq; rcases List.mem_append.mp hq with h1 | h2
        · rcases List.mem_map.mp (mem_snd_of_mem_zip h1) with ⟨r, hr, heq⟩
          rw [← heq]; exact (hrhss r (List.mem_cons_of_mem _ hr)).2
        · exact (hvals' q h2).2
      · intro q hq; rcases List.mem_append.mp hq with h1 | h2
        · rcases List.mem_map.mp (mem_snd_of_mem_zip h1) with ⟨r, hr, heq⟩
          rw [← heq]; exact (hrhss r hr).2
        · exact (hvals q h2).2
      · intro z _
        simp only [List.map, List.zip_cons_cons, List.cons_append]
        rw [lookupSubstEnv_append]
        by_cases hzf : (z == f) = true
        · have heq := eq_of_beq hzf
          have hznot_fr : z ∉ fr := heq ▸ hf_not_fr
          have hfnot_zip : z ∉ (fr.zip (rr.map (substMany σEnv))).map Prod.fst := by
            rw [zip_fst_eq_of_eq_len (by simp at hlen; simp [hlen])]; exact hznot_fr
          have hnone : lookupSubstEnv z (fr.zip (rr.map (substMany σEnv))) = none := by
            cases h : lookupSubstEnv z (fr.zip (rr.map (substMany σEnv)))
            · rfl
            · have his := lookupSubstEnv_isSome_iff_contains z (fr.zip (rr.map (substMany σEnv)))
              rw [h] at his
              exact False.elim (hfnot_zip (List.contains_iff_mem.mp his.symm))
          rw [hnone]
          simp [σEnv', lookupSubstEnv, hzf]
        · simp only [Bool.not_eq_true] at hzf
          simp only [σEnv', lookupSubstEnv, hzf, Bool.false_eq_true, ↓reduceIte]
          rw [← lookupSubstEnv_append]
    rw [hsub_eq]
    exact ClosedObsEquiv.refl _ _ _
  | [], _ :: _, _, _, hlen, _, _, _, _ | _ :: _, [], _, _, hlen, _, _, _, _ => by simp at hlen

private theorem map_pair_eq_zip_map (f : Expr → Expr) :
    (bs : List (Ident × Expr)) →
      bs.map (fun b => (b.1, f b.2)) = (bs.map Prod.fst).zip ((bs.map Prod.snd).map f)
  | [] => rfl
  | _ :: r => by simp [map_pair_eq_zip_map f r]

/-- **Full `CoEnv`-Driven `coTryReduceMatch` Soundness (`coTryReduceMatchEnv_alphaClone_obsEquiv`, `src/core.gsa:6554-6588`)**:
    Derives skipped `.no` arms, `.yes binds` match hit, fresh `let` bindings, and `coCloneTerm`
    (`AlphaOptRel`) arm body cloning **directly from `CoEnvConsistent σEnv cenv`**! -/
theorem coTryReduceMatchEnv_alphaClone_obsEquiv (Δ : AdtEnv) {Φ : FunEnv} (hΦ : ClosedFunEnv Φ)
    {σEnv : List (Ident × Expr)} {cenv : CoEnvM}
    (hcons : CoEnvConsistent σEnv cenv)
    {scrut : Expr} (hscrut_dom : ∀ z ∈ freeVars scrut, (lookupSubstEnv z σEnv).isSome = true)
    (skippedArms : List (Pat × Expr))
    (hskip : ∀ a ∈ skippedArms, coMatchPatKnownEnv a.1 scrut cenv = .no)
    {hitPat : Pat} {hitBody clonedBody : Expr} (tailArms : List (Pat × Expr))
    {binds : List (Ident × Expr)} {freshVars : List Ident}
    (hhit : coMatchPatKnownEnv hitPat scrut cenv = .yes binds)
    (harm_dom : ∀ z ∈ freeVars hitBody, z ∈ patBoundNames hitPat ∨ (lookupSubstEnv z σEnv).isSome = true)
    (hb_nodup : (binds.map Prod.fst).Nodup)
    (hfr_len : freshVars.length = binds.length)
    (hfr_nodup : freshVars.Nodup)
    (hfr_not_rhss : ∀ f ∈ freshVars, ∀ b ∈ binds, f ∉ freeVars b.2)
    (hfr_not_env : ∀ f ∈ freshVars, ∀ z ∈ freeVars hitBody, z ∉ binds.map Prod.fst → z ≠ f)
    (hclone : AlphaOptRel Φ ((binds.map Prod.fst).zip freshVars) hitBody clonedBody) :
    ClosedObsEquiv Δ Φ Φ
      (substMany σEnv (.match_ scrut (skippedArms ++ (hitPat, hitBody) :: tailArms)))
      (substMany σEnv (wrapFreshLetBinds freshVars (binds.map Prod.snd) clonedBody)) := by
  rcases coMatchPatKnownEnv_yes_sound hcons hitPat scrut hscrut_dom hhit with ⟨hv_s, hbinds_vc, hmp_hit⟩
  have hvs_cl : freeVars (substMany σEnv scrut) = [] :=
    substMany_closed_freeVars_nil (fun p hp => (hcons.valsCl p hp).2) hscrut_dom
  rw [substMany_match_eq]
  have hskip_steps : ∀ (pref : List (Pat × Expr)),
      (∀ a ∈ pref, coMatchPatKnownEnv a.1 scrut cenv = .no) →
      ClosedObsEquiv Δ Φ Φ
        (.match_ (substMany σEnv scrut) (substManyArms σEnv (pref ++ (hitPat, hitBody) :: tailArms)))
        (.match_ (substMany σEnv scrut) (substManyArms σEnv ((hitPat, hitBody) :: tailArms))) := by
    intro pref; induction pref with
    | nil => intro _; exact ClosedObsEquiv.refl _ _ _
    | cons a r ih =>
      intro hs_all
      rcases a with ⟨pa, ba⟩
      have hno := coMatchPatKnownEnv_no_sound hcons pa scrut hscrut_dom hv_s (hs_all (pa, ba) (List.mem_cons_self ..))
      simp only [List.cons_append, substManyArms, List.map]
      have hmiss : ClosedObsEquiv Δ Φ Φ
          (.match_ (substMany σEnv scrut)
            ((pa, substMany (σEnv.filter (fun p => !((patBoundNames pa).contains p.1))) ba) ::
             substManyArms σEnv (r ++ (hitPat, hitBody) :: tailArms)))
          (.match_ (substMany σEnv scrut) (substManyArms σEnv (r ++ (hitPat, hitBody) :: tailArms))) :=
        ClosedObsEquiv.of_obsEquiv (obsEquiv_of_det_step (fun _ => .matchMiss hv_s hno))
      exact ClosedObsEquiv.trans hmiss (ih (fun x hx => hs_all x (List.mem_cons_of_mem _ hx)))
  refine ClosedObsEquiv.trans (hskip_steps skippedArms hskip) ?_
  simp only [substManyArms, List.map]
  let semBinds := binds.map (fun b => (b.1, substMany σEnv b.2))
  have hhit_step : ClosedObsEquiv Δ Φ Φ
      (.match_ (substMany σEnv scrut)
        ((hitPat, substMany (σEnv.filter (fun p => !((patBoundNames hitPat).contains p.1))) hitBody) ::
         substManyArms σEnv tailArms))
      (substMany semBinds (substMany (σEnv.filter (fun p => !((patBoundNames hitPat).contains p.1))) hitBody)) :=
    ClosedObsEquiv.of_obsEquiv (obsEquiv_of_det_step (fun _ => .matchHit hv_s hmp_hit))
  refine ClosedObsEquiv.trans hhit_step ?_
  have hsem_fst : semBinds.map Prod.fst = patBoundNames hitPat :=
    matchPat_fst_eq_patBoundNames hitPat hmp_hit
  have hsem_cl : ∀ q ∈ semBinds, freeVars q.2 = [] := by
    intro q hq; rcases List.mem_map.mp hq with ⟨b, hb, rfl⟩; exact (hbinds_vc b hb).2
  rw [substMany_binds_filter_eq hsem_cl (fun p hp => (hcons.valsCl p hp).2) hsem_fst hitBody]
  have hwrap := wrapFreshLetBinds_subst_closedObsEquiv Δ Φ freshVars (binds.map Prod.snd) clonedBody
    (by simp [hfr_len]) hfr_nodup hcons.valsCl
    (fun r hr => by rcases List.mem_map.mp hr with ⟨b, hb, rfl⟩; exact hbinds_vc b hb)
    (fun f hf r hr => by rcases List.mem_map.mp hr with ⟨b, hb, rfl⟩; exact hfr_not_rhss f hf b hb)
  refine ClosedObsEquiv.trans ?_ (ClosedObsEquiv.symm hwrap)
  apply alphaOptRel_subst_closedObsEquiv Δ hΦ hclone
  have hbn_eq : binds.map Prod.fst = patBoundNames hitPat := by
    have hmap_fst : semBinds.map Prod.fst = binds.map Prod.fst := by
      simp [semBinds, List.map_map, Function.comp]
    rw [← hmap_fst, hsem_fst]
  refine ⟨?_, ?_, ?_⟩
  · intro q hq; rcases List.mem_append.mp hq with h1 | h2
    · rcases List.mem_map.mp h1 with ⟨b, hb, rfl⟩; exact hbinds_vc b hb
    · exact hcons.valsCl q h2
  · intro q hq; rcases List.mem_append.mp hq with h1 | h2
    · rcases List.mem_map.mp (mem_snd_of_mem_zip h1) with ⟨r, hr, heq⟩
      rcases List.mem_map.mp hr with ⟨b, hb, rfl⟩
      rw [← heq]; exact hbinds_vc b hb
    · exact hcons.valsCl q h2
  · intro z hz
    by_cases hzb : z ∈ binds.map Prod.fst
    · rcases List.mem_iff_getElem.mp hzb with ⟨i, hi, rfl⟩
      have hi_b : i < binds.length := by simp at hi; exact hi
      have hi_f : i < freshVars.length := by omega
      have hsem_eq : semBinds = (binds.map Prod.fst).zip ((binds.map Prod.snd).map (substMany σEnv)) :=
        map_pair_eq_zip_map (substMany σEnv) binds
      have hlu1 := lookupSubstEnv_nodup_zip (vs := (binds.map Prod.snd).map (substMany σEnv)) hb_nodup
        (by simp) i hi
      have hlu2 := lookupSubstEnv_nodup_zip (vs := (binds.map Prod.snd).map (substMany σEnv)) hfr_nodup
        (by simp [hfr_len]) i hi_f
      have hren := lookupRename_nodup_zip hb_nodup (ys := freshVars) (by simp [hfr_len]) [] i hi
      simp only [List.append_nil] at hren
      exact ⟨((binds.map Prod.snd).map (substMany σEnv))[i]'(by simp [hi_b]),
             by rw [hsem_eq, lookupSubstEnv_append, hlu1],
             by rw [hren, lookupSubstEnv_append, hlu2]⟩
    · have hz_dom : (lookupSubstEnv z σEnv).isSome = true := by
        rcases harm_dom z hz with hpat | hd
        · exact False.elim (hzb (hbn_eq.symm ▸ hpat))
        · exact hd
      have hznot_sem : z ∉ semBinds.map Prod.fst := by rw [hsem_fst, ← hbn_eq]; exact hzb
      have hznot_pair : z ∉ ((binds.map Prod.fst).zip freshVars).map Prod.fst := by
        rw [zip_fst_eq_of_eq_len (by simp [hfr_len])]; exact hzb
      have hren_id : lookupRename ((binds.map Prod.fst).zip freshVars) z = z := by
        simpa [lookupRename] using lookupRename_not_mem_fst (ρ := []) hznot_pair
      have hznot_fr : z ∉ (freshVars.zip ((binds.map Prod.snd).map (substMany σEnv))).map Prod.fst := by
        rw [zip_fst_eq_of_eq_len (by simp [hfr_len])]
        intro hmem_fr
        exact hfr_not_env z hmem_fr z hz hzb rfl
      cases hlu_z : lookupSubstEnv z σEnv
      · rw [hlu_z] at hz_dom; simp at hz_dom
      · rename_i vz
        exact ⟨vz, by rw [lookupSubstEnv_not_mem_fst hznot_sem, hlu_z],
                   by rw [hren_id, lookupSubstEnv_not_mem_fst hznot_fr, hlu_z]⟩

/-! ### 10.5 Interface-Scoped `ScopedCtxObsEquiv`, General OptBody / `TmMakeCls`-in-Body `$spec$` & Exact `$spec$19` / `$spec$18` Artifact Proofs -/

def ctxInDom (dom : Ident → Bool) : ExprCtx → Bool
  | .hole => true
  | .lam _ _ _ C => ctxInDom dom C
  | .letLhs _ C b => ctxInDom dom C && exprInDom dom b
  | .letRhs _ a C => exprInDom dom a && ctxInDom dom C
  | .applyFn C args => ctxInDom dom C && exprListInDom dom args
  | .applyArg fn pre C post =>
    exprInDom dom fn && exprListInDom dom pre && ctxInDom dom C && exprListInDom dom post
  | .applyDirArg nm pre C post =>
    dom nm && exprListInDom dom pre && ctxInDom dom C && exprListInDom dom post
  | .binL _ C b => ctxInDom dom C && exprInDom dom b
  | .binR _ a C => exprInDom dom a && ctxInDom dom C
  | .un _ C => ctxInDom dom C
  | .ifC C t e2 => ctxInDom dom C && exprInDom dom t && exprInDom dom e2
  | .ifT c C e2 => exprInDom dom c && ctxInDom dom C && exprInDom dom e2
  | .ifE c t C => exprInDom dom c && exprInDom dom t && ctxInDom dom C
  | .whileCond C b => ctxInDom dom C && exprInDom dom b
  | .whileBody c C => exprInDom dom c && ctxInDom dom C
  | .matchScrut C arms => ctxInDom dom C && exprArmsInDom dom arms
  | .matchArm scrut pre _ C post =>
    exprInDom dom scrut && exprArmsInDom dom pre && ctxInDom dom C && exprArmsInDom dom post
  | .tupleElem pre C post | .blockElem pre C post | .makeDataElem _ _ pre C post
  | .concPrimElem _ pre C post =>
    exprListInDom dom pre && ctxInDom dom C && exprListInDom dom post
  | .getTag C | .cellNew C | .cellGet C | .spawn C | .await C => ctxInDom dom C
  | .cellSetL C b => ctxInDom dom C && exprInDom dom b
  | .cellSetR a C => exprInDom dom a && ctxInDom dom C

private theorem exprListInDom_append {dom : Ident → Bool} {l1 l2 : List Expr} :
    exprListInDom dom (l1 ++ l2) = (exprListInDom dom l1 && exprListInDom dom l2) := by
  induction l1 with
  | nil => simp [exprListInDom]
  | cons _ _ ih => simp [exprListInDom, ih, Bool.and_assoc]

private theorem exprArmsInDom_append {dom : Ident → Bool} {l1 l2 : List (Pat × Expr)} :
    exprArmsInDom dom (l1 ++ l2) = (exprArmsInDom dom l1 && exprArmsInDom dom l2) := by
  induction l1 with
  | nil => simp [exprArmsInDom]
  | cons _ _ ih => simp [exprArmsInDom, ih, Bool.and_assoc]

theorem ctxInDom_fill {dom : Ident → Bool} (C : ExprCtx) {e : Expr}
    (hC : ctxInDom dom C = true) (he : exprInDom dom e = true) :
    exprInDom dom (C.fill e) = true := by
  induction C with
  | hole => exact he
  | lam _ _ _ C ih | un _ C ih | getTag C ih | cellNew C ih | cellGet C ih | spawn C ih | await C ih =>
    simp only [ctxInDom, ExprCtx.fill, exprInDom] at hC ⊢; exact ih hC
  | letLhs _ C b ih | binL _ C b ih | whileCond C b ih | cellSetL C b ih =>
    simp only [ctxInDom, ExprCtx.fill, exprInDom, Bool.and_eq_true] at hC ⊢
    exact ⟨ih hC.1, hC.2⟩
  | letRhs _ a C ih | binR _ a C ih | whileBody a C ih | cellSetR a C ih =>
    simp only [ctxInDom, ExprCtx.fill, exprInDom, Bool.and_eq_true] at hC ⊢
    exact ⟨hC.1, ih hC.2⟩
  | applyFn C args ih =>
    simp only [ctxInDom, ExprCtx.fill, exprInDom, Bool.and_eq_true] at hC ⊢
    exact ⟨ih hC.1, hC.2⟩
  | matchScrut C arms ih =>
    simp only [ctxInDom, ExprCtx.fill, exprInDom, Bool.and_eq_true] at hC ⊢
    exact ⟨ih hC.1, hC.2⟩
  | matchArm scrut pre pat C post ih =>
    simp only [ctxInDom, ExprCtx.fill, exprInDom, exprArmsInDom_append, exprArmsInDom, Bool.and_eq_true] at hC ⊢
    exact ⟨hC.1.1.1, hC.1.1.2, ih hC.1.2, hC.2⟩
  | applyArg fn pre C post ih =>
    simp only [ctxInDom, ExprCtx.fill, exprInDom, exprListInDom_append, exprListInDom, Bool.and_eq_true] at hC ⊢
    exact ⟨hC.1.1.1, hC.1.1.2, ih hC.1.2, hC.2⟩
  | applyDirArg nm pre C post ih =>
    simp only [ctxInDom, ExprCtx.fill, exprInDom, exprListInDom_append, exprListInDom, Bool.and_eq_true] at hC ⊢
    exact ⟨hC.1.1.1, hC.1.1.2, ih hC.1.2, hC.2⟩
  | ifC C t e2 ih =>
    simp only [ctxInDom, ExprCtx.fill, exprInDom, Bool.and_eq_true] at hC ⊢
    exact ⟨⟨ih hC.1.1, hC.1.2⟩, hC.2⟩
  | ifT c C e2 ih =>
    simp only [ctxInDom, ExprCtx.fill, exprInDom, Bool.and_eq_true] at hC ⊢
    exact ⟨⟨hC.1.1, ih hC.1.2⟩, hC.2⟩
  | ifE c t C ih =>
    simp only [ctxInDom, ExprCtx.fill, exprInDom, Bool.and_eq_true] at hC ⊢
    exact ⟨⟨hC.1.1, hC.1.2⟩, ih hC.2⟩
  | tupleElem pre C post ih | blockElem pre C post ih | makeDataElem _ _ pre C post ih
  | concPrimElem _ pre C post ih =>
    simp only [ctxInDom, ExprCtx.fill, exprInDom, exprListInDom_append, exprListInDom, Bool.and_eq_true] at hC ⊢
    exact ⟨hC.1.1, ih hC.1.2, hC.2⟩

theorem ctxInDom_comp {dom : Ident → Bool} (C1 C2 : ExprCtx)
    (h1 : ctxInDom dom C1 = true) (h2 : ctxInDom dom C2 = true) :
    ctxInDom dom (C1.comp C2) = true := by
  induction C1 with
  | hole => exact h2
  | lam _ _ _ C ih | un _ C ih | getTag C ih | cellNew C ih | cellGet C ih | spawn C ih | await C ih =>
    simp only [ctxInDom, ExprCtx.comp] at h1 ⊢; exact ih h1
  | letLhs _ C _ ih | binL _ C _ ih | whileCond C _ ih | matchScrut C _ ih
  | cellSetL C _ ih | applyFn C _ ih =>
    simp only [ctxInDom, ExprCtx.comp, Bool.and_eq_true] at h1 ⊢; exact ⟨ih h1.1, h1.2⟩
  | letRhs _ _ C ih | binR _ _ C ih | whileBody _ C ih | cellSetR _ C ih =>
    simp only [ctxInDom, ExprCtx.comp, Bool.and_eq_true] at h1 ⊢; exact ⟨h1.1, ih h1.2⟩
  | applyArg _ _ C _ ih | applyDirArg _ _ C _ ih | matchArm _ _ _ C _ ih =>
    simp only [ctxInDom, ExprCtx.comp, Bool.and_eq_true] at h1 ⊢
    exact ⟨⟨⟨h1.1.1.1, h1.1.1.2⟩, ih h1.1.2⟩, h1.2⟩
  | ifC C _ _ ih =>
    simp only [ctxInDom, ExprCtx.comp, Bool.and_eq_true] at h1 ⊢
    exact ⟨⟨ih h1.1.1, h1.1.2⟩, h1.2⟩
  | ifT _ C _ ih | tupleElem _ C _ ih | blockElem _ C _ ih | makeDataElem _ _ _ C _ ih
  | concPrimElem _ _ C _ ih =>
    simp only [ctxInDom, ExprCtx.comp, Bool.and_eq_true] at h1 ⊢
    exact ⟨⟨h1.1.1, ih h1.1.2⟩, h1.2⟩
  | ifE _ _ C ih =>
    simp only [ctxInDom, ExprCtx.comp, Bool.and_eq_true] at h1 ⊢
    exact ⟨⟨h1.1.1, h1.1.2⟩, ih h1.2⟩

mutual
private theorem exprInDom_mono {d1 d2 : Ident → Bool} (hsub : ∀ f, d1 f = true → d2 f = true) :
    (e : Expr) → exprInDom d1 e = true → exprInDom d2 e = true
  | .lit _, _ | .var _, _ | .loc _, _ | .taskRef _, _ | .syncRef _ _, _ | .trap _, _ => rfl
  | .lam _ _ _ b, h => exprInDom_mono hsub b h
  | .tuple es, h | .block es, h | .makeData _ _ es, h | .concPrim _ es, h =>
    exprListInDom_mono hsub es h
  | .apply fn args, h => by
    simp only [exprInDom, Bool.and_eq_true] at h ⊢
    exact ⟨exprInDom_mono hsub fn h.1, exprListInDom_mono hsub args h.2⟩
  | .applyDir nm args, h => by
    simp only [exprInDom, Bool.and_eq_true] at h ⊢
    exact ⟨hsub nm h.1, exprListInDom_mono hsub args h.2⟩
  | .bin _ a b, h | .let_ _ a b, h | .while_ a b, h | .cellSet a b, h => by
    simp only [exprInDom, Bool.and_eq_true] at h ⊢
    exact ⟨exprInDom_mono hsub a h.1, exprInDom_mono hsub b h.2⟩
  | .un _ a, h | .getTag a, h | .cellNew a, h | .cellGet a, h | .spawn a, h | .await a, h =>
    exprInDom_mono hsub a h
  | .if_ c t e, h => by
    simp only [exprInDom, Bool.and_eq_true] at h ⊢
    exact ⟨⟨exprInDom_mono hsub c h.1.1, exprInDom_mono hsub t h.1.2⟩, exprInDom_mono hsub e h.2⟩
  | .match_ s arms, h => by
    simp only [exprInDom, Bool.and_eq_true] at h ⊢
    exact ⟨exprInDom_mono hsub s h.1, exprArmsInDom_mono hsub arms h.2⟩
termination_by e => sizeOf e

private theorem exprListInDom_mono {d1 d2 : Ident → Bool} (hsub : ∀ f, d1 f = true → d2 f = true) :
    (es : List Expr) → exprListInDom d1 es = true → exprListInDom d2 es = true
  | [], _ => rfl
  | e :: r, h => by
    simp only [exprListInDom, Bool.and_eq_true] at h ⊢
    exact ⟨exprInDom_mono hsub e h.1, exprListInDom_mono hsub r h.2⟩
termination_by es => sizeOf es

private theorem exprArmsInDom_mono {d1 d2 : Ident → Bool} (hsub : ∀ f, d1 f = true → d2 f = true) :
    (arms : List (Pat × Expr)) → exprArmsInDom d1 arms = true → exprArmsInDom d2 arms = true
  | [], _ => rfl
  | (_, b) :: r, h => by
    simp only [exprArmsInDom, Bool.and_eq_true] at h ⊢
    exact ⟨exprInDom_mono hsub b h.1, exprArmsInDom_mono hsub r h.2⟩
termination_by arms => sizeOf arms
end

theorem ctxInDom_mono {d1 d2 : Ident → Bool} (hsub : ∀ f, d1 f = true → d2 f = true) :
    (C : ExprCtx) → ctxInDom d1 C = true → ctxInDom d2 C = true
  | .hole, _ => rfl
  | .lam _ _ _ C, h | .un _ C, h | .getTag C, h | .cellNew C, h | .cellGet C, h
  | .spawn C, h | .await C, h => ctxInDom_mono hsub C h
  | .letLhs _ C b, h | .binL _ C b, h | .whileCond C b, h | .cellSetL C b, h => by
    simp only [ctxInDom, Bool.and_eq_true] at h ⊢
    exact ⟨ctxInDom_mono hsub C h.1, exprInDom_mono hsub b h.2⟩
  | .letRhs _ a C, h | .binR _ a C, h | .whileBody a C, h | .cellSetR a C, h => by
    simp only [ctxInDom, Bool.and_eq_true] at h ⊢
    exact ⟨exprInDom_mono hsub a h.1, ctxInDom_mono hsub C h.2⟩
  | .applyFn C args, h => by
    simp only [ctxInDom, Bool.and_eq_true] at h ⊢
    exact ⟨ctxInDom_mono hsub C h.1, exprListInDom_mono hsub args h.2⟩
  | .matchScrut C arms, h => by
    simp only [ctxInDom, Bool.and_eq_true] at h ⊢
    exact ⟨ctxInDom_mono hsub C h.1, exprArmsInDom_mono hsub arms h.2⟩
  | .matchArm scrut pre _ C post, h => by
    simp only [ctxInDom, Bool.and_eq_true] at h ⊢
    exact ⟨⟨⟨exprInDom_mono hsub scrut h.1.1.1, exprArmsInDom_mono hsub pre h.1.1.2⟩,
             ctxInDom_mono hsub C h.1.2⟩, exprArmsInDom_mono hsub post h.2⟩
  | .applyArg fn pre C post, h => by
    simp only [ctxInDom, Bool.and_eq_true] at h ⊢
    exact ⟨⟨⟨exprInDom_mono hsub fn h.1.1.1, exprListInDom_mono hsub pre h.1.1.2⟩,
             ctxInDom_mono hsub C h.1.2⟩, exprListInDom_mono hsub post h.2⟩
  | .applyDirArg nm pre C post, h => by
    simp only [ctxInDom, Bool.and_eq_true] at h ⊢
    exact ⟨⟨⟨hsub nm h.1.1.1, exprListInDom_mono hsub pre h.1.1.2⟩,
             ctxInDom_mono hsub C h.1.2⟩, exprListInDom_mono hsub post h.2⟩
  | .ifC C t e2, h => by
    simp only [ctxInDom, Bool.and_eq_true] at h ⊢
    exact ⟨⟨ctxInDom_mono hsub C h.1.1, exprInDom_mono hsub t h.1.2⟩, exprInDom_mono hsub e2 h.2⟩
  | .ifT c C e2, h => by
    simp only [ctxInDom, Bool.and_eq_true] at h ⊢
    exact ⟨⟨exprInDom_mono hsub c h.1.1, ctxInDom_mono hsub C h.1.2⟩, exprInDom_mono hsub e2 h.2⟩
  | .ifE c t C, h => by
    simp only [ctxInDom, Bool.and_eq_true] at h ⊢
    exact ⟨⟨exprInDom_mono hsub c h.1.1, exprInDom_mono hsub t h.1.2⟩, ctxInDom_mono hsub C h.2⟩
  | .tupleElem pre C post, h | .blockElem pre C post, h | .makeDataElem _ _ pre C post, h
  | .concPrimElem _ pre C post, h => by
    simp only [ctxInDom, Bool.and_eq_true] at h ⊢
    exact ⟨⟨exprListInDom_mono hsub pre h.1.1, ctxInDom_mono hsub C h.1.2⟩, exprListInDom_mono hsub post h.2⟩

/-- Positive syntactic completeness witness: `ExprCtx` embeds holes inside `match_` (scrutinee & arms),
    `while_`, `getTag`, `spawn`, `await`, and `concPrim`, as well as `.lam`. -/
theorem matchContext_exists : ∃ C : ExprCtx, C.fill (.lit .unit) = .match_ (.lit .unit) [] :=
  ⟨.matchScrut .hole [], rfl⟩

theorem isGroundValue_exprInDom (dom : Ident → Bool) {v : Expr} (hg : IsGroundValue v) :
    exprInDom dom v = true := by
  induction hg with
  | lit _ => rfl
  | tuple _ ih => exact exprListInDom_iff.mpr ih
  | makeData _ _ _ ih => exact exprListInDom_iff.mpr ih

/-- **Interface-Scoped Higher-Order Contextual Equivalence (`ScopedCtxObsEquiv`)**:
    Restricts observing contexts `C : ExprCtx` to the program's external/public function interface
    `pubFns : Ident → Bool` (`ctxInDom pubFns C = true`), preventing external contexts from
    directly naming newly synthesized compiler-internal `$flat$` / `$spec$` entries while allowing
    full higher-order closure observation, heap-cell storage, and multi-pass `Φ0 ↦ Φ1 ↦ Φ2` transitivity! -/
def ScopedCtxObsEquiv (pubFns : Ident → Bool) (Γ : List Ident) (Δ : AdtEnv)
    (Φ1 Φ2 : FunEnv) (e1 e2 : Expr) : Prop :=
  (∀ z ∈ freeVars e1, z ∈ Γ) ∧
  (∀ z ∈ freeVars e2, z ∈ Γ) ∧
  ∀ (C : ExprCtx) (σ : Store) (out : Expr),
    CtxCloses Γ C →
    ctxInDom pubFns C = true →
    ClosedStore σ →
    (∀ v ∈ σ, IsGroundValue v) →
    IsGroundOutcome out →
    ((∃ σ', Steps Δ Φ1 (C.fill e1) σ out σ') ↔
     (∃ σ', Steps Δ Φ2 (C.fill e2) σ out σ'))

theorem ScopedCtxObsEquiv.refl {pubFns : Ident → Bool} {Γ : List Ident} {Δ : AdtEnv}
    {Φ : FunEnv} {e : Expr} (hΓ : ∀ z ∈ freeVars e, z ∈ Γ) :
    ScopedCtxObsEquiv pubFns Γ Δ Φ Φ e e :=
  ⟨hΓ, hΓ, fun _ _ _ _ _ _ _ _ => Iff.rfl⟩

theorem ScopedCtxObsEquiv.symm {pubFns : Ident → Bool} {Γ : List Ident} {Δ : AdtEnv}
    {Φ1 Φ2 : FunEnv} {e1 e2 : Expr}
    (h : ScopedCtxObsEquiv pubFns Γ Δ Φ1 Φ2 e1 e2) :
    ScopedCtxObsEquiv pubFns Γ Δ Φ2 Φ1 e2 e1 :=
  ⟨h.2.1, h.1, fun C σ out hcl hdom hσ hσg hout => (h.2.2 C σ out hcl hdom hσ hσg hout).symm⟩

theorem ScopedCtxObsEquiv.trans {pubFns : Ident → Bool} {Γ : List Ident} {Δ : AdtEnv}
    {Φ1 Φ2 Φ3 : FunEnv} {e1 e2 e3 : Expr}
    (h12 : ScopedCtxObsEquiv pubFns Γ Δ Φ1 Φ2 e1 e2)
    (h23 : ScopedCtxObsEquiv pubFns Γ Δ Φ2 Φ3 e2 e3) :
    ScopedCtxObsEquiv pubFns Γ Δ Φ1 Φ3 e1 e3 :=
  ⟨h12.1, h23.2.1, fun C σ out hcl hdom hσ hσg hout =>
    (h12.2.2 C σ out hcl hdom hσ hσg hout).trans (h23.2.2 C σ out hcl hdom hσ hσg hout)⟩

theorem ScopedCtxObsEquiv.congr_lam {pubFns : Ident → Bool} {Γ : List Ident} {Δ : AdtEnv}
    {Φ1 Φ2 : FunEnv} (m : Mode) (ps : List (Ident × Ty)) (ret : Ty) {b1 b2 : Expr}
    (hb : ScopedCtxObsEquiv pubFns (ps.map Prod.fst ++ Γ) Δ Φ1 Φ2 b1 b2) :
    ScopedCtxObsEquiv pubFns Γ Δ Φ1 Φ2 (.lam m ps ret b1) (.lam m ps ret b2) := by
  have hlam_fv : ∀ b : Expr, (∀ z ∈ freeVars b, z ∈ ps.map Prod.fst ++ Γ) →
      ∀ z ∈ freeVars (.lam m ps ret b), z ∈ Γ := by
    intro b hsub z hz
    simp only [freeVars, List.mem_filter, Bool.not_eq_true'] at hz
    rcases List.mem_append.mp (hsub z hz.1) with hps | hΓ
    · rcases List.mem_map.mp hps with ⟨p, hp, rfl⟩
      have hany : ps.any (fun q => q.1 == p.1) = true :=
        List.any_eq_true.mpr ⟨p, hp, beq_self_eq_true _⟩
      rw [hany] at hz; cases hz.2
    · exact hΓ
  refine ⟨hlam_fv b1 hb.1, hlam_fv b2 hb.2.1, ?_⟩
  intro C σ out hcl hdom hσ hσg hout
  have hcl' : CtxCloses (ps.map Prod.fst ++ Γ) (C.comp (.lam m ps ret .hole)) := by
    intro b hsub; rw [ExprCtx.comp_fill]; exact hcl (.lam m ps ret b) (hlam_fv b hsub)
  have hdom' : ctxInDom pubFns (C.comp (.lam m ps ret .hole)) = true :=
    ctxInDom_comp C (.lam m ps ret .hole) hdom rfl
  simpa [ExprCtx.comp_fill, ExprCtx.fill] using hb.2.2 (C.comp (.lam m ps ret .hole)) σ out hcl' hdom' hσ hσg hout

theorem ScopedCtxObsEquiv.congr_ctx {pubFns : Ident → Bool} {ΓInner ΓOuter : List Ident}
    {Δ : AdtEnv} {Φ1 Φ2 : FunEnv} (C0 : ExprCtx) (hC0dom : ctxInDom pubFns C0 = true)
    (hscope : ∀ e : Expr, (∀ z ∈ freeVars e, z ∈ ΓInner) → ∀ z ∈ freeVars (C0.fill e), z ∈ ΓOuter)
    {e1 e2 : Expr} (he : ScopedCtxObsEquiv pubFns ΓInner Δ Φ1 Φ2 e1 e2) :
    ScopedCtxObsEquiv pubFns ΓOuter Δ Φ1 Φ2 (C0.fill e1) (C0.fill e2) := by
  refine ⟨hscope e1 he.1, hscope e2 he.2.1, ?_⟩
  intro C σ out hcl hdom hσ hσg hout
  have hcl' : CtxCloses ΓInner (C.comp C0) := by
    intro e hsub; rw [ExprCtx.comp_fill]; exact hcl (C0.fill e) (hscope e hsub)
  have hdom' : ctxInDom pubFns (C.comp C0) = true := ctxInDom_comp C C0 hdom hC0dom
  simpa [ExprCtx.comp_fill] using he.2.2 (C.comp C0) σ out hcl' hdom' hσ hσg hout

theorem scopedCtxObsEquiv_of_ctxObsEquiv {pubFns : Ident → Bool} {Γ : List Ident}
    {Δ : AdtEnv} {Φ1 Φ2 : FunEnv} {e1 e2 : Expr}
    (h : CtxObsEquiv Γ Δ Φ1 Φ2 e1 e2) :
    ScopedCtxObsEquiv pubFns Γ Δ Φ1 Φ2 e1 e2 :=
  ⟨h.1, h.2.1, fun C σ out hcl _ hσ hσg hout => h.2.2 C σ out hcl hσ hσg hout⟩

/-- **Private Function-Table Extension Unobservability (`scopedCtxObsEquiv_extend_private_funEnv`)**:
    Extending `Φ1 ↦ Φ2` with private compiler-generated `$flat$` / `$spec$` entries outside `dom`
    (where `pubFns ⊆ dom`) is completely unobservable (`ScopedCtxObsEquiv pubFns Γ Δ Φ1 Φ2 e e`)
    for every open expression `e` in `dom`! -/
theorem scopedCtxObsEquiv_extend_private_funEnv {pubFns dom : Ident → Bool} {Γ : List Ident}
    {Δ : AdtEnv} {Φ1 Φ2 : FunEnv} {e : Expr}
    (hagree : FunEnvAgreesOn dom Φ1 Φ2) (hΦ1dom : ClosedDomEnv dom Φ1)
    (hpub : ∀ f, pubFns f = true → dom f = true)
    (hΓ : ∀ z ∈ freeVars e, z ∈ Γ) (heDom : exprInDom dom e = true) :
    ScopedCtxObsEquiv pubFns Γ Δ Φ1 Φ2 e e := by
  refine ⟨hΓ, hΓ, ?_⟩
  intro C σ out _ hCpub _ hσg _
  have hCdom : ctxInDom dom C = true := ctxInDom_mono hpub C hCpub
  have hfillDom : exprInDom dom (C.fill e) = true := ctxInDom_fill C hCdom heDom
  have hσDom : StoreInDom dom σ := fun v hv => isGroundValue_exprInDom dom (hσg v hv)
  constructor
  · rintro ⟨σ', hs⟩
    exact ⟨σ', (steps_funEnv_agree_iff hagree hΦ1dom hσDom hfillDom).mp hs⟩
  · rintro ⟨σ', hs⟩
    exact ⟨σ', (steps_funEnv_agree_iff hagree hΦ1dom hσDom hfillDom).mpr hs⟩

/-- **Resolution of `PublicNames.lean` (`private_entry_unobservable_scoped`)**:
    Adding a generated callable `"$spec$a"` to an empty `FunEnv` — which broke unrestricted
    `CtxObsEquiv` because an unrestricted context could call `.applyDir "$spec$a" []` —
    satisfies `ScopedCtxObsEquiv (fun _ => false)` with zero public symbols! -/
theorem private_entry_unobservable_scoped :
    let emptyΦ : FunEnv := fun _ => none
    let extendedΦ : FunEnv := fun n =>
      if n == "$spec$a" then some { name := n, params := [], retTy := .void, body := .lit .unit } else none
    ScopedCtxObsEquiv (fun _ => false) [] (fun _ => none) emptyΦ extendedΦ (.lit .unit) (.lit .unit) := by
  exact scopedCtxObsEquiv_extend_private_funEnv (dom := fun _ => false)
    (fun _ h => by cases h)
    (fun _ _ h => by cases h)
    (fun _ h => h)
    (fun _ h => by simp [freeVars] at h)
    rfl

/-- **Composing Private `$flat$/$spec$` Table Extension With Higher-Order Dead-`let` Elimination
    (`pureLetDrop_after_private_extend_scopedCtxObsEquiv`)**:
    Chains `Φ0 ↦ Φ1` (adding private `$flat$/$spec$` entries) with `PureLetDropEnv Φ1 Φ2`
    (eliminating dead pure/closure `let` bindings inside functions and returned closures)! -/
theorem pureLetDrop_after_private_extend_scopedCtxObsEquiv {pubFns dom : Ident → Bool}
    {Γ : List Ident} {Δ : AdtEnv} {Φ0 Φ1 Φ2 : FunEnv} {e1 e2 : Expr}
    (hagree01 : FunEnvAgreesOn dom Φ0 Φ1) (hΦ0dom : ClosedDomEnv dom Φ0)
    (hpub : ∀ f, pubFns f = true → dom f = true)
    (hΦ12 : PureLetDropEnv Φ1 Φ2) (hΦ1cl : ClosedFunEnv Φ1)
    (hΓ1 : ∀ z ∈ freeVars e1, z ∈ Γ) (he1Dom : exprInDom dom e1 = true)
    (hr : PureLetDropRel e1 e2) :
    ScopedCtxObsEquiv pubFns Γ Δ Φ0 Φ2 e1 e2 :=
  ScopedCtxObsEquiv.trans
    (scopedCtxObsEquiv_extend_private_funEnv hagree01 hΦ0dom hpub hΓ1 he1Dom)
    (scopedCtxObsEquiv_of_ctxObsEquiv (pureLetDrop_implies_ctxObsEquiv hΦ12 hΦ1cl hΓ1 hr))

/-- **Main Positional Multi-Callback `$spec$` Soundness With Fresh-Renamed Parameters,
    `TmMakeCls` Body Wrappers & Multi-Argument Callback Inlining (`positional_hof_loop_spec_optBody_obsEquiv`)**:
    Composes `positional_hof_loop_spec_obsEquiv` + `recFunBody_obsEquiv_congr` + `AlphaOptRel`
    + `steps_funEnv_agree_iff` so `Φ2` contains **only** the real emitted `$spec$` function
    with fresh-renamed state/capture parameters, cloned `match` binders, optional `TmMakeCls`
    body wrappers, and N-ary direct `TmVar` / `let` callback inlining! -/
theorem positional_hof_loop_spec_optBody_obsEquiv {Δ : AdtEnv} {Φ1 Φ2 Φ_raw Φ_aux : FunEnv}
    (S : PositionalLoopSpec Δ Φ_raw)
    {dom2 : Ident → Bool}
    {specParamsFresh : List (Ident × Ty)} {specRet : Ty} {rawSpecBody specOptBody : Expr}
    (hagree1 : FunEnvAgreesOn S.dom Φ1 Φ_raw)
    (hΦ1dom : ClosedDomEnv S.dom Φ1)
    (horigDom : S.dom S.origFn = true)
    (hΦaux_cl : ClosedFunEnv Φ_aux)
    (hraw_fd : Φ_raw S.specFn = some {
      name := S.specFn, params := posSpecParams S.slots, retTy := specRet, body := rawSpecBody })
    (haux_fd : Φ_aux S.specFn = some {
      name := S.specFn, params := specParamsFresh, retTy := specRet, body := specOptBody })
    (hraw_aux_other : ∀ g, g ≠ S.specFn → Φ_raw g = Φ_aux g)
    (hfr_len : specParamsFresh.length = (posSpecParams S.slots).length)
    (hfr_nodup : (specParamsFresh.map Prod.fst).Nodup)
    (hraw_fv : ∀ z ∈ freeVars rawSpecBody, z ∈ (posSpecParams S.slots).map Prod.fst)
    (hrel_raw : AlphaOptRel Φ_raw
      (((posSpecParams S.slots).map Prod.fst).zip (specParamsFresh.map Prod.fst)) rawSpecBody specOptBody)
    (hrel_aux : AlphaOptRel Φ_aux
      (((posSpecParams S.slots).map Prod.fst).zip (specParamsFresh.map Prod.fst)) rawSpecBody specOptBody)
    (hagree2 : FunEnvAgreesOn dom2 Φ2 Φ_aux)
    (hΦ2dom : ClosedDomEnv dom2 Φ2)
    (hspecDom2 : dom2 S.specFn = true)
    {initArgs1 initArgs2 : List Expr} {σ σ' : Store} {out : Expr}
    (hσCl : ClosedStore σ) (hσDom1 : StoreInDom S.dom σ) (hσDom2 : StoreInDom dom2 σ)
    (hout : IsTerminal out)
    (hinitRel : PosCallArgsRel S.origFn S.specFn S.slots S.slots initArgs1 initArgs2)
    (hargs1Cl : ∀ e ∈ initArgs1, freeVars e = [])
    (hargs1Dom : ∀ e ∈ initArgs1, exprInDom S.dom e = true)
    (hargs2Cl : ∀ e ∈ initArgs2, freeVars e = [])
    (hargs2Dom2 : ∀ e ∈ initArgs2, exprInDom dom2 e = true) :
    Steps Δ Φ1 (.applyDir S.origFn initArgs1) σ out σ' ↔
      Steps Δ Φ2 (.applyDir S.specFn initArgs2) σ out σ' := by
  have hstep1 := positional_hof_loop_spec_obsEquiv S (σ' := σ') hagree1 hΦ1dom horigDom hσCl hσDom1 hout
    hinitRel hargs1Cl hargs1Dom
  have he2Cl : freeVars (.applyDir S.specFn initArgs2) = [] := by
    simp [freeVars, freeVarsList_eq_nil_iff.mpr hargs2Cl]
  have he2Dom2 : exprInDom dom2 (.applyDir S.specFn initArgs2) = true := by
    simp only [exprInDom, Bool.and_eq_true]
    exact ⟨hspecDom2, exprListInDom_iff.mpr hargs2Dom2⟩
  have henv_rel : ∀ vs, (∀ v ∈ vs, IsValue v) → (∀ v ∈ vs, freeVars v = []) →
      vs.length = (posSpecParams S.slots).length →
      AlphaEnvRel (((posSpecParams S.slots).map Prod.fst).zip (specParamsFresh.map Prod.fst))
        (zipParams (posSpecParams S.slots) vs) (zipParams specParamsFresh vs) (freeVars rawSpecBody) := by
    intro vs hvs hcl hvlen
    refine ⟨?_, ?_, ?_⟩
    · intro p hp; unfold zipParams at hp
      exact ⟨hvs p.2 (mem_snd_of_mem_zip hp), hcl p.2 (mem_snd_of_mem_zip hp)⟩
    · intro p hp; unfold zipParams at hp
      exact ⟨hvs p.2 (mem_snd_of_mem_zip hp), hcl p.2 (mem_snd_of_mem_zip hp)⟩
    · intro z hz
      rcases List.mem_iff_getElem.mp (hraw_fv z hz) with ⟨i, hi, rfl⟩
      have hi_v : i < vs.length := by simp at hi; omega
      have hi_f : i < (specParamsFresh.map Prod.fst).length := by simp at hi ⊢; omega
      have hlu1 := lookupSubstEnv_nodup_zip (vs := vs) S.hSpecNodup (by simp [hvlen]) i hi
      have hlu2 := lookupSubstEnv_nodup_zip (vs := vs) hfr_nodup (by simp [hvlen, hfr_len]) i hi_f
      have hren := lookupRename_nodup_zip S.hSpecNodup (ys := specParamsFresh.map Prod.fst)
        (by simp [hfr_len]) [] i hi
      simp only [List.append_nil] at hren
      exact ⟨vs[i], by unfold zipParams; exact hlu1, by rw [hren]; unfold zipParams; exact hlu2⟩
  have hstep2 := recFunBody_obsEquiv_congr (σ' := σ') S.hΦcl hΦaux_cl hraw_fd haux_fd hraw_aux_other hfr_len.symm
    (fun vs hvs hcl hvlen => alphaOptRel_subst_closedObsEquiv Δ S.hΦcl hrel_raw (henv_rel vs hvs hcl hvlen))
    (fun vs hvs hcl hvlen => alphaOptRel_subst_closedObsEquiv Δ hΦaux_cl hrel_aux (henv_rel vs hvs hcl hvlen))
    hσCl he2Cl hout
  have hstep3 := steps_funEnv_agree_iff (Δ := Δ) hagree2 hΦ2dom hσDom2 he2Dom2 (σ' := σ') (out := out)
  exact hstep1.trans (hstep2.trans hstep3.symm)

/-! #### Exact Real-Artifact Theorem 2: `specLoopColl` (`before.gs`) -> `specLoopColl$spec$19` (`after.gs`) & `TmMakeCls`-in-Body Wrapper -/

/-- Verbatim parsed `specLoopColl` `FunDef` from `before.gs` (constant callback argument `2`, parameter `fv0_0_q`). -/
def beforeSpecLoopCollFd : FunDef := {
  name := "specLoopColl",
  params := [("n", .int), ("f", .fn .local [.int] .int), ("fv0_0_q", .int)],
  retTy := .int,
  body := .if_ (.bin .leInt (.var "n") (.lit (.int 0)))
    (.var "fv0_0_q")
    (.applyDir "specLoopColl"
      [.bin .sub (.var "n") (.lit (.int 1)),
       .var "f",
       .bin .add (.var "fv0_0_q") (.apply (.var "f") [.lit (.int 2)])])
}

/-- Verbatim parsed `specLoopColl$spec$19` `FunDef` from `after.gs` (`$co$20$n`, `$co$22$q`, `$co$25$fv0_0_q`, `$co$26$z`). -/
def afterSpecLoopCollSpec19Fd : FunDef := {
  name := "specLoopColl$spec$19",
  params := [("$co$20$n", .int), ("$co$22$q", .int), ("$co$25$fv0_0_q", .int)],
  retTy := .int,
  body := .if_ (.bin .leInt (.var "$co$20$n") (.lit (.int 0)))
    (.var "$co$25$fv0_0_q")
    (.applyDir "specLoopColl$spec$19"
      [.bin .sub (.var "$co$20$n") (.lit (.int 1)),
       .var "$co$22$q",
       .bin .add (.var "$co$25$fv0_0_q")
         (.let_ "$co$26$z" (.lit (.int 2))
           (.bin .mul (.var "$co$26$z") (.var "$co$22$q")))])
}

/-- Verbatim pre-`coOptTerm` `placeholderFd` (`src/core.gsa:6820,7129-7153`, `placeholder.gs:16`):
    reconstructs `let $co$21$f = lam shared (($co$24$z: int)) int ($co$24$z * $co$22$q)` INSIDE
    `specLoopColl$spec$19`'s body while the recursive branch STILL calls `$co$21$f(2)` prior to `coOptTerm`! -/
def placeholderSpecLoopCollSpec19Fd : FunDef := {
  name := "specLoopColl$spec$19",
  params := [("$co$20$n", .int), ("$co$22$q", .int), ("$co$25$fv0_0_q", .int)],
  retTy := .int,
  body := .let_ "$co$21$f"
    (.lam .shared [("$co$24$z", .int)] .int (.bin .mul (.var "$co$24$z") (.var "$co$22$q")))
    (.if_ (.bin .leInt (.var "$co$20$n") (.lit (.int 0)))
      (.var "$co$25$fv0_0_q")
      (.applyDir "specLoopColl$spec$19"
        [.bin .sub (.var "$co$20$n") (.lit (.int 1)),
         .var "$co$22$q",
         .bin .add (.var "$co$25$fv0_0_q") (.apply (.var "$co$21$f") [.lit (.int 2)])]))
}

def specLoopCollCbSlot (qVal : Expr) : CbSlotSpec := {
  fParam := "f", fnTy := .fn .local [.int] .int, cbMode := .shared,
  cbParams := [("z", .int)], cbRet := .int,
  cbBody := .bin .mul (.var "z") (.var "q"),
  fvs := [("q", .int)], fvVals := [qVal],
  lowering := .inline1 "$co$26$z"
}

/-- **Exact Real-Artifact Theorem 2a (`exact_artifact_specLoopColl_spec19_obsEquiv`)**:
    Connects verbatim `before.gs` `specLoopColl` to verbatim `after.gs` `specLoopColl$spec$19`
    (including fresh-renamed state parameters `$co$20$n`, `$co$25$fv0_0_q`, capture `$co$22$q`,
    constant callback argument `2`, and inlined `$co$26$z`) across all `n, q, acc : Int32`! -/
theorem exact_artifact_specLoopColl_spec19_obsEquiv (n q acc : Int32)
    {σ σ' : Store} {out : Expr} (hσCl : ClosedStore σ)
    (hσDom : StoreInDom (fun nm => nm == "specLoopColl") σ)
    (hout : IsTerminal out) :
    let cb := specLoopCollCbSlot (.lit (.int q))
    let Φ1 : FunEnv := fun nm =>
      if nm == "specLoopColl" then some beforeSpecLoopCollFd else none
    let Φ2 : FunEnv := fun nm =>
      if nm == "specLoopColl" then some beforeSpecLoopCollFd
      else if nm == "specLoopColl$spec$19" then some afterSpecLoopCollSpec19Fd
      else none
    Steps (fun _ => none) Φ1 (.applyDir "specLoopColl" [.lit (.int n), cb.cls, .lit (.int acc)]) σ out σ' ↔
      Steps (fun _ => none) Φ2 (.applyDir "specLoopColl$spec$19" [.lit (.int n), .lit (.int q), .lit (.int acc)]) σ out σ' := by
  let cb := specLoopCollCbSlot (.lit (.int q))
  let slots : List PosSpecSlot := [.state ("n", .int), .callback cb, .state ("fv0_0_q", .int)]
  let rawBody : Expr :=
    .if_ (.bin .leInt (.var "n") (.lit (.int 0)))
      (.var "fv0_0_q")
      (.applyDir "specLoopColl$spec$19"
        [.bin .sub (.var "n") (.lit (.int 1)),
         .var "q",
         .bin .add (.var "fv0_0_q")
           (.let_ "$co$26$z" (.lit (.int 2)) (.bin .mul (.var "$co$26$z") (.var "q")))])
  let Φ1 : FunEnv := fun nm =>
    if nm == "specLoopColl" then some beforeSpecLoopCollFd else none
  let Φ2 : FunEnv := fun nm =>
    if nm == "specLoopColl" then some beforeSpecLoopCollFd
    else if nm == "specLoopColl$spec$19" then some afterSpecLoopCollSpec19Fd
    else none
  let Φ_raw : FunEnv := fun nm =>
    if nm == "specLoopColl" then some beforeSpecLoopCollFd
    else if nm == "specLoopColl$spec$19" then
      some { name := "specLoopColl$spec$19", params := [("n", .int), ("q", .int), ("fv0_0_q", .int)],
             retTy := .int, body := rawBody }
    else none
  have hΦraw_cl : ClosedFunEnv Φ_raw := by
    intro nm fd hlu; dsimp only [Φ_raw] at hlu
    split at hlu
    · injection hlu with hlu; subst hlu; decide
    · split at hlu
      · injection hlu with hlu; subst hlu; decide
      · cases hlu
  have hΦ2_cl : ClosedFunEnv Φ2 := by
    intro nm fd hlu; dsimp only [Φ2] at hlu
    split at hlu
    · injection hlu with hlu; subst hlu; decide
    · split at hlu
      · injection hlu with hlu; subst hlu; decide
      · cases hlu
  have hcbWf : CbSlotWF (fun nm => nm == "specLoopColl") Φ_raw cb := by
    refine ⟨?_, ?_, ?_, rfl, ?_, ?_, rfl, ⟨"z", .int, rfl, ?_, rfl⟩⟩
    · intro v hv; simp [cb, specLoopCollCbSlot] at hv; subst hv; exact .lit _
    · intro v hv; simp [cb, specLoopCollCbSlot] at hv; subst hv; rfl
    · intro v hv; simp [cb, specLoopCollCbSlot] at hv; subst hv; rfl
    · dsimp only [cb, specLoopCollCbSlot]; decide
    · dsimp only [cb, specLoopCollCbSlot]; decide
    · dsimp only [cb, specLoopCollCbSlot]; decide
  let S : PositionalLoopSpec (fun _ => none) Φ_raw := {
    origFn := "specLoopColl",
    specFn := "specLoopColl$spec$19",
    slots := slots,
    loopRet := .int,
    loopBody := beforeSpecLoopCollFd.body,
    dom := fun nm => nm == "specLoopColl",
    hΦcl := hΦraw_cl,
    hLoop := rfl,
    hSpec := rfl,
    hcbs := fun c hc => by simp [slots, cbSlotsOf] at hc; subst hc; exact hcbWf,
    hOrigNodup := by dsimp only [slots, cb, specLoopCollCbSlot, posOrigParams]; decide,
    hSpecNodup := by dsimp only [slots, cb, specLoopCollCbSlot, posSpecParams]; decide,
    hinlDisjSpec := by
      intro c hc inlP hlow; simp [slots, cbSlotsOf] at hc; subst hc
      simp [cb, specLoopCollCbSlot] at hlow; subst hlow
      dsimp only [slots, cb, specLoopCollCbSlot, posSpecParams]; decide,
    hLoopNoFv := by dsimp only [slots, cb, specLoopCollCbSlot, allCbFvNames, cbSlotsOf, beforeSpecLoopCollFd]; decide,
    hEligible := .if_
      (.bin (.var rfl) (.lit _))
      (.var rfl)
      (.selfCall (.state ("n", .int) (.bin (.var rfl) (.lit _))
        (.callback cb
          (.state ("fv0_0_q", .int)
            (.bin (.var rfl) (.cbCallInline1 rfl rfl rfl (.lit _)))
            .nil))))
  }
  exact positional_hof_loop_spec_optBody_obsEquiv S
    (dom2 := fun nm => nm == "specLoopColl" || nm == "specLoopColl$spec$19")
    (Φ_aux := Φ2)
    (fun nm h => by have heq := eq_of_beq h; subst heq; rfl)
    (fun nm fd h1 hlu => by have heq := eq_of_beq h1; subst heq; simp at hlu; subst hlu; rfl)
    rfl hΦ2_cl rfl rfl
    (fun g hg => by
      have hne : (g == "specLoopColl$spec$19") = false := beq_false_of_ne hg
      simp only [Φ_raw, Φ2, hne, Bool.false_eq_true, ↓reduceIte])
    rfl (by decide)
    (by dsimp only [S, slots, cb, specLoopCollCbSlot, posSpecParams, rawBody]; decide)
    (checkAlphaOpt_sound Φ_raw [("n", "$co$20$n"), ("q", "$co$22$q"), ("fv0_0_q", "$co$25$fv0_0_q")]
      rawBody afterSpecLoopCollSpec19Fd.body (by decide))
    (checkAlphaOpt_sound Φ2 [("n", "$co$20$n"), ("q", "$co$22$q"), ("fv0_0_q", "$co$25$fv0_0_q")]
      rawBody afterSpecLoopCollSpec19Fd.body (by decide))
    (fun _ _ => rfl)
    (fun nm fd _ hlu => by
      dsimp only [Φ2] at hlu
      split at hlu
      · injection hlu with hlu; subst hlu; decide
      · split at hlu
        · injection hlu with hlu; subst hlu; decide
        · cases hlu)
    rfl hσCl hσDom (fun v hv => exprInDom_mono (fun f hf => by simp [hf]) v (hσDom v hv)) hout
    (.state ("n", .int) (.lit _) (.callback cb (.state ("fv0_0_q", .int) (.lit _) .nil)))
    (fun e he => by simp at he; rcases he with rfl | rfl | rfl <;> rfl)
    (fun e he => by simp at he; rcases he with rfl | rfl | rfl <;> rfl)
    (fun e he => by simp at he; rcases he with rfl | rfl | rfl <;> rfl)
    (fun e he => by simp at he; rcases he with rfl | rfl | rfl <;> rfl)

theorem if_else_obsEquiv_congr {Δ : AdtEnv} {Φ : FunEnv} (c t : Expr) {e1 e2 : Expr}
    (he : ObsEquiv Δ Φ Φ e1 e2) :
    ObsEquiv Δ Φ Φ (.if_ c t e1) (.if_ c t e2) := by
  intro σ σ' out hout
  rw [activeCtx_steps_terminal_iff (isActiveCtx_ifCond Δ t e1) hout,
      activeCtx_steps_terminal_iff (isActiveCtx_ifCond Δ t e2) hout]
  constructor
  · rintro (⟨tr, rfl, htr⟩ | ⟨vc, sm, hvc, hsc, hk⟩)
    · exact Or.inl ⟨tr, rfl, htr⟩
    · refine Or.inr ⟨vc, sm, hvc, hsc, ?_⟩
      cases hk with
      | refl => cases hout with | inl hv => cases hv | inr h => rcases h with ⟨_, h⟩; cases h
      | trans hs hrest =>
        cases hs with
        | ifStep hs_vc => exact False.elim (isValue_no_step hvc hs_vc)
        | ifTrap => cases hvc
        | ifTrue => exact .trans .ifTrue hrest
        | ifFalse => exact .trans .ifFalse ((he sm σ' out hout).mp hrest)
  · rintro (⟨tr, rfl, htr⟩ | ⟨vc, sm, hvc, hsc, hk⟩)
    · exact Or.inl ⟨tr, rfl, htr⟩
    · refine Or.inr ⟨vc, sm, hvc, hsc, ?_⟩
      cases hk with
      | refl => cases hout with | inl hv => cases hv | inr h => rcases h with ⟨_, h⟩; cases h
      | trans hs hrest =>
        cases hs with
        | ifStep hs_vc => exact False.elim (isValue_no_step hvc hs_vc)
        | ifTrap => cases hvc
        | ifTrue => exact .trans .ifTrue hrest
        | ifFalse => exact .trans .ifFalse ((he sm σ' out hout).mpr hrest)

/-- **General In-Body Closure Reconstruction + Call-Site Inlining + Dead-Wrapper Elimination
    (`inline1_reconstructed_cls_let_obsEquiv`, `src/core.gsa:6820,7129-7153`)**:
    Proves that reconstructing `let f = lam m [(p, pTy)] ret cbBody` around an expression `E[f(vArg)]`
    that still calls `f(vArg)`, inlining that known-closure call to `let inlP = vArg; cbBody[p := inlP]`,
    and eliminating the now-unused `let f = lam ...` wrapper preserves exact `ObsEquiv`! -/
theorem inline1_reconstructed_cls_let_obsEquiv {Δ : AdtEnv} {Φ : FunEnv}
    (f : Ident) (m : Mode) (p : Ident) (pTy ret : Ty) (cbBody : Expr)
    (inlP : Ident) {vArg : Expr} (hvArg : IsValue vArg)
    (hfresh : SafeFreshFor inlP cbBody)
    (E : Expr → Expr)
    (hcongr : ∀ a b, ObsEquiv Δ Φ Φ a b → ObsEquiv Δ Φ Φ (E a) (E b))
    (hsub : subst f (.lam m [(p, pTy)] ret cbBody) (E (.apply (.var f) [vArg])) =
            E (.apply (.lam m [(p, pTy)] ret cbBody) [vArg])) :
    ObsEquiv Δ Φ Φ
      (E (.let_ inlP vArg (subst p (.var inlP) cbBody)))
      (.let_ f (.lam m [(p, pTy)] ret cbBody) (E (.apply (.var f) [vArg]))) := by
  have hletCls : ObsEquiv Δ Φ Φ
      (.let_ f (.lam m [(p, pTy)] ret cbBody) (E (.apply (.var f) [vArg])))
      (E (.apply (.lam m [(p, pTy)] ret cbBody) [vArg])) := by
    rw [← hsub]
    exact obsEquiv_of_det_step (fun _ => .letVal (.lam _ _ _ _))
  have hbeta : ObsEquiv Δ Φ Φ
      (.apply (.lam m [(p, pTy)] ret cbBody) [vArg])
      (subst p vArg cbBody) :=
    obsEquiv_of_det_step (fun _ => .applyBeta (fun v hv => by simp at hv; subst hv; exact hvArg) rfl)
  have hinl : ObsEquiv Δ Φ Φ
      (.let_ inlP vArg (subst p (.var inlP) cbBody))
      (subst p vArg cbBody) := by
    rw [← subst_fresh_var_cancel (w := vArg) cbBody hfresh]
    exact obsEquiv_of_det_step (fun _ => .letVal hvArg)
  exact ObsEquiv.trans (hcongr _ _ hinl) (ObsEquiv.symm (ObsEquiv.trans hletCls (hcongr _ _ hbeta)))

/-- **Exact Real-Artifact Theorem 2b (`specFn_body_makeCls_wrapper_obsEquiv`)**:
    Proves that the **verbatim pre-`coOptTerm` placeholder `FunDef`** (`placeholderSpecLoopCollSpec19Fd`,
    parsed from `placeholder.gs:16`, where `let $co$21$f = lam shared (($co$24$z: int)) ...` is
    reconstructed inside `specLoopColl$spec$19` and STILL called as `$co$21$f(2)` in the recursive
    branch before `coOptTerm` inlines `$co$21$f(2)` and drops the dead wrapper) is observationally
    equivalent to both `afterSpecLoopCollSpec19Fd` and original `beforeSpecLoopCollFd` across all iterations! -/
theorem specFn_body_makeCls_wrapper_obsEquiv (n q acc : Int32)
    {σ σ' : Store} {out : Expr} (hσCl : ClosedStore σ)
    (hσDom : StoreInDom (fun nm => nm == "specLoopColl") σ)
    (hout : IsTerminal out) :
    let cb := specLoopCollCbSlot (.lit (.int q))
    let Φ1 : FunEnv := fun nm =>
      if nm == "specLoopColl" then some beforeSpecLoopCollFd else none
    let Φ_wrap : FunEnv := fun nm =>
      if nm == "specLoopColl$spec$19" then some placeholderSpecLoopCollSpec19Fd
      else if nm == "specLoopColl" then some beforeSpecLoopCollFd
      else none
    Steps (fun _ => none) Φ1 (.applyDir "specLoopColl" [.lit (.int n), cb.cls, .lit (.int acc)]) σ out σ' ↔
      Steps (fun _ => none) Φ_wrap (.applyDir "specLoopColl$spec$19" [.lit (.int n), .lit (.int q), .lit (.int acc)]) σ out σ' := by
  have hpost := exact_artifact_specLoopColl_spec19_obsEquiv n q acc hσCl hσDom hout (σ' := σ')
  refine hpost.trans ?_
  let Φ2 : FunEnv := fun nm =>
    if nm == "specLoopColl" then some beforeSpecLoopCollFd
    else if nm == "specLoopColl$spec$19" then some afterSpecLoopCollSpec19Fd
    else none
  let Φ_wrap : FunEnv := fun nm =>
    if nm == "specLoopColl$spec$19" then some placeholderSpecLoopCollSpec19Fd
    else if nm == "specLoopColl" then some beforeSpecLoopCollFd
    else none
  have hΦ2_cl : ClosedFunEnv Φ2 := by
    intro nm fd hlu; dsimp only [Φ2] at hlu
    split at hlu
    · injection hlu with hlu; subst hlu; decide
    · split at hlu
      · injection hlu with hlu; subst hlu; decide
      · cases hlu
  have hΦw_cl : ClosedFunEnv Φ_wrap := by
    intro nm fd hlu; dsimp only [Φ_wrap] at hlu
    split at hlu
    · injection hlu with hlu; subst hlu; decide
    · split at hlu
      · injection hlu with hlu; subst hlu; decide
      · cases hlu
  have hbody : ∀ (Φx : FunEnv), ClosedFunEnv Φx →
      ∀ vs, (∀ v ∈ vs, IsValue v) → (∀ v ∈ vs, freeVars v = []) →
      vs.length = afterSpecLoopCollSpec19Fd.params.length →
      ClosedObsEquiv (fun _ => none) Φx Φx
        (substMany (zipParams afterSpecLoopCollSpec19Fd.params vs) afterSpecLoopCollSpec19Fd.body)
        (substMany (zipParams placeholderSpecLoopCollSpec19Fd.params vs) placeholderSpecLoopCollSpec19Fd.body) := by
    intro Φx _ vs hvs hcl hvlen
    rcases vs with _ | ⟨vn, _ | ⟨vq, _ | ⟨vacc, _ | _⟩⟩⟩ <;> try (simp [afterSpecLoopCollSpec19Fd] at hvlen)
    have hvn : IsValue vn := hvs vn (by simp)
    have hvq : IsValue vq := hvs vq (by simp)
    have hvacc : IsValue vacc := hvs vacc (by simp)
    have hcn : freeVars vn = [] := hcl vn (by simp)
    have hcq : freeVars vq = [] := hcl vq (by simp)
    have hcacc : freeVars vacc = [] := hcl vacc (by simp)
    let env : List (Ident × Expr) :=
      [("$co$20$n", vn), ("$co$22$q", vq), ("$co$25$fv0_0_q", vacc)]
    have henv_cl : ∀ p ∈ env, freeVars p.2 = [] := by
      intro p hp; simp [env] at hp; rcases hp with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
      · exact hcn
      · exact hcq
      · exact hcacc
    let E : Expr → Expr := fun x =>
      .if_ (.bin .leInt vn (.lit (.int 0)))
        vacc
        (.applyDir "specLoopColl$spec$19"
          [.bin .sub vn (.lit (.int 1)), vq, .bin .add vacc x])
    have hafter_eq :
        substMany (zipParams afterSpecLoopCollSpec19Fd.params [vn, vq, vacc]) afterSpecLoopCollSpec19Fd.body =
          E (.let_ "$co$26$z" (.lit (.int 2))
              (subst "$co$24$z" (.var "$co$26$z") (.bin .mul (.var "$co$24$z") vq))) := by
      change substMany env afterSpecLoopCollSpec19Fd.body = _
      have hfl26 : env.filter (fun p => !("$co$26$z" == p.1)) = env := rfl
      simp only [afterSpecLoopCollSpec19Fd, E, substMany_if_eq, substMany_bin_eq,
        substMany_applyDir_eq, substManyList, List.map, substMany_let_eq, hfl26,
        (substMany_atom_eq env).1, substMany_var_lookup henv_cl]
      simp [env, lookupSubstEnv, subst, subst_not_mem_freeVars vq (by simp [hcq])]
    have hph_eq :
        substMany (zipParams placeholderSpecLoopCollSpec19Fd.params [vn, vq, vacc]) placeholderSpecLoopCollSpec19Fd.body =
          .let_ "$co$21$f"
            (.lam .shared [("$co$24$z", .int)] .int (.bin .mul (.var "$co$24$z") vq))
            (E (.apply (.var "$co$21$f") [.lit (.int 2)])) := by
      change substMany env placeholderSpecLoopCollSpec19Fd.body = _
      have hfl21 : env.filter (fun p => !("$co$21$f" == p.1)) = env := rfl
      have hd24 : ∀ x ∈ ([("$co$24$z", Ty.int)].map Prod.fst), x ∉ env.map Prod.fst := by
        simp [env]
      simp only [placeholderSpecLoopCollSpec19Fd, E, substMany_let_eq, hfl21,
        substMany_lam_disjoint Mode.shared [("$co$24$z", Ty.int)] Ty.int _ env hd24,
        substMany_if_eq, substMany_bin_eq, substMany_applyDir_eq, substMany_apply_eq,
        substManyList, List.map, (substMany_atom_eq env).1, substMany_var_lookup henv_cl]
      simp [env, lookupSubstEnv]
    rw [hafter_eq, hph_eq]
    apply ClosedObsEquiv.of_obsEquiv
    refine inline1_reconstructed_cls_let_obsEquiv
      "$co$21$f" .shared "$co$24$z" .int .int (.bin .mul (.var "$co$24$z") vq)
      "$co$26$z" (.lit _) (.bin (.var (by decide)) (.closed hcq)) E ?_ ?_
    · intro a b hab
      apply if_else_obsEquiv_congr
      have hadd : ObsEquiv (fun _ => none) Φx Φx (.bin .add vacc a) (.bin .add vacc b) :=
        activeCtx_obsEquiv_congr (isActiveCtx_binRight (fun _ => none) (by decide) (by decide) hvacc) hab
      simpa using activeList_obsEquiv_congr (Δ := fun _ => none) (Φ := Φx)
        (Expr.applyDir "specLoopColl$spec$19")
        (fun ws hws rest => isActiveCtx_applyDirArg (fun _ => none) "specLoopColl$spec$19" hws rest)
        (es1 := [.bin .sub vn (.lit (.int 1)), vq, .bin .add vacc a])
        (es2 := [.bin .sub vn (.lit (.int 1)), vq, .bin .add vacc b])
        [] (fun _ h => by cases h) rfl
        (fun i h1 _ => by
          have hi3 : i < 3 := by simpa using h1
          match i, hi3 with
          | 0, _ => exact ObsEquiv.refl _ _ _
          | 1, _ => exact ObsEquiv.refl _ _ _
          | 2, _ => exact hadd)
    · simp [E, subst, substList,
        subst_not_mem_freeVars vn (by simp [hcn]),
        subst_not_mem_freeVars vq (by simp [hcq]),
        subst_not_mem_freeVars vacc (by simp [hcacc])]
  exact recFunBody_obsEquiv_congr hΦ2_cl hΦw_cl (f := "specLoopColl$spec$19")
    rfl rfl
    (fun g hg => by
      have hne : (g == "specLoopColl$spec$19") = false := beq_false_of_ne hg
      simp only [Φ2, Φ_wrap, hne, Bool.false_eq_true, ↓reduceIte])
    rfl (hbody Φ2 hΦ2_cl) (hbody Φ_wrap hΦw_cl) hσCl rfl hout

/-! #### Exact Real-Artifact Theorem 3: 2-Argument Callback `std.list.listFold_Int_Int` -> `std.list.listFold_Int_Int$spec$18` (`general.gs`) -/

/-- Monomorphized `std.list.listFold_Int_Int` (`stdlib/std/list.gsa:43`) taking 2-arg callback `f : (Int, Int) -> Int`. -/
def beforeListFoldIntFd : FunDef := {
  name := "std.list.listFold_Int_Int",
  params := [("xs", .adt "List_Int"), ("init", .int), ("f", .fn .local [.int, .int] .int)],
  retTy := .int,
  body := .match_ (.var "xs")
    [(.ctor "List_Int" 0 [], .var "init"),
     (.ctor "List_Int" 1 [.var "h", .var "t"],
      .applyDir "std.list.listFold_Int_Int"
        [.var "t",
         .apply (.var "f") [.var "init", .var "h"],
         .var "f"])]
}

/-- Verbatim parsed `std.list.listFold_Int_Int$spec$18` from `general.gs` (`$co$19$xs`, `$co$20$init`, `$co$22$factor`,
    cloned `Cons($co$26$h, $co$27$t)`, and 2-argument callback `(acc, x) -> acc * factor + x` inlined directly!). -/
def afterListFoldSpec18Fd : FunDef := {
  name := "std.list.listFold_Int_Int$spec$18",
  params := [("$co$19$xs", .adt "List_Int"), ("$co$20$init", .int), ("$co$22$factor", .int)],
  retTy := .int,
  body := .match_ (.var "$co$19$xs")
    [(.ctor "List_Int" 0 [], .var "$co$20$init"),
     (.ctor "List_Int" 1 [.var "$co$26$h", .var "$co$27$t"],
      .applyDir "std.list.listFold_Int_Int$spec$18"
        [.var "$co$27$t",
         .bin .add (.bin .mul (.var "$co$20$init") (.var "$co$22$factor")) (.var "$co$26$h"),
         .var "$co$22$factor"])]
}

def listFoldMulAddCbSlot (factorVal : Expr) : CbSlotSpec := {
  fParam := "f", fnTy := .fn .local [.int, .int] .int, cbMode := .shared,
  cbParams := [("acc", .int), ("x", .int)], cbRet := .int,
  cbBody := .bin .add (.bin .mul (.var "acc") (.var "factor")) (.var "x"),
  fvs := [("factor", .int)], fvVals := [factorVal],
  lowering := .flatDir "$tmp$listFoldCb"
}

/-- **Exact Real-Artifact Theorem 3 (`exact_artifact_listFold_spec18_obsEquiv`)**:
    Proves full `Steps` equivalence between `std.list.listFold_Int_Int` (with 2-arg callback
    `(acc, x) -> acc * factor + x`) and the verbatim parsed `general.gs` `std.list.listFold_Int_Int$spec$18`
    (where `Φ2` contains ONLY `std.list.listFold_Int_Int` and `std.list.listFold_Int_Int$spec$18`,
    with the 2-arg callback directly inlined to `($co$20$init * $co$22$factor) + $co$26$h`)
    across **all** closed `List_Int` values `xsVal` and all `initVal, factorVal`! -/
theorem exact_artifact_listFold_spec18_obsEquiv {Δ : AdtEnv}
    {xsVal initVal factorVal : Expr} {σ σ' : Store} {out : Expr}
    (hxsVal : IsValue xsVal) (hxsCl : freeVars xsVal = []) (hxsDom : exprInDom (fun nm => nm == "std.list.listFold_Int_Int") xsVal = true)
    (hinitVal : IsValue initVal) (hinitCl : freeVars initVal = []) (hinitDom : exprInDom (fun nm => nm == "std.list.listFold_Int_Int") initVal = true)
    (hfacVal : IsValue factorVal) (hfacCl : freeVars factorVal = []) (hfacDom : exprInDom (fun nm => nm == "std.list.listFold_Int_Int") factorVal = true)
    (hσCl : ClosedStore σ)
    (hσDom : StoreInDom (fun nm => nm == "std.list.listFold_Int_Int") σ)
    (hout : IsTerminal out) :
    let cb := listFoldMulAddCbSlot factorVal
    let Φ1 : FunEnv := fun nm =>
      if nm == "std.list.listFold_Int_Int" then some beforeListFoldIntFd else none
    let Φ2 : FunEnv := fun nm =>
      if nm == "std.list.listFold_Int_Int" then some beforeListFoldIntFd
      else if nm == "std.list.listFold_Int_Int$spec$18" then some afterListFoldSpec18Fd
      else none
    Steps Δ Φ1 (.applyDir "std.list.listFold_Int_Int" [xsVal, initVal, cb.cls]) σ out σ' ↔
      Steps Δ Φ2 (.applyDir "std.list.listFold_Int_Int$spec$18" [xsVal, initVal, factorVal]) σ out σ' := by
  intro cb Φ1 Φ2
  let slots : List PosSpecSlot := [.state ("xs", .adt "List_Int"), .state ("init", .int), .callback cb]
  let rawBody : Expr :=
    .match_ (.var "xs")
      [(.ctor "List_Int" 0 [], .var "init"),
       (.ctor "List_Int" 1 [.var "h", .var "t"],
        .applyDir "std.list.listFold_Int_Int$spec$18"
          [.var "t",
           .applyDir "$tmp$listFoldCb" [.var "factor", .var "init", .var "h"],
           .var "factor"])]
  let cbFlatFd : FunDef := {
    name := "$tmp$listFoldCb",
    params := [("factor", .int), ("acc", .int), ("x", .int)],
    retTy := .int,
    body := .bin .add (.bin .mul (.var "acc") (.var "factor")) (.var "x")
  }
  let Φ_raw : FunEnv := fun nm =>
    if nm == "std.list.listFold_Int_Int" then some beforeListFoldIntFd
    else if nm == "std.list.listFold_Int_Int$spec$18" then
      some { name := "std.list.listFold_Int_Int$spec$18",
             params := [("xs", .adt "List_Int"), ("init", .int), ("factor", .int)],
             retTy := .int, body := rawBody }
    else if nm == "$tmp$listFoldCb" then some cbFlatFd
    else none
  let Φ_aux : FunEnv := fun nm =>
    if nm == "std.list.listFold_Int_Int" then some beforeListFoldIntFd
    else if nm == "std.list.listFold_Int_Int$spec$18" then some afterListFoldSpec18Fd
    else if nm == "$tmp$listFoldCb" then some cbFlatFd
    else none
  have hΦraw_cl : ClosedFunEnv Φ_raw := by
    intro nm fd hlu; dsimp only [Φ_raw] at hlu
    split at hlu
    · injection hlu with hlu; subst hlu
      simp only [beforeListFoldIntFd, freeVars, freeVarsArms, freeVarsList, patBoundNames, List.foldr_cons, List.foldr_nil]; decide
    · split at hlu
      · injection hlu with hlu; subst hlu
        simp only [rawBody, freeVars, freeVarsArms, freeVarsList, patBoundNames, List.foldr_cons, List.foldr_nil]; decide
      · split at hlu
        · injection hlu with hlu; subst hlu; decide
        · cases hlu
  have hΦaux_cl : ClosedFunEnv Φ_aux := by
    intro nm fd hlu; dsimp only [Φ_aux] at hlu
    split at hlu
    · injection hlu with hlu; subst hlu
      simp only [beforeListFoldIntFd, freeVars, freeVarsArms, freeVarsList, patBoundNames, List.foldr_cons, List.foldr_nil]; decide
    · split at hlu
      · injection hlu with hlu; subst hlu
        simp only [afterListFoldSpec18Fd, freeVars, freeVarsArms, freeVarsList, patBoundNames, List.foldr_cons, List.foldr_nil]; decide
      · split at hlu
        · injection hlu with hlu; subst hlu; decide
        · cases hlu
  have hcbWf : CbSlotWF (fun nm => nm == "std.list.listFold_Int_Int") Φ_raw cb := by
    refine ⟨?_, ?_, ?_, rfl, ?_, ?_, rfl, rfl⟩
    · intro v hv; simp [cb, listFoldMulAddCbSlot] at hv; subst hv; exact hfacVal
    · intro v hv; simp [cb, listFoldMulAddCbSlot] at hv; subst hv; exact hfacCl
    · intro v hv; simp [cb, listFoldMulAddCbSlot] at hv; subst hv; exact hfacDom
    · dsimp only [cb, listFoldMulAddCbSlot]; decide
    · dsimp only [cb, listFoldMulAddCbSlot]; decide
  let S : PositionalLoopSpec Δ Φ_raw := {
    origFn := "std.list.listFold_Int_Int",
    specFn := "std.list.listFold_Int_Int$spec$18",
    slots := slots,
    loopRet := .int,
    loopBody := beforeListFoldIntFd.body,
    dom := fun nm => nm == "std.list.listFold_Int_Int",
    hΦcl := hΦraw_cl,
    hLoop := rfl,
    hSpec := rfl,
    hcbs := fun c hc => by simp [slots, cbSlotsOf] at hc; subst hc; exact hcbWf,
    hOrigNodup := by dsimp only [slots, cb, listFoldMulAddCbSlot, posOrigParams]; decide,
    hSpecNodup := by dsimp only [slots, cb, listFoldMulAddCbSlot, posSpecParams]; decide,
    hinlDisjSpec := by
      intro c hc _ hlow; simp [slots, cbSlotsOf] at hc; subst hc
      simp [cb, listFoldMulAddCbSlot] at hlow,
    hLoopNoFv := by
      dsimp only [slots, cb, listFoldMulAddCbSlot, allCbFvNames, cbSlotsOf, beforeListFoldIntFd]
      simp only [freeVars, freeVarsArms, freeVarsList, patBoundNames, List.foldr_cons, List.foldr_nil]; decide,
    hEligible := .match_ (.var rfl)
      (.cons
        (by
          dsimp only [slots, cb, listFoldMulAddCbSlot, allCbOrigNames, posSpecParams, cbSlotsOf]
          simp only [patBoundNames, List.foldr_nil]; decide)
        (.var rfl)
        (.cons
          (by
            dsimp only [slots, cb, listFoldMulAddCbSlot, allCbOrigNames, posSpecParams, cbSlotsOf]
            simp only [patBoundNames, List.foldr_cons, List.foldr_nil]; decide)
          (.selfCall (.state ("xs", .adt "List_Int") (.var rfl)
            (.state ("init", .int)
              (.cbCallFlat rfl rfl rfl (.cons (.var rfl) (.cons (.var rfl) .nil)))
              (.callback cb .nil))))
          .nil))
  }
  have hrel_both : ∀ (Φx : FunEnv), Φx "$tmp$listFoldCb" = some cbFlatFd →
      AlphaOptRel Φx [("xs", "$co$19$xs"), ("init", "$co$20$init"), ("factor", "$co$22$factor")]
        rawBody afterListFoldSpec18Fd.body := by
    intro Φx hcb
    refine .matchAlpha (.var _ "xs")
      (.cons (.ctor "List_Int" 0 .nil) (by decide) (by decide) (by decide) (.var _ "init")
        (.cons (.ctor "List_Int" 1 (.cons (.var "h" "$co$26$h") (.cons (.var "t" "$co$27$t") .nil)))
          (by decide) (by decide) (by decide) ?_ (.nil _)))
    refine .applyDir "std.list.listFold_Int_Int$spec$18"
      (.cons (.var _ "t") (.cons ?_ (.cons (.var _ "factor") (.nil _))))
    exact .inlineDirVars (srcVars := ["factor", "init", "h"]) hcb rfl (by decide) (by decide)
      (checkAlphaOpt_sound Φx _ cbFlatFd.body
        (.bin .add (.bin .mul (.var "$co$20$init") (.var "$co$22$factor")) (.var "$co$26$h")) (by decide))
  let dom2 : Ident → Bool := fun nm => nm == "std.list.listFold_Int_Int" || nm == "std.list.listFold_Int_Int$spec$18"
  have hsub12 : ∀ f, (f == "std.list.listFold_Int_Int") = true → dom2 f = true :=
    fun f hf => by simp [dom2, hf]
  exact positional_hof_loop_spec_optBody_obsEquiv S (dom2 := dom2) (Φ_aux := Φ_aux)
    (fun nm h => by have heq := eq_of_beq h; subst heq; rfl)
    (fun nm fd h1 hlu => by
      have heq := eq_of_beq h1; subst heq; dsimp only [Φ1] at hlu; simp at hlu; subst hlu
      simp only [beforeListFoldIntFd, exprInDom, exprArmsInDom, exprListInDom]; rfl)
    rfl hΦaux_cl rfl rfl
    (fun g hg => by
      have hne : (g == "std.list.listFold_Int_Int$spec$18") = false := beq_false_of_ne hg
      simp only [Φ_raw, Φ_aux, hne, Bool.false_eq_true, ↓reduceIte])
    rfl (by decide)
    (by
      dsimp only [S, slots, cb, listFoldMulAddCbSlot, posSpecParams, rawBody]
      simp only [freeVars, freeVarsArms, freeVarsList, patBoundNames, List.foldr_cons, List.foldr_nil]; decide)
    (hrel_both Φ_raw rfl)
    (hrel_both Φ_aux rfl)
    (fun nm hdom => by
      simp only [dom2, Bool.or_eq_true] at hdom
      rcases hdom with h1 | h2
      · rw [eq_of_beq h1]; rfl
      · rw [eq_of_beq h2]; rfl)
    (fun nm fd _ hlu => by
      dsimp only [Φ2] at hlu
      split at hlu
      · injection hlu with hlu; subst hlu
        simp only [beforeListFoldIntFd, exprInDom, exprArmsInDom, exprListInDom]; rfl
      · split at hlu
        · injection hlu with hlu; subst hlu
          simp only [afterListFoldSpec18Fd, exprInDom, exprArmsInDom, exprListInDom]; rfl
        · cases hlu)
    rfl
    hσCl hσDom (fun v hv => exprInDom_mono hsub12 v (hσDom v hv)) hout
    (.state ("xs", .adt "List_Int") (PosSpecRel.refl _ _ _ xsVal)
      (.state ("init", .int) (PosSpecRel.refl _ _ _ initVal) (.callback cb .nil)))
    (fun e he => by
      simp at he; rcases he with rfl | rfl | rfl
      · exact hxsCl
      · exact hinitCl
      · exact cb.cls_closed hcbWf)
    (fun e he => by
      simp at he; rcases he with rfl | rfl | rfl
      · exact hxsDom
      · exact hinitDom
      · exact cb.cls_inDom hcbWf)
    (fun e he => by simp at he; rcases he with rfl | rfl | rfl; exact hxsCl; exact hinitCl; exact hfacCl)
    (fun e he => by
      simp at he; rcases he with rfl | rfl | rfl
      · exact exprInDom_mono hsub12 _ hxsDom
      · exact exprInDom_mono hsub12 _ hinitDom
      · exact exprInDom_mono hsub12 _ hfacDom)

end CoreGeisha
