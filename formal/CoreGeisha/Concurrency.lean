import CoreGeisha.Syntax
import CoreGeisha.Typing
import CoreGeisha.Semantics
import CoreGeisha.Soundness

/-!
# Core Geisha: Concurrent Type Safety & Compile-Time Data-Race Freedom

Machine-checked proof (zero `sorry`) that Core Geisha's phantom capture-mode
system (`Mode.local` vs `Mode.shared`) and `IsSend` discipline enforce **strict
thread-local heap isolation** across arbitrary interleaved concurrent executions
(`ConcSteps`):

1. **Concurrent Pool Preservation & Progress** (`concStep_preserves_inv`, `conc_type_safety`):
   Every thread in a reachable concurrent task pool remains closed, well-typed,
   and never gets stuck (`¬ IsStuck`).
2. **Global Heap Ownership Partition** (`HeapOwned`, `step_preserves_ownership`):
   Every allocated `Cell` location `l < σ.length` has a unique owning thread
   `owners[l] = tid`; `spawn` transfers zero locations (`exprLocs body = []` by
   `shared` closure typing) and `await` transfers zero locations
   (`exprLocs_empty_of_isValue_isSend`).
3. **Compile-Time Data-Race Freedom** (`conc_heap_disjoint`, `conc_data_race_freedom`):
   Distinct threads NEVER reach—let alone concurrently read or write—the same
   mutable `Cell` location (`¬ HasDataRace tasks`).
-/

namespace CoreGeisha

/-! ## Pattern & Simultaneous-Substitution Location Bounds -/

mutual
theorem matchPat_locs {p : Pat} {v : Expr} {env : List (Ident × Expr)}
    (hm : matchPat p v = some env) :
    ∀ x u, (x, u) ∈ env → ∀ l ∈ exprLocs u, l ∈ exprLocs v := by
  cases p with
  | wild =>
    simp only [matchPat, Option.some.injEq] at hm
    subst hm; intro _ _ h; cases h
  | var y =>
    simp only [matchPat, Option.some.injEq] at hm
    subst hm
    intro _ u hu l hl
    simp only [List.mem_singleton, Prod.mk.injEq] at hu
    rcases hu with ⟨_, rfl⟩
    exact hl
  | lit _ =>
    cases v <;> simp only [matchPat] at hm <;> try cases hm
    split at hm
    · cases hm; intro _ _ h; cases h
    · cases hm
  | tuple ps =>
    cases v <;> simp only [matchPat] at hm <;> try cases hm
    intro x u hu l hl
    simp only [exprLocs]
    exact matchPats_locs hm x u hu l hl
  | ctor adt tag ps =>
    cases v <;> simp only [matchPat] at hm <;> try cases hm
    split at hm
    · intro x u hu l hl
      simp only [exprLocs]
      exact matchPats_locs hm x u hu l hl
    · cases hm

theorem matchPats_locs {ps : List Pat} {vs : List Expr} {env : List (Ident × Expr)}
    (hm : matchPats ps vs = some env) :
    ∀ x u, (x, u) ∈ env → ∀ l ∈ exprLocs u, l ∈ exprLocsList vs := by
  cases ps with
  | nil =>
    cases vs <;> simp only [matchPats] at hm <;> try cases hm
    intro _ _ h; cases h
  | cons p rest =>
    cases vs with
    | nil => simp [matchPats] at hm
    | cons v vrest =>
      simp only [matchPats] at hm
      cases h1 : matchPat p v with
      | none => rw [h1] at hm; cases hm
      | some b1 =>
        rw [h1] at hm
        cases h2 : matchPats rest vrest with
        | none => rw [h2] at hm; cases hm
        | some b2 =>
          rw [h2] at hm; cases hm
          intro x u hmem l hl
          simp only [exprLocsList, List.mem_append]
          rcases List.mem_append.mp hmem with hm1 | hm2
          · exact Or.inl (matchPat_locs h1 x u hm1 l hl)
          · exact Or.inr (matchPats_locs h2 x u hm2 l hl)
end

theorem mem_exprLocs_substMany {env : List (Ident × Expr)} {e : Expr} {l : Loc}
    (hl : l ∈ exprLocs (substMany env e)) :
    l ∈ exprLocs e ∨ ∃ x u, (x, u) ∈ env ∧ l ∈ exprLocs u := by
  induction env generalizing e with
  | nil => exact Or.inl hl
  | cons kv rest ih =>
    cases kv with
    | mk x v =>
      simp only [substMany] at hl
      rcases ih hl with hsub | ⟨y, u, hmem, hlu⟩
      · rcases mem_exprLocs_subst e hsub with he | hv
        · exact Or.inl he
        · exact Or.inr ⟨x, v, List.mem_cons_self .., hv⟩
      · exact Or.inr ⟨y, u, List.mem_cons_of_mem _ hmem, hlu⟩

theorem zipParams_mem_locs {ps : List (Ident × Ty)} {args : List Expr}
    {x : Ident} {u : Expr} {l : Loc}
    (hmem : (x, u) ∈ zipParams ps args) (hl : l ∈ exprLocs u) :
    l ∈ exprLocsList args := by
  induction ps generalizing args with
  | nil => simp [zipParams] at hmem
  | cons p prest ih =>
    cases args with
    | nil => simp [zipParams] at hmem
    | cons a arest =>
      simp only [zipParams, List.map_cons, List.zip_cons_cons, List.mem_cons, Prod.mk.injEq] at hmem
      simp only [exprLocsList, List.mem_append]
      rcases hmem with ⟨_, rfl⟩ | hrest
      · exact Or.inl hl
      · exact Or.inr (ih hrest)

/-! ## Active Cell Access Implies Syntactic Location Presence -/

mutual
theorem activeCellAccess_mem_exprLocs {b : Bool} :
    (e : Expr) → ∀ {l : Loc}, ActiveCellAccess b e l → l ∈ exprLocs e
  | _, _, .read _ _ => by simp [exprLocs]
  | _, _, .write _ _ _ => by simp [exprLocs]
  | _, _, .tuple hs => by
    simp only [exprLocs]
    exact activeCellAccessList_mem_exprLocs _ hs
  | _, _, .blockCons hs => by
    simp [exprLocs, exprLocsList, activeCellAccess_mem_exprLocs _ hs]
  | _, _, .applyFn hs => by
    simp [exprLocs, activeCellAccess_mem_exprLocs _ hs]
  | _, _, .applyArgs _ hs => by
    simp [exprLocs, activeCellAccessList_mem_exprLocs _ hs]
  | _, _, .applyDirArgs hs => by
    simp only [exprLocs]
    exact activeCellAccessList_mem_exprLocs _ hs
  | _, _, .un hs => by
    simp only [exprLocs]
    exact activeCellAccess_mem_exprLocs _ hs
  | _, _, .binLeft hs => by
    simp [exprLocs, activeCellAccess_mem_exprLocs _ hs]
  | _, _, .binRight _ _ _ hs => by
    simp [exprLocs, activeCellAccess_mem_exprLocs _ hs]
  | _, _, .let_ hs => by
    simp [exprLocs, activeCellAccess_mem_exprLocs _ hs]
  | _, _, .if_ hs => by
    simp [exprLocs, activeCellAccess_mem_exprLocs _ hs]
  | _, _, .match_ hs => by
    simp [exprLocs, activeCellAccess_mem_exprLocs _ hs]
  | _, _, .makeData hs => by
    simp only [exprLocs]
    exact activeCellAccessList_mem_exprLocs _ hs
  | _, _, .getTag hs => by
    simp only [exprLocs]
    exact activeCellAccess_mem_exprLocs _ hs
  | _, _, .cellNew hs => by
    simp only [exprLocs]
    exact activeCellAccess_mem_exprLocs _ hs
  | _, _, .cellGetStep hs => by
    simp only [exprLocs]
    exact activeCellAccess_mem_exprLocs _ hs
  | _, _, .cellSetLeft hs => by
    simp [exprLocs, activeCellAccess_mem_exprLocs _ hs]
  | _, _, .cellSetRight _ hs => by
    simp [exprLocs, activeCellAccess_mem_exprLocs _ hs]
  | _, _, .spawn hs => by
    simp only [exprLocs]
    exact activeCellAccess_mem_exprLocs _ hs
  | _, _, .awaitStep hs => by
    simp only [exprLocs]
    exact activeCellAccess_mem_exprLocs _ hs
termination_by e => sizeOf e

theorem activeCellAccessList_mem_exprLocs {b : Bool} :
    (es : List Expr) → ∀ {l : Loc}, ActiveCellAccessList b es l → l ∈ exprLocsList es
  | _, _, .head hs => by simp [exprLocsList, activeCellAccess_mem_exprLocs _ hs]
  | _, _, .tail _ hs => by simp [exprLocsList, activeCellAccessList_mem_exprLocs _ hs]
termination_by es => sizeOf es
end

/-- Non-vacuity witness: if two threads actually held `.loc 0` with one writing
    and one reading, `HasDataRace` would hold. -/
theorem hasDataRace_nonvacuous :
    HasDataRace [.cellSet (.loc 0) (.lit (.int 1)), .cellGet (.loc 0)] := by
  refine ⟨0, 1, .cellSet (.loc 0) (.lit (.int 1)), .cellGet (.loc 0), true, false, 0,
    by decide, rfl, rfl, .write 0 rfl (.lit _), .read 0 rfl, Or.inl rfl⟩

/-! ## Heap Ownership Partition Invariant -/

/-- Thread-exclusive heap ownership partition:
    - Every allocated `Cell` `l < σ.length` has a unique owner thread ID `owners[l]`.
    - Every location `l` reachable inside thread `tid`'s expression belongs to `tid`.
    - Every location `l'` stored inside heap cell `σ[l]` belongs to the same owner as `l`. -/
structure HeapOwned (owners : List Nat) (tasks : List Expr) (σ : Store) : Prop where
  len_eq : owners.length = σ.length
  task_locs : ∀ (tid : Nat) (e : Expr) (l : Loc), tasks[tid]? = some e → l ∈ exprLocs e → owners[l]? = some tid
  store_locs : ∀ (l : Loc) (v : Expr) (l' : Loc), σ[l]? = some v → l' ∈ exprLocs v → owners[l']? = owners[l]?

/-- Monotone extension of thread ownership list as new `Cell`s are allocated. -/
def OwnersExtend (o1 o2 : List Nat) : Prop :=
  ∀ (l : Loc) (tid : Nat), o1[l]? = some tid → o2[l]? = some tid

theorem OwnersExtend.refl (o : List Nat) : OwnersExtend o o :=
  fun _ _ h => h

theorem OwnersExtend.append (o : List Nat) (tid : Nat) : OwnersExtend o (o ++ [tid]) := by
  intro l t hl
  have hlt : l < o.length := lt_length_of_getElem?_eq_some hl
  rw [List.getElem?_append_left hlt]
  exact hl

/-! ## Single-Step Ownership Preservation -/

mutual
theorem step_preserves_ownership {Δ : AdtEnv} {Φ : FunEnv} (hΦ : FunEnvTyped Δ Φ)
    {Ψ : StoreTy} {Θ : TaskTy} {tasks : List Expr}
    {e : Expr} {σ : Store} {e' : Expr} {σ' : Store} {sp : Option Expr} {τ : Ty}
    {owners : List Nat} {tid : Nat}
    (ht : HasType Δ Φ Ψ Θ emptyCtx e τ)
    (hstep : Step Δ Φ tasks e σ e' σ' sp)
    (htasks : TasksTyped Δ Φ Ψ Θ tasks)
    (hlen : owners.length = σ.length)
    (he_own : ∀ l ∈ exprLocs e, owners[l]? = some tid)
    (hstore_own : ∀ (l : Loc) (v : Expr) (l' : Loc), σ[l]? = some v → l' ∈ exprLocs v → owners[l']? = owners[l]?) :
    ∃ owners',
      OwnersExtend owners owners' ∧
      owners'.length = σ'.length ∧
      (∀ l ∈ exprLocs e', owners'[l]? = some tid) ∧
      (∀ (l : Loc) (v : Expr) (l' : Loc), σ'[l]? = some v → l' ∈ exprLocs v → owners'[l']? = owners'[l]?) ∧
      (∀ body, sp = some body → exprLocs body = []) := by
  cases hstep with
  | tupleStep hs =>
    cases ht with
    | tuple hts =>
      simp only [exprLocs] at he_own ⊢
      exact stepList_preserves_ownership hΦ hts hs htasks hlen he_own hstore_own
  | tupleTrap _ =>
    exact ⟨owners, OwnersExtend.refl _, hlen, (fun _ h => nomatch h), hstore_own, (fun _ h => nomatch h)⟩
  | blockEmpty =>
    exact ⟨owners, OwnersExtend.refl _, hlen, (fun _ h => nomatch h), hstore_own, (fun _ h => nomatch h)⟩
  | blockSingle =>
    refine ⟨owners, OwnersExtend.refl _, hlen, ?_, hstore_own, (fun _ h => nomatch h)⟩
    intro l hl
    apply he_own l
    simp [exprLocs, exprLocsList, hl]
  | blockConsStep hs =>
    cases ht with
    | blockCons h1 _ =>
      rcases step_preserves_ownership hΦ h1 hs htasks hlen
        (fun l hl => he_own l (by simp [exprLocs, exprLocsList, hl])) hstore_own with
        ⟨owners', hext, hlen', he1', hst', hsp⟩
      refine ⟨owners', hext, hlen', ?_, hst', hsp⟩
      intro l hl
      simp only [exprLocs, exprLocsList, List.mem_append] at hl
      rcases hl with hl1 | hlrest
      · exact he1' l hl1
      · exact hext l tid (he_own l (by simp [exprLocs, exprLocsList, hlrest]))
  | blockConsVal _ =>
    refine ⟨owners, OwnersExtend.refl _, hlen, ?_, hstore_own, (fun _ h => nomatch h)⟩
    intro l hl
    apply he_own l
    simp only [exprLocs, exprLocsList, List.mem_append] at hl ⊢
    exact Or.inr hl
  | blockConsTrap =>
    exact ⟨owners, OwnersExtend.refl _, hlen, (fun _ h => nomatch h), hstore_own, (fun _ h => nomatch h)⟩
  | applyFn hs =>
    cases ht with
    | apply hfn _ _ =>
      rcases step_preserves_ownership hΦ hfn hs htasks hlen
        (fun l hl => he_own l (by simp [exprLocs, hl])) hstore_own with
        ⟨owners', hext, hlen', he1', hst', hsp⟩
      refine ⟨owners', hext, hlen', ?_, hst', hsp⟩
      intro l hl
      simp only [exprLocs, List.mem_append] at hl
      rcases hl with h1 | h2
      · exact he1' l h1
      · exact hext l tid (he_own l (by simp [exprLocs, h2]))
  | applyFnTrap =>
    exact ⟨owners, OwnersExtend.refl _, hlen, (fun _ h => nomatch h), hstore_own, (fun _ h => nomatch h)⟩
  | applyArgs _ hs =>
    cases ht with
    | apply _ hargs _ =>
      rcases stepList_preserves_ownership hΦ hargs hs htasks hlen
        (fun l hl => he_own l (by simp [exprLocs, hl])) hstore_own with
        ⟨owners', hext, hlen', he2', hst', hsp⟩
      refine ⟨owners', hext, hlen', ?_, hst', hsp⟩
      intro l hl
      simp only [exprLocs, List.mem_append] at hl
      rcases hl with h1 | h2
      · exact hext l tid (he_own l (by simp [exprLocs, h1]))
      · exact he2' l h2
  | applyArgsTrap _ _ =>
    exact ⟨owners, OwnersExtend.refl _, hlen, (fun _ h => nomatch h), hstore_own, (fun _ h => nomatch h)⟩
  | applyBeta _ _ =>
    refine ⟨owners, OwnersExtend.refl _, hlen, ?_, hstore_own, (fun _ h => nomatch h)⟩
    intro l hl
    rcases mem_exprLocs_substMany hl with hbody | ⟨x, u, hmem, hlu⟩
    · exact he_own l (by simp [exprLocs, hbody])
    · exact he_own l (by simp [exprLocs, zipParams_mem_locs hmem hlu])
  | applyDirArgs hs =>
    cases ht with
    | applyDir _ hargs _ =>
      simp only [exprLocs] at he_own ⊢
      exact stepList_preserves_ownership hΦ hargs hs htasks hlen he_own hstore_own
  | applyDirTrap _ =>
    exact ⟨owners, OwnersExtend.refl _, hlen, (fun _ h => nomatch h), hstore_own, (fun _ h => nomatch h)⟩
  | applyDirBeta hf _ _ =>
    refine ⟨owners, OwnersExtend.refl _, hlen, ?_, hstore_own, (fun _ h => nomatch h)⟩
    intro l hl
    have hfd := exprLocs_empty_of_empty_store (hΦ _ _ hf)
    rcases mem_exprLocs_substMany hl with hbody | ⟨x, u, hmem, hlu⟩
    · rw [hfd] at hbody; cases hbody
    · exact he_own l (by simp [exprLocs, zipParams_mem_locs hmem hlu])
  | unStep hs =>
    cases ht with
    | un _ h1 =>
      simp only [exprLocs] at he_own ⊢
      exact step_preserves_ownership hΦ h1 hs htasks hlen he_own hstore_own
  | unTrap =>
    exact ⟨owners, OwnersExtend.refl _, hlen, (fun _ h => nomatch h), hstore_own, (fun _ h => nomatch h)⟩
  | unVal _ =>
    exact ⟨owners, OwnersExtend.refl _, hlen, (fun _ h => nomatch h), hstore_own, (fun _ h => nomatch h)⟩
  | binLeft hs =>
    cases ht with
    | bin _ h1 _ =>
      rcases step_preserves_ownership hΦ h1 hs htasks hlen
        (fun l hl => he_own l (by simp [exprLocs, hl])) hstore_own with
        ⟨owners', hext, hlen', he1', hst', hsp⟩
      refine ⟨owners', hext, hlen', ?_, hst', hsp⟩
      intro l hl
      simp only [exprLocs, List.mem_append] at hl
      rcases hl with hl1 | hl2
      · exact he1' l hl1
      · exact hext l tid (he_own l (by simp [exprLocs, hl2]))
  | binLeftTrap =>
    exact ⟨owners, OwnersExtend.refl _, hlen, (fun _ h => nomatch h), hstore_own, (fun _ h => nomatch h)⟩
  | binAndFalse =>
    exact ⟨owners, OwnersExtend.refl _, hlen, (fun _ h => nomatch h), hstore_own, (fun _ h => nomatch h)⟩
  | binAndTrue =>
    refine ⟨owners, OwnersExtend.refl _, hlen, ?_, hstore_own, (fun _ h => nomatch h)⟩
    intro l hl; exact he_own l (by simp [exprLocs, hl])
  | binOrTrue =>
    exact ⟨owners, OwnersExtend.refl _, hlen, (fun _ h => nomatch h), hstore_own, (fun _ h => nomatch h)⟩
  | binOrFalse =>
    refine ⟨owners, OwnersExtend.refl _, hlen, ?_, hstore_own, (fun _ h => nomatch h)⟩
    intro l hl; exact he_own l (by simp [exprLocs, hl])
  | binRight _ _ _ hs =>
    cases ht with
    | bin _ _ h2 =>
      rcases step_preserves_ownership hΦ h2 hs htasks hlen
        (fun l hl => he_own l (by simp [exprLocs, hl])) hstore_own with
        ⟨owners', hext, hlen', he2', hst', hsp⟩
      refine ⟨owners', hext, hlen', ?_, hst', hsp⟩
      intro l hl
      simp only [exprLocs, List.mem_append] at hl
      rcases hl with hl1 | hl2
      · exact hext l tid (he_own l (by simp [exprLocs, hl1]))
      · exact he2' l hl2
  | binRightTrap _ _ _ =>
    exact ⟨owners, OwnersExtend.refl _, hlen, (fun _ h => nomatch h), hstore_own, (fun _ h => nomatch h)⟩
  | binVal _ =>
    exact ⟨owners, OwnersExtend.refl _, hlen, (fun _ h => nomatch h), hstore_own, (fun _ h => nomatch h)⟩
  | binTrap _ =>
    exact ⟨owners, OwnersExtend.refl _, hlen, (fun _ h => nomatch h), hstore_own, (fun _ h => nomatch h)⟩
  | letStep hs =>
    cases ht with
    | let_ h1 _ =>
      rcases step_preserves_ownership hΦ h1 hs htasks hlen
        (fun l hl => he_own l (by simp [exprLocs, hl])) hstore_own with
        ⟨owners', hext, hlen', he1', hst', hsp⟩
      refine ⟨owners', hext, hlen', ?_, hst', hsp⟩
      intro l hl
      simp only [exprLocs, List.mem_append] at hl
      rcases hl with hl1 | hl2
      · exact he1' l hl1
      · exact hext l tid (he_own l (by simp [exprLocs, hl2]))
  | letTrap =>
    exact ⟨owners, OwnersExtend.refl _, hlen, (fun _ h => nomatch h), hstore_own, (fun _ h => nomatch h)⟩
  | letVal _ =>
    refine ⟨owners, OwnersExtend.refl _, hlen, ?_, hstore_own, (fun _ h => nomatch h)⟩
    intro l hl
    rcases mem_exprLocs_subst _ hl with h2 | h1
    · exact he_own l (by simp [exprLocs, h2])
    · exact he_own l (by simp [exprLocs, h1])
  | ifStep hs =>
    cases ht with
    | if_ hc _ _ =>
      rcases step_preserves_ownership hΦ hc hs htasks hlen
        (fun l hl => he_own l (by simp [exprLocs, hl])) hstore_own with
        ⟨owners', hext, hlen', hec', hst', hsp⟩
      refine ⟨owners', hext, hlen', ?_, hst', hsp⟩
      intro l hl
      simp only [exprLocs, List.mem_append] at hl
      rcases hl with (hlc | hlt) | hle
      · exact hec' l hlc
      · exact hext l tid (he_own l (by simp [exprLocs, hlt]))
      · exact hext l tid (he_own l (by simp [exprLocs, hle]))
  | ifTrap =>
    exact ⟨owners, OwnersExtend.refl _, hlen, (fun _ h => nomatch h), hstore_own, (fun _ h => nomatch h)⟩
  | ifTrue =>
    refine ⟨owners, OwnersExtend.refl _, hlen, ?_, hstore_own, (fun _ h => nomatch h)⟩
    intro l hl; exact he_own l (by simp [exprLocs, hl])
  | ifFalse =>
    refine ⟨owners, OwnersExtend.refl _, hlen, ?_, hstore_own, (fun _ h => nomatch h)⟩
    intro l hl; exact he_own l (by simp [exprLocs, hl])
  | whileUnfold =>
    refine ⟨owners, OwnersExtend.refl _, hlen, ?_, hstore_own, (fun _ h => nomatch h)⟩
    intro l hl
    simp only [exprLocs, exprLocsList, List.append_nil, List.mem_append] at hl
    rcases hl with hlc | hlb | hlc2 | hlb2
    · exact he_own l (by simp [exprLocs, hlc])
    · exact he_own l (by simp [exprLocs, hlb])
    · exact he_own l (by simp [exprLocs, hlc2])
    · exact he_own l (by simp [exprLocs, hlb2])
  | matchScrut hs =>
    cases ht with
    | match_ hscr _ =>
      rcases step_preserves_ownership hΦ hscr hs htasks hlen
        (fun l hl => he_own l (by simp [exprLocs, hl])) hstore_own with
        ⟨owners', hext, hlen', hes', hst', hsp⟩
      refine ⟨owners', hext, hlen', ?_, hst', hsp⟩
      intro l hl
      simp only [exprLocs, List.mem_append] at hl
      rcases hl with hls | hla
      · exact hes' l hls
      · exact hext l tid (he_own l (by simp [exprLocs, hla]))
  | matchScrutTrap =>
    exact ⟨owners, OwnersExtend.refl _, hlen, (fun _ h => nomatch h), hstore_own, (fun _ h => nomatch h)⟩
  | matchEmpty _ =>
    exact ⟨owners, OwnersExtend.refl _, hlen, (fun _ h => nomatch h), hstore_own, (fun _ h => nomatch h)⟩
  | matchHit _ hm =>
    refine ⟨owners, OwnersExtend.refl _, hlen, ?_, hstore_own, (fun _ h => nomatch h)⟩
    intro l hl
    rcases mem_exprLocs_substMany hl with hbody | ⟨x, u, hmem, hlu⟩
    · exact he_own l (by simp [exprLocs, exprLocsArms, hbody])
    · exact he_own l (by simp [exprLocs, matchPat_locs hm x u hmem l hlu])
  | matchMiss _ _ =>
    refine ⟨owners, OwnersExtend.refl _, hlen, ?_, hstore_own, (fun _ h => nomatch h)⟩
    intro l hl
    simp only [exprLocs, List.mem_append] at hl
    rcases hl with hls | hla
    · exact he_own l (by simp [exprLocs, hls])
    · exact he_own l (by simp [exprLocs, exprLocsArms, hla])
  | makeDataStep hs =>
    cases ht with
    | makeData _ hts =>
      simp only [exprLocs] at he_own ⊢
      exact stepList_preserves_ownership hΦ hts hs htasks hlen he_own hstore_own
  | makeDataTrap _ =>
    exact ⟨owners, OwnersExtend.refl _, hlen, (fun _ h => nomatch h), hstore_own, (fun _ h => nomatch h)⟩
  | getTagStep hs =>
    cases ht with
    | getTag h1 =>
      simp only [exprLocs] at he_own ⊢
      exact step_preserves_ownership hΦ h1 hs htasks hlen he_own hstore_own
  | getTagTrap =>
    exact ⟨owners, OwnersExtend.refl _, hlen, (fun _ h => nomatch h), hstore_own, (fun _ h => nomatch h)⟩
  | getTagVal _ =>
    exact ⟨owners, OwnersExtend.refl _, hlen, (fun _ h => nomatch h), hstore_own, (fun _ h => nomatch h)⟩
  | cellNewStep hs =>
    cases ht with
    | cellNew h1 =>
      simp only [exprLocs] at he_own ⊢
      exact step_preserves_ownership hΦ h1 hs htasks hlen he_own hstore_own
  | cellNewTrap =>
    exact ⟨owners, OwnersExtend.refl _, hlen, (fun _ h => nomatch h), hstore_own, (fun _ h => nomatch h)⟩
  | @cellNewVal v _ =>
    refine ⟨owners ++ [tid], OwnersExtend.append owners tid, by simp [hlen], ?_, ?_, (fun _ h => nomatch h)⟩
    · intro l hl
      simp only [exprLocs, List.mem_singleton] at hl
      subst hl
      rw [← hlen]
      simp
    · intro l w l' hw hl'
      cases Nat.lt_or_ge l σ.length with
      | inl hlt =>
        rw [List.getElem?_append_left hlt] at hw
        have hlt_o : l < owners.length := hlen ▸ hlt
        have heq_base := hstore_own l w l' hw hl'
        have hl_some : owners[l]? = some owners[l] := List.getElem?_eq_getElem hlt_o
        rw [hl_some] at heq_base
        have hlt_o' : l' < owners.length := lt_length_of_getElem?_eq_some heq_base
        rw [List.getElem?_append_left hlt_o', List.getElem?_append_left hlt_o, heq_base, hl_some]
      | inr hge =>
        rw [List.getElem?_append_right hge] at hw
        have hlt1 : l - σ.length < 1 := by simpa using lt_length_of_getElem?_eq_some hw
        have heql : l = σ.length := Nat.le_antisymm (Nat.le_of_sub_eq_zero (Nat.lt_one_iff.mp hlt1)) hge
        subst heql
        simp at hw
        subst hw
        have hv_own : owners[l']? = some tid := he_own l' (by simp [exprLocs, hl'])
        have hlt_o' : l' < owners.length := lt_length_of_getElem?_eq_some hv_own
        rw [List.getElem?_append_left hlt_o', hv_own, ← hlen]
        simp
  | cellGetStep hs =>
    cases ht with
    | cellGet h1 _ =>
      simp only [exprLocs] at he_own ⊢
      exact step_preserves_ownership hΦ h1 hs htasks hlen he_own hstore_own
  | cellGetTrap =>
    exact ⟨owners, OwnersExtend.refl _, hlen, (fun _ h => nomatch h), hstore_own, (fun _ h => nomatch h)⟩
  | cellGetVal hvσ =>
    refine ⟨owners, OwnersExtend.refl _, hlen, ?_, hstore_own, (fun _ h => nomatch h)⟩
    intro l' hl'
    exact (hstore_own _ e' l' hvσ hl').trans (he_own _ (by simp [exprLocs]))
  | cellSetLeft hs =>
    cases ht with
    | cellSet h1 _ =>
      rcases step_preserves_ownership hΦ h1 hs htasks hlen
        (fun l hl => he_own l (by simp [exprLocs, hl])) hstore_own with
        ⟨owners', hext, hlen', he1', hst', hsp⟩
      refine ⟨owners', hext, hlen', ?_, hst', hsp⟩
      intro l hl
      simp only [exprLocs, List.mem_append] at hl
      rcases hl with hl1 | hl2
      · exact he1' l hl1
      · exact hext l tid (he_own l (by simp [exprLocs, hl2]))
  | cellSetLeftTrap =>
    exact ⟨owners, OwnersExtend.refl _, hlen, (fun _ h => nomatch h), hstore_own, (fun _ h => nomatch h)⟩
  | cellSetRight _ hs =>
    cases ht with
    | cellSet _ h2 =>
      rcases step_preserves_ownership hΦ h2 hs htasks hlen
        (fun l hl => he_own l (by simp [exprLocs, hl])) hstore_own with
        ⟨owners', hext, hlen', he2', hst', hsp⟩
      refine ⟨owners', hext, hlen', ?_, hst', hsp⟩
      intro l hl
      simp only [exprLocs, List.mem_append] at hl
      rcases hl with hl1 | hl2
      · exact hext l tid (he_own l (by simp [exprLocs, hl1]))
      · exact he2' l hl2
  | cellSetRightTrap _ =>
    exact ⟨owners, OwnersExtend.refl _, hlen, (fun _ h => nomatch h), hstore_own, (fun _ h => nomatch h)⟩
  | @cellSetVal l v _ hlt _ =>
    refine ⟨owners, OwnersExtend.refl _, by simp [hlen], (fun _ h => nomatch h), ?_, (fun _ h => nomatch h)⟩
    intro k w l' hk hl'
    by_cases hkl : k = l
    · subst hkl
      simp only [List.getElem?_set_self hlt, Option.some.injEq] at hk
      subst hk
      have hl_own : owners[k]? = some tid := he_own k (by simp [exprLocs])
      have hv_own : owners[l']? = some tid := he_own l' (by simp [exprLocs, hl'])
      rw [hv_own, hl_own]
    · rw [List.getElem?_set_ne (Ne.symm hkl)] at hk
      exact hstore_own k w l' hk hl'
  | spawnStep hs =>
    cases ht with
    | spawn h1 _ _ =>
      simp only [exprLocs] at he_own ⊢
      exact step_preserves_ownership hΦ h1 hs htasks hlen he_own hstore_own
  | spawnTrap =>
    exact ⟨owners, OwnersExtend.refl _, hlen, (fun _ h => nomatch h), hstore_own, (fun _ h => nomatch h)⟩
  | spawnBeta =>
    refine ⟨owners, OwnersExtend.refl _, hlen, (fun _ h => nomatch h), hstore_own, ?_⟩
    intro b hb
    cases hb
    cases ht with
    | spawn hfn _ _ =>
      cases hfn with
      | lam _ _ _ _ hsh => exact (hsh rfl).2
  | awaitStep hs =>
    cases ht with
    | await h1 _ _ =>
      simp only [exprLocs] at he_own ⊢
      exact step_preserves_ownership hΦ h1 hs htasks hlen he_own hstore_own
  | awaitTrap =>
    exact ⟨owners, OwnersExtend.refl _, hlen, (fun _ h => nomatch h), hstore_own, (fun _ h => nomatch h)⟩
  | awaitVal het hv =>
    refine ⟨owners, OwnersExtend.refl _, hlen, ?_, hstore_own, (fun _ h => nomatch h)⟩
    cases ht with
    | await href _ _ =>
      cases href with
      | taskRef htid hsend0 _ =>
        rcases htasks.2 _ _ htid with ⟨et', het', hetTy⟩
        rw [het] at het'; cases het'
        have hvlocs := exprLocs_empty_of_isValue_isSend hetTy hv hsend0
        intro l hl
        rw [hvlocs] at hl
        cases hl
  | awaitTaskTrap _ =>
    exact ⟨owners, OwnersExtend.refl _, hlen, (fun _ h => nomatch h), hstore_own, (fun _ h => nomatch h)⟩
termination_by sizeOf e

theorem stepList_preserves_ownership {Δ : AdtEnv} {Φ : FunEnv} (hΦ : FunEnvTyped Δ Φ)
    {Ψ : StoreTy} {Θ : TaskTy} {tasks : List Expr}
    {es : List Expr} {σ : Store} {es' : List Expr} {σ' : Store} {sp : Option Expr} {τs : List Ty}
    {owners : List Nat} {tid : Nat}
    (hts : HasTypes Δ Φ Ψ Θ emptyCtx es τs)
    (hstep : StepList Δ Φ tasks es σ es' σ' sp)
    (htasks : TasksTyped Δ Φ Ψ Θ tasks)
    (hlen : owners.length = σ.length)
    (hes_own : ∀ l ∈ exprLocsList es, owners[l]? = some tid)
    (hstore_own : ∀ (l : Loc) (v : Expr) (l' : Loc), σ[l]? = some v → l' ∈ exprLocs v → owners[l']? = owners[l]?) :
    ∃ owners',
      OwnersExtend owners owners' ∧
      owners'.length = σ'.length ∧
      (∀ l ∈ exprLocsList es', owners'[l]? = some tid) ∧
      (∀ (l : Loc) (v : Expr) (l' : Loc), σ'[l]? = some v → l' ∈ exprLocs v → owners'[l']? = owners'[l]?) ∧
      (∀ body, sp = some body → exprLocs body = []) := by
  cases hstep with
  | head hs =>
    cases hts with
    | cons h1 _ =>
      rcases step_preserves_ownership hΦ h1 hs htasks hlen
        (fun l hl => hes_own l (by simp [exprLocsList, hl])) hstore_own with
        ⟨owners', hext, hlen', he1', hst', hsp⟩
      refine ⟨owners', hext, hlen', ?_, hst', hsp⟩
      intro l hl
      simp only [exprLocsList, List.mem_append] at hl
      rcases hl with hl1 | hlr
      · exact he1' l hl1
      · exact hext l tid (hes_own l (by simp [exprLocsList, hlr]))
  | tail _ hs =>
    cases hts with
    | cons _ hrest =>
      rcases stepList_preserves_ownership hΦ hrest hs htasks hlen
        (fun l hl => hes_own l (by simp [exprLocsList, hl])) hstore_own with
        ⟨owners', hext, hlen', her', hst', hsp⟩
      refine ⟨owners', hext, hlen', ?_, hst', hsp⟩
      intro l hl
      simp only [exprLocsList, List.mem_append] at hl
      rcases hl with hl1 | hlr
      · exact hext l tid (hes_own l (by simp [exprLocsList, hl1]))
      · exact her' l hlr
termination_by sizeOf es
end

/-! ## Concurrent Pool Invariant Preservation (`ConcStep` & `ConcSteps`) -/

/-- Combined concurrent configuration invariant: well-typed store, well-typed
    task pool, and strict per-thread heap ownership partition. -/
def ConcInv (Δ : AdtEnv) (Φ : FunEnv) (tasks : List Expr) (σ : Store) : Prop :=
  ∃ (Ψ : StoreTy) (Θ : TaskTy) (owners : List Nat),
    StoreTyped Δ Φ Ψ Θ σ ∧
    TasksTyped Δ Φ Ψ Θ tasks ∧
    HeapOwned owners tasks σ

theorem concStep_preserves_inv {Δ : AdtEnv} {Φ : FunEnv} (hΦ : FunEnvTyped Δ Φ)
    {tasks tasks' : List Expr} {σ σ' : Store}
    (hinv : ConcInv Δ Φ tasks σ)
    (hstep : ConcStep Δ Φ tasks σ tasks' σ') :
    ConcInv Δ Φ tasks' σ' := by
  rcases hinv with ⟨Ψ, Θ, owners, hσ, htasks, hown⟩
  match hstep with
  | .stepNone (tid := tid) (e := e) (e' := e') het hs =>
    have hlt_t : tid < tasks.length := lt_length_of_getElem?_eq_some het
    have hlt_Θ : tid < Θ.length := htasks.1 ▸ hlt_t
    have hΘ_some : Θ[tid]? = some Θ[tid] := List.getElem?_eq_getElem hlt_Θ
    rcases htasks.2 tid Θ[tid] hΘ_some with ⟨e0, he0, hetTy⟩
    rw [het] at he0; cases he0
    rcases preservation hΦ hetTy hs hσ htasks with ⟨Ψ', Θ', hsExt, hsp, hetTy', hσ'⟩
    simp only [SpawnTyped] at hsp
    subst hsp
    have he_own : ∀ l ∈ exprLocs e, owners[l]? = some tid :=
      fun l hl => hown.task_locs tid e l het hl
    rcases step_preserves_ownership hΦ hetTy hs htasks hown.len_eq he_own hown.store_locs with
      ⟨owners', hownExt, hlen', he_own', hst_own', _⟩
    refine ⟨Ψ', Θ', owners', hσ', ?_, ?_⟩
    · refine ⟨by simp [htasks.1], fun k τk hk => ?_⟩
      by_cases hkt : k = tid
      · subst hkt
        rw [hΘ_some] at hk; cases hk
        exact ⟨e', List.getElem?_set_self hlt_t, hetTy'⟩
      · rcases htasks.2 k τk hk with ⟨ek, hek, hekTy⟩
        refine ⟨ek, ?_, typing_env_weaken hsExt (TaskExtends.refl Θ') hekTy⟩
        rw [List.getElem?_set_ne (Ne.symm hkt)]
        exact hek
    · refine ⟨hlen', fun k ek l hek hl => ?_, hst_own'⟩
      by_cases hkt : k = tid
      · subst hkt
        rw [List.getElem?_set_self hlt_t] at hek
        cases hek
        exact he_own' l hl
      · rw [List.getElem?_set_ne (Ne.symm hkt)] at hek
        exact hownExt l k (hown.task_locs k ek l hek hl)
  | .stepSpawn (tid := tid) (e := e) (e' := e') (spawned := spawned) het hs =>
    have hlt_t : tid < tasks.length := lt_length_of_getElem?_eq_some het
    have hlt_Θ : tid < Θ.length := htasks.1 ▸ hlt_t
    have hΘ_some : Θ[tid]? = some Θ[tid] := List.getElem?_eq_getElem hlt_Θ
    rcases htasks.2 tid Θ[tid] hΘ_some with ⟨e0, he0, hetTy⟩
    rw [het] at he0; cases he0
    rcases preservation hΦ hetTy hs hσ htasks with ⟨Ψ', Θ', hsExt, hsp, hetTy', hσ'⟩
    rcases hsp with ⟨τsp, rfl, _, hspTy⟩
    have htkExt : TaskExtends Θ (Θ ++ [τsp]) := TaskExtends.append Θ τsp
    have he_own : ∀ l ∈ exprLocs e, owners[l]? = some tid :=
      fun l hl => hown.task_locs tid e l het hl
    rcases step_preserves_ownership hΦ hetTy hs htasks hown.len_eq he_own hown.store_locs with
      ⟨owners', hownExt, hlen', he_own', hst_own', hspLocs⟩
    refine ⟨Ψ', Θ ++ [τsp], owners', hσ', ?_, ?_⟩
    · refine ⟨by simp [htasks.1], fun k τk hk => ?_⟩
      cases Nat.lt_or_ge k Θ.length with
      | inl hlt_k =>
        rw [List.getElem?_append_left hlt_k] at hk
        have hlt_set : k < (tasks.set tid e').length := by simp [htasks.1, hlt_k]
        by_cases hkt : k = tid
        · subst hkt
          rw [hΘ_some] at hk; cases hk
          refine ⟨e', ?_, hetTy'⟩
          rw [List.getElem?_append_left hlt_set, List.getElem?_set_self hlt_t]
        · rcases htasks.2 k τk hk with ⟨ek, hek, hekTy⟩
          refine ⟨ek, ?_, typing_env_weaken hsExt htkExt hekTy⟩
          rw [List.getElem?_append_left hlt_set, List.getElem?_set_ne (Ne.symm hkt)]
          exact hek
      | inr hge_k =>
        rw [List.getElem?_append_right hge_k] at hk
        have hlt1 : k - Θ.length < 1 := by simpa using lt_length_of_getElem?_eq_some hk
        have heqk : k = Θ.length := Nat.le_antisymm (Nat.le_of_sub_eq_zero (Nat.lt_one_iff.mp hlt1)) hge_k
        subst heqk
        simp at hk
        subst hk
        refine ⟨spawned, ?_, hspTy⟩
        have hlen_set : (tasks.set tid e').length = Θ.length := by simp [htasks.1]
        rw [← hlen_set]
        simp
    · refine ⟨hlen', fun k ek l hek hl => ?_, hst_own'⟩
      cases Nat.lt_or_ge k (tasks.set tid e').length with
      | inl hlt_k =>
        rw [List.getElem?_append_left hlt_k] at hek
        by_cases hkt : k = tid
        · subst hkt
          rw [List.getElem?_set_self hlt_t] at hek
          cases hek
          exact he_own' l hl
        · rw [List.getElem?_set_ne (Ne.symm hkt)] at hek
          exact hownExt l k (hown.task_locs k ek l hek hl)
      | inr hge_k =>
        rw [List.getElem?_append_right hge_k] at hek
        have hlt1 : k - (tasks.set tid e').length < 1 := by simpa using lt_length_of_getElem?_eq_some hek
        have heqk : k = (tasks.set tid e').length :=
          Nat.le_antisymm (Nat.le_of_sub_eq_zero (Nat.lt_one_iff.mp hlt1)) hge_k
        subst heqk
        simp at hek
        subst hek
        rw [hspLocs spawned rfl] at hl
        cases hl

theorem concSteps_preserves_inv {Δ : AdtEnv} {Φ : FunEnv} (hΦ : FunEnvTyped Δ Φ)
    {t0 tasks : List Expr} {σ0 σ : Store}
    (hinv0 : ConcInv Δ Φ t0 σ0)
    (hsteps : ConcSteps Δ Φ t0 σ0 tasks σ) :
    ConcInv Δ Φ tasks σ := by
  induction hsteps with
  | refl => exact hinv0
  | trans hs _ ih => exact ih (concStep_preserves_inv hΦ hinv0 hs)

/-! ## Top-Level Concurrent Safety, Heap Disjointness & Data-Race Freedom -/

/-- Initial 1-thread configuration `[e0]` on empty heap `[]` satisfies `ConcInv`. -/
theorem concInv_init {Δ : AdtEnv} {Φ : FunEnv} {e0 : Expr} {τ0 : Ty}
    (ht0 : HasType Δ Φ [] [] emptyCtx e0 τ0) :
    ConcInv Δ Φ [e0] [] := by
  have he0_locs : exprLocs e0 = [] := exprLocs_empty_of_empty_store ht0
  have hextT : TaskExtends [] [τ0] := TaskExtends.append [] τ0
  have ht0' : HasType Δ Φ [] [τ0] emptyCtx e0 τ0 :=
    typing_env_weaken (StoreExtends.refl []) hextT ht0
  refine ⟨[], [τ0], [], ?_, ?_, ?_⟩
  · exact ⟨rfl, fun _ _ h => by simp at h⟩
  · refine ⟨rfl, fun tid τ htid => ?_⟩
    cases tid with
    | zero =>
      simp at htid; subst htid
      exact ⟨e0, rfl, ht0'⟩
    | succ n => simp at htid
  · refine ⟨rfl, fun tid e l het hl => ?_, fun _ _ _ h => by simp at h⟩
    cases tid with
    | zero =>
      simp at het; subst het
      rw [he0_locs] at hl; cases hl
    | succ n => simp at het

/-- **Concurrent Type Safety**: Across any arbitrary interleaving of spawned
    tasks (`ConcSteps`), NO thread in `tasks` ever reaches an undefined/stuck
    state (`¬ IsStuck`). -/
theorem conc_type_safety {Δ : AdtEnv} {Φ : FunEnv} {e0 : Expr} {τ0 : Ty}
    {tasks : List Expr} {σ : Store}
    (hΦ : FunEnvTyped Δ Φ)
    (ht0 : HasType Δ Φ [] [] emptyCtx e0 τ0)
    (hsteps : ConcSteps Δ Φ [e0] [] tasks σ) :
    ∀ (tid : Nat) (e : Expr), tasks[tid]? = some e → ¬ IsStuck Δ Φ tasks e σ := by
  rcases concSteps_preserves_inv hΦ (concInv_init ht0) hsteps with ⟨Ψ, Θ, _, hσ, htasks, _⟩
  intro tid e het ⟨hnt, hnblk, hns⟩
  have hlt_t : tid < tasks.length := lt_length_of_getElem?_eq_some het
  have hlt_Θ : tid < Θ.length := htasks.1 ▸ hlt_t
  rcases htasks.2 tid Θ[tid] (List.getElem?_eq_getElem hlt_Θ) with ⟨e1, he1, heTy⟩
  rw [het] at he1; cases he1
  rcases progress hΦ heTy hσ htasks with hterm | hblk | hs
  · exact hnt hterm
  · exact hnblk hblk
  · exact hns hs

/-- **Global Heap Location Disjointness**: At every reachable concurrent
    configuration, any two distinct threads `i ≠ j` have strictly disjoint sets
    of reachable `Cell` heap locations. -/
theorem conc_heap_disjoint {Δ : AdtEnv} {Φ : FunEnv} {e0 : Expr} {τ0 : Ty}
    {tasks : List Expr} {σ : Store}
    (hΦ : FunEnvTyped Δ Φ)
    (ht0 : HasType Δ Φ [] [] emptyCtx e0 τ0)
    (hsteps : ConcSteps Δ Φ [e0] [] tasks σ) :
    ∀ (i j : Nat) (ei ej : Expr) (l : Loc),
      i ≠ j →
      tasks[i]? = some ei →
      tasks[j]? = some ej →
      l ∈ exprLocs ei →
      l ∉ exprLocs ej := by
  rcases concSteps_preserves_inv hΦ (concInv_init ht0) hsteps with ⟨_, _, owners, _, _, hown⟩
  intro i j ei ej l hij hei hej hli hlj
  have hoi : owners[l]? = some i := hown.task_locs i ei l hei hli
  have hoj : owners[l]? = some j := hown.task_locs j ej l hej hlj
  rw [hoi] at hoj
  cases hoj
  exact hij rfl

/-- **Compile-Time Data-Race Freedom Theorem**: Well-typed Core Geisha programs
    are completely free of `Cell` data races (`¬ HasDataRace tasks`) across all
    possible concurrent thread interleavings. -/
theorem conc_data_race_freedom {Δ : AdtEnv} {Φ : FunEnv} {e0 : Expr} {τ0 : Ty}
    {tasks : List Expr} {σ : Store}
    (hΦ : FunEnvTyped Δ Φ)
    (ht0 : HasType Δ Φ [] [] emptyCtx e0 τ0)
    (hsteps : ConcSteps Δ Φ [e0] [] tasks σ) :
    ¬ HasDataRace tasks := by
  intro ⟨i, j, ei, ej, b1, b2, l, hij, hei, hej, ha1, ha2, _⟩
  exact conc_heap_disjoint hΦ ht0 hsteps i j ei ej l hij hei hej
    (activeCellAccess_mem_exprLocs ei ha1)
    (activeCellAccess_mem_exprLocs ej ha2)

end CoreGeisha
