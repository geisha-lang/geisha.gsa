import CoreGeisha.Syntax
import CoreGeisha.Typing
import CoreGeisha.Semantics
import CoreGeisha.Soundness

/-!
# Core Geisha: Full Concurrent Type Safety (`Task` + `MVar` + `Chan` + `Actor`) & Data-Race Freedom

Machine-checked proof (zero `sorry`) that Core Geisha's phantom capture-mode
system (`Mode.local` vs `Mode.shared`), `IsSend` discipline, synchronized
channels/boxes (`Chan`, `MVar`), and thread-pinned sequential `Actor`s
encapsulating `!Send` mutable state enforce **strict per-thread heap isolation**
across arbitrary interleaved executions (`ConcSteps`):

1. **Concurrent Pool Preservation & Progress** (`concStep_preserves_inv`, `conc_type_safety`, `conc_actor_safety`):
   Every `Task` and sequential `Actor` in a reachable `ConcPool` remains closed,
   well-typed, and never enters an undefined/stuck state.
2. **Global Heap Ownership Partition** (`HeapOwned`, `step_preserves_ownership`, `applyConcEff_owned`):
   Every allocated `Cell` location `l < σ.length` has a unique owning `ThreadId`
   (`.task tid` or `.actor aid`); `MVar`s, `Chan`s, `Task` results, `spawn`
   closures, and `Actor` mailbox handlers carry ZERO `Cell` locations across
   threads (`exprLocs = []`), while an `Actor s` safely mutates `!Send` `Cell`s
   owned exclusively by `.actor aid` inside its sequential mailbox loop.
3. **Compile-Time Data-Race Freedom** (`conc_heap_disjoint`, `conc_data_race_freedom`):
   No two distinct threads (Task-Task, Task-Actor, or Actor-Actor) ever reach or
   concurrently access the same mutable `Cell` (`¬ HasDataRace pool`).
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
  | _, _, .concPrimArgs hs => by
    simp only [exprLocs]
    exact activeCellAccessList_mem_exprLocs _ hs
termination_by e => sizeOf e

theorem activeCellAccessList_mem_exprLocs {b : Bool} :
    (es : List Expr) → ∀ {l : Loc}, ActiveCellAccessList b es l → l ∈ exprLocsList es
  | _, _, .head hs => by simp [exprLocsList, activeCellAccess_mem_exprLocs _ hs]
  | _, _, .tail _ hs => by simp [exprLocsList, activeCellAccessList_mem_exprLocs _ hs]
termination_by es => sizeOf es
end

/-- Non-vacuity witness: if a Task and an Actor (or two Tasks) both held `.loc 0`
    with one writing and one reading, `HasDataRace` would hold. -/
theorem hasDataRace_nonvacuous :
    HasDataRace
      { tasks := [.running (.cellSet (.loc 0) (.lit (.int 1)))]
        actors := [{ phase := .init (.cellGet (.loc 0)), mailbox := [] }] } := by
  refine ⟨.task 0, .actor 0, .cellSet (.loc 0) (.lit (.int 1)), .cellGet (.loc 0),
    true, false, 0, by decide, rfl, rfl, .write 0 rfl (.lit _), .read 0 rfl, Or.inl rfl⟩

/-! ## Heap Ownership Partition Invariant (`HeapOwned`) -/

/-- Thread-exclusive heap ownership partition across all `Task`s, `Actor`s, `MVar`s, and `Chan`s:
    - Every allocated `Cell` `l < σ.length` has a unique owner `owners[l] : ThreadId`.
    - Every `Loc` inside running task `tid` is owned by `.task tid`.
    - Every `Loc` inside actor `aid`'s state/active expression is owned by `.actor aid`,
      and every handler waiting in `aid`'s mailbox embeds ZERO `Loc`s.
    - Every value buffered inside any `MVar` or `Chan` embeds ZERO `Loc`s.
    - Every `Loc` stored inside heap cell `σ[l]` belongs to the same owner as `l`. -/
structure HeapOwned (owners : List ThreadId) (pool : ConcPool) (σ : Store) : Prop where
  len_eq     : owners.length = σ.length
  task_locs  : ∀ (tid : TaskId) (e : Expr) (l : Loc),
    pool.tasks[tid]? = some (.running e) → l ∈ exprLocs e → owners[l]? = some (.task tid)
  actor_locs : ∀ (aid : Nat) (act : ActorState),
    pool.actors[aid]? = some act →
    (∀ l ∈ actorPhaseLocs act.phase, owners[l]? = some (.actor aid)) ∧
    (∀ msg ∈ act.mailbox, exprLocs msg.handler = [])
  mvar_locs  : ∀ (mid : Nat) (v : Expr),
    pool.mvars[mid]? = some (some v) → exprLocs v = []
  chan_locs  : ∀ (cid : Nat) (ch : ChanState) (v : Expr),
    pool.chans[cid]? = some ch → v ∈ ch.buf → exprLocs v = []
  store_locs : ∀ (l : Loc) (v : Expr) (l' : Loc),
    σ[l]? = some v → l' ∈ exprLocs v → owners[l']? = owners[l]?

/-- Monotone extension of thread ownership list as new `Cell`s are allocated. -/
def OwnersExtend (o1 o2 : List ThreadId) : Prop :=
  ∀ (l : Loc) (th : ThreadId), o1[l]? = some th → o2[l]? = some th

theorem OwnersExtend.refl (o : List ThreadId) : OwnersExtend o o :=
  fun _ _ h => h

theorem OwnersExtend.append (o : List ThreadId) (th : ThreadId) : OwnersExtend o (o ++ [th]) := by
  intro l t hl
  have hlt : l < o.length := lt_length_of_getElem?_eq_some hl
  rw [List.getElem?_append_left hlt]
  exact hl

/-- Zero-location transfer property of any cross-thread `ConcEff` emitted by `Step`. -/
def EffLocsClean : ConcEff → Prop
  | .none => True
  | .spawnTask body => exprLocs body = []
  | .allocMVar init => ∀ v, init = some v → exprLocs v = []
  | .takeMVar _ => True
  | .putMVar _ val => exprLocs val = []
  | .allocChan _ => True
  | .sendChan _ val => exprLocs val = []
  | .recvChan _ => True
  | .closeChan _ => True
  | .spawnActor initExpr => exprLocs initExpr = []
  | .callActor _ handler => exprLocs handler = []
  | .sendActor _ handler => exprLocs handler = []

theorem isSend_fnShared (Δ : AdtEnv) (ps : List Ty) (ret : Ty) :
    IsSend Δ (.fn .shared ps ret) := by
  refine ⟨fun _ => False, ?_, TySendIn.fnShared ps ret⟩
  intro _ h; cases h

/-! ## Single-Step Ownership Preservation -/

mutual
theorem step_preserves_ownership {Δ : AdtEnv} {Φ : FunEnv} (hΦ : FunEnvTyped Δ Φ)
    {Ψ : StoreTy} {Θ : TaskTy} {pool : ConcPool}
    {e : Expr} {σ : Store} {e' : Expr} {σ' : Store} {eff : ConcEff} {τ : Ty}
    {owners : List ThreadId} {th : ThreadId}
    (ht : HasType Δ Φ Ψ Θ emptyCtx e τ)
    (hstep : Step Δ Φ pool e σ e' σ' eff)
    (hpool : PoolTyped Δ Φ Ψ Θ pool)
    (hmvar_locs : ∀ (mid : Nat) (v : Expr), pool.mvars[mid]? = some (some v) → exprLocs v = [])
    (hchan_locs : ∀ (cid : Nat) (ch : ChanState) (v : Expr), pool.chans[cid]? = some ch → v ∈ ch.buf → exprLocs v = [])
    (hlen : owners.length = σ.length)
    (he_own : ∀ l ∈ exprLocs e, owners[l]? = some th)
    (hstore_own : ∀ (l : Loc) (v : Expr) (l' : Loc), σ[l]? = some v → l' ∈ exprLocs v → owners[l']? = owners[l]?) :
    ∃ owners',
      OwnersExtend owners owners' ∧
      owners'.length = σ'.length ∧
      (∀ l ∈ exprLocs e', owners'[l]? = some th) ∧
      (∀ (l : Loc) (v : Expr) (l' : Loc), σ'[l]? = some v → l' ∈ exprLocs v → owners'[l']? = owners'[l]?) ∧
      EffLocsClean eff := by
  cases hstep with
  | tupleStep hs =>
    cases ht with
    | tuple hts =>
      simp only [exprLocs] at he_own ⊢
      exact stepList_preserves_ownership hΦ hts hs hpool hmvar_locs hchan_locs hlen he_own hstore_own
  | tupleTrap _ =>
    exact ⟨owners, OwnersExtend.refl _, hlen, (fun _ h => nomatch h), hstore_own, trivial⟩
  | blockEmpty =>
    exact ⟨owners, OwnersExtend.refl _, hlen, (fun _ h => nomatch h), hstore_own, trivial⟩
  | blockSingle =>
    refine ⟨owners, OwnersExtend.refl _, hlen, ?_, hstore_own, trivial⟩
    intro l hl
    apply he_own l
    simp [exprLocs, exprLocsList, hl]
  | blockConsStep hs =>
    cases ht with
    | blockCons h1 _ =>
      rcases step_preserves_ownership hΦ h1 hs hpool hmvar_locs hchan_locs hlen
        (fun l hl => he_own l (by simp [exprLocs, exprLocsList, hl])) hstore_own with
        ⟨owners', hext, hlen', he1', hst', hclean⟩
      refine ⟨owners', hext, hlen', ?_, hst', hclean⟩
      intro l hl
      simp only [exprLocs, exprLocsList, List.mem_append] at hl
      rcases hl with hl1 | hlrest
      · exact he1' l hl1
      · exact hext l th (he_own l (by simp [exprLocs, exprLocsList, hlrest]))
  | blockConsVal _ =>
    refine ⟨owners, OwnersExtend.refl _, hlen, ?_, hstore_own, trivial⟩
    intro l hl
    apply he_own l
    simp only [exprLocs, exprLocsList, List.mem_append] at hl ⊢
    exact Or.inr hl
  | blockConsTrap =>
    exact ⟨owners, OwnersExtend.refl _, hlen, (fun _ h => nomatch h), hstore_own, trivial⟩
  | applyFn hs =>
    cases ht with
    | apply hfn _ _ =>
      rcases step_preserves_ownership hΦ hfn hs hpool hmvar_locs hchan_locs hlen
        (fun l hl => he_own l (by simp [exprLocs, hl])) hstore_own with
        ⟨owners', hext, hlen', he1', hst', hclean⟩
      refine ⟨owners', hext, hlen', ?_, hst', hclean⟩
      intro l hl
      simp only [exprLocs, List.mem_append] at hl
      rcases hl with h1 | h2
      · exact he1' l h1
      · exact hext l th (he_own l (by simp [exprLocs, h2]))
  | applyFnTrap =>
    exact ⟨owners, OwnersExtend.refl _, hlen, (fun _ h => nomatch h), hstore_own, trivial⟩
  | applyArgs _ hs =>
    cases ht with
    | apply _ hargs _ =>
      rcases stepList_preserves_ownership hΦ hargs hs hpool hmvar_locs hchan_locs hlen
        (fun l hl => he_own l (by simp [exprLocs, hl])) hstore_own with
        ⟨owners', hext, hlen', he2', hst', hclean⟩
      refine ⟨owners', hext, hlen', ?_, hst', hclean⟩
      intro l hl
      simp only [exprLocs, List.mem_append] at hl
      rcases hl with h1 | h2
      · exact hext l th (he_own l (by simp [exprLocs, h1]))
      · exact he2' l h2
  | applyArgsTrap _ _ =>
    exact ⟨owners, OwnersExtend.refl _, hlen, (fun _ h => nomatch h), hstore_own, trivial⟩
  | applyBeta _ _ =>
    refine ⟨owners, OwnersExtend.refl _, hlen, ?_, hstore_own, trivial⟩
    intro l hl
    rcases mem_exprLocs_substMany hl with hbody | ⟨x, u, hmem, hlu⟩
    · exact he_own l (by simp [exprLocs, hbody])
    · exact he_own l (by simp [exprLocs, zipParams_mem_locs hmem hlu])
  | applyDirArgs hs =>
    cases ht with
    | applyDir _ hargs _ =>
      simp only [exprLocs] at he_own ⊢
      exact stepList_preserves_ownership hΦ hargs hs hpool hmvar_locs hchan_locs hlen he_own hstore_own
  | applyDirTrap _ =>
    exact ⟨owners, OwnersExtend.refl _, hlen, (fun _ h => nomatch h), hstore_own, trivial⟩
  | applyDirBeta hf _ _ =>
    refine ⟨owners, OwnersExtend.refl _, hlen, ?_, hstore_own, trivial⟩
    intro l hl
    have hfd := exprLocs_empty_of_empty_store (hΦ _ _ hf)
    rcases mem_exprLocs_substMany hl with hbody | ⟨x, u, hmem, hlu⟩
    · rw [hfd] at hbody; cases hbody
    · exact he_own l (by simp [exprLocs, zipParams_mem_locs hmem hlu])
  | unStep hs =>
    cases ht with
    | un _ h1 =>
      simp only [exprLocs] at he_own ⊢
      exact step_preserves_ownership hΦ h1 hs hpool hmvar_locs hchan_locs hlen he_own hstore_own
  | unTrap =>
    exact ⟨owners, OwnersExtend.refl _, hlen, (fun _ h => nomatch h), hstore_own, trivial⟩
  | unVal _ =>
    exact ⟨owners, OwnersExtend.refl _, hlen, (fun _ h => nomatch h), hstore_own, trivial⟩
  | binLeft hs =>
    cases ht with
    | bin _ h1 _ =>
      rcases step_preserves_ownership hΦ h1 hs hpool hmvar_locs hchan_locs hlen
        (fun l hl => he_own l (by simp [exprLocs, hl])) hstore_own with
        ⟨owners', hext, hlen', he1', hst', hclean⟩
      refine ⟨owners', hext, hlen', ?_, hst', hclean⟩
      intro l hl
      simp only [exprLocs, List.mem_append] at hl
      rcases hl with hl1 | hl2
      · exact he1' l hl1
      · exact hext l th (he_own l (by simp [exprLocs, hl2]))
  | binLeftTrap =>
    exact ⟨owners, OwnersExtend.refl _, hlen, (fun _ h => nomatch h), hstore_own, trivial⟩
  | binAndFalse =>
    exact ⟨owners, OwnersExtend.refl _, hlen, (fun _ h => nomatch h), hstore_own, trivial⟩
  | binAndTrue =>
    refine ⟨owners, OwnersExtend.refl _, hlen, ?_, hstore_own, trivial⟩
    intro l hl; exact he_own l (by simp [exprLocs, hl])
  | binOrTrue =>
    exact ⟨owners, OwnersExtend.refl _, hlen, (fun _ h => nomatch h), hstore_own, trivial⟩
  | binOrFalse =>
    refine ⟨owners, OwnersExtend.refl _, hlen, ?_, hstore_own, trivial⟩
    intro l hl; exact he_own l (by simp [exprLocs, hl])
  | binRight _ _ _ hs =>
    cases ht with
    | bin _ _ h2 =>
      rcases step_preserves_ownership hΦ h2 hs hpool hmvar_locs hchan_locs hlen
        (fun l hl => he_own l (by simp [exprLocs, hl])) hstore_own with
        ⟨owners', hext, hlen', he2', hst', hclean⟩
      refine ⟨owners', hext, hlen', ?_, hst', hclean⟩
      intro l hl
      simp only [exprLocs, List.mem_append] at hl
      rcases hl with hl1 | hl2
      · exact hext l th (he_own l (by simp [exprLocs, hl1]))
      · exact he2' l hl2
  | binRightTrap _ _ _ =>
    exact ⟨owners, OwnersExtend.refl _, hlen, (fun _ h => nomatch h), hstore_own, trivial⟩
  | binVal _ =>
    exact ⟨owners, OwnersExtend.refl _, hlen, (fun _ h => nomatch h), hstore_own, trivial⟩
  | binTrap _ =>
    exact ⟨owners, OwnersExtend.refl _, hlen, (fun _ h => nomatch h), hstore_own, trivial⟩
  | letStep hs =>
    cases ht with
    | let_ h1 _ =>
      rcases step_preserves_ownership hΦ h1 hs hpool hmvar_locs hchan_locs hlen
        (fun l hl => he_own l (by simp [exprLocs, hl])) hstore_own with
        ⟨owners', hext, hlen', he1', hst', hclean⟩
      refine ⟨owners', hext, hlen', ?_, hst', hclean⟩
      intro l hl
      simp only [exprLocs, List.mem_append] at hl
      rcases hl with hl1 | hl2
      · exact he1' l hl1
      · exact hext l th (he_own l (by simp [exprLocs, hl2]))
  | letTrap =>
    exact ⟨owners, OwnersExtend.refl _, hlen, (fun _ h => nomatch h), hstore_own, trivial⟩
  | letVal _ =>
    refine ⟨owners, OwnersExtend.refl _, hlen, ?_, hstore_own, trivial⟩
    intro l hl
    rcases mem_exprLocs_subst _ hl with h2 | h1
    · exact he_own l (by simp [exprLocs, h2])
    · exact he_own l (by simp [exprLocs, h1])
  | ifStep hs =>
    cases ht with
    | if_ hc _ _ =>
      rcases step_preserves_ownership hΦ hc hs hpool hmvar_locs hchan_locs hlen
        (fun l hl => he_own l (by simp [exprLocs, hl])) hstore_own with
        ⟨owners', hext, hlen', hec', hst', hclean⟩
      refine ⟨owners', hext, hlen', ?_, hst', hclean⟩
      intro l hl
      simp only [exprLocs, List.mem_append] at hl
      rcases hl with (hlc | hlt) | hle
      · exact hec' l hlc
      · exact hext l th (he_own l (by simp [exprLocs, hlt]))
      · exact hext l th (he_own l (by simp [exprLocs, hle]))
  | ifTrap =>
    exact ⟨owners, OwnersExtend.refl _, hlen, (fun _ h => nomatch h), hstore_own, trivial⟩
  | ifTrue =>
    refine ⟨owners, OwnersExtend.refl _, hlen, ?_, hstore_own, trivial⟩
    intro l hl; exact he_own l (by simp [exprLocs, hl])
  | ifFalse =>
    refine ⟨owners, OwnersExtend.refl _, hlen, ?_, hstore_own, trivial⟩
    intro l hl; exact he_own l (by simp [exprLocs, hl])
  | whileUnfold =>
    refine ⟨owners, OwnersExtend.refl _, hlen, ?_, hstore_own, trivial⟩
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
      rcases step_preserves_ownership hΦ hscr hs hpool hmvar_locs hchan_locs hlen
        (fun l hl => he_own l (by simp [exprLocs, hl])) hstore_own with
        ⟨owners', hext, hlen', hes', hst', hclean⟩
      refine ⟨owners', hext, hlen', ?_, hst', hclean⟩
      intro l hl
      simp only [exprLocs, List.mem_append] at hl
      rcases hl with hls | hla
      · exact hes' l hls
      · exact hext l th (he_own l (by simp [exprLocs, hla]))
  | matchScrutTrap =>
    exact ⟨owners, OwnersExtend.refl _, hlen, (fun _ h => nomatch h), hstore_own, trivial⟩
  | matchEmpty _ =>
    exact ⟨owners, OwnersExtend.refl _, hlen, (fun _ h => nomatch h), hstore_own, trivial⟩
  | matchHit _ hm =>
    refine ⟨owners, OwnersExtend.refl _, hlen, ?_, hstore_own, trivial⟩
    intro l hl
    rcases mem_exprLocs_substMany hl with hbody | ⟨x, u, hmem, hlu⟩
    · exact he_own l (by simp [exprLocs, exprLocsArms, hbody])
    · exact he_own l (by simp [exprLocs, matchPat_locs hm x u hmem l hlu])
  | matchMiss _ _ =>
    refine ⟨owners, OwnersExtend.refl _, hlen, ?_, hstore_own, trivial⟩
    intro l hl
    simp only [exprLocs, List.mem_append] at hl
    rcases hl with hls | hla
    · exact he_own l (by simp [exprLocs, hls])
    · exact he_own l (by simp [exprLocs, exprLocsArms, hla])
  | makeDataStep hs =>
    cases ht with
    | makeData _ hts =>
      simp only [exprLocs] at he_own ⊢
      exact stepList_preserves_ownership hΦ hts hs hpool hmvar_locs hchan_locs hlen he_own hstore_own
  | makeDataTrap _ =>
    exact ⟨owners, OwnersExtend.refl _, hlen, (fun _ h => nomatch h), hstore_own, trivial⟩
  | getTagStep hs =>
    cases ht with
    | getTag h1 =>
      simp only [exprLocs] at he_own ⊢
      exact step_preserves_ownership hΦ h1 hs hpool hmvar_locs hchan_locs hlen he_own hstore_own
  | getTagTrap =>
    exact ⟨owners, OwnersExtend.refl _, hlen, (fun _ h => nomatch h), hstore_own, trivial⟩
  | getTagVal _ =>
    exact ⟨owners, OwnersExtend.refl _, hlen, (fun _ h => nomatch h), hstore_own, trivial⟩
  | cellNewStep hs =>
    cases ht with
    | cellNew h1 =>
      simp only [exprLocs] at he_own ⊢
      exact step_preserves_ownership hΦ h1 hs hpool hmvar_locs hchan_locs hlen he_own hstore_own
  | cellNewTrap =>
    exact ⟨owners, OwnersExtend.refl _, hlen, (fun _ h => nomatch h), hstore_own, trivial⟩
  | @cellNewVal v _ =>
    refine ⟨owners ++ [th], OwnersExtend.append owners th, by simp [hlen], ?_, ?_, trivial⟩
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
        have hv_own : owners[l']? = some th := he_own l' (by simp [exprLocs, hl'])
        have hlt_o' : l' < owners.length := lt_length_of_getElem?_eq_some hv_own
        rw [List.getElem?_append_left hlt_o', hv_own, ← hlen]
        simp
  | cellGetStep hs =>
    cases ht with
    | cellGet h1 _ =>
      simp only [exprLocs] at he_own ⊢
      exact step_preserves_ownership hΦ h1 hs hpool hmvar_locs hchan_locs hlen he_own hstore_own
  | cellGetTrap =>
    exact ⟨owners, OwnersExtend.refl _, hlen, (fun _ h => nomatch h), hstore_own, trivial⟩
  | cellGetVal hvσ =>
    refine ⟨owners, OwnersExtend.refl _, hlen, ?_, hstore_own, trivial⟩
    intro l' hl'
    exact (hstore_own _ e' l' hvσ hl').trans (he_own _ (by simp [exprLocs]))
  | cellSetLeft hs =>
    cases ht with
    | cellSet h1 _ =>
      rcases step_preserves_ownership hΦ h1 hs hpool hmvar_locs hchan_locs hlen
        (fun l hl => he_own l (by simp [exprLocs, hl])) hstore_own with
        ⟨owners', hext, hlen', he1', hst', hclean⟩
      refine ⟨owners', hext, hlen', ?_, hst', hclean⟩
      intro l hl
      simp only [exprLocs, List.mem_append] at hl
      rcases hl with hl1 | hl2
      · exact he1' l hl1
      · exact hext l th (he_own l (by simp [exprLocs, hl2]))
  | cellSetLeftTrap =>
    exact ⟨owners, OwnersExtend.refl _, hlen, (fun _ h => nomatch h), hstore_own, trivial⟩
  | cellSetRight _ hs =>
    cases ht with
    | cellSet _ h2 =>
      rcases step_preserves_ownership hΦ h2 hs hpool hmvar_locs hchan_locs hlen
        (fun l hl => he_own l (by simp [exprLocs, hl])) hstore_own with
        ⟨owners', hext, hlen', he2', hst', hclean⟩
      refine ⟨owners', hext, hlen', ?_, hst', hclean⟩
      intro l hl
      simp only [exprLocs, List.mem_append] at hl
      rcases hl with hl1 | hl2
      · exact hext l th (he_own l (by simp [exprLocs, hl1]))
      · exact he2' l hl2
  | cellSetRightTrap _ =>
    exact ⟨owners, OwnersExtend.refl _, hlen, (fun _ h => nomatch h), hstore_own, trivial⟩
  | @cellSetVal l v _ hlt _ =>
    refine ⟨owners, OwnersExtend.refl _, by simp [hlen], (fun _ h => nomatch h), ?_, trivial⟩
    intro k w l' hk hl'
    by_cases hkl : k = l
    · subst hkl
      simp only [List.getElem?_set_self hlt, Option.some.injEq] at hk
      subst hk
      have hl_own : owners[k]? = some th := he_own k (by simp [exprLocs])
      have hv_own : owners[l']? = some th := he_own l' (by simp [exprLocs, hl'])
      rw [hv_own, hl_own]
    · rw [List.getElem?_set_ne (Ne.symm hkl)] at hk
      exact hstore_own k w l' hk hl'
  | spawnStep hs =>
    cases ht with
    | spawn h1 _ _ =>
      simp only [exprLocs] at he_own ⊢
      exact step_preserves_ownership hΦ h1 hs hpool hmvar_locs hchan_locs hlen he_own hstore_own
  | spawnTrap =>
    exact ⟨owners, OwnersExtend.refl _, hlen, (fun _ h => nomatch h), hstore_own, trivial⟩
  | spawnBeta =>
    refine ⟨owners, OwnersExtend.refl _, hlen, (fun _ h => nomatch h), hstore_own, ?_⟩
    cases ht with
    | spawn hfn _ _ =>
      cases hfn with
      | lam _ _ _ _ hsh => exact (hsh rfl).2
  | awaitStep hs =>
    cases ht with
    | await h1 _ _ =>
      simp only [exprLocs] at he_own ⊢
      exact step_preserves_ownership hΦ h1 hs hpool hmvar_locs hchan_locs hlen he_own hstore_own
  | awaitTrap =>
    exact ⟨owners, OwnersExtend.refl _, hlen, (fun _ h => nomatch h), hstore_own, trivial⟩
  | awaitVal het hv =>
    refine ⟨owners, OwnersExtend.refl _, hlen, ?_, hstore_own, trivial⟩
    cases ht with
    | await href _ _ =>
      cases href with
      | taskRef htid hsend0 _ =>
        rcases hpool.tasks_ty _ _ htid with ⟨_, te, hte, hrun⟩
        rw [het] at hte; cases hte
        have hvlocs := exprLocs_empty_of_isValue_isSend (hrun _ rfl) hv hsend0
        intro l hl
        rw [hvlocs] at hl
        cases hl
  | awaitTaskTrap _ =>
    exact ⟨owners, OwnersExtend.refl _, hlen, (fun _ h => nomatch h), hstore_own, trivial⟩
  | concPrimArgs hs =>
    cases ht with
    | concPrim _ hargs _ =>
      simp only [exprLocs] at he_own ⊢
      exact stepList_preserves_ownership hΦ hargs hs hpool hmvar_locs hchan_locs hlen he_own hstore_own
  | concPrimTrap _ =>
    exact ⟨owners, OwnersExtend.refl _, hlen, (fun _ h => nomatch h), hstore_own, trivial⟩
  | concPrimVal hprim =>
    cases ht with
    | concPrim hop hargs _ =>
      cases hprim with
      | mvarNew hv =>
        cases hop with
        | mvarNew hsend =>
          cases hargs with
          | cons hvTy hnil =>
            cases hnil
            refine ⟨owners, OwnersExtend.refl _, hlen, (fun _ h => nomatch h), hstore_own, ?_⟩
            intro u hu; cases hu
            exact exprLocs_empty_of_isValue_isSend hvTy hv hsend
      | mvarEmpty _ =>
        exact ⟨owners, OwnersExtend.refl _, hlen, (fun _ h => nomatch h), hstore_own, fun _ h => nomatch h⟩
      | mvarTake hslot =>
        refine ⟨owners, OwnersExtend.refl _, hlen, ?_, hstore_own, trivial⟩
        intro l hl
        rw [hmvar_locs _ _ hslot] at hl
        cases hl
      | mvarPut _ hv =>
        cases hop with
        | mvarPut hsend =>
          cases hargs with
          | cons _ hrest =>
            cases hrest with
            | cons hvTy hnil =>
              cases hnil
              exact ⟨owners, OwnersExtend.refl _, hlen, (fun _ h => nomatch h), hstore_own,
                exprLocs_empty_of_isValue_isSend hvTy hv hsend⟩
      | chanNew _ _ =>
        exact ⟨owners, OwnersExtend.refl _, hlen, (fun _ h => nomatch h), hstore_own, trivial⟩
      | chanSendClosed _ _ _ =>
        exact ⟨owners, OwnersExtend.refl _, hlen, (fun _ h => nomatch h), hstore_own, trivial⟩
      | chanSendOpen _ _ _ hv =>
        cases hop with
        | chanSend hsend =>
          cases hargs with
          | cons _ hrest =>
            cases hrest with
            | cons hvTy hnil =>
              cases hnil
              exact ⟨owners, OwnersExtend.refl _, hlen, (fun _ h => nomatch h), hstore_own,
                exprLocs_empty_of_isValue_isSend hvTy hv hsend⟩
      | chanRecvVal hch hbuf =>
        refine ⟨owners, OwnersExtend.refl _, hlen, ?_, hstore_own, trivial⟩
        intro l hl
        have hvNil := hchan_locs _ _ _ hch (by rw [hbuf]; exact List.mem_cons_self ..)
        simp [exprLocs, exprLocsList, hvNil] at hl
      | chanRecvClosed _ _ _ =>
        exact ⟨owners, OwnersExtend.refl _, hlen, (fun _ h => nomatch h), hstore_own, trivial⟩
      | chanClose _ =>
        exact ⟨owners, OwnersExtend.refl _, hlen, (fun _ h => nomatch h), hstore_own, trivial⟩
      | actorSpawn hv =>
        cases hop with
        | @actorSpawn σ_ty =>
          cases hargs with
          | cons hfn hnil =>
            cases hnil
            refine ⟨owners, OwnersExtend.refl _, hlen, (fun _ h => nomatch h), hstore_own, ?_⟩
            have hfnNil := exprLocs_empty_of_isValue_isSend hfn hv (isSend_fnShared Δ [] σ_ty)
            simp [EffLocsClean, exprLocs, exprLocsList, hfnNil]
      | actorCall _ hv =>
        cases hop with
        | @actorCall σ_ty r_ty _ =>
          cases hargs with
          | cons _ hrest =>
            cases hrest with
            | cons hfn hnil =>
              cases hnil
              exact ⟨owners, OwnersExtend.refl _, hlen, (fun _ h => nomatch h), hstore_own,
                exprLocs_empty_of_isValue_isSend hfn hv (isSend_fnShared Δ [σ_ty] r_ty)⟩
      | actorSend _ hv =>
        cases hop with
        | @actorSend σ_ty =>
          cases hargs with
          | cons _ hrest =>
            cases hrest with
            | cons hfn hnil =>
              cases hnil
              exact ⟨owners, OwnersExtend.refl _, hlen, (fun _ h => nomatch h), hstore_own,
                exprLocs_empty_of_isValue_isSend hfn hv (isSend_fnShared Δ [σ_ty] .void)⟩
termination_by sizeOf e

theorem stepList_preserves_ownership {Δ : AdtEnv} {Φ : FunEnv} (hΦ : FunEnvTyped Δ Φ)
    {Ψ : StoreTy} {Θ : TaskTy} {pool : ConcPool}
    {es : List Expr} {σ : Store} {es' : List Expr} {σ' : Store} {eff : ConcEff} {τs : List Ty}
    {owners : List ThreadId} {th : ThreadId}
    (hts : HasTypes Δ Φ Ψ Θ emptyCtx es τs)
    (hstep : StepList Δ Φ pool es σ es' σ' eff)
    (hpool : PoolTyped Δ Φ Ψ Θ pool)
    (hmvar_locs : ∀ (mid : Nat) (v : Expr), pool.mvars[mid]? = some (some v) → exprLocs v = [])
    (hchan_locs : ∀ (cid : Nat) (ch : ChanState) (v : Expr), pool.chans[cid]? = some ch → v ∈ ch.buf → exprLocs v = [])
    (hlen : owners.length = σ.length)
    (hes_own : ∀ l ∈ exprLocsList es, owners[l]? = some th)
    (hstore_own : ∀ (l : Loc) (v : Expr) (l' : Loc), σ[l]? = some v → l' ∈ exprLocs v → owners[l']? = owners[l]?) :
    ∃ owners',
      OwnersExtend owners owners' ∧
      owners'.length = σ'.length ∧
      (∀ l ∈ exprLocsList es', owners'[l]? = some th) ∧
      (∀ (l : Loc) (v : Expr) (l' : Loc), σ'[l]? = some v → l' ∈ exprLocs v → owners'[l']? = owners'[l]?) ∧
      EffLocsClean eff := by
  cases hstep with
  | head hs =>
    cases hts with
    | cons h1 _ =>
      rcases step_preserves_ownership hΦ h1 hs hpool hmvar_locs hchan_locs hlen
        (fun l hl => hes_own l (by simp [exprLocsList, hl])) hstore_own with
        ⟨owners', hext, hlen', he1', hst', hclean⟩
      refine ⟨owners', hext, hlen', ?_, hst', hclean⟩
      intro l hl
      simp only [exprLocsList, List.mem_append] at hl
      rcases hl with hl1 | hlr
      · exact he1' l hl1
      · exact hext l th (hes_own l (by simp [exprLocsList, hlr]))
  | tail _ hs =>
    cases hts with
    | cons _ hrest =>
      rcases stepList_preserves_ownership hΦ hrest hs hpool hmvar_locs hchan_locs hlen
        (fun l hl => hes_own l (by simp [exprLocsList, hl])) hstore_own with
        ⟨owners', hext, hlen', her', hst', hclean⟩
      refine ⟨owners', hext, hlen', ?_, hst', hclean⟩
      intro l hl
      simp only [exprLocsList, List.mem_append] at hl
      rcases hl with hl1 | hlr
      · exact hext l th (hes_own l (by simp [exprLocsList, hl1]))
      · exact her' l hlr
termination_by sizeOf es
end

/-! ## Pool Typing & Ownership Evolution Helpers for `applyConcEff` -/

/-- Intermediate pool typing where domain lengths match `Θ_dom` while expressions
    and reply-task references are already weakened to `Θ_env`. -/
structure PoolEntriesTyped (Δ : AdtEnv) (Φ : FunEnv) (Ψ : StoreTy)
    (Θ_dom Θ_env : TaskTy) (pool : ConcPool) : Prop where
  tasks_len  : pool.tasks.length = Θ_dom.tasks.length
  tasks_ty   : ∀ (tid : TaskId) (τ : Ty), Θ_dom.tasks[tid]? = some τ →
    IsSend Δ τ ∧ ∃ te, pool.tasks[tid]? = some te ∧
      (∀ e, te = .running e → HasType Δ Φ Ψ Θ_env emptyCtx e τ)
  mvars_len  : pool.mvars.length = Θ_dom.mvars.length
  mvars_ty   : ∀ (mid : Nat) (τ : Ty), Θ_dom.mvars[mid]? = some τ →
    IsSend Δ τ ∧ ∃ slot, pool.mvars[mid]? = some slot ∧
      (∀ v, slot = some v → IsValue v ∧ HasType Δ Φ Ψ Θ_env emptyCtx v τ)
  chans_len  : pool.chans.length = Θ_dom.chans.length
  chans_ty   : ∀ (cid : Nat) (τ : Ty), Θ_dom.chans[cid]? = some τ →
    IsSend Δ τ ∧ ∃ ch, pool.chans[cid]? = some ch ∧
      (∀ v ∈ ch.buf, IsValue v ∧ HasType Δ Φ Ψ Θ_env emptyCtx v τ)
  actors_len : pool.actors.length = Θ_dom.actors.length
  actors_ty  : ∀ (aid : Nat) (σ_ty : Ty), Θ_dom.actors[aid]? = some σ_ty →
    ∃ act, pool.actors[aid]? = some act ∧
      ActorPhaseTyped Δ Φ Ψ Θ_env σ_ty act.phase ∧
      (∀ msg ∈ act.mailbox, ActorMsgTyped Δ Φ Ψ Θ_env σ_ty msg)

theorem actorPhaseTyped_weaken {Δ : AdtEnv} {Φ : FunEnv} {Ψ Ψ' : StoreTy} {Θ Θ' : TaskTy}
    {σ_ty : Ty} {ph : ActorPhase}
    (hs : StoreExtends Ψ Ψ') (htk : TaskExtends Θ Θ')
    (h : ActorPhaseTyped Δ Φ Ψ Θ σ_ty ph) : ActorPhaseTyped Δ Φ Ψ' Θ' σ_ty ph := by
  cases ph with
  | init e => exact typing_env_weaken hs htk h
  | idle sv => exact ⟨h.1, typing_env_weaken hs htk h.2⟩
  | busy sv e reply =>
    cases reply with
    | none =>
      exact ⟨h.1, typing_env_weaken hs htk h.2.1, typing_env_weaken hs htk h.2.2⟩
    | some tid =>
      rcases h with ⟨hsv, hsvTy, r_ty, htid, hsend, heTy⟩
      exact ⟨hsv, typing_env_weaken hs htk hsvTy,
        r_ty, htk.tasks.2 _ _ htid, hsend, typing_env_weaken hs htk heTy⟩
  | failed _ => trivial

theorem actorMsgTyped_weaken {Δ : AdtEnv} {Φ : FunEnv} {Ψ Ψ' : StoreTy} {Θ Θ' : TaskTy}
    {σ_ty : Ty} {msg : ActorMsg}
    (hs : StoreExtends Ψ Ψ') (htk : TaskExtends Θ Θ')
    (h : ActorMsgTyped Δ Φ Ψ Θ σ_ty msg) : ActorMsgTyped Δ Φ Ψ' Θ' σ_ty msg := by
  cases hrep : msg.replyTask with
  | none =>
    simp only [ActorMsgTyped, hrep] at h ⊢
    exact ⟨h.1, typing_env_weaken hs htk h.2⟩
  | some tid =>
    simp only [ActorMsgTyped, hrep] at h ⊢
    rcases h with ⟨hv, r_ty, htid, hsend, hfn⟩
    exact ⟨hv, r_ty, htk.tasks.2 _ _ htid, hsend, typing_env_weaken hs htk hfn⟩

theorem poolTyped_weaken_entries {Δ : AdtEnv} {Φ : FunEnv} {Ψ Ψ' : StoreTy} {Θ Θ' : TaskTy}
    {pool : ConcPool}
    (hs : StoreExtends Ψ Ψ') (htk : TaskExtends Θ Θ')
    (hp : PoolTyped Δ Φ Ψ Θ pool) :
    PoolEntriesTyped Δ Φ Ψ' Θ Θ' pool :=
  { tasks_len  := hp.tasks_len
    tasks_ty   := fun tid τ htid => by
      rcases hp.tasks_ty tid τ htid with ⟨hsend, te, hte, hrun⟩
      exact ⟨hsend, te, hte, fun e he => typing_env_weaken hs htk (hrun e he)⟩
    mvars_len  := hp.mvars_len
    mvars_ty   := fun mid τ hmid => by
      rcases hp.mvars_ty mid τ hmid with ⟨hsend, slot, hslot, hv⟩
      exact ⟨hsend, slot, hslot, fun v h => ⟨(hv v h).1, typing_env_weaken hs htk (hv v h).2⟩⟩
    chans_len  := hp.chans_len
    chans_ty   := fun cid τ hcid => by
      rcases hp.chans_ty cid τ hcid with ⟨hsend, ch, hch, hbuf⟩
      exact ⟨hsend, ch, hch, fun v hv => ⟨(hbuf v hv).1, typing_env_weaken hs htk (hbuf v hv).2⟩⟩
    actors_len := hp.actors_len
    actors_ty  := fun aid σ_ty haid => by
      rcases hp.actors_ty aid σ_ty haid with ⟨act, hact, hph, hmb⟩
      exact ⟨act, hact, actorPhaseTyped_weaken hs htk hph,
        fun msg hm => actorMsgTyped_weaken hs htk (hmb msg hm)⟩ }

theorem poolEntries_to_poolTyped {Δ : AdtEnv} {Φ : FunEnv} {Ψ : StoreTy} {Θ : TaskTy}
    {pool : ConcPool} (hp : PoolEntriesTyped Δ Φ Ψ Θ Θ pool) :
    PoolTyped Δ Φ Ψ Θ pool :=
  { tasks_len  := hp.tasks_len
    tasks_ty   := hp.tasks_ty
    mvars_len  := hp.mvars_len
    mvars_ty   := hp.mvars_ty
    chans_len  := hp.chans_len
    chans_ty   := hp.chans_ty
    actors_len := hp.actors_len
    actors_ty  := hp.actors_ty }

theorem setPoolTask_entries {Δ : AdtEnv} {Φ : FunEnv} {Ψ : StoreTy} {Θ_dom Θ_env : TaskTy}
    {pool : ConcPool} {tid : TaskId} {τ : Ty} {e' : Expr}
    (hp : PoolEntriesTyped Δ Φ Ψ Θ_dom Θ_env pool)
    (htid : Θ_dom.tasks[tid]? = some τ)
    (he' : HasType Δ Φ Ψ Θ_env emptyCtx e' τ) :
    PoolEntriesTyped Δ Φ Ψ Θ_dom Θ_env (setPoolTask pool tid (.running e')) := by
  have hlt_dom : tid < Θ_dom.tasks.length := lt_length_of_getElem?_eq_some htid
  have hlt_p : tid < pool.tasks.length := hp.tasks_len ▸ hlt_dom
  refine { hp with
    tasks_len := by simp [setPoolTask, hp.tasks_len]
    tasks_ty := fun k τk hk => ?_ }
  by_cases hkt : k = tid
  · subst hkt
    have hsend := (hp.tasks_ty k τk hk).1
    rw [htid] at hk; cases hk
    refine ⟨hsend, .running e', ?_, fun u hu => by cases hu; exact he'⟩
    simp [setPoolTask, List.getElem?_set_self hlt_p]
  · rcases hp.tasks_ty k τk hk with ⟨hsend, te, hte, hrun⟩
    refine ⟨hsend, te, ?_, hrun⟩
    simp [setPoolTask, List.getElem?_set_ne (Ne.symm hkt), hte]

theorem setPoolActorPhase_entries {Δ : AdtEnv} {Φ : FunEnv} {Ψ : StoreTy} {Θ_dom Θ_env : TaskTy}
    {pool : ConcPool} {aid : Nat} {σ_ty : Ty} {ph' : ActorPhase}
    (hp : PoolEntriesTyped Δ Φ Ψ Θ_dom Θ_env pool)
    (haid : Θ_dom.actors[aid]? = some σ_ty)
    (hph' : ActorPhaseTyped Δ Φ Ψ Θ_env σ_ty ph') :
    PoolEntriesTyped Δ Φ Ψ Θ_dom Θ_env (setPoolActorPhase pool aid ph') := by
  rcases hp.actors_ty aid σ_ty haid with ⟨act, hact, _, hmb⟩
  have hlt_a : aid < pool.actors.length := lt_length_of_getElem?_eq_some hact
  simp only [setPoolActorPhase, hact, setPoolActor]
  refine { hp with
    actors_len := by simp [hp.actors_len]
    actors_ty := fun k σk hk => ?_ }
  by_cases hka : k = aid
  · subst hka
    rw [haid] at hk; cases hk
    exact ⟨{ act with phase := ph' }, List.getElem?_set_self hlt_a, hph', hmb⟩
  · rcases hp.actors_ty k σk hk with ⟨actk, hactk, hphk, hmbk⟩
    exact ⟨actk, by rw [List.getElem?_set_ne (Ne.symm hka)]; exact hactk, hphk, hmbk⟩

theorem applyConcEff_preserves_typed {Δ : AdtEnv} {Φ : FunEnv} {Ψ' : StoreTy} {Θ Θ' : TaskTy}
    {p1 : ConcPool} {eff : ConcEff}
    (hp1 : PoolEntriesTyped Δ Φ Ψ' Θ Θ' p1)
    (heff : EffTyped Δ Φ Ψ' Θ Θ' eff) :
    PoolTyped Δ Φ Ψ' Θ' (applyConcEff p1 eff) := by
  cases eff with
  | none =>
    simp only [EffTyped] at heff; subst heff
    exact poolEntries_to_poolTyped hp1
  | spawnTask body =>
    rcases heff with ⟨τsp, rfl, hsend, hbody⟩
    refine
      { tasks_len  := by simp [applyConcEff, hp1.tasks_len]
        tasks_ty   := fun k τk hk => ?_
        mvars_len  := hp1.mvars_len
        mvars_ty   := hp1.mvars_ty
        chans_len  := hp1.chans_len
        chans_ty   := hp1.chans_ty
        actors_len := hp1.actors_len
        actors_ty  := hp1.actors_ty }
    cases Nat.lt_or_ge k Θ.tasks.length with
    | inl hlt =>
      rw [List.getElem?_append_left hlt] at hk
      have hlt_p : k < p1.tasks.length := hp1.tasks_len ▸ hlt
      rcases hp1.tasks_ty k τk hk with ⟨hs, te, hte, hrun⟩
      exact ⟨hs, te, by simp [applyConcEff, List.getElem?_append_left hlt_p, hte], hrun⟩
    | inr hge =>
      rw [List.getElem?_append_right hge] at hk
      have hlt1 : k - Θ.tasks.length < 1 := by simpa using lt_length_of_getElem?_eq_some hk
      have heqk : k = Θ.tasks.length := Nat.le_antisymm (Nat.le_of_sub_eq_zero (Nat.lt_one_iff.mp hlt1)) hge
      subst heqk; simp at hk; subst hk
      refine ⟨hsend, .running body, ?_, fun u hu => by cases hu; exact hbody⟩
      simp [applyConcEff, ← hp1.tasks_len]
  | allocMVar init =>
    rcases heff with ⟨τm, rfl, hsend, hinit⟩
    refine
      { tasks_len  := hp1.tasks_len
        tasks_ty   := hp1.tasks_ty
        mvars_len  := by simp [applyConcEff, hp1.mvars_len]
        mvars_ty   := fun k τk hk => ?_
        chans_len  := hp1.chans_len
        chans_ty   := hp1.chans_ty
        actors_len := hp1.actors_len
        actors_ty  := hp1.actors_ty }
    cases Nat.lt_or_ge k Θ.mvars.length with
    | inl hlt =>
      rw [List.getElem?_append_left hlt] at hk
      have hlt_p : k < p1.mvars.length := hp1.mvars_len ▸ hlt
      rcases hp1.mvars_ty k τk hk with ⟨hs, slot, hslot, hv⟩
      exact ⟨hs, slot, by simp [applyConcEff, List.getElem?_append_left hlt_p, hslot], hv⟩
    | inr hge =>
      rw [List.getElem?_append_right hge] at hk
      have hlt1 : k - Θ.mvars.length < 1 := by simpa using lt_length_of_getElem?_eq_some hk
      have heqk : k = Θ.mvars.length := Nat.le_antisymm (Nat.le_of_sub_eq_zero (Nat.lt_one_iff.mp hlt1)) hge
      subst heqk; simp at hk; subst hk
      exact ⟨hsend, init, by simp [applyConcEff, ← hp1.mvars_len], hinit⟩
  | takeMVar mid =>
    simp only [EffTyped] at heff; subst heff
    refine { poolEntries_to_poolTyped hp1 with
      mvars_len := by simp [applyConcEff, hp1.mvars_len]
      mvars_ty  := fun k τk hk => ?_ }
    rcases hp1.mvars_ty k τk hk with ⟨hs, slot, hslot, hv⟩
    by_cases hkm : k = mid
    · subst hkm
      have hlt_p : k < p1.mvars.length := lt_length_of_getElem?_eq_some hslot
      exact ⟨hs, none, by simp [applyConcEff, List.getElem?_set_self hlt_p], fun _ h => nomatch h⟩
    · exact ⟨hs, slot, by simp [applyConcEff, List.getElem?_set_ne (Ne.symm hkm), hslot], hv⟩
  | putMVar mid val =>
    rcases heff with ⟨τm, rfl, hmid, hsend, hvVal, hvTy⟩
    simp only [applyConcEff]
    refine { poolEntries_to_poolTyped hp1 with
      mvars_len := by simp [hp1.mvars_len]
      mvars_ty  := fun k τk hk => ?_ }
    by_cases hkm : k = mid
    · subst hkm
      rw [hmid] at hk; cases hk
      have hlt_m := lt_length_of_getElem?_eq_some hmid
      have hlt_p : k < p1.mvars.length := hp1.mvars_len ▸ hlt_m
      exact ⟨hsend, some val, List.getElem?_set_self hlt_p,
        fun u hu => by cases hu; exact ⟨hvVal, hvTy⟩⟩
    · rcases hp1.mvars_ty k τk hk with ⟨hs, slot, hslot, hv⟩
      exact ⟨hs, slot, by rw [List.getElem?_set_ne (Ne.symm hkm)]; exact hslot, hv⟩
  | allocChan cap =>
    rcases heff with ⟨τc, rfl, hsend⟩
    refine
      { tasks_len  := hp1.tasks_len
        tasks_ty   := hp1.tasks_ty
        mvars_len  := hp1.mvars_len
        mvars_ty   := hp1.mvars_ty
        chans_len  := by simp [applyConcEff, hp1.chans_len]
        chans_ty   := fun k τk hk => ?_
        actors_len := hp1.actors_len
        actors_ty  := hp1.actors_ty }
    cases Nat.lt_or_ge k Θ.chans.length with
    | inl hlt =>
      rw [List.getElem?_append_left hlt] at hk
      have hlt_p : k < p1.chans.length := hp1.chans_len ▸ hlt
      rcases hp1.chans_ty k τk hk with ⟨hs, ch, hch, hbuf⟩
      exact ⟨hs, ch, by simp [applyConcEff, List.getElem?_append_left hlt_p, hch], hbuf⟩
    | inr hge =>
      rw [List.getElem?_append_right hge] at hk
      have hlt1 : k - Θ.chans.length < 1 := by simpa using lt_length_of_getElem?_eq_some hk
      have heqk : k = Θ.chans.length := Nat.le_antisymm (Nat.le_of_sub_eq_zero (Nat.lt_one_iff.mp hlt1)) hge
      subst heqk; simp at hk; subst hk
      exact ⟨hsend, { cap := cap, buf := [], closed := false },
        by simp [applyConcEff, ← hp1.chans_len], fun _ h => nomatch h⟩
  | sendChan cid val =>
    rcases heff with ⟨τc, rfl, hcid, hsend, hvVal, hvTy⟩
    rcases hp1.chans_ty cid τc hcid with ⟨_, ch0, hch0, hbuf0⟩
    have hlt_c : cid < p1.chans.length := lt_length_of_getElem?_eq_some hch0
    simp only [applyConcEff, hch0]
    refine
      { tasks_len  := hp1.tasks_len
        tasks_ty   := hp1.tasks_ty
        mvars_len  := hp1.mvars_len
        mvars_ty   := hp1.mvars_ty
        chans_len  := by simp [hp1.chans_len]
        chans_ty   := fun k τk hk => ?_
        actors_len := hp1.actors_len
        actors_ty  := hp1.actors_ty }
    by_cases hkc : k = cid
    · subst hkc
      rw [hcid] at hk; cases hk
      refine ⟨hsend, { ch0 with buf := ch0.buf ++ [val] },
        List.getElem?_set_self hlt_c, fun u hu => ?_⟩
      rcases List.mem_append.mp hu with hmem | hsing
      · exact hbuf0 u hmem
      · simp only [List.mem_singleton] at hsing; subst hsing
        exact ⟨hvVal, hvTy⟩
    · rcases hp1.chans_ty k τk hk with ⟨hs, chk, hchk, hbufk⟩
      exact ⟨hs, chk, by rw [List.getElem?_set_ne (Ne.symm hkc)]; exact hchk, hbufk⟩
  | recvChan cid =>
    simp only [EffTyped] at heff; subst heff
    cases hch0 : p1.chans[cid]? with
    | none =>
      simpa [applyConcEff, hch0] using poolEntries_to_poolTyped hp1
    | some ch0 =>
      have hlt_c : cid < p1.chans.length := lt_length_of_getElem?_eq_some hch0
      simp only [applyConcEff, hch0]
      refine
        { tasks_len  := hp1.tasks_len
          tasks_ty   := hp1.tasks_ty
          mvars_len  := hp1.mvars_len
          mvars_ty   := hp1.mvars_ty
          chans_len  := by simp [hp1.chans_len]
          chans_ty   := fun k τk hk => ?_
          actors_len := hp1.actors_len
          actors_ty  := hp1.actors_ty }
      by_cases hkc : k = cid
      · subst hkc
        rcases hp1.chans_ty k τk hk with ⟨hs, ch', hch', hbuf'⟩
        rw [hch0] at hch'; cases hch'
        refine ⟨hs, { ch0 with buf := ch0.buf.tail },
          List.getElem?_set_self hlt_c, fun u hu => ?_⟩
        exact hbuf' u (List.mem_of_mem_tail hu)
      · rcases hp1.chans_ty k τk hk with ⟨hs, chk, hchk, hbufk⟩
        exact ⟨hs, chk, by rw [List.getElem?_set_ne (Ne.symm hkc)]; exact hchk, hbufk⟩
  | closeChan cid =>
    simp only [EffTyped] at heff; subst heff
    cases hch0 : p1.chans[cid]? with
    | none =>
      simpa [applyConcEff, hch0] using poolEntries_to_poolTyped hp1
    | some ch0 =>
      have hlt_c : cid < p1.chans.length := lt_length_of_getElem?_eq_some hch0
      simp only [applyConcEff, hch0]
      refine
        { tasks_len  := hp1.tasks_len
          tasks_ty   := hp1.tasks_ty
          mvars_len  := hp1.mvars_len
          mvars_ty   := hp1.mvars_ty
          chans_len  := by simp [hp1.chans_len]
          chans_ty   := fun k τk hk => ?_
          actors_len := hp1.actors_len
          actors_ty  := hp1.actors_ty }
      by_cases hkc : k = cid
      · subst hkc
        rcases hp1.chans_ty k τk hk with ⟨hs, ch', hch', hbuf'⟩
        rw [hch0] at hch'; cases hch'
        exact ⟨hs, { ch0 with closed := true },
          List.getElem?_set_self hlt_c, hbuf'⟩
      · rcases hp1.chans_ty k τk hk with ⟨hs, chk, hchk, hbufk⟩
        exact ⟨hs, chk, by rw [List.getElem?_set_ne (Ne.symm hkc)]; exact hchk, hbufk⟩
  | spawnActor initExpr =>
    rcases heff with ⟨σ_ty, rfl, hinit⟩
    refine
      { tasks_len  := hp1.tasks_len
        tasks_ty   := hp1.tasks_ty
        mvars_len  := hp1.mvars_len
        mvars_ty   := hp1.mvars_ty
        chans_len  := hp1.chans_len
        chans_ty   := hp1.chans_ty
        actors_len := by simp [applyConcEff, hp1.actors_len]
        actors_ty  := fun k σk hk => ?_ }
    cases Nat.lt_or_ge k Θ.actors.length with
    | inl hlt =>
      rw [List.getElem?_append_left hlt] at hk
      have hlt_p : k < p1.actors.length := hp1.actors_len ▸ hlt
      rcases hp1.actors_ty k σk hk with ⟨act, hact, hph, hmb⟩
      exact ⟨act, by simp [applyConcEff, List.getElem?_append_left hlt_p, hact], hph, hmb⟩
    | inr hge =>
      rw [List.getElem?_append_right hge] at hk
      have hlt1 : k - Θ.actors.length < 1 := by simpa using lt_length_of_getElem?_eq_some hk
      have heqk : k = Θ.actors.length := Nat.le_antisymm (Nat.le_of_sub_eq_zero (Nat.lt_one_iff.mp hlt1)) hge
      subst heqk; simp at hk; subst hk
      exact ⟨{ phase := .init initExpr, mailbox := [] },
        by simp [applyConcEff, ← hp1.actors_len], hinit, fun _ h => nomatch h⟩
  | callActor aid handler =>
    rcases heff with ⟨σ_ty, r_ty, rfl, haid, hsend, hvFn, hfnTy⟩
    rcases hp1.actors_ty aid σ_ty haid with ⟨act0, hact0, hph0, hmb0⟩
    have hlt_a : aid < p1.actors.length := lt_length_of_getElem?_eq_some hact0
    simp only [applyConcEff, hact0]
    refine
      { tasks_len  := by simp [hp1.tasks_len]
        tasks_ty   := fun k τk hk => ?_
        mvars_len  := hp1.mvars_len
        mvars_ty   := hp1.mvars_ty
        chans_len  := hp1.chans_len
        chans_ty   := hp1.chans_ty
        actors_len := by simp [hp1.actors_len]
        actors_ty  := fun k σk hk => ?_ }
    · cases Nat.lt_or_ge k Θ.tasks.length with
      | inl hlt =>
        rw [List.getElem?_append_left hlt] at hk
        have hlt_p : k < p1.tasks.length := hp1.tasks_len ▸ hlt
        rcases hp1.tasks_ty k τk hk with ⟨hs, te, hte, hrun⟩
        exact ⟨hs, te, by rw [List.getElem?_append_left hlt_p]; exact hte, hrun⟩
      | inr hge =>
        rw [List.getElem?_append_right hge] at hk
        have hlt1 : k - Θ.tasks.length < 1 := by simpa using lt_length_of_getElem?_eq_some hk
        have heqk : k = Θ.tasks.length := Nat.le_antisymm (Nat.le_of_sub_eq_zero (Nat.lt_one_iff.mp hlt1)) hge
        subst heqk; simp at hk; subst hk
        exact ⟨hsend, .pendingReply,
          by simp [← hp1.tasks_len], fun _ h => nomatch h⟩
    · by_cases hka : k = aid
      · subst hka
        rw [haid] at hk; cases hk
        refine ⟨{ act0 with mailbox := act0.mailbox ++ [{ handler := handler, replyTask := some p1.tasks.length }] },
          List.getElem?_set_self hlt_a, hph0, fun msg hm => ?_⟩
        rcases List.mem_append.mp hm with hold | hnew
        · exact hmb0 msg hold
        · simp only [List.mem_singleton] at hnew; subst hnew
          refine ⟨hvFn, r_ty, ?_, hsend, hfnTy⟩
          simp [hp1.tasks_len]
      · rcases hp1.actors_ty k σk hk with ⟨actk, hactk, hphk, hmbk⟩
        exact ⟨actk, by rw [List.getElem?_set_ne (Ne.symm hka)]; exact hactk, hphk, hmbk⟩
  | sendActor aid handler =>
    rcases heff with ⟨σ_ty, rfl, haid, hvFn, hfnTy⟩
    rcases hp1.actors_ty aid σ_ty haid with ⟨act0, hact0, hph0, hmb0⟩
    have hlt_a : aid < p1.actors.length := lt_length_of_getElem?_eq_some hact0
    simp only [applyConcEff, hact0]
    refine
      { tasks_len  := hp1.tasks_len
        tasks_ty   := hp1.tasks_ty
        mvars_len  := hp1.mvars_len
        mvars_ty   := hp1.mvars_ty
        chans_len  := hp1.chans_len
        chans_ty   := hp1.chans_ty
        actors_len := by simp [hp1.actors_len]
        actors_ty  := fun k σk hk => ?_ }
    by_cases hka : k = aid
    · subst hka
      rw [haid] at hk; cases hk
      refine ⟨{ act0 with mailbox := act0.mailbox ++ [{ handler := handler, replyTask := none }] },
        List.getElem?_set_self hlt_a, hph0, fun msg hm => ?_⟩
      rcases List.mem_append.mp hm with hold | hnew
      · exact hmb0 msg hold
      · simp only [List.mem_singleton] at hnew; subst hnew
        exact ⟨hvFn, hfnTy⟩
    · rcases hp1.actors_ty k σk hk with ⟨actk, hactk, hphk, hmbk⟩
      exact ⟨actk, by rw [List.getElem?_set_ne (Ne.symm hka)]; exact hactk, hphk, hmbk⟩

theorem applyConcEff_preserves_owned {owners : List ThreadId} {p1 : ConcPool} {σ : Store}
    {eff : ConcEff}
    (hown : HeapOwned owners p1 σ)
    (hclean : EffLocsClean eff) :
    HeapOwned owners (applyConcEff p1 eff) σ := by
  cases eff with
  | none => exact hown
  | spawnTask body =>
    simp only [applyConcEff]
    refine { hown with task_locs := fun k ek l hek hl => ?_ }
    cases Nat.lt_or_ge k p1.tasks.length with
    | inl hlt =>
      rw [List.getElem?_append_left hlt] at hek
      exact hown.task_locs k ek l hek hl
    | inr hge =>
      rw [List.getElem?_append_right hge] at hek
      have hlt1 : k - p1.tasks.length < 1 := by simpa using lt_length_of_getElem?_eq_some hek
      have heqk : k = p1.tasks.length := Nat.le_antisymm (Nat.le_of_sub_eq_zero (Nat.lt_one_iff.mp hlt1)) hge
      subst heqk; simp at hek; subst hek
      simp only [EffLocsClean] at hclean
      rw [hclean] at hl; cases hl
  | allocMVar init =>
    simp only [applyConcEff]
    refine { hown with mvar_locs := fun k v hk => ?_ }
    cases Nat.lt_or_ge k p1.mvars.length with
    | inl hlt =>
      rw [List.getElem?_append_left hlt] at hk
      exact hown.mvar_locs k v hk
    | inr hge =>
      rw [List.getElem?_append_right hge] at hk
      have hlt1 : k - p1.mvars.length < 1 := by simpa using lt_length_of_getElem?_eq_some hk
      have heqk : k = p1.mvars.length := Nat.le_antisymm (Nat.le_of_sub_eq_zero (Nat.lt_one_iff.mp hlt1)) hge
      subst heqk; simp at hk
      exact hclean v hk
  | takeMVar mid =>
    simp only [applyConcEff]
    refine { hown with mvar_locs := fun k v hk => ?_ }
    by_cases hkm : k = mid
    · subst hkm
      cases Nat.lt_or_ge k p1.mvars.length with
      | inl hlt => simp [List.getElem?_set_self hlt] at hk
      | inr hge => simp [List.set_eq_of_length_le hge, List.getElem?_eq_none hge] at hk
    · rw [List.getElem?_set_ne (Ne.symm hkm)] at hk
      exact hown.mvar_locs k v hk
  | putMVar mid val =>
    simp only [applyConcEff]
    refine { hown with mvar_locs := fun k v hk => ?_ }
    by_cases hkm : k = mid
    · subst hkm
      cases Nat.lt_or_ge k p1.mvars.length with
      | inl hlt =>
        simp only [List.getElem?_set_self hlt, Option.some.injEq] at hk
        cases hk; exact hclean
      | inr hge => simp [List.set_eq_of_length_le hge, List.getElem?_eq_none hge] at hk
    · rw [List.getElem?_set_ne (Ne.symm hkm)] at hk
      exact hown.mvar_locs k v hk
  | allocChan cap =>
    simp only [applyConcEff]
    refine { hown with chan_locs := fun k ch v hk hv => ?_ }
    cases Nat.lt_or_ge k p1.chans.length with
    | inl hlt =>
      rw [List.getElem?_append_left hlt] at hk
      exact hown.chan_locs k ch v hk hv
    | inr hge =>
      rw [List.getElem?_append_right hge] at hk
      have hlt1 : k - p1.chans.length < 1 := by simpa using lt_length_of_getElem?_eq_some hk
      have heqk : k = p1.chans.length := Nat.le_antisymm (Nat.le_of_sub_eq_zero (Nat.lt_one_iff.mp hlt1)) hge
      subst heqk; simp at hk; subst hk; cases hv
  | sendChan cid val =>
    cases hch0 : p1.chans[cid]? with
    | none => simpa [applyConcEff, hch0] using hown
    | some ch0 =>
      have hlt_c : cid < p1.chans.length := lt_length_of_getElem?_eq_some hch0
      simp only [applyConcEff, hch0]
      refine { hown with chan_locs := fun k ch v hk hv => ?_ }
      by_cases hkc : k = cid
      · subst hkc
        simp only [List.getElem?_set_self hlt_c, Option.some.injEq] at hk
        subst hk
        rcases List.mem_append.mp hv with hold | hnew
        · exact hown.chan_locs k ch0 v hch0 hold
        · simp only [List.mem_singleton] at hnew; subst hnew; exact hclean
      · rw [List.getElem?_set_ne (Ne.symm hkc)] at hk
        exact hown.chan_locs k ch v hk hv
  | recvChan cid =>
    cases hch0 : p1.chans[cid]? with
    | none => simpa [applyConcEff, hch0] using hown
    | some ch0 =>
      have hlt_c : cid < p1.chans.length := lt_length_of_getElem?_eq_some hch0
      simp only [applyConcEff, hch0]
      refine { hown with chan_locs := fun k ch v hk hv => ?_ }
      by_cases hkc : k = cid
      · subst hkc
        simp only [List.getElem?_set_self hlt_c, Option.some.injEq] at hk
        subst hk
        exact hown.chan_locs k ch0 v hch0 (List.mem_of_mem_tail hv)
      · rw [List.getElem?_set_ne (Ne.symm hkc)] at hk
        exact hown.chan_locs k ch v hk hv
  | closeChan cid =>
    cases hch0 : p1.chans[cid]? with
    | none => simpa [applyConcEff, hch0] using hown
    | some ch0 =>
      have hlt_c : cid < p1.chans.length := lt_length_of_getElem?_eq_some hch0
      simp only [applyConcEff, hch0]
      refine { hown with chan_locs := fun k ch v hk hv => ?_ }
      by_cases hkc : k = cid
      · subst hkc
        simp only [List.getElem?_set_self hlt_c, Option.some.injEq] at hk
        subst hk
        exact hown.chan_locs k ch0 v hch0 hv
      · rw [List.getElem?_set_ne (Ne.symm hkc)] at hk
        exact hown.chan_locs k ch v hk hv
  | spawnActor initExpr =>
    simp only [applyConcEff]
    refine { hown with actor_locs := fun k act hk => ?_ }
    cases Nat.lt_or_ge k p1.actors.length with
    | inl hlt =>
      rw [List.getElem?_append_left hlt] at hk
      exact hown.actor_locs k act hk
    | inr hge =>
      rw [List.getElem?_append_right hge] at hk
      have hlt1 : k - p1.actors.length < 1 := by simpa using lt_length_of_getElem?_eq_some hk
      have heqk : k = p1.actors.length := Nat.le_antisymm (Nat.le_of_sub_eq_zero (Nat.lt_one_iff.mp hlt1)) hge
      subst heqk; simp at hk; subst hk
      simp only [EffLocsClean] at hclean
      exact ⟨fun l hl => by simp [actorPhaseLocs, hclean] at hl, fun _ h => nomatch h⟩
  | callActor aid handler =>
    cases hact0 : p1.actors[aid]? with
    | none => simpa [applyConcEff, hact0] using hown
    | some act0 =>
      have hlt_a : aid < p1.actors.length := lt_length_of_getElem?_eq_some hact0
      simp only [applyConcEff, hact0]
      refine { hown with
        task_locs  := fun k ek l hek hl => ?_
        actor_locs := fun k act hk => ?_ }
      · cases Nat.lt_or_ge k p1.tasks.length with
        | inl hlt =>
          rw [List.getElem?_append_left hlt] at hek
          exact hown.task_locs k ek l hek hl
        | inr hge =>
          rw [List.getElem?_append_right hge] at hek
          have hlt1 : k - p1.tasks.length < 1 := by simpa using lt_length_of_getElem?_eq_some hek
          have heqk : k = p1.tasks.length := Nat.le_antisymm (Nat.le_of_sub_eq_zero (Nat.lt_one_iff.mp hlt1)) hge
          subst heqk; simp at hek
      · by_cases hka : k = aid
        · subst hka
          simp only [List.getElem?_set_self hlt_a, Option.some.injEq] at hk
          subst hk
          rcases hown.actor_locs k act0 hact0 with ⟨hph, hmb⟩
          refine ⟨hph, fun msg hm => ?_⟩
          rcases List.mem_append.mp hm with hold | hnew
          · exact hmb msg hold
          · simp only [List.mem_singleton] at hnew; subst hnew; exact hclean
        · rw [List.getElem?_set_ne (Ne.symm hka)] at hk
          exact hown.actor_locs k act hk
  | sendActor aid handler =>
    cases hact0 : p1.actors[aid]? with
    | none => simpa [applyConcEff, hact0] using hown
    | some act0 =>
      have hlt_a : aid < p1.actors.length := lt_length_of_getElem?_eq_some hact0
      simp only [applyConcEff, hact0]
      refine { hown with actor_locs := fun k act hk => ?_ }
      by_cases hka : k = aid
      · subst hka
        simp only [List.getElem?_set_self hlt_a, Option.some.injEq] at hk
        subst hk
        rcases hown.actor_locs k act0 hact0 with ⟨hph, hmb⟩
        refine ⟨hph, fun msg hm => ?_⟩
        rcases List.mem_append.mp hm with hold | hnew
        · exact hmb msg hold
        · simp only [List.mem_singleton] at hnew; subst hnew; exact hclean
      · rw [List.getElem?_set_ne (Ne.symm hka)] at hk
        exact hown.actor_locs k act hk

/-! ## Concurrent Pool Invariant Preservation (`ConcStep` & `ConcSteps`) -/

/-- Combined concurrent configuration invariant: well-typed store, well-typed
    `Task` + `MVar` + `Chan` + `Actor` pool, and strict per-thread heap ownership. -/
def ConcInv (Δ : AdtEnv) (Φ : FunEnv) (pool : ConcPool) (σ : Store) : Prop :=
  ∃ (Ψ : StoreTy) (Θ : TaskTy) (owners : List ThreadId),
    StoreTyped Δ Φ Ψ Θ σ ∧
    PoolTyped Δ Φ Ψ Θ pool ∧
    HeapOwned owners pool σ

theorem concStep_preserves_inv {Δ : AdtEnv} {Φ : FunEnv} (hΦ : FunEnvTyped Δ Φ)
    {pool pool' : ConcPool} {σ σ' : Store}
    (hinv : ConcInv Δ Φ pool σ)
    (hstep : ConcStep Δ Φ pool σ pool' σ') :
    ConcInv Δ Φ pool' σ' := by
  rcases hinv with ⟨Ψ, Θ, owners, hσ, hpool, hown⟩
  match hstep with
  | .taskStep (tid := tid) (e := e) (e' := e') (eff := eff) het hs =>
    have hlt_t : tid < pool.tasks.length := lt_length_of_getElem?_eq_some het
    have hlt_Θ : tid < Θ.tasks.length := hpool.tasks_len ▸ hlt_t
    have hΘ_some : Θ.tasks[tid]? = some Θ.tasks[tid] := List.getElem?_eq_getElem hlt_Θ
    rcases hpool.tasks_ty tid Θ.tasks[tid] hΘ_some with ⟨_, te0, hte0, hrun0⟩
    rw [het] at hte0; cases hte0
    have hetTy := hrun0 e rfl
    rcases preservation hΦ hetTy hs hσ hpool with ⟨Ψ', Θ', hsExt, heff, hetTy', hσ'⟩
    have htkExt := effTyped_extends heff
    have hp_weak := poolTyped_weaken_entries hsExt htkExt hpool
    have hp1 := setPoolTask_entries hp_weak hΘ_some hetTy'
    have hpool' := applyConcEff_preserves_typed hp1 heff
    have he_own : ∀ l ∈ exprLocs e, owners[l]? = some (.task tid) :=
      fun l hl => hown.task_locs tid e l het hl
    rcases step_preserves_ownership hΦ hetTy hs hpool hown.mvar_locs hown.chan_locs
      hown.len_eq he_own hown.store_locs with
      ⟨owners', hownExt, hlen', he_own', hst_own', hclean⟩
    have hown1 : HeapOwned owners' (setPoolTask pool tid (.running e')) σ' :=
      { len_eq     := hlen'
        task_locs  := fun k ek l hek hl => by
          by_cases hkt : k = tid
          · subst hkt
            simp only [setPoolTask, List.getElem?_set_self hlt_t, Option.some.injEq,
              TaskEntry.running.injEq] at hek
            subst hek; exact he_own' l hl
          · simp only [setPoolTask, List.getElem?_set_ne (Ne.symm hkt)] at hek
            exact hownExt l (.task k) (hown.task_locs k ek l hek hl)
        actor_locs := fun k act hk => by
          rcases hown.actor_locs k act hk with ⟨hph, hmb⟩
          exact ⟨fun l hl => hownExt l (.actor k) (hph l hl), hmb⟩
        mvar_locs  := hown.mvar_locs
        chan_locs  := hown.chan_locs
        store_locs := hst_own' }
    exact ⟨Ψ', Θ', owners', hσ', hpool', applyConcEff_preserves_owned hown1 hclean⟩

  | .actorInitStep (aid := aid) (act := act) (e := e) (e' := e') (eff := eff) hact hph hs =>
    have hlt_a : aid < pool.actors.length := lt_length_of_getElem?_eq_some hact
    have hlt_Θ : aid < Θ.actors.length := hpool.actors_len ▸ hlt_a
    have hΘ_some : Θ.actors[aid]? = some Θ.actors[aid] := List.getElem?_eq_getElem hlt_Θ
    rcases hpool.actors_ty aid Θ.actors[aid] hΘ_some with ⟨act0, hact0, hphTy, _⟩
    rw [hact] at hact0; cases hact0
    rw [hph] at hphTy
    simp only [ActorPhaseTyped] at hphTy
    rcases preservation hΦ hphTy hs hσ hpool with ⟨Ψ', Θ', hsExt, heff, heTy', hσ'⟩
    have htkExt := effTyped_extends heff
    have hp_weak := poolTyped_weaken_entries hsExt htkExt hpool
    have hp1 := setPoolActorPhase_entries hp_weak hΘ_some (ph' := .init e') heTy'
    have hpool' := applyConcEff_preserves_typed hp1 heff
    rcases hown.actor_locs aid act hact with ⟨hact_own, hmb_own⟩
    have he_own : ∀ l ∈ exprLocs e, owners[l]? = some (.actor aid) := by
      intro l hl; apply hact_own l; simp [hph, actorPhaseLocs, hl]
    rcases step_preserves_ownership hΦ hphTy hs hpool hown.mvar_locs hown.chan_locs
      hown.len_eq he_own hown.store_locs with
      ⟨owners', hownExt, hlen', he_own', hst_own', hclean⟩
    have hown1 : HeapOwned owners' (setPoolActorPhase pool aid (.init e')) σ' :=
      { len_eq     := hlen'
        task_locs  := fun k ek l hek hl =>
          hownExt l (.task k) (hown.task_locs k ek l (by simpa [setPoolActorPhase, hact, setPoolActor] using hek) hl)
        actor_locs := fun k actk hk => by
          by_cases hka : k = aid
          · subst hka
            simp only [setPoolActorPhase, hact, setPoolActor, List.getElem?_set_self hlt_a,
              Option.some.injEq] at hk
            subst hk
            exact ⟨fun l hl => he_own' l (by simpa [actorPhaseLocs] using hl), hmb_own⟩
          · simp only [setPoolActorPhase, hact, setPoolActor, List.getElem?_set_ne (Ne.symm hka)] at hk
            rcases hown.actor_locs k actk hk with ⟨hphk, hmbk⟩
            exact ⟨fun l hl => hownExt l (.actor k) (hphk l hl), hmbk⟩
        mvar_locs  := fun m v hm => hown.mvar_locs m v (by simpa [setPoolActorPhase, hact, setPoolActor] using hm)
        chan_locs  := fun c ch v hc hv => hown.chan_locs c ch v (by simpa [setPoolActorPhase, hact, setPoolActor] using hc) hv
        store_locs := hst_own' }
    exact ⟨Ψ', Θ', owners', hσ', hpool', applyConcEff_preserves_owned hown1 hclean⟩

  | .actorInitDone (aid := aid) (act := act) (sv := sv) hact hph hsv =>
    have hlt_a : aid < pool.actors.length := lt_length_of_getElem?_eq_some hact
    have hlt_Θ : aid < Θ.actors.length := hpool.actors_len ▸ hlt_a
    have hΘ_some : Θ.actors[aid]? = some Θ.actors[aid] := List.getElem?_eq_getElem hlt_Θ
    rcases hpool.actors_ty aid Θ.actors[aid] hΘ_some with ⟨act0, hact0, hphTy, _⟩
    rw [hact] at hact0; cases hact0
    rw [hph] at hphTy
    have hp0 := poolTyped_weaken_entries (StoreExtends.refl Ψ) (TaskExtends.refl Θ) hpool
    have hp1 := poolEntries_to_poolTyped (setPoolActorPhase_entries hp0 hΘ_some (ph' := .idle sv) ⟨hsv, hphTy⟩)
    rcases hown.actor_locs aid act hact with ⟨hact_own, hmb_own⟩
    refine ⟨Ψ, Θ, owners, hσ, hp1,
      { len_eq     := hown.len_eq
        task_locs  := fun k ek l hek hl =>
          hown.task_locs k ek l (by simpa [setPoolActorPhase, hact, setPoolActor] using hek) hl
        actor_locs := fun k actk hk => by
          by_cases hka : k = aid
          · subst hka
            simp only [setPoolActorPhase, hact, setPoolActor, List.getElem?_set_self hlt_a,
              Option.some.injEq] at hk
            subst hk
            exact ⟨fun l hl => hact_own l (by simpa [hph, actorPhaseLocs] using hl), hmb_own⟩
          · simp only [setPoolActorPhase, hact, setPoolActor, List.getElem?_set_ne (Ne.symm hka)] at hk
            exact hown.actor_locs k actk hk
        mvar_locs  := fun m v hm => hown.mvar_locs m v (by simpa [setPoolActorPhase, hact, setPoolActor] using hm)
        chan_locs  := fun c ch v hc hv => hown.chan_locs c ch v (by simpa [setPoolActorPhase, hact, setPoolActor] using hc) hv
        store_locs := hown.store_locs }⟩

  | .actorInitTrap (aid := aid) (act := act) (t := t) hact _ =>
    have hlt_a : aid < pool.actors.length := lt_length_of_getElem?_eq_some hact
    have hlt_Θ : aid < Θ.actors.length := hpool.actors_len ▸ hlt_a
    have hΘ_some : Θ.actors[aid]? = some Θ.actors[aid] := List.getElem?_eq_getElem hlt_Θ
    have hp0 := poolTyped_weaken_entries (StoreExtends.refl Ψ) (TaskExtends.refl Θ) hpool
    have hp1 := poolEntries_to_poolTyped (setPoolActorPhase_entries hp0 hΘ_some (ph' := .failed t) trivial)
    rcases hown.actor_locs aid act hact with ⟨_, hmb_own⟩
    refine ⟨Ψ, Θ, owners, hσ, hp1,
      { len_eq     := hown.len_eq
        task_locs  := fun k ek l hek hl =>
          hown.task_locs k ek l (by simpa [setPoolActorPhase, hact, setPoolActor] using hek) hl
        actor_locs := fun k actk hk => by
          by_cases hka : k = aid
          · subst hka
            simp only [setPoolActorPhase, hact, setPoolActor, List.getElem?_set_self hlt_a,
              Option.some.injEq] at hk
            subst hk
            exact ⟨(fun _ h => nomatch h), hmb_own⟩
          · simp only [setPoolActorPhase, hact, setPoolActor, List.getElem?_set_ne (Ne.symm hka)] at hk
            exact hown.actor_locs k actk hk
        mvar_locs  := fun m v hm => hown.mvar_locs m v (by simpa [setPoolActorPhase, hact, setPoolActor] using hm)
        chan_locs  := fun c ch v hc hv => hown.chan_locs c ch v (by simpa [setPoolActorPhase, hact, setPoolActor] using hc) hv
        store_locs := hown.store_locs }⟩

  | .actorDequeue (aid := aid) (sv := sv) (msg := msg) (rest := rest) hact =>
    have hlt_a : aid < pool.actors.length := lt_length_of_getElem?_eq_some hact
    have hlt_Θ : aid < Θ.actors.length := hpool.actors_len ▸ hlt_a
    have hΘ_some : Θ.actors[aid]? = some Θ.actors[aid] := List.getElem?_eq_getElem hlt_Θ
    rcases hpool.actors_ty aid Θ.actors[aid] hΘ_some with ⟨act0, hact0, hphTy, hmbTy⟩
    rw [hact] at hact0; cases hact0
    rcases hphTy with ⟨hsv, hsvTy⟩
    have hmsgTy := hmbTy msg (List.mem_cons_self ..)
    have hbusyTy : ActorPhaseTyped Δ Φ Ψ Θ Θ.actors[aid] (.busy sv (.apply msg.handler [sv]) msg.replyTask) := by
      cases hrep : msg.replyTask with
      | none =>
        simp only [ActorMsgTyped, hrep] at hmsgTy
        exact ⟨hsv, hsvTy, .apply hmsgTy.2 (.cons hsvTy .nil) (TySub.refl _)⟩
      | some tid =>
        simp only [ActorMsgTyped, hrep] at hmsgTy
        rcases hmsgTy with ⟨_, r_ty, htid, hsend, hfnTy⟩
        exact ⟨hsv, hsvTy, r_ty, htid, hsend, .apply hfnTy (.cons hsvTy .nil) (TySub.refl _)⟩
    rcases hown.actor_locs aid _ hact with ⟨hsv_own, hmb_own⟩
    have hmsgNil : exprLocs msg.handler = [] := hmb_own msg (List.mem_cons_self ..)
    simp only [setPoolActor]
    refine ⟨Ψ, Θ, owners, hσ,
      { tasks_len  := hpool.tasks_len
        tasks_ty   := hpool.tasks_ty
        mvars_len  := hpool.mvars_len
        mvars_ty   := hpool.mvars_ty
        chans_len  := hpool.chans_len
        chans_ty   := hpool.chans_ty
        actors_len := by simp [hpool.actors_len]
        actors_ty  := fun k σk hk => by
          by_cases hka : k = aid
          · subst hka
            rw [hΘ_some] at hk; cases hk
            exact ⟨{ phase := .busy sv (.apply msg.handler [sv]) msg.replyTask, mailbox := rest },
              List.getElem?_set_self hlt_a,
              hbusyTy, fun m hm => hmbTy m (List.mem_cons_of_mem _ hm)⟩
          · rcases hpool.actors_ty k σk hk with ⟨actk, hactk, hphk, hmbk⟩
            exact ⟨actk, by rw [List.getElem?_set_ne (Ne.symm hka)]; exact hactk, hphk, hmbk⟩ },
      { len_eq     := hown.len_eq
        task_locs  := hown.task_locs
        actor_locs := fun k actk hk => by
          by_cases hka : k = aid
          · subst hka
            simp only [List.getElem?_set_self hlt_a, Option.some.injEq] at hk
            subst hk
            refine ⟨fun l hl => ?_, fun m hm => hmb_own m (List.mem_cons_of_mem _ hm)⟩
            simp only [actorPhaseLocs, exprLocs, exprLocsList, hmsgNil, List.nil_append,
              List.append_nil, List.mem_append] at hl
            rcases hl with h1 | h2
            · exact hsv_own l h1
            · exact hsv_own l h2
          · rw [List.getElem?_set_ne (Ne.symm hka)] at hk
            exact hown.actor_locs k actk hk
        mvar_locs  := hown.mvar_locs
        chan_locs  := hown.chan_locs
        store_locs := hown.store_locs }⟩

  | .actorBusyStep (aid := aid) (act := act) (sv := sv) (e := e) (e' := e') (reply := reply) (eff := eff) hact hph hs =>
    have hlt_a : aid < pool.actors.length := lt_length_of_getElem?_eq_some hact
    have hlt_Θ : aid < Θ.actors.length := hpool.actors_len ▸ hlt_a
    have hΘ_some : Θ.actors[aid]? = some Θ.actors[aid] := List.getElem?_eq_getElem hlt_Θ
    rcases hpool.actors_ty aid Θ.actors[aid] hΘ_some with ⟨act0, hact0, hphTy, _⟩
    rw [hact] at hact0; cases hact0
    rw [hph] at hphTy
    rcases hown.actor_locs aid act hact with ⟨hact_own, hmb_own⟩
    have he_own : ∀ l ∈ exprLocs e, owners[l]? = some (.actor aid) := by
      intro l hl; apply hact_own l; simp [hph, actorPhaseLocs, hl]
    have hsv_own : ∀ l ∈ exprLocs sv, owners[l]? = some (.actor aid) := by
      intro l hl; apply hact_own l; simp [hph, actorPhaseLocs, hl]
    cases reply with
    | none =>
      rcases hphTy with ⟨hsv, hsvTy, heTy⟩
      rcases preservation hΦ heTy hs hσ hpool with ⟨Ψ', Θ', hsExt, heff, heTy', hσ'⟩
      have htkExt := effTyped_extends heff
      have hp_weak := poolTyped_weaken_entries hsExt htkExt hpool
      have hbusy' : ActorPhaseTyped Δ Φ Ψ' Θ' Θ.actors[aid] (.busy sv e' none) :=
        ⟨hsv, typing_env_weaken hsExt htkExt hsvTy, heTy'⟩
      have hp1 := setPoolActorPhase_entries hp_weak hΘ_some hbusy'
      have hpool' := applyConcEff_preserves_typed hp1 heff
      rcases step_preserves_ownership hΦ heTy hs hpool hown.mvar_locs hown.chan_locs
        hown.len_eq he_own hown.store_locs with
        ⟨owners', hownExt, hlen', he_own', hst_own', hclean⟩
      have hown1 : HeapOwned owners' (setPoolActorPhase pool aid (.busy sv e' none)) σ' :=
        { len_eq     := hlen'
          task_locs  := fun k ek l hek hl =>
            hownExt l (.task k) (hown.task_locs k ek l (by simpa [setPoolActorPhase, hact, setPoolActor] using hek) hl)
          actor_locs := fun k actk hk => by
            by_cases hka : k = aid
            · subst hka
              simp only [setPoolActorPhase, hact, setPoolActor, List.getElem?_set_self hlt_a,
                Option.some.injEq] at hk
              subst hk
              refine ⟨fun l hl => ?_, hmb_own⟩
              simp only [actorPhaseLocs, List.mem_append] at hl
              rcases hl with h1 | h2
              · exact hownExt l (.actor k) (hsv_own l h1)
              · exact he_own' l h2
            · simp only [setPoolActorPhase, hact, setPoolActor, List.getElem?_set_ne (Ne.symm hka)] at hk
              rcases hown.actor_locs k actk hk with ⟨hphk, hmbk⟩
              exact ⟨fun l hl => hownExt l (.actor k) (hphk l hl), hmbk⟩
          mvar_locs  := fun m v hm => hown.mvar_locs m v (by simpa [setPoolActorPhase, hact, setPoolActor] using hm)
          chan_locs  := fun c ch v hc hv => hown.chan_locs c ch v (by simpa [setPoolActorPhase, hact, setPoolActor] using hc) hv
          store_locs := hst_own' }
      exact ⟨Ψ', Θ', owners', hσ', hpool', applyConcEff_preserves_owned hown1 hclean⟩
    | some tid =>
      rcases hphTy with ⟨hsv, hsvTy, r_ty, htid, hsend, heTy⟩
      rcases preservation hΦ heTy hs hσ hpool with ⟨Ψ', Θ', hsExt, heff, heTy', hσ'⟩
      have htkExt := effTyped_extends heff
      have hp_weak := poolTyped_weaken_entries hsExt htkExt hpool
      have hbusy' : ActorPhaseTyped Δ Φ Ψ' Θ' Θ.actors[aid] (.busy sv e' (some tid)) :=
        ⟨hsv, typing_env_weaken hsExt htkExt hsvTy, r_ty, htkExt.tasks.2 _ _ htid, hsend, heTy'⟩
      have hp1 := setPoolActorPhase_entries hp_weak hΘ_some hbusy'
      have hpool' := applyConcEff_preserves_typed hp1 heff
      rcases step_preserves_ownership hΦ heTy hs hpool hown.mvar_locs hown.chan_locs
        hown.len_eq he_own hown.store_locs with
        ⟨owners', hownExt, hlen', he_own', hst_own', hclean⟩
      have hown1 : HeapOwned owners' (setPoolActorPhase pool aid (.busy sv e' (some tid))) σ' :=
        { len_eq     := hlen'
          task_locs  := fun k ek l hek hl =>
            hownExt l (.task k) (hown.task_locs k ek l (by simpa [setPoolActorPhase, hact, setPoolActor] using hek) hl)
          actor_locs := fun k actk hk => by
            by_cases hka : k = aid
            · subst hka
              simp only [setPoolActorPhase, hact, setPoolActor, List.getElem?_set_self hlt_a,
                Option.some.injEq] at hk
              subst hk
              refine ⟨fun l hl => ?_, hmb_own⟩
              simp only [actorPhaseLocs, List.mem_append] at hl
              rcases hl with h1 | h2
              · exact hownExt l (.actor k) (hsv_own l h1)
              · exact he_own' l h2
            · simp only [setPoolActorPhase, hact, setPoolActor, List.getElem?_set_ne (Ne.symm hka)] at hk
              rcases hown.actor_locs k actk hk with ⟨hphk, hmbk⟩
              exact ⟨fun l hl => hownExt l (.actor k) (hphk l hl), hmbk⟩
          mvar_locs  := fun m v hm => hown.mvar_locs m v (by simpa [setPoolActorPhase, hact, setPoolActor] using hm)
          chan_locs  := fun c ch v hc hv => hown.chan_locs c ch v (by simpa [setPoolActorPhase, hact, setPoolActor] using hc) hv
          store_locs := hst_own' }
      exact ⟨Ψ', Θ', owners', hσ', hpool', applyConcEff_preserves_owned hown1 hclean⟩

  | .actorBusyDone (aid := aid) (act := act) (sv := sv) (v := v) (reply := reply) hact hph hv =>
    have hlt_a : aid < pool.actors.length := lt_length_of_getElem?_eq_some hact
    have hlt_Θ : aid < Θ.actors.length := hpool.actors_len ▸ hlt_a
    have hΘ_some : Θ.actors[aid]? = some Θ.actors[aid] := List.getElem?_eq_getElem hlt_Θ
    rcases hpool.actors_ty aid Θ.actors[aid] hΘ_some with ⟨act0, hact0, hphTy, _⟩
    rw [hact] at hact0; cases hact0
    rw [hph] at hphTy
    rcases hown.actor_locs aid act hact with ⟨hact_own, hmb_own⟩
    have hsv_own : ∀ l ∈ exprLocs sv, owners[l]? = some (.actor aid) := by
      intro l hl; apply hact_own l; simp [hph, actorPhaseLocs, hl]
    have hp0 := poolTyped_weaken_entries (StoreExtends.refl Ψ) (TaskExtends.refl Θ) hpool
    cases reply with
    | none =>
      rcases hphTy with ⟨hsv, hsvTy, _⟩
      have hp1 := poolEntries_to_poolTyped (setPoolActorPhase_entries hp0 hΘ_some (ph' := .idle sv) ⟨hsv, hsvTy⟩)
      refine ⟨Ψ, Θ, owners, hσ, hp1,
        { len_eq     := hown.len_eq
          task_locs  := fun k ek l hek hl =>
            hown.task_locs k ek l (by simpa [setPoolActorPhase, hact, setPoolActor] using hek) hl
          actor_locs := fun k actk hk => by
            by_cases hka : k = aid
            · subst hka
              simp only [setPoolActorPhase, hact, setPoolActor, List.getElem?_set_self hlt_a,
                Option.some.injEq] at hk
              subst hk
              exact ⟨hsv_own, hmb_own⟩
            · simp only [setPoolActorPhase, hact, setPoolActor, List.getElem?_set_ne (Ne.symm hka)] at hk
              exact hown.actor_locs k actk hk
          mvar_locs  := fun m u hm => hown.mvar_locs m u (by simpa [setPoolActorPhase, hact, setPoolActor] using hm)
          chan_locs  := fun c ch u hc hu => hown.chan_locs c ch u (by simpa [setPoolActorPhase, hact, setPoolActor] using hc) hu
          store_locs := hown.store_locs }⟩
    | some tid =>
      rcases hphTy with ⟨hsv, hsvTy, r_ty, htid, hsend, hvTy⟩
      have hvNil : exprLocs v = [] := exprLocs_empty_of_isValue_isSend hvTy hv hsend
      have hp1 := setPoolActorPhase_entries hp0 hΘ_some (ph' := .idle sv) ⟨hsv, hsvTy⟩
      have hp2 := poolEntries_to_poolTyped (setPoolTask_entries hp1 htid hvTy)
      have hlt_t : tid < (setPoolActorPhase pool aid (.idle sv)).tasks.length := by
        simp [setPoolActorPhase, hact, setPoolActor, hpool.tasks_len]
        exact lt_length_of_getElem?_eq_some htid
      refine ⟨Ψ, Θ, owners, hσ, hp2,
        { len_eq     := hown.len_eq
          task_locs  := fun k ek l hek hl => by
            by_cases hkt : k = tid
            · subst hkt
              simp only [setPoolTask, List.getElem?_set_self hlt_t, Option.some.injEq,
                TaskEntry.running.injEq] at hek
              subst hek; rw [hvNil] at hl; cases hl
            · simp only [setPoolTask, List.getElem?_set_ne (Ne.symm hkt)] at hek
              exact hown.task_locs k ek l (by simpa [setPoolActorPhase, hact, setPoolActor] using hek) hl
          actor_locs := fun k actk hk => by
            simp only [setPoolTask] at hk
            by_cases hka : k = aid
            · subst hka
              simp only [setPoolActorPhase, hact, setPoolActor, List.getElem?_set_self hlt_a,
                Option.some.injEq] at hk
              subst hk
              exact ⟨hsv_own, hmb_own⟩
            · simp only [setPoolActorPhase, hact, setPoolActor, List.getElem?_set_ne (Ne.symm hka)] at hk
              exact hown.actor_locs k actk hk
          mvar_locs  := fun m u hm => hown.mvar_locs m u (by simpa [setPoolTask, setPoolActorPhase, hact, setPoolActor] using hm)
          chan_locs  := fun c ch u hc hu => hown.chan_locs c ch u (by simpa [setPoolTask, setPoolActorPhase, hact, setPoolActor] using hc) hu
          store_locs := hown.store_locs }⟩

  | .actorBusyTrap (aid := aid) (act := act) (t := t) (reply := reply) hact hph =>
    have hlt_a : aid < pool.actors.length := lt_length_of_getElem?_eq_some hact
    have hlt_Θ : aid < Θ.actors.length := hpool.actors_len ▸ hlt_a
    have hΘ_some : Θ.actors[aid]? = some Θ.actors[aid] := List.getElem?_eq_getElem hlt_Θ
    rcases hpool.actors_ty aid Θ.actors[aid] hΘ_some with ⟨act0, hact0, hphTy, _⟩
    rw [hact] at hact0; cases hact0
    rw [hph] at hphTy
    rcases hown.actor_locs aid act hact with ⟨_, hmb_own⟩
    have hp0 := poolTyped_weaken_entries (StoreExtends.refl Ψ) (TaskExtends.refl Θ) hpool
    have hp1 := setPoolActorPhase_entries hp0 hΘ_some (ph' := .failed t) trivial
    cases reply with
    | none =>
      refine ⟨Ψ, Θ, owners, hσ, poolEntries_to_poolTyped hp1,
        { len_eq     := hown.len_eq
          task_locs  := fun k ek l hek hl =>
            hown.task_locs k ek l (by simpa [setPoolActorPhase, hact, setPoolActor] using hek) hl
          actor_locs := fun k actk hk => by
            by_cases hka : k = aid
            · subst hka
              simp only [setPoolActorPhase, hact, setPoolActor, List.getElem?_set_self hlt_a,
                Option.some.injEq] at hk
              subst hk
              exact ⟨(fun _ h => nomatch h), hmb_own⟩
            · simp only [setPoolActorPhase, hact, setPoolActor, List.getElem?_set_ne (Ne.symm hka)] at hk
              exact hown.actor_locs k actk hk
          mvar_locs  := fun m u hm => hown.mvar_locs m u (by simpa [setPoolActorPhase, hact, setPoolActor] using hm)
          chan_locs  := fun c ch u hc hu => hown.chan_locs c ch u (by simpa [setPoolActorPhase, hact, setPoolActor] using hc) hu
          store_locs := hown.store_locs }⟩
    | some tid =>
      rcases hphTy with ⟨_, _, r_ty, htid, _, _⟩
      have hp2 := poolEntries_to_poolTyped (setPoolTask_entries hp1 htid (.trap t r_ty))
      have hlt_t : tid < (setPoolActorPhase pool aid (.failed t)).tasks.length := by
        simp [setPoolActorPhase, hact, setPoolActor, hpool.tasks_len]
        exact lt_length_of_getElem?_eq_some htid
      refine ⟨Ψ, Θ, owners, hσ, hp2,
        { len_eq     := hown.len_eq
          task_locs  := fun k ek l hek hl => by
            by_cases hkt : k = tid
            · subst hkt
              simp only [setPoolTask, List.getElem?_set_self hlt_t, Option.some.injEq,
                TaskEntry.running.injEq] at hek
              subst hek; cases hl
            · simp only [setPoolTask, List.getElem?_set_ne (Ne.symm hkt)] at hek
              exact hown.task_locs k ek l (by simpa [setPoolActorPhase, hact, setPoolActor] using hek) hl
          actor_locs := fun k actk hk => by
            simp only [setPoolTask] at hk
            by_cases hka : k = aid
            · subst hka
              simp only [setPoolActorPhase, hact, setPoolActor, List.getElem?_set_self hlt_a,
                Option.some.injEq] at hk
              subst hk
              exact ⟨(fun _ h => nomatch h), hmb_own⟩
            · simp only [setPoolActorPhase, hact, setPoolActor, List.getElem?_set_ne (Ne.symm hka)] at hk
              exact hown.actor_locs k actk hk
          mvar_locs  := fun m u hm => hown.mvar_locs m u (by simpa [setPoolTask, setPoolActorPhase, hact, setPoolActor] using hm)
          chan_locs  := fun c ch u hc hu => hown.chan_locs c ch u (by simpa [setPoolTask, setPoolActorPhase, hact, setPoolActor] using hc) hu
          store_locs := hown.store_locs }⟩

  | .actorFailedReply (aid := aid) (t := t) (msg := msg) (rest := rest) hact =>
    have hlt_a : aid < pool.actors.length := lt_length_of_getElem?_eq_some hact
    have hlt_Θ : aid < Θ.actors.length := hpool.actors_len ▸ hlt_a
    have hΘ_some : Θ.actors[aid]? = some Θ.actors[aid] := List.getElem?_eq_getElem hlt_Θ
    rcases hpool.actors_ty aid Θ.actors[aid] hΘ_some with ⟨act0, hact0, _, hmbTy⟩
    rw [hact] at hact0; cases hact0
    have hmsgTy := hmbTy msg (List.mem_cons_self ..)
    rcases hown.actor_locs aid _ hact with ⟨_, hmb_own⟩
    let p1 := setPoolActor pool aid { phase := .failed t, mailbox := rest }
    have hp1 : PoolEntriesTyped Δ Φ Ψ Θ Θ p1 :=
      { tasks_len  := hpool.tasks_len
        tasks_ty   := hpool.tasks_ty
        mvars_len  := hpool.mvars_len
        mvars_ty   := hpool.mvars_ty
        chans_len  := hpool.chans_len
        chans_ty   := hpool.chans_ty
        actors_len := by simp [p1, setPoolActor, hpool.actors_len]
        actors_ty  := fun k σk hk => by
          by_cases hka : k = aid
          · subst hka
            rw [hΘ_some] at hk; cases hk
            exact ⟨{ phase := .failed t, mailbox := rest },
              by simp only [p1, setPoolActor]; exact List.getElem?_set_self hlt_a,
              trivial, fun m hm => hmbTy m (List.mem_cons_of_mem _ hm)⟩
          · rcases hpool.actors_ty k σk hk with ⟨actk, hactk, hphk, hmbk⟩
            exact ⟨actk, by simp only [p1, setPoolActor, List.getElem?_set_ne (Ne.symm hka)]; exact hactk, hphk, hmbk⟩ }
    have hown1 : HeapOwned owners p1 σ :=
      { len_eq     := hown.len_eq
        task_locs  := hown.task_locs
        actor_locs := fun k actk hk => by
          by_cases hka : k = aid
          · subst hka
            simp only [p1, setPoolActor, List.getElem?_set_self hlt_a, Option.some.injEq] at hk
            subst hk
            exact ⟨(fun _ h => nomatch h), fun m hm => hmb_own m (List.mem_cons_of_mem _ hm)⟩
          · simp only [p1, setPoolActor, List.getElem?_set_ne (Ne.symm hka)] at hk
            exact hown.actor_locs k actk hk
        mvar_locs  := hown.mvar_locs
        chan_locs  := hown.chan_locs
        store_locs := hown.store_locs }
    cases hrep : msg.replyTask with
    | none =>
      exact ⟨Ψ, Θ, owners, hσ, poolEntries_to_poolTyped hp1, hown1⟩
    | some tid =>
      simp only [ActorMsgTyped, hrep] at hmsgTy
      rcases hmsgTy with ⟨_, r_ty, htid, _, _⟩
      have hp2 := poolEntries_to_poolTyped (setPoolTask_entries hp1 htid (.trap t r_ty))
      have hlt_t : tid < (setPoolActor pool aid { phase := .failed t, mailbox := rest }).tasks.length := by
        simp [setPoolActor, hpool.tasks_len]
        exact lt_length_of_getElem?_eq_some htid
      refine ⟨Ψ, Θ, owners, hσ, hp2,
        { len_eq     := hown1.len_eq
          task_locs  := fun k ek l hek hl => by
            by_cases hkt : k = tid
            · subst hkt
              simp only [setPoolTask, List.getElem?_set_self hlt_t, Option.some.injEq,
                TaskEntry.running.injEq] at hek
              subst hek; cases hl
            · simp only [setPoolTask, List.getElem?_set_ne (Ne.symm hkt)] at hek
              exact hown1.task_locs k ek l hek hl
          actor_locs := fun k actk hk => hown1.actor_locs k actk (by simpa [setPoolTask] using hk)
          mvar_locs  := fun m u hm => hown1.mvar_locs m u (by simpa [setPoolTask] using hm)
          chan_locs  := fun c ch u hc hu => hown1.chan_locs c ch u (by simpa [setPoolTask] using hc) hu
          store_locs := hown1.store_locs }⟩

theorem concSteps_preserves_inv {Δ : AdtEnv} {Φ : FunEnv} (hΦ : FunEnvTyped Δ Φ)
    {p0 pool : ConcPool} {σ0 σ : Store}
    (hinv0 : ConcInv Δ Φ p0 σ0)
    (hsteps : ConcSteps Δ Φ p0 σ0 pool σ) :
    ConcInv Δ Φ pool σ := by
  induction hsteps with
  | refl => exact hinv0
  | trans hs _ ih => exact ih (concStep_preserves_inv hΦ hinv0 hs)

/-! ## Top-Level Concurrent Safety, Heap Disjointness & Data-Race Freedom -/

/-- Initial 1-thread configuration `initPool e0` (`main : Void`) on empty heap `[]` satisfies `ConcInv`. -/
theorem concInv_init {Δ : AdtEnv} {Φ : FunEnv} {e0 : Expr}
    (ht0 : HasType Δ Φ [] emptyTaskTy emptyCtx e0 .void) :
    ConcInv Δ Φ (initPool e0) [] := by
  have he0_locs : exprLocs e0 = [] := exprLocs_empty_of_empty_store ht0
  let Θ0 : TaskTy := { tasks := [.void] }
  have hextT : TaskExtends emptyTaskTy Θ0 := TaskExtends.appendTask emptyTaskTy .void
  have ht0' : HasType Δ Φ [] Θ0 emptyCtx e0 .void :=
    typing_env_weaken (StoreExtends.refl []) hextT ht0
  have hvoidSend : IsSend Δ .void := by
    refine ⟨fun _ => False, ?_, TySendIn.void⟩
    intro _ h; cases h
  refine ⟨[], Θ0, [], ?_, ?_, ?_⟩
  · exact ⟨rfl, fun _ _ h => by simp at h⟩
  · refine
      { tasks_len  := rfl
        tasks_ty   := fun tid τ htid => ?_
        mvars_len  := rfl
        mvars_ty   := fun _ _ h => by simp [Θ0] at h
        chans_len  := rfl
        chans_ty   := fun _ _ h => by simp [Θ0] at h
        actors_len := rfl
        actors_ty  := fun _ _ h => by simp [Θ0] at h }
    cases tid with
    | zero =>
      simp [Θ0] at htid; subst htid
      exact ⟨hvoidSend, .running e0, rfl, fun u hu => by cases hu; exact ht0'⟩
    | succ _ => simp [Θ0] at htid
  · refine
      { len_eq     := rfl
        task_locs  := fun tid e l het hl => ?_
        actor_locs := fun _ _ h => by simp [initPool] at h
        mvar_locs  := fun _ _ h => by simp [initPool] at h
        chan_locs  := fun _ _ _ h => by simp [initPool] at h
        store_locs := fun _ _ _ h => by simp at h }
    cases tid with
    | zero =>
      simp [initPool] at het; subst het
      rw [he0_locs] at hl; cases hl
    | succ _ => simp [initPool] at het

theorem activeThreadExpr_owner {owners : List ThreadId} {pool : ConcPool} {σ : Store}
    (hown : HeapOwned owners pool σ)
    {th : ThreadId} {e : Expr} {l : Loc}
    (hae : activeThreadExpr pool th = some e)
    (hl : l ∈ exprLocs e) :
    owners[l]? = some th := by
  cases th with
  | task tid =>
    simp only [activeThreadExpr] at hae
    cases hte : pool.tasks[tid]? with
    | none => rw [hte] at hae; cases hae
    | some te =>
      rw [hte] at hae
      cases te with
      | pendingReply => cases hae
      | running er =>
        dsimp only at hae
        cases hae
        exact hown.task_locs tid e l hte hl
  | actor aid =>
    simp only [activeThreadExpr] at hae
    cases hact : pool.actors[aid]? with
    | none => rw [hact] at hae; cases hae
    | some act =>
      rw [hact] at hae
      rcases hown.actor_locs aid act hact with ⟨hph_own, _⟩
      cases act with
      | mk ph mb =>
        cases ph with
        | init ei =>
          dsimp only at hae; cases hae
          exact hph_own l (by simp [actorPhaseLocs, hl])
        | idle _ => dsimp only at hae; cases hae
        | busy sv eb rep =>
          dsimp only at hae; cases hae
          exact hph_own l (by simp [actorPhaseLocs, hl])
        | failed _ => dsimp only at hae; cases hae

/-- **Concurrent Type Safety (`Task`s & `Actor`s)**: Across any arbitrary interleaving
    of `Task`s, `MVar`s, `Chan`s, and `Actor`s (`ConcSteps`), NO active thread
    (`Task` or `Actor`) ever enters an undefined/stuck state (`¬ IsStuck`). -/
theorem conc_type_safety {Δ : AdtEnv} {Φ : FunEnv} {e0 : Expr}
    {pool : ConcPool} {σ : Store}
    (hΦ : FunEnvTyped Δ Φ)
    (ht0 : HasType Δ Φ [] emptyTaskTy emptyCtx e0 .void)
    (hsteps : ConcSteps Δ Φ (initPool e0) [] pool σ) :
    ∀ (th : ThreadId) (e : Expr),
      activeThreadExpr pool th = some e → ¬ IsStuck Δ Φ pool e σ := by
  rcases concSteps_preserves_inv hΦ (concInv_init ht0) hsteps with ⟨Ψ, Θ, _, hσ, hpool, _⟩
  intro th e hae ⟨hnt, hnblk, hns⟩
  have heTy : ∃ τ, HasType Δ Φ Ψ Θ emptyCtx e τ := by
    cases th with
    | task tid =>
      simp only [activeThreadExpr] at hae
      cases hte : pool.tasks[tid]? with
      | none => rw [hte] at hae; cases hae
      | some te =>
        rw [hte] at hae
        cases te with
        | pendingReply => cases hae
        | running er =>
          dsimp only at hae; cases hae
          have hlt_t : tid < pool.tasks.length := lt_length_of_getElem?_eq_some hte
          have hlt_Θ : tid < Θ.tasks.length := hpool.tasks_len ▸ hlt_t
          rcases hpool.tasks_ty tid Θ.tasks[tid] (List.getElem?_eq_getElem hlt_Θ) with ⟨_, te1, hte1, hrun⟩
          rw [hte] at hte1; cases hte1
          exact ⟨_, hrun e rfl⟩
    | actor aid =>
      simp only [activeThreadExpr] at hae
      cases hact : pool.actors[aid]? with
      | none => rw [hact] at hae; cases hae
      | some act =>
        rw [hact] at hae
        have hlt_a : aid < pool.actors.length := lt_length_of_getElem?_eq_some hact
        have hlt_Θ : aid < Θ.actors.length := hpool.actors_len ▸ hlt_a
        rcases hpool.actors_ty aid Θ.actors[aid] (List.getElem?_eq_getElem hlt_Θ) with ⟨act1, hact1, hphTy, _⟩
        rw [hact] at hact1; cases hact1
        cases act with
        | mk ph mb =>
          cases ph with
          | init ei =>
            dsimp only [ActorPhaseTyped] at hae hphTy; cases hae
            exact ⟨_, hphTy⟩
          | idle _ => dsimp only at hae; cases hae
          | busy sv eb rep =>
            dsimp only [ActorPhaseTyped] at hae hphTy; cases hae
            cases rep with
            | none => exact ⟨.void, hphTy.2.2⟩
            | some _ => rcases hphTy.2.2 with ⟨r_ty, _, _, hbTy⟩; exact ⟨r_ty, hbTy⟩
          | failed _ => dsimp only at hae; cases hae
  rcases heTy with ⟨τ, heTy⟩
  rcases progress hΦ heTy hσ hpool with hterm | hblk | hs
  · exact hnt hterm
  · exact hnblk hblk
  · exact hns hs

/-- **Global Heap Location Disjointness**: At every reachable concurrent
    configuration, any two distinct threads `th1 ≠ th2` (Task-Task, Task-Actor,
    or Actor-Actor) hold strictly disjoint sets of reachable `Cell` heap locations. -/
theorem conc_heap_disjoint {Δ : AdtEnv} {Φ : FunEnv} {e0 : Expr}
    {pool : ConcPool} {σ : Store}
    (hΦ : FunEnvTyped Δ Φ)
    (ht0 : HasType Δ Φ [] emptyTaskTy emptyCtx e0 .void)
    (hsteps : ConcSteps Δ Φ (initPool e0) [] pool σ) :
    ∀ (th1 th2 : ThreadId) (e1 e2 : Expr) (l : Loc),
      th1 ≠ th2 →
      activeThreadExpr pool th1 = some e1 →
      activeThreadExpr pool th2 = some e2 →
      l ∈ exprLocs e1 →
      l ∉ exprLocs e2 := by
  rcases concSteps_preserves_inv hΦ (concInv_init ht0) hsteps with ⟨_, _, owners, _, _, hown⟩
  intro th1 th2 e1 e2 l hne ha1 ha2 hl1 hl2
  have ho1 := activeThreadExpr_owner hown ha1 hl1
  have ho2 := activeThreadExpr_owner hown ha2 hl2
  rw [ho1] at ho2
  cases ho2
  exact hne rfl

/-- **Compile-Time Data-Race Freedom Theorem (`Task` + `MVar` + `Chan` + `Actor`)**:
    Well-typed Core Geisha programs are completely free of `Cell` data races
    (`¬ HasDataRace pool`) across all possible concurrent thread and actor interleavings. -/
theorem conc_data_race_freedom {Δ : AdtEnv} {Φ : FunEnv} {e0 : Expr}
    {pool : ConcPool} {σ : Store}
    (hΦ : FunEnvTyped Δ Φ)
    (ht0 : HasType Δ Φ [] emptyTaskTy emptyCtx e0 .void)
    (hsteps : ConcSteps Δ Φ (initPool e0) [] pool σ) :
    ¬ HasDataRace pool := by
  intro ⟨th1, th2, e1, e2, b1, b2, l, hne, ha1, ha2, hacc1, hacc2, _⟩
  exact conc_heap_disjoint hΦ ht0 hsteps th1 th2 e1 e2 l hne ha1 ha2
    (activeCellAccess_mem_exprLocs e1 hacc1)
    (activeCellAccess_mem_exprLocs e2 hacc2)

end CoreGeisha
