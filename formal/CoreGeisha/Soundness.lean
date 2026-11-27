import CoreGeisha.Syntax
import CoreGeisha.Typing
import CoreGeisha.Semantics

/-!
# Core Geisha: Type Soundness, Capture-Mode Subtyping, and Zero-Location Lemma

Machine-checked proof (zero `sorry`, zero external dependencies beyond Lean 4
core) of:
- Reflexivity, transitivity, and admissibility (`typing_sub`) of capture-mode subtyping
- Coinductive unfolding and subtyping monotonicity of `IsSend`
- **Zero-Location Lemma** (`exprLocs_empty_of_isValue_isSend`): every closed
  well-typed `IsSend` value contains zero mutable `Cell` heap locations
- Substitution preservation under lexical `shared` closure capture checking
- Single-thread **Progress** and **Preservation** (including `spawn` / `await`)
-/

namespace CoreGeisha

/-! ## Store, Task & Context Auxiliary Lemmas -/

theorem ListExtends.refl (xs : List Ty) : ListExtends xs xs :=
  ⟨Nat.le_refl _, fun _ _ h => h⟩

theorem ListExtends.trans {xs ys zs : List Ty}
    (h12 : ListExtends xs ys) (h23 : ListExtends ys zs) : ListExtends xs zs :=
  ⟨Nat.le_trans h12.1 h23.1, fun i τ h => h23.2 i τ (h12.2 i τ h)⟩

theorem ListExtends.empty (xs : List Ty) : ListExtends [] xs :=
  ⟨Nat.zero_le _, fun _ _ h => by simp at h⟩

theorem StoreExtends.refl (Ψ : StoreTy) : StoreExtends Ψ Ψ :=
  ListExtends.refl Ψ

theorem StoreExtends.trans {Ψ1 Ψ2 Ψ3 : StoreTy}
    (h12 : StoreExtends Ψ1 Ψ2) (h23 : StoreExtends Ψ2 Ψ3) : StoreExtends Ψ1 Ψ3 :=
  ListExtends.trans h12 h23

theorem TaskExtends.refl (Θ : TaskTy) : TaskExtends Θ Θ :=
  ⟨ListExtends.refl _, ListExtends.refl _, ListExtends.refl _, ListExtends.refl _⟩

theorem TaskExtends.trans {Θ1 Θ2 Θ3 : TaskTy}
    (h12 : TaskExtends Θ1 Θ2) (h23 : TaskExtends Θ2 Θ3) : TaskExtends Θ1 Θ3 :=
  ⟨ListExtends.trans h12.tasks h23.tasks,
   ListExtends.trans h12.mvars h23.mvars,
   ListExtends.trans h12.chans h23.chans,
   ListExtends.trans h12.actors h23.actors⟩

theorem TaskExtends.empty (Θ : TaskTy) : TaskExtends emptyTaskTy Θ :=
  ⟨ListExtends.empty _, ListExtends.empty _, ListExtends.empty _, ListExtends.empty _⟩

theorem lt_length_of_getElem?_eq_some {α : Type} {xs : List α} {l : Nat} {a : α}
    (h : xs[l]? = some a) : l < xs.length := by
  cases Nat.lt_or_ge l xs.length with
  | inl hlt => exact hlt
  | inr hge =>
    rw [List.getElem?_eq_none hge] at h
    cases h

theorem ListExtends.append (xs : List Ty) (τ : Ty) : ListExtends xs (xs ++ [τ]) := by
  refine ⟨by simp, fun l t h => ?_⟩
  have hlt : l < xs.length := lt_length_of_getElem?_eq_some h
  rw [List.getElem?_append_left hlt]
  exact h

theorem StoreExtends.append (Ψ : StoreTy) (τ : Ty) : StoreExtends Ψ (Ψ ++ [τ]) :=
  ListExtends.append Ψ τ

theorem TaskExtends.appendTask (Θ : TaskTy) (τ : Ty) :
    TaskExtends Θ { Θ with tasks := Θ.tasks ++ [τ] } :=
  ⟨ListExtends.append Θ.tasks τ, ListExtends.refl _, ListExtends.refl _, ListExtends.refl _⟩

theorem TaskExtends.appendMVar (Θ : TaskTy) (τ : Ty) :
    TaskExtends Θ { Θ with mvars := Θ.mvars ++ [τ] } :=
  ⟨ListExtends.refl _, ListExtends.append Θ.mvars τ, ListExtends.refl _, ListExtends.refl _⟩

theorem TaskExtends.appendChan (Θ : TaskTy) (τ : Ty) :
    TaskExtends Θ { Θ with chans := Θ.chans ++ [τ] } :=
  ⟨ListExtends.refl _, ListExtends.refl _, ListExtends.append Θ.chans τ, ListExtends.refl _⟩

theorem TaskExtends.appendActor (Θ : TaskTy) (τ : Ty) :
    TaskExtends Θ { Θ with actors := Θ.actors ++ [τ] } :=
  ⟨ListExtends.refl _, ListExtends.refl _, ListExtends.refl _, ListExtends.append Θ.actors τ⟩

theorem extendMany_append (Γ : Ctx) (bs1 bs2 : List (Ident × Ty)) :
    extendMany Γ (bs1 ++ bs2) = extendMany (extendMany Γ bs2) bs1 := by
  induction bs1 with
  | nil => rfl
  | cons b rest ih =>
    cases b with
    | mk x τ => simp only [List.cons_append, extendMany, ih]

theorem extendCtx_shadow (Γ : Ctx) (x : Ident) (τ1 τ2 : Ty) :
    extendCtx (extendCtx Γ x τ1) x τ2 = extendCtx Γ x τ2 := by
  funext y
  simp only [extendCtx]
  split <;> rfl

theorem extendCtx_comm (Γ : Ctx) {x y : Ident} (hxy : x ≠ y) (τ1 τ2 : Ty) :
    extendCtx (extendCtx Γ x τ1) y τ2 = extendCtx (extendCtx Γ y τ2) x τ1 := by
  funext z
  simp only [extendCtx]
  by_cases hzy : z = y
  · subst hzy
    have hyx : (z == x) = false := beq_false_of_ne (Ne.symm hxy)
    simp [hyx]
  · have hzy' : (z == y) = false := beq_false_of_ne hzy
    simp [hzy']

theorem extendMany_eq_of_ne (Γ : Ctx) (x z : Ident) (τx : Ty) (hzx : z ≠ x)
    (bs : List (Ident × Ty)) :
    extendMany (extendCtx Γ x τx) bs z = extendMany Γ bs z := by
  induction bs with
  | nil =>
    simp only [extendMany, extendCtx]
    have h : (z == x) = false := beq_false_of_ne hzx
    simp [h]
  | cons p ps ih =>
    cases p with
    | mk k tk =>
      simp only [extendMany, extendCtx]
      split
      · rfl
      · exact ih

theorem extendMany_shadow (Γ : Ctx) (x : Ident) (τx : Ty) (bs : List (Ident × Ty))
    (hmem : x ∈ bs.map Prod.fst) :
    extendMany (extendCtx Γ x τx) bs = extendMany Γ bs := by
  induction bs with
  | nil => simp at hmem
  | cons b rest ih =>
    cases b with
    | mk y τy =>
      simp only [List.map_cons, List.mem_cons] at hmem
      simp only [extendMany]
      rcases hmem with rfl | hrest
      · funext z
        simp only [extendCtx]
        by_cases hzx : z = x
        · subst hzx; simp
        · have hzx' : (z == x) = false := beq_false_of_ne hzx
          simp only [hzx', Bool.false_eq_true, ↓reduceIte]
          exact extendMany_eq_of_ne Γ x z τx hzx rest
      · rw [ih hrest]

theorem extendMany_comm (Γ : Ctx) (x : Ident) (τx : Ty) (bs : List (Ident × Ty))
    (hnot : x ∉ bs.map Prod.fst) :
    extendMany (extendCtx Γ x τx) bs = extendCtx (extendMany Γ bs) x τx := by
  induction bs with
  | nil => rfl
  | cons b rest ih =>
    cases b with
    | mk y τy =>
      simp only [List.map_cons, List.mem_cons, not_or] at hnot
      simp only [extendMany]
      rw [ih hnot.2, extendCtx_comm _ hnot.1]

/-! ## Subtyping Reflexivity, Transitivity & Admissibility (`typing_sub`) -/

theorem ModeSub.trans {m1 m2 m3 : Mode} (h12 : ModeSub m1 m2) (h23 : ModeSub m2 m3) :
    ModeSub m1 m3 := by
  cases h12 <;> cases h23 <;> constructor

mutual
theorem TySub.refl : (t : Ty) → TySub t t
  | .void => .void
  | .int => .int
  | .int64 => .int64
  | .float => .float
  | .float32 => .float32
  | .bool => .bool
  | .char => .char
  | .str => .str
  | .ptr => .ptr
  | .scopedPtr => .scopedPtr
  | .arena => .arena
  | .foreignPtr => .foreignPtr
  | .atomicInt => .atomicInt
  | .tuple ts => .tuple (TyListSub.refl ts)
  | .fn m ps r => .fn (.refl m) (TyListSub.refl ps) (TySub.refl r)
  | .adt n => .adt n
  | .simd128 s => .simd128 s
  | .simd256 s => .simd256 s
  | .cell t => .cell t
  | .mutArray t => .mutArray t
  | .immArray t => .immArray (TySub.refl t)
  | .task t => .task (TySub.refl t)
  | .mvar t => .mvar t
  | .chan t => .chan t
  | .actor t => .actor t

theorem TyListSub.refl : (ts : List Ty) → TyListSub ts ts
  | [] => .nil
  | t :: ts => .cons (TySub.refl t) (TyListSub.refl ts)
end

mutual
theorem TySub.trans {t1 t2 t3 : Ty} (h12 : TySub t1 t2) (h23 : TySub t2 t3) :
    TySub t1 t3 := by
  cases t2 with
  | void => cases h12; cases h23; exact .void
  | int => cases h12; cases h23; exact .int
  | int64 => cases h12; cases h23; exact .int64
  | float => cases h12; cases h23; exact .float
  | float32 => cases h12; cases h23; exact .float32
  | bool => cases h12; cases h23; exact .bool
  | char => cases h12; cases h23; exact .char
  | str => cases h12; cases h23; exact .str
  | ptr => cases h12; cases h23; exact .ptr
  | scopedPtr => cases h12; cases h23; exact .scopedPtr
  | arena => cases h12; cases h23; exact .arena
  | foreignPtr => cases h12; cases h23; exact .foreignPtr
  | atomicInt => cases h12; cases h23; exact .atomicInt
  | tuple ts2 =>
    cases h12 with
    | tuple hs12 =>
      cases h23 with
      | tuple hs23 => exact .tuple (TyListSub.trans hs12 hs23)
  | fn m2 ps2 r2 =>
    cases h12 with
    | fn hm12 hps12 hr12 =>
      cases h23 with
      | fn hm23 hps23 hr23 =>
        exact .fn (ModeSub.trans hm12 hm23) (TyListSub.trans hps23 hps12) (TySub.trans hr12 hr23)
  | adt n => cases h12; cases h23; exact .adt n
  | simd128 s => cases h12; cases h23; exact .simd128 s
  | simd256 s => cases h12; cases h23; exact .simd256 s
  | cell t => cases h12; cases h23; exact .cell t
  | mutArray t => cases h12; cases h23; exact .mutArray t
  | immArray u2 =>
    cases h12 with
    | immArray hs12 =>
      cases h23 with
      | immArray hs23 => exact .immArray (TySub.trans hs12 hs23)
  | task u2 =>
    cases h12 with
    | task hs12 =>
      cases h23 with
      | task hs23 => exact .task (TySub.trans hs12 hs23)
  | mvar t => cases h12; cases h23; exact .mvar t
  | chan t => cases h12; cases h23; exact .chan t
  | actor t => cases h12; cases h23; exact .actor t
termination_by sizeOf t2

theorem TyListSub.trans {ts1 ts2 ts3 : List Ty}
    (h12 : TyListSub ts1 ts2) (h23 : TyListSub ts2 ts3) : TyListSub ts1 ts3 := by
  cases ts2 with
  | nil => cases h12; cases h23; exact .nil
  | cons u2 us2 =>
    cases h12 with
    | cons ht12 hts12 =>
      cases h23 with
      | cons ht23 hts23 =>
        exact .cons (TySub.trans ht12 ht23) (TyListSub.trans hts12 hts23)
termination_by sizeOf ts2
end

theorem tyListSub_length : {ts1 ts2 : List Ty} → TyListSub ts1 ts2 → ts1.length = ts2.length
  | _, _, .nil => rfl
  | _, _, .cons _ hs => by simp [tyListSub_length hs]

/- Admissibility of subsumption for syntax-directed `HasType`. -/
mutual
theorem typing_sub {Δ : AdtEnv} {Φ : FunEnv} {Ψ : StoreTy} {Θ : TaskTy} {Γ : Ctx}
    {e : Expr} {τ1 τ2 : Ty}
    (hsub : TySub τ1 τ2) (ht : HasType Δ Φ Ψ Θ Γ e τ1) :
    HasType Δ Φ Ψ Θ Γ e τ2 := by
  cases ht with
  | lit hl =>
    cases hl <;> cases hsub <;> exact .lit (by constructor)
  | var hx hs0 => exact .var hx (TySub.trans hs0 hsub)
  | loc hl =>
    cases hsub
    exact .loc hl
  | taskRef htid hsend hs0 =>
    cases hsub with
    | task hs => exact .taskRef htid hsend (TySub.trans hs0 hs)
  | syncRef hsr =>
    cases hsr with
    | mvar hm hsend => cases hsub; exact .syncRef (.mvar hm hsend)
    | chan hc hsend => cases hsub; exact .syncRef (.chan hc hsend)
    | actor ha => cases hsub; exact .syncRef (.actor ha)
  | tuple hts =>
    cases hsub with
    | tuple htsub => exact .tuple (typingList_sub htsub hts)
  | blockEmpty =>
    cases hsub
    exact .blockEmpty
  | blockSingle he =>
    exact .blockSingle (typing_sub hsub he)
  | blockCons h1 h2 =>
    exact .blockCons h1 (typing_sub hsub h2)
  | lam hm0 hps0 hr0 hbody hsh =>
    cases hsub with
    | fn hm hps hr =>
      exact .lam (ModeSub.trans hm0 hm) (TyListSub.trans hps hps0) (TySub.trans hr0 hr) hbody hsh
  | apply hfn hargs hr0 =>
    exact .apply hfn hargs (TySub.trans hr0 hsub)
  | applyDir hf hargs hr0 =>
    exact .applyDir hf hargs (TySub.trans hr0 hsub)
  | bin hop h1 h2 =>
    cases hop <;> cases hsub <;> exact .bin (by constructor) h1 h2
  | un hop h1 =>
    cases hop <;> cases hsub <;> exact .un (by constructor) h1
  | let_ h1 h2 =>
    exact .let_ h1 (typing_sub hsub h2)
  | if_ hc h1 h2 =>
    exact .if_ hc (typing_sub hsub h1) (typing_sub hsub h2)
  | while_ hc hb =>
    cases hsub
    exact .while_ hc hb
  | match_ hs harms =>
    exact .match_ hs (typingArms_sub hsub harms)
  | makeData hlv hts =>
    cases hsub
    exact .makeData hlv hts
  | getTag h1 =>
    cases hsub
    exact .getTag h1
  | cellNew h1 =>
    cases hsub
    exact .cellNew h1
  | cellGet h1 hs0 =>
    exact .cellGet h1 (TySub.trans hs0 hsub)
  | cellSet h1 h2 =>
    cases hsub
    exact .cellSet h1 h2
  | spawn h1 hsend hs0 =>
    cases hsub with
    | task hs => exact .spawn h1 hsend (TySub.trans hs0 hs)
  | await h1 hsend hs0 =>
    exact .await h1 hsend (TySub.trans hs0 hsub)
  | concPrim hop hargs hs0 =>
    exact .concPrim hop hargs (TySub.trans hs0 hsub)
  | trap t _ => exact .trap t τ2
termination_by sizeOf e

theorem typingList_sub {Δ : AdtEnv} {Φ : FunEnv} {Ψ : StoreTy} {Θ : TaskTy} {Γ : Ctx}
    {es : List Expr} {ts1 ts2 : List Ty}
    (hsub : TyListSub ts1 ts2) (hts : HasTypes Δ Φ Ψ Θ Γ es ts1) :
    HasTypes Δ Φ Ψ Θ Γ es ts2 := by
  cases hts with
  | nil => cases hsub; exact .nil
  | cons h1 hrest =>
    cases hsub with
    | cons hs1 hsrest =>
      exact .cons (typing_sub hs1 h1) (typingList_sub hsrest hrest)
termination_by sizeOf es

theorem typingArms_sub {Δ : AdtEnv} {Φ : FunEnv} {Ψ : StoreTy} {Θ : TaskTy} {Γ : Ctx}
    {τs τr1 τr2 : Ty} {arms : List (Pat × Expr)}
    (hsub : TySub τr1 τr2) (harms : ArmsHaveType Δ Φ Ψ Θ Γ τs arms τr1) :
    ArmsHaveType Δ Φ Ψ Θ Γ τs arms τr2 := by
  cases harms with
  | nil => exact .nil
  | cons hp hb hrest =>
    exact .cons hp (typing_sub hsub hb) (typingArms_sub hsub hrest)
termination_by sizeOf arms
end

/-! ## Coinductive `IsSend` Unfolding & Subtyping Properties -/

inductive AllIsSend (Δ : AdtEnv) : List Ty → Prop where
  | nil : AllIsSend Δ []
  | cons {t : Ty} {ts : List Ty} : IsSend Δ t → AllIsSend Δ ts → AllIsSend Δ (t :: ts)

mutual
theorem tySendIn_of_tySub {S : Ident → Prop} {τ0 τ : Ty}
    (hsub : TySub τ0 τ) (hsend : TySendIn S τ) : TySendIn S τ0 := by
  cases hsub with
  | void => exact .void
  | int => exact .int
  | int64 => exact .int64
  | float => exact .float
  | float32 => exact .float32
  | bool => exact .bool
  | char => exact .char
  | str => exact .str
  | ptr => cases hsend
  | scopedPtr => cases hsend
  | arena => cases hsend
  | foreignPtr => cases hsend
  | atomicInt => exact .atomicInt
  | tuple hts =>
    cases hsend with
    | tuple hls => exact .tuple (tyListSendIn_of_tyListSub hts hls)
  | fn hm _ _ =>
    cases hsend with
    | fnShared _ _ =>
      cases hm with
      | refl => exact .fnShared _ _
  | adt _ => exact hsend
  | simd128 _ => exact .simd128 _
  | simd256 _ => exact .simd256 _
  | cell _ => cases hsend
  | mutArray _ => cases hsend
  | immArray ht =>
    cases hsend with
    | immArray hs => exact .immArray (tySendIn_of_tySub ht hs)
  | task ht =>
    cases hsend with
    | task hs => exact .task (tySendIn_of_tySub ht hs)
  | mvar _ => exact hsend
  | chan _ => exact hsend
  | actor _ => exact hsend

theorem tyListSendIn_of_tyListSub {S : Ident → Prop} {ts0 ts : List Ty}
    (hsub : TyListSub ts0 ts) (hsend : TyListSendIn S ts) : TyListSendIn S ts0 := by
  cases hsub with
  | nil => exact .nil
  | cons ht hts =>
    cases hsend with
    | cons hs hss =>
      exact .cons (tySendIn_of_tySub ht hs) (tyListSendIn_of_tyListSub hts hss)
end

theorem isSend_of_tySub {Δ : AdtEnv} {τ0 τ : Ty}
    (hsub : TySub τ0 τ) (hsend : IsSend Δ τ) : IsSend Δ τ0 := by
  rcases hsend with ⟨S, hclosed, hs⟩
  exact ⟨S, hclosed, tySendIn_of_tySub hsub hs⟩

theorem isSend_cell_false {Δ : AdtEnv} {τ : Ty} : ¬ IsSend Δ (.cell τ) := by
  intro ⟨_, _, hs⟩
  cases hs

theorem isSend_fn_mode {Δ : AdtEnv} {m : Mode} {ps : List Ty} {ret : Ty}
    (hsend : IsSend Δ (.fn m ps ret)) : m = .shared := by
  rcases hsend with ⟨_, _, hs⟩
  cases hs
  rfl

theorem tyListSendIn_to_allIsSend {Δ : AdtEnv} {S : Ident → Prop}
    (hclosed : AdtSendClosed Δ S) : {ts : List Ty} → TyListSendIn S ts → AllIsSend Δ ts
  | _, .nil => .nil
  | _, .cons h1 hrest => .cons ⟨S, hclosed, h1⟩ (tyListSendIn_to_allIsSend hclosed hrest)

theorem isSend_tuple_all {Δ : AdtEnv} {τs : List Ty}
    (hsend : IsSend Δ (.tuple τs)) : AllIsSend Δ τs := by
  rcases hsend with ⟨S, hclosed, hs⟩
  cases hs with
  | tuple hls => exact tyListSendIn_to_allIsSend hclosed hls

theorem isSend_adt_fields {Δ : AdtEnv} {adt : Ident} {tag : Nat} {flds : List Ty}
    (hsend : IsSend Δ (.adt adt)) (hlv : lookupVariant Δ adt tag = some flds) :
    AllIsSend Δ flds := by
  rcases hsend with ⟨S, hclosed, hs⟩
  cases hs with
  | adt hadt =>
    rcases hclosed adt hadt with ⟨defn, hΔ, hvars⟩
    simp only [lookupVariant, hΔ] at hlv
    cases hfind : defn.variants.find? (fun v => v.tag == tag) with
    | none => rw [hfind] at hlv; cases hlv
    | some v =>
      rw [hfind] at hlv
      cases hlv
      have hvmem : v ∈ defn.variants := List.mem_of_find?_eq_some hfind
      exact tyListSendIn_to_allIsSend hclosed (hvars v hvmem)

/-! ## Pattern Bound-Name & Static Zero-Location Lemmas -/

mutual
theorem patHasType_boundNames {Δ : AdtEnv} {p : Pat} {τ : Ty} {bs : List (Ident × Ty)}
    (h : PatHasType Δ p τ bs) : bs.map Prod.fst = patBoundNames p := by
  cases h with
  | wild _ => simp [patBoundNames]
  | var _ _ => simp [patBoundNames]
  | lit _ => simp [patBoundNames]
  | tuple hps => simp only [patBoundNames]; exact patsHaveType_boundNames hps
  | ctor _ hps => simp only [patBoundNames]; exact patsHaveType_boundNames hps

theorem patsHaveType_boundNames {Δ : AdtEnv} {ps : List Pat} {τs : List Ty} {bs : List (Ident × Ty)}
    (h : PatsHaveType Δ ps τs bs) :
    bs.map Prod.fst = ps.foldr (fun p acc => patBoundNames p ++ acc) [] := by
  cases h with
  | nil => rfl
  | cons hp hps =>
    simp only [List.map_append, List.foldr_cons]
    rw [patHasType_boundNames hp, patsHaveType_boundNames hps]
end

/- Any expression well-typed under an empty store typing (`Ψ = []`) contains
   zero literal `Cell` locations. -/
mutual
theorem exprLocs_empty_of_empty_store {Δ : AdtEnv} {Φ : FunEnv} {Θ : TaskTy} {Γ : Ctx}
    {e : Expr} {τ : Ty} (h : HasType Δ Φ [] Θ Γ e τ) : exprLocs e = [] := by
  cases h with
  | lit _ => rfl
  | var _ _ => rfl
  | loc hl => simp at hl
  | taskRef _ _ _ => rfl
  | syncRef _ => rfl
  | tuple hts => simp only [exprLocs]; exact exprLocsList_empty_of_empty_store hts
  | blockEmpty => rfl
  | blockSingle he =>
    simp only [exprLocs, exprLocsList, exprLocs_empty_of_empty_store he, List.append_nil]
  | blockCons h1 h2 =>
    have ih1 := exprLocs_empty_of_empty_store h1
    have ih2 := exprLocs_empty_of_empty_store h2
    simp only [exprLocs, exprLocsList] at ih2 ⊢
    rw [ih1, ih2, List.append_nil]
  | lam _ _ _ hbody _ =>
    simp only [exprLocs]; exact exprLocs_empty_of_empty_store hbody
  | apply hfn hargs _ =>
    simp [exprLocs, exprLocs_empty_of_empty_store hfn, exprLocsList_empty_of_empty_store hargs]
  | applyDir _ hargs _ =>
    simp only [exprLocs]; exact exprLocsList_empty_of_empty_store hargs
  | bin _ h1 h2 =>
    simp [exprLocs, exprLocs_empty_of_empty_store h1, exprLocs_empty_of_empty_store h2]
  | un _ h1 =>
    simp only [exprLocs]; exact exprLocs_empty_of_empty_store h1
  | let_ h1 h2 =>
    simp [exprLocs, exprLocs_empty_of_empty_store h1, exprLocs_empty_of_empty_store h2]
  | if_ hc h1 h2 =>
    simp [exprLocs, exprLocs_empty_of_empty_store hc,
      exprLocs_empty_of_empty_store h1, exprLocs_empty_of_empty_store h2]
  | while_ hc hb =>
    simp [exprLocs, exprLocs_empty_of_empty_store hc, exprLocs_empty_of_empty_store hb]
  | match_ hs harms =>
    simp [exprLocs, exprLocs_empty_of_empty_store hs, exprLocsArms_empty_of_empty_store harms]
  | makeData _ hts =>
    simp only [exprLocs]; exact exprLocsList_empty_of_empty_store hts
  | getTag h1 =>
    simp only [exprLocs]; exact exprLocs_empty_of_empty_store h1
  | cellNew h1 =>
    simp only [exprLocs]; exact exprLocs_empty_of_empty_store h1
  | cellGet h1 _ =>
    simp only [exprLocs]; exact exprLocs_empty_of_empty_store h1
  | cellSet h1 h2 =>
    simp [exprLocs, exprLocs_empty_of_empty_store h1, exprLocs_empty_of_empty_store h2]
  | spawn h1 _ _ =>
    simp only [exprLocs]; exact exprLocs_empty_of_empty_store h1
  | await h1 _ _ =>
    simp only [exprLocs]; exact exprLocs_empty_of_empty_store h1
  | concPrim _ hargs _ =>
    simp only [exprLocs]; exact exprLocsList_empty_of_empty_store hargs
  | trap _ _ => rfl
termination_by sizeOf e

theorem exprLocsList_empty_of_empty_store {Δ : AdtEnv} {Φ : FunEnv} {Θ : TaskTy} {Γ : Ctx}
    {es : List Expr} {τs : List Ty} (h : HasTypes Δ Φ [] Θ Γ es τs) : exprLocsList es = [] := by
  cases h with
  | nil => rfl
  | cons h1 hrest =>
    simp [exprLocsList, exprLocs_empty_of_empty_store h1, exprLocsList_empty_of_empty_store hrest]
termination_by sizeOf es

theorem exprLocsArms_empty_of_empty_store {Δ : AdtEnv} {Φ : FunEnv} {Θ : TaskTy} {Γ : Ctx}
    {τs τr : Ty} {arms : List (Pat × Expr)}
    (h : ArmsHaveType Δ Φ [] Θ Γ τs arms τr) : exprLocsArms arms = [] := by
  cases h with
  | nil => rfl
  | cons _ hb hrest =>
    simp [exprLocsArms, exprLocs_empty_of_empty_store hb, exprLocsArms_empty_of_empty_store hrest]
termination_by sizeOf arms
end

/-! ## Zero-Location Lemma for Closed `IsSend` Values -/

/- Key concurrency soundness lemma: any closed well-typed value `v` whose type
   satisfies `IsSend Δ τ` embeds ZERO mutable `Cell` heap locations (`exprLocs v = []`). -/
mutual
theorem exprLocs_empty_of_isValue_isSend {Δ : AdtEnv} {Φ : FunEnv} {Ψ : StoreTy} {Θ : TaskTy}
    {v : Expr} {τ : Ty}
    (ht : HasType Δ Φ Ψ Θ emptyCtx v τ) (hv : IsValue v) (hsend : IsSend Δ τ) :
    exprLocs v = [] := by
  cases ht with
  | lit _ => rfl
  | var hx _ => simp [emptyCtx] at hx
  | loc _ => exact absurd hsend isSend_cell_false
  | taskRef _ _ _ => rfl
  | syncRef _ => rfl
  | tuple hts =>
    cases hv with
    | tuple hvs =>
      simp only [exprLocs]
      exact exprLocsList_empty_of_isValue_isSend hts hvs (isSend_tuple_all hsend)
  | lam hm _ _ _ hsh =>
    have hm_sh := isSend_fn_mode hsend
    subst hm_sh
    cases hm with
    | refl =>
      simp only [exprLocs]
      exact (hsh rfl).2
  | makeData hlv hts =>
    cases hv with
    | makeData _ _ hvs =>
      simp only [exprLocs]
      exact exprLocsList_empty_of_isValue_isSend hts hvs (isSend_adt_fields hsend hlv)
  | blockEmpty => cases hv
  | blockSingle _ => cases hv
  | blockCons _ _ => cases hv
  | apply _ _ _ => cases hv
  | applyDir _ _ _ => cases hv
  | bin _ _ _ => cases hv
  | un _ _ => cases hv
  | let_ _ _ => cases hv
  | if_ _ _ _ => cases hv
  | while_ _ _ => cases hv
  | match_ _ _ => cases hv
  | getTag _ => cases hv
  | cellNew _ => cases hv
  | cellGet _ _ => cases hv
  | cellSet _ _ => cases hv
  | spawn _ _ _ => cases hv
  | await _ _ _ => cases hv
  | concPrim _ _ _ => cases hv
  | trap _ _ => cases hv
termination_by sizeOf v

theorem exprLocsList_empty_of_isValue_isSend {Δ : AdtEnv} {Φ : FunEnv} {Ψ : StoreTy} {Θ : TaskTy}
    {vs : List Expr} {τs : List Ty}
    (hts : HasTypes Δ Φ Ψ Θ emptyCtx vs τs)
    (hvs : ∀ v ∈ vs, IsValue v)
    (hsend : AllIsSend Δ τs) :
    exprLocsList vs = [] := by
  cases hts with
  | nil => rfl
  | cons h1 hrest =>
    cases hsend with
    | cons hs1 hsrest =>
      have hv1 : IsValue _ := hvs _ (List.mem_cons_self ..)
      have hvrest : ∀ u ∈ _, IsValue u := fun u hu => hvs u (List.mem_cons_of_mem _ hu)
      simp [exprLocsList,
        exprLocs_empty_of_isValue_isSend h1 hv1 hs1,
        exprLocsList_empty_of_isValue_isSend hrest hvrest hsrest]
termination_by sizeOf vs
end

/-! ## Free-Variable & Location Substitution Lemmas -/

private theorem lookup_extendMany_or {Γ : Ctx} {bs : List (Ident × Ty)} {z : Ident} {τ : Ty}
    (h : extendMany Γ bs z = some τ) : z ∈ bs.map Prod.fst ∨ Γ z = some τ := by
  induction bs with
  | nil => exact Or.inr h
  | cons b rest ih =>
    cases b with
    | mk k tk =>
      simp only [extendMany, extendCtx] at h
      by_cases hzk : (z == k) = true
      · rw [hzk] at h
        have heq : z = k := beq_iff_eq.mp hzk
        subst heq
        exact Or.inl (List.mem_cons_self ..)
      · have hzk' : (z == k) = false := Bool.eq_false_iff.mpr hzk
        rw [hzk'] at h
        simp only [Bool.false_eq_true, ↓reduceIte] at h
        rcases ih h with hm | hg
        · exact Or.inl (List.mem_cons_of_mem _ hm)
        · exact Or.inr hg

mutual
theorem freeVars_typed {Δ : AdtEnv} {Φ : FunEnv} {Ψ : StoreTy} {Θ : TaskTy} {Γ : Ctx}
    {e : Expr} {τ : Ty} (ht : HasType Δ Φ Ψ Θ Γ e τ) :
    ∀ z ∈ freeVars e, ∃ τz, Γ z = some τz := by
  cases ht with
  | lit _ => intro _ h; cases h
  | var hx _ =>
    intro z hz
    simp only [freeVars, List.mem_singleton] at hz
    subst hz; exact ⟨_, hx⟩
  | loc _ => intro _ h; cases h
  | taskRef _ _ _ => intro _ h; cases h
  | syncRef _ => intro _ h; cases h
  | tuple hts => simp only [freeVars]; exact freeVarsList_typed hts
  | blockEmpty => intro _ h; cases h
  | blockSingle he =>
    intro z hz
    simp only [freeVars, freeVarsList, List.append_nil] at hz
    exact freeVars_typed he z hz
  | @blockCons _ e1 e2 es _ _ h1 h2 =>
    intro z hz
    simp only [freeVars, freeVarsList, List.mem_append] at hz
    rcases hz with hz1 | hz2
    · exact freeVars_typed h1 z hz1
    · have hz2' : z ∈ freeVars (.block (e2 :: es)) := by
        simp [freeVars, freeVarsList, hz2]
      exact freeVars_typed h2 z hz2'
  | @lam _ _ _ ps _ _ _ body _ _ _ hbody _ =>
    intro z hz
    simp only [freeVars, List.mem_filter] at hz
    rcases freeVars_typed hbody z hz.1 with ⟨τz, hlookup⟩
    rcases lookup_extendMany_or hlookup with hmem | hg
    · exfalso
      rcases List.mem_map.mp hmem with ⟨p, hp, rfl⟩
      have hany : ps.any (fun q => q.1 == p.1) = true :=
        List.any_eq_true.mpr ⟨p, hp, beq_self_eq_true _⟩
      simp [hany] at hz
    · exact ⟨τz, hg⟩
  | apply hfn hargs _ =>
    intro z hz
    simp only [freeVars, List.mem_append] at hz
    rcases hz with h1 | h2
    · exact freeVars_typed hfn z h1
    · exact freeVarsList_typed hargs z h2
  | applyDir _ hargs _ => simp only [freeVars]; exact freeVarsList_typed hargs
  | bin _ h1 h2 =>
    intro z hz
    simp only [freeVars, List.mem_append] at hz
    rcases hz with hz1 | hz2
    · exact freeVars_typed h1 z hz1
    · exact freeVars_typed h2 z hz2
  | un _ h1 => simp only [freeVars]; exact freeVars_typed h1
  | @let_ _ y e1 e2 _ _ h1 h2 =>
    intro z hz
    simp only [freeVars, List.mem_append, List.mem_filter] at hz
    rcases hz with hz1 | ⟨hz2, hne⟩
    · exact freeVars_typed h1 z hz1
    · rcases freeVars_typed h2 z hz2 with ⟨τz, hlookup⟩
      simp only [extendCtx] at hlookup
      have hzy : (z == y) = false := by
        cases hq : z == y
        · rfl
        · simp [bne, hq] at hne
      rw [hzy] at hlookup
      simp only [Bool.false_eq_true, ↓reduceIte] at hlookup
      exact ⟨τz, hlookup⟩
  | if_ hc h1 h2 =>
    intro z hz
    simp only [freeVars, List.mem_append] at hz
    rcases hz with (hzc | hz1) | hz2
    · exact freeVars_typed hc z hzc
    · exact freeVars_typed h1 z hz1
    · exact freeVars_typed h2 z hz2
  | while_ hc hb =>
    intro z hz
    simp only [freeVars, List.mem_append] at hz
    rcases hz with hzc | hzb
    · exact freeVars_typed hc z hzc
    · exact freeVars_typed hb z hzb
  | match_ hs harms =>
    intro z hz
    simp only [freeVars, List.mem_append] at hz
    rcases hz with hzs | hza
    · exact freeVars_typed hs z hzs
    · exact freeVarsArms_typed harms z hza
  | makeData _ hts => simp only [freeVars]; exact freeVarsList_typed hts
  | getTag h1 => simp only [freeVars]; exact freeVars_typed h1
  | cellNew h1 => simp only [freeVars]; exact freeVars_typed h1
  | cellGet h1 _ => simp only [freeVars]; exact freeVars_typed h1
  | cellSet h1 h2 =>
    intro z hz
    simp only [freeVars, List.mem_append] at hz
    rcases hz with hz1 | hz2
    · exact freeVars_typed h1 z hz1
    · exact freeVars_typed h2 z hz2
  | spawn h1 _ _ => simp only [freeVars]; exact freeVars_typed h1
  | await h1 _ _ => simp only [freeVars]; exact freeVars_typed h1
  | concPrim _ hargs _ => simp only [freeVars]; exact freeVarsList_typed hargs
  | trap _ _ => intro _ h; cases h
termination_by sizeOf e

theorem freeVarsList_typed {Δ : AdtEnv} {Φ : FunEnv} {Ψ : StoreTy} {Θ : TaskTy} {Γ : Ctx}
    {es : List Expr} {τs : List Ty} (hts : HasTypes Δ Φ Ψ Θ Γ es τs) :
    ∀ z ∈ freeVarsList es, ∃ τz, Γ z = some τz := by
  cases hts with
  | nil => intro _ h; cases h
  | cons h1 hrest =>
    intro z hz
    simp only [freeVarsList, List.mem_append] at hz
    rcases hz with hz1 | hzr
    · exact freeVars_typed h1 z hz1
    · exact freeVarsList_typed hrest z hzr
termination_by sizeOf es

theorem freeVarsArms_typed {Δ : AdtEnv} {Φ : FunEnv} {Ψ : StoreTy} {Θ : TaskTy} {Γ : Ctx}
    {τs τr : Ty} {arms : List (Pat × Expr)} (harms : ArmsHaveType Δ Φ Ψ Θ Γ τs arms τr) :
    ∀ z ∈ freeVarsArms arms, ∃ τz, Γ z = some τz := by
  cases harms with
  | nil => intro _ h; cases h
  | @cons _ _ _ p body bs rest hp hbody hrest =>
    intro z hz
    simp only [freeVarsArms, List.mem_append, List.mem_filter, Bool.not_eq_true',
      List.contains_eq_mem, decide_eq_false_iff_not] at hz
    rcases hz with ⟨hzb, hnotc⟩ | hzr
    · rcases freeVars_typed hbody z hzb with ⟨τz, hlookup⟩
      rcases lookup_extendMany_or hlookup with hmem | hg
      · rw [patHasType_boundNames hp] at hmem
        exact absurd hmem hnotc
      · exact ⟨τz, hg⟩
    · exact freeVarsArms_typed hrest z hzr
termination_by sizeOf arms
end

theorem freeVars_empty_of_closed {Δ : AdtEnv} {Φ : FunEnv} {Ψ : StoreTy} {Θ : TaskTy}
    {v : Expr} {τ : Ty} (hv : HasType Δ Φ Ψ Θ emptyCtx v τ) :
    ∀ z, z ∉ freeVars v := by
  intro z hz
  rcases freeVars_typed hv z hz with ⟨_, h⟩
  simp [emptyCtx] at h

mutual
theorem subst_not_mem_freeVars {x : Ident} {v : Expr} :
    (e : Expr) → x ∉ freeVars e → subst x v e = e
  | .lit _, _ => rfl
  | .var y, hnot => by
    simp only [freeVars, List.mem_singleton] at hnot
    have hyx : (y == x) = false := beq_false_of_ne (Ne.symm hnot)
    simp [subst, hyx]
  | .loc _, _ => rfl
  | .taskRef _, _ => rfl
  | .syncRef _ _, _ => rfl
  | .tuple es, hnot => by
    simp only [subst, substList_not_mem_freeVars es hnot]
  | .block es, hnot => by
    simp only [subst, substList_not_mem_freeVars es hnot]
  | .lam m ps ret body, hnot => by
    simp only [subst]
    by_cases hany : ps.any (fun p => p.1 == x) = true
    · simp [hany]
    · simp only [hany, Bool.false_eq_true, ↓reduceIte]
      have hnotb : x ∉ freeVars body := by
        intro hmem
        apply hnot
        simp [freeVars, hmem, hany]
      rw [subst_not_mem_freeVars body hnotb]
  | .apply fn args, hnot => by
    simp only [freeVars, List.mem_append, not_or] at hnot
    simp [subst, subst_not_mem_freeVars fn hnot.1, substList_not_mem_freeVars args hnot.2]
  | .applyDir fn args, hnot => by
    simp [subst, substList_not_mem_freeVars args hnot]
  | .bin op e1 e2, hnot => by
    simp only [freeVars, List.mem_append, not_or] at hnot
    simp [subst, subst_not_mem_freeVars e1 hnot.1, subst_not_mem_freeVars e2 hnot.2]
  | .un op e1, hnot => by
    simp [subst, subst_not_mem_freeVars e1 hnot]
  | .let_ y e1 e2, hnot => by
    simp only [freeVars, List.mem_append, List.mem_filter, not_or] at hnot
    simp only [subst, subst_not_mem_freeVars e1 hnot.1]
    by_cases hyx : (y == x) = true
    · simp [hyx]
    · simp only [hyx, Bool.false_eq_true, ↓reduceIte]
      have hnot2 : x ∉ freeVars e2 := by
        intro hm2
        apply hnot.2
        have hxy : (x != y) = true := by
          have hne : x ≠ y := fun h => hyx (beq_iff_eq.mpr h.symm)
          exact bne_iff_ne.mpr hne
        exact ⟨hm2, hxy⟩
      rw [subst_not_mem_freeVars e2 hnot2]
  | .if_ c t e2, hnot => by
    simp only [freeVars, List.mem_append, not_or] at hnot
    simp [subst, subst_not_mem_freeVars c hnot.1.1,
      subst_not_mem_freeVars t hnot.1.2, subst_not_mem_freeVars e2 hnot.2]
  | .while_ c b, hnot => by
    simp only [freeVars, List.mem_append, not_or] at hnot
    simp [subst, subst_not_mem_freeVars c hnot.1, subst_not_mem_freeVars b hnot.2]
  | .match_ s arms, hnot => by
    simp only [freeVars, List.mem_append, not_or] at hnot
    simp [subst, subst_not_mem_freeVars s hnot.1, substArms_not_mem_freeVars arms hnot.2]
  | .makeData adt tag es, hnot => by
    simp [subst, substList_not_mem_freeVars es hnot]
  | .getTag e1, hnot => by
    simp [subst, subst_not_mem_freeVars e1 hnot]
  | .cellNew e1, hnot => by
    simp [subst, subst_not_mem_freeVars e1 hnot]
  | .cellGet e1, hnot => by
    simp [subst, subst_not_mem_freeVars e1 hnot]
  | .cellSet e1 e2, hnot => by
    simp only [freeVars, List.mem_append, not_or] at hnot
    simp [subst, subst_not_mem_freeVars e1 hnot.1, subst_not_mem_freeVars e2 hnot.2]
  | .spawn e1, hnot => by
    simp [subst, subst_not_mem_freeVars e1 hnot]
  | .await e1, hnot => by
    simp [subst, subst_not_mem_freeVars e1 hnot]
  | .concPrim _ args, hnot => by
    simp [subst, substList_not_mem_freeVars args hnot]
  | .trap _, _ => rfl

theorem substList_not_mem_freeVars {x : Ident} {v : Expr} :
    (es : List Expr) → x ∉ freeVarsList es → substList x v es = es
  | [], _ => rfl
  | e :: es, hnot => by
    simp only [freeVarsList, List.mem_append, not_or] at hnot
    simp [substList, subst_not_mem_freeVars e hnot.1, substList_not_mem_freeVars es hnot.2]

theorem substArms_not_mem_freeVars {x : Ident} {v : Expr} :
    (arms : List (Pat × Expr)) → x ∉ freeVarsArms arms → substArms x v arms = arms
  | [], _ => rfl
  | (p, body) :: rest, hnot => by
    simp only [freeVarsArms, List.mem_append, List.mem_filter, Bool.not_eq_true',
      List.contains_eq_mem, decide_eq_false_iff_not, not_or] at hnot
    simp only [substArms, substArms_not_mem_freeVars rest hnot.2]
    by_cases hc : (patBoundNames p).contains x = true
    · rw [hc]; simp
    · have hc' : (patBoundNames p).contains x = false := Bool.eq_false_iff.mpr hc
      rw [hc']
      simp only [Bool.false_eq_true, ↓reduceIte]
      have hnotm : x ∉ patBoundNames p := fun hm => hc (List.contains_iff_mem.mpr hm)
      have hnotb : x ∉ freeVars body := fun hb => hnot.1 ⟨hb, hnotm⟩
      rw [subst_not_mem_freeVars body hnotb]
end

mutual
theorem mem_freeVars_subst {x z : Ident} {v : Expr} (hclosed : ∀ w, w ∉ freeVars v) :
    (e : Expr) → z ∈ freeVars (subst x v e) → z ≠ x ∧ z ∈ freeVars e
  | .lit _, h => by cases h
  | .var y, h => by
    simp only [subst] at h
    by_cases hyx : (y == x) = true
    · rw [hyx] at h
      simp only [↓reduceIte] at h
      exact absurd h (hclosed z)
    · have hyx' : (y == x) = false := Bool.eq_false_iff.mpr hyx
      rw [hyx'] at h
      simp only [Bool.false_eq_true, ↓reduceIte, freeVars, List.mem_singleton] at h
      subst h
      exact ⟨fun h => hyx (beq_iff_eq.mpr h), List.mem_singleton.mpr rfl⟩
  | .loc _, h => by cases h
  | .taskRef _, h => by cases h
  | .syncRef _ _, h => by cases h
  | .tuple es, h => mem_freeVarsList_subst hclosed es h
  | .block es, h => mem_freeVarsList_subst hclosed es h
  | .lam m ps ret body, h => by
    simp only [subst] at h
    by_cases hany : ps.any (fun p => p.1 == x) = true
    · rw [hany] at h
      simp only [↓reduceIte, freeVars, List.mem_filter] at h
      have hzx : z ≠ x := by
        intro rfl
        simp [hany] at h
      exact ⟨hzx, List.mem_filter.mpr h⟩
    · have hany' : ps.any (fun p => p.1 == x) = false := Bool.eq_false_iff.mpr hany
      rw [hany'] at h
      simp only [Bool.false_eq_true, ↓reduceIte, freeVars, List.mem_filter] at h
      rcases mem_freeVars_subst hclosed body h.1 with ⟨hzx, hzb⟩
      exact ⟨hzx, List.mem_filter.mpr ⟨hzb, h.2⟩⟩
  | .apply fn args, h => by
    simp only [subst, freeVars, List.mem_append] at h ⊢
    rcases h with h1 | h2
    · rcases mem_freeVars_subst hclosed fn h1 with ⟨hne, hm⟩; exact ⟨hne, Or.inl hm⟩
    · rcases mem_freeVarsList_subst hclosed args h2 with ⟨hne, hm⟩; exact ⟨hne, Or.inr hm⟩
  | .applyDir fn args, h => mem_freeVarsList_subst hclosed args h
  | .bin op e1 e2, h => by
    simp only [subst, freeVars, List.mem_append] at h ⊢
    rcases h with h1 | h2
    · rcases mem_freeVars_subst hclosed e1 h1 with ⟨hne, hm⟩; exact ⟨hne, Or.inl hm⟩
    · rcases mem_freeVars_subst hclosed e2 h2 with ⟨hne, hm⟩; exact ⟨hne, Or.inr hm⟩
  | .un op e1, h => mem_freeVars_subst hclosed e1 h
  | .let_ y e1 e2, h => by
    simp only [subst] at h
    by_cases hyx : (y == x) = true
    · rw [hyx] at h
      simp only [↓reduceIte, freeVars, List.mem_append, List.mem_filter] at h ⊢
      rcases h with h1 | ⟨h2, hne_zy⟩
      · rcases mem_freeVars_subst hclosed e1 h1 with ⟨hne, hm⟩
        exact ⟨hne, Or.inl hm⟩
      · have hy_eq_x : y = x := beq_iff_eq.mp hyx
        subst hy_eq_x
        have hzx : z ≠ y := bne_iff_ne.mp hne_zy
        exact ⟨hzx, Or.inr ⟨h2, hne_zy⟩⟩
    · have hyx' : (y == x) = false := Bool.eq_false_iff.mpr hyx
      rw [hyx'] at h
      simp only [Bool.false_eq_true, ↓reduceIte, freeVars, List.mem_append, List.mem_filter] at h ⊢
      rcases h with h1 | ⟨h2, hne_zy⟩
      · rcases mem_freeVars_subst hclosed e1 h1 with ⟨hne, hm⟩
        exact ⟨hne, Or.inl hm⟩
      · rcases mem_freeVars_subst hclosed e2 h2 with ⟨hne, hm⟩
        exact ⟨hne, Or.inr ⟨hm, hne_zy⟩⟩
  | .if_ c t e2, h => by
    simp only [subst, freeVars, List.mem_append] at h ⊢
    rcases h with (hc | ht) | he2
    · rcases mem_freeVars_subst hclosed c hc with ⟨hne, hm⟩; exact ⟨hne, Or.inl (Or.inl hm)⟩
    · rcases mem_freeVars_subst hclosed t ht with ⟨hne, hm⟩; exact ⟨hne, Or.inl (Or.inr hm)⟩
    · rcases mem_freeVars_subst hclosed e2 he2 with ⟨hne, hm⟩; exact ⟨hne, Or.inr hm⟩
  | .while_ c b, h => by
    simp only [subst, freeVars, List.mem_append] at h ⊢
    rcases h with hc | hb
    · rcases mem_freeVars_subst hclosed c hc with ⟨hne, hm⟩; exact ⟨hne, Or.inl hm⟩
    · rcases mem_freeVars_subst hclosed b hb with ⟨hne, hm⟩; exact ⟨hne, Or.inr hm⟩
  | .match_ s arms, h => by
    simp only [subst, freeVars, List.mem_append] at h ⊢
    rcases h with hs | ha
    · rcases mem_freeVars_subst hclosed s hs with ⟨hne, hm⟩; exact ⟨hne, Or.inl hm⟩
    · rcases mem_freeVarsArms_subst hclosed arms ha with ⟨hne, hm⟩; exact ⟨hne, Or.inr hm⟩
  | .makeData adt tag es, h => mem_freeVarsList_subst hclosed es h
  | .getTag e1, h => mem_freeVars_subst hclosed e1 h
  | .cellNew e1, h => mem_freeVars_subst hclosed e1 h
  | .cellGet e1, h => mem_freeVars_subst hclosed e1 h
  | .cellSet e1 e2, h => by
    simp only [subst, freeVars, List.mem_append] at h ⊢
    rcases h with h1 | h2
    · rcases mem_freeVars_subst hclosed e1 h1 with ⟨hne, hm⟩; exact ⟨hne, Or.inl hm⟩
    · rcases mem_freeVars_subst hclosed e2 h2 with ⟨hne, hm⟩; exact ⟨hne, Or.inr hm⟩
  | .spawn e1, h => mem_freeVars_subst hclosed e1 h
  | .await e1, h => mem_freeVars_subst hclosed e1 h
  | .concPrim _ args, h => mem_freeVarsList_subst hclosed args h
  | .trap _, h => by cases h

theorem mem_freeVarsList_subst {x z : Ident} {v : Expr} (hclosed : ∀ w, w ∉ freeVars v) :
    (es : List Expr) → z ∈ freeVarsList (substList x v es) → z ≠ x ∧ z ∈ freeVarsList es
  | [], h => by cases h
  | e :: es, h => by
    simp only [substList, freeVarsList, List.mem_append] at h ⊢
    rcases h with h1 | h2
    · rcases mem_freeVars_subst hclosed e h1 with ⟨hne, hm⟩; exact ⟨hne, Or.inl hm⟩
    · rcases mem_freeVarsList_subst hclosed es h2 with ⟨hne, hm⟩; exact ⟨hne, Or.inr hm⟩

theorem mem_freeVarsArms_subst {x z : Ident} {v : Expr} (hclosed : ∀ w, w ∉ freeVars v) :
    (arms : List (Pat × Expr)) → z ∈ freeVarsArms (substArms x v arms) → z ≠ x ∧ z ∈ freeVarsArms arms
  | [], h => by cases h
  | (p, body) :: rest, h => by
    simp only [substArms, freeVarsArms, List.mem_append, List.mem_filter, Bool.not_eq_true',
      List.contains_eq_mem, decide_eq_false_iff_not] at h ⊢
    rcases h with ⟨hb, hnotp⟩ | hr
    · by_cases hxm : x ∈ patBoundNames p
      · simp only [hxm, decide_true, ↓reduceIte] at hb
        have hzx : z ≠ x := by
          intro rfl
          exact hnotp hxm
        exact ⟨hzx, Or.inl ⟨hb, hnotp⟩⟩
      · simp only [hxm, decide_false, Bool.false_eq_true, ↓reduceIte] at hb
        rcases mem_freeVars_subst hclosed body hb with ⟨hne, hm⟩
        exact ⟨hne, Or.inl ⟨hm, hnotp⟩⟩
    · rcases mem_freeVarsArms_subst hclosed rest hr with ⟨hne, hm⟩
      exact ⟨hne, Or.inr hm⟩
end

mutual
theorem mem_exprLocs_subst {x : Ident} {v : Expr} {l : Loc} :
    (e : Expr) → l ∈ exprLocs (subst x v e) → l ∈ exprLocs e ∨ l ∈ exprLocs v
  | .lit _, h => by cases h
  | .var y, h => by
    simp only [subst] at h
    split at h
    · exact Or.inr h
    · cases h
  | .loc _, h => Or.inl h
  | .taskRef _, h => by cases h
  | .syncRef _ _, h => by cases h
  | .tuple es, h => mem_exprLocsList_subst es h
  | .block es, h => mem_exprLocsList_subst es h
  | .lam m ps ret body, h => by
    simp only [subst] at h
    split at h
    · exact Or.inl h
    · exact mem_exprLocs_subst body h
  | .apply fn args, h => by
    simp only [subst, exprLocs, List.mem_append] at h ⊢
    rcases h with h1 | h2
    · exact (mem_exprLocs_subst fn h1).imp Or.inl id
    · exact (mem_exprLocsList_subst args h2).imp Or.inr id
  | .applyDir _ args, h => mem_exprLocsList_subst args h
  | .bin _ e1 e2, h => by
    simp only [subst, exprLocs, List.mem_append] at h ⊢
    rcases h with h1 | h2
    · exact (mem_exprLocs_subst e1 h1).imp Or.inl id
    · exact (mem_exprLocs_subst e2 h2).imp Or.inr id
  | .un _ e1, h => mem_exprLocs_subst e1 h
  | .let_ y e1 e2, h => by
    simp only [subst] at h
    split at h
    · simp only [exprLocs, List.mem_append] at h ⊢
      rcases h with h1 | h2
      · exact (mem_exprLocs_subst e1 h1).imp Or.inl id
      · exact Or.inl (Or.inr h2)
    · simp only [exprLocs, List.mem_append] at h ⊢
      rcases h with h1 | h2
      · exact (mem_exprLocs_subst e1 h1).imp Or.inl id
      · exact (mem_exprLocs_subst e2 h2).imp Or.inr id
  | .if_ c t e2, h => by
    simp only [subst, exprLocs, List.mem_append] at h ⊢
    rcases h with (hc | ht) | he2
    · exact (mem_exprLocs_subst c hc).imp (fun m => Or.inl (Or.inl m)) id
    · exact (mem_exprLocs_subst t ht).imp (fun m => Or.inl (Or.inr m)) id
    · exact (mem_exprLocs_subst e2 he2).imp Or.inr id
  | .while_ c b, h => by
    simp only [subst, exprLocs, List.mem_append] at h ⊢
    rcases h with hc | hb
    · exact (mem_exprLocs_subst c hc).imp Or.inl id
    · exact (mem_exprLocs_subst b hb).imp Or.inr id
  | .match_ s arms, h => by
    simp only [subst, exprLocs, List.mem_append] at h ⊢
    rcases h with hs | ha
    · exact (mem_exprLocs_subst s hs).imp Or.inl id
    · exact (mem_exprLocsArms_subst arms ha).imp Or.inr id
  | .makeData _ _ es, h => mem_exprLocsList_subst es h
  | .getTag e1, h => mem_exprLocs_subst e1 h
  | .cellNew e1, h => mem_exprLocs_subst e1 h
  | .cellGet e1, h => mem_exprLocs_subst e1 h
  | .cellSet e1 e2, h => by
    simp only [subst, exprLocs, List.mem_append] at h ⊢
    rcases h with h1 | h2
    · exact (mem_exprLocs_subst e1 h1).imp Or.inl id
    · exact (mem_exprLocs_subst e2 h2).imp Or.inr id
  | .spawn e1, h => mem_exprLocs_subst e1 h
  | .await e1, h => mem_exprLocs_subst e1 h
  | .concPrim _ args, h => mem_exprLocsList_subst args h
  | .trap _, h => by cases h

theorem mem_exprLocsList_subst {x : Ident} {v : Expr} {l : Loc} :
    (es : List Expr) → l ∈ exprLocsList (substList x v es) → l ∈ exprLocsList es ∨ l ∈ exprLocs v
  | [], h => by cases h
  | e :: es, h => by
    simp only [substList, exprLocsList, List.mem_append] at h ⊢
    rcases h with h1 | h2
    · exact (mem_exprLocs_subst e h1).imp Or.inl id
    · exact (mem_exprLocsList_subst es h2).imp Or.inr id

theorem mem_exprLocsArms_subst {x : Ident} {v : Expr} {l : Loc} :
    (arms : List (Pat × Expr)) → l ∈ exprLocsArms (substArms x v arms) →
      l ∈ exprLocsArms arms ∨ l ∈ exprLocs v
  | [], h => by cases h
  | (p, body) :: rest, h => by
    simp only [substArms, exprLocsArms, List.mem_append] at h ⊢
    rcases h with hb | hr
    · split at hb
      · exact Or.inl (Or.inl hb)
      · exact (mem_exprLocs_subst body hb).imp Or.inl id
    · exact (mem_exprLocsArms_subst rest hr).imp Or.inr id
end

theorem exprLocs_subst_nil {x : Ident} {v e : Expr}
    (he : exprLocs e = []) (hv : exprLocs v = []) :
    exprLocs (subst x v e) = [] := by
  apply List.eq_nil_iff_forall_not_mem.mpr
  intro l hl
  rcases mem_exprLocs_subst e hl with h1 | h2
  · rw [he] at h1; cases h1
  · rw [hv] at h2; cases h2

/-! ## Context, Store & Task Weakening -/

private theorem extCtx_mono {Γ1 Γ2 : Ctx} (hsub : ∀ x t, Γ1 x = some t → Γ2 x = some t)
    (x : Ident) (τ : Ty) : ∀ y t, extendCtx Γ1 x τ y = some t → extendCtx Γ2 x τ y = some t := by
  intro y t hy
  simp only [extendCtx] at hy ⊢
  split at hy <;> simp_all

private theorem extMany_mono {Γ1 Γ2 : Ctx} (hsub : ∀ x t, Γ1 x = some t → Γ2 x = some t)
    (bs : List (Ident × Ty)) : ∀ y t, extendMany Γ1 bs y = some t → extendMany Γ2 bs y = some t := by
  induction bs with
  | nil => exact hsub
  | cons b rest ih =>
    cases b with
    | mk k tk => exact extCtx_mono ih k tk

mutual
theorem typing_ctx_weaken {Δ : AdtEnv} {Φ : FunEnv} {Ψ : StoreTy} {Θ : TaskTy}
    {Γ1 Γ2 : Ctx} {e : Expr} {τ : Ty}
    (hsub : ∀ x t, Γ1 x = some t → Γ2 x = some t)
    (h : HasType Δ Φ Ψ Θ Γ1 e τ) : HasType Δ Φ Ψ Θ Γ2 e τ := by
  cases h with
  | lit hl => exact .lit hl
  | var hx hs => exact .var (hsub _ _ hx) hs
  | loc hl => exact .loc hl
  | taskRef htid hsend hs => exact .taskRef htid hsend hs
  | syncRef hsr => exact .syncRef hsr
  | tuple hts => exact .tuple (typingList_ctx_weaken hsub hts)
  | blockEmpty => exact .blockEmpty
  | blockSingle he => exact .blockSingle (typing_ctx_weaken hsub he)
  | blockCons h1 h2 => exact .blockCons (typing_ctx_weaken hsub h1) (typing_ctx_weaken hsub h2)
  | lam hm hps hr hbody hsh =>
    refine .lam hm hps hr (typing_ctx_weaken (extMany_mono hsub _) hbody) (fun hms => ?_)
    rcases hsh hms with ⟨hfv, hlocs⟩
    refine ⟨fun x hx => ?_, hlocs⟩
    rcases hfv x hx with ⟨τx, hgx, hsend⟩
    exact ⟨τx, hsub x τx hgx, hsend⟩
  | apply hfn hargs hr =>
    exact .apply (typing_ctx_weaken hsub hfn) (typingList_ctx_weaken hsub hargs) hr
  | applyDir hf hargs hr =>
    exact .applyDir hf (typingList_ctx_weaken hsub hargs) hr
  | bin hop h1 h2 => exact .bin hop (typing_ctx_weaken hsub h1) (typing_ctx_weaken hsub h2)
  | un hop h1 => exact .un hop (typing_ctx_weaken hsub h1)
  | let_ h1 h2 => exact .let_ (typing_ctx_weaken hsub h1) (typing_ctx_weaken (extCtx_mono hsub _ _) h2)
  | if_ hc h1 h2 =>
    exact .if_ (typing_ctx_weaken hsub hc) (typing_ctx_weaken hsub h1) (typing_ctx_weaken hsub h2)
  | while_ hc hb => exact .while_ (typing_ctx_weaken hsub hc) (typing_ctx_weaken hsub hb)
  | match_ hs harms => exact .match_ (typing_ctx_weaken hsub hs) (typingArms_ctx_weaken hsub harms)
  | makeData hv hts => exact .makeData hv (typingList_ctx_weaken hsub hts)
  | getTag he => exact .getTag (typing_ctx_weaken hsub he)
  | cellNew he => exact .cellNew (typing_ctx_weaken hsub he)
  | cellGet he hs => exact .cellGet (typing_ctx_weaken hsub he) hs
  | cellSet h1 h2 => exact .cellSet (typing_ctx_weaken hsub h1) (typing_ctx_weaken hsub h2)
  | spawn h1 hsend hs => exact .spawn (typing_ctx_weaken hsub h1) hsend hs
  | await h1 hsend hs => exact .await (typing_ctx_weaken hsub h1) hsend hs
  | concPrim hop hargs hr => exact .concPrim hop (typingList_ctx_weaken hsub hargs) hr
  | trap t τ => exact .trap t τ
termination_by sizeOf e

theorem typingList_ctx_weaken {Δ : AdtEnv} {Φ : FunEnv} {Ψ : StoreTy} {Θ : TaskTy}
    {Γ1 Γ2 : Ctx} {es : List Expr} {τs : List Ty}
    (hsub : ∀ x t, Γ1 x = some t → Γ2 x = some t)
    (h : HasTypes Δ Φ Ψ Θ Γ1 es τs) : HasTypes Δ Φ Ψ Θ Γ2 es τs := by
  cases h with
  | nil => exact .nil
  | cons h1 hrest => exact .cons (typing_ctx_weaken hsub h1) (typingList_ctx_weaken hsub hrest)
termination_by sizeOf es

theorem typingArms_ctx_weaken {Δ : AdtEnv} {Φ : FunEnv} {Ψ : StoreTy} {Θ : TaskTy}
    {Γ1 Γ2 : Ctx} {τs τr : Ty} {arms : List (Pat × Expr)}
    (hsub : ∀ x t, Γ1 x = some t → Γ2 x = some t)
    (h : ArmsHaveType Δ Φ Ψ Θ Γ1 τs arms τr) : ArmsHaveType Δ Φ Ψ Θ Γ2 τs arms τr := by
  cases h with
  | nil => exact .nil
  | cons hp hb hrest =>
    exact .cons hp (typing_ctx_weaken (extMany_mono hsub _) hb) (typingArms_ctx_weaken hsub hrest)
termination_by sizeOf arms
end

theorem typing_closed_weaken {Δ : AdtEnv} {Φ : FunEnv} {Ψ : StoreTy} {Θ : TaskTy}
    {Γ : Ctx} {v : Expr} {τ : Ty}
    (h : HasType Δ Φ Ψ Θ emptyCtx v τ) : HasType Δ Φ Ψ Θ Γ v τ :=
  typing_ctx_weaken (fun _ _ hx => by simp [emptyCtx] at hx) h

mutual
theorem typing_env_weaken {Δ : AdtEnv} {Φ : FunEnv} {Ψ Ψ' : StoreTy} {Θ Θ' : TaskTy}
    {Γ : Ctx} {e : Expr} {τ : Ty}
    (hs : StoreExtends Ψ Ψ') (htk : TaskExtends Θ Θ')
    (h : HasType Δ Φ Ψ Θ Γ e τ) : HasType Δ Φ Ψ' Θ' Γ e τ := by
  cases h with
  | lit hl => exact .lit hl
  | var hx hsub => exact .var hx hsub
  | loc hl => exact .loc (hs.2 _ _ hl)
  | taskRef htid hsend hsub => exact .taskRef (htk.tasks.2 _ _ htid) hsend hsub
  | syncRef hsr =>
    cases hsr with
    | mvar hm hsend => exact .syncRef (.mvar (htk.mvars.2 _ _ hm) hsend)
    | chan hc hsend => exact .syncRef (.chan (htk.chans.2 _ _ hc) hsend)
    | actor ha => exact .syncRef (.actor (htk.actors.2 _ _ ha))
  | tuple hts => exact .tuple (typingList_env_weaken hs htk hts)
  | blockEmpty => exact .blockEmpty
  | blockSingle he => exact .blockSingle (typing_env_weaken hs htk he)
  | blockCons h1 h2 => exact .blockCons (typing_env_weaken hs htk h1) (typing_env_weaken hs htk h2)
  | lam hm hps hr hbody hsh => exact .lam hm hps hr (typing_env_weaken hs htk hbody) hsh
  | apply hfn hargs hr =>
    exact .apply (typing_env_weaken hs htk hfn) (typingList_env_weaken hs htk hargs) hr
  | applyDir hf hargs hr =>
    exact .applyDir hf (typingList_env_weaken hs htk hargs) hr
  | bin hop h1 h2 => exact .bin hop (typing_env_weaken hs htk h1) (typing_env_weaken hs htk h2)
  | un hop h1 => exact .un hop (typing_env_weaken hs htk h1)
  | let_ h1 h2 => exact .let_ (typing_env_weaken hs htk h1) (typing_env_weaken hs htk h2)
  | if_ hc h1 h2 =>
    exact .if_ (typing_env_weaken hs htk hc) (typing_env_weaken hs htk h1) (typing_env_weaken hs htk h2)
  | while_ hc hb => exact .while_ (typing_env_weaken hs htk hc) (typing_env_weaken hs htk hb)
  | match_ hscr harms => exact .match_ (typing_env_weaken hs htk hscr) (typingArms_env_weaken hs htk harms)
  | makeData hv hts => exact .makeData hv (typingList_env_weaken hs htk hts)
  | getTag he => exact .getTag (typing_env_weaken hs htk he)
  | cellNew he => exact .cellNew (typing_env_weaken hs htk he)
  | cellGet he hsub => exact .cellGet (typing_env_weaken hs htk he) hsub
  | cellSet h1 h2 => exact .cellSet (typing_env_weaken hs htk h1) (typing_env_weaken hs htk h2)
  | spawn h1 hsend hsub => exact .spawn (typing_env_weaken hs htk h1) hsend hsub
  | await h1 hsend hsub => exact .await (typing_env_weaken hs htk h1) hsend hsub
  | concPrim hop hargs hr => exact .concPrim hop (typingList_env_weaken hs htk hargs) hr
  | trap t τ => exact .trap t τ
termination_by sizeOf e

theorem typingList_env_weaken {Δ : AdtEnv} {Φ : FunEnv} {Ψ Ψ' : StoreTy} {Θ Θ' : TaskTy}
    {Γ : Ctx} {es : List Expr} {τs : List Ty}
    (hs : StoreExtends Ψ Ψ') (htk : TaskExtends Θ Θ')
    (h : HasTypes Δ Φ Ψ Θ Γ es τs) : HasTypes Δ Φ Ψ' Θ' Γ es τs := by
  cases h with
  | nil => exact .nil
  | cons h1 hrest => exact .cons (typing_env_weaken hs htk h1) (typingList_env_weaken hs htk hrest)
termination_by sizeOf es

theorem typingArms_env_weaken {Δ : AdtEnv} {Φ : FunEnv} {Ψ Ψ' : StoreTy} {Θ Θ' : TaskTy}
    {Γ : Ctx} {τs τr : Ty} {arms : List (Pat × Expr)}
    (hs : StoreExtends Ψ Ψ') (htk : TaskExtends Θ Θ')
    (h : ArmsHaveType Δ Φ Ψ Θ Γ τs arms τr) : ArmsHaveType Δ Φ Ψ' Θ' Γ τs arms τr := by
  cases h with
  | nil => exact .nil
  | cons hp hb hrest =>
    exact .cons hp (typing_env_weaken hs htk hb) (typingArms_env_weaken hs htk hrest)
termination_by sizeOf arms
end

/-! ## Substitution & Pattern-Matching Typing Lemmas -/

mutual
theorem subst_typing {Δ : AdtEnv} {Φ : FunEnv} {Ψ : StoreTy} {Θ : TaskTy} {Γ : Ctx}
    {x : Ident} {v e : Expr} {τx τ : Ty}
    (he : HasType Δ Φ Ψ Θ (extendCtx Γ x τx) e τ)
    (hvVal : IsValue v)
    (hv : HasType Δ Φ Ψ Θ emptyCtx v τx) :
    HasType Δ Φ Ψ Θ Γ (subst x v e) τ := by
  cases he with
  | lit hl => exact .lit hl
  | @var _ y _ _ hy hsub =>
    simp only [subst, extendCtx] at hy ⊢
    by_cases hyx : (y == x) = true
    · rw [hyx] at hy ⊢
      simp only [↓reduceIte, Option.some.injEq] at hy
      subst hy
      exact typing_sub hsub (typing_closed_weaken hv)
    · have hyx' : (y == x) = false := Bool.eq_false_iff.mpr hyx
      rw [hyx'] at hy ⊢
      simp only [Bool.false_eq_true, ↓reduceIte] at hy ⊢
      exact .var hy hsub
  | loc hl => exact .loc hl
  | taskRef htid hsend hsub => exact .taskRef htid hsend hsub
  | syncRef hsr => exact .syncRef hsr
  | tuple hts => exact .tuple (substList_typing hts hvVal hv)
  | blockEmpty => exact .blockEmpty
  | blockSingle h1 => exact .blockSingle (subst_typing h1 hvVal hv)
  | blockCons h1 h2 => exact .blockCons (subst_typing h1 hvVal hv) (subst_typing h2 hvVal hv)
  | @lam _ m0 m ps paramTys ret0 ret body hm hps hr hbody hsh =>
    simp only [subst]
    by_cases hany : ps.any (fun p => p.1 == x) = true
    · simp only [hany, ↓reduceIte]
      have hmem : x ∈ ps.map Prod.fst := by
        rw [List.any_eq_true] at hany
        rcases hany with ⟨⟨k, tk⟩, hmemk, heqk⟩
        simp only [beq_iff_eq] at heqk
        subst heqk
        exact List.mem_map.mpr ⟨(k, tk), hmemk, rfl⟩
      rw [extendMany_shadow Γ x τx ps hmem] at hbody
      refine .lam hm hps hr hbody (fun hms => ?_)
      rcases hsh hms with ⟨hfv, hlocs⟩
      refine ⟨fun z hz => ?_, hlocs⟩
      rcases hfv z hz with ⟨τz, hgz, hsend⟩
      have hzx : z ≠ x := by
        intro rfl
        simp only [freeVars, List.mem_filter] at hz
        simp [hany] at hz
      have hzx' : (z == x) = false := beq_false_of_ne hzx
      simp only [extendCtx, hzx', Bool.false_eq_true, ↓reduceIte] at hgz
      exact ⟨τz, hgz, hsend⟩
    · simp only [hany, Bool.false_eq_true, ↓reduceIte]
      have hnot : x ∉ ps.map Prod.fst := by
        intro hmem
        apply hany
        rw [List.any_eq_true]
        rcases List.mem_map.mp hmem with ⟨p, hp, rfl⟩
        exact ⟨p, hp, beq_self_eq_true _⟩
      have hany' : ps.any (fun p => p.1 == x) = false := Bool.eq_false_iff.mpr hany
      have hbody' := hbody
      rw [extendMany_comm Γ x τx ps hnot] at hbody'
      refine .lam hm hps hr (subst_typing hbody' hvVal hv) (fun hms => ?_)
      rcases hsh hms with ⟨hfv, hlocs⟩
      refine ⟨fun z hz => ?_, ?_⟩
      · have hsub_lam : subst x v (.lam .shared ps ret0 body) = .lam .shared ps ret0 (subst x v body) := by
          simp [subst, hany']
        have hz' : z ∈ freeVars (subst x v (.lam .shared ps ret0 body)) := by
          rw [hsub_lam]; exact hz
        rcases mem_freeVars_subst (freeVars_empty_of_closed hv) (.lam .shared ps ret0 body) hz' with ⟨hzx, hz0⟩
        rcases hfv z hz0 with ⟨τz, hgz, hsend⟩
        have hzx' : (z == x) = false := beq_false_of_ne hzx
        simp only [extendCtx, hzx', Bool.false_eq_true, ↓reduceIte] at hgz
        exact ⟨τz, hgz, hsend⟩
      · by_cases hxfree : x ∈ freeVars body
        · have hxlam : x ∈ freeVars (.lam .shared ps ret0 body) := by
            simp [freeVars, hxfree, hany']
          rcases hfv x hxlam with ⟨τx', hgx, hsendx⟩
          simp only [extendCtx, beq_self_eq_true, ↓reduceIte, Option.some.injEq] at hgx
          subst hgx
          have hvlocs : exprLocs v = [] := exprLocs_empty_of_isValue_isSend hv hvVal hsendx
          exact exprLocs_subst_nil hlocs hvlocs
        · rw [subst_not_mem_freeVars body hxfree]
          exact hlocs
  | apply hfn hargs hr =>
    exact .apply (subst_typing hfn hvVal hv) (substList_typing hargs hvVal hv) hr
  | applyDir hf hargs hr =>
    exact .applyDir hf (substList_typing hargs hvVal hv) hr
  | bin hop h1 h2 => exact .bin hop (subst_typing h1 hvVal hv) (subst_typing h2 hvVal hv)
  | un hop h1 => exact .un hop (subst_typing h1 hvVal hv)
  | @let_ _ y e1 e2 τ1 _ h1 h2 =>
    simp only [subst]
    by_cases hyx : (y == x) = true
    · simp only [hyx, ↓reduceIte]
      have heq : y = x := beq_iff_eq.mp hyx
      subst heq
      rw [extendCtx_shadow] at h2
      exact .let_ (subst_typing h1 hvVal hv) h2
    · simp only [hyx, Bool.false_eq_true, ↓reduceIte]
      have hne : x ≠ y := fun h => hyx (beq_iff_eq.mpr h.symm)
      rw [extendCtx_comm Γ hne τx τ1] at h2
      exact .let_ (subst_typing h1 hvVal hv) (subst_typing h2 hvVal hv)
  | if_ hc h1 h2 => exact .if_ (subst_typing hc hvVal hv) (subst_typing h1 hvVal hv) (subst_typing h2 hvVal hv)
  | while_ hc hb => exact .while_ (subst_typing hc hvVal hv) (subst_typing hb hvVal hv)
  | match_ hs harms => exact .match_ (subst_typing hs hvVal hv) (substArms_typing harms hvVal hv)
  | makeData hlv hts => exact .makeData hlv (substList_typing hts hvVal hv)
  | getTag h1 => exact .getTag (subst_typing h1 hvVal hv)
  | cellNew h1 => exact .cellNew (subst_typing h1 hvVal hv)
  | cellGet h1 hs => exact .cellGet (subst_typing h1 hvVal hv) hs
  | cellSet h1 h2 => exact .cellSet (subst_typing h1 hvVal hv) (subst_typing h2 hvVal hv)
  | spawn h1 hsend hs => exact .spawn (subst_typing h1 hvVal hv) hsend hs
  | await h1 hsend hs => exact .await (subst_typing h1 hvVal hv) hsend hs
  | concPrim hop hargs hr => exact .concPrim hop (substList_typing hargs hvVal hv) hr
  | trap t τ => exact .trap t τ
termination_by sizeOf e

theorem substList_typing {Δ : AdtEnv} {Φ : FunEnv} {Ψ : StoreTy} {Θ : TaskTy} {Γ : Ctx}
    {x : Ident} {v : Expr} {es : List Expr} {τx : Ty} {τs : List Ty}
    (hes : HasTypes Δ Φ Ψ Θ (extendCtx Γ x τx) es τs)
    (hvVal : IsValue v)
    (hv : HasType Δ Φ Ψ Θ emptyCtx v τx) :
    HasTypes Δ Φ Ψ Θ Γ (substList x v es) τs := by
  cases hes with
  | nil => exact .nil
  | cons h1 hrest => exact .cons (subst_typing h1 hvVal hv) (substList_typing hrest hvVal hv)
termination_by sizeOf es

theorem substArms_typing {Δ : AdtEnv} {Φ : FunEnv} {Ψ : StoreTy} {Θ : TaskTy} {Γ : Ctx}
    {x : Ident} {v : Expr} {τx τs τr : Ty} {arms : List (Pat × Expr)}
    (harms : ArmsHaveType Δ Φ Ψ Θ (extendCtx Γ x τx) τs arms τr)
    (hvVal : IsValue v)
    (hv : HasType Δ Φ Ψ Θ emptyCtx v τx) :
    ArmsHaveType Δ Φ Ψ Θ Γ τs (substArms x v arms) τr := by
  cases harms with
  | nil => exact .nil
  | @cons _ _ _ p body bs rest hp hbody hrest =>
    simp only [substArms]
    have hbn : bs.map Prod.fst = patBoundNames p := patHasType_boundNames hp
    by_cases hcont : (patBoundNames p).contains x = true
    · simp only [hcont, ↓reduceIte]
      have hmem : x ∈ bs.map Prod.fst := by
        rw [hbn]
        exact List.contains_iff_mem.mp hcont
      rw [extendMany_shadow Γ x τx bs hmem] at hbody
      exact .cons hp hbody (substArms_typing hrest hvVal hv)
    · simp only [hcont, Bool.false_eq_true, ↓reduceIte]
      have hnot : x ∉ bs.map Prod.fst := by
        rw [hbn]
        intro hm
        exact hcont (List.contains_iff_mem.mpr hm)
      rw [extendMany_comm Γ x τx bs hnot] at hbody
      exact .cons hp (subst_typing hbody hvVal hv) (substArms_typing hrest hvVal hv)
termination_by sizeOf arms
end

/-- Closed value bindings matching a typed binder list `bs`. -/
inductive ValuesMatchEnv (Δ : AdtEnv) (Φ : FunEnv) (Ψ : StoreTy) (Θ : TaskTy) :
    List (Ident × Expr) → List (Ident × Ty) → Prop where
  | nil : ValuesMatchEnv Δ Φ Ψ Θ [] []
  | cons {x : Ident} {v : Expr} {τ : Ty} {env : List (Ident × Expr)} {bs : List (Ident × Ty)} :
      IsValue v →
      HasType Δ Φ Ψ Θ emptyCtx v τ →
      ValuesMatchEnv Δ Φ Ψ Θ env bs →
      ValuesMatchEnv Δ Φ Ψ Θ ((x, v) :: env) ((x, τ) :: bs)

theorem ValuesMatchEnv.append {Δ : AdtEnv} {Φ : FunEnv} {Ψ : StoreTy} {Θ : TaskTy}
    {e1 e2 : List (Ident × Expr)} {b1 b2 : List (Ident × Ty)}
    (h1 : ValuesMatchEnv Δ Φ Ψ Θ e1 b1) (h2 : ValuesMatchEnv Δ Φ Ψ Θ e2 b2) :
    ValuesMatchEnv Δ Φ Ψ Θ (e1 ++ e2) (b1 ++ b2) := by
  induction h1 with
  | nil => exact h2
  | cons hv ht _ ih => exact .cons hv ht ih

theorem substMany_typing {Δ : AdtEnv} {Φ : FunEnv} {Ψ : StoreTy} {Θ : TaskTy} {Γ : Ctx}
    {env : List (Ident × Expr)} {bs : List (Ident × Ty)} {e : Expr} {τ : Ty}
    (hm : ValuesMatchEnv Δ Φ Ψ Θ env bs)
    (he : HasType Δ Φ Ψ Θ (extendMany Γ bs) e τ) :
    HasType Δ Φ Ψ Θ Γ (substMany env e) τ := by
  induction hm generalizing e with
  | nil => exact he
  | cons hvVal hv _ ih =>
    simp only [extendMany] at he
    simp only [substMany]
    exact ih (subst_typing he hvVal hv)

theorem zipParams_match {Δ : AdtEnv} {Φ : FunEnv} {Ψ : StoreTy} {Θ : TaskTy}
    {ps : List (Ident × Ty)} {args : List Expr}
    (ht : HasTypes Δ Φ Ψ Θ emptyCtx args (ps.map Prod.snd))
    (hvals : ∀ a ∈ args, IsValue a) :
    ValuesMatchEnv Δ Φ Ψ Θ (zipParams ps args) ps := by
  induction ps generalizing args with
  | nil =>
    cases ht
    exact .nil
  | cons p rest ih =>
    cases p with
    | mk x τ =>
      cases ht with
      | cons ha hrest =>
        simp only [zipParams, List.map_cons, List.zip_cons_cons]
        exact .cons (hvals _ (List.mem_cons_self ..)) ha
          (ih hrest (fun a ha' => hvals a (List.mem_cons_of_mem _ ha')))

theorem hasTypes_length {Δ : AdtEnv} {Φ : FunEnv} {Ψ : StoreTy} {Θ : TaskTy} {Γ : Ctx}
    {es : List Expr} {τs : List Ty} (h : HasTypes Δ Φ Ψ Θ Γ es τs) :
    es.length = τs.length := by
  induction es generalizing τs with
  | nil => cases h; rfl
  | cons _ _ ih =>
    cases h with
    | cons _ hrest => simp [ih hrest]

mutual
theorem matchPat_sound {Δ : AdtEnv} {Φ : FunEnv} {Ψ : StoreTy} {Θ : TaskTy}
    {p : Pat} {τ : Ty} {bs : List (Ident × Ty)} {v : Expr} {env : List (Ident × Expr)}
    (hp : PatHasType Δ p τ bs) (ht : HasType Δ Φ Ψ Θ emptyCtx v τ) (hv : IsValue v)
    (hm : matchPat p v = some env) :
    ValuesMatchEnv Δ Φ Ψ Θ env bs := by
  cases hp with
  | wild _ =>
    simp only [matchPat, Option.some.injEq] at hm
    subst hm; exact .nil
  | var _ _ =>
    simp only [matchPat, Option.some.injEq] at hm
    subst hm; exact .cons hv ht .nil
  | lit _ =>
    cases v <;> simp only [matchPat] at hm <;> try cases hm
    split at hm
    · cases hm; exact .nil
    · cases hm
  | tuple hps =>
    cases v <;> simp only [matchPat] at hm <;> try cases hm
    cases ht with
    | tuple hts =>
      cases hv with
      | tuple hvs => exact matchPats_sound hps hts hvs hm
  | ctor hlookup hps =>
    cases v <;> simp only [matchPat] at hm <;> try cases hm
    split at hm
    · rename_i heq
      simp only [Bool.and_eq_true, beq_iff_eq] at heq
      rcases heq with ⟨rfl, rfl⟩
      cases ht with
      | makeData hlookup2 hts =>
        rw [hlookup] at hlookup2
        cases hlookup2
        cases hv with
        | makeData _ _ hvs => exact matchPats_sound hps hts hvs hm
    · cases hm

theorem matchPats_sound {Δ : AdtEnv} {Φ : FunEnv} {Ψ : StoreTy} {Θ : TaskTy}
    {ps : List Pat} {τs : List Ty} {bs : List (Ident × Ty)} {vs : List Expr}
    {env : List (Ident × Expr)}
    (hps : PatsHaveType Δ ps τs bs) (hts : HasTypes Δ Φ Ψ Θ emptyCtx vs τs)
    (hvs : ∀ v ∈ vs, IsValue v) (hm : matchPats ps vs = some env) :
    ValuesMatchEnv Δ Φ Ψ Θ env bs := by
  cases hps with
  | nil =>
    cases hts
    simp only [matchPats, Option.some.injEq] at hm
    subst hm; exact .nil
  | cons hp hrest =>
    cases hts with
    | cons hv hts' =>
      simp only [matchPats] at hm
      cases h1 : matchPat _ _ with
      | none => rw [h1] at hm; cases hm
      | some b1 =>
        rw [h1] at hm
        cases h2 : matchPats _ _ with
        | none => rw [h2] at hm; cases hm
        | some b2 =>
          rw [h2] at hm
          cases hm
          exact ValuesMatchEnv.append
            (matchPat_sound hp hv (hvs _ (List.mem_cons_self ..)) h1)
            (matchPats_sound hrest hts' (fun u hu => hvs u (List.mem_cons_of_mem _ hu)) h2)
end

/-! ## Store Typing Helpers -/

theorem store_typed_task_weaken {Δ : AdtEnv} {Φ : FunEnv} {Ψ : StoreTy} {Θ Θ' : TaskTy} {σ : Store}
    (htk : TaskExtends Θ Θ') (hst : StoreTyped Δ Φ Ψ Θ σ) :
    StoreTyped Δ Φ Ψ Θ' σ := by
  refine ⟨hst.1, fun l t hl => ?_⟩
  rcases hst.2 l t hl with ⟨v, hv, hval, hvt⟩
  exact ⟨v, hv, hval, typing_env_weaken (StoreExtends.refl Ψ) htk hvt⟩

theorem store_typed_alloc {Δ : AdtEnv} {Φ : FunEnv} {Ψ : StoreTy} {Θ : TaskTy}
    {σ : Store} {v : Expr} {τ : Ty}
    (hst : StoreTyped Δ Φ Ψ Θ σ) (hv : IsValue v) (ht : HasType Δ Φ Ψ Θ emptyCtx v τ) :
    StoreTyped Δ Φ (Ψ ++ [τ]) Θ (σ ++ [v]) := by
  have hext : StoreExtends Ψ (Ψ ++ [τ]) := StoreExtends.append Ψ τ
  refine ⟨by simp [hst.1], fun l t hl => ?_⟩
  cases Nat.lt_or_ge l Ψ.length with
  | inl hlt =>
    rw [List.getElem?_append_left hlt] at hl
    rcases hst.2 l t hl with ⟨w, hw, hwv, hwt⟩
    have hlt' : l < σ.length := hst.1 ▸ hlt
    refine ⟨w, ?_, hwv, typing_env_weaken hext (TaskExtends.refl Θ) hwt⟩
    rw [List.getElem?_append_left hlt']
    exact hw
  | inr hge =>
    rw [List.getElem?_append_right hge] at hl
    have hlt1 : l - Ψ.length < 1 := by simpa using lt_length_of_getElem?_eq_some hl
    have heql : l = Ψ.length := Nat.le_antisymm (Nat.le_of_sub_eq_zero (Nat.lt_one_iff.mp hlt1)) hge
    subst heql
    simp at hl
    subst hl
    refine ⟨v, ?_, hv, typing_env_weaken hext (TaskExtends.refl Θ) ht⟩
    rw [← hst.1]
    simp

theorem store_typed_update {Δ : AdtEnv} {Φ : FunEnv} {Ψ : StoreTy} {Θ : TaskTy} {σ : Store}
    {l : Loc} {v : Expr} {τ : Ty}
    (hst : StoreTyped Δ Φ Ψ Θ σ) (hl : Ψ[l]? = some τ)
    (hv : IsValue v) (ht : HasType Δ Φ Ψ Θ emptyCtx v τ) :
    StoreTyped Δ Φ Ψ Θ (σ.set l v) := by
  have hltΨ : l < Ψ.length := lt_length_of_getElem?_eq_some hl
  have hltσ : l < σ.length := hst.1 ▸ hltΨ
  refine ⟨by simp [hst.1], fun k t hk => ?_⟩
  by_cases hkl : k = l
  · subst hkl
    rw [hl] at hk; cases hk
    exact ⟨v, by simp [hltσ], hv, ht⟩
  · rcases hst.2 k t hk with ⟨w, hw, hwv, hwt⟩
    refine ⟨w, ?_, hwv, hwt⟩
    rw [List.getElem?_set_ne (Ne.symm hkl)]
    exact hw

/-! ## Canonical Forms & Operator Lemmas -/

theorem canonical_bool {Δ : AdtEnv} {Φ : FunEnv} {Ψ : StoreTy} {Θ : TaskTy} {v : Expr}
    (ht : HasType Δ Φ Ψ Θ emptyCtx v .bool) (hv : IsValue v) :
    ∃ b : Bool, v = .lit (.bool b) := by
  cases hv with
  | lit l => cases ht with | lit hl => cases hl; exact ⟨_, rfl⟩
  | loc _ => cases ht
  | taskRef _ => cases ht
  | syncRef _ _ => cases ht with | syncRef hsr => cases hsr
  | lam _ _ _ _ => cases ht
  | tuple _ => cases ht
  | makeData _ _ _ => cases ht

theorem canonical_int {Δ : AdtEnv} {Φ : FunEnv} {Ψ : StoreTy} {Θ : TaskTy} {v : Expr}
    (ht : HasType Δ Φ Ψ Θ emptyCtx v .int) (hv : IsValue v) :
    ∃ n : Int32, v = .lit (.int n) := by
  cases hv with
  | lit l => cases ht with | lit hl => cases hl; exact ⟨_, rfl⟩
  | loc _ => cases ht
  | taskRef _ => cases ht
  | syncRef _ _ => cases ht with | syncRef hsr => cases hsr
  | lam _ _ _ _ => cases ht
  | tuple _ => cases ht
  | makeData _ _ _ => cases ht

theorem canonical_str {Δ : AdtEnv} {Φ : FunEnv} {Ψ : StoreTy} {Θ : TaskTy} {v : Expr}
    (ht : HasType Δ Φ Ψ Θ emptyCtx v .str) (hv : IsValue v) :
    ∃ s : String, v = .lit (.str s) := by
  cases hv with
  | lit l => cases ht with | lit hl => cases hl; exact ⟨_, rfl⟩
  | loc _ => cases ht
  | taskRef _ => cases ht
  | syncRef _ _ => cases ht with | syncRef hsr => cases hsr
  | lam _ _ _ _ => cases ht
  | tuple _ => cases ht
  | makeData _ _ _ => cases ht

theorem canonical_int64 {Δ : AdtEnv} {Φ : FunEnv} {Ψ : StoreTy} {Θ : TaskTy} {v : Expr}
    (ht : HasType Δ Φ Ψ Θ emptyCtx v .int64) (hv : IsValue v) :
    ∃ n : Int64, v = .lit (.int64 n) := by
  cases hv with
  | lit l => cases ht with | lit hl => cases hl; exact ⟨_, rfl⟩
  | loc _ => cases ht
  | taskRef _ => cases ht
  | syncRef _ _ => cases ht with | syncRef hsr => cases hsr
  | lam _ _ _ _ => cases ht
  | tuple _ => cases ht
  | makeData _ _ _ => cases ht

theorem canonical_float {Δ : AdtEnv} {Φ : FunEnv} {Ψ : StoreTy} {Θ : TaskTy} {v : Expr}
    (ht : HasType Δ Φ Ψ Θ emptyCtx v .float) (hv : IsValue v) :
    ∃ bits : UInt64, v = .lit (.floatBits bits) := by
  cases hv with
  | lit l => cases ht with | lit hl => cases hl; exact ⟨_, rfl⟩
  | loc _ => cases ht
  | taskRef _ => cases ht
  | syncRef _ _ => cases ht with | syncRef hsr => cases hsr
  | lam _ _ _ _ => cases ht
  | tuple _ => cases ht
  | makeData _ _ _ => cases ht

theorem canonical_float32 {Δ : AdtEnv} {Φ : FunEnv} {Ψ : StoreTy} {Θ : TaskTy} {v : Expr}
    (ht : HasType Δ Φ Ψ Θ emptyCtx v .float32) (hv : IsValue v) :
    ∃ bits : UInt32, v = .lit (.float32Bits bits) := by
  cases hv with
  | lit l => cases ht with | lit hl => cases hl; exact ⟨_, rfl⟩
  | loc _ => cases ht
  | taskRef _ => cases ht
  | syncRef _ _ => cases ht with | syncRef hsr => cases hsr
  | lam _ _ _ _ => cases ht
  | tuple _ => cases ht
  | makeData _ _ _ => cases ht

theorem canonical_char {Δ : AdtEnv} {Φ : FunEnv} {Ψ : StoreTy} {Θ : TaskTy} {v : Expr}
    (ht : HasType Δ Φ Ψ Θ emptyCtx v .char) (hv : IsValue v) :
    ∃ c : UInt32, v = .lit (.char c) := by
  cases hv with
  | lit l => cases ht with | lit hl => cases hl; exact ⟨_, rfl⟩
  | loc _ => cases ht
  | taskRef _ => cases ht
  | syncRef _ _ => cases ht with | syncRef hsr => cases hsr
  | lam _ _ _ _ => cases ht
  | tuple _ => cases ht
  | makeData _ _ _ => cases ht

theorem canonical_fn {Δ : AdtEnv} {Φ : FunEnv} {Ψ : StoreTy} {Θ : TaskTy} {v : Expr}
    {m : Mode} {paramTys : List Ty} {ret : Ty}
    (ht : HasType Δ Φ Ψ Θ emptyCtx v (.fn m paramTys ret)) (hv : IsValue v) :
    ∃ m0 ps ret0 body,
      v = .lam m0 ps ret0 body ∧
      ModeSub m0 m ∧
      TyListSub paramTys (ps.map Prod.snd) ∧
      TySub ret0 ret := by
  cases hv with
  | lit _ => cases ht with | lit hl => cases hl
  | loc _ => cases ht
  | taskRef _ => cases ht
  | syncRef _ _ => cases ht with | syncRef hsr => cases hsr
  | lam m0 ps ret0 body =>
    cases ht with
    | lam hm hps hr _ _ => exact ⟨m0, ps, ret0, body, rfl, hm, hps, hr⟩
  | tuple _ => cases ht
  | makeData _ _ _ => cases ht

theorem canonical_adt {Δ : AdtEnv} {Φ : FunEnv} {Ψ : StoreTy} {Θ : TaskTy} {v : Expr} {adt : Ident}
    (ht : HasType Δ Φ Ψ Θ emptyCtx v (.adt adt)) (hv : IsValue v) :
    ∃ tag vs, v = .makeData adt tag vs ∧ (∀ u ∈ vs, IsValue u) := by
  cases hv with
  | lit _ => cases ht with | lit hl => cases hl
  | loc _ => cases ht
  | taskRef _ => cases ht
  | syncRef _ _ => cases ht with | syncRef hsr => cases hsr
  | lam _ _ _ _ => cases ht
  | tuple _ => cases ht
  | makeData _ tag hvs =>
    cases ht with
    | makeData _ _ => exact ⟨tag, _, rfl, hvs⟩

theorem canonical_cell {Δ : AdtEnv} {Φ : FunEnv} {Ψ : StoreTy} {Θ : TaskTy} {v : Expr} {τ : Ty}
    (ht : HasType Δ Φ Ψ Θ emptyCtx v (.cell τ)) (hv : IsValue v) :
    ∃ l : Loc, v = .loc l ∧ Ψ[l]? = some τ := by
  cases hv with
  | lit _ => cases ht with | lit hl => cases hl
  | loc l => cases ht with | loc hl => exact ⟨l, rfl, hl⟩
  | taskRef _ => cases ht
  | syncRef _ _ => cases ht with | syncRef hsr => cases hsr
  | lam _ _ _ _ => cases ht
  | tuple _ => cases ht
  | makeData _ _ _ => cases ht

theorem canonical_task {Δ : AdtEnv} {Φ : FunEnv} {Ψ : StoreTy} {Θ : TaskTy} {v : Expr} {τ : Ty}
    (ht : HasType Δ Φ Ψ Θ emptyCtx v (.task τ)) (hv : IsValue v) :
    ∃ tid τ0, v = .taskRef tid ∧ Θ.tasks[tid]? = some τ0 ∧ IsSend Δ τ0 ∧ TySub τ0 τ := by
  cases hv with
  | lit _ => cases ht with | lit hl => cases hl
  | loc _ => cases ht
  | taskRef tid =>
    cases ht with
    | taskRef htid hsend hs => exact ⟨tid, _, rfl, htid, hsend, hs⟩
  | syncRef _ _ => cases ht with | syncRef hsr => cases hsr
  | lam _ _ _ _ => cases ht
  | tuple _ => cases ht
  | makeData _ _ _ => cases ht

theorem canonical_mvar {Δ : AdtEnv} {Φ : FunEnv} {Ψ : StoreTy} {Θ : TaskTy} {v : Expr} {τ : Ty}
    (ht : HasType Δ Φ Ψ Θ emptyCtx v (.mvar τ)) (hv : IsValue v) :
    ∃ mid, v = .syncRef .mvar mid ∧ Θ.mvars[mid]? = some τ ∧ IsSend Δ τ := by
  cases hv with
  | lit _ => cases ht with | lit hl => cases hl
  | loc _ => cases ht
  | taskRef _ => cases ht
  | syncRef k id =>
    cases ht with
    | syncRef hsr =>
      cases hsr with
      | mvar hm hsend => exact ⟨id, rfl, hm, hsend⟩
  | lam _ _ _ _ => cases ht
  | tuple _ => cases ht
  | makeData _ _ _ => cases ht

theorem canonical_chan {Δ : AdtEnv} {Φ : FunEnv} {Ψ : StoreTy} {Θ : TaskTy} {v : Expr} {τ : Ty}
    (ht : HasType Δ Φ Ψ Θ emptyCtx v (.chan τ)) (hv : IsValue v) :
    ∃ cid, v = .syncRef .chan cid ∧ Θ.chans[cid]? = some τ ∧ IsSend Δ τ := by
  cases hv with
  | lit _ => cases ht with | lit hl => cases hl
  | loc _ => cases ht
  | taskRef _ => cases ht
  | syncRef k id =>
    cases ht with
    | syncRef hsr =>
      cases hsr with
      | chan hc hsend => exact ⟨id, rfl, hc, hsend⟩
  | lam _ _ _ _ => cases ht
  | tuple _ => cases ht
  | makeData _ _ _ => cases ht

theorem canonical_actor {Δ : AdtEnv} {Φ : FunEnv} {Ψ : StoreTy} {Θ : TaskTy} {v : Expr} {σ_ty : Ty}
    (ht : HasType Δ Φ Ψ Θ emptyCtx v (.actor σ_ty)) (hv : IsValue v) :
    ∃ aid, v = .syncRef .actor aid ∧ Θ.actors[aid]? = some σ_ty := by
  cases hv with
  | lit _ => cases ht with | lit hl => cases hl
  | loc _ => cases ht
  | taskRef _ => cases ht
  | syncRef k id =>
    cases ht with
    | syncRef hsr =>
      cases hsr with
      | actor ha => exact ⟨id, rfl, ha⟩
  | lam _ _ _ _ => cases ht
  | tuple _ => cases ht
  | makeData _ _ _ => cases ht

theorem evalUnOp_sound {op : UnOp} {l l' : Lit} {τ1 τr : Ty}
    (hop : UnOpHasType op τ1 τr) (hl : LitHasType l τ1) (he : evalUnOp op l = some l') :
    LitHasType l' τr := by
  cases hop <;> cases hl <;> simp [evalUnOp] at he <;> subst he <;> constructor

theorem evalBinOp_sound {op : BinOp} {l1 l2 l' : Lit} {τ1 τ2 τr : Ty}
    (hop : BinOpHasType op τ1 τ2 τr) (hl1 : LitHasType l1 τ1) (hl2 : LitHasType l2 τ2)
    (he : evalBinOp op l1 l2 = some (.val l')) :
    LitHasType l' τr := by
  cases hop <;> cases hl1 <;> cases hl2 <;> simp [evalBinOp] at he
  all_goals
    first
    | (subst he; constructor)
    | (split at he <;> simp at he; subst he; constructor)

theorem unOp_eval_progress {Δ : AdtEnv} {Φ : FunEnv} {Ψ : StoreTy} {Θ : TaskTy}
    {pool : ConcPool} {σ : Store} {op : UnOp} {v1 : Expr} {τ1 τr : Ty}
    (hop : UnOpHasType op τ1 τr)
    (ht1 : HasType Δ Φ Ψ Θ emptyCtx v1 τ1) (hv1 : IsValue v1) :
    ∃ e' σ' eff, Step Δ Φ pool (.un op v1) σ e' σ' eff := by
  cases hop with
  | not =>
    rcases canonical_bool ht1 hv1 with ⟨b, rfl⟩
    exact ⟨_, σ, .none, .unVal (l' := .bool (!b)) rfl⟩
  | neg =>
    rcases canonical_int ht1 hv1 with ⟨n, rfl⟩
    exact ⟨_, σ, .none, .unVal (l' := .int (-n)) rfl⟩
  | bitNot =>
    rcases canonical_int ht1 hv1 with ⟨n, rfl⟩
    exact ⟨_, σ, .none, .unVal (l' := .int (~~~n)) rfl⟩
  | neg64 =>
    rcases canonical_int64 ht1 hv1 with ⟨n, rfl⟩
    exact ⟨_, σ, .none, .unVal (l' := .int64 (-n)) rfl⟩
  | bitNot64 =>
    rcases canonical_int64 ht1 hv1 with ⟨n, rfl⟩
    exact ⟨_, σ, .none, .unVal (l' := .int64 (~~~n)) rfl⟩
  | negFloat =>
    rcases canonical_float ht1 hv1 with ⟨bits, rfl⟩
    exact ⟨_, σ, .none, .unVal (l' := .floatBits (-(Float.ofBits bits)).toBits) rfl⟩
  | negFloat32 =>
    rcases canonical_float32 ht1 hv1 with ⟨bits, rfl⟩
    exact ⟨_, σ, .none, .unVal (l' := .float32Bits (-(Float32.ofBits bits)).toBits) rfl⟩
  | intToI64 =>
    rcases canonical_int ht1 hv1 with ⟨n, rfl⟩
    exact ⟨_, σ, .none, .unVal (l' := .int64 (Int64.ofInt n.toInt)) rfl⟩
  | i64ToInt =>
    rcases canonical_int64 ht1 hv1 with ⟨n, rfl⟩
    exact ⟨_, σ, .none, .unVal (l' := .int (Int32.ofInt n.toInt)) rfl⟩

theorem binOp_eval_progress {Δ : AdtEnv} {Φ : FunEnv} {Ψ : StoreTy} {Θ : TaskTy}
    {pool : ConcPool} {σ : Store} {op : BinOp} {v1 v2 : Expr} {τ1 τ2 τr : Ty}
    (hand : op ≠ .and) (hor : op ≠ .or)
    (hop : BinOpHasType op τ1 τ2 τr)
    (ht1 : HasType Δ Φ Ψ Θ emptyCtx v1 τ1) (hv1 : IsValue v1)
    (ht2 : HasType Δ Φ Ψ Θ emptyCtx v2 τ2) (hv2 : IsValue v2) :
    ∃ e' σ' eff, Step Δ Φ pool (.bin op v1 v2) σ e' σ' eff := by
  cases hop with
  | and => exact False.elim (hand rfl)
  | or => exact False.elim (hor rfl)
  | div =>
    rcases canonical_int ht1 hv1 with ⟨a, rfl⟩
    rcases canonical_int ht2 hv2 with ⟨b, rfl⟩
    by_cases hb : (b == 0) = true
    · exact ⟨.trap .divByZero, σ, .none, .binTrap (by simp [evalBinOp, hb])⟩
    · have hb' : (b == 0) = false := Bool.eq_false_iff.mpr hb
      exact ⟨_, σ, .none, .binVal (l' := .int (a / b)) (by simp [evalBinOp, hb'])⟩
  | rem =>
    rcases canonical_int ht1 hv1 with ⟨a, rfl⟩
    rcases canonical_int ht2 hv2 with ⟨b, rfl⟩
    by_cases hb : (b == 0) = true
    · exact ⟨.trap .divByZero, σ, .none, .binTrap (by simp [evalBinOp, hb])⟩
    · have hb' : (b == 0) = false := Bool.eq_false_iff.mpr hb
      exact ⟨_, σ, .none, .binVal (l' := .int (a % b)) (by simp [evalBinOp, hb'])⟩
  | div64 =>
    rcases canonical_int64 ht1 hv1 with ⟨a, rfl⟩
    rcases canonical_int64 ht2 hv2 with ⟨b, rfl⟩
    by_cases hb : (b == 0) = true
    · exact ⟨.trap .divByZero, σ, .none, .binTrap (by simp [evalBinOp, hb])⟩
    · have hb' : (b == 0) = false := Bool.eq_false_iff.mpr hb
      exact ⟨_, σ, .none, .binVal (l' := .int64 (a / b)) (by simp [evalBinOp, hb'])⟩
  | rem64 =>
    rcases canonical_int64 ht1 hv1 with ⟨a, rfl⟩
    rcases canonical_int64 ht2 hv2 with ⟨b, rfl⟩
    by_cases hb : (b == 0) = true
    · exact ⟨.trap .divByZero, σ, .none, .binTrap (by simp [evalBinOp, hb])⟩
    · have hb' : (b == 0) = false := Bool.eq_false_iff.mpr hb
      exact ⟨_, σ, .none, .binVal (l' := .int64 (a % b)) (by simp [evalBinOp, hb'])⟩
  | _ =>
    first
    | (rcases canonical_int ht1 hv1 with ⟨a, rfl⟩
       rcases canonical_int ht2 hv2 with ⟨b, rfl⟩
       exact ⟨_, σ, .none, .binVal (l' := _) rfl⟩)
    | (rcases canonical_int64 ht1 hv1 with ⟨a, rfl⟩
       rcases canonical_int64 ht2 hv2 with ⟨b, rfl⟩
       exact ⟨_, σ, .none, .binVal (l' := _) rfl⟩)
    | (rcases canonical_int64 ht1 hv1 with ⟨a, rfl⟩
       rcases canonical_int ht2 hv2 with ⟨b, rfl⟩
       exact ⟨_, σ, .none, .binVal (l' := _) rfl⟩)
    | (rcases canonical_float ht1 hv1 with ⟨a, rfl⟩
       rcases canonical_float ht2 hv2 with ⟨b, rfl⟩
       exact ⟨_, σ, .none, .binVal (l' := _) rfl⟩)
    | (rcases canonical_float32 ht1 hv1 with ⟨a, rfl⟩
       rcases canonical_float32 ht2 hv2 with ⟨b, rfl⟩
       exact ⟨_, σ, .none, .binVal (l' := _) rfl⟩)
    | (rcases canonical_bool ht1 hv1 with ⟨a, rfl⟩
       rcases canonical_bool ht2 hv2 with ⟨b, rfl⟩
       exact ⟨_, σ, .none, .binVal (l' := _) rfl⟩)
    | (rcases canonical_char ht1 hv1 with ⟨a, rfl⟩
       rcases canonical_char ht2 hv2 with ⟨b, rfl⟩
       exact ⟨_, σ, .none, .binVal (l' := _) rfl⟩)
    | (rcases canonical_str ht1 hv1 with ⟨a, rfl⟩
       rcases canonical_str ht2 hv2 with ⟨b, rfl⟩
       exact ⟨_, σ, .none, .binVal (l' := _) rfl⟩)

/-! ## Progress Theorem -/

mutual
theorem progress {Δ : AdtEnv} {Φ : FunEnv} {Ψ : StoreTy} {Θ : TaskTy}
    {pool : ConcPool} {σ : Store} {e : Expr} {τ : Ty}
    (hΦ : FunEnvTyped Δ Φ)
    (ht : HasType Δ Φ Ψ Θ emptyCtx e τ)
    (hσ : StoreTyped Δ Φ Ψ Θ σ)
    (hpool : PoolTyped Δ Φ Ψ Θ pool) :
    IsTerminal e ∨ BlockedOnTask pool e ∨ ∃ e' σ' eff, Step Δ Φ pool e σ e' σ' eff := by
  cases ht with
  | lit _ => exact Or.inl (Or.inl (.lit _))
  | var hx _ => simp [emptyCtx] at hx
  | loc _ => exact Or.inl (Or.inl (.loc _))
  | taskRef _ _ _ => exact Or.inl (Or.inl (.taskRef _))
  | syncRef _ => exact Or.inl (Or.inl (.syncRef _ _))
  | tuple hts =>
    rcases progressList hΦ hts hσ hpool with hvals | ⟨t, htrap⟩ | hblk | ⟨es', σ', eff, hstep⟩
    · exact Or.inl (Or.inl (.tuple hvals))
    · exact Or.inr (Or.inr ⟨.trap t, σ, .none, .tupleTrap htrap⟩)
    · exact Or.inr (Or.inl (.tuple hblk))
    · exact Or.inr (Or.inr ⟨.tuple es', σ', eff, .tupleStep hstep⟩)
  | blockEmpty => exact Or.inr (Or.inr ⟨.lit .unit, σ, .none, .blockEmpty⟩)
  | blockSingle _ => exact Or.inr (Or.inr ⟨_, σ, .none, .blockSingle⟩)
  | blockCons h1 _ =>
    rcases progress hΦ h1 hσ hpool with (hv1 | ⟨t, rfl⟩) | hblk | ⟨e1', σ', eff, hs1⟩
    · exact Or.inr (Or.inr ⟨_, σ, .none, .blockConsVal hv1⟩)
    · exact Or.inr (Or.inr ⟨.trap t, σ, .none, .blockConsTrap⟩)
    · exact Or.inr (Or.inl (.blockCons hblk))
    · exact Or.inr (Or.inr ⟨_, σ', eff, .blockConsStep hs1⟩)
  | lam _ _ _ _ _ => exact Or.inl (Or.inl (.lam _ _ _ _))
  | apply hfn hargs _ =>
    rcases progress hΦ hfn hσ hpool with (hvfn | ⟨t, rfl⟩) | hblk | ⟨fn', σ', eff, hsfn⟩
    · rcases progressList hΦ hargs hσ hpool with hvals | ⟨t, htrap⟩ | hblkArgs | ⟨args', σ', eff, hsargs⟩
      · rcases canonical_fn hfn hvfn with ⟨_, ps, _, _, rfl, _, hpsSub, _⟩
        have hlen1 := hasTypes_length hargs
        have hlen2 := tyListSub_length hpsSub
        rw [hlen2, List.length_map] at hlen1
        exact Or.inr (Or.inr ⟨_, σ, .none, .applyBeta hvals hlen1⟩)
      · exact Or.inr (Or.inr ⟨.trap t, σ, .none, .applyArgsTrap hvfn htrap⟩)
      · exact Or.inr (Or.inl (.applyArgs hvfn hblkArgs))
      · exact Or.inr (Or.inr ⟨_, σ', eff, .applyArgs hvfn hsargs⟩)
    · exact Or.inr (Or.inr ⟨.trap t, σ, .none, .applyFnTrap⟩)
    · exact Or.inr (Or.inl (.applyFn hblk))
    · exact Or.inr (Or.inr ⟨_, σ', eff, .applyFn hsfn⟩)
  | applyDir hf hargs _ =>
    rcases progressList hΦ hargs hσ hpool with hvals | ⟨t, htrap⟩ | hblk | ⟨args', σ', eff, hsargs⟩
    · have hlen := hasTypes_length hargs
      rw [List.length_map] at hlen
      exact Or.inr (Or.inr ⟨_, σ, .none, .applyDirBeta hf hvals hlen⟩)
    · exact Or.inr (Or.inr ⟨.trap t, σ, .none, .applyDirTrap htrap⟩)
    · exact Or.inr (Or.inl (.applyDirArgs hblk))
    · exact Or.inr (Or.inr ⟨_, σ', eff, .applyDirArgs hsargs⟩)
  | @bin _ op e1 e2 _ _ _ hop h1 h2 =>
    rcases progress hΦ h1 hσ hpool with (hv1 | ⟨t, rfl⟩) | hblk1 | ⟨e1', σ', eff, hs1⟩
    · by_cases hand : op = .and
      · subst hand
        cases hop
        rcases canonical_bool h1 hv1 with ⟨b, rfl⟩
        cases b
        · exact Or.inr (Or.inr ⟨_, σ, .none, .binAndFalse⟩)
        · exact Or.inr (Or.inr ⟨_, σ, .none, .binAndTrue⟩)
      · by_cases hor : op = .or
        · subst hor
          cases hop
          rcases canonical_bool h1 hv1 with ⟨b, rfl⟩
          cases b
          · exact Or.inr (Or.inr ⟨_, σ, .none, .binOrFalse⟩)
          · exact Or.inr (Or.inr ⟨_, σ, .none, .binOrTrue⟩)
        · rcases progress hΦ h2 hσ hpool with (hv2 | ⟨t, rfl⟩) | hblk2 | ⟨e2', σ', eff, hs2⟩
          · exact Or.inr (Or.inr (binOp_eval_progress hand hor hop h1 hv1 h2 hv2))
          · exact Or.inr (Or.inr ⟨.trap t, σ, .none, .binRightTrap hand hor hv1⟩)
          · exact Or.inr (Or.inl (.binRight hand hor hv1 hblk2))
          · exact Or.inr (Or.inr ⟨_, σ', eff, .binRight hand hor hv1 hs2⟩)
    · exact Or.inr (Or.inr ⟨.trap t, σ, .none, .binLeftTrap⟩)
    · exact Or.inr (Or.inl (.binLeft hblk1))
    · exact Or.inr (Or.inr ⟨_, σ', eff, .binLeft hs1⟩)
  | un hop h1 =>
    rcases progress hΦ h1 hσ hpool with (hv1 | ⟨t, rfl⟩) | hblk | ⟨e1', σ', eff, hs1⟩
    · exact Or.inr (Or.inr (unOp_eval_progress hop h1 hv1))
    · exact Or.inr (Or.inr ⟨.trap t, σ, .none, .unTrap⟩)
    · exact Or.inr (Or.inl (.un hblk))
    · exact Or.inr (Or.inr ⟨_, σ', eff, .unStep hs1⟩)
  | let_ h1 _ =>
    rcases progress hΦ h1 hσ hpool with (hv1 | ⟨t, rfl⟩) | hblk | ⟨e1', σ', eff, hs1⟩
    · exact Or.inr (Or.inr ⟨_, σ, .none, .letVal hv1⟩)
    · exact Or.inr (Or.inr ⟨.trap t, σ, .none, .letTrap⟩)
    · exact Or.inr (Or.inl (.let_ hblk))
    · exact Or.inr (Or.inr ⟨_, σ', eff, .letStep hs1⟩)
  | if_ hc _ _ =>
    rcases progress hΦ hc hσ hpool with (hvc | ⟨t, rfl⟩) | hblk | ⟨c', σ', eff, hsc⟩
    · rcases canonical_bool hc hvc with ⟨b, rfl⟩
      cases b
      · exact Or.inr (Or.inr ⟨_, σ, .none, .ifFalse⟩)
      · exact Or.inr (Or.inr ⟨_, σ, .none, .ifTrue⟩)
    · exact Or.inr (Or.inr ⟨.trap t, σ, .none, .ifTrap⟩)
    · exact Or.inr (Or.inl (.if_ hblk))
    · exact Or.inr (Or.inr ⟨_, σ', eff, .ifStep hsc⟩)
  | while_ _ _ => exact Or.inr (Or.inr ⟨_, σ, .none, .whileUnfold⟩)
  | @match_ _ scrut arms _ _ hs _ =>
    rcases progress hΦ hs hσ hpool with (hvs | ⟨t, rfl⟩) | hblk | ⟨s', σ', eff, hss⟩
    · cases arms with
      | nil => exact Or.inr (Or.inr ⟨.trap .matchFailure, σ, .none, .matchEmpty hvs⟩)
      | cons arm rest =>
        cases arm with
        | mk p body =>
          cases hm : matchPat p scrut with
          | none => exact Or.inr (Or.inr ⟨_, σ, .none, .matchMiss hvs hm⟩)
          | some env => exact Or.inr (Or.inr ⟨_, σ, .none, .matchHit hvs hm⟩)
    · exact Or.inr (Or.inr ⟨.trap t, σ, .none, .matchScrutTrap⟩)
    · exact Or.inr (Or.inl (.match_ hblk))
    · exact Or.inr (Or.inr ⟨_, σ', eff, .matchScrut hss⟩)
  | makeData _ hts =>
    rcases progressList hΦ hts hσ hpool with hvals | ⟨t, htrap⟩ | hblk | ⟨es', σ', eff, hstep⟩
    · exact Or.inl (Or.inl (.makeData _ _ hvals))
    · exact Or.inr (Or.inr ⟨.trap t, σ, .none, .makeDataTrap htrap⟩)
    · exact Or.inr (Or.inl (.makeData hblk))
    · exact Or.inr (Or.inr ⟨_, σ', eff, .makeDataStep hstep⟩)
  | getTag he =>
    rcases progress hΦ he hσ hpool with (hv | ⟨t, rfl⟩) | hblk | ⟨e', σ', eff, hse⟩
    · rcases canonical_adt he hv with ⟨tag, vs, rfl, hvs⟩
      exact Or.inr (Or.inr ⟨_, σ, .none, .getTagVal hvs⟩)
    · exact Or.inr (Or.inr ⟨.trap t, σ, .none, .getTagTrap⟩)
    · exact Or.inr (Or.inl (.getTag hblk))
    · exact Or.inr (Or.inr ⟨_, σ', eff, .getTagStep hse⟩)
  | cellNew he =>
    rcases progress hΦ he hσ hpool with (hv | ⟨t, rfl⟩) | hblk | ⟨e', σ', eff, hse⟩
    · exact Or.inr (Or.inr ⟨_, _, .none, .cellNewVal hv⟩)
    · exact Or.inr (Or.inr ⟨.trap t, σ, .none, .cellNewTrap⟩)
    · exact Or.inr (Or.inl (.cellNew hblk))
    · exact Or.inr (Or.inr ⟨_, σ', eff, .cellNewStep hse⟩)
  | cellGet he _ =>
    rcases progress hΦ he hσ hpool with (hv | ⟨t, rfl⟩) | hblk | ⟨e', σ', eff, hse⟩
    · rcases canonical_cell he hv with ⟨l, rfl, hl⟩
      rcases hσ.2 l _ hl with ⟨v, hvσ, _, _⟩
      exact Or.inr (Or.inr ⟨v, σ, .none, .cellGetVal hvσ⟩)
    · exact Or.inr (Or.inr ⟨.trap t, σ, .none, .cellGetTrap⟩)
    · exact Or.inr (Or.inl (.cellGet hblk))
    · exact Or.inr (Or.inr ⟨_, σ', eff, .cellGetStep hse⟩)
  | cellSet h1 h2 =>
    rcases progress hΦ h1 hσ hpool with (hv1 | ⟨t, rfl⟩) | hblk1 | ⟨e1', σ', eff, hs1⟩
    · rcases progress hΦ h2 hσ hpool with (hv2 | ⟨t, rfl⟩) | hblk2 | ⟨e2', σ', eff, hs2⟩
      · rcases canonical_cell h1 hv1 with ⟨l, rfl, hl⟩
        have hltΨ : l < Ψ.length := lt_length_of_getElem?_eq_some hl
        have hltσ : l < σ.length := hσ.1 ▸ hltΨ
        exact Or.inr (Or.inr ⟨_, _, .none, .cellSetVal hltσ hv2⟩)
      · exact Or.inr (Or.inr ⟨.trap t, σ, .none, .cellSetRightTrap hv1⟩)
      · exact Or.inr (Or.inl (.cellSetRight hv1 hblk2))
      · exact Or.inr (Or.inr ⟨_, σ', eff, .cellSetRight hv1 hs2⟩)
    · exact Or.inr (Or.inr ⟨.trap t, σ, .none, .cellSetLeftTrap⟩)
    · exact Or.inr (Or.inl (.cellSetLeft hblk1))
    · exact Or.inr (Or.inr ⟨_, σ', eff, .cellSetLeft hs1⟩)
  | spawn hfn _ _ =>
    rcases progress hΦ hfn hσ hpool with (hvfn | ⟨t, rfl⟩) | hblk | ⟨fn', σ', eff, hsfn⟩
    · rcases canonical_fn hfn hvfn with ⟨_, ps, _, body, rfl, hmSub, hpsSub, _⟩
      cases hmSub with
      | refl =>
        cases hps : ps with
        | nil => exact Or.inr (Or.inr ⟨_, σ, .spawnTask body, .spawnBeta⟩)
        | cons _ _ => rw [hps] at hpsSub; cases hpsSub
    · exact Or.inr (Or.inr ⟨.trap t, σ, .none, .spawnTrap⟩)
    · exact Or.inr (Or.inl (.spawn hblk))
    · exact Or.inr (Or.inr ⟨_, σ', eff, .spawnStep hsfn⟩)
  | await he _ _ =>
    rcases progress hΦ he hσ hpool with (hve | ⟨t, rfl⟩) | hblk | ⟨e', σ', eff, hse⟩
    · rcases canonical_task he hve with ⟨tid, τ0, rfl, htid, _, _⟩
      rcases hpool.tasks_ty tid τ0 htid with ⟨_, te, hte, _⟩
      cases te with
      | pendingReply => exact Or.inr (Or.inl (.awaitPending hte))
      | running et =>
        by_cases hterm : IsTerminal et
        · rcases hterm with hval | ⟨tr, rfl⟩
          · exact Or.inr (Or.inr ⟨et, σ, .none, .awaitVal hte hval⟩)
          · exact Or.inr (Or.inr ⟨.trap tr, σ, .none, .awaitTaskTrap hte⟩)
        · exact Or.inr (Or.inl (.awaitRunning hte hterm))
    · exact Or.inr (Or.inr ⟨.trap t, σ, .none, .awaitTrap⟩)
    · exact Or.inr (Or.inl (.awaitStep hblk))
    · exact Or.inr (Or.inr ⟨_, σ', eff, .awaitStep hse⟩)
  | concPrim hop hargs _ =>
    rcases progressList hΦ hargs hσ hpool with hvals | ⟨t, htrap⟩ | hblk | ⟨args', σ', eff, hsargs⟩
    · cases hop with
      | mvarNew _ =>
        cases hargs with
        | cons _ hnil =>
          cases hnil
          exact Or.inr (Or.inr ⟨_, σ, _, .concPrimVal (.mvarNew (hvals _ (List.mem_cons_self ..)))⟩)
      | @mvarEmpty τm _ =>
        cases hargs
        exact Or.inr (Or.inr ⟨_, σ, _, .concPrimVal (.mvarEmpty τm)⟩)
      | mvarTake _ =>
        cases hargs with
        | cons h1 hnil =>
          cases hnil
          rcases canonical_mvar h1 (hvals _ (List.mem_cons_self ..)) with ⟨mid, rfl, hmid, _⟩
          rcases hpool.mvars_ty mid _ hmid with ⟨_, slot, hslot, _⟩
          cases slot with
          | none => exact Or.inr (Or.inl (.mvarTakeWait hslot))
          | some v => exact Or.inr (Or.inr ⟨v, σ, _, .concPrimVal (.mvarTake hslot)⟩)
      | mvarPut _ =>
        cases hargs with
        | cons h1 hrest =>
          cases hrest with
          | cons h2 hnil =>
            cases hnil
            have hv1 := hvals _ (List.mem_cons_self ..)
            have hv2 := hvals _ (List.mem_cons_of_mem _ (List.mem_cons_self ..))
            rcases canonical_mvar h1 hv1 with ⟨mid, rfl, hmid, _⟩
            rcases hpool.mvars_ty mid _ hmid with ⟨_, slot, hslot, _⟩
            cases slot with
            | none => exact Or.inr (Or.inr ⟨_, σ, _, .concPrimVal (.mvarPut hslot hv2)⟩)
            | some old => exact Or.inr (Or.inl (.mvarPutWait hslot hv2))
      | @chanNew τc _ =>
        cases hargs with
        | cons h1 hnil =>
          cases hnil
          rcases canonical_int h1 (hvals _ (List.mem_cons_self ..)) with ⟨n, rfl⟩
          exact Or.inr (Or.inr ⟨_, σ, _, .concPrimVal (.chanNew τc n)⟩)
      | chanSend _ =>
        cases hargs with
        | cons h1 hrest =>
          cases hrest with
          | cons h2 hnil =>
            cases hnil
            have hv1 := hvals _ (List.mem_cons_self ..)
            have hv2 := hvals _ (List.mem_cons_of_mem _ (List.mem_cons_self ..))
            rcases canonical_chan h1 hv1 with ⟨cid, rfl, hcid, _⟩
            rcases hpool.chans_ty cid _ hcid with ⟨_, ch, hch, _⟩
            cases hcl : ch.closed
            · by_cases hroom : ch.cap = 0 ∨ ch.buf.length < ch.cap
              · exact Or.inr (Or.inr ⟨_, σ, _, .concPrimVal (.chanSendOpen hch hcl hroom hv2)⟩)
              · exact Or.inr (Or.inl (.chanSendWait hch hcl hroom hv2))
            · exact Or.inr (Or.inr ⟨_, σ, _, .concPrimVal (.chanSendClosed hch hcl hv2)⟩)
      | chanRecv optAdt =>
        cases hargs with
        | cons h1 hnil =>
          cases hnil
          rcases canonical_chan h1 (hvals _ (List.mem_cons_self ..)) with ⟨cid, rfl, hcid, _⟩
          rcases hpool.chans_ty cid _ hcid with ⟨_, ch, hch, _⟩
          cases hbuf : ch.buf with
          | cons v rest =>
            exact Or.inr (Or.inr ⟨_, σ, _, .concPrimVal (.chanRecvVal hch hbuf)⟩)
          | nil =>
            cases hcl : ch.closed
            · exact Or.inr (Or.inl (.chanRecvWait hch hbuf hcl))
            · exact Or.inr (Or.inr ⟨_, σ, _, .concPrimVal (.chanRecvClosed hch hbuf hcl)⟩)
      | chanClose =>
        cases hargs with
        | cons h1 hnil =>
          cases hnil
          rcases canonical_chan h1 (hvals _ (List.mem_cons_self ..)) with ⟨cid, rfl, hcid, _⟩
          rcases hpool.chans_ty cid _ hcid with ⟨_, ch, hch, _⟩
          exact Or.inr (Or.inr ⟨_, σ, _, .concPrimVal (.chanClose hch)⟩)
      | actorSpawn =>
        cases hargs with
        | cons _ hnil =>
          cases hnil
          exact Or.inr (Or.inr ⟨_, σ, _, .concPrimVal (.actorSpawn (hvals _ (List.mem_cons_self ..)))⟩)
      | actorCall _ =>
        cases hargs with
        | cons h1 hrest =>
          cases hrest with
          | cons _ hnil =>
            cases hnil
            have hv1 := hvals _ (List.mem_cons_self ..)
            have hv2 := hvals _ (List.mem_cons_of_mem _ (List.mem_cons_self ..))
            rcases canonical_actor h1 hv1 with ⟨aid, rfl, haid⟩
            rcases hpool.actors_ty aid _ haid with ⟨act, hact, _, _⟩
            exact Or.inr (Or.inr ⟨_, σ, _, .concPrimVal (.actorCall hact hv2)⟩)
      | actorSend =>
        cases hargs with
        | cons h1 hrest =>
          cases hrest with
          | cons _ hnil =>
            cases hnil
            have hv1 := hvals _ (List.mem_cons_self ..)
            have hv2 := hvals _ (List.mem_cons_of_mem _ (List.mem_cons_self ..))
            rcases canonical_actor h1 hv1 with ⟨aid, rfl, haid⟩
            rcases hpool.actors_ty aid _ haid with ⟨act, hact, _, _⟩
            exact Or.inr (Or.inr ⟨_, σ, _, .concPrimVal (.actorSend hact hv2)⟩)
    · exact Or.inr (Or.inr ⟨.trap t, σ, .none, .concPrimTrap htrap⟩)
    · exact Or.inr (Or.inl (.concPrimArgs hblk))
    · exact Or.inr (Or.inr ⟨_, σ', eff, .concPrimArgs hsargs⟩)
  | trap t _ => exact Or.inl (Or.inr ⟨t, rfl⟩)
termination_by sizeOf e

theorem progressList {Δ : AdtEnv} {Φ : FunEnv} {Ψ : StoreTy} {Θ : TaskTy}
    {pool : ConcPool} {σ : Store} {es : List Expr} {τs : List Ty}
    (hΦ : FunEnvTyped Δ Φ)
    (hts : HasTypes Δ Φ Ψ Θ emptyCtx es τs)
    (hσ : StoreTyped Δ Φ Ψ Θ σ)
    (hpool : PoolTyped Δ Φ Ψ Θ pool) :
    (∀ e ∈ es, IsValue e) ∨
    (∃ t, ListFirstTrap es t) ∨
    BlockedOnTaskList pool es ∨
    (∃ es' σ' eff, StepList Δ Φ pool es σ es' σ' eff) := by
  cases hts with
  | nil => exact Or.inl (fun _ h => by cases h)
  | cons h1 hrest =>
    rcases progress hΦ h1 hσ hpool with (hv1 | ⟨t, rfl⟩) | hblk1 | ⟨e1', σ', eff, hs1⟩
    · rcases progressList hΦ hrest hσ hpool with hvals | ⟨t, htrap⟩ | hblkr | ⟨es', σ', eff, hss⟩
      · exact Or.inl (fun u hu => by
          rcases List.mem_cons.mp hu with rfl | hu'
          · exact hv1
          · exact hvals u hu')
      · exact Or.inr (Or.inl ⟨t, .tail hv1 htrap⟩)
      · exact Or.inr (Or.inr (Or.inl (.tail hv1 hblkr)))
      · exact Or.inr (Or.inr (Or.inr ⟨_, σ', eff, .tail hv1 hss⟩))
    · exact Or.inr (Or.inl ⟨t, .head t _⟩)
    · exact Or.inr (Or.inr (Or.inl (.head hblk1)))
    · exact Or.inr (Or.inr (Or.inr ⟨_, σ', eff, .head hs1⟩))
termination_by sizeOf es
end

/-! ## Preservation Theorem (Subject Reduction) -/

/-- Characterization of concurrent pool typing evolution across a single `Step`. -/
def EffTyped (Δ : AdtEnv) (Φ : FunEnv) (Ψ' : StoreTy) (Θ Θ' : TaskTy) :
    ConcEff → Prop
  | .none => Θ' = Θ
  | .spawnTask body =>
    ∃ τsp, Θ' = { Θ with tasks := Θ.tasks ++ [τsp] } ∧
      IsSend Δ τsp ∧ HasType Δ Φ Ψ' Θ' emptyCtx body τsp
  | .allocMVar init =>
    ∃ τm, Θ' = { Θ with mvars := Θ.mvars ++ [τm] } ∧
      IsSend Δ τm ∧ (∀ v, init = some v → IsValue v ∧ HasType Δ Φ Ψ' Θ' emptyCtx v τm)
  | .takeMVar _ => Θ' = Θ
  | .putMVar mid val =>
    ∃ τm, Θ' = Θ ∧ Θ.mvars[mid]? = some τm ∧
      IsSend Δ τm ∧ IsValue val ∧ HasType Δ Φ Ψ' Θ' emptyCtx val τm
  | .allocChan _ =>
    ∃ τc, Θ' = { Θ with chans := Θ.chans ++ [τc] } ∧ IsSend Δ τc
  | .sendChan cid val =>
    ∃ τc, Θ' = Θ ∧ Θ.chans[cid]? = some τc ∧
      IsSend Δ τc ∧ IsValue val ∧ HasType Δ Φ Ψ' Θ' emptyCtx val τc
  | .recvChan _ => Θ' = Θ
  | .closeChan _ => Θ' = Θ
  | .spawnActor initExpr =>
    ∃ σ_ty, Θ' = { Θ with actors := Θ.actors ++ [σ_ty] } ∧
      HasType Δ Φ Ψ' Θ' emptyCtx initExpr σ_ty
  | .callActor aid handler =>
    ∃ σ_ty r_ty, Θ' = { Θ with tasks := Θ.tasks ++ [r_ty] } ∧
      Θ.actors[aid]? = some σ_ty ∧ IsSend Δ r_ty ∧ IsValue handler ∧
      HasType Δ Φ Ψ' Θ' emptyCtx handler (.fn .shared [σ_ty] r_ty)
  | .sendActor aid handler =>
    ∃ σ_ty, Θ' = Θ ∧ Θ.actors[aid]? = some σ_ty ∧ IsValue handler ∧
      HasType Δ Φ Ψ' Θ' emptyCtx handler (.fn .shared [σ_ty] .void)

theorem effTyped_extends {Δ : AdtEnv} {Φ : FunEnv} {Ψ' : StoreTy} {Θ Θ' : TaskTy}
    {eff : ConcEff} (heff : EffTyped Δ Φ Ψ' Θ Θ' eff) : TaskExtends Θ Θ' := by
  cases eff with
  | none => simp only [EffTyped] at heff; subst heff; exact TaskExtends.refl _
  | spawnTask _ => rcases heff with ⟨τsp, rfl, _, _⟩; exact TaskExtends.appendTask Θ τsp
  | allocMVar _ => rcases heff with ⟨τm, rfl, _, _⟩; exact TaskExtends.appendMVar Θ τm
  | takeMVar _ => simp only [EffTyped] at heff; subst heff; exact TaskExtends.refl _
  | putMVar _ _ => rcases heff with ⟨_, rfl, _, _, _, _⟩; exact TaskExtends.refl _
  | allocChan _ => rcases heff with ⟨τc, rfl, _⟩; exact TaskExtends.appendChan Θ τc
  | sendChan _ _ => rcases heff with ⟨_, rfl, _, _, _, _⟩; exact TaskExtends.refl _
  | recvChan _ => simp only [EffTyped] at heff; subst heff; exact TaskExtends.refl _
  | closeChan _ => simp only [EffTyped] at heff; subst heff; exact TaskExtends.refl _
  | spawnActor _ => rcases heff with ⟨σ_ty, rfl, _⟩; exact TaskExtends.appendActor Θ σ_ty
  | callActor _ _ => rcases heff with ⟨_, r_ty, rfl, _, _, _, _⟩; exact TaskExtends.appendTask Θ r_ty
  | sendActor _ _ => rcases heff with ⟨_, rfl, _, _, _⟩; exact TaskExtends.refl _

mutual
theorem preservation {Δ : AdtEnv} {Φ : FunEnv} (hΦ : FunEnvTyped Δ Φ)
    {Ψ : StoreTy} {Θ : TaskTy} {pool : ConcPool}
    {e : Expr} {σ : Store} {e' : Expr} {σ' : Store} {eff : ConcEff} {τ : Ty}
    (ht : HasType Δ Φ Ψ Θ emptyCtx e τ)
    (hstep : Step Δ Φ pool e σ e' σ' eff)
    (hσ : StoreTyped Δ Φ Ψ Θ σ)
    (hpool : PoolTyped Δ Φ Ψ Θ pool) :
    ∃ Ψ' Θ',
      StoreExtends Ψ Ψ' ∧
      EffTyped Δ Φ Ψ' Θ Θ' eff ∧
      HasType Δ Φ Ψ' Θ' emptyCtx e' τ ∧
      StoreTyped Δ Φ Ψ' Θ' σ' := by
  cases hstep with
  | tupleStep hs =>
    cases ht with
    | tuple hts =>
      rcases preservationList hΦ hts hs hσ hpool with ⟨Ψ', Θ', hext, heff, hts', hσ'⟩
      exact ⟨Ψ', Θ', hext, heff, .tuple hts', hσ'⟩
  | tupleTrap _ => exact ⟨Ψ, Θ, StoreExtends.refl Ψ, rfl, .trap _ τ, hσ⟩
  | blockEmpty =>
    cases ht
    exact ⟨Ψ, Θ, StoreExtends.refl Ψ, rfl, .lit .unit, hσ⟩
  | blockSingle =>
    cases ht with
    | blockSingle he => exact ⟨Ψ, Θ, StoreExtends.refl Ψ, rfl, he, hσ⟩
  | blockConsStep hs =>
    cases ht with
    | blockCons h1 h2 =>
      rcases preservation hΦ h1 hs hσ hpool with ⟨Ψ', Θ', hext, heff, h1', hσ'⟩
      exact ⟨Ψ', Θ', hext, heff,
        .blockCons h1' (typing_env_weaken hext (effTyped_extends heff) h2), hσ'⟩
  | blockConsVal _ =>
    cases ht with
    | blockCons _ h2 => exact ⟨Ψ, Θ, StoreExtends.refl Ψ, rfl, h2, hσ⟩
  | blockConsTrap => exact ⟨Ψ, Θ, StoreExtends.refl Ψ, rfl, .trap _ τ, hσ⟩
  | applyFn hs =>
    cases ht with
    | apply hfn hargs hr =>
      rcases preservation hΦ hfn hs hσ hpool with ⟨Ψ', Θ', hext, heff, hfn', hσ'⟩
      exact ⟨Ψ', Θ', hext, heff,
        .apply hfn' (typingList_env_weaken hext (effTyped_extends heff) hargs) hr, hσ'⟩
  | applyFnTrap => exact ⟨Ψ, Θ, StoreExtends.refl Ψ, rfl, .trap _ τ, hσ⟩
  | applyArgs _ hs =>
    cases ht with
    | apply hfn hargs hr =>
      rcases preservationList hΦ hargs hs hσ hpool with ⟨Ψ', Θ', hext, heff, hargs', hσ'⟩
      exact ⟨Ψ', Θ', hext, heff,
        .apply (typing_env_weaken hext (effTyped_extends heff) hfn) hargs' hr, hσ'⟩
  | applyArgsTrap _ _ => exact ⟨Ψ, Θ, StoreExtends.refl Ψ, rfl, .trap _ τ, hσ⟩
  | applyBeta hvals _ =>
    cases ht with
    | apply hfn hargs hr =>
      cases hfn with
      | lam _ hpsSub hrSub hbody _ =>
        have hargs' := typingList_sub hpsSub hargs
        have hmatch := zipParams_match hargs' hvals
        exact ⟨Ψ, Θ, StoreExtends.refl Ψ, rfl,
          typing_sub (TySub.trans hrSub hr) (substMany_typing hmatch hbody), hσ⟩
  | applyDirArgs hs =>
    cases ht with
    | applyDir hf hargs hr =>
      rcases preservationList hΦ hargs hs hσ hpool with ⟨Ψ', Θ', hext, heff, hargs', hσ'⟩
      exact ⟨Ψ', Θ', hext, heff, .applyDir hf hargs' hr, hσ'⟩
  | applyDirTrap _ => exact ⟨Ψ, Θ, StoreExtends.refl Ψ, rfl, .trap _ τ, hσ⟩
  | applyDirBeta hf' hvals _ =>
    cases ht with
    | applyDir hf hargs hr =>
      rw [hf] at hf'; cases hf'
      have hbody0 := hΦ _ _ hf
      have hbody := typing_env_weaken (ListExtends.empty Ψ) (TaskExtends.empty Θ) hbody0
      have hmatch := zipParams_match hargs hvals
      exact ⟨Ψ, Θ, StoreExtends.refl Ψ, rfl,
        typing_sub hr (substMany_typing hmatch hbody), hσ⟩
  | unStep hs =>
    cases ht with
    | un hop h1 =>
      rcases preservation hΦ h1 hs hσ hpool with ⟨Ψ', Θ', hext, heff, h1', hσ'⟩
      exact ⟨Ψ', Θ', hext, heff, .un hop h1', hσ'⟩
  | unTrap => exact ⟨Ψ, Θ, StoreExtends.refl Ψ, rfl, .trap _ τ, hσ⟩
  | unVal he =>
    cases ht with
    | un hop h1 =>
      cases h1 with
      | lit hl => exact ⟨Ψ, Θ, StoreExtends.refl Ψ, rfl, .lit (evalUnOp_sound hop hl he), hσ⟩
  | binLeft hs =>
    cases ht with
    | bin hop h1 h2 =>
      rcases preservation hΦ h1 hs hσ hpool with ⟨Ψ', Θ', hext, heff, h1', hσ'⟩
      exact ⟨Ψ', Θ', hext, heff,
        .bin hop h1' (typing_env_weaken hext (effTyped_extends heff) h2), hσ'⟩
  | binLeftTrap => exact ⟨Ψ, Θ, StoreExtends.refl Ψ, rfl, .trap _ τ, hσ⟩
  | binAndFalse =>
    cases ht with
    | bin hop _ _ => cases hop; exact ⟨Ψ, Θ, StoreExtends.refl Ψ, rfl, .lit (.bool false), hσ⟩
  | binAndTrue =>
    cases ht with
    | bin hop _ h2 => cases hop; exact ⟨Ψ, Θ, StoreExtends.refl Ψ, rfl, h2, hσ⟩
  | binOrTrue =>
    cases ht with
    | bin hop _ _ => cases hop; exact ⟨Ψ, Θ, StoreExtends.refl Ψ, rfl, .lit (.bool true), hσ⟩
  | binOrFalse =>
    cases ht with
    | bin hop _ h2 => cases hop; exact ⟨Ψ, Θ, StoreExtends.refl Ψ, rfl, h2, hσ⟩
  | binRight _ _ _ hs =>
    cases ht with
    | bin hop h1 h2 =>
      rcases preservation hΦ h2 hs hσ hpool with ⟨Ψ', Θ', hext, heff, h2', hσ'⟩
      exact ⟨Ψ', Θ', hext, heff,
        .bin hop (typing_env_weaken hext (effTyped_extends heff) h1) h2', hσ'⟩
  | binRightTrap _ _ _ => exact ⟨Ψ, Θ, StoreExtends.refl Ψ, rfl, .trap _ τ, hσ⟩
  | binVal he =>
    cases ht with
    | bin hop h1 h2 =>
      cases h1 with
      | lit hl1 =>
        cases h2 with
        | lit hl2 =>
          exact ⟨Ψ, Θ, StoreExtends.refl Ψ, rfl, .lit (evalBinOp_sound hop hl1 hl2 he), hσ⟩
  | binTrap _ => exact ⟨Ψ, Θ, StoreExtends.refl Ψ, rfl, .trap _ τ, hσ⟩
  | letStep hs =>
    cases ht with
    | let_ h1 h2 =>
      rcases preservation hΦ h1 hs hσ hpool with ⟨Ψ', Θ', hext, heff, h1', hσ'⟩
      exact ⟨Ψ', Θ', hext, heff,
        .let_ h1' (typing_env_weaken hext (effTyped_extends heff) h2), hσ'⟩
  | letTrap => exact ⟨Ψ, Θ, StoreExtends.refl Ψ, rfl, .trap _ τ, hσ⟩
  | letVal hv1 =>
    cases ht with
    | let_ h1 h2 =>
      exact ⟨Ψ, Θ, StoreExtends.refl Ψ, rfl, subst_typing h2 hv1 h1, hσ⟩
  | ifStep hs =>
    cases ht with
    | if_ hc h1 h2 =>
      rcases preservation hΦ hc hs hσ hpool with ⟨Ψ', Θ', hext, heff, hc', hσ'⟩
      have htk := effTyped_extends heff
      exact ⟨Ψ', Θ', hext, heff,
        .if_ hc' (typing_env_weaken hext htk h1) (typing_env_weaken hext htk h2), hσ'⟩
  | ifTrap => exact ⟨Ψ, Θ, StoreExtends.refl Ψ, rfl, .trap _ τ, hσ⟩
  | ifTrue =>
    cases ht with
    | if_ _ h1 _ => exact ⟨Ψ, Θ, StoreExtends.refl Ψ, rfl, h1, hσ⟩
  | ifFalse =>
    cases ht with
    | if_ _ _ h2 => exact ⟨Ψ, Θ, StoreExtends.refl Ψ, rfl, h2, hσ⟩
  | whileUnfold =>
    cases ht with
    | while_ hc hb =>
      exact ⟨Ψ, Θ, StoreExtends.refl Ψ, rfl,
        .if_ hc (.blockCons hb (.blockSingle (.while_ hc hb))) (.lit .unit), hσ⟩
  | matchScrut hs =>
    cases ht with
    | match_ hscr harms =>
      rcases preservation hΦ hscr hs hσ hpool with ⟨Ψ', Θ', hext, heff, hscr', hσ'⟩
      exact ⟨Ψ', Θ', hext, heff,
        .match_ hscr' (typingArms_env_weaken hext (effTyped_extends heff) harms), hσ'⟩
  | matchScrutTrap => exact ⟨Ψ, Θ, StoreExtends.refl Ψ, rfl, .trap _ τ, hσ⟩
  | matchEmpty _ => exact ⟨Ψ, Θ, StoreExtends.refl Ψ, rfl, .trap .matchFailure τ, hσ⟩
  | matchHit hv hm =>
    cases ht with
    | match_ hs harms =>
      cases harms with
      | cons hp hbody _ =>
        have hmatch := matchPat_sound hp hs hv hm
        exact ⟨Ψ, Θ, StoreExtends.refl Ψ, rfl, substMany_typing hmatch hbody, hσ⟩
  | matchMiss _ _ =>
    cases ht with
    | match_ hs harms =>
      cases harms with
      | cons _ _ hrest => exact ⟨Ψ, Θ, StoreExtends.refl Ψ, rfl, .match_ hs hrest, hσ⟩
  | makeDataStep hs =>
    cases ht with
    | makeData hlv hts =>
      rcases preservationList hΦ hts hs hσ hpool with ⟨Ψ', Θ', hext, heff, hts', hσ'⟩
      exact ⟨Ψ', Θ', hext, heff, .makeData hlv hts', hσ'⟩
  | makeDataTrap _ => exact ⟨Ψ, Θ, StoreExtends.refl Ψ, rfl, .trap _ τ, hσ⟩
  | getTagStep hs =>
    cases ht with
    | getTag he =>
      rcases preservation hΦ he hs hσ hpool with ⟨Ψ', Θ', hext, heff, he', hσ'⟩
      exact ⟨Ψ', Θ', hext, heff, .getTag he', hσ'⟩
  | getTagTrap => exact ⟨Ψ, Θ, StoreExtends.refl Ψ, rfl, .trap _ τ, hσ⟩
  | getTagVal _ =>
    cases ht with
    | getTag _ => exact ⟨Ψ, Θ, StoreExtends.refl Ψ, rfl, .lit (.int _), hσ⟩
  | cellNewStep hs =>
    cases ht with
    | cellNew he =>
      rcases preservation hΦ he hs hσ hpool with ⟨Ψ', Θ', hext, heff, he', hσ'⟩
      exact ⟨Ψ', Θ', hext, heff, .cellNew he', hσ'⟩
  | cellNewTrap => exact ⟨Ψ, Θ, StoreExtends.refl Ψ, rfl, .trap _ τ, hσ⟩
  | cellNewVal hv =>
    cases ht with
    | @cellNew _ _ τ0 he =>
      have hext : StoreExtends Ψ (Ψ ++ [τ0]) := StoreExtends.append Ψ τ0
      have hloc : (Ψ ++ [τ0])[σ.length]? = some τ0 := by rw [hσ.1]; simp
      exact ⟨Ψ ++ [τ0], Θ, hext, rfl, .loc hloc, store_typed_alloc hσ hv he⟩
  | cellGetStep hs =>
    cases ht with
    | cellGet he hsub =>
      rcases preservation hΦ he hs hσ hpool with ⟨Ψ', Θ', hext, heff, he', hσ'⟩
      exact ⟨Ψ', Θ', hext, heff, .cellGet he' hsub, hσ'⟩
  | cellGetTrap => exact ⟨Ψ, Θ, StoreExtends.refl Ψ, rfl, .trap _ τ, hσ⟩
  | cellGetVal hvσ =>
    cases ht with
    | cellGet hloc hsub =>
      cases hloc with
      | loc hl =>
        rcases hσ.2 _ _ hl with ⟨v', hv', _, hvt⟩
        rw [hvσ] at hv'; cases hv'
        exact ⟨Ψ, Θ, StoreExtends.refl Ψ, rfl, typing_sub hsub hvt, hσ⟩
  | cellSetLeft hs =>
    cases ht with
    | cellSet h1 h2 =>
      rcases preservation hΦ h1 hs hσ hpool with ⟨Ψ', Θ', hext, heff, h1', hσ'⟩
      exact ⟨Ψ', Θ', hext, heff,
        .cellSet h1' (typing_env_weaken hext (effTyped_extends heff) h2), hσ'⟩
  | cellSetLeftTrap => exact ⟨Ψ, Θ, StoreExtends.refl Ψ, rfl, .trap _ τ, hσ⟩
  | cellSetRight _ hs =>
    cases ht with
    | cellSet h1 h2 =>
      rcases preservation hΦ h2 hs hσ hpool with ⟨Ψ', Θ', hext, heff, h2', hσ'⟩
      exact ⟨Ψ', Θ', hext, heff,
        .cellSet (typing_env_weaken hext (effTyped_extends heff) h1) h2', hσ'⟩
  | cellSetRightTrap _ => exact ⟨Ψ, Θ, StoreExtends.refl Ψ, rfl, .trap _ τ, hσ⟩
  | cellSetVal _ hv =>
    cases ht with
    | cellSet h1 h2 =>
      cases h1 with
      | loc hl =>
        exact ⟨Ψ, Θ, StoreExtends.refl Ψ, rfl, .lit .unit, store_typed_update hσ hl hv h2⟩
  | spawnStep hs =>
    cases ht with
    | spawn hfn hsend hsub =>
      rcases preservation hΦ hfn hs hσ hpool with ⟨Ψ', Θ', hext, heff, hfn', hσ'⟩
      exact ⟨Ψ', Θ', hext, heff, .spawn hfn' hsend hsub, hσ'⟩
  | spawnTrap => exact ⟨Ψ, Θ, StoreExtends.refl Ψ, rfl, .trap _ τ, hσ⟩
  | spawnBeta =>
    cases ht with
    | @spawn _ _ τ0 _ hfn hsend hsub =>
      cases hfn with
      | lam _ _ hrSub hbody _ =>
        let Θ' : TaskTy := { Θ with tasks := Θ.tasks ++ [τ0] }
        have hbodyτ : HasType Δ Φ Ψ Θ emptyCtx _ τ0 := typing_sub hrSub hbody
        have htkExt : TaskExtends Θ Θ' := TaskExtends.appendTask Θ τ0
        have hbody' : HasType Δ Φ Ψ Θ' emptyCtx _ τ0 :=
          typing_env_weaken (StoreExtends.refl Ψ) htkExt hbodyτ
        have htid : Θ'.tasks[pool.tasks.length]? = some τ0 := by
          simp [Θ', hpool.tasks_len]
        exact ⟨Ψ, Θ', StoreExtends.refl Ψ,
          ⟨τ0, rfl, hsend, hbody'⟩,
          .taskRef htid hsend hsub,
          store_typed_task_weaken htkExt hσ⟩
  | awaitStep hs =>
    cases ht with
    | await he hsend hsub =>
      rcases preservation hΦ he hs hσ hpool with ⟨Ψ', Θ', hext, heff, he', hσ'⟩
      exact ⟨Ψ', Θ', hext, heff, .await he' hsend hsub, hσ'⟩
  | awaitTrap => exact ⟨Ψ, Θ, StoreExtends.refl Ψ, rfl, .trap _ τ, hσ⟩
  | awaitVal het _ =>
    cases ht with
    | await href _ hsub =>
      cases href with
      | taskRef htid _ hs0 =>
        rcases hpool.tasks_ty _ _ htid with ⟨_, te, hte, hrun⟩
        rw [het] at hte; cases hte
        exact ⟨Ψ, Θ, StoreExtends.refl Ψ, rfl,
          typing_sub (TySub.trans hs0 hsub) (hrun _ rfl), hσ⟩
  | awaitTaskTrap _ =>
    exact ⟨Ψ, Θ, StoreExtends.refl Ψ, rfl, .trap _ τ, hσ⟩
  | concPrimArgs hs =>
    cases ht with
    | concPrim hop hargs hr =>
      rcases preservationList hΦ hargs hs hσ hpool with ⟨Ψ', Θ', hext, heff, hargs', hσ'⟩
      exact ⟨Ψ', Θ', hext, heff, .concPrim hop hargs' hr, hσ'⟩
  | concPrimTrap _ =>
    exact ⟨Ψ, Θ, StoreExtends.refl Ψ, rfl, .trap _ τ, hσ⟩
  | concPrimVal hprim =>
    cases ht with
    | concPrim hop hargs hr =>
      cases hprim with
      | mvarNew hv =>
        cases hop with
        | @mvarNew τm hsend =>
          cases hargs with
          | cons hvTy hnil =>
            cases hnil
            let Θ' : TaskTy := { Θ with mvars := Θ.mvars ++ [τm] }
            have htkExt : TaskExtends Θ Θ' := TaskExtends.appendMVar Θ τm
            have hm : Θ'.mvars[pool.mvars.length]? = some τm := by
              simp [Θ', hpool.mvars_len]
            exact ⟨Ψ, Θ', StoreExtends.refl Ψ,
              ⟨τm, rfl, hsend, fun u hu => by
                cases hu
                exact ⟨hv, typing_env_weaken (StoreExtends.refl Ψ) htkExt hvTy⟩⟩,
              typing_sub hr (.syncRef (.mvar hm hsend)),
              store_typed_task_weaken htkExt hσ⟩
      | mvarEmpty τm =>
        cases hop with
        | mvarEmpty hsend =>
          let Θ' : TaskTy := { Θ with mvars := Θ.mvars ++ [τm] }
          have htkExt : TaskExtends Θ Θ' := TaskExtends.appendMVar Θ τm
          have hm : Θ'.mvars[pool.mvars.length]? = some τm := by
            simp [Θ', hpool.mvars_len]
          exact ⟨Ψ, Θ', StoreExtends.refl Ψ,
            ⟨τm, rfl, hsend, fun _ hu => nomatch hu⟩,
            typing_sub hr (.syncRef (.mvar hm hsend)),
            store_typed_task_weaken htkExt hσ⟩
      | mvarTake hslot =>
        cases hop with
        | mvarTake _ =>
          cases hargs with
          | cons href hnil =>
            cases hnil
            cases href with
            | syncRef hsr =>
              cases hsr with
              | mvar hmid _ =>
                rcases hpool.mvars_ty _ _ hmid with ⟨_, slot, hslot', hval⟩
                rw [hslot] at hslot'; cases hslot'
                exact ⟨Ψ, Θ, StoreExtends.refl Ψ, rfl, typing_sub hr (hval _ rfl).2, hσ⟩
      | mvarPut _ hv =>
        cases hop with
        | @mvarPut τm hsend =>
          cases hargs with
          | cons href hrest =>
            cases hrest with
            | cons hvTy hnil =>
              cases hnil
              cases href with
              | syncRef hsr =>
                cases hsr with
                | mvar hmid _ =>
                  exact ⟨Ψ, Θ, StoreExtends.refl Ψ,
                    ⟨τm, rfl, hmid, hsend, hv, hvTy⟩,
                    typing_sub hr (.lit .unit), hσ⟩
      | chanNew τc _ =>
        cases hop with
        | chanNew hsend =>
          let Θ' : TaskTy := { Θ with chans := Θ.chans ++ [τc] }
          have htkExt : TaskExtends Θ Θ' := TaskExtends.appendChan Θ τc
          have hc : Θ'.chans[pool.chans.length]? = some τc := by
            simp [Θ', hpool.chans_len]
          exact ⟨Ψ, Θ', StoreExtends.refl Ψ,
            ⟨τc, rfl, hsend⟩,
            typing_sub hr (.syncRef (.chan hc hsend)),
            store_typed_task_weaken htkExt hσ⟩
      | chanSendClosed _ _ _ =>
        cases hop
        exact ⟨Ψ, Θ, StoreExtends.refl Ψ, rfl, typing_sub hr (.lit (.bool false)), hσ⟩
      | chanSendOpen _ _ _ hv =>
        cases hop with
        | @chanSend τc hsend =>
          cases hargs with
          | cons href hrest =>
            cases hrest with
            | cons hvTy hnil =>
              cases hnil
              cases href with
              | syncRef hsr =>
                cases hsr with
                | chan hcid _ =>
                  exact ⟨Ψ, Θ, StoreExtends.refl Ψ,
                    ⟨τc, rfl, hcid, hsend, hv, hvTy⟩,
                    typing_sub hr (.lit (.bool true)), hσ⟩
      | chanRecvVal hch hbuf =>
        cases hop with
        | chanRecv _ _ hlv1 =>
          cases hargs with
          | cons href hnil =>
            cases hnil
            cases href with
            | syncRef hsr =>
              cases hsr with
              | chan hcid _ =>
                rcases hpool.chans_ty _ _ hcid with ⟨_, ch', hch', hbufTy⟩
                rw [hch] at hch'; cases hch'
                have hvTy := (hbufTy _ (by rw [hbuf]; exact List.mem_cons_self ..)).2
                exact ⟨Ψ, Θ, StoreExtends.refl Ψ, rfl,
                  typing_sub hr (.makeData hlv1 (.cons hvTy .nil)), hσ⟩
      | chanRecvClosed _ _ _ =>
        cases hop with
        | chanRecv _ hlv0 _ =>
          exact ⟨Ψ, Θ, StoreExtends.refl Ψ, rfl,
            typing_sub hr (.makeData hlv0 .nil), hσ⟩
      | chanClose _ =>
        cases hop
        exact ⟨Ψ, Θ, StoreExtends.refl Ψ, rfl, typing_sub hr (.lit .unit), hσ⟩
      | actorSpawn _ =>
        cases hop with
        | @actorSpawn σ_ty =>
          cases hargs with
          | cons hfn hnil =>
            cases hnil
            let Θ' : TaskTy := { Θ with actors := Θ.actors ++ [σ_ty] }
            have htkExt : TaskExtends Θ Θ' := TaskExtends.appendActor Θ σ_ty
            have ha : Θ'.actors[pool.actors.length]? = some σ_ty := by
              simp [Θ', hpool.actors_len]
            have hinit : HasType Δ Φ Ψ Θ' emptyCtx (.apply _ []) σ_ty :=
              .apply (typing_env_weaken (StoreExtends.refl Ψ) htkExt hfn) .nil (TySub.refl _)
            exact ⟨Ψ, Θ', StoreExtends.refl Ψ,
              ⟨σ_ty, rfl, hinit⟩,
              typing_sub hr (.syncRef (.actor ha)),
              store_typed_task_weaken htkExt hσ⟩
      | actorCall _ hv =>
        cases hop with
        | @actorCall σ_ty r_ty hsend =>
          cases hargs with
          | cons href hrest =>
            cases hrest with
            | cons hfn hnil =>
              cases hnil
              cases href with
              | syncRef hsr =>
                cases hsr with
                | actor haid =>
                  let Θ' : TaskTy := { Θ with tasks := Θ.tasks ++ [r_ty] }
                  have htkExt : TaskExtends Θ Θ' := TaskExtends.appendTask Θ r_ty
                  have htid : Θ'.tasks[pool.tasks.length]? = some r_ty := by
                    simp [Θ', hpool.tasks_len]
                  exact ⟨Ψ, Θ', StoreExtends.refl Ψ,
                    ⟨σ_ty, r_ty, rfl, haid, hsend, hv,
                      typing_env_weaken (StoreExtends.refl Ψ) htkExt hfn⟩,
                    typing_sub hr (.taskRef htid hsend (TySub.refl _)),
                    store_typed_task_weaken htkExt hσ⟩
      | actorSend _ hv =>
        cases hop with
        | @actorSend σ_ty =>
          cases hargs with
          | cons href hrest =>
            cases hrest with
            | cons hfn hnil =>
              cases hnil
              cases href with
              | syncRef hsr =>
                cases hsr with
                | actor haid =>
                  exact ⟨Ψ, Θ, StoreExtends.refl Ψ,
                    ⟨σ_ty, rfl, haid, hv, hfn⟩,
                    typing_sub hr (.lit .unit), hσ⟩
termination_by sizeOf e

theorem preservationList {Δ : AdtEnv} {Φ : FunEnv} (hΦ : FunEnvTyped Δ Φ)
    {Ψ : StoreTy} {Θ : TaskTy} {pool : ConcPool}
    {es : List Expr} {σ : Store} {es' : List Expr} {σ' : Store} {eff : ConcEff} {τs : List Ty}
    (hts : HasTypes Δ Φ Ψ Θ emptyCtx es τs)
    (hstep : StepList Δ Φ pool es σ es' σ' eff)
    (hσ : StoreTyped Δ Φ Ψ Θ σ)
    (hpool : PoolTyped Δ Φ Ψ Θ pool) :
    ∃ Ψ' Θ',
      StoreExtends Ψ Ψ' ∧
      EffTyped Δ Φ Ψ' Θ Θ' eff ∧
      HasTypes Δ Φ Ψ' Θ' emptyCtx es' τs ∧
      StoreTyped Δ Φ Ψ' Θ' σ' := by
  cases hstep with
  | head hs =>
    cases hts with
    | cons h1 hrest =>
      rcases preservation hΦ h1 hs hσ hpool with ⟨Ψ', Θ', hext, heff, h1', hσ'⟩
      exact ⟨Ψ', Θ', hext, heff,
        .cons h1' (typingList_env_weaken hext (effTyped_extends heff) hrest), hσ'⟩
  | tail _ hs =>
    cases hts with
    | cons h1 hrest =>
      rcases preservationList hΦ hrest hs hσ hpool with ⟨Ψ', Θ', hext, heff, hrest', hσ'⟩
      exact ⟨Ψ', Θ', hext, heff,
        .cons (typing_env_weaken hext (effTyped_extends heff) h1) hrest', hσ'⟩
termination_by sizeOf es
end

/-! ## Sequential Multi-Step Type Safety Corollary -/

theorem emptyPool_typed {Δ : AdtEnv} {Φ : FunEnv} {Ψ : StoreTy} :
    PoolTyped Δ Φ Ψ emptyTaskTy emptyPool :=
  { tasks_len  := rfl
    tasks_ty   := fun _ _ h => by simp [emptyTaskTy] at h
    mvars_len  := rfl
    mvars_ty   := fun _ _ h => by simp [emptyTaskTy] at h
    chans_len  := rfl
    chans_ty   := fun _ _ h => by simp [emptyTaskTy] at h
    actors_len := rfl
    actors_ty  := fun _ _ h => by simp [emptyTaskTy] at h }

theorem type_safety {Δ : AdtEnv} {Φ : FunEnv} {Ψ : StoreTy} {σ σ' : Store} {e e' : Expr} {τ : Ty}
    (hΦ : FunEnvTyped Δ Φ)
    (ht : HasType Δ Φ Ψ emptyTaskTy emptyCtx e τ)
    (hσ : StoreTyped Δ Φ Ψ emptyTaskTy σ)
    (hsteps : Steps Δ Φ e σ e' σ') :
    ¬ IsStuck Δ Φ emptyPool e' σ' := by
  induction hsteps generalizing Ψ with
  | refl =>
    intro ⟨hnt, hnblk, hns⟩
    rcases progress hΦ ht hσ emptyPool_typed with ht' | hblk | hs'
    · exact hnt ht'
    · exact hnblk hblk
    · exact hns hs'
  | trans hstep _ ih =>
    rcases preservation hΦ ht hstep hσ emptyPool_typed with ⟨Ψ', Θ', _, heff, ht', hσ'⟩
    simp only [EffTyped] at heff
    subst heff
    exact ih ht' hσ'

end CoreGeisha
