import CoreGeisha.Syntax
import CoreGeisha.Typing
import CoreGeisha.Semantics

/-!
# Core Geisha: Type Soundness (Progress + Preservation)

Machine-checked proof (zero `sorry`, zero external dependencies beyond Lean 4
core) that every well-typed closed Core Geisha expression never gets stuck (no
undefined behavior): evaluation either terminates in a value, raises a defined
runtime trap (`divByZero` / `matchFailure`), or takes a type- and
store-preserving step.
-/

namespace CoreGeisha

/-! ## Store & Context Auxiliary Lemmas -/

theorem StoreExtends.refl (Ψ : StoreTy) : StoreExtends Ψ Ψ :=
  ⟨Nat.le_refl _, fun _ _ h => h⟩

theorem StoreExtends.trans {Ψ1 Ψ2 Ψ3 : StoreTy}
    (h12 : StoreExtends Ψ1 Ψ2) (h23 : StoreExtends Ψ2 Ψ3) : StoreExtends Ψ1 Ψ3 :=
  ⟨Nat.le_trans h12.1 h23.1, fun l τ h => h23.2 l τ (h12.2 l τ h)⟩

theorem lt_length_of_getElem?_eq_some {α : Type} {xs : List α} {l : Nat} {a : α}
    (h : xs[l]? = some a) : l < xs.length := by
  cases Nat.lt_or_ge l xs.length with
  | inl hlt => exact hlt
  | inr hge =>
    rw [List.getElem?_eq_none hge] at h
    cases h

theorem StoreExtends.append (Ψ : StoreTy) (τ : Ty) : StoreExtends Ψ (Ψ ++ [τ]) := by
  refine ⟨by simp, fun l t h => ?_⟩
  have hlt : l < Ψ.length := lt_length_of_getElem?_eq_some h
  rw [List.getElem?_append_left hlt]
  exact h

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

/-! ## Context & Store Weakening -/

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
theorem typing_ctx_weaken {Δ : AdtEnv} {Φ : FunEnv} {Ψ : StoreTy} {Γ1 Γ2 : Ctx} {e : Expr} {τ : Ty}
    (hsub : ∀ x t, Γ1 x = some t → Γ2 x = some t)
    (h : HasType Δ Φ Ψ Γ1 e τ) : HasType Δ Φ Ψ Γ2 e τ := by
  cases h with
  | lit hl => exact .lit hl
  | var hx => exact .var (hsub _ _ hx)
  | loc hl => exact .loc hl
  | tuple hts => exact .tuple (typingList_ctx_weaken hsub hts)
  | blockEmpty => exact .blockEmpty
  | blockSingle he => exact .blockSingle (typing_ctx_weaken hsub he)
  | blockCons h1 h2 => exact .blockCons (typing_ctx_weaken hsub h1) (typing_ctx_weaken hsub h2)
  | lam hbody => exact .lam (typing_ctx_weaken (extMany_mono hsub _) hbody)
  | apply hfn hargs => exact .apply (typing_ctx_weaken hsub hfn) (typingList_ctx_weaken hsub hargs)
  | applyDir hf hargs => exact .applyDir hf (typingList_ctx_weaken hsub hargs)
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
  | cellGet he => exact .cellGet (typing_ctx_weaken hsub he)
  | cellSet h1 h2 => exact .cellSet (typing_ctx_weaken hsub h1) (typing_ctx_weaken hsub h2)
  | trap t τ => exact .trap t τ

theorem typingList_ctx_weaken {Δ : AdtEnv} {Φ : FunEnv} {Ψ : StoreTy} {Γ1 Γ2 : Ctx}
    {es : List Expr} {τs : List Ty}
    (hsub : ∀ x t, Γ1 x = some t → Γ2 x = some t)
    (h : HasTypes Δ Φ Ψ Γ1 es τs) : HasTypes Δ Φ Ψ Γ2 es τs := by
  cases h with
  | nil => exact .nil
  | cons h1 hrest => exact .cons (typing_ctx_weaken hsub h1) (typingList_ctx_weaken hsub hrest)

theorem typingArms_ctx_weaken {Δ : AdtEnv} {Φ : FunEnv} {Ψ : StoreTy} {Γ1 Γ2 : Ctx}
    {τs τr : Ty} {arms : List (Pat × Expr)}
    (hsub : ∀ x t, Γ1 x = some t → Γ2 x = some t)
    (h : ArmsHaveType Δ Φ Ψ Γ1 τs arms τr) : ArmsHaveType Δ Φ Ψ Γ2 τs arms τr := by
  cases h with
  | nil => exact .nil
  | cons hp hb hrest =>
    exact .cons hp (typing_ctx_weaken (extMany_mono hsub _) hb) (typingArms_ctx_weaken hsub hrest)
end

theorem typing_closed_weaken {Δ : AdtEnv} {Φ : FunEnv} {Ψ : StoreTy} {Γ : Ctx} {v : Expr} {τ : Ty}
    (h : HasType Δ Φ Ψ emptyCtx v τ) : HasType Δ Φ Ψ Γ v τ :=
  typing_ctx_weaken (fun _ _ hx => by simp [emptyCtx] at hx) h

mutual
theorem typing_store_weaken {Δ : AdtEnv} {Φ : FunEnv} {Ψ Ψ' : StoreTy} {Γ : Ctx} {e : Expr} {τ : Ty}
    (hext : StoreExtends Ψ Ψ') (h : HasType Δ Φ Ψ Γ e τ) : HasType Δ Φ Ψ' Γ e τ := by
  cases h with
  | lit hl => exact .lit hl
  | var hx => exact .var hx
  | loc hl => exact .loc (hext.2 _ _ hl)
  | tuple hts => exact .tuple (typingList_store_weaken hext hts)
  | blockEmpty => exact .blockEmpty
  | blockSingle he => exact .blockSingle (typing_store_weaken hext he)
  | blockCons h1 h2 => exact .blockCons (typing_store_weaken hext h1) (typing_store_weaken hext h2)
  | lam hbody => exact .lam (typing_store_weaken hext hbody)
  | apply hfn hargs => exact .apply (typing_store_weaken hext hfn) (typingList_store_weaken hext hargs)
  | applyDir hf hargs => exact .applyDir hf (typingList_store_weaken hext hargs)
  | bin hop h1 h2 => exact .bin hop (typing_store_weaken hext h1) (typing_store_weaken hext h2)
  | un hop h1 => exact .un hop (typing_store_weaken hext h1)
  | let_ h1 h2 => exact .let_ (typing_store_weaken hext h1) (typing_store_weaken hext h2)
  | if_ hc h1 h2 =>
    exact .if_ (typing_store_weaken hext hc) (typing_store_weaken hext h1) (typing_store_weaken hext h2)
  | while_ hc hb => exact .while_ (typing_store_weaken hext hc) (typing_store_weaken hext hb)
  | match_ hs harms => exact .match_ (typing_store_weaken hext hs) (typingArms_store_weaken hext harms)
  | makeData hv hts => exact .makeData hv (typingList_store_weaken hext hts)
  | getTag he => exact .getTag (typing_store_weaken hext he)
  | cellNew he => exact .cellNew (typing_store_weaken hext he)
  | cellGet he => exact .cellGet (typing_store_weaken hext he)
  | cellSet h1 h2 => exact .cellSet (typing_store_weaken hext h1) (typing_store_weaken hext h2)
  | trap t τ => exact .trap t τ

theorem typingList_store_weaken {Δ : AdtEnv} {Φ : FunEnv} {Ψ Ψ' : StoreTy} {Γ : Ctx}
    {es : List Expr} {τs : List Ty}
    (hext : StoreExtends Ψ Ψ') (h : HasTypes Δ Φ Ψ Γ es τs) : HasTypes Δ Φ Ψ' Γ es τs := by
  cases h with
  | nil => exact .nil
  | cons h1 hrest => exact .cons (typing_store_weaken hext h1) (typingList_store_weaken hext hrest)

theorem typingArms_store_weaken {Δ : AdtEnv} {Φ : FunEnv} {Ψ Ψ' : StoreTy} {Γ : Ctx}
    {τs τr : Ty} {arms : List (Pat × Expr)}
    (hext : StoreExtends Ψ Ψ') (h : ArmsHaveType Δ Φ Ψ Γ τs arms τr) :
    ArmsHaveType Δ Φ Ψ' Γ τs arms τr := by
  cases h with
  | nil => exact .nil
  | cons hp hb hrest =>
    exact .cons hp (typing_store_weaken hext hb) (typingArms_store_weaken hext hrest)
end

/-! ## Substitution & Pattern-Matching Typing Lemmas -/

mutual
theorem subst_typing {Δ : AdtEnv} {Φ : FunEnv} {Ψ : StoreTy} {Γ : Ctx}
    {x : Ident} {v e : Expr} {τx τ : Ty}
    (he : HasType Δ Φ Ψ (extendCtx Γ x τx) e τ)
    (hv : HasType Δ Φ Ψ emptyCtx v τx) :
    HasType Δ Φ Ψ Γ (subst x v e) τ := by
  cases he with
  | lit hl => exact .lit hl
  | @var _ y _ hy =>
    simp only [subst, extendCtx] at hy ⊢
    by_cases hyx : (y == x) = true
    · rw [hyx] at hy ⊢
      simp only [↓reduceIte, Option.some.injEq] at hy
      subst hy
      exact typing_closed_weaken hv
    · have hyx' : (y == x) = false := Bool.eq_false_iff.mpr hyx
      rw [hyx'] at hy ⊢
      simp only [Bool.false_eq_true, ↓reduceIte] at hy ⊢
      exact .var hy
  | loc hl => exact .loc hl
  | tuple hts => exact .tuple (substList_typing hts hv)
  | blockEmpty => exact .blockEmpty
  | blockSingle h1 => exact .blockSingle (subst_typing h1 hv)
  | blockCons h1 h2 => exact .blockCons (subst_typing h1 hv) (subst_typing h2 hv)
  | @lam _ ps ret body hbody =>
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
      exact .lam hbody
    · simp only [hany]
      have hnot : x ∉ ps.map Prod.fst := by
        intro hmem
        apply hany
        rw [List.any_eq_true]
        rcases List.mem_map.mp hmem with ⟨p, hp, rfl⟩
        exact ⟨p, hp, beq_self_eq_true _⟩
      rw [extendMany_comm Γ x τx ps hnot] at hbody
      exact .lam (subst_typing hbody hv)
  | apply hfn hargs => exact .apply (subst_typing hfn hv) (substList_typing hargs hv)
  | applyDir hf hargs => exact .applyDir hf (substList_typing hargs hv)
  | bin hop h1 h2 => exact .bin hop (subst_typing h1 hv) (subst_typing h2 hv)
  | un hop h1 => exact .un hop (subst_typing h1 hv)
  | @let_ _ y e1 e2 τ1 τ2 h1 h2 =>
    simp only [subst]
    by_cases hyx : (y == x) = true
    · simp only [hyx, ↓reduceIte]
      have heq : y = x := beq_iff_eq.mp hyx
      subst heq
      rw [extendCtx_shadow] at h2
      exact .let_ (subst_typing h1 hv) h2
    · simp only [hyx]
      have hne : x ≠ y := fun h => hyx (beq_iff_eq.mpr h.symm)
      rw [extendCtx_comm Γ hne τx τ1] at h2
      exact .let_ (subst_typing h1 hv) (subst_typing h2 hv)
  | if_ hc h1 h2 => exact .if_ (subst_typing hc hv) (subst_typing h1 hv) (subst_typing h2 hv)
  | while_ hc hb => exact .while_ (subst_typing hc hv) (subst_typing hb hv)
  | match_ hs harms => exact .match_ (subst_typing hs hv) (substArms_typing harms hv)
  | makeData hlv hts => exact .makeData hlv (substList_typing hts hv)
  | getTag h1 => exact .getTag (subst_typing h1 hv)
  | cellNew h1 => exact .cellNew (subst_typing h1 hv)
  | cellGet h1 => exact .cellGet (subst_typing h1 hv)
  | cellSet h1 h2 => exact .cellSet (subst_typing h1 hv) (subst_typing h2 hv)
  | trap t τ => exact .trap t τ

theorem substList_typing {Δ : AdtEnv} {Φ : FunEnv} {Ψ : StoreTy} {Γ : Ctx}
    {x : Ident} {v : Expr} {es : List Expr} {τx : Ty} {τs : List Ty}
    (hes : HasTypes Δ Φ Ψ (extendCtx Γ x τx) es τs)
    (hv : HasType Δ Φ Ψ emptyCtx v τx) :
    HasTypes Δ Φ Ψ Γ (substList x v es) τs := by
  cases hes with
  | nil => exact .nil
  | cons h1 hrest => exact .cons (subst_typing h1 hv) (substList_typing hrest hv)

theorem substArms_typing {Δ : AdtEnv} {Φ : FunEnv} {Ψ : StoreTy} {Γ : Ctx}
    {x : Ident} {v : Expr} {τx τs τr : Ty} {arms : List (Pat × Expr)}
    (harms : ArmsHaveType Δ Φ Ψ (extendCtx Γ x τx) τs arms τr)
    (hv : HasType Δ Φ Ψ emptyCtx v τx) :
    ArmsHaveType Δ Φ Ψ Γ τs (substArms x v arms) τr := by
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
      exact .cons hp hbody (substArms_typing hrest hv)
    · simp only [hcont]
      have hnot : x ∉ bs.map Prod.fst := by
        rw [hbn]
        intro hm
        exact hcont (List.contains_iff_mem.mpr hm)
      rw [extendMany_comm Γ x τx bs hnot] at hbody
      exact .cons hp (subst_typing hbody hv) (substArms_typing hrest hv)
end

/-- Closed value bindings matching a typed binder list `bs`. -/
inductive ValuesMatchEnv (Δ : AdtEnv) (Φ : FunEnv) (Ψ : StoreTy) :
    List (Ident × Expr) → List (Ident × Ty) → Prop where
  | nil : ValuesMatchEnv Δ Φ Ψ [] []
  | cons {x : Ident} {v : Expr} {τ : Ty} {env : List (Ident × Expr)} {bs : List (Ident × Ty)} :
      IsValue v →
      HasType Δ Φ Ψ emptyCtx v τ →
      ValuesMatchEnv Δ Φ Ψ env bs →
      ValuesMatchEnv Δ Φ Ψ ((x, v) :: env) ((x, τ) :: bs)

theorem ValuesMatchEnv.append {Δ : AdtEnv} {Φ : FunEnv} {Ψ : StoreTy}
    {e1 e2 : List (Ident × Expr)} {b1 b2 : List (Ident × Ty)}
    (h1 : ValuesMatchEnv Δ Φ Ψ e1 b1) (h2 : ValuesMatchEnv Δ Φ Ψ e2 b2) :
    ValuesMatchEnv Δ Φ Ψ (e1 ++ e2) (b1 ++ b2) := by
  induction h1 with
  | nil => exact h2
  | cons hv ht _ ih => exact .cons hv ht ih

theorem substMany_typing {Δ : AdtEnv} {Φ : FunEnv} {Ψ : StoreTy} {Γ : Ctx}
    {env : List (Ident × Expr)} {bs : List (Ident × Ty)} {e : Expr} {τ : Ty}
    (hm : ValuesMatchEnv Δ Φ Ψ env bs)
    (he : HasType Δ Φ Ψ (extendMany Γ bs) e τ) :
    HasType Δ Φ Ψ Γ (substMany env e) τ := by
  induction hm generalizing e with
  | nil => exact he
  | cons _ hv _ ih =>
    simp only [extendMany] at he
    simp only [substMany]
    exact ih (subst_typing he hv)

theorem zipParams_match {Δ : AdtEnv} {Φ : FunEnv} {Ψ : StoreTy}
    {ps : List (Ident × Ty)} {args : List Expr}
    (ht : HasTypes Δ Φ Ψ emptyCtx args (ps.map Prod.snd))
    (hvals : ∀ a ∈ args, IsValue a) :
    ValuesMatchEnv Δ Φ Ψ (zipParams ps args) ps := by
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

theorem hasTypes_length {Δ : AdtEnv} {Φ : FunEnv} {Ψ : StoreTy} {Γ : Ctx}
    {es : List Expr} {τs : List Ty} (h : HasTypes Δ Φ Ψ Γ es τs) :
    es.length = τs.length := by
  induction es generalizing τs with
  | nil => cases h; rfl
  | cons _ _ ih =>
    cases h with
    | cons _ hrest => simp [ih hrest]

mutual
theorem matchPat_sound {Δ : AdtEnv} {Φ : FunEnv} {Ψ : StoreTy}
    {p : Pat} {τ : Ty} {bs : List (Ident × Ty)} {v : Expr} {env : List (Ident × Expr)}
    (hp : PatHasType Δ p τ bs) (ht : HasType Δ Φ Ψ emptyCtx v τ) (hv : IsValue v)
    (hm : matchPat p v = some env) :
    ValuesMatchEnv Δ Φ Ψ env bs := by
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

theorem matchPats_sound {Δ : AdtEnv} {Φ : FunEnv} {Ψ : StoreTy}
    {ps : List Pat} {τs : List Ty} {bs : List (Ident × Ty)} {vs : List Expr}
    {env : List (Ident × Expr)}
    (hps : PatsHaveType Δ ps τs bs) (hts : HasTypes Δ Φ Ψ emptyCtx vs τs)
    (hvs : ∀ v ∈ vs, IsValue v) (hm : matchPats ps vs = some env) :
    ValuesMatchEnv Δ Φ Ψ env bs := by
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

theorem store_typed_alloc {Δ : AdtEnv} {Φ : FunEnv} {Ψ : StoreTy} {σ : Store} {v : Expr} {τ : Ty}
    (hst : StoreTyped Δ Φ Ψ σ) (hv : IsValue v) (ht : HasType Δ Φ Ψ emptyCtx v τ) :
    StoreTyped Δ Φ (Ψ ++ [τ]) (σ ++ [v]) := by
  have hext : StoreExtends Ψ (Ψ ++ [τ]) := StoreExtends.append Ψ τ
  refine ⟨by simp [hst.1], fun l t hl => ?_⟩
  cases Nat.lt_or_ge l Ψ.length with
  | inl hlt =>
    rw [List.getElem?_append_left hlt] at hl
    rcases hst.2 l t hl with ⟨w, hw, hwv, hwt⟩
    have hlt' : l < σ.length := hst.1 ▸ hlt
    refine ⟨w, ?_, hwv, typing_store_weaken hext hwt⟩
    rw [List.getElem?_append_left hlt']
    exact hw
  | inr hge =>
    rw [List.getElem?_append_right hge] at hl
    have hlt1 : l - Ψ.length < 1 := by simpa using lt_length_of_getElem?_eq_some hl
    have heql : l = Ψ.length := Nat.le_antisymm (Nat.le_of_sub_eq_zero (Nat.lt_one_iff.mp hlt1)) hge
    subst heql
    simp at hl
    subst hl
    refine ⟨v, ?_, hv, typing_store_weaken hext ht⟩
    rw [← hst.1]
    simp

theorem store_typed_update {Δ : AdtEnv} {Φ : FunEnv} {Ψ : StoreTy} {σ : Store}
    {l : Loc} {v : Expr} {τ : Ty}
    (hst : StoreTyped Δ Φ Ψ σ) (hl : Ψ[l]? = some τ)
    (hv : IsValue v) (ht : HasType Δ Φ Ψ emptyCtx v τ) :
    StoreTyped Δ Φ Ψ (σ.set l v) := by
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

theorem canonical_bool {Δ : AdtEnv} {Φ : FunEnv} {Ψ : StoreTy} {v : Expr}
    (ht : HasType Δ Φ Ψ emptyCtx v .bool) (hv : IsValue v) :
    ∃ b : Bool, v = .lit (.bool b) := by
  cases hv with
  | lit l => cases ht with | lit hl => cases hl; exact ⟨_, rfl⟩
  | loc _ => cases ht
  | lam _ _ _ => cases ht
  | tuple _ => cases ht
  | makeData _ _ _ => cases ht

theorem canonical_int {Δ : AdtEnv} {Φ : FunEnv} {Ψ : StoreTy} {v : Expr}
    (ht : HasType Δ Φ Ψ emptyCtx v .int) (hv : IsValue v) :
    ∃ n : Int32, v = .lit (.int n) := by
  cases hv with
  | lit l => cases ht with | lit hl => cases hl; exact ⟨_, rfl⟩
  | loc _ => cases ht
  | lam _ _ _ => cases ht
  | tuple _ => cases ht
  | makeData _ _ _ => cases ht

theorem canonical_str {Δ : AdtEnv} {Φ : FunEnv} {Ψ : StoreTy} {v : Expr}
    (ht : HasType Δ Φ Ψ emptyCtx v .str) (hv : IsValue v) :
    ∃ s : String, v = .lit (.str s) := by
  cases hv with
  | lit l => cases ht with | lit hl => cases hl; exact ⟨_, rfl⟩
  | loc _ => cases ht
  | lam _ _ _ => cases ht
  | tuple _ => cases ht
  | makeData _ _ _ => cases ht

theorem canonical_fn {Δ : AdtEnv} {Φ : FunEnv} {Ψ : StoreTy} {v : Expr}
    {paramTys : List Ty} {ret : Ty}
    (ht : HasType Δ Φ Ψ emptyCtx v (.fn paramTys ret)) (hv : IsValue v) :
    ∃ ps body, v = .lam ps ret body ∧ ps.map Prod.snd = paramTys := by
  cases hv with
  | lit _ => cases ht with | lit hl => cases hl
  | loc _ => cases ht
  | lam ps r body => cases ht; exact ⟨ps, body, rfl, rfl⟩
  | tuple _ => cases ht
  | makeData _ _ _ => cases ht

theorem canonical_adt {Δ : AdtEnv} {Φ : FunEnv} {Ψ : StoreTy} {v : Expr} {adt : Ident}
    (ht : HasType Δ Φ Ψ emptyCtx v (.adt adt)) (hv : IsValue v) :
    ∃ tag vs, v = .makeData adt tag vs ∧ (∀ u ∈ vs, IsValue u) := by
  cases hv with
  | lit _ => cases ht with | lit hl => cases hl
  | loc _ => cases ht
  | lam _ _ _ => cases ht
  | tuple _ => cases ht
  | makeData a tag hvs => cases ht; exact ⟨tag, _, rfl, hvs⟩

theorem canonical_cell {Δ : AdtEnv} {Φ : FunEnv} {Ψ : StoreTy} {v : Expr} {τ : Ty}
    (ht : HasType Δ Φ Ψ emptyCtx v (.cell τ)) (hv : IsValue v) :
    ∃ l : Loc, v = .loc l ∧ Ψ[l]? = some τ := by
  cases hv with
  | lit _ => cases ht with | lit hl => cases hl
  | loc l => cases ht with | loc hl => exact ⟨l, rfl, hl⟩
  | lam _ _ _ => cases ht
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

/-! ## Progress Theorem -/

mutual
theorem progress {Δ : AdtEnv} {Φ : FunEnv} {Ψ : StoreTy} {σ : Store} {e : Expr} {τ : Ty}
    (hΦ : FunEnvTyped Δ Φ) (ht : HasType Δ Φ Ψ emptyCtx e τ) (hσ : StoreTyped Δ Φ Ψ σ) :
    IsTerminal e ∨ ∃ e' σ', Step Δ Φ e σ e' σ' := by
  cases ht with
  | lit _ => exact Or.inl (Or.inl (.lit _))
  | var hx => simp [emptyCtx] at hx
  | loc _ => exact Or.inl (Or.inl (.loc _))
  | tuple hts =>
    rcases progressList hΦ hts hσ with hvals | ⟨t, htrap⟩ | ⟨es', σ', hstep⟩
    · exact Or.inl (Or.inl (.tuple hvals))
    · exact Or.inr ⟨.trap t, σ, .tupleTrap htrap⟩
    · exact Or.inr ⟨.tuple es', σ', .tupleStep hstep⟩
  | blockEmpty => exact Or.inr ⟨.lit .unit, σ, .blockEmpty⟩
  | blockSingle _ => exact Or.inr ⟨_, σ, .blockSingle⟩
  | blockCons h1 _ =>
    rcases progress hΦ h1 hσ with (hv1 | ⟨t, rfl⟩) | ⟨e1', σ', hs1⟩
    · exact Or.inr ⟨_, σ, .blockConsVal hv1⟩
    · exact Or.inr ⟨.trap t, σ, .blockConsTrap⟩
    · exact Or.inr ⟨_, σ', .blockConsStep hs1⟩
  | lam _ => exact Or.inl (Or.inl (.lam _ _ _))
  | apply hfn hargs =>
    rcases progress hΦ hfn hσ with (hvfn | ⟨t, rfl⟩) | ⟨fn', σ', hsfn⟩
    · rcases progressList hΦ hargs hσ with hvals | ⟨t, htrap⟩ | ⟨args', σ', hsargs⟩
      · rcases canonical_fn hfn hvfn with ⟨ps, body, rfl, hmap⟩
        have hlen := hasTypes_length hargs
        rw [← hmap, List.length_map] at hlen
        exact Or.inr ⟨_, σ, .applyBeta hvals hlen⟩
      · exact Or.inr ⟨.trap t, σ, .applyArgsTrap hvfn htrap⟩
      · exact Or.inr ⟨_, σ', .applyArgs hvfn hsargs⟩
    · exact Or.inr ⟨.trap t, σ, .applyFnTrap⟩
    · exact Or.inr ⟨_, σ', .applyFn hsfn⟩
  | applyDir hf hargs =>
    rcases progressList hΦ hargs hσ with hvals | ⟨t, htrap⟩ | ⟨args', σ', hsargs⟩
    · have hlen := hasTypes_length hargs
      rw [List.length_map] at hlen
      exact Or.inr ⟨_, σ, .applyDirBeta hf hvals hlen⟩
    · exact Or.inr ⟨.trap t, σ, .applyDirTrap htrap⟩
    · exact Or.inr ⟨_, σ', .applyDirArgs hsargs⟩
  | bin hop h1 h2 =>
    rcases progress hΦ h1 hσ with (hv1 | ⟨t, rfl⟩) | ⟨e1', σ', hs1⟩
    · cases hop with
      | and =>
        rcases canonical_bool h1 hv1 with ⟨b, rfl⟩
        cases b
        · exact Or.inr ⟨_, σ, .binAndFalse⟩
        · exact Or.inr ⟨_, σ, .binAndTrue⟩
      | or =>
        rcases canonical_bool h1 hv1 with ⟨b, rfl⟩
        cases b
        · exact Or.inr ⟨_, σ, .binOrFalse⟩
        · exact Or.inr ⟨_, σ, .binOrTrue⟩
        | div =>
          rcases progress hΦ h2 hσ with (hv2 | ⟨t, rfl⟩) | ⟨e2', σ', hs2⟩
          · rcases canonical_int h1 hv1 with ⟨a, rfl⟩
            rcases canonical_int h2 hv2 with ⟨b, rfl⟩
            by_cases hb : (b == 0) = true
            · exact Or.inr ⟨.trap .divByZero, σ, .binTrap (by simp [evalBinOp, hb])⟩
            · have hb' : (b == 0) = false := Bool.eq_false_iff.mpr hb
              exact Or.inr ⟨_, σ, .binVal (l' := .int (a / b)) (by simp [evalBinOp, hb'])⟩
          · exact Or.inr ⟨.trap t, σ, .binRightTrap (by decide) (by decide) hv1⟩
          · exact Or.inr ⟨_, σ', .binRight (by decide) (by decide) hv1 hs2⟩
        | rem =>
          rcases progress hΦ h2 hσ with (hv2 | ⟨t, rfl⟩) | ⟨e2', σ', hs2⟩
          · rcases canonical_int h1 hv1 with ⟨a, rfl⟩
            rcases canonical_int h2 hv2 with ⟨b, rfl⟩
            by_cases hb : (b == 0) = true
            · exact Or.inr ⟨.trap .divByZero, σ, .binTrap (by simp [evalBinOp, hb])⟩
            · have hb' : (b == 0) = false := Bool.eq_false_iff.mpr hb
              exact Or.inr ⟨_, σ, .binVal (l' := .int (a % b)) (by simp [evalBinOp, hb'])⟩
          · exact Or.inr ⟨.trap t, σ, .binRightTrap (by decide) (by decide) hv1⟩
          · exact Or.inr ⟨_, σ', .binRight (by decide) (by decide) hv1 hs2⟩
        | _ =>
          rcases progress hΦ h2 hσ with (hv2 | ⟨t, rfl⟩) | ⟨e2', σ', hs2⟩
          · first
            | (rcases canonical_int h1 hv1 with ⟨a, rfl⟩
               rcases canonical_int h2 hv2 with ⟨b, rfl⟩
               exact Or.inr ⟨_, σ, .binVal (l' := _) rfl⟩)
            | (rcases canonical_bool h1 hv1 with ⟨a, rfl⟩
               rcases canonical_bool h2 hv2 with ⟨b, rfl⟩
               exact Or.inr ⟨_, σ, .binVal (l' := _) rfl⟩)
            | (rcases canonical_str h1 hv1 with ⟨a, rfl⟩
               rcases canonical_str h2 hv2 with ⟨b, rfl⟩
               exact Or.inr ⟨_, σ, .binVal (l' := _) rfl⟩)
          · exact Or.inr ⟨.trap t, σ, .binRightTrap (by decide) (by decide) hv1⟩
          · exact Or.inr ⟨_, σ', .binRight (by decide) (by decide) hv1 hs2⟩
    · exact Or.inr ⟨.trap t, σ, .binLeftTrap⟩
    · exact Or.inr ⟨_, σ', .binLeft hs1⟩
  | un hop h1 =>
    rcases progress hΦ h1 hσ with (hv1 | ⟨t, rfl⟩) | ⟨e1', σ', hs1⟩
    · cases hop with
      | not =>
        rcases canonical_bool h1 hv1 with ⟨b, rfl⟩
        exact Or.inr ⟨_, σ, .unVal (l' := .bool (!b)) rfl⟩
      | neg =>
        rcases canonical_int h1 hv1 with ⟨n, rfl⟩
        exact Or.inr ⟨_, σ, .unVal (l' := .int (-n)) rfl⟩
      | bitNot =>
        rcases canonical_int h1 hv1 with ⟨n, rfl⟩
        exact Or.inr ⟨_, σ, .unVal (l' := .int (~~~n)) rfl⟩
    · exact Or.inr ⟨.trap t, σ, .unTrap⟩
    · exact Or.inr ⟨_, σ', .unStep hs1⟩
  | let_ h1 _ =>
    rcases progress hΦ h1 hσ with (hv1 | ⟨t, rfl⟩) | ⟨e1', σ', hs1⟩
    · exact Or.inr ⟨_, σ, .letVal hv1⟩
    · exact Or.inr ⟨.trap t, σ, .letTrap⟩
    · exact Or.inr ⟨_, σ', .letStep hs1⟩
  | if_ hc _ _ =>
    rcases progress hΦ hc hσ with (hvc | ⟨t, rfl⟩) | ⟨c', σ', hsc⟩
    · rcases canonical_bool hc hvc with ⟨b, rfl⟩
      cases b
      · exact Or.inr ⟨_, σ, .ifFalse⟩
      · exact Or.inr ⟨_, σ, .ifTrue⟩
    · exact Or.inr ⟨.trap t, σ, .ifTrap⟩
    · exact Or.inr ⟨_, σ', .ifStep hsc⟩
  | while_ _ _ => exact Or.inr ⟨_, σ, .whileUnfold⟩
  | @match_ _ scrut arms _ _ hs _ =>
    rcases progress hΦ hs hσ with (hvs | ⟨t, rfl⟩) | ⟨s', σ', hss⟩
    · cases arms with
      | nil => exact Or.inr ⟨.trap .matchFailure, σ, .matchEmpty hvs⟩
      | cons arm rest =>
        cases arm with
        | mk p body =>
          cases hm : matchPat p scrut with
          | none => exact Or.inr ⟨_, σ, .matchMiss hvs hm⟩
          | some env => exact Or.inr ⟨_, σ, .matchHit hvs hm⟩
    · exact Or.inr ⟨.trap t, σ, .matchScrutTrap⟩
    · exact Or.inr ⟨_, σ', .matchScrut hss⟩
  | makeData _ hts =>
    rcases progressList hΦ hts hσ with hvals | ⟨t, htrap⟩ | ⟨es', σ', hstep⟩
    · exact Or.inl (Or.inl (.makeData _ _ hvals))
    · exact Or.inr ⟨.trap t, σ, .makeDataTrap htrap⟩
    · exact Or.inr ⟨_, σ', .makeDataStep hstep⟩
  | getTag he =>
    rcases progress hΦ he hσ with (hv | ⟨t, rfl⟩) | ⟨e', σ', hse⟩
    · rcases canonical_adt he hv with ⟨tag, vs, rfl, hvs⟩
      exact Or.inr ⟨_, σ, .getTagVal hvs⟩
    · exact Or.inr ⟨.trap t, σ, .getTagTrap⟩
    · exact Or.inr ⟨_, σ', .getTagStep hse⟩
  | cellNew he =>
    rcases progress hΦ he hσ with (hv | ⟨t, rfl⟩) | ⟨e', σ', hse⟩
    · exact Or.inr ⟨_, _, .cellNewVal hv⟩
    · exact Or.inr ⟨.trap t, σ, .cellNewTrap⟩
    · exact Or.inr ⟨_, σ', .cellNewStep hse⟩
  | cellGet he =>
    rcases progress hΦ he hσ with (hv | ⟨t, rfl⟩) | ⟨e', σ', hse⟩
    · rcases canonical_cell he hv with ⟨l, rfl, hl⟩
      rcases hσ.2 l _ hl with ⟨v, hvσ, _, _⟩
      exact Or.inr ⟨v, σ, .cellGetVal hvσ⟩
    · exact Or.inr ⟨.trap t, σ, .cellGetTrap⟩
    · exact Or.inr ⟨_, σ', .cellGetStep hse⟩
  | cellSet h1 h2 =>
    rcases progress hΦ h1 hσ with (hv1 | ⟨t, rfl⟩) | ⟨e1', σ', hs1⟩
    · rcases progress hΦ h2 hσ with (hv2 | ⟨t, rfl⟩) | ⟨e2', σ', hs2⟩
      · rcases canonical_cell h1 hv1 with ⟨l, rfl, hl⟩
        have hltΨ : l < Ψ.length := lt_length_of_getElem?_eq_some hl
        have hltσ : l < σ.length := hσ.1 ▸ hltΨ
        exact Or.inr ⟨_, _, .cellSetVal hltσ hv2⟩
      · exact Or.inr ⟨.trap t, σ, .cellSetRightTrap hv1⟩
      · exact Or.inr ⟨_, σ', .cellSetRight hv1 hs2⟩
    · exact Or.inr ⟨.trap t, σ, .cellSetLeftTrap⟩
    · exact Or.inr ⟨_, σ', .cellSetLeft hs1⟩
  | trap t _ => exact Or.inl (Or.inr ⟨t, rfl⟩)

theorem progressList {Δ : AdtEnv} {Φ : FunEnv} {Ψ : StoreTy} {σ : Store}
    {es : List Expr} {τs : List Ty}
    (hΦ : FunEnvTyped Δ Φ) (hts : HasTypes Δ Φ Ψ emptyCtx es τs) (hσ : StoreTyped Δ Φ Ψ σ) :
    (∀ e ∈ es, IsValue e) ∨ (∃ t, ListFirstTrap es t) ∨ (∃ es' σ', StepList Δ Φ es σ es' σ') := by
  cases hts with
  | nil => exact Or.inl (fun _ h => by cases h)
  | cons h1 hrest =>
    rcases progress hΦ h1 hσ with (hv1 | ⟨t, rfl⟩) | ⟨e1', σ', hs1⟩
    · rcases progressList hΦ hrest hσ with hvals | ⟨t, htrap⟩ | ⟨es', σ', hss⟩
      · exact Or.inl (fun u hu => by
          rcases List.mem_cons.mp hu with rfl | hu'
          · exact hv1
          · exact hvals u hu')
      · exact Or.inr (Or.inl ⟨t, .tail hv1 htrap⟩)
      · exact Or.inr (Or.inr ⟨_, σ', .tail hv1 hss⟩)
    · exact Or.inr (Or.inl ⟨t, .head t _⟩)
    · exact Or.inr (Or.inr ⟨_, σ', .head hs1⟩)
end

/-! ## Preservation Theorem (Subject Reduction) -/

mutual
theorem preservation {Δ : AdtEnv} {Φ : FunEnv} (hΦ : FunEnvTyped Δ Φ)
    {e : Expr} {σ : Store} {e' : Expr} {σ' : Store}
    (hstep : Step Δ Φ e σ e' σ')
    {Ψ : StoreTy} {τ : Ty}
    (ht : HasType Δ Φ Ψ emptyCtx e τ) (hσ : StoreTyped Δ Φ Ψ σ) :
    ∃ Ψ', StoreExtends Ψ Ψ' ∧ HasType Δ Φ Ψ' emptyCtx e' τ ∧ StoreTyped Δ Φ Ψ' σ' := by
  cases hstep with
  | tupleStep hs =>
    cases ht with
    | tuple hts =>
      rcases preservationList hΦ hs hts hσ with ⟨Ψ', hext, hts', hσ'⟩
      exact ⟨Ψ', hext, .tuple hts', hσ'⟩
  | tupleTrap _ => exact ⟨Ψ, StoreExtends.refl Ψ, .trap _ τ, hσ⟩
  | blockEmpty =>
    cases ht
    exact ⟨Ψ, StoreExtends.refl Ψ, .lit .unit, hσ⟩
  | blockSingle =>
    cases ht with
    | blockSingle he => exact ⟨Ψ, StoreExtends.refl Ψ, he, hσ⟩
  | blockConsStep hs =>
    cases ht with
    | blockCons h1 h2 =>
      rcases preservation hΦ hs h1 hσ with ⟨Ψ', hext, h1', hσ'⟩
      exact ⟨Ψ', hext, .blockCons h1' (typing_store_weaken hext h2), hσ'⟩
  | blockConsVal _ =>
    cases ht with
    | blockCons _ h2 => exact ⟨Ψ, StoreExtends.refl Ψ, h2, hσ⟩
  | blockConsTrap => exact ⟨Ψ, StoreExtends.refl Ψ, .trap _ τ, hσ⟩
  | applyFn hs =>
    cases ht with
    | apply hfn hargs =>
      rcases preservation hΦ hs hfn hσ with ⟨Ψ', hext, hfn', hσ'⟩
      exact ⟨Ψ', hext, .apply hfn' (typingList_store_weaken hext hargs), hσ'⟩
  | applyFnTrap => exact ⟨Ψ, StoreExtends.refl Ψ, .trap _ τ, hσ⟩
  | applyArgs _ hs =>
    cases ht with
    | apply hfn hargs =>
      rcases preservationList hΦ hs hargs hσ with ⟨Ψ', hext, hargs', hσ'⟩
      exact ⟨Ψ', hext, .apply (typing_store_weaken hext hfn) hargs', hσ'⟩
  | applyArgsTrap _ _ => exact ⟨Ψ, StoreExtends.refl Ψ, .trap _ τ, hσ⟩
  | applyBeta hvals _ =>
    cases ht with
    | apply hfn hargs =>
      cases hfn with
      | lam hbody =>
        have hmatch := zipParams_match hargs hvals
        exact ⟨Ψ, StoreExtends.refl Ψ, substMany_typing hmatch hbody, hσ⟩
  | applyDirArgs hs =>
    cases ht with
    | applyDir hf hargs =>
      rcases preservationList hΦ hs hargs hσ with ⟨Ψ', hext, hargs', hσ'⟩
      exact ⟨Ψ', hext, .applyDir hf hargs', hσ'⟩
  | applyDirTrap _ => exact ⟨Ψ, StoreExtends.refl Ψ, .trap _ τ, hσ⟩
  | applyDirBeta hf hvals _ =>
    cases ht with
    | applyDir hf' hargs =>
      rw [hf] at hf'; cases hf'
      have hbody0 := hΦ _ _ hf
      have hext0 : StoreExtends [] Ψ := ⟨Nat.zero_le _, fun _ _ h => by simp at h⟩
      have hbody := typing_store_weaken hext0 hbody0
      have hmatch := zipParams_match hargs hvals
      exact ⟨Ψ, StoreExtends.refl Ψ, substMany_typing hmatch hbody, hσ⟩
  | unStep hs =>
    cases ht with
    | un hop h1 =>
      rcases preservation hΦ hs h1 hσ with ⟨Ψ', hext, h1', hσ'⟩
      exact ⟨Ψ', hext, .un hop h1', hσ'⟩
  | unTrap => exact ⟨Ψ, StoreExtends.refl Ψ, .trap _ τ, hσ⟩
  | unVal he =>
    cases ht with
    | un hop h1 =>
      cases h1 with
      | lit hl => exact ⟨Ψ, StoreExtends.refl Ψ, .lit (evalUnOp_sound hop hl he), hσ⟩
  | binLeft hs =>
    cases ht with
    | bin hop h1 h2 =>
      rcases preservation hΦ hs h1 hσ with ⟨Ψ', hext, h1', hσ'⟩
      exact ⟨Ψ', hext, .bin hop h1' (typing_store_weaken hext h2), hσ'⟩
  | binLeftTrap => exact ⟨Ψ, StoreExtends.refl Ψ, .trap _ τ, hσ⟩
  | binAndFalse =>
    cases ht with
    | bin hop _ _ => cases hop; exact ⟨Ψ, StoreExtends.refl Ψ, .lit (.bool false), hσ⟩
  | binAndTrue =>
    cases ht with
    | bin hop _ h2 => cases hop; exact ⟨Ψ, StoreExtends.refl Ψ, h2, hσ⟩
  | binOrTrue =>
    cases ht with
    | bin hop _ _ => cases hop; exact ⟨Ψ, StoreExtends.refl Ψ, .lit (.bool true), hσ⟩
  | binOrFalse =>
    cases ht with
    | bin hop _ h2 => cases hop; exact ⟨Ψ, StoreExtends.refl Ψ, h2, hσ⟩
  | binRight _ _ _ hs =>
    cases ht with
    | bin hop h1 h2 =>
      rcases preservation hΦ hs h2 hσ with ⟨Ψ', hext, h2', hσ'⟩
      exact ⟨Ψ', hext, .bin hop (typing_store_weaken hext h1) h2', hσ'⟩
  | binRightTrap _ _ _ => exact ⟨Ψ, StoreExtends.refl Ψ, .trap _ τ, hσ⟩
  | binVal he =>
    cases ht with
    | bin hop h1 h2 =>
      cases h1 with
      | lit hl1 =>
        cases h2 with
        | lit hl2 =>
          exact ⟨Ψ, StoreExtends.refl Ψ, .lit (evalBinOp_sound hop hl1 hl2 he), hσ⟩
  | binTrap _ => exact ⟨Ψ, StoreExtends.refl Ψ, .trap _ τ, hσ⟩
  | letStep hs =>
    cases ht with
    | let_ h1 h2 =>
      rcases preservation hΦ hs h1 hσ with ⟨Ψ', hext, h1', hσ'⟩
      exact ⟨Ψ', hext, .let_ h1' (typing_store_weaken hext h2), hσ'⟩
  | letTrap => exact ⟨Ψ, StoreExtends.refl Ψ, .trap _ τ, hσ⟩
  | letVal _ =>
    cases ht with
    | let_ h1 h2 => exact ⟨Ψ, StoreExtends.refl Ψ, subst_typing h2 h1, hσ⟩
  | ifStep hs =>
    cases ht with
    | if_ hc h1 h2 =>
      rcases preservation hΦ hs hc hσ with ⟨Ψ', hext, hc', hσ'⟩
      exact ⟨Ψ', hext, .if_ hc' (typing_store_weaken hext h1) (typing_store_weaken hext h2), hσ'⟩
  | ifTrap => exact ⟨Ψ, StoreExtends.refl Ψ, .trap _ τ, hσ⟩
  | ifTrue =>
    cases ht with
    | if_ _ h1 _ => exact ⟨Ψ, StoreExtends.refl Ψ, h1, hσ⟩
  | ifFalse =>
    cases ht with
    | if_ _ _ h2 => exact ⟨Ψ, StoreExtends.refl Ψ, h2, hσ⟩
  | whileUnfold =>
    cases ht with
    | while_ hc hb =>
      exact ⟨Ψ, StoreExtends.refl Ψ,
        .if_ hc (.blockCons hb (.blockSingle (.while_ hc hb))) (.lit .unit), hσ⟩
  | matchScrut hs =>
    cases ht with
    | match_ hscr harms =>
      rcases preservation hΦ hs hscr hσ with ⟨Ψ', hext, hscr', hσ'⟩
      exact ⟨Ψ', hext, .match_ hscr' (typingArms_store_weaken hext harms), hσ'⟩
  | matchScrutTrap => exact ⟨Ψ, StoreExtends.refl Ψ, .trap _ τ, hσ⟩
  | matchEmpty _ => exact ⟨Ψ, StoreExtends.refl Ψ, .trap .matchFailure τ, hσ⟩
  | matchHit hv hm =>
    cases ht with
    | match_ hs harms =>
      cases harms with
      | cons hp hbody _ =>
        have hmatch := matchPat_sound hp hs hv hm
        exact ⟨Ψ, StoreExtends.refl Ψ, substMany_typing hmatch hbody, hσ⟩
  | matchMiss _ _ =>
    cases ht with
    | match_ hs harms =>
      cases harms with
      | cons _ _ hrest => exact ⟨Ψ, StoreExtends.refl Ψ, .match_ hs hrest, hσ⟩
  | makeDataStep hs =>
    cases ht with
    | makeData hv hts =>
      rcases preservationList hΦ hs hts hσ with ⟨Ψ', hext, hts', hσ'⟩
      exact ⟨Ψ', hext, .makeData hv hts', hσ'⟩
  | makeDataTrap _ => exact ⟨Ψ, StoreExtends.refl Ψ, .trap _ τ, hσ⟩
  | getTagStep hs =>
    cases ht with
    | getTag he =>
      rcases preservation hΦ hs he hσ with ⟨Ψ', hext, he', hσ'⟩
      exact ⟨Ψ', hext, .getTag he', hσ'⟩
  | getTagTrap => exact ⟨Ψ, StoreExtends.refl Ψ, .trap _ τ, hσ⟩
  | getTagVal _ =>
    cases ht with
    | getTag _ => exact ⟨Ψ, StoreExtends.refl Ψ, .lit (.int _), hσ⟩
  | cellNewStep hs =>
    cases ht with
    | cellNew he =>
      rcases preservation hΦ hs he hσ with ⟨Ψ', hext, he', hσ'⟩
      exact ⟨Ψ', hext, .cellNew he', hσ'⟩
  | cellNewTrap => exact ⟨Ψ, StoreExtends.refl Ψ, .trap _ τ, hσ⟩
  | cellNewVal hv =>
    cases ht with
    | @cellNew _ _ τ0 he =>
      have hext : StoreExtends Ψ (Ψ ++ [τ0]) := StoreExtends.append Ψ τ0
      have hloc : (Ψ ++ [τ0])[σ.length]? = some τ0 := by rw [hσ.1]; simp
      exact ⟨Ψ ++ [τ0], hext, .loc hloc, store_typed_alloc hσ hv he⟩
  | cellGetStep hs =>
    cases ht with
    | cellGet he =>
      rcases preservation hΦ hs he hσ with ⟨Ψ', hext, he', hσ'⟩
      exact ⟨Ψ', hext, .cellGet he', hσ'⟩
  | cellGetTrap => exact ⟨Ψ, StoreExtends.refl Ψ, .trap _ τ, hσ⟩
  | cellGetVal hvσ =>
    cases ht with
    | cellGet hloc =>
      cases hloc with
      | loc hl =>
        rcases hσ.2 _ _ hl with ⟨v', hv', _, hvt⟩
        rw [hvσ] at hv'; cases hv'
        exact ⟨Ψ, StoreExtends.refl Ψ, hvt, hσ⟩
  | cellSetLeft hs =>
    cases ht with
    | cellSet h1 h2 =>
      rcases preservation hΦ hs h1 hσ with ⟨Ψ', hext, h1', hσ'⟩
      exact ⟨Ψ', hext, .cellSet h1' (typing_store_weaken hext h2), hσ'⟩
  | cellSetLeftTrap => exact ⟨Ψ, StoreExtends.refl Ψ, .trap _ τ, hσ⟩
  | cellSetRight _ hs =>
    cases ht with
    | cellSet h1 h2 =>
      rcases preservation hΦ hs h2 hσ with ⟨Ψ', hext, h2', hσ'⟩
      exact ⟨Ψ', hext, .cellSet (typing_store_weaken hext h1) h2', hσ'⟩
  | cellSetRightTrap _ => exact ⟨Ψ, StoreExtends.refl Ψ, .trap _ τ, hσ⟩
  | cellSetVal _ hv =>
    cases ht with
    | cellSet h1 h2 =>
      cases h1 with
      | loc hl =>
        exact ⟨Ψ, StoreExtends.refl Ψ, .lit .unit, store_typed_update hσ hl hv h2⟩
termination_by sizeOf e

theorem preservationList {Δ : AdtEnv} {Φ : FunEnv} (hΦ : FunEnvTyped Δ Φ)
    {es : List Expr} {σ : Store} {es' : List Expr} {σ' : Store}
    (hstep : StepList Δ Φ es σ es' σ')
    {Ψ : StoreTy} {τs : List Ty}
    (hts : HasTypes Δ Φ Ψ emptyCtx es τs) (hσ : StoreTyped Δ Φ Ψ σ) :
    ∃ Ψ', StoreExtends Ψ Ψ' ∧ HasTypes Δ Φ Ψ' emptyCtx es' τs ∧ StoreTyped Δ Φ Ψ' σ' := by
  cases hstep with
  | head hs =>
    cases hts with
    | cons h1 hrest =>
      rcases preservation hΦ hs h1 hσ with ⟨Ψ', hext, h1', hσ'⟩
      exact ⟨Ψ', hext, .cons h1' (typingList_store_weaken hext hrest), hσ'⟩
  | tail _ hs =>
    cases hts with
    | cons h1 hrest =>
      rcases preservationList hΦ hs hrest hσ with ⟨Ψ', hext, hrest', hσ'⟩
      exact ⟨Ψ', hext, .cons (typing_store_weaken hext h1) hrest', hσ'⟩
termination_by sizeOf es
end

/-! ## Multi-Step Type Safety Corollary -/

theorem type_safety {Δ : AdtEnv} {Φ : FunEnv} {Ψ : StoreTy} {σ σ' : Store} {e e' : Expr} {τ : Ty}
    (hΦ : FunEnvTyped Δ Φ) (ht : HasType Δ Φ Ψ emptyCtx e τ) (hσ : StoreTyped Δ Φ Ψ σ)
    (hsteps : Steps Δ Φ e σ e' σ') :
    ¬ IsStuck Δ Φ e' σ' := by
  induction hsteps generalizing Ψ with
  | refl =>
    intro ⟨hnt, hns⟩
    rcases progress hΦ ht hσ with ht' | hs'
    · exact hnt ht'
    · exact hns hs'
  | trans hstep _ ih =>
    rcases preservation hΦ hstep ht hσ with ⟨Ψ', _, ht', hσ'⟩
    exact ih ht' hσ'

end CoreGeisha
