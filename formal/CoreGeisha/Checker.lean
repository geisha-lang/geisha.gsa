import CoreGeisha.Syntax
import CoreGeisha.Typing
import CoreGeisha.Semantics
import CoreGeisha.Soundness

/-!
# Core Geisha: Verified Executable Type Checker

An executable type checker `checkProgram` / `checkExpr` with a machine-checked
soundness proof (`checkProgram_sound`, `verified_program_safety`) linking
concrete Core IR programs dumped by `geisha.gs` directly to `CoreGeisha.type_safety`.
-/

namespace CoreGeisha

/-! ## Decidable Type Equality with Soundness Proof -/

mutual
def tyEq : Ty → Ty → Bool
  | .void, .void => true
  | .int, .int => true
  | .bool, .bool => true
  | .str, .str => true
  | .tuple ts1, .tuple ts2 => tyListEq ts1 ts2
  | .fn ps1 r1, .fn ps2 r2 => tyListEq ps1 ps2 && tyEq r1 r2
  | .adt n1, .adt n2 => n1 == n2
  | .cell t1, .cell t2 => tyEq t1 t2
  | _, _ => false

def tyListEq : List Ty → List Ty → Bool
  | [], [] => true
  | t1 :: ts1, t2 :: ts2 => tyEq t1 t2 && tyListEq ts1 ts2
  | _, _ => false
end

mutual
theorem tyEq_sound {t1 t2 : Ty} (h : tyEq t1 t2 = true) : t1 = t2 := by
  cases t1 <;> cases t2 <;> simp only [tyEq] at h <;> try cases h
  · rfl
  · rfl
  · rfl
  · rfl
  · rw [tyListEq_sound h]
  · simp only [Bool.and_eq_true] at h
    rw [tyListEq_sound h.1, tyEq_sound h.2]
  · simp only [beq_iff_eq] at h
    rw [h]
  · rw [tyEq_sound h]

theorem tyListEq_sound {ts1 ts2 : List Ty} (h : tyListEq ts1 ts2 = true) : ts1 = ts2 := by
  cases ts1 <;> cases ts2 <;> simp only [tyListEq] at h <;> try cases h
  · rfl
  · simp only [Bool.and_eq_true] at h
    rw [tyEq_sound h.1, tyListEq_sound h.2]
end

/-! ## Literal & Operator Checkers -/

def checkLit : Lit → Ty
  | .int _ => .int
  | .bool _ => .bool
  | .str _ => .str
  | .unit => .void

theorem checkLit_sound (l : Lit) : LitHasType l (checkLit l) := by
  cases l <;> constructor

def checkUnOp (op : UnOp) (τ : Ty) : Except String Ty :=
  match op, τ with
  | .not, .bool => .ok .bool
  | .neg, .int => .ok .int
  | .bitNot, .int => .ok .int
  | _, _ => .error s!"unary operator {repr op} ill-typed for {repr τ}"

theorem checkUnOp_sound {op : UnOp} {τ1 τr : Ty} (h : checkUnOp op τ1 = .ok τr) :
    UnOpHasType op τ1 τr := by
  cases op <;> cases τ1 <;> simp [checkUnOp] at h <;> subst h <;> constructor

def checkBinOp (op : BinOp) (τ1 τ2 : Ty) : Except String Ty :=
  match op, τ1, τ2 with
  | .add, .int, .int => .ok .int
  | .sub, .int, .int => .ok .int
  | .mul, .int, .int => .ok .int
  | .div, .int, .int => .ok .int
  | .rem, .int, .int => .ok .int
  | .bitAnd, .int, .int => .ok .int
  | .bitOr, .int, .int => .ok .int
  | .bitXor, .int, .int => .ok .int
  | .eqInt, .int, .int => .ok .bool
  | .neInt, .int, .int => .ok .bool
  | .ltInt, .int, .int => .ok .bool
  | .leInt, .int, .int => .ok .bool
  | .gtInt, .int, .int => .ok .bool
  | .geInt, .int, .int => .ok .bool
  | .eqBool, .bool, .bool => .ok .bool
  | .eqStr, .str, .str => .ok .bool
  | .strConcat, .str, .str => .ok .str
  | .and, .bool, .bool => .ok .bool
  | .or, .bool, .bool => .ok .bool
  | _, _, _ => .error s!"binary operator {repr op} ill-typed for ({repr τ1}, {repr τ2})"

theorem checkBinOp_sound {op : BinOp} {τ1 τ2 τr : Ty} (h : checkBinOp op τ1 τ2 = .ok τr) :
    BinOpHasType op τ1 τ2 τr := by
  cases op <;> cases τ1 <;> cases τ2 <;> simp [checkBinOp] at h <;> subst h <;> constructor

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
def checkExpr (Δ : AdtEnv) (Φ : FunEnv) (Γ : Ctx) : Expr → Except String Ty
  | .lit l => .ok (checkLit l)
  | .var x =>
    match Γ x with
    | some τ => .ok τ
    | none => .error s!"unbound variable '{x}'"
  | .loc l => .error s!"runtime location #{l} not allowed in static Core IR"
  | .tuple es =>
    match checkExprList Δ Φ Γ es with
    | .ok τs => .ok (.tuple τs)
    | .error e => .error e
  | .block [] => .ok .void
  | .block [e] => checkExpr Δ Φ Γ e
  | .block (e1 :: e2 :: es) =>
    match checkExpr Δ Φ Γ e1 with
    | .error err => .error err
    | .ok _ => checkExpr Δ Φ Γ (.block (e2 :: es))
  | .lam ps ret body =>
    match checkExpr Δ Φ (extendMany Γ ps) body with
    | .error err => .error err
    | .ok τb =>
      if tyEq τb ret then .ok (.fn (ps.map Prod.snd) ret)
      else .error s!"lambda return type mismatch: expected {repr ret}, got {repr τb}"
  | .apply fn args =>
    match checkExpr Δ Φ Γ fn with
    | .error err => .error err
    | .ok (.fn paramTys ret) =>
      match checkExprList Δ Φ Γ args with
      | .error err => .error err
      | .ok argTys =>
        if tyListEq argTys paramTys then .ok ret
        else .error s!"closure call argument mismatch: expected {repr paramTys}, got {repr argTys}"
    | .ok other => .error s!"calling non-function value of type {repr other}"
  | .applyDir name args =>
    match Φ name with
    | none => .error s!"unknown direct-call function '{name}'"
    | some fd =>
      match checkExprList Δ Φ Γ args with
      | .error err => .error err
      | .ok argTys =>
        if tyListEq argTys (fd.params.map Prod.snd) then .ok fd.retTy
        else .error s!"direct call '{name}' argument mismatch: expected {repr (fd.params.map Prod.snd)}, got {repr argTys}"
  | .bin op e1 e2 =>
    match checkExpr Δ Φ Γ e1 with
    | .error err => .error err
    | .ok τ1 =>
      match checkExpr Δ Φ Γ e2 with
      | .error err => .error err
      | .ok τ2 => checkBinOp op τ1 τ2
  | .un op e =>
    match checkExpr Δ Φ Γ e with
    | .error err => .error err
    | .ok τ1 => checkUnOp op τ1
  | .let_ x e1 e2 =>
    match checkExpr Δ Φ Γ e1 with
    | .error err => .error err
    | .ok τ1 => checkExpr Δ Φ (extendCtx Γ x τ1) e2
  | .if_ c t e =>
    match checkExpr Δ Φ Γ c with
    | .error err => .error err
    | .ok .bool =>
      match checkExpr Δ Φ Γ t with
      | .error err => .error err
      | .ok τt =>
        match checkExpr Δ Φ Γ e with
        | .error err => .error err
        | .ok τe =>
          if tyEq τt τe then .ok τt
          else .error s!"if branch mismatch: {repr τt} vs {repr τe}"
    | .ok other => .error s!"if condition must be Bool, got {repr other}"
  | .while_ c b =>
    match checkExpr Δ Φ Γ c with
    | .error err => .error err
    | .ok .bool =>
      match checkExpr Δ Φ Γ b with
      | .error err => .error err
      | .ok _ => .ok .void
    | .ok other => .error s!"while condition must be Bool, got {repr other}"
  | .match_ scrut arms =>
    match checkExpr Δ Φ Γ scrut with
    | .error err => .error err
    | .ok τs =>
      match arms with
      | [] => .error "empty match expression"
      | (p, body) :: rest =>
        match checkPat Δ p τs with
        | .error err => .error err
        | .ok bs =>
          match checkExpr Δ Φ (extendMany Γ bs) body with
          | .error err => .error err
          | .ok τr =>
            match checkArms Δ Φ Γ τs τr rest with
            | .error err => .error err
            | .ok () => .ok τr
  | .makeData adt tag es =>
    match lookupVariant Δ adt tag with
    | none => .error s!"unknown variant {adt}#{tag}"
    | some flds =>
      match checkExprList Δ Φ Γ es with
      | .error err => .error err
      | .ok argTys =>
        if tyListEq argTys flds then .ok (.adt adt)
        else .error s!"constructor {adt}#{tag} field mismatch: expected {repr flds}, got {repr argTys}"
  | .getTag e =>
    match checkExpr Δ Φ Γ e with
    | .error err => .error err
    | .ok (.adt _) => .ok .int
    | .ok other => .error s!"getTag expects ADT, got {repr other}"
  | .cellNew e =>
    match checkExpr Δ Φ Γ e with
    | .error err => .error err
    | .ok τ => .ok (.cell τ)
  | .cellGet e =>
    match checkExpr Δ Φ Γ e with
    | .error err => .error err
    | .ok (.cell τ) => .ok τ
    | .ok other => .error s!"cellGet expects Cell, got {repr other}"
  | .cellSet e1 e2 =>
    match checkExpr Δ Φ Γ e1 with
    | .error err => .error err
    | .ok (.cell τ) =>
      match checkExpr Δ Φ Γ e2 with
      | .error err => .error err
      | .ok τ2 =>
        if tyEq τ2 τ then .ok .void
        else .error s!"cellSet type mismatch: expected {repr τ}, got {repr τ2}"
    | .ok other => .error s!"cellSet expects Cell, got {repr other}"
  | .trap t => .error s!"runtime trap {repr t} not allowed in static Core IR"

def checkExprList (Δ : AdtEnv) (Φ : FunEnv) (Γ : Ctx) : List Expr → Except String (List Ty)
  | [] => .ok []
  | e :: es =>
    match checkExpr Δ Φ Γ e with
    | .error err => .error err
    | .ok τ =>
      match checkExprList Δ Φ Γ es with
      | .error err => .error err
      | .ok τs => .ok (τ :: τs)

def checkArms (Δ : AdtEnv) (Φ : FunEnv) (Γ : Ctx) (τs τr : Ty) :
    List (Pat × Expr) → Except String Unit
  | [] => .ok ()
  | (p, body) :: rest =>
    match checkPat Δ p τs with
    | .error err => .error err
    | .ok bs =>
      match checkExpr Δ Φ (extendMany Γ bs) body with
      | .error err => .error err
      | .ok τb =>
        if tyEq τb τr then checkArms Δ Φ Γ τs τr rest
        else .error s!"match arm type mismatch: expected {repr τr}, got {repr τb}"
end

/-! ## Soundness Proof of Executable Type Checker -/

mutual
theorem checkExpr_sound {Δ : AdtEnv} {Φ : FunEnv} {Γ : Ctx} {e : Expr} {τ : Ty}
    (h : checkExpr Δ Φ Γ e = .ok τ) : HasType Δ Φ [] Γ e τ := by
  cases e with
  | lit l =>
    simp only [checkExpr, Except.ok.injEq] at h
    subst h; exact .lit (checkLit_sound l)
  | var x =>
    simp only [checkExpr] at h
    cases hx : Γ x with
    | none => simp only [hx] at h; cases h
    | some τ0 => simp only [hx] at h; cases h; exact .var hx
  | loc _ => simp [checkExpr] at h
  | tuple es =>
    simp only [checkExpr] at h
    cases hts : checkExprList Δ Φ Γ es with
    | error _ => simp only [hts] at h; cases h
    | ok τs => simp only [hts] at h; cases h; exact .tuple (checkExprList_sound hts)
  | block es =>
    cases es with
    | nil => simp only [checkExpr, Except.ok.injEq] at h; subst h; exact .blockEmpty
    | cons e1 rest =>
      cases rest with
      | nil =>
        simp only [checkExpr] at h
        exact .blockSingle (checkExpr_sound h)
      | cons e2 tail =>
        simp only [checkExpr] at h
        cases h1 : checkExpr Δ Φ Γ e1 with
        | error _ => simp only [h1] at h; cases h
        | ok τ1 =>
          simp only [h1] at h
          exact .blockCons (checkExpr_sound h1) (checkExpr_sound h)
  | lam ps ret body =>
    simp only [checkExpr] at h
    cases hb : checkExpr Δ Φ (extendMany Γ ps) body with
    | error _ => simp only [hb] at h; cases h
    | ok τb =>
      simp only [hb] at h
      split at h
      · rename_i heq
        cases h
        have h' := tyEq_sound heq
        subst h'
        exact .lam (checkExpr_sound hb)
      · cases h
  | apply fn args =>
    simp only [checkExpr] at h
    cases hfn : checkExpr Δ Φ Γ fn with
    | error _ => simp only [hfn] at h; cases h
    | ok τfn =>
      simp only [hfn] at h
      cases τfn <;> try cases h
      rename_i paramTys ret
      cases hargs : checkExprList Δ Φ Γ args with
      | error _ => simp only [hargs] at h; cases h
      | ok argTys =>
        simp only [hargs] at h
        split at h
        · rename_i heq
          cases h
          have h' := tyListEq_sound heq
          subst h'
          exact .apply (checkExpr_sound hfn) (checkExprList_sound hargs)
        · cases h
  | applyDir name args =>
    simp only [checkExpr] at h
    cases hf : Φ name with
    | none => simp only [hf] at h; cases h
    | some fd =>
      simp only [hf] at h
      cases hargs : checkExprList Δ Φ Γ args with
      | error _ => simp only [hargs] at h; cases h
      | ok argTys =>
        simp only [hargs] at h
        split at h
        · rename_i heq
          cases h
          have h' := tyListEq_sound heq
          subst h'
          exact .applyDir hf (checkExprList_sound hargs)
        · cases h
  | bin op e1 e2 =>
    simp only [checkExpr] at h
    cases h1 : checkExpr Δ Φ Γ e1 with
    | error _ => simp only [h1] at h; cases h
    | ok τ1 =>
      simp only [h1] at h
      cases h2 : checkExpr Δ Φ Γ e2 with
      | error _ => simp only [h2] at h; cases h
      | ok τ2 =>
        simp only [h2] at h
        exact .bin (checkBinOp_sound h) (checkExpr_sound h1) (checkExpr_sound h2)
  | un op e1 =>
    simp only [checkExpr] at h
    cases h1 : checkExpr Δ Φ Γ e1 with
    | error _ => simp only [h1] at h; cases h
    | ok τ1 =>
      simp only [h1] at h
      exact .un (checkUnOp_sound h) (checkExpr_sound h1)
  | let_ x e1 e2 =>
    simp only [checkExpr] at h
    cases h1 : checkExpr Δ Φ Γ e1 with
    | error _ => simp only [h1] at h; cases h
    | ok τ1 =>
      simp only [h1] at h
      exact .let_ (checkExpr_sound h1) (checkExpr_sound h)
  | if_ c t e2 =>
    simp only [checkExpr] at h
    cases hc : checkExpr Δ Φ Γ c with
    | error _ => simp only [hc] at h; cases h
    | ok τc =>
      simp only [hc] at h
      cases τc <;> try cases h
      cases ht : checkExpr Δ Φ Γ t with
      | error _ => simp only [ht] at h; cases h
      | ok τt =>
        simp only [ht] at h
        cases he : checkExpr Δ Φ Γ e2 with
        | error _ => simp only [he] at h; cases h
        | ok τe =>
          simp only [he] at h
          split at h
          · rename_i heq
            cases h
            have h' := tyEq_sound heq
            subst h'
            exact .if_ (checkExpr_sound hc) (checkExpr_sound ht) (checkExpr_sound he)
          · cases h
  | while_ c b =>
    simp only [checkExpr] at h
    cases hc : checkExpr Δ Φ Γ c with
    | error _ => simp only [hc] at h; cases h
    | ok τc =>
      simp only [hc] at h
      cases τc <;> try cases h
      cases hb : checkExpr Δ Φ Γ b with
      | error _ => simp only [hb] at h; cases h
      | ok τb =>
        simp only [hb] at h; cases h
        exact .while_ (checkExpr_sound hc) (checkExpr_sound hb)
  | match_ scrut arms =>
    simp only [checkExpr] at h
    cases hs : checkExpr Δ Φ Γ scrut with
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
            cases hb : checkExpr Δ Φ (extendMany Γ bs) body with
            | error _ => simp only [hb] at h; cases h
            | ok τr =>
              simp only [hb] at h
              cases hr : checkArms Δ Φ Γ τs τr rest with
              | error _ => simp only [hr] at h; cases h
              | ok u =>
                simp only [hr] at h; cases h
                exact .match_ (checkExpr_sound hs)
                  (.cons (checkPat_sound hp) (checkExpr_sound hb) (checkArms_sound hr))
  | makeData adt tag es =>
    simp only [checkExpr] at h
    cases hlv : lookupVariant Δ adt tag with
    | none => simp only [hlv] at h; cases h
    | some flds =>
      simp only [hlv] at h
      cases hes : checkExprList Δ Φ Γ es with
      | error _ => simp only [hes] at h; cases h
      | ok argTys =>
        simp only [hes] at h
        split at h
        · rename_i heq
          cases h
          have h' := tyListEq_sound heq
          subst h'
          exact .makeData hlv (checkExprList_sound hes)
        · cases h
  | getTag e1 =>
    simp only [checkExpr] at h
    cases h1 : checkExpr Δ Φ Γ e1 with
    | error _ => simp only [h1] at h; cases h
    | ok τ1 =>
      simp only [h1] at h
      cases τ1 <;> try cases h
      exact .getTag (checkExpr_sound h1)
  | cellNew e1 =>
    simp only [checkExpr] at h
    cases h1 : checkExpr Δ Φ Γ e1 with
    | error _ => simp only [h1] at h; cases h
    | ok τ1 => simp only [h1] at h; cases h; exact .cellNew (checkExpr_sound h1)
  | cellGet e1 =>
    simp only [checkExpr] at h
    cases h1 : checkExpr Δ Φ Γ e1 with
    | error _ => simp only [h1] at h; cases h
    | ok τ1 =>
      simp only [h1] at h
      cases τ1 <;> try cases h
      exact .cellGet (checkExpr_sound h1)
  | cellSet e1 e2 =>
    simp only [checkExpr] at h
    cases h1 : checkExpr Δ Φ Γ e1 with
    | error _ => simp only [h1] at h; cases h
    | ok τ1 =>
      simp only [h1] at h
      cases τ1 <;> try cases h
      rename_i τelem
      cases h2 : checkExpr Δ Φ Γ e2 with
      | error _ => simp only [h2] at h; cases h
      | ok τ2 =>
        simp only [h2] at h
        split at h
        · rename_i heq
          cases h
          have h' := tyEq_sound heq
          subst h'
          exact .cellSet (checkExpr_sound h1) (checkExpr_sound h2)
        · cases h
  | trap _ => simp [checkExpr] at h
termination_by sizeOf e

theorem checkExprList_sound {Δ : AdtEnv} {Φ : FunEnv} {Γ : Ctx} {es : List Expr} {τs : List Ty}
    (h : checkExprList Δ Φ Γ es = .ok τs) : HasTypes Δ Φ [] Γ es τs := by
  cases es with
  | nil => simp only [checkExprList, Except.ok.injEq] at h; subst h; exact .nil
  | cons e rest =>
    simp only [checkExprList] at h
    cases h1 : checkExpr Δ Φ Γ e with
    | error _ => simp only [h1] at h; cases h
    | ok τ =>
      simp only [h1] at h
      cases h2 : checkExprList Δ Φ Γ rest with
      | error _ => simp only [h2] at h; cases h
      | ok τs' =>
        simp only [h2] at h; cases h
        exact .cons (checkExpr_sound h1) (checkExprList_sound h2)
termination_by sizeOf es

theorem checkArms_sound {Δ : AdtEnv} {Φ : FunEnv} {Γ : Ctx} {τs τr : Ty}
    {arms : List (Pat × Expr)}
    (h : checkArms Δ Φ Γ τs τr arms = .ok ()) : ArmsHaveType Δ Φ [] Γ τs arms τr := by
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
        cases hb : checkExpr Δ Φ (extendMany Γ bs) body with
        | error _ => simp only [hb] at h; cases h
        | ok τb =>
          simp only [hb] at h
          split at h
          · rename_i heq
            have h' := tyEq_sound heq
            subst h'
            exact .cons (checkPat_sound hp) (checkExpr_sound hb) (checkArms_sound h)
          · cases h
termination_by sizeOf arms
end

/-! ## Whole-Program Checker & End-to-End Safety Theorem -/

/-- A concrete Core Geisha program as exported by `geisha.gs --dump-core`. -/
structure Program where
  adts : List AdtDef
  funs : List FunDef
  deriving Repr

def Program.toAdtEnv (p : Program) : AdtEnv :=
  fun name => p.adts.find? (fun a => a.name == name)

def Program.toFunEnv (p : Program) : FunEnv :=
  fun name => p.funs.find? (fun f => f.name == name)

def checkFunDef (Δ : AdtEnv) (Φ : FunEnv) (fd : FunDef) : Except String Unit :=
  match checkExpr Δ Φ (extendMany emptyCtx fd.params) fd.body with
  | .error err => .error s!"in function '{fd.name}': {err}"
  | .ok τb =>
    if tyEq τb fd.retTy then .ok ()
    else .error s!"in function '{fd.name}': body type {repr τb} != declared return type {repr fd.retTy}"

def checkFunList (Δ : AdtEnv) (Φ : FunEnv) : List FunDef → Except String Unit
  | [] => .ok ()
  | fd :: rest =>
    match checkFunDef Δ Φ fd with
    | .error err => .error err
    | .ok () => checkFunList Δ Φ rest

def checkProgram (prog : Program) : Except String Unit :=
  checkFunList prog.toAdtEnv prog.toFunEnv prog.funs

theorem checkFunDef_sound {Δ : AdtEnv} {Φ : FunEnv} {fd : FunDef}
    (h : checkFunDef Δ Φ fd = .ok ()) :
    HasType Δ Φ [] (extendMany emptyCtx fd.params) fd.body fd.retTy := by
  simp only [checkFunDef] at h
  cases hb : checkExpr Δ Φ (extendMany emptyCtx fd.params) fd.body with
  | error _ => simp only [hb] at h; cases h
  | ok τb =>
    simp only [hb] at h
    split at h
    · rename_i heq
      have h' := tyEq_sound heq
      subst h'
      exact checkExpr_sound hb
    · cases h

theorem checkFunList_mem {Δ : AdtEnv} {Φ : FunEnv} {fds : List FunDef} {fd : FunDef}
    (h : checkFunList Δ Φ fds = .ok ()) (hmem : fd ∈ fds) :
    HasType Δ Φ [] (extendMany emptyCtx fd.params) fd.body fd.retTy := by
  induction fds with
  | nil => cases hmem
  | cons f rest ih =>
    simp only [checkFunList] at h
    cases hf : checkFunDef Δ Φ f with
    | error _ => simp only [hf] at h; cases h
    | ok u =>
      simp only [hf] at h
      rcases List.mem_cons.mp hmem with rfl | hrest
      · exact checkFunDef_sound hf
      · exact ih h hrest

theorem checkProgram_sound {prog : Program} (h : checkProgram prog = .ok ()) :
    FunEnvTyped prog.toAdtEnv prog.toFunEnv := by
  intro name fd hfd
  have hmem : fd ∈ prog.funs := List.mem_of_find?_eq_some hfd
  exact checkFunList_mem h hmem

/-- End-to-end Verified Translation Validation Theorem:
    Any Core Geisha program accepted by `checkProgram` is guaranteed by Lean 4's
    kernel to never reach a stuck state (no UB) when executing any 0-arg entry
    function (e.g. `main`). -/
theorem verified_program_safety (prog : Program) (hchk : checkProgram prog = .ok ())
    (entry : Ident) (fd : FunDef) (hfd : prog.toFunEnv entry = some fd)
    (hnoargs : fd.params = [])
    (e' : Expr) (σ' : Store)
    (hsteps : Steps prog.toAdtEnv prog.toFunEnv fd.body [] e' σ') :
    ¬ IsStuck prog.toAdtEnv prog.toFunEnv e' σ' := by
  have hΦ : FunEnvTyped prog.toAdtEnv prog.toFunEnv := checkProgram_sound hchk
  have hbody : HasType prog.toAdtEnv prog.toFunEnv [] emptyCtx fd.body fd.retTy := by
    have h1 := hΦ entry fd hfd
    rw [hnoargs] at h1
    exact h1
  have hσ0 : StoreTyped prog.toAdtEnv prog.toFunEnv [] [] :=
    ⟨rfl, fun _ _ h => by simp at h⟩
  exact type_safety hΦ hbody hσ0 hsteps

end CoreGeisha
