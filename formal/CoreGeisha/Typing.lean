import CoreGeisha.Syntax

/-!
# Core Geisha: Declarative Static Semantics (Type System)

Independent, declarative typing rules `HasType Δ Φ Ψ Γ e τ` for Core Geisha,
decoupled from the Hindley-Milner inference algorithm in `src/infer.gs`.
-/

namespace CoreGeisha

/-- Local variable typing context `Γ : Ident → Option Ty`. -/
abbrev Ctx := Ident → Option Ty

/-- Empty typing context. -/
def emptyCtx : Ctx := fun _ => none

/-- Extend context `Γ` with `x : τ` (shadowing any previous binding of `x`). -/
def extendCtx (Γ : Ctx) (x : Ident) (τ : Ty) : Ctx :=
  fun y => if y == x then some τ else Γ y

/-- Extend context `Γ` with a list of `(Ident × Ty)` bindings; earlier entries
    shadow later ones (matching `substMany`). -/
def extendMany (Γ : Ctx) : List (Ident × Ty) → Ctx
  | [] => Γ
  | (x, τ) :: rest => extendCtx (extendMany Γ rest) x τ

/-- Store typing `Ψ : List Ty` assigning a type to each allocated `Cell` location. -/
abbrev StoreTy := List Ty

/-- Store typing extension: `Ψ'` extends `Ψ` (monotone heap growth). -/
def StoreExtends (Ψ Ψ' : StoreTy) : Prop :=
  Ψ.length ≤ Ψ'.length ∧ ∀ (l : Loc) (τ : Ty), Ψ[l]? = some τ → Ψ'[l]? = some τ

/-- Literal typing judgment. -/
inductive LitHasType : Lit → Ty → Prop where
  | int (n : Int32) : LitHasType (.int n) .int
  | bool (b : Bool) : LitHasType (.bool b) .bool
  | str (s : String) : LitHasType (.str s) .str
  | unit : LitHasType .unit .void

/-- Unary operator typing judgment. -/
inductive UnOpHasType : UnOp → Ty → Ty → Prop where
  | not : UnOpHasType .not .bool .bool
  | neg : UnOpHasType .neg .int .int
  | bitNot : UnOpHasType .bitNot .int .int

/-- Binary operator typing judgment. -/
inductive BinOpHasType : BinOp → Ty → Ty → Ty → Prop where
  | add : BinOpHasType .add .int .int .int
  | sub : BinOpHasType .sub .int .int .int
  | mul : BinOpHasType .mul .int .int .int
  | div : BinOpHasType .div .int .int .int
  | rem : BinOpHasType .rem .int .int .int
  | bitAnd : BinOpHasType .bitAnd .int .int .int
  | bitOr : BinOpHasType .bitOr .int .int .int
  | bitXor : BinOpHasType .bitXor .int .int .int
  | eqInt : BinOpHasType .eqInt .int .int .bool
  | neInt : BinOpHasType .neInt .int .int .bool
  | ltInt : BinOpHasType .ltInt .int .int .bool
  | leInt : BinOpHasType .leInt .int .int .bool
  | gtInt : BinOpHasType .gtInt .int .int .bool
  | geInt : BinOpHasType .geInt .int .int .bool
  | eqBool : BinOpHasType .eqBool .bool .bool .bool
  | eqStr : BinOpHasType .eqStr .str .str .bool
  | strConcat : BinOpHasType .strConcat .str .str .str
  | and : BinOpHasType .and .bool .bool .bool
  | or : BinOpHasType .or .bool .bool .bool

/- Pattern typing judgment: `PatHasType Δ p τ bs` checks that pattern `p`
   matches values of type `τ` and binds variables `bs`. -/
mutual
inductive PatHasType (Δ : AdtEnv) : Pat → Ty → List (Ident × Ty) → Prop where
  | wild (τ : Ty) : PatHasType Δ .wild τ []
  | var (x : Ident) (τ : Ty) : PatHasType Δ (.var x) τ [(x, τ)]
  | lit {l : Lit} {τ : Ty} : LitHasType l τ → PatHasType Δ (.lit l) τ []
  | tuple {ps : List Pat} {τs : List Ty} {bs : List (Ident × Ty)} :
      PatsHaveType Δ ps τs bs →
      PatHasType Δ (.tuple ps) (.tuple τs) bs
  | ctor {adt : Ident} {tag : Nat} {ps : List Pat} {flds : List Ty} {bs : List (Ident × Ty)} :
      lookupVariant Δ adt tag = some flds →
      PatsHaveType Δ ps flds bs →
      PatHasType Δ (.ctor adt tag ps) (.adt adt) bs

inductive PatsHaveType (Δ : AdtEnv) : List Pat → List Ty → List (Ident × Ty) → Prop where
  | nil : PatsHaveType Δ [] [] []
  | cons {p : Pat} {ps : List Pat} {τ : Ty} {τs : List Ty} {b1 b2 : List (Ident × Ty)} :
      PatHasType Δ p τ b1 →
      PatsHaveType Δ ps τs b2 →
      PatsHaveType Δ (p :: ps) (τ :: τs) (b1 ++ b2)
end

/- Core Geisha expression typing judgment `Δ; Φ; Ψ; Γ ⊢ e : τ`. -/
mutual
inductive HasType (Δ : AdtEnv) (Φ : FunEnv) (Ψ : StoreTy) : Ctx → Expr → Ty → Prop where
  | lit {Γ : Ctx} {l : Lit} {τ : Ty} :
      LitHasType l τ →
      HasType Δ Φ Ψ Γ (.lit l) τ
  | var {Γ : Ctx} {x : Ident} {τ : Ty} :
      Γ x = some τ →
      HasType Δ Φ Ψ Γ (.var x) τ
  | loc {Γ : Ctx} {l : Loc} {τ : Ty} :
      Ψ[l]? = some τ →
      HasType Δ Φ Ψ Γ (.loc l) (.cell τ)
  | tuple {Γ : Ctx} {es : List Expr} {τs : List Ty} :
      HasTypes Δ Φ Ψ Γ es τs →
      HasType Δ Φ Ψ Γ (.tuple es) (.tuple τs)
  | blockEmpty {Γ : Ctx} :
      HasType Δ Φ Ψ Γ (.block []) .void
  | blockSingle {Γ : Ctx} {e : Expr} {τ : Ty} :
      HasType Δ Φ Ψ Γ e τ →
      HasType Δ Φ Ψ Γ (.block [e]) τ
  | blockCons {Γ : Ctx} {e1 e2 : Expr} {es : List Expr} {τ1 τ : Ty} :
      HasType Δ Φ Ψ Γ e1 τ1 →
      HasType Δ Φ Ψ Γ (.block (e2 :: es)) τ →
      HasType Δ Φ Ψ Γ (.block (e1 :: e2 :: es)) τ
  | lam {Γ : Ctx} {ps : List (Ident × Ty)} {ret : Ty} {body : Expr} :
      HasType Δ Φ Ψ (extendMany Γ ps) body ret →
      HasType Δ Φ Ψ Γ (.lam ps ret body) (.fn (ps.map Prod.snd) ret)
  | apply {Γ : Ctx} {fn : Expr} {args : List Expr} {paramTys : List Ty} {ret : Ty} :
      HasType Δ Φ Ψ Γ fn (.fn paramTys ret) →
      HasTypes Δ Φ Ψ Γ args paramTys →
      HasType Δ Φ Ψ Γ (.apply fn args) ret
  | applyDir {Γ : Ctx} {name : Ident} {fd : FunDef} {args : List Expr} :
      Φ name = some fd →
      HasTypes Δ Φ Ψ Γ args (fd.params.map Prod.snd) →
      HasType Δ Φ Ψ Γ (.applyDir name args) fd.retTy
  | bin {Γ : Ctx} {op : BinOp} {e1 e2 : Expr} {τ1 τ2 τr : Ty} :
      BinOpHasType op τ1 τ2 τr →
      HasType Δ Φ Ψ Γ e1 τ1 →
      HasType Δ Φ Ψ Γ e2 τ2 →
      HasType Δ Φ Ψ Γ (.bin op e1 e2) τr
  | un {Γ : Ctx} {op : UnOp} {e : Expr} {τ1 τr : Ty} :
      UnOpHasType op τ1 τr →
      HasType Δ Φ Ψ Γ e τ1 →
      HasType Δ Φ Ψ Γ (.un op e) τr
  | let_ {Γ : Ctx} {x : Ident} {e1 e2 : Expr} {τ1 τ2 : Ty} :
      HasType Δ Φ Ψ Γ e1 τ1 →
      HasType Δ Φ Ψ (extendCtx Γ x τ1) e2 τ2 →
      HasType Δ Φ Ψ Γ (.let_ x e1 e2) τ2
  | if_ {Γ : Ctx} {c t e : Expr} {τ : Ty} :
      HasType Δ Φ Ψ Γ c .bool →
      HasType Δ Φ Ψ Γ t τ →
      HasType Δ Φ Ψ Γ e τ →
      HasType Δ Φ Ψ Γ (.if_ c t e) τ
  | while_ {Γ : Ctx} {c b : Expr} {τb : Ty} :
      HasType Δ Φ Ψ Γ c .bool →
      HasType Δ Φ Ψ Γ b τb →
      HasType Δ Φ Ψ Γ (.while_ c b) .void
  | match_ {Γ : Ctx} {scrut : Expr} {arms : List (Pat × Expr)} {τs τr : Ty} :
      HasType Δ Φ Ψ Γ scrut τs →
      ArmsHaveType Δ Φ Ψ Γ τs arms τr →
      HasType Δ Φ Ψ Γ (.match_ scrut arms) τr
  | makeData {Γ : Ctx} {adt : Ident} {tag : Nat} {es : List Expr} {flds : List Ty} :
      lookupVariant Δ adt tag = some flds →
      HasTypes Δ Φ Ψ Γ es flds →
      HasType Δ Φ Ψ Γ (.makeData adt tag es) (.adt adt)
  | getTag {Γ : Ctx} {e : Expr} {adt : Ident} :
      HasType Δ Φ Ψ Γ e (.adt adt) →
      HasType Δ Φ Ψ Γ (.getTag e) .int
  | cellNew {Γ : Ctx} {e : Expr} {τ : Ty} :
      HasType Δ Φ Ψ Γ e τ →
      HasType Δ Φ Ψ Γ (.cellNew e) (.cell τ)
  | cellGet {Γ : Ctx} {e : Expr} {τ : Ty} :
      HasType Δ Φ Ψ Γ e (.cell τ) →
      HasType Δ Φ Ψ Γ (.cellGet e) τ
  | cellSet {Γ : Ctx} {e1 e2 : Expr} {τ : Ty} :
      HasType Δ Φ Ψ Γ e1 (.cell τ) →
      HasType Δ Φ Ψ Γ e2 τ →
      HasType Δ Φ Ψ Γ (.cellSet e1 e2) .void
  | trap {Γ : Ctx} (t : Trap) (τ : Ty) :
      HasType Δ Φ Ψ Γ (.trap t) τ

inductive HasTypes (Δ : AdtEnv) (Φ : FunEnv) (Ψ : StoreTy) : Ctx → List Expr → List Ty → Prop where
  | nil {Γ : Ctx} : HasTypes Δ Φ Ψ Γ [] []
  | cons {Γ : Ctx} {e : Expr} {es : List Expr} {τ : Ty} {τs : List Ty} :
      HasType Δ Φ Ψ Γ e τ →
      HasTypes Δ Φ Ψ Γ es τs →
      HasTypes Δ Φ Ψ Γ (e :: es) (τ :: τs)

inductive ArmsHaveType (Δ : AdtEnv) (Φ : FunEnv) (Ψ : StoreTy) :
    Ctx → Ty → List (Pat × Expr) → Ty → Prop where
  | nil {Γ : Ctx} {τs τr : Ty} :
      ArmsHaveType Δ Φ Ψ Γ τs [] τr
  | cons {Γ : Ctx} {τs τr : Ty} {p : Pat} {body : Expr} {bs : List (Ident × Ty)}
      {rest : List (Pat × Expr)} :
      PatHasType Δ p τs bs →
      HasType Δ Φ Ψ (extendMany Γ bs) body τr →
      ArmsHaveType Δ Φ Ψ Γ τs rest τr →
      ArmsHaveType Δ Φ Ψ Γ τs ((p, body) :: rest) τr
end

/-- Top-level function table well-typedness: every function body is well-typed
    under its declared parameters and empty store typing (closed top-level defs). -/
def FunEnvTyped (Δ : AdtEnv) (Φ : FunEnv) : Prop :=
  ∀ name fd, Φ name = some fd →
    HasType Δ Φ [] (extendMany emptyCtx fd.params) fd.body fd.retTy

/-- Store well-typedness: `σ` and `Ψ` have equal length, and every cell holds a
    closed value of its declared type. -/
def StoreTyped (Δ : AdtEnv) (Φ : FunEnv) (Ψ : StoreTy) (σ : Store) : Prop :=
  σ.length = Ψ.length ∧
  ∀ (l : Loc) (τ : Ty), Ψ[l]? = some τ →
    ∃ v, σ[l]? = some v ∧ IsValue v ∧ HasType Δ Φ Ψ emptyCtx v τ

end CoreGeisha
