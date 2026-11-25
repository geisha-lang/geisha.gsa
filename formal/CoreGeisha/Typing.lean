import CoreGeisha.Syntax

/-!
# Core Geisha: Declarative Static Semantics, Capture Modes, and `IsSend`

Independent, syntax-directed typing rules `HasType Δ Φ Ψ Θ Γ e τ` for Core Geisha
(with admissible subsumption `typing_sub` proved in `Soundness.lean`), including:
- Coinductive thread-shareability `IsSend Δ τ` (supporting recursive ADTs while
  rejecting `Cell τ` and `local` closures)
- Capture-mode subtyping `ModeSub` / `TySub` (`shared <: local`, invariant `Cell`)
- Lexical capture checking on `shared` closures (`HasType.lam`)
- Concurrent `Task` typing (`taskRef`, `spawn`, `await`)
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

/-- Task typing `Θ : List Ty` assigning a result type to each spawned `TaskId`. -/
abbrev TaskTy := List Ty

/-- Task typing extension: `Θ'` extends `Θ` (monotone task pool growth). -/
def TaskExtends (Θ Θ' : TaskTy) : Prop :=
  Θ.length ≤ Θ'.length ∧ ∀ (tid : TaskId) (τ : Ty), Θ[tid]? = some τ → Θ'[tid]? = some τ

/-! ## Capture-Mode Subtyping (`shared <: local`) -/

/-- A `shared` closure (`Send`) can always be used where a `local` closure is
    expected, never vice versa. -/
inductive ModeSub : Mode → Mode → Prop where
  | refl (m : Mode) : ModeSub m m
  | sharedToLocal : ModeSub .shared .local

/- Structural subtyping induced by `ModeSub`.
   `Cell` and nominal `ADT` types are invariant; functions are covariant in
   capture mode and return type, and contravariant in parameter types. -/
mutual
inductive TySub : Ty → Ty → Prop where
  | void : TySub .void .void
  | int : TySub .int .int
  | bool : TySub .bool .bool
  | str : TySub .str .str
  | tuple {ts1 ts2 : List Ty} : TyListSub ts1 ts2 → TySub (.tuple ts1) (.tuple ts2)
  | fn {m1 m2 : Mode} {ps1 ps2 : List Ty} {r1 r2 : Ty} :
      ModeSub m1 m2 →
      TyListSub ps2 ps1 →
      TySub r1 r2 →
      TySub (.fn m1 ps1 r1) (.fn m2 ps2 r2)
  | adt (n : Ident) : TySub (.adt n) (.adt n)
  | cell (t : Ty) : TySub (.cell t) (.cell t)
  | task {t1 t2 : Ty} : TySub t1 t2 → TySub (.task t1) (.task t2)

inductive TyListSub : List Ty → List Ty → Prop where
  | nil : TyListSub [] []
  | cons {t1 t2 : Ty} {ts1 ts2 : List Ty} :
      TySub t1 t2 →
      TyListSub ts1 ts2 →
      TyListSub (t1 :: ts1) (t2 :: ts2)
end

/-! ## Coinductive `IsSend` Predicate (Supporting Recursive ADTs) -/

/- One-step `Send` membership relative to a candidate set `S` of `Send` ADTs.
   Notably, `Ty.cell _` and `Ty.fn .local _ _` have NO constructors here. -/
mutual
inductive TySendIn (S : Ident → Prop) : Ty → Prop where
  | void : TySendIn S .void
  | int : TySendIn S .int
  | bool : TySendIn S .bool
  | str : TySendIn S .str
  | tuple {ts : List Ty} : TyListSendIn S ts → TySendIn S (.tuple ts)
  | fnShared (ps : List Ty) (ret : Ty) : TySendIn S (.fn .shared ps ret)
  | adt {name : Ident} : S name → TySendIn S (.adt name)
  | task {t : Ty} : TySendIn S t → TySendIn S (.task t)

inductive TyListSendIn (S : Ident → Prop) : List Ty → Prop where
  | nil : TyListSendIn S []
  | cons {t : Ty} {ts : List Ty} :
      TySendIn S t →
      TyListSendIn S ts →
      TyListSendIn S (t :: ts)
end

/-- A set `S` of ADT names is closed under variant field types in `Δ`. -/
def AdtSendClosed (Δ : AdtEnv) (S : Ident → Prop) : Prop :=
  ∀ name, S name → ∃ defn, Δ name = some defn ∧
    ∀ v ∈ defn.variants, TyListSendIn S v.fields

/-- Greatest fixed point (Park coinduction): `τ` is safe to transfer across
    thread boundaries (`IsSend Δ τ`) iff `τ` belongs to `TySendIn S` for some
    `Δ`-closed set of ADTs `S`. -/
def IsSend (Δ : AdtEnv) (τ : Ty) : Prop :=
  ∃ S : Ident → Prop, AdtSendClosed Δ S ∧ TySendIn S τ

/-! ## Operators, Literals, and Patterns -/

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

/-! ## Syntax-Directed Expression Typing Judgment `Δ; Φ; Ψ; Θ; Γ ⊢ e : τ` -/

mutual
inductive HasType (Δ : AdtEnv) (Φ : FunEnv) (Ψ : StoreTy) (Θ : TaskTy) :
    Ctx → Expr → Ty → Prop where
  | lit {Γ : Ctx} {l : Lit} {τ : Ty} :
      LitHasType l τ →
      HasType Δ Φ Ψ Θ Γ (.lit l) τ
  | var {Γ : Ctx} {x : Ident} {τ0 τ : Ty} :
      Γ x = some τ0 →
      TySub τ0 τ →
      HasType Δ Φ Ψ Θ Γ (.var x) τ
  | loc {Γ : Ctx} {l : Loc} {τ : Ty} :
      Ψ[l]? = some τ →
      HasType Δ Φ Ψ Θ Γ (.loc l) (.cell τ)
  | taskRef {Γ : Ctx} {tid : TaskId} {τ0 τ : Ty} :
      Θ[tid]? = some τ0 →
      IsSend Δ τ0 →
      TySub τ0 τ →
      HasType Δ Φ Ψ Θ Γ (.taskRef tid) (.task τ)
  | tuple {Γ : Ctx} {es : List Expr} {τs : List Ty} :
      HasTypes Δ Φ Ψ Θ Γ es τs →
      HasType Δ Φ Ψ Θ Γ (.tuple es) (.tuple τs)
  | blockEmpty {Γ : Ctx} :
      HasType Δ Φ Ψ Θ Γ (.block []) .void
  | blockSingle {Γ : Ctx} {e : Expr} {τ : Ty} :
      HasType Δ Φ Ψ Θ Γ e τ →
      HasType Δ Φ Ψ Θ Γ (.block [e]) τ
  | blockCons {Γ : Ctx} {e1 e2 : Expr} {es : List Expr} {τ1 τ : Ty} :
      HasType Δ Φ Ψ Θ Γ e1 τ1 →
      HasType Δ Φ Ψ Θ Γ (.block (e2 :: es)) τ →
      HasType Δ Φ Ψ Θ Γ (.block (e1 :: e2 :: es)) τ
  | lam {Γ : Ctx} {m0 m : Mode} {ps : List (Ident × Ty)} {paramTys : List Ty}
      {ret0 ret : Ty} {body : Expr} :
      ModeSub m0 m →
      TyListSub paramTys (ps.map Prod.snd) →
      TySub ret0 ret →
      HasType Δ Φ Ψ Θ (extendMany Γ ps) body ret0 →
      (m0 = .shared →
        (∀ x ∈ freeVars (.lam .shared ps ret0 body), ∃ τx, Γ x = some τx ∧ IsSend Δ τx) ∧
        exprLocs body = []) →
      HasType Δ Φ Ψ Θ Γ (.lam m0 ps ret0 body) (.fn m paramTys ret)
  | apply {Γ : Ctx} {m : Mode} {fn : Expr} {args : List Expr}
      {paramTys : List Ty} {ret0 ret : Ty} :
      HasType Δ Φ Ψ Θ Γ fn (.fn m paramTys ret0) →
      HasTypes Δ Φ Ψ Θ Γ args paramTys →
      TySub ret0 ret →
      HasType Δ Φ Ψ Θ Γ (.apply fn args) ret
  | applyDir {Γ : Ctx} {name : Ident} {fd : FunDef} {args : List Expr} {ret : Ty} :
      Φ name = some fd →
      HasTypes Δ Φ Ψ Θ Γ args (fd.params.map Prod.snd) →
      TySub fd.retTy ret →
      HasType Δ Φ Ψ Θ Γ (.applyDir name args) ret
  | bin {Γ : Ctx} {op : BinOp} {e1 e2 : Expr} {τ1 τ2 τr : Ty} :
      BinOpHasType op τ1 τ2 τr →
      HasType Δ Φ Ψ Θ Γ e1 τ1 →
      HasType Δ Φ Ψ Θ Γ e2 τ2 →
      HasType Δ Φ Ψ Θ Γ (.bin op e1 e2) τr
  | un {Γ : Ctx} {op : UnOp} {e : Expr} {τ1 τr : Ty} :
      UnOpHasType op τ1 τr →
      HasType Δ Φ Ψ Θ Γ e τ1 →
      HasType Δ Φ Ψ Θ Γ (.un op e) τr
  | let_ {Γ : Ctx} {x : Ident} {e1 e2 : Expr} {τ1 τ2 : Ty} :
      HasType Δ Φ Ψ Θ Γ e1 τ1 →
      HasType Δ Φ Ψ Θ (extendCtx Γ x τ1) e2 τ2 →
      HasType Δ Φ Ψ Θ Γ (.let_ x e1 e2) τ2
  | if_ {Γ : Ctx} {c t e : Expr} {τ : Ty} :
      HasType Δ Φ Ψ Θ Γ c .bool →
      HasType Δ Φ Ψ Θ Γ t τ →
      HasType Δ Φ Ψ Θ Γ e τ →
      HasType Δ Φ Ψ Θ Γ (.if_ c t e) τ
  | while_ {Γ : Ctx} {c b : Expr} {τb : Ty} :
      HasType Δ Φ Ψ Θ Γ c .bool →
      HasType Δ Φ Ψ Θ Γ b τb →
      HasType Δ Φ Ψ Θ Γ (.while_ c b) .void
  | match_ {Γ : Ctx} {scrut : Expr} {arms : List (Pat × Expr)} {τs τr : Ty} :
      HasType Δ Φ Ψ Θ Γ scrut τs →
      ArmsHaveType Δ Φ Ψ Θ Γ τs arms τr →
      HasType Δ Φ Ψ Θ Γ (.match_ scrut arms) τr
  | makeData {Γ : Ctx} {adt : Ident} {tag : Nat} {es : List Expr} {flds : List Ty} :
      lookupVariant Δ adt tag = some flds →
      HasTypes Δ Φ Ψ Θ Γ es flds →
      HasType Δ Φ Ψ Θ Γ (.makeData adt tag es) (.adt adt)
  | getTag {Γ : Ctx} {e : Expr} {adt : Ident} :
      HasType Δ Φ Ψ Θ Γ e (.adt adt) →
      HasType Δ Φ Ψ Θ Γ (.getTag e) .int
  | cellNew {Γ : Ctx} {e : Expr} {τ : Ty} :
      HasType Δ Φ Ψ Θ Γ e τ →
      HasType Δ Φ Ψ Θ Γ (.cellNew e) (.cell τ)
  | cellGet {Γ : Ctx} {e : Expr} {τ0 τ : Ty} :
      HasType Δ Φ Ψ Θ Γ e (.cell τ0) →
      TySub τ0 τ →
      HasType Δ Φ Ψ Θ Γ (.cellGet e) τ
  | cellSet {Γ : Ctx} {e1 e2 : Expr} {τ : Ty} :
      HasType Δ Φ Ψ Θ Γ e1 (.cell τ) →
      HasType Δ Φ Ψ Θ Γ e2 τ →
      HasType Δ Φ Ψ Θ Γ (.cellSet e1 e2) .void
  | spawn {Γ : Ctx} {fn : Expr} {τ0 τ : Ty} :
      HasType Δ Φ Ψ Θ Γ fn (.fn .shared [] τ0) →
      IsSend Δ τ0 →
      TySub τ0 τ →
      HasType Δ Φ Ψ Θ Γ (.spawn fn) (.task τ)
  | await {Γ : Ctx} {e : Expr} {τ0 τ : Ty} :
      HasType Δ Φ Ψ Θ Γ e (.task τ0) →
      IsSend Δ τ0 →
      TySub τ0 τ →
      HasType Δ Φ Ψ Θ Γ (.await e) τ
  | trap {Γ : Ctx} (t : Trap) (τ : Ty) :
      HasType Δ Φ Ψ Θ Γ (.trap t) τ

inductive HasTypes (Δ : AdtEnv) (Φ : FunEnv) (Ψ : StoreTy) (Θ : TaskTy) :
    Ctx → List Expr → List Ty → Prop where
  | nil {Γ : Ctx} : HasTypes Δ Φ Ψ Θ Γ [] []
  | cons {Γ : Ctx} {e : Expr} {es : List Expr} {τ : Ty} {τs : List Ty} :
      HasType Δ Φ Ψ Θ Γ e τ →
      HasTypes Δ Φ Ψ Θ Γ es τs →
      HasTypes Δ Φ Ψ Θ Γ (e :: es) (τ :: τs)

inductive ArmsHaveType (Δ : AdtEnv) (Φ : FunEnv) (Ψ : StoreTy) (Θ : TaskTy) :
    Ctx → Ty → List (Pat × Expr) → Ty → Prop where
  | nil {Γ : Ctx} {τs τr : Ty} :
      ArmsHaveType Δ Φ Ψ Θ Γ τs [] τr
  | cons {Γ : Ctx} {τs τr : Ty} {p : Pat} {body : Expr} {bs : List (Ident × Ty)}
      {rest : List (Pat × Expr)} :
      PatHasType Δ p τs bs →
      HasType Δ Φ Ψ Θ (extendMany Γ bs) body τr →
      ArmsHaveType Δ Φ Ψ Θ Γ τs rest τr →
      ArmsHaveType Δ Φ Ψ Θ Γ τs ((p, body) :: rest) τr
end

/-- Top-level function table well-typedness: every function body is well-typed
    under its declared parameters and empty store/task typings (closed static defs). -/
def FunEnvTyped (Δ : AdtEnv) (Φ : FunEnv) : Prop :=
  ∀ name fd, Φ name = some fd →
    HasType Δ Φ [] [] (extendMany emptyCtx fd.params) fd.body fd.retTy

/-- Store well-typedness: `σ` and `Ψ` have equal length, and every cell holds a
    closed value of its declared type. -/
def StoreTyped (Δ : AdtEnv) (Φ : FunEnv) (Ψ : StoreTy) (Θ : TaskTy) (σ : Store) : Prop :=
  σ.length = Ψ.length ∧
  ∀ (l : Loc) (τ : Ty), Ψ[l]? = some τ →
    ∃ v, σ[l]? = some v ∧ IsValue v ∧ HasType Δ Φ Ψ Θ emptyCtx v τ

/-- Task pool well-typedness: `tasks` and `Θ` have equal length, and every
    task holds a closed expression of its declared result type. -/
def TasksTyped (Δ : AdtEnv) (Φ : FunEnv) (Ψ : StoreTy) (Θ : TaskTy) (tasks : List Expr) : Prop :=
  tasks.length = Θ.length ∧
  ∀ (tid : TaskId) (τ : Ty), Θ[tid]? = some τ →
    ∃ e, tasks[tid]? = some e ∧ HasType Δ Φ Ψ Θ emptyCtx e τ

end CoreGeisha
