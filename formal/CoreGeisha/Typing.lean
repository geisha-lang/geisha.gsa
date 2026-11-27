import CoreGeisha.Syntax

/-!
# Core Geisha: Declarative Static Semantics, Capture Modes, `IsSend`, and Concurrency Primitives

Independent, syntax-directed typing rules `HasType Δ Φ Ψ Θ Γ e τ` for Core Geisha
(with admissible subsumption `typing_sub` proved in `Soundness.lean`), including:
- Coinductive thread-shareability `IsSend Δ τ` (supporting recursive ADTs, `MVar τ`,
  `Chan τ`, and `Actor σ_ty` encapsulating `!Send` state `σ_ty`, while rejecting
  `Cell τ` and `local` closures)
- Capture-mode subtyping `ModeSub` / `TySub` (`shared <: local`, invariant `Cell`/`MVar`/`Chan`/`Actor`)
- Lexical capture checking on `shared` closures (`HasType.lam`)
- Concurrent `Task`, `MVar`, `Chan`, and sequential `Actor` typing
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

/-- Monotone list-typing extension (`ys` extends `xs`). -/
def ListExtends (xs ys : List Ty) : Prop :=
  xs.length ≤ ys.length ∧ ∀ (i : Nat) (τ : Ty), xs[i]? = some τ → ys[i]? = some τ

/-- Store typing `Ψ : List Ty` assigning a type to each allocated `Cell` location. -/
abbrev StoreTy := List Ty

/-- Store typing extension: `Ψ'` extends `Ψ` (monotone heap growth). -/
abbrev StoreExtends (Ψ Ψ' : StoreTy) : Prop := ListExtends Ψ Ψ'

/-- Concurrent pool typing `Θ`: assigns payload/state types to allocated `Task`,
    `MVar`, `Chan`, and `Actor` handles. -/
structure TaskTy where
  tasks  : List Ty := []
  mvars  : List Ty := []
  chans  : List Ty := []
  actors : List Ty := []
  deriving Repr

/-- Empty concurrent pool typing. -/
def emptyTaskTy : TaskTy := {}

/-- Monotone growth of concurrent pool typing `Θ`. -/
structure TaskExtends (Θ Θ' : TaskTy) : Prop where
  tasks  : ListExtends Θ.tasks Θ'.tasks
  mvars  : ListExtends Θ.mvars Θ'.mvars
  chans  : ListExtends Θ.chans Θ'.chans
  actors : ListExtends Θ.actors Θ'.actors

/-! ## Capture-Mode Subtyping (`shared <: local`) -/

/-- A `shared` closure (`Send`) can always be used where a `local` closure is
    expected, never vice versa. -/
inductive ModeSub : Mode → Mode → Prop where
  | refl (m : Mode) : ModeSub m m
  | sharedToLocal : ModeSub .shared .local

/- Structural subtyping induced by `ModeSub`.
   `Cell`, `MVar`, `Chan`, `Actor`, and nominal `ADT` types are invariant;
   functions are covariant in capture mode and return type, and contravariant
   in parameter types; `Task` is covariant in its immutable result type. -/
mutual
inductive TySub : Ty → Ty → Prop where
  | void : TySub .void .void
  | int : TySub .int .int
  | int64 : TySub .int64 .int64
  | float : TySub .float .float
  | float32 : TySub .float32 .float32
  | bool : TySub .bool .bool
  | char : TySub .char .char
  | str : TySub .str .str
  | ptr : TySub .ptr .ptr
  | scopedPtr : TySub .scopedPtr .scopedPtr
  | arena : TySub .arena .arena
  | foreignPtr : TySub .foreignPtr .foreignPtr
  | atomicInt : TySub .atomicInt .atomicInt
  | tuple {ts1 ts2 : List Ty} : TyListSub ts1 ts2 → TySub (.tuple ts1) (.tuple ts2)
  | fn {m1 m2 : Mode} {ps1 ps2 : List Ty} {r1 r2 : Ty} :
      ModeSub m1 m2 →
      TyListSub ps2 ps1 →
      TySub r1 r2 →
      TySub (.fn m1 ps1 r1) (.fn m2 ps2 r2)
  | adt (n : Ident) : TySub (.adt n) (.adt n)
  | cell (t : Ty) : TySub (.cell t) (.cell t)
  | mutArray (t : Ty) : TySub (.mutArray t) (.mutArray t)
  | immArray {t1 t2 : Ty} : TySub t1 t2 → TySub (.immArray t1) (.immArray t2)
  | task {t1 t2 : Ty} : TySub t1 t2 → TySub (.task t1) (.task t2)
  | mvar (t : Ty) : TySub (.mvar t) (.mvar t)
  | chan (t : Ty) : TySub (.chan t) (.chan t)
  | actor (t : Ty) : TySub (.actor t) (.actor t)

inductive TyListSub : List Ty → List Ty → Prop where
  | nil : TyListSub [] []
  | cons {t1 t2 : Ty} {ts1 ts2 : List Ty} :
      TySub t1 t2 →
      TyListSub ts1 ts2 →
      TyListSub (t1 :: ts1) (t2 :: ts2)
end

/-! ## Coinductive `IsSend` Predicate (Supporting Recursive ADTs & `!Send`-State Actors) -/

/- One-step `Send` membership relative to a candidate set `S` of `Send` ADTs.
   - `Ty.cell _`, `Ty.mutArray _`, `Ty.ptr`, `Ty.scopedPtr`, `Ty.arena`, `Ty.foreignPtr`,
     and `Ty.fn .local _ _` have NO constructors (`!Send`, matching `src/infer.gsa`).
   - `Ty.mvar t`, `Ty.chan t`, `Ty.task t`, and `Ty.immArray t` require `TySendIn S t`.
   - `Ty.actor s` is unconditionally `Send` even when `s` is `!Send` (e.g. `Cell`!),
     because `s` never leaves the actor's dedicated sequential thread. -/
mutual
inductive TySendIn (S : Ident → Prop) : Ty → Prop where
  | void : TySendIn S .void
  | int : TySendIn S .int
  | int64 : TySendIn S .int64
  | float : TySendIn S .float
  | float32 : TySendIn S .float32
  | bool : TySendIn S .bool
  | char : TySendIn S .char
  | str : TySendIn S .str
  | atomicInt : TySendIn S .atomicInt
  | tuple {ts : List Ty} : TyListSendIn S ts → TySendIn S (.tuple ts)
  | fnShared (ps : List Ty) (ret : Ty) : TySendIn S (.fn .shared ps ret)
  | adt {name : Ident} : S name → TySendIn S (.adt name)
  | immArray {t : Ty} : TySendIn S t → TySendIn S (.immArray t)
  | task {t : Ty} : TySendIn S t → TySendIn S (.task t)
  | mvar {t : Ty} : TySendIn S t → TySendIn S (.mvar t)
  | chan {t : Ty} : TySendIn S t → TySendIn S (.chan t)
  | actor (s : Ty) : TySendIn S (.actor s)

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

/-! ## Operators, Literals, Concurrency Handles/Primitives, and Patterns -/

/-- Literal typing judgment. -/
inductive LitHasType : Lit → Ty → Prop where
  | int (n : Int32) : LitHasType (.int n) .int
  | int64 (n : Int64) : LitHasType (.int64 n) .int64
  | floatBits (bits : UInt64) : LitHasType (.floatBits bits) .float
  | float32Bits (bits : UInt32) : LitHasType (.float32Bits bits) .float32
  | bool (b : Bool) : LitHasType (.bool b) .bool
  | char (c : UInt32) : LitHasType (.char c) .char
  | str (s : String) : LitHasType (.str s) .str
  | unit : LitHasType .unit .void

/-- Unary operator typing judgment. -/
inductive UnOpHasType : UnOp → Ty → Ty → Prop where
  | not : UnOpHasType .not .bool .bool
  | neg : UnOpHasType .neg .int .int
  | bitNot : UnOpHasType .bitNot .int .int
  | neg64 : UnOpHasType .neg64 .int64 .int64
  | bitNot64 : UnOpHasType .bitNot64 .int64 .int64
  | negFloat : UnOpHasType .negFloat .float .float
  | negFloat32 : UnOpHasType .negFloat32 .float32 .float32

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
  | shlInt : BinOpHasType .shlInt .int .int .int
  | shrInt : BinOpHasType .shrInt .int .int .int
  | ushrInt : BinOpHasType .ushrInt .int .int .int
  | eqInt : BinOpHasType .eqInt .int .int .bool
  | neInt : BinOpHasType .neInt .int .int .bool
  | ltInt : BinOpHasType .ltInt .int .int .bool
  | leInt : BinOpHasType .leInt .int .int .bool
  | gtInt : BinOpHasType .gtInt .int .int .bool
  | geInt : BinOpHasType .geInt .int .int .bool
  | add64 : BinOpHasType .add64 .int64 .int64 .int64
  | sub64 : BinOpHasType .sub64 .int64 .int64 .int64
  | mul64 : BinOpHasType .mul64 .int64 .int64 .int64
  | div64 : BinOpHasType .div64 .int64 .int64 .int64
  | rem64 : BinOpHasType .rem64 .int64 .int64 .int64
  | bitAnd64 : BinOpHasType .bitAnd64 .int64 .int64 .int64
  | bitOr64 : BinOpHasType .bitOr64 .int64 .int64 .int64
  | bitXor64 : BinOpHasType .bitXor64 .int64 .int64 .int64
  | shl64 : BinOpHasType .shl64 .int64 .int .int64
  | shr64 : BinOpHasType .shr64 .int64 .int .int64
  | ushr64 : BinOpHasType .ushr64 .int64 .int .int64
  | eq64 : BinOpHasType .eq64 .int64 .int64 .bool
  | ne64 : BinOpHasType .ne64 .int64 .int64 .bool
  | lt64 : BinOpHasType .lt64 .int64 .int64 .bool
  | le64 : BinOpHasType .le64 .int64 .int64 .bool
  | gt64 : BinOpHasType .gt64 .int64 .int64 .bool
  | ge64 : BinOpHasType .ge64 .int64 .int64 .bool
  | addFloat : BinOpHasType .addFloat .float .float .float
  | subFloat : BinOpHasType .subFloat .float .float .float
  | mulFloat : BinOpHasType .mulFloat .float .float .float
  | divFloat : BinOpHasType .divFloat .float .float .float
  | eqFloat : BinOpHasType .eqFloat .float .float .bool
  | neFloat : BinOpHasType .neFloat .float .float .bool
  | ltFloat : BinOpHasType .ltFloat .float .float .bool
  | leFloat : BinOpHasType .leFloat .float .float .bool
  | gtFloat : BinOpHasType .gtFloat .float .float .bool
  | geFloat : BinOpHasType .geFloat .float .float .bool
  | addF32 : BinOpHasType .addF32 .float32 .float32 .float32
  | subF32 : BinOpHasType .subF32 .float32 .float32 .float32
  | mulF32 : BinOpHasType .mulF32 .float32 .float32 .float32
  | divF32 : BinOpHasType .divF32 .float32 .float32 .float32
  | eqF32 : BinOpHasType .eqF32 .float32 .float32 .bool
  | neF32 : BinOpHasType .neF32 .float32 .float32 .bool
  | ltF32 : BinOpHasType .ltF32 .float32 .float32 .bool
  | leF32 : BinOpHasType .leF32 .float32 .float32 .bool
  | gtF32 : BinOpHasType .gtF32 .float32 .float32 .bool
  | geF32 : BinOpHasType .geF32 .float32 .float32 .bool
  | eqBool : BinOpHasType .eqBool .bool .bool .bool
  | neBool : BinOpHasType .neBool .bool .bool .bool
  | bitAndBool : BinOpHasType .bitAndBool .bool .bool .bool
  | bitOrBool : BinOpHasType .bitOrBool .bool .bool .bool
  | bitXorBool : BinOpHasType .bitXorBool .bool .bool .bool
  | eqChar : BinOpHasType .eqChar .char .char .bool
  | neChar : BinOpHasType .neChar .char .char .bool
  | ltChar : BinOpHasType .ltChar .char .char .bool
  | leChar : BinOpHasType .leChar .char .char .bool
  | gtChar : BinOpHasType .gtChar .char .char .bool
  | geChar : BinOpHasType .geChar .char .char .bool
  | eqStr : BinOpHasType .eqStr .str .str .bool
  | neStr : BinOpHasType .neStr .str .str .bool
  | ltStr : BinOpHasType .ltStr .str .str .bool
  | leStr : BinOpHasType .leStr .str .str .bool
  | gtStr : BinOpHasType .gtStr .str .str .bool
  | geStr : BinOpHasType .geStr .str .str .bool
  | strConcat : BinOpHasType .strConcat .str .str .str
  | and : BinOpHasType .and .bool .bool .bool
  | or : BinOpHasType .or .bool .bool .bool

/-- Runtime `MVar` / `Chan` / `Actor` handle typing judgment. -/
inductive SyncRefHasType (Δ : AdtEnv) (Θ : TaskTy) : SyncKind → Nat → Ty → Prop where
  | mvar {mid : Nat} {τ : Ty} :
      Θ.mvars[mid]? = some τ →
      IsSend Δ τ →
      SyncRefHasType Δ Θ .mvar mid (.mvar τ)
  | chan {cid : Nat} {τ : Ty} :
      Θ.chans[cid]? = some τ →
      IsSend Δ τ →
      SyncRefHasType Δ Θ .chan cid (.chan τ)
  | actor {aid : Nat} {σ_ty : Ty} :
      Θ.actors[aid]? = some σ_ty →
      SyncRefHasType Δ Θ .actor aid (.actor σ_ty)

/-- Typing rules for `MVar`, `Chan`, and sequential `Actor` primitives (`std.sync`, `std.actor`).
    Crucially:
    - `actorSpawn` requires a `shared` initializer `() => s`, while `s` need NOT be `IsSend`.
    - `actorCall` requires a `shared` handler `s => r` and `IsSend Δ r`, while `s` need NOT be `IsSend`.
    - `actorSend` requires a `shared` handler `s => Void`, while `s` need NOT be `IsSend`. -/
inductive ConcPrimHasType (Δ : AdtEnv) : ConcPrim → List Ty → Ty → Prop where
  | mvarNew {τ : Ty} :
      IsSend Δ τ →
      ConcPrimHasType Δ .mvarNew [τ] (.mvar τ)
  | mvarEmpty {τ : Ty} :
      IsSend Δ τ →
      ConcPrimHasType Δ (.mvarEmpty τ) [] (.mvar τ)
  | mvarTake {τ : Ty} :
      IsSend Δ τ →
      ConcPrimHasType Δ .mvarTake [.mvar τ] τ
  | mvarPut {τ : Ty} :
      IsSend Δ τ →
      ConcPrimHasType Δ .mvarPut [.mvar τ, τ] .void
  | chanNew {τ : Ty} :
      IsSend Δ τ →
      ConcPrimHasType Δ (.chanNew τ) [.int] (.chan τ)
  | chanSend {τ : Ty} :
      IsSend Δ τ →
      ConcPrimHasType Δ .chanSend [.chan τ, τ] .bool
  | chanRecv {optAdt : Ident} {τ : Ty} :
      IsSend Δ τ →
      lookupVariant Δ optAdt 0 = some [] →
      lookupVariant Δ optAdt 1 = some [τ] →
      ConcPrimHasType Δ (.chanRecv optAdt) [.chan τ] (.adt optAdt)
  | chanClose {τ : Ty} :
      ConcPrimHasType Δ .chanClose [.chan τ] .void
  | actorSpawn {σ_ty : Ty} :
      ConcPrimHasType Δ .actorSpawn [.fn .shared [] σ_ty] (.actor σ_ty)
  | actorCall {σ_ty r_ty : Ty} :
      IsSend Δ r_ty →
      ConcPrimHasType Δ .actorCall [.actor σ_ty, .fn .shared [σ_ty] r_ty] (.task r_ty)
  | actorSend {σ_ty : Ty} :
      ConcPrimHasType Δ .actorSend [.actor σ_ty, .fn .shared [σ_ty] .void] .void

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
      Θ.tasks[tid]? = some τ0 →
      IsSend Δ τ0 →
      TySub τ0 τ →
      HasType Δ Φ Ψ Θ Γ (.taskRef tid) (.task τ)
  | syncRef {Γ : Ctx} {k : SyncKind} {id : Nat} {τ : Ty} :
      SyncRefHasType Δ Θ k id τ →
      HasType Δ Φ Ψ Θ Γ (.syncRef k id) τ
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
  | concPrim {Γ : Ctx} {op : ConcPrim} {args : List Expr}
      {argTys : List Ty} {ret0 ret : Ty} :
      ConcPrimHasType Δ op argTys ret0 →
      HasTypes Δ Φ Ψ Θ Γ args argTys →
      TySub ret0 ret →
      HasType Δ Φ Ψ Θ Γ (.concPrim op args) ret
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
    under its declared parameters and empty store/pool typings (closed static defs). -/
def FunEnvTyped (Δ : AdtEnv) (Φ : FunEnv) : Prop :=
  ∀ name fd, Φ name = some fd →
    HasType Δ Φ [] emptyTaskTy (extendMany emptyCtx fd.params) fd.body fd.retTy

/-- Store well-typedness: `σ` and `Ψ` have equal length, and every cell holds a
    closed value of its declared type. -/
def StoreTyped (Δ : AdtEnv) (Φ : FunEnv) (Ψ : StoreTy) (Θ : TaskTy) (σ : Store) : Prop :=
  σ.length = Ψ.length ∧
  ∀ (l : Loc) (τ : Ty), Ψ[l]? = some τ →
    ∃ v, σ[l]? = some v ∧ IsValue v ∧ HasType Δ Φ Ψ Θ emptyCtx v τ

end CoreGeisha
