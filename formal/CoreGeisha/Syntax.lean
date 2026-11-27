/-!
# Core Geisha: Abstract Syntax, Types, Modes, Concurrency Handles, Values, and Store

This module defines the formal abstract syntax of **Core Geisha**, closely
mirroring `src/core.gsa` (`Term`, `Type`, `Pattern`, `AdtInfo`, `FunDef`) in the
self-hosted Geisha compiler (`geisha.gsa`), while making closure capture modes
(`Mode`), concurrent `Task` / `MVar` / `Chan` / `Actor` handles and primitives,
mutable store locations (`Cell`), and runtime traps explicit.

## Alignment with `src/core.gsa`

| `src/core.gsa` | `CoreGeisha.Syntax` | Notes |
| --- | --- | --- |
| `TyVoid`, `TyCon "Int"/"Bool"/"String"` | `Ty.void`, `Ty.int`, `Ty.bool`, `Ty.str` | Monomorphic core types |
| `TyCon "$Local"` / `TyCon "$Shared"` | `Mode.local`, `Mode.shared` | Closure capture modes |
| `TyTuple`, `TyArr` | `Ty.tuple`, `Ty.fn` | Mode-annotated multi-arg functions |
| `TyCon adtName` | `Ty.adt name` | Monomorphized ADTs |
| `TyComp (TyCon "Cell") t` | `Ty.cell t` | Thread-local mutable heap cells (`!Send`) |
| `TyComp (TyCon "Task") t` | `Ty.task t` | Concurrent task handles (`Send` iff `t : Send`) |
| `TyComp (TyCon "MVar"/"Chan"/"Actor") t` | `Ty.mvar t`, `Ty.chan t`, `Ty.actor t` | Synchronized boxes, MPMC channels, sequential actors |
| `TmLit`, `TmVar`, `TmTuple`, `TmBlock` | `Expr.lit`, `Expr.var`, `Expr.tuple`, `Expr.block` | Core expressions |
| `TmMakeCls`, `TmApplyCls`, `TmApplyDir` | `Expr.lam`, `Expr.apply`, `Expr.applyDir` | Strict multi-arg closures & direct calls |
| `TmBin`, `TmUn`, `TmLet`, `TmIf`, `TmWhile` | `Expr.bin`, `Expr.un`, `Expr.let_`, `Expr.if_`, `Expr.while_` | Control flow & ops |
| `TmMatch`, `TmMakeData`, `TmGetTag` | `Expr.match_`, `Expr.makeData`, `Expr.getTag` | ADT construction & pattern matching |
| `cellNew`, `cellGet`, `cellSet` | `Expr.cellNew`, `Expr.cellGet`, `Expr.cellSet` | Explicit mutable store ops |
| `__concTaskSpawn`, `__concTaskAwait` | `Expr.spawn`, `Expr.await` | Concurrent task fork/join |
| `__concMVar*`, `__concChan*`, `__concActor*` | `Expr.concPrim` | `MVar`, `Chan`, and thread-pinned `Actor` primitives |
-/

namespace CoreGeisha

/-- Identifiers for variables, top-level functions, and ADT names. -/
abbrev Ident := String

/-- Store locations for mutable `Cell` values. -/
abbrev Loc := Nat

/-- Runtime task identifiers for concurrent `Task` values. -/
abbrev TaskId := Nat

/-- Runtime handle kind for `MVar`, `Chan`, and `Actor` values. -/
inductive SyncKind where
  | mvar : SyncKind
  | chan : SyncKind
  | actor : SyncKind
  deriving Repr, BEq, DecidableEq

/-- Closure capture mode:
    - `local`: may capture thread-local `!Send` state (`Cell`, `local` closures); cannot cross threads.
    - `shared`: captures only `IsSend` values (`Send`); safe to `spawn` or send across threads. -/
inductive Mode where
  | local : Mode
  | shared : Mode
  deriving Repr, BEq, DecidableEq

/-- Core Geisha monomorphic types (post-monomorphization, matching `src/core.gsa` & `src/codegen.gsa`). -/
inductive Ty where
  | void : Ty
  | int : Ty
  | int64 : Ty
  | float : Ty
  | float32 : Ty
  | bool : Ty
  | char : Ty
  | str : Ty
  | ptr : Ty
  | scopedPtr : Ty
  | arena : Ty
  | foreignPtr : Ty
  | atomicInt : Ty
  | tuple : List Ty → Ty
  | fn : Mode → List Ty → Ty → Ty
  | adt : Ident → Ty
  | cell : Ty → Ty
  | mutArray : Ty → Ty
  | immArray : Ty → Ty
  | task : Ty → Ty
  | mvar : Ty → Ty
  | chan : Ty → Ty
  | actor : Ty → Ty
  deriving Repr, BEq

/-- Built-in synchronization and sequential actor operations (`std.sync`, `std.actor`). -/
inductive ConcPrim where
  | mvarNew : ConcPrim
  | mvarEmpty : Ty → ConcPrim
  | mvarTake : ConcPrim
  | mvarPut : ConcPrim
  | chanNew : Ty → ConcPrim
  | chanSend : ConcPrim
  | chanRecv : Ident → ConcPrim
  | chanClose : ConcPrim
  | actorSpawn : ConcPrim
  | actorCall : ConcPrim
  | actorSend : ConcPrim
  deriving Repr, BEq

/-- Core literals (`Lit` in `src/ast.gsa`; IEEE-754 floats stored as exact bit patterns). -/
inductive Lit where
  | int : Int32 → Lit
  | int64 : Int64 → Lit
  | floatBits : UInt64 → Lit
  | float32Bits : UInt32 → Lit
  | bool : Bool → Lit
  | char : UInt32 → Lit
  | str : String → Lit
  | unit : Lit
  deriving Repr, BEq, DecidableEq

/-- Unary operators (`UnOp` in `src/ast.gsa`, monomorphized by operand type). -/
inductive UnOp where
  | not : UnOp         -- `!` on Bool
  | neg : UnOp         -- unary `-` on Int (wrapping 32-bit)
  | bitNot : UnOp      -- `~` on Int
  | neg64 : UnOp       -- unary `-` on Int64 (wrapping 64-bit)
  | bitNot64 : UnOp    -- `~` on Int64
  | negFloat : UnOp    -- unary `-` on Float
  | negFloat32 : UnOp  -- unary `-` on Float32
  | intToI64 : UnOp    -- sign-extending Int -> Int64 cast
  | i64ToInt : UnOp    -- truncating Int64 -> Int cast
  deriving Repr, BEq, DecidableEq

/-- Binary operators (`BinOp` in `src/ast.gsa`, monomorphized by operand type). -/
inductive BinOp where
  | add : BinOp
  | sub : BinOp
  | mul : BinOp
  | div : BinOp        -- traps on divisor == 0
  | rem : BinOp        -- traps on divisor == 0
  | bitAnd : BinOp
  | bitOr : BinOp
  | bitXor : BinOp
  | shlInt : BinOp
  | shrInt : BinOp
  | ushrInt : BinOp
  | eqInt : BinOp
  | neInt : BinOp
  | ltInt : BinOp
  | leInt : BinOp
  | gtInt : BinOp
  | geInt : BinOp
  | add64 : BinOp
  | sub64 : BinOp
  | mul64 : BinOp
  | div64 : BinOp      -- traps on divisor == 0
  | rem64 : BinOp      -- traps on divisor == 0
  | bitAnd64 : BinOp
  | bitOr64 : BinOp
  | bitXor64 : BinOp
  | shl64 : BinOp      -- (Int64, Int) -> Int64
  | shr64 : BinOp      -- (Int64, Int) -> Int64
  | ushr64 : BinOp     -- (Int64, Int) -> Int64
  | eq64 : BinOp
  | ne64 : BinOp
  | lt64 : BinOp
  | le64 : BinOp
  | gt64 : BinOp
  | ge64 : BinOp
  | addFloat : BinOp
  | subFloat : BinOp
  | mulFloat : BinOp
  | divFloat : BinOp
  | eqFloat : BinOp
  | neFloat : BinOp
  | ltFloat : BinOp
  | leFloat : BinOp
  | gtFloat : BinOp
  | geFloat : BinOp
  | addF32 : BinOp
  | subF32 : BinOp
  | mulF32 : BinOp
  | divF32 : BinOp
  | eqF32 : BinOp
  | neF32 : BinOp
  | ltF32 : BinOp
  | leF32 : BinOp
  | gtF32 : BinOp
  | geF32 : BinOp
  | eqBool : BinOp
  | neBool : BinOp
  | bitAndBool : BinOp
  | bitOrBool : BinOp
  | bitXorBool : BinOp
  | eqChar : BinOp
  | neChar : BinOp
  | ltChar : BinOp
  | leChar : BinOp
  | gtChar : BinOp
  | geChar : BinOp
  | eqStr : BinOp
  | neStr : BinOp
  | ltStr : BinOp
  | leStr : BinOp
  | gtStr : BinOp
  | geStr : BinOp
  | strConcat : BinOp
  | and : BinOp        -- short-circuit logical &&
  | or : BinOp         -- short-circuit logical ||
  deriving Repr, BEq, DecidableEq

/-- Patterns (`Pattern` in `src/ast.gsa`, normalized for Core IR). -/
inductive Pat where
  | wild : Pat
  | var : Ident → Pat
  | lit : Lit → Pat
  | tuple : List Pat → Pat
  | ctor : Ident → Nat → List Pat → Pat
  deriving Repr

/-- Explicit runtime traps (defined abnormal termination, distinct from UB/stuck). -/
inductive Trap where
  | divByZero : Trap
  | matchFailure : Trap
  | hostTrap : Trap
  deriving Repr, BEq, DecidableEq

/-- Core Geisha expressions, mirroring `Term` in `src/core.gsa` plus runtime
    locations, concurrency handles, `spawn`/`await`, `concPrim`, and traps. -/
inductive Expr where
  | lit : Lit → Expr
  | var : Ident → Expr
  | loc : Loc → Expr
  | taskRef : TaskId → Expr
  | syncRef : SyncKind → Nat → Expr
  | tuple : List Expr → Expr
  | block : List Expr → Expr
  | lam : Mode → List (Ident × Ty) → Ty → Expr → Expr
  | apply : Expr → List Expr → Expr
  | applyDir : Ident → List Expr → Expr
  | bin : BinOp → Expr → Expr → Expr
  | un : UnOp → Expr → Expr
  | let_ : Ident → Expr → Expr → Expr
  | if_ : Expr → Expr → Expr → Expr
  | while_ : Expr → Expr → Expr
  | match_ : Expr → List (Pat × Expr) → Expr
  | makeData : Ident → Nat → List Expr → Expr
  | getTag : Expr → Expr
  | cellNew : Expr → Expr
  | cellGet : Expr → Expr
  | cellSet : Expr → Expr → Expr
  | spawn : Expr → Expr
  | await : Expr → Expr
  | concPrim : ConcPrim → List Expr → Expr
  | trap : Trap → Expr
  deriving Repr

/-- Variant definition inside an ADT: constructor tag index and payload field types. -/
structure VariantDef where
  tag : Nat
  fields : List Ty
  deriving Repr

/-- Monomorphic ADT definition (`AdtInfo` in `src/infer.gsa` / `src/core.gsa`). -/
structure AdtDef where
  name : Ident
  variants : List VariantDef
  deriving Repr

/-- Top-level function definition (`FunDef` in `src/core.gsa`). -/
structure FunDef where
  name : Ident
  params : List (Ident × Ty)
  retTy : Ty
  body : Expr
  deriving Repr

/-- Host/runtime builtin or C `extern` declaration (`ExternDef` / prelude intrinsics). -/
structure ExternDecl where
  name : Ident
  params : List (Ident × Ty)
  retTy : Ty
  deriving Repr

/-- Lower an `ExternDecl` into a typed `FunDef` stub at the host boundary. -/
def ExternDecl.toFunDef (ed : ExternDecl) : FunDef :=
  { name := ed.name, params := ed.params, retTy := ed.retTy, body := .trap .hostTrap }

/-- Global ADT registry `Δ`. -/
abbrev AdtEnv := Ident → Option AdtDef

/-- Global top-level function table `Φ`. -/
abbrev FunEnv := Ident → Option FunDef

/-- Look up a variant by ADT name and tag index. -/
def lookupVariant (Δ : AdtEnv) (adtName : Ident) (tag : Nat) : Option (List Ty) :=
  match Δ adtName with
  | none => none
  | some defn =>
    match defn.variants.find? (fun v => v.tag == tag) with
    | none => none
    | some v => some v.fields

/-- Values: irreducible expressions produced by evaluation. -/
inductive IsValue : Expr → Prop where
  | lit (l : Lit) : IsValue (.lit l)
  | loc (l : Loc) : IsValue (.loc l)
  | taskRef (tid : TaskId) : IsValue (.taskRef tid)
  | syncRef (k : SyncKind) (id : Nat) : IsValue (.syncRef k id)
  | lam (m : Mode) (ps : List (Ident × Ty)) (ret : Ty) (body : Expr) :
      IsValue (.lam m ps ret body)
  | tuple {es : List Expr} : (∀ e ∈ es, IsValue e) → IsValue (.tuple es)
  | makeData (adt : Ident) (tag : Nat) {es : List Expr} :
      (∀ e ∈ es, IsValue e) → IsValue (.makeData adt tag es)

/-- Mutable heap store `σ`: maps allocated `Loc` indices to stored values. -/
abbrev Store := List Expr

/-- Names bound by a pattern. -/
def patBoundNames : Pat → List Ident
  | .wild => []
  | .var x => [x]
  | .lit _ => []
  | .tuple ps => ps.foldr (fun p acc => patBoundNames p ++ acc) []
  | .ctor _ _ ps => ps.foldr (fun p acc => patBoundNames p ++ acc) []

/- Free lexical variables occurring in an expression. -/
mutual
def freeVars : Expr → List Ident
  | .lit _ => []
  | .var x => [x]
  | .loc _ => []
  | .taskRef _ => []
  | .syncRef _ _ => []
  | .tuple es => freeVarsList es
  | .block es => freeVarsList es
  | .lam _ ps _ body => (freeVars body).filter (fun z => !(ps.any (fun p => p.1 == z)))
  | .apply fn args => freeVars fn ++ freeVarsList args
  | .applyDir _ args => freeVarsList args
  | .bin _ e1 e2 => freeVars e1 ++ freeVars e2
  | .un _ e => freeVars e
  | .let_ y e1 e2 => freeVars e1 ++ (freeVars e2).filter (fun z => z != y)
  | .if_ c t e => freeVars c ++ freeVars t ++ freeVars e
  | .while_ c b => freeVars c ++ freeVars b
  | .match_ scrut arms => freeVars scrut ++ freeVarsArms arms
  | .makeData _ _ es => freeVarsList es
  | .getTag e => freeVars e
  | .cellNew e => freeVars e
  | .cellGet e => freeVars e
  | .cellSet e1 e2 => freeVars e1 ++ freeVars e2
  | .spawn e => freeVars e
  | .await e => freeVars e
  | .concPrim _ args => freeVarsList args
  | .trap _ => []

def freeVarsList : List Expr → List Ident
  | [] => []
  | e :: es => freeVars e ++ freeVarsList es

def freeVarsArms : List (Pat × Expr) → List Ident
  | [] => []
  | (p, body) :: rest =>
    (freeVars body).filter (fun z => !((patBoundNames p).contains z)) ++ freeVarsArms rest
end

/- All runtime `Cell` heap locations syntactically embedded in an expression
   (including inside closure bodies and ADT/tuple payloads). -/
mutual
def exprLocs : Expr → List Loc
  | .lit _ => []
  | .var _ => []
  | .loc l => [l]
  | .taskRef _ => []
  | .syncRef _ _ => []
  | .tuple es => exprLocsList es
  | .block es => exprLocsList es
  | .lam _ _ _ body => exprLocs body
  | .apply fn args => exprLocs fn ++ exprLocsList args
  | .applyDir _ args => exprLocsList args
  | .bin _ e1 e2 => exprLocs e1 ++ exprLocs e2
  | .un _ e => exprLocs e
  | .let_ _ e1 e2 => exprLocs e1 ++ exprLocs e2
  | .if_ c t e => exprLocs c ++ exprLocs t ++ exprLocs e
  | .while_ c b => exprLocs c ++ exprLocs b
  | .match_ scrut arms => exprLocs scrut ++ exprLocsArms arms
  | .makeData _ _ es => exprLocsList es
  | .getTag e => exprLocs e
  | .cellNew e => exprLocs e
  | .cellGet e => exprLocs e
  | .cellSet e1 e2 => exprLocs e1 ++ exprLocs e2
  | .spawn e => exprLocs e
  | .await e => exprLocs e
  | .concPrim _ args => exprLocsList args
  | .trap _ => []

def exprLocsList : List Expr → List Loc
  | [] => []
  | e :: es => exprLocs e ++ exprLocsList es

def exprLocsArms : List (Pat × Expr) → List Loc
  | [] => []
  | (_, body) :: rest => exprLocs body ++ exprLocsArms rest
end

/- Capture-avoiding substitution of a CLOSED value `v` for `x` in `e`.
   Because `v` is closed during CBV evaluation, shadowing stops substitution
   without needing α-renaming. -/
mutual
def subst (x : Ident) (v : Expr) : Expr → Expr
  | .lit l => .lit l
  | .var y => if y == x then v else .var y
  | .loc l => .loc l
  | .taskRef tid => .taskRef tid
  | .syncRef k id => .syncRef k id
  | .tuple es => .tuple (substList x v es)
  | .block es => .block (substList x v es)
  | .lam m ps ret body =>
    if ps.any (fun p => p.1 == x) then
      .lam m ps ret body
    else
      .lam m ps ret (subst x v body)
  | .apply fn args => .apply (subst x v fn) (substList x v args)
  | .applyDir fn args => .applyDir fn (substList x v args)
  | .bin op e1 e2 => .bin op (subst x v e1) (subst x v e2)
  | .un op e => .un op (subst x v e)
  | .let_ y e1 e2 =>
    if y == x then
      .let_ y (subst x v e1) e2
    else
      .let_ y (subst x v e1) (subst x v e2)
  | .if_ c t e => .if_ (subst x v c) (subst x v t) (subst x v e)
  | .while_ c b => .while_ (subst x v c) (subst x v b)
  | .match_ scrut arms => .match_ (subst x v scrut) (substArms x v arms)
  | .makeData adt tag es => .makeData adt tag (substList x v es)
  | .getTag e => .getTag (subst x v e)
  | .cellNew e => .cellNew (subst x v e)
  | .cellGet e => .cellGet (subst x v e)
  | .cellSet e1 e2 => .cellSet (subst x v e1) (subst x v e2)
  | .spawn e => .spawn (subst x v e)
  | .await e => .await (subst x v e)
  | .concPrim op args => .concPrim op (substList x v args)
  | .trap t => .trap t

def substList (x : Ident) (v : Expr) : List Expr → List Expr
  | [] => []
  | e :: es => subst x v e :: substList x v es

def substArms (x : Ident) (v : Expr) : List (Pat × Expr) → List (Pat × Expr)
  | [] => []
  | (p, body) :: rest =>
    let body' := if (patBoundNames p).contains x then body else subst x v body
    (p, body') :: substArms x v rest
end

/-- Simultaneous substitution of a list of `(Ident, closed Value)` bindings,
    where earlier entries shadow later ones (matching `extendMany`). -/
def substMany : List (Ident × Expr) → Expr → Expr
  | [], e => e
  | (x, v) :: rest, e => substMany rest (subst x v e)

end CoreGeisha
