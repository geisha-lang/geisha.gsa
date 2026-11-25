/-!
# Core Geisha: Abstract Syntax, Types, Values, and Store

This module defines the formal abstract syntax of **Core Geisha**, closely
mirroring `src/core.gs` (`Term`, `Type`, `Pattern`, `AdtInfo`, `FunDef`) in the
self-hosted Geisha compiler (`geisha.gs`), while making runtime values, mutable
store locations (`Cell`), and runtime traps explicit.

## Alignment with `src/core.gs`

| `src/core.gs` | `CoreGeisha.Syntax` | Notes |
| --- | --- | --- |
| `TyVoid`, `TyCon "Int"/"Bool"/"String"` | `Ty.void`, `Ty.int`, `Ty.bool`, `Ty.str` | Monomorphic core types |
| `TyTuple`, `TyArr` | `Ty.tuple`, `Ty.fn` | Multi-arg uncurried functions |
| `TyCon adtName` | `Ty.adt name` | Monomorphized ADTs |
| `TyComp (TyCon "Cell") t` | `Ty.cell t` | Mutable heap cells |
| `TmLit`, `TmVar`, `TmTuple`, `TmBlock` | `Expr.lit`, `Expr.var`, `Expr.tuple`, `Expr.block` | Core expressions |
| `TmMakeCls`, `TmApplyCls`, `TmApplyDir` | `Expr.lam`, `Expr.apply`, `Expr.applyDir` | Strict multi-arg closures & direct calls |
| `TmBin`, `TmUn`, `TmLet`, `TmIf`, `TmWhile` | `Expr.bin`, `Expr.un`, `Expr.let_`, `Expr.if_`, `Expr.while_` | Control flow & ops |
| `TmMatch`, `TmMakeData`, `TmGetTag` | `Expr.match_`, `Expr.makeData`, `Expr.getTag` | ADT construction & pattern matching |
| `cellNew`, `cellGet`, `cellSet` | `Expr.cellNew`, `Expr.cellGet`, `Expr.cellSet` | Explicit mutable store ops |
-/

namespace CoreGeisha

/-- Identifiers for variables, top-level functions, and ADT names. -/
abbrev Ident := String

/-- Store locations for mutable `Cell` values. -/
abbrev Loc := Nat

/-- Core Geisha monomorphic types (post-monomorphization, matching `src/core.gs`). -/
inductive Ty where
  | void : Ty
  | int : Ty
  | bool : Ty
  | str : Ty
  | tuple : List Ty → Ty
  | fn : List Ty → Ty → Ty
  | adt : Ident → Ty
  | cell : Ty → Ty
  deriving Repr, BEq

/-- Core literals (`Lit` in `src/ast.gs`). -/
inductive Lit where
  | int : Int32 → Lit
  | bool : Bool → Lit
  | str : String → Lit
  | unit : Lit
  deriving Repr, BEq, DecidableEq

/-- Unary operators (`UnOp` in `src/ast.gs`). -/
inductive UnOp where
  | not : UnOp      -- `!` on Bool
  | neg : UnOp      -- unary `-` on Int (wrapping 32-bit)
  | bitNot : UnOp   -- `~` on Int
  deriving Repr, BEq, DecidableEq

/-- Binary operators (`BinOp` in `src/ast.gs`). -/
inductive BinOp where
  | add : BinOp
  | sub : BinOp
  | mul : BinOp
  | div : BinOp     -- traps on divisor == 0
  | rem : BinOp     -- traps on divisor == 0
  | bitAnd : BinOp
  | bitOr : BinOp
  | bitXor : BinOp
  | eqInt : BinOp
  | neInt : BinOp
  | ltInt : BinOp
  | leInt : BinOp
  | gtInt : BinOp
  | geInt : BinOp
  | eqBool : BinOp
  | eqStr : BinOp
  | strConcat : BinOp
  | and : BinOp     -- short-circuit logical &&
  | or : BinOp      -- short-circuit logical ||
  deriving Repr, BEq, DecidableEq

/-- Patterns (`Pattern` in `src/ast.gs`, normalized for Core IR). -/
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
  deriving Repr, BEq, DecidableEq

/-- Core Geisha expressions, mirroring `Term` in `src/core.gs` plus runtime locations & traps. -/
inductive Expr where
  | lit : Lit → Expr
  | var : Ident → Expr
  | loc : Loc → Expr
  | tuple : List Expr → Expr
  | block : List Expr → Expr
  | lam : List (Ident × Ty) → Ty → Expr → Expr
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
  | trap : Trap → Expr
  deriving Repr

/-- Variant definition inside an ADT: constructor tag index and payload field types. -/
structure VariantDef where
  tag : Nat
  fields : List Ty
  deriving Repr

/-- Monomorphic ADT definition (`AdtInfo` in `src/infer.gs` / `src/core.gs`). -/
structure AdtDef where
  name : Ident
  variants : List VariantDef
  deriving Repr

/-- Top-level function definition (`FunDef` in `src/core.gs`). -/
structure FunDef where
  name : Ident
  params : List (Ident × Ty)
  retTy : Ty
  body : Expr
  deriving Repr

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
  | lam (ps : List (Ident × Ty)) (ret : Ty) (body : Expr) : IsValue (.lam ps ret body)
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

/- Capture-avoiding substitution of a CLOSED value `v` for `x` in `e`.
   Because `v` is closed during CBV evaluation, shadowing stops substitution
   without needing α-renaming. -/
mutual
def subst (x : Ident) (v : Expr) : Expr → Expr
  | .lit l => .lit l
  | .var y => if y == x then v else .var y
  | .loc l => .loc l
  | .tuple es => .tuple (substList x v es)
  | .block es => .block (substList x v es)
  | .lam ps ret body =>
    if ps.any (fun p => p.1 == x) then
      .lam ps ret body
    else
      .lam ps ret (subst x v body)
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
