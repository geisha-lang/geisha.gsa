import CoreGeisha.Syntax
import CoreGeisha.Semantics

/-!
# Core Geisha: Escape Analysis & Stack-Frame Region Memory Safety

This module formalizes intraprocedural & call-frame escape analysis and stack
allocation promotion for Core Geisha, mirroring `runEscapeAnalysis` in
`src/core.gsa` and stack `alloca` promotion in `src/codegen.gsa`:

1. **Executable Escape Checker (`checkFunEscape`, `checkProgramEscape`)**:
   Verifies stack-promoted `Cell` bindings (`FnStackSpec`) — ensuring every
   stack-promoted variable is bound by a local `cellNew`, never escapes via
   bare variable return/argument/ADT/tuple/store payload or closure capture
   (`onlyDirectCellOps`), and is accessed solely via direct `cellGet`/`cellSet`.
2. **Stack-Frame Region Semantics (`RExpr`, `RStore`, `RStep`, `IsDanglingAccess`)**:
   Models explicit stack-frame regions (`RegionId`, `.stackCellNew`, `.frame`)
   where function exit pops the entire region (`popRegion` marking all live
   slots of that `RegionId` as `.stackFreed`), and characterizes use-after-return
   memory faults via `IsDanglingAccess`.
3. **Machine-Checked Theorems**:
   - `dangling_access_nonvacuous`: concrete counterexample demonstrating an
     unchecked escaping stack cell stepping to `IsDanglingAccess`.
   - `escape_no_dangling_pointers`: any program passing `checkProgramEscape`
     never reaches `IsDanglingAccess` across arbitrarily nested and recursive
     calls (`RSteps`).
   - `stack_alloc_simulates_heap`: stack-promoted region execution is
     observationally simulated by standard heap execution (`Steps`) with
     matching live store contents (`RStoreMatches`).
-/

namespace CoreGeisha

/-! ## Part 1: Stack-Allocation Annotations & Executable Escape Checker -/

/-- Per-function list of local `Cell` variable names promoted from heap
    allocation to stack-frame region allocation (`alloca`). -/
structure FnStackSpec where
  fnName : Ident
  vars   : List Ident
  deriving Repr, BEq

/-- Empty top-level function table. -/
def emptyFunEnv : FunEnv := fun _ => none

/-- Build a `FunEnv` lookup table from a list of `FunDef` declarations. -/
def buildFunEnvFromList (funs : List FunDef) : FunEnv :=
  fun name => funs.find? (·.name == name)

/-- Look up the stack-promoted variable list declared for `fnName` (if any). -/
def lookupStackVars (specs : List FnStackSpec) (fnName : Ident) : List Ident :=
  match specs.find? (·.fnName == fnName) with
  | some spec => spec.vars
  | none => []

/-- Check that a list of identifiers contains no duplicates. -/
def noDupIdents : List Ident → Bool
  | [] => true
  | x :: xs => !(xs.contains x) && noDupIdents xs

/-- Static Core IR expressions contain no runtime heap location literals. -/
def exprHasNoLocs (e : Expr) : Bool :=
  (exprLocs e).isEmpty

/-- Every free variable of `e` is declared among `params`. -/
def exprClosedUnderParams (params : List (Ident × Ty)) (e : Expr) : Bool :=
  (freeVars e).all (fun z => params.any (·.1 == z))

/-- Extract `y` when `e = .var y`. -/
def asVar? : Expr → Option Ident
  | .var y => some y
  | _ => none

/-- Extract `init` when `e = .cellNew init`. -/
def asCellNew? : Expr → Option Expr
  | .cellNew init => some init
  | _ => none

/- Syntactic non-escape check inside a stack cell's scope: `x` ONLY appears as
   the direct target `.var x` of `.cellGet (.var x)` or `.cellSet (.var x) rhs`,
   never as a bare value, never captured in a closure, and never shadowed. -/
mutual
def onlyDirectCellOps (x : Ident) : Expr → Bool
  | .lit _ => true
  | .var y => y != x
  | .loc _ => true
  | .taskRef _ => true
  | .syncRef _ _ => true
  | .tuple es => onlyDirectCellOpsList x es
  | .block es => onlyDirectCellOpsList x es
  | .lam m ps ret body => !((freeVars (.lam m ps ret body)).contains x)
  | .apply fn args => onlyDirectCellOps x fn && onlyDirectCellOpsList x args
  | .applyDir _ args => onlyDirectCellOpsList x args
  | .bin _ e1 e2 => onlyDirectCellOps x e1 && onlyDirectCellOps x e2
  | .un _ e => onlyDirectCellOps x e
  | .let_ y e1 e2 => y != x && onlyDirectCellOps x e1 && onlyDirectCellOps x e2
  | .if_ c t e => onlyDirectCellOps x c && onlyDirectCellOps x t && onlyDirectCellOps x e
  | .while_ c b => onlyDirectCellOps x c && onlyDirectCellOps x b
  | .match_ scrut arms => onlyDirectCellOps x scrut && onlyDirectCellOpsArms x arms
  | .makeData _ _ es => onlyDirectCellOpsList x es
  | .getTag e => onlyDirectCellOps x e
  | .cellNew e => onlyDirectCellOps x e
  | .cellGet e => if asVar? e == some x then true else onlyDirectCellOps x e
  | .cellSet e1 e2 =>
    if asVar? e1 == some x then
      onlyDirectCellOps x e2
    else
      onlyDirectCellOps x e1 && onlyDirectCellOps x e2
  | .spawn e => onlyDirectCellOps x e
  | .await e => onlyDirectCellOps x e
  | .concPrim _ args => onlyDirectCellOpsList x args
  | .trap _ => true

def onlyDirectCellOpsList (x : Ident) : List Expr → Bool
  | [] => true
  | e :: es => onlyDirectCellOps x e && onlyDirectCellOpsList x es

def onlyDirectCellOpsArms (x : Ident) : List (Pat × Expr) → Bool
  | [] => true
  | (p, body) :: rest =>
    !((patBoundNames p).contains x) && onlyDirectCellOps x body && onlyDirectCellOpsArms x rest
end

/- Check whether `x` is bound at least once via `.let_ x (.cellNew init) e2`
   in the current function frame (outside closures). -/
mutual
def containsLetCellNew (x : Ident) : Expr → Bool
  | .lit _ => false
  | .var _ => false
  | .loc _ => false
  | .taskRef _ => false
  | .syncRef _ _ => false
  | .tuple es => containsLetCellNewList x es
  | .block es => containsLetCellNewList x es
  | .lam _ _ _ _ => false
  | .apply fn args => containsLetCellNew x fn || containsLetCellNewList x args
  | .applyDir _ args => containsLetCellNewList x args
  | .bin _ e1 e2 => containsLetCellNew x e1 || containsLetCellNew x e2
  | .un _ e => containsLetCellNew x e
  | .let_ y (.cellNew init) e2 =>
    (y == x) || containsLetCellNew x init || containsLetCellNew x e2
  | .let_ _ e1 e2 => containsLetCellNew x e1 || containsLetCellNew x e2
  | .if_ c t e => containsLetCellNew x c || containsLetCellNew x t || containsLetCellNew x e
  | .while_ c b => containsLetCellNew x c || containsLetCellNew x b
  | .match_ scrut arms => containsLetCellNew x scrut || containsLetCellNewArms x arms
  | .makeData _ _ es => containsLetCellNewList x es
  | .getTag e => containsLetCellNew x e
  | .cellNew e => containsLetCellNew x e
  | .cellGet e => containsLetCellNew x e
  | .cellSet e1 e2 => containsLetCellNew x e1 || containsLetCellNew x e2
  | .spawn e => containsLetCellNew x e
  | .await e => containsLetCellNew x e
  | .concPrim _ args => containsLetCellNewList x args
  | .trap _ => false

def containsLetCellNewList (x : Ident) : List Expr → Bool
  | [] => false
  | e :: es => containsLetCellNew x e || containsLetCellNewList x es

def containsLetCellNewArms (x : Ident) : List (Pat × Expr) → Bool
  | [] => false
  | (_, body) :: rest => containsLetCellNew x body || containsLetCellNewArms x rest
end

/- Check that outside `.let_ x (.cellNew init) e2` bindings, `x` never occurs
   free or rebound, and at every `.let_ x (.cellNew init) e2`, `init` also
   satisfies `checkStackVarInExpr x init` while `e2` satisfies `onlyDirectCellOps x e2`. -/
mutual
def checkStackVarInExpr (x : Ident) : Expr → Bool
  | .lit _ => true
  | .var y => y != x
  | .loc _ => true
  | .taskRef _ => true
  | .syncRef _ _ => true
  | .tuple es => checkStackVarInExprList x es
  | .block es => checkStackVarInExprList x es
  | .lam m ps ret body => !((freeVars (.lam m ps ret body)).contains x)
  | .apply fn args => checkStackVarInExpr x fn && checkStackVarInExprList x args
  | .applyDir _ args => checkStackVarInExprList x args
  | .bin _ e1 e2 => checkStackVarInExpr x e1 && checkStackVarInExpr x e2
  | .un _ e => checkStackVarInExpr x e
  | .let_ y (.cellNew init) e2 =>
    if y == x then
      checkStackVarInExpr x init && onlyDirectCellOps x e2
    else
      checkStackVarInExpr x init && checkStackVarInExpr x e2
  | .let_ y e1 e2 => y != x && checkStackVarInExpr x e1 && checkStackVarInExpr x e2
  | .if_ c t e =>
    checkStackVarInExpr x c && checkStackVarInExpr x t && checkStackVarInExpr x e
  | .while_ c b => checkStackVarInExpr x c && checkStackVarInExpr x b
  | .match_ scrut arms => checkStackVarInExpr x scrut && checkStackVarInExprArms x arms
  | .makeData _ _ es => checkStackVarInExprList x es
  | .getTag e => checkStackVarInExpr x e
  | .cellNew e => checkStackVarInExpr x e
  | .cellGet e => checkStackVarInExpr x e
  | .cellSet e1 e2 => checkStackVarInExpr x e1 && checkStackVarInExpr x e2
  | .spawn e => checkStackVarInExpr x e
  | .await e => checkStackVarInExpr x e
  | .concPrim _ args => checkStackVarInExprList x args
  | .trap _ => true

def checkStackVarInExprList (x : Ident) : List Expr → Bool
  | [] => true
  | e :: es => checkStackVarInExpr x e && checkStackVarInExprList x es

def checkStackVarInExprArms (x : Ident) : List (Pat × Expr) → Bool
  | [] => true
  | (p, body) :: rest =>
    !((patBoundNames p).contains x) && checkStackVarInExpr x body && checkStackVarInExprArms x rest
end

/-- Combined per-variable check: `x` is bound as a local `cellNew` and never escapes. -/
def checkStackCellVar (x : Ident) (e : Expr) : Bool :=
  containsLetCellNew x e && checkStackVarInExpr x e

/-- Verify stack-allocation annotations `svars` on a single `FunDef`. -/
def checkFunEscape (fd : FunDef) (svars : List Ident) : Except String Unit :=
  if !(exprHasNoLocs fd.body) then
    .error s!"in function '{fd.name}': runtime location not allowed in static Core IR"
  else if !(exprClosedUnderParams fd.params fd.body) then
    .error s!"in function '{fd.name}': unbound variable in function body"
  else if !(noDupIdents svars) then
    .error s!"in function '{fd.name}': duplicate variable in stack-allocs"
  else if svars.any (fun x => fd.params.any (·.1 == x)) then
    .error s!"in function '{fd.name}': parameter cannot be stack-promoted cell"
  else if !(svars.all (fun x => checkStackCellVar x fd.body)) then
    .error s!"in function '{fd.name}': stack-alloc variable escapes or is not a local cellNew"
  else
    .ok ()

/-- Verify stack-allocation specifications across an entire program's `FunDef` table. -/
def checkProgramEscapeSpecs (funs : List FunDef) : List FnStackSpec → Except String Unit
  | [] => .ok ()
  | spec :: rest =>
    match funs.find? (·.name == spec.fnName) with
    | none => .error s!"stack-allocs references unknown function '{spec.fnName}'"
    | some fd =>
      match checkFunEscape fd spec.vars with
      | .error err => .error err
      | .ok () => checkProgramEscapeSpecs funs rest

/-- Whole-program executable escape checker. -/
def checkProgramEscape (funs : List FunDef) (specs : List FnStackSpec) : Except String Unit :=
  if !(funs.all (fun fd => exprHasNoLocs fd.body && exprClosedUnderParams fd.params fd.body)) then
    .error "program contains invalid static function body (runtime loc or unbound variable)"
  else if !(noDupIdents (specs.map FnStackSpec.fnName)) then
    .error "duplicate function entry in stack-allocs specifications"
  else
    checkProgramEscapeSpecs funs specs

/-! ## Part 2: Stack-Frame Region Operational Semantics -/

/-- Dynamic call-frame region identifier. -/
abbrev RegionId := Nat

/-- Region-instrumented Core Geisha expressions, extending `Expr` with explicit
    stack-region cell allocation (`.stackCellNew rid e`) and call-frame region
    delimiters (`.frame rid e`). -/
inductive RExpr where
  | lit : Lit → RExpr
  | var : Ident → RExpr
  | loc : Loc → RExpr
  | taskRef : TaskId → RExpr
  | syncRef : SyncKind → Nat → RExpr
  | tuple : List RExpr → RExpr
  | block : List RExpr → RExpr
  | lam : Mode → List (Ident × Ty) → Ty → RExpr → RExpr
  | apply : RExpr → List RExpr → RExpr
  | applyDir : Ident → List RExpr → RExpr
  | bin : BinOp → RExpr → RExpr → RExpr
  | un : UnOp → RExpr → RExpr
  | let_ : Ident → RExpr → RExpr → RExpr
  | if_ : RExpr → RExpr → RExpr → RExpr
  | while_ : RExpr → RExpr → RExpr
  | match_ : RExpr → List (Pat × RExpr) → RExpr
  | makeData : Ident → Nat → List RExpr → RExpr
  | getTag : RExpr → RExpr
  | cellNew : RExpr → RExpr
  | stackCellNew : RegionId → RExpr → RExpr
  | cellGet : RExpr → RExpr
  | cellSet : RExpr → RExpr → RExpr
  | spawn : RExpr → RExpr
  | await : RExpr → RExpr
  | concPrim : ConcPrim → List RExpr → RExpr
  | frame : RegionId → RExpr → RExpr
  | trap : Trap → RExpr
  deriving Repr

/-- Extract `y` when `re = .var y`. -/
def rAsVar? : RExpr → Option Ident
  | .var y => some y
  | _ => none

/-- Region-semantics runtime values (neither `.frame` nor `.stackCellNew` is a value). -/
inductive IsRValue : RExpr → Prop where
  | lit (l : Lit) : IsRValue (.lit l)
  | loc (l : Loc) : IsRValue (.loc l)
  | taskRef (tid : TaskId) : IsRValue (.taskRef tid)
  | syncRef (k : SyncKind) (id : Nat) : IsRValue (.syncRef k id)
  | lam (m : Mode) (ps : List (Ident × Ty)) (ret : Ty) (body : RExpr) :
      IsRValue (.lam m ps ret body)
  | tuple {es : List RExpr} : (∀ e ∈ es, IsRValue e) → IsRValue (.tuple es)
  | makeData (adt : Ident) (tag : Nat) {es : List RExpr} :
      (∀ e ∈ es, IsRValue e) → IsRValue (.makeData adt tag es)

/- Compile a static `Expr` for execution in call-frame region `rid`, promoting
   `let x = cellNew init in e2` to `.stackCellNew rid` whenever `x ∈ svars`.
   Closure bodies are compiled with `svars = []` because closures execute in
   separate invocations rather than the enclosing function's stack frame. -/
mutual
def compileExpr (svars : List Ident) (rid : RegionId) : Expr → RExpr
  | .lit l => .lit l
  | .var x => .var x
  | .loc l => .loc l
  | .taskRef tid => .taskRef tid
  | .syncRef k id => .syncRef k id
  | .tuple es => .tuple (compileExprList svars rid es)
  | .block es => .block (compileExprList svars rid es)
  | .lam m ps ret body => .lam m ps ret (compileExpr [] rid body)
  | .apply fn args => .apply (compileExpr svars rid fn) (compileExprList svars rid args)
  | .applyDir fn args => .applyDir fn (compileExprList svars rid args)
  | .bin op e1 e2 => .bin op (compileExpr svars rid e1) (compileExpr svars rid e2)
  | .un op e => .un op (compileExpr svars rid e)
  | .let_ y (.cellNew init) e2 =>
    if svars.contains y then
      .let_ y (.stackCellNew rid (compileExpr svars rid init)) (compileExpr svars rid e2)
    else
      .let_ y (.cellNew (compileExpr svars rid init)) (compileExpr svars rid e2)
  | .let_ y e1 e2 => .let_ y (compileExpr svars rid e1) (compileExpr svars rid e2)
  | .if_ c t e =>
    .if_ (compileExpr svars rid c) (compileExpr svars rid t) (compileExpr svars rid e)
  | .while_ c b => .while_ (compileExpr svars rid c) (compileExpr svars rid b)
  | .match_ scrut arms =>
    .match_ (compileExpr svars rid scrut) (compileExprArms svars rid arms)
  | .makeData adt tag es => .makeData adt tag (compileExprList svars rid es)
  | .getTag e => .getTag (compileExpr svars rid e)
  | .cellNew e => .cellNew (compileExpr svars rid e)
  | .cellGet e => .cellGet (compileExpr svars rid e)
  | .cellSet e1 e2 => .cellSet (compileExpr svars rid e1) (compileExpr svars rid e2)
  | .spawn e => .spawn (compileExpr svars rid e)
  | .await e => .await (compileExpr svars rid e)
  | .concPrim op args => .concPrim op (compileExprList svars rid args)
  | .trap t => .trap t

def compileExprList (svars : List Ident) (rid : RegionId) : List Expr → List RExpr
  | [] => []
  | e :: es => compileExpr svars rid e :: compileExprList svars rid es

def compileExprArms (svars : List Ident) (rid : RegionId) :
    List (Pat × Expr) → List (Pat × RExpr)
  | [] => []
  | (p, body) :: rest => (p, compileExpr svars rid body) :: compileExprArms svars rid rest
end

/- Erase region annotations back to standard heap-allocated Core Geisha `Expr`. -/
mutual
def eraseRExpr : RExpr → Expr
  | .lit l => .lit l
  | .var x => .var x
  | .loc l => .loc l
  | .taskRef tid => .taskRef tid
  | .syncRef k id => .syncRef k id
  | .tuple es => .tuple (eraseRExprList es)
  | .block es => .block (eraseRExprList es)
  | .lam m ps ret body => .lam m ps ret (eraseRExpr body)
  | .apply fn args => .apply (eraseRExpr fn) (eraseRExprList args)
  | .applyDir fn args => .applyDir fn (eraseRExprList args)
  | .bin op e1 e2 => .bin op (eraseRExpr e1) (eraseRExpr e2)
  | .un op e => .un op (eraseRExpr e)
  | .let_ y e1 e2 => .let_ y (eraseRExpr e1) (eraseRExpr e2)
  | .if_ c t e => .if_ (eraseRExpr c) (eraseRExpr t) (eraseRExpr e)
  | .while_ c b => .while_ (eraseRExpr c) (eraseRExpr b)
  | .match_ scrut arms => .match_ (eraseRExpr scrut) (eraseRExprArms arms)
  | .makeData adt tag es => .makeData adt tag (eraseRExprList es)
  | .getTag e => .getTag (eraseRExpr e)
  | .cellNew e => .cellNew (eraseRExpr e)
  | .stackCellNew _ e => .cellNew (eraseRExpr e)
  | .cellGet e => .cellGet (eraseRExpr e)
  | .cellSet e1 e2 => .cellSet (eraseRExpr e1) (eraseRExpr e2)
  | .spawn e => .spawn (eraseRExpr e)
  | .await e => .await (eraseRExpr e)
  | .concPrim op args => .concPrim op (eraseRExprList args)
  | .frame _ e => eraseRExpr e
  | .trap t => .trap t

def eraseRExprList : List RExpr → List Expr
  | [] => []
  | e :: es => eraseRExpr e :: eraseRExprList es

def eraseRExprArms : List (Pat × RExpr) → List (Pat × Expr)
  | [] => []
  | (p, body) :: rest => (p, eraseRExpr body) :: eraseRExprArms rest
end

/- Free lexical variables of an `RExpr`. -/
mutual
def rFreeVars : RExpr → List Ident
  | .lit _ => []
  | .var x => [x]
  | .loc _ => []
  | .taskRef _ => []
  | .syncRef _ _ => []
  | .tuple es => rFreeVarsList es
  | .block es => rFreeVarsList es
  | .lam _ ps _ body => (rFreeVars body).filter (fun z => !(ps.any (fun p => p.1 == z)))
  | .apply fn args => rFreeVars fn ++ rFreeVarsList args
  | .applyDir _ args => rFreeVarsList args
  | .bin _ e1 e2 => rFreeVars e1 ++ rFreeVars e2
  | .un _ e => rFreeVars e
  | .let_ y e1 e2 => rFreeVars e1 ++ (rFreeVars e2).filter (fun z => z != y)
  | .if_ c t e => rFreeVars c ++ rFreeVars t ++ rFreeVars e
  | .while_ c b => rFreeVars c ++ rFreeVars b
  | .match_ scrut arms => rFreeVars scrut ++ rFreeVarsArms arms
  | .makeData _ _ es => rFreeVarsList es
  | .getTag e => rFreeVars e
  | .cellNew e => rFreeVars e
  | .stackCellNew _ e => rFreeVars e
  | .cellGet e => rFreeVars e
  | .cellSet e1 e2 => rFreeVars e1 ++ rFreeVars e2
  | .spawn e => rFreeVars e
  | .await e => rFreeVars e
  | .concPrim _ args => rFreeVarsList args
  | .frame _ e => rFreeVars e
  | .trap _ => []

def rFreeVarsList : List RExpr → List Ident
  | [] => []
  | e :: es => rFreeVars e ++ rFreeVarsList es

def rFreeVarsArms : List (Pat × RExpr) → List Ident
  | [] => []
  | (p, body) :: rest =>
    (rFreeVars body).filter (fun z => !((patBoundNames p).contains z)) ++ rFreeVarsArms rest
end

/- All runtime `Loc`s syntactically embedded in an `RExpr`. -/
mutual
def rExprLocs : RExpr → List Loc
  | .lit _ => []
  | .var _ => []
  | .loc l => [l]
  | .taskRef _ => []
  | .syncRef _ _ => []
  | .tuple es => rExprLocsList es
  | .block es => rExprLocsList es
  | .lam _ _ _ body => rExprLocs body
  | .apply fn args => rExprLocs fn ++ rExprLocsList args
  | .applyDir _ args => rExprLocsList args
  | .bin _ e1 e2 => rExprLocs e1 ++ rExprLocs e2
  | .un _ e => rExprLocs e
  | .let_ _ e1 e2 => rExprLocs e1 ++ rExprLocs e2
  | .if_ c t e => rExprLocs c ++ rExprLocs t ++ rExprLocs e
  | .while_ c b => rExprLocs c ++ rExprLocs b
  | .match_ scrut arms => rExprLocs scrut ++ rExprLocsArms arms
  | .makeData _ _ es => rExprLocsList es
  | .getTag e => rExprLocs e
  | .cellNew e => rExprLocs e
  | .stackCellNew _ e => rExprLocs e
  | .cellGet e => rExprLocs e
  | .cellSet e1 e2 => rExprLocs e1 ++ rExprLocs e2
  | .spawn e => rExprLocs e
  | .await e => rExprLocs e
  | .concPrim _ args => rExprLocsList args
  | .frame _ e => rExprLocs e
  | .trap _ => []

def rExprLocsList : List RExpr → List Loc
  | [] => []
  | e :: es => rExprLocs e ++ rExprLocsList es

def rExprLocsArms : List (Pat × RExpr) → List Loc
  | [] => []
  | (_, body) :: rest => rExprLocs body ++ rExprLocsArms rest
end

/- Capture-avoiding substitution on `RExpr` (mirroring `subst` on `Expr`). -/
mutual
def rSubst (x : Ident) (v : RExpr) : RExpr → RExpr
  | .lit l => .lit l
  | .var y => if y == x then v else .var y
  | .loc l => .loc l
  | .taskRef tid => .taskRef tid
  | .syncRef k id => .syncRef k id
  | .tuple es => .tuple (rSubstList x v es)
  | .block es => .block (rSubstList x v es)
  | .lam m ps ret body =>
    if ps.any (fun p => p.1 == x) then
      .lam m ps ret body
    else
      .lam m ps ret (rSubst x v body)
  | .apply fn args => .apply (rSubst x v fn) (rSubstList x v args)
  | .applyDir fn args => .applyDir fn (rSubstList x v args)
  | .bin op e1 e2 => .bin op (rSubst x v e1) (rSubst x v e2)
  | .un op e => .un op (rSubst x v e)
  | .let_ y e1 e2 =>
    if y == x then
      .let_ y (rSubst x v e1) e2
    else
      .let_ y (rSubst x v e1) (rSubst x v e2)
  | .if_ c t e => .if_ (rSubst x v c) (rSubst x v t) (rSubst x v e)
  | .while_ c b => .while_ (rSubst x v c) (rSubst x v b)
  | .match_ scrut arms => .match_ (rSubst x v scrut) (rSubstArms x v arms)
  | .makeData adt tag es => .makeData adt tag (rSubstList x v es)
  | .getTag e => .getTag (rSubst x v e)
  | .cellNew e => .cellNew (rSubst x v e)
  | .stackCellNew rid e => .stackCellNew rid (rSubst x v e)
  | .cellGet e => .cellGet (rSubst x v e)
  | .cellSet e1 e2 => .cellSet (rSubst x v e1) (rSubst x v e2)
  | .spawn e => .spawn (rSubst x v e)
  | .await e => .await (rSubst x v e)
  | .concPrim op args => .concPrim op (rSubstList x v args)
  | .frame rid e => .frame rid (rSubst x v e)
  | .trap t => .trap t

def rSubstList (x : Ident) (v : RExpr) : List RExpr → List RExpr
  | [] => []
  | e :: es => rSubst x v e :: rSubstList x v es

def rSubstArms (x : Ident) (v : RExpr) : List (Pat × RExpr) → List (Pat × RExpr)
  | [] => []
  | (p, body) :: rest =>
    let body' := if (patBoundNames p).contains x then body else rSubst x v body
    (p, body') :: rSubstArms x v rest
end

/-- Simultaneous substitution of a list of `(Ident × RExpr)` bindings. -/
def rSubstMany : List (Ident × RExpr) → RExpr → RExpr
  | [], e => e
  | (x, v) :: rest, e => rSubstMany rest (rSubst x v e)

/-- Zip parameter declarations with `RExpr` argument values. -/
def rZipParams (ps : List (Ident × Ty)) (vs : List RExpr) : List (Ident × RExpr) :=
  (ps.map Prod.fst).zip vs

/- Deterministic pattern matching on `RExpr` values (mirroring `matchPat`). -/
mutual
def rMatchPat : Pat → RExpr → Option (List (Ident × RExpr))
  | .wild, _ => some []
  | .var x, v => some [(x, v)]
  | .lit l1, .lit l2 => if l1 == l2 then some [] else none
  | .tuple ps, .tuple vs => rMatchPats ps vs
  | .ctor adt1 tag1 ps, .makeData adt2 tag2 vs =>
    if adt1 == adt2 && tag1 == tag2 then rMatchPats ps vs else none
  | _, _ => none

def rMatchPats : List Pat → List RExpr → Option (List (Ident × RExpr))
  | [], [] => some []
  | p :: ps, v :: vs =>
    match rMatchPat p v, rMatchPats ps vs with
    | some b1, some b2 => some (b1 ++ b2)
    | _, _ => none
  | _, _ => none
end

/-- Leftmost non-value in an `RExpr` list is `.trap t`. -/
inductive RListFirstTrap : List RExpr → Trap → Prop where
  | head (t : Trap) (rest : List RExpr) : RListFirstTrap (.trap t :: rest) t
  | tail {v : RExpr} {rest : List RExpr} {t : Trap} :
      IsRValue v → RListFirstTrap rest t → RListFirstTrap (v :: rest) t

/-- Region-instrumented store slot: heap-allocated cell, live stack-frame cell,
    or popped/deallocated stack-frame cell (`stackFreed`). -/
inductive RegionSlot where
  | heap (val : RExpr)
  | stackLive (rid : RegionId) (val : RExpr)
  | stackFreed (rid : RegionId)
  deriving Repr

/-- Region-instrumented mutable store `ρ`. -/
abbrev RStore := List RegionSlot

/-- Deallocate all live stack slots owned by region `rid` on frame exit. -/
def popRegionSlot (rid : RegionId) : RegionSlot → RegionSlot
  | .heap val => .heap val
  | .stackLive r val => if r == rid then .stackFreed r else .stackLive r val
  | .stackFreed r => .stackFreed r

/-- Pop region `rid` across the entire `RStore`. -/
def popRegion (rid : RegionId) (ρ : RStore) : RStore :=
  ρ.map (popRegionSlot rid)

/- Sequential region-aware small-step operational semantics
   `RStep Φ specs re ρ nextRid re' ρ' nextRid'`. -/
mutual
inductive RStep (Φ : FunEnv) (specs : List FnStackSpec) :
    RExpr → RStore → RegionId → RExpr → RStore → RegionId → Prop where
  -- Tuple: strict left-to-right
  | tupleStep {es es' : List RExpr} {ρ ρ' : RStore} {n n' : RegionId} :
      RStepList Φ specs es ρ n es' ρ' n' →
      RStep Φ specs (.tuple es) ρ n (.tuple es') ρ' n'
  | tupleTrap {es : List RExpr} {t : Trap} {ρ : RStore} {n : RegionId} :
      RListFirstTrap es t →
      RStep Φ specs (.tuple es) ρ n (.trap t) ρ n

  -- Block: sequential evaluation
  | blockEmpty {ρ : RStore} {n : RegionId} :
      RStep Φ specs (.block []) ρ n (.lit .unit) ρ n
  | blockSingle {e : RExpr} {ρ : RStore} {n : RegionId} :
      RStep Φ specs (.block [e]) ρ n e ρ n
  | blockConsStep {e1 e1' e2 : RExpr} {es : List RExpr} {ρ ρ' : RStore} {n n' : RegionId} :
      RStep Φ specs e1 ρ n e1' ρ' n' →
      RStep Φ specs (.block (e1 :: e2 :: es)) ρ n (.block (e1' :: e2 :: es)) ρ' n'
  | blockConsVal {v1 e2 : RExpr} {es : List RExpr} {ρ : RStore} {n : RegionId} :
      IsRValue v1 →
      RStep Φ specs (.block (v1 :: e2 :: es)) ρ n (.block (e2 :: es)) ρ n
  | blockConsTrap {t : Trap} {e2 : RExpr} {es : List RExpr} {ρ : RStore} {n : RegionId} :
      RStep Φ specs (.block (.trap t :: e2 :: es)) ρ n (.trap t) ρ n

  -- Closure application
  | applyFn {fn fn' : RExpr} {args : List RExpr} {ρ ρ' : RStore} {n n' : RegionId} :
      RStep Φ specs fn ρ n fn' ρ' n' →
      RStep Φ specs (.apply fn args) ρ n (.apply fn' args) ρ' n'
  | applyFnTrap {t : Trap} {args : List RExpr} {ρ : RStore} {n : RegionId} :
      RStep Φ specs (.apply (.trap t) args) ρ n (.trap t) ρ n
  | applyArgs {fn : RExpr} {args args' : List RExpr} {ρ ρ' : RStore} {n n' : RegionId} :
      IsRValue fn →
      RStepList Φ specs args ρ n args' ρ' n' →
      RStep Φ specs (.apply fn args) ρ n (.apply fn args') ρ' n'
  | applyArgsTrap {fn : RExpr} {args : List RExpr} {t : Trap} {ρ : RStore} {n : RegionId} :
      IsRValue fn →
      RListFirstTrap args t →
      RStep Φ specs (.apply fn args) ρ n (.trap t) ρ n
  | applyBeta {m : Mode} {ps : List (Ident × Ty)} {ret : Ty} {body : RExpr}
      {args : List RExpr} {ρ : RStore} {n : RegionId} :
      (∀ a ∈ args, IsRValue a) →
      args.length = ps.length →
      RStep Φ specs (.apply (.lam m ps ret body) args) ρ n
        (rSubstMany (rZipParams ps args) body) ρ n

  -- Direct top-level function call: pushes a fresh stack-frame region `n`
  | applyDirArgs {name : Ident} {args args' : List RExpr} {ρ ρ' : RStore} {n n' : RegionId} :
      RStepList Φ specs args ρ n args' ρ' n' →
      RStep Φ specs (.applyDir name args) ρ n (.applyDir name args') ρ' n'
  | applyDirTrap {name : Ident} {args : List RExpr} {t : Trap} {ρ : RStore} {n : RegionId} :
      RListFirstTrap args t →
      RStep Φ specs (.applyDir name args) ρ n (.trap t) ρ n
  | applyDirBeta {name : Ident} {fd : FunDef} {args : List RExpr} {ρ : RStore} {n : RegionId} :
      Φ name = some fd →
      (∀ a ∈ args, IsRValue a) →
      args.length = fd.params.length →
      RStep Φ specs (.applyDir name args) ρ n
        (.frame n (rSubstMany (rZipParams fd.params args)
          (compileExpr (lookupStackVars specs name) n fd.body)))
        ρ (n + 1)

  -- Unary operators
  | unStep {op : UnOp} {e e' : RExpr} {ρ ρ' : RStore} {n n' : RegionId} :
      RStep Φ specs e ρ n e' ρ' n' →
      RStep Φ specs (.un op e) ρ n (.un op e') ρ' n'
  | unTrap {op : UnOp} {t : Trap} {ρ : RStore} {n : RegionId} :
      RStep Φ specs (.un op (.trap t)) ρ n (.trap t) ρ n
  | unVal {op : UnOp} {l l' : Lit} {ρ : RStore} {n : RegionId} :
      evalUnOp op l = some l' →
      RStep Φ specs (.un op (.lit l)) ρ n (.lit l') ρ n

  -- Binary operators
  | binLeft {op : BinOp} {e1 e1' e2 : RExpr} {ρ ρ' : RStore} {n n' : RegionId} :
      RStep Φ specs e1 ρ n e1' ρ' n' →
      RStep Φ specs (.bin op e1 e2) ρ n (.bin op e1' e2) ρ' n'
  | binLeftTrap {op : BinOp} {t : Trap} {e2 : RExpr} {ρ : RStore} {n : RegionId} :
      RStep Φ specs (.bin op (.trap t) e2) ρ n (.trap t) ρ n
  | binAndFalse {e2 : RExpr} {ρ : RStore} {n : RegionId} :
      RStep Φ specs (.bin .and (.lit (.bool false)) e2) ρ n (.lit (.bool false)) ρ n
  | binAndTrue {e2 : RExpr} {ρ : RStore} {n : RegionId} :
      RStep Φ specs (.bin .and (.lit (.bool true)) e2) ρ n e2 ρ n
  | binOrTrue {e2 : RExpr} {ρ : RStore} {n : RegionId} :
      RStep Φ specs (.bin .or (.lit (.bool true)) e2) ρ n (.lit (.bool true)) ρ n
  | binOrFalse {e2 : RExpr} {ρ : RStore} {n : RegionId} :
      RStep Φ specs (.bin .or (.lit (.bool false)) e2) ρ n e2 ρ n
  | binRight {op : BinOp} {v1 e2 e2' : RExpr} {ρ ρ' : RStore} {n n' : RegionId} :
      op ≠ .and → op ≠ .or →
      IsRValue v1 →
      RStep Φ specs e2 ρ n e2' ρ' n' →
      RStep Φ specs (.bin op v1 e2) ρ n (.bin op v1 e2') ρ' n'
  | binRightTrap {op : BinOp} {v1 : RExpr} {t : Trap} {ρ : RStore} {n : RegionId} :
      op ≠ .and → op ≠ .or →
      IsRValue v1 →
      RStep Φ specs (.bin op v1 (.trap t)) ρ n (.trap t) ρ n
  | binVal {op : BinOp} {l1 l2 l' : Lit} {ρ : RStore} {n : RegionId} :
      evalBinOp op l1 l2 = some (.val l') →
      RStep Φ specs (.bin op (.lit l1) (.lit l2)) ρ n (.lit l') ρ n
  | binTrap {op : BinOp} {l1 l2 : Lit} {t : Trap} {ρ : RStore} {n : RegionId} :
      evalBinOp op l1 l2 = some (.trap t) →
      RStep Φ specs (.bin op (.lit l1) (.lit l2)) ρ n (.trap t) ρ n

  -- Let binding
  | letStep {x : Ident} {e1 e1' e2 : RExpr} {ρ ρ' : RStore} {n n' : RegionId} :
      RStep Φ specs e1 ρ n e1' ρ' n' →
      RStep Φ specs (.let_ x e1 e2) ρ n (.let_ x e1' e2) ρ' n'
  | letTrap {x : Ident} {t : Trap} {e2 : RExpr} {ρ : RStore} {n : RegionId} :
      RStep Φ specs (.let_ x (.trap t) e2) ρ n (.trap t) ρ n
  | letVal {x : Ident} {v1 e2 : RExpr} {ρ : RStore} {n : RegionId} :
      IsRValue v1 →
      RStep Φ specs (.let_ x v1 e2) ρ n (rSubst x v1 e2) ρ n

  -- Conditional
  | ifStep {c c' t e : RExpr} {ρ ρ' : RStore} {n n' : RegionId} :
      RStep Φ specs c ρ n c' ρ' n' →
      RStep Φ specs (.if_ c t e) ρ n (.if_ c' t e) ρ' n'
  | ifTrap {tr : Trap} {t e : RExpr} {ρ : RStore} {n : RegionId} :
      RStep Φ specs (.if_ (.trap tr) t e) ρ n (.trap tr) ρ n
  | ifTrue {t e : RExpr} {ρ : RStore} {n : RegionId} :
      RStep Φ specs (.if_ (.lit (.bool true)) t e) ρ n t ρ n
  | ifFalse {t e : RExpr} {ρ : RStore} {n : RegionId} :
      RStep Φ specs (.if_ (.lit (.bool false)) t e) ρ n e ρ n

  -- While loop
  | whileUnfold {c b : RExpr} {ρ : RStore} {n : RegionId} :
      RStep Φ specs (.while_ c b) ρ n (.if_ c (.block [b, .while_ c b]) (.lit .unit)) ρ n

  -- Pattern matching
  | matchScrut {s s' : RExpr} {arms : List (Pat × RExpr)} {ρ ρ' : RStore} {n n' : RegionId} :
      RStep Φ specs s ρ n s' ρ' n' →
      RStep Φ specs (.match_ s arms) ρ n (.match_ s' arms) ρ' n'
  | matchScrutTrap {t : Trap} {arms : List (Pat × RExpr)} {ρ : RStore} {n : RegionId} :
      RStep Φ specs (.match_ (.trap t) arms) ρ n (.trap t) ρ n
  | matchEmpty {v : RExpr} {ρ : RStore} {n : RegionId} :
      IsRValue v →
      RStep Φ specs (.match_ v []) ρ n (.trap .matchFailure) ρ n
  | matchHit {v : RExpr} {p : Pat} {body : RExpr} {rest : List (Pat × RExpr)}
      {env : List (Ident × RExpr)} {ρ : RStore} {n : RegionId} :
      IsRValue v →
      rMatchPat p v = some env →
      RStep Φ specs (.match_ v ((p, body) :: rest)) ρ n (rSubstMany env body) ρ n
  | matchMiss {v : RExpr} {p : Pat} {body : RExpr} {rest : List (Pat × RExpr)}
      {ρ : RStore} {n : RegionId} :
      IsRValue v →
      rMatchPat p v = none →
      RStep Φ specs (.match_ v ((p, body) :: rest)) ρ n (.match_ v rest) ρ n

  -- ADT construction & tag inspection
  | makeDataStep {adt : Ident} {tag : Nat} {es es' : List RExpr} {ρ ρ' : RStore} {n n' : RegionId} :
      RStepList Φ specs es ρ n es' ρ' n' →
      RStep Φ specs (.makeData adt tag es) ρ n (.makeData adt tag es') ρ' n'
  | makeDataTrap {adt : Ident} {tag : Nat} {es : List RExpr} {t : Trap}
      {ρ : RStore} {n : RegionId} :
      RListFirstTrap es t →
      RStep Φ specs (.makeData adt tag es) ρ n (.trap t) ρ n
  | getTagStep {e e' : RExpr} {ρ ρ' : RStore} {n n' : RegionId} :
      RStep Φ specs e ρ n e' ρ' n' →
      RStep Φ specs (.getTag e) ρ n (.getTag e') ρ' n'
  | getTagTrap {t : Trap} {ρ : RStore} {n : RegionId} :
      RStep Φ specs (.getTag (.trap t)) ρ n (.trap t) ρ n
  | getTagVal {adt : Ident} {tag : Nat} {vs : List RExpr} {ρ : RStore} {n : RegionId} :
      (∀ v ∈ vs, IsRValue v) →
      RStep Φ specs (.getTag (.makeData adt tag vs)) ρ n (.lit (.int (Int32.ofNat tag))) ρ n

  -- Heap Cell allocation
  | cellNewStep {e e' : RExpr} {ρ ρ' : RStore} {n n' : RegionId} :
      RStep Φ specs e ρ n e' ρ' n' →
      RStep Φ specs (.cellNew e) ρ n (.cellNew e') ρ' n'
  | cellNewTrap {t : Trap} {ρ : RStore} {n : RegionId} :
      RStep Φ specs (.cellNew (.trap t)) ρ n (.trap t) ρ n
  | cellNewVal {v : RExpr} {ρ : RStore} {n : RegionId} :
      IsRValue v →
      RStep Φ specs (.cellNew v) ρ n (.loc ρ.length) (ρ ++ [.heap v]) n

  -- Stack-Frame Region Cell allocation
  | stackCellNewStep {rid : RegionId} {e e' : RExpr} {ρ ρ' : RStore} {n n' : RegionId} :
      RStep Φ specs e ρ n e' ρ' n' →
      RStep Φ specs (.stackCellNew rid e) ρ n (.stackCellNew rid e') ρ' n'
  | stackCellNewTrap {rid : RegionId} {t : Trap} {ρ : RStore} {n : RegionId} :
      RStep Φ specs (.stackCellNew rid (.trap t)) ρ n (.trap t) ρ n
  | stackCellNewVal {rid : RegionId} {v : RExpr} {ρ : RStore} {n : RegionId} :
      IsRValue v →
      RStep Φ specs (.stackCellNew rid v) ρ n (.loc ρ.length) (ρ ++ [.stackLive rid v]) n

  -- Cell read (valid ONLY on `.heap` or `.stackLive`, NEVER on `.stackFreed`)
  | cellGetStep {e e' : RExpr} {ρ ρ' : RStore} {n n' : RegionId} :
      RStep Φ specs e ρ n e' ρ' n' →
      RStep Φ specs (.cellGet e) ρ n (.cellGet e') ρ' n'
  | cellGetTrap {t : Trap} {ρ : RStore} {n : RegionId} :
      RStep Φ specs (.cellGet (.trap t)) ρ n (.trap t) ρ n
  | cellGetHeap {l : Loc} {v : RExpr} {ρ : RStore} {n : RegionId} :
      ρ[l]? = some (.heap v) →
      RStep Φ specs (.cellGet (.loc l)) ρ n v ρ n
  | cellGetStack {l : Loc} {rid : RegionId} {v : RExpr} {ρ : RStore} {n : RegionId} :
      ρ[l]? = some (.stackLive rid v) →
      RStep Φ specs (.cellGet (.loc l)) ρ n v ρ n

  -- Cell write (valid ONLY on `.heap` or `.stackLive`, NEVER on `.stackFreed`)
  | cellSetLeft {e1 e1' e2 : RExpr} {ρ ρ' : RStore} {n n' : RegionId} :
      RStep Φ specs e1 ρ n e1' ρ' n' →
      RStep Φ specs (.cellSet e1 e2) ρ n (.cellSet e1' e2) ρ' n'
  | cellSetLeftTrap {t : Trap} {e2 : RExpr} {ρ : RStore} {n : RegionId} :
      RStep Φ specs (.cellSet (.trap t) e2) ρ n (.trap t) ρ n
  | cellSetRight {v1 e2 e2' : RExpr} {ρ ρ' : RStore} {n n' : RegionId} :
      IsRValue v1 →
      RStep Φ specs e2 ρ n e2' ρ' n' →
      RStep Φ specs (.cellSet v1 e2) ρ n (.cellSet v1 e2') ρ' n'
  | cellSetRightTrap {v1 : RExpr} {t : Trap} {ρ : RStore} {n : RegionId} :
      IsRValue v1 →
      RStep Φ specs (.cellSet v1 (.trap t)) ρ n (.trap t) ρ n
  | cellSetHeap {l : Loc} {old v : RExpr} {ρ : RStore} {n : RegionId} :
      ρ[l]? = some (.heap old) →
      IsRValue v →
      RStep Φ specs (.cellSet (.loc l) v) ρ n (.lit .unit) (ρ.set l (.heap v)) n
  | cellSetStack {l : Loc} {rid : RegionId} {old v : RExpr} {ρ : RStore} {n : RegionId} :
      ρ[l]? = some (.stackLive rid old) →
      IsRValue v →
      RStep Φ specs (.cellSet (.loc l) v) ρ n (.lit .unit) (ρ.set l (.stackLive rid v)) n

  -- Sequential evaluation inside `spawn`, `await`, `concPrim` arguments
  | spawnStep {e e' : RExpr} {ρ ρ' : RStore} {n n' : RegionId} :
      RStep Φ specs e ρ n e' ρ' n' →
      RStep Φ specs (.spawn e) ρ n (.spawn e') ρ' n'
  | spawnTrap {t : Trap} {ρ : RStore} {n : RegionId} :
      RStep Φ specs (.spawn (.trap t)) ρ n (.trap t) ρ n
  | awaitStep {e e' : RExpr} {ρ ρ' : RStore} {n n' : RegionId} :
      RStep Φ specs e ρ n e' ρ' n' →
      RStep Φ specs (.await e) ρ n (.await e') ρ' n'
  | awaitTrap {t : Trap} {ρ : RStore} {n : RegionId} :
      RStep Φ specs (.await (.trap t)) ρ n (.trap t) ρ n
  | concPrimArgs {op : ConcPrim} {args args' : List RExpr} {ρ ρ' : RStore} {n n' : RegionId} :
      RStepList Φ specs args ρ n args' ρ' n' →
      RStep Φ specs (.concPrim op args) ρ n (.concPrim op args') ρ' n'
  | concPrimTrap {op : ConcPrim} {args : List RExpr} {t : Trap} {ρ : RStore} {n : RegionId} :
      RListFirstTrap args t →
      RStep Φ specs (.concPrim op args) ρ n (.trap t) ρ n

  -- Call-frame region execution and exit (popping `rid` upon return or trap)
  | frameStep {rid : RegionId} {e e' : RExpr} {ρ ρ' : RStore} {n n' : RegionId} :
      RStep Φ specs e ρ n e' ρ' n' →
      RStep Φ specs (.frame rid e) ρ n (.frame rid e') ρ' n'
  | frameVal {rid : RegionId} {v : RExpr} {ρ : RStore} {n : RegionId} :
      IsRValue v →
      RStep Φ specs (.frame rid v) ρ n v (popRegion rid ρ) n
  | frameTrap {rid : RegionId} {t : Trap} {ρ : RStore} {n : RegionId} :
      RStep Φ specs (.frame rid (.trap t)) ρ n (.trap t) (popRegion rid ρ) n

inductive RStepList (Φ : FunEnv) (specs : List FnStackSpec) :
    List RExpr → RStore → RegionId → List RExpr → RStore → RegionId → Prop where
  | head {e e' : RExpr} {es : List RExpr} {ρ ρ' : RStore} {n n' : RegionId} :
      RStep Φ specs e ρ n e' ρ' n' →
      RStepList Φ specs (e :: es) ρ n (e' :: es) ρ' n'
  | tail {v : RExpr} {es es' : List RExpr} {ρ ρ' : RStore} {n n' : RegionId} :
      IsRValue v →
      RStepList Φ specs es ρ n es' ρ' n' →
      RStepList Φ specs (v :: es) ρ n (v :: es') ρ' n'
end

/-- Reflexive-transitive closure of `RStep`. -/
inductive RSteps (Φ : FunEnv) (specs : List FnStackSpec) :
    RExpr → RStore → RegionId → RExpr → RStore → RegionId → Prop where
  | refl (re : RExpr) (ρ : RStore) (n : RegionId) :
      RSteps Φ specs re ρ n re ρ n
  | trans {re1 re2 re3 : RExpr} {ρ1 ρ2 ρ3 : RStore} {n1 n2 n3 : RegionId} :
      RStep Φ specs re1 ρ1 n1 re2 ρ2 n2 →
      RSteps Φ specs re2 ρ2 n2 re3 ρ3 n3 →
      RSteps Φ specs re1 ρ1 n1 re3 ρ3 n3

/- Active evaluation-context characterization of a Use-After-Return / Dangling
   Stack Pointer fault (`cellGet` or `cellSet` targeting a `.stackFreed` slot). -/
mutual
inductive DanglingAt (ρ : RStore) : RExpr → Prop where
  | read {l : Loc} {rid : RegionId} :
      ρ[l]? = some (.stackFreed rid) →
      DanglingAt ρ (.cellGet (.loc l))
  | write {l : Loc} {rid : RegionId} {v : RExpr} :
      ρ[l]? = some (.stackFreed rid) →
      IsRValue v →
      DanglingAt ρ (.cellSet (.loc l) v)
  | tuple {es : List RExpr} :
      DanglingAtList ρ es →
      DanglingAt ρ (.tuple es)
  | blockCons {e1 e2 : RExpr} {es : List RExpr} :
      DanglingAt ρ e1 →
      DanglingAt ρ (.block (e1 :: e2 :: es))
  | applyFn {fn : RExpr} {args : List RExpr} :
      DanglingAt ρ fn →
      DanglingAt ρ (.apply fn args)
  | applyArgs {fn : RExpr} {args : List RExpr} :
      IsRValue fn →
      DanglingAtList ρ args →
      DanglingAt ρ (.apply fn args)
  | applyDirArgs {name : Ident} {args : List RExpr} :
      DanglingAtList ρ args →
      DanglingAt ρ (.applyDir name args)
  | un {op : UnOp} {e : RExpr} :
      DanglingAt ρ e →
      DanglingAt ρ (.un op e)
  | binLeft {op : BinOp} {e1 e2 : RExpr} :
      DanglingAt ρ e1 →
      DanglingAt ρ (.bin op e1 e2)
  | binRight {op : BinOp} {v1 e2 : RExpr} :
      op ≠ .and → op ≠ .or →
      IsRValue v1 →
      DanglingAt ρ e2 →
      DanglingAt ρ (.bin op v1 e2)
  | let_ {x : Ident} {e1 e2 : RExpr} :
      DanglingAt ρ e1 →
      DanglingAt ρ (.let_ x e1 e2)
  | if_ {c t e : RExpr} :
      DanglingAt ρ c →
      DanglingAt ρ (.if_ c t e)
  | match_ {s : RExpr} {arms : List (Pat × RExpr)} :
      DanglingAt ρ s →
      DanglingAt ρ (.match_ s arms)
  | makeData {adt : Ident} {tag : Nat} {es : List RExpr} :
      DanglingAtList ρ es →
      DanglingAt ρ (.makeData adt tag es)
  | getTag {e : RExpr} :
      DanglingAt ρ e →
      DanglingAt ρ (.getTag e)
  | cellNew {e : RExpr} :
      DanglingAt ρ e →
      DanglingAt ρ (.cellNew e)
  | stackCellNew {rid : RegionId} {e : RExpr} :
      DanglingAt ρ e →
      DanglingAt ρ (.stackCellNew rid e)
  | cellGetStep {e : RExpr} :
      DanglingAt ρ e →
      DanglingAt ρ (.cellGet e)
  | cellSetLeft {e1 e2 : RExpr} :
      DanglingAt ρ e1 →
      DanglingAt ρ (.cellSet e1 e2)
  | cellSetRight {v1 e2 : RExpr} :
      IsRValue v1 →
      DanglingAt ρ e2 →
      DanglingAt ρ (.cellSet v1 e2)
  | spawn {e : RExpr} :
      DanglingAt ρ e →
      DanglingAt ρ (.spawn e)
  | await {e : RExpr} :
      DanglingAt ρ e →
      DanglingAt ρ (.await e)
  | concPrimArgs {op : ConcPrim} {args : List RExpr} :
      DanglingAtList ρ args →
      DanglingAt ρ (.concPrim op args)
  | frame {rid : RegionId} {e : RExpr} :
      DanglingAt ρ e →
      DanglingAt ρ (.frame rid e)

inductive DanglingAtList (ρ : RStore) : List RExpr → Prop where
  | head {e : RExpr} {es : List RExpr} :
      DanglingAt ρ e →
      DanglingAtList ρ (e :: es)
  | tail {v : RExpr} {es : List RExpr} :
      IsRValue v →
      DanglingAtList ρ es →
      DanglingAtList ρ (v :: es)
end

/-- Explicit Use-After-Return / Dangling Stack Pointer fault predicate. -/
def IsDanglingAccess (re : RExpr) (ρ : RStore) : Prop :=
  DanglingAt ρ re

/-- Store correspondence between a region store `ρ : RStore` and a standard
    heap store `σ : Store`: equal allocation length and identical erased values
    at every live (`.heap` or `.stackLive`) location. -/
def RStoreMatches (ρ : RStore) (σ : Store) : Prop :=
  ρ.length = σ.length ∧
  (∀ (l : Loc) (rv : RExpr), ρ[l]? = some (.heap rv) → σ[l]? = some (eraseRExpr rv)) ∧
  (∀ (l : Loc) (rid : RegionId) (rv : RExpr),
    ρ[l]? = some (.stackLive rid rv) → σ[l]? = some (eraseRExpr rv))

/-! ## Structural Predicates & Algebraic Lemmas for Escape Soundness and Simulation -/

theorem asVar?_eq_some {e : Expr} {y : Ident} :
    asVar? e = some y ↔ e = .var y := by
  cases e <;> simp [asVar?]

theorem asCellNew?_eq_some {e init : Expr} :
    asCellNew? e = some init ↔ e = .cellNew init := by
  cases e <;> simp [asCellNew?]

theorem rAsVar?_eq_some {e : RExpr} {y : Ident} :
    rAsVar? e = some y ↔ e = .var y := by
  cases e <;> simp [rAsVar?]

theorem compileExpr_let_nonCellNew (svars : List Ident) (rid : RegionId)
    (y : Ident) (e1 e2 : Expr) (h : asCellNew? e1 = none) :
    compileExpr svars rid (.let_ y e1 e2) =
      .let_ y (compileExpr svars rid e1) (compileExpr svars rid e2) := by
  cases e1 <;> simp [asCellNew?] at h <;> rfl

theorem checkStackVarInExpr_let_nonCellNew (x y : Ident) (e1 e2 : Expr)
    (h : asCellNew? e1 = none) :
    checkStackVarInExpr x (.let_ y e1 e2) =
      (y != x && checkStackVarInExpr x e1 && checkStackVarInExpr x e2) := by
  cases e1 <;> simp [asCellNew?] at h <;> rfl

theorem rAsVar?_compileExpr (svars : List Ident) (rid : RegionId) (e : Expr) :
    rAsVar? (compileExpr svars rid e) = asVar? e := by
  cases e with
  | let_ y e1 e2 =>
    cases hcn : asCellNew? e1 with
    | none => rw [compileExpr_let_nonCellNew _ _ _ _ _ hcn]; rfl
    | some init =>
      rw [asCellNew?_eq_some.mp hcn]
      simp only [compileExpr]
      split <;> rfl
  | _ => rfl

theorem rAsVar?_of_isRValue {v : RExpr} (hv : IsRValue v) : rAsVar? v = none := by
  cases hv <;> rfl

/-! ### Self-Contained List Indexing & Store Helpers -/

theorem lt_length_of_getElem?_eq_some {α : Type} {xs : List α} {i : Nat} {x : α}
    (h : xs[i]? = some x) : i < xs.length := by
  induction xs generalizing i with
  | nil => simp at h
  | cons a rest ih =>
    cases i with
    | zero => exact Nat.zero_lt_succ _
    | succ j =>
      simp only [List.getElem?_cons_succ] at h
      exact Nat.succ_lt_succ (ih h)

theorem mem_of_getElem?_eq_some {α : Type} {xs : List α} {i : Nat} {x : α}
    (h : xs[i]? = some x) : x ∈ xs := by
  induction xs generalizing i with
  | nil => simp at h
  | cons a rest ih =>
    cases i with
    | zero =>
      simp only [List.getElem?_cons_zero, Option.some.injEq] at h
      subst h
      exact List.Mem.head _
    | succ j =>
      simp only [List.getElem?_cons_succ] at h
      exact List.Mem.tail _ (ih h)

theorem getElem?_append_last {α : Type} (xs : List α) (x : α) :
    (xs ++ [x])[xs.length]? = some x := by
  induction xs with
  | nil => rfl
  | cons _ rest ih =>
    simp only [List.cons_append, List.length_cons, List.getElem?_cons_succ]
    exact ih

theorem getElem?_append_lt {α : Type} {xs : List α} {x : α} {i : Nat}
    (h : i < xs.length) : (xs ++ [x])[i]? = xs[i]? := by
  induction xs generalizing i with
  | nil => cases h
  | cons a rest ih =>
    cases i with
    | zero => rfl
    | succ j =>
      simp only [List.cons_append, List.getElem?_cons_succ]
      exact ih (Nat.lt_of_succ_lt_succ h)

theorem getElem?_append_gt {α : Type} {xs : List α} {x : α} {i : Nat}
    (h : xs.length < i) : (xs ++ [x])[i]? = none := by
  induction xs generalizing i with
  | nil =>
    cases i with
    | zero => cases h
    | succ j =>
      cases j <;> simp at h ⊢
  | cons a rest ih =>
    cases i with
    | zero => cases h
    | succ j =>
      simp only [List.cons_append, List.getElem?_cons_succ]
      exact ih (Nat.lt_of_succ_lt_succ h)

theorem getElem?_set_self {α : Type} {xs : List α} {i : Nat} {x : α}
    (h : i < xs.length) : (xs.set i x)[i]? = some x := by
  induction xs generalizing i with
  | nil => cases h
  | cons a rest ih =>
    cases i with
    | zero => rfl
    | succ j =>
      simp only [List.set_cons_succ, List.getElem?_cons_succ]
      exact ih (Nat.lt_of_succ_lt_succ h)

theorem getElem?_set_ne {α : Type} {xs : List α} {i j : Nat} {x : α}
    (hne : i ≠ j) : (xs.set i x)[j]? = xs[j]? := by
  induction xs generalizing i j with
  | nil => rfl
  | cons a rest ih =>
    cases i with
    | zero =>
      cases j with
      | zero => exact absurd rfl hne
      | succ _ => rfl
    | succ i' =>
      cases j with
      | zero => rfl
      | succ j' =>
        simp only [List.set_cons_succ, List.getElem?_cons_succ]
        exact ih (fun heq => hne (congrArg Nat.succ heq))

theorem mem_set_subset {α : Type} {xs : List α} {i : Nat} {x y : α}
    (h : y ∈ xs.set i x) : y = x ∨ y ∈ xs := by
  induction xs generalizing i with
  | nil => cases h
  | cons a rest ih =>
    cases i with
    | zero =>
      rcases List.mem_cons.mp h with rfl | hr
      · exact Or.inl rfl
      · exact Or.inr (List.Mem.tail _ hr)
    | succ j =>
      rcases List.mem_cons.mp h with rfl | hr
      · exact Or.inr (List.Mem.head _)
      · rcases ih hr with rfl | hm
        · exact Or.inl rfl
        · exact Or.inr (List.Mem.tail _ hm)

theorem getElem?_popRegion (rid : RegionId) (ρ : RStore) (l : Loc) :
    (popRegion rid ρ)[l]? = (ρ[l]?).map (popRegionSlot rid) := by
  unfold popRegion
  induction ρ generalizing l with
  | nil => rfl
  | cons s rest ih =>
    cases l with
    | zero => rfl
    | succ j => exact ih j

theorem length_popRegion (rid : RegionId) (ρ : RStore) :
    (popRegion rid ρ).length = ρ.length := by
  simp [popRegion]

/-! ### Erasure, Value, Substitution, and Pattern-Match Correspondence -/

mutual
theorem eraseRExpr_compileExpr (svars : List Ident) (rid : RegionId) (e : Expr) :
    eraseRExpr (compileExpr svars rid e) = e := by
  cases e with
  | lit l => rfl
  | var x => rfl
  | loc l => rfl
  | taskRef tid => rfl
  | syncRef k id => rfl
  | tuple es =>
    simp [compileExpr, eraseRExpr, eraseRExpr_compileExprList svars rid es]
  | block es =>
    simp [compileExpr, eraseRExpr, eraseRExpr_compileExprList svars rid es]
  | lam m ps ret body =>
    simp [compileExpr, eraseRExpr, eraseRExpr_compileExpr [] rid body]
  | apply fn args =>
    simp [compileExpr, eraseRExpr,
      eraseRExpr_compileExpr svars rid fn, eraseRExpr_compileExprList svars rid args]
  | applyDir fn args =>
    simp [compileExpr, eraseRExpr, eraseRExpr_compileExprList svars rid args]
  | bin op e1 e2 =>
    simp [compileExpr, eraseRExpr,
      eraseRExpr_compileExpr svars rid e1, eraseRExpr_compileExpr svars rid e2]
  | un op e1 =>
    simp [compileExpr, eraseRExpr, eraseRExpr_compileExpr svars rid e1]
  | let_ y e1 e2 =>
    cases hcn : asCellNew? e1 with
    | none =>
      rw [compileExpr_let_nonCellNew _ _ _ _ _ hcn]
      simp [eraseRExpr, eraseRExpr_compileExpr svars rid e1, eraseRExpr_compileExpr svars rid e2]
    | some init =>
      have he1 := asCellNew?_eq_some.mp hcn
      subst he1
      simp only [compileExpr]
      split <;>
        simp [eraseRExpr, eraseRExpr_compileExpr svars rid init, eraseRExpr_compileExpr svars rid e2]
  | if_ c t e2 =>
    simp [compileExpr, eraseRExpr, eraseRExpr_compileExpr svars rid c,
      eraseRExpr_compileExpr svars rid t, eraseRExpr_compileExpr svars rid e2]
  | while_ c b =>
    simp [compileExpr, eraseRExpr,
      eraseRExpr_compileExpr svars rid c, eraseRExpr_compileExpr svars rid b]
  | match_ scrut arms =>
    simp [compileExpr, eraseRExpr,
      eraseRExpr_compileExpr svars rid scrut, eraseRExpr_compileExprArms svars rid arms]
  | makeData adt tag es =>
    simp [compileExpr, eraseRExpr, eraseRExpr_compileExprList svars rid es]
  | getTag e1 =>
    simp [compileExpr, eraseRExpr, eraseRExpr_compileExpr svars rid e1]
  | cellNew e1 =>
    simp [compileExpr, eraseRExpr, eraseRExpr_compileExpr svars rid e1]
  | cellGet e1 =>
    simp [compileExpr, eraseRExpr, eraseRExpr_compileExpr svars rid e1]
  | cellSet e1 e2 =>
    simp [compileExpr, eraseRExpr,
      eraseRExpr_compileExpr svars rid e1, eraseRExpr_compileExpr svars rid e2]
  | spawn e1 =>
    simp [compileExpr, eraseRExpr, eraseRExpr_compileExpr svars rid e1]
  | await e1 =>
    simp [compileExpr, eraseRExpr, eraseRExpr_compileExpr svars rid e1]
  | concPrim op args =>
    simp [compileExpr, eraseRExpr, eraseRExpr_compileExprList svars rid args]
  | trap t => rfl
termination_by sizeOf e

theorem eraseRExpr_compileExprList (svars : List Ident) (rid : RegionId) (es : List Expr) :
    eraseRExprList (compileExprList svars rid es) = es := by
  cases es with
  | nil => rfl
  | cons e rest =>
    simp [compileExprList, eraseRExprList,
      eraseRExpr_compileExpr svars rid e, eraseRExpr_compileExprList svars rid rest]
termination_by sizeOf es

theorem eraseRExpr_compileExprArms (svars : List Ident) (rid : RegionId)
    (arms : List (Pat × Expr)) :
    eraseRExprArms (compileExprArms svars rid arms) = arms := by
  cases arms with
  | nil => rfl
  | cons arm rest =>
    cases arm with
    | mk p body =>
      simp [compileExprArms, eraseRExprArms,
        eraseRExpr_compileExpr svars rid body, eraseRExpr_compileExprArms svars rid rest]
termination_by sizeOf arms
end

theorem isValue_eraseRExpr {v : RExpr} (hv : IsRValue v) : IsValue (eraseRExpr v) := by
  induction hv with
  | lit l => exact .lit l
  | loc l => exact .loc l
  | taskRef tid => exact .taskRef tid
  | syncRef k id => exact .syncRef k id
  | lam m ps ret body => exact .lam m ps ret (eraseRExpr body)
  | tuple _ ih =>
    apply IsValue.tuple
    intro e' he'
    have hmem : ∀ (es : List RExpr), e' ∈ eraseRExprList es → ∃ u ∈ es, eraseRExpr u = e' := by
      intro es hes
      induction es with
      | nil => cases hes
      | cons a tl ihl =>
        rcases List.mem_cons.mp hes with rfl | htl
        · exact ⟨a, List.Mem.head _, rfl⟩
        · rcases ihl htl with ⟨u, hu, heq⟩
          exact ⟨u, List.Mem.tail _ hu, heq⟩
    rcases hmem _ he' with ⟨u, hu, rfl⟩
    exact ih u hu
  | makeData adt tag _ ih =>
    apply IsValue.makeData
    intro e' he'
    have hmem : ∀ (es : List RExpr), e' ∈ eraseRExprList es → ∃ u ∈ es, eraseRExpr u = e' := by
      intro es hes
      induction es with
      | nil => cases hes
      | cons a tl ihl =>
        rcases List.mem_cons.mp hes with rfl | htl
        · exact ⟨a, List.Mem.head _, rfl⟩
        · rcases ihl htl with ⟨u, hu, heq⟩
          exact ⟨u, List.Mem.tail _ hu, heq⟩
    rcases hmem _ he' with ⟨u, hu, rfl⟩
    exact ih u hu

theorem mem_eraseRExprList_of_isRValue {args : List RExpr} (h : ∀ a ∈ args, IsRValue a) :
    ∀ a' ∈ eraseRExprList args, IsValue a' := by
  induction args with
  | nil => intro _ hm; cases hm
  | cons a rest ih =>
    intro a' hm
    rcases List.mem_cons.mp hm with rfl | hr
    · exact isValue_eraseRExpr (h a (List.Mem.head _))
    · exact ih (fun x hx => h x (List.Mem.tail _ hx)) a' hr

theorem length_eraseRExprList (es : List RExpr) :
    (eraseRExprList es).length = es.length := by
  induction es with
  | nil => rfl
  | cons _ rest ih => simp [eraseRExprList, ih]

theorem listFirstTrap_eraseRExprList {es : List RExpr} {t : Trap}
    (h : RListFirstTrap es t) : ListFirstTrap (eraseRExprList es) t := by
  induction h with
  | head t rest => exact .head t (eraseRExprList rest)
  | tail hv _ ih => exact .tail (isValue_eraseRExpr hv) ih

mutual
theorem eraseRExpr_rSubst (x : Ident) (v e : RExpr) :
    eraseRExpr (rSubst x v e) = subst x (eraseRExpr v) (eraseRExpr e) := by
  cases e with
  | lit l => rfl
  | var y =>
    simp only [rSubst, eraseRExpr, subst]
    split <;> rfl
  | loc l => rfl
  | taskRef tid => rfl
  | syncRef k id => rfl
  | tuple es => simp [rSubst, eraseRExpr, subst, eraseRExpr_rSubstList]
  | block es => simp [rSubst, eraseRExpr, subst, eraseRExpr_rSubstList]
  | lam m ps ret body =>
    simp only [rSubst, eraseRExpr, subst]
    split <;> simp [eraseRExpr, eraseRExpr_rSubst]
  | apply fn args =>
    simp [rSubst, eraseRExpr, subst, eraseRExpr_rSubst, eraseRExpr_rSubstList]
  | applyDir fn args => simp [rSubst, eraseRExpr, subst, eraseRExpr_rSubstList]
  | bin op e1 e2 => simp [rSubst, eraseRExpr, subst, eraseRExpr_rSubst]
  | un op e1 => simp [rSubst, eraseRExpr, subst, eraseRExpr_rSubst]
  | let_ y e1 e2 =>
    simp only [rSubst, eraseRExpr, subst]
    split <;> simp [eraseRExpr, eraseRExpr_rSubst]
  | if_ c t e2 => simp [rSubst, eraseRExpr, subst, eraseRExpr_rSubst]
  | while_ c b => simp [rSubst, eraseRExpr, subst, eraseRExpr_rSubst]
  | match_ scrut arms =>
    simp [rSubst, eraseRExpr, subst, eraseRExpr_rSubst, eraseRExpr_rSubstArms]
  | makeData adt tag es => simp [rSubst, eraseRExpr, subst, eraseRExpr_rSubstList]
  | getTag e1 => simp [rSubst, eraseRExpr, subst, eraseRExpr_rSubst]
  | cellNew e1 => simp [rSubst, eraseRExpr, subst, eraseRExpr_rSubst]
  | stackCellNew rid e1 => simp [rSubst, eraseRExpr, subst, eraseRExpr_rSubst]
  | cellGet e1 => simp [rSubst, eraseRExpr, subst, eraseRExpr_rSubst]
  | cellSet e1 e2 => simp [rSubst, eraseRExpr, subst, eraseRExpr_rSubst]
  | spawn e1 => simp [rSubst, eraseRExpr, subst, eraseRExpr_rSubst]
  | await e1 => simp [rSubst, eraseRExpr, subst, eraseRExpr_rSubst]
  | concPrim op args => simp [rSubst, eraseRExpr, subst, eraseRExpr_rSubstList]
  | frame rid e1 => simp [rSubst, eraseRExpr, eraseRExpr_rSubst]
  | trap t => rfl

theorem eraseRExpr_rSubstList (x : Ident) (v : RExpr) (es : List RExpr) :
    eraseRExprList (rSubstList x v es) = substList x (eraseRExpr v) (eraseRExprList es) := by
  cases es with
  | nil => rfl
  | cons e rest =>
    simp [rSubstList, eraseRExprList, substList, eraseRExpr_rSubst, eraseRExpr_rSubstList]

theorem eraseRExpr_rSubstArms (x : Ident) (v : RExpr) (arms : List (Pat × RExpr)) :
    eraseRExprArms (rSubstArms x v arms) = substArms x (eraseRExpr v) (eraseRExprArms arms) := by
  cases arms with
  | nil => rfl
  | cons arm rest =>
    cases arm with
    | mk p body =>
      simp only [rSubstArms, eraseRExprArms, substArms]
      split <;> simp [eraseRExpr_rSubst, eraseRExpr_rSubstArms]
end

theorem eraseRExpr_rSubstMany (bs : List (Ident × RExpr)) (e : RExpr) :
    eraseRExpr (rSubstMany bs e) =
      substMany (bs.map (fun b => (b.1, eraseRExpr b.2))) (eraseRExpr e) := by
  induction bs generalizing e with
  | nil => rfl
  | cons b rest ih =>
    cases b with
    | mk x v =>
      simp only [rSubstMany, List.map_cons, substMany]
      rw [ih, eraseRExpr_rSubst]

theorem map_rZipParams (ps : List (Ident × Ty)) (vs : List RExpr) :
    (rZipParams ps vs).map (fun b => (b.1, eraseRExpr b.2)) =
      zipParams ps (eraseRExprList vs) := by
  unfold rZipParams zipParams
  have haux : ∀ (xs : List Ident) (ys : List RExpr),
      (xs.zip ys).map (fun b => (b.1, eraseRExpr b.2)) = xs.zip (eraseRExprList ys) := by
    intro xs
    induction xs with
    | nil => intro _; rfl
    | cons x xrest ih =>
      intro ys
      cases ys with
      | nil => rfl
      | cons y yrest =>
        simp [eraseRExprList, ih]
  exact haux (ps.map Prod.fst) vs

mutual
theorem matchPat_eraseRExpr {p : Pat} {v : RExpr} (hv : IsRValue v) :
    matchPat p (eraseRExpr v) =
      (rMatchPat p v).map (fun env => env.map (fun b => (b.1, eraseRExpr b.2))) := by
  cases p with
  | wild => rfl
  | var x => rfl
  | lit l1 =>
    cases hv <;> simp [eraseRExpr, matchPat, rMatchPat]
  | tuple ps =>
    cases hv with
    | tuple hvs =>
      simp only [eraseRExpr, matchPat, rMatchPat]
      exact matchPats_eraseRExpr ps hvs
    | _ => rfl
  | ctor adt1 tag1 ps =>
    cases hv with
    | makeData adt2 tag2 hvs =>
      simp only [eraseRExpr, matchPat, rMatchPat]
      split
      · exact matchPats_eraseRExpr ps hvs
      · rfl
    | _ => rfl
termination_by sizeOf p

theorem matchPats_eraseRExpr (ps : List Pat) {vs : List RExpr}
    (hvs : ∀ u ∈ vs, IsRValue u) :
    matchPats ps (eraseRExprList vs) =
      (rMatchPats ps vs).map (fun env => env.map (fun b => (b.1, eraseRExpr b.2))) := by
  cases ps with
  | nil =>
    cases vs <;> rfl
  | cons p prest =>
    cases vs with
    | nil => rfl
    | cons v vrest =>
      simp only [eraseRExprList, matchPats, rMatchPats]
      rw [matchPat_eraseRExpr (p := p) (hvs v (List.Mem.head _)),
          matchPats_eraseRExpr prest (fun u hu => hvs u (List.Mem.tail _ hu))]
      cases rMatchPat p v <;> cases rMatchPats prest vrest <;> simp [List.map_append]
termination_by sizeOf ps
end

/-! ### `RStoreMatches` Preservation Lemmas & Step Simulation -/

theorem rStoreMatches_nil : RStoreMatches [] [] :=
  ⟨rfl, fun _ _ h => by simp at h, fun _ _ _ h => by simp at h⟩

theorem rStoreMatches_append_heap {ρ : RStore} {σ : Store}
    (hm : RStoreMatches ρ σ) (rv : RExpr) :
    RStoreMatches (ρ ++ [.heap rv]) (σ ++ [eraseRExpr rv]) := by
  rcases hm with ⟨hlen, hheap, hstack⟩
  refine ⟨by simp [hlen], ?_, ?_⟩
  · intro l u hl
    rcases Nat.lt_trichotomy l ρ.length with hlt | rfl | hgt
    · rw [getElem?_append_lt hlt] at hl
      rw [getElem?_append_lt (hlen ▸ hlt)]
      exact hheap l u hl
    · rw [getElem?_append_last] at hl
      injection hl with hl
      injection hl with hl
      subst hl
      rw [hlen, getElem?_append_last]
    · rw [getElem?_append_gt hgt] at hl
      cases hl
  · intro l rid u hl
    rcases Nat.lt_trichotomy l ρ.length with hlt | rfl | hgt
    · rw [getElem?_append_lt hlt] at hl
      rw [getElem?_append_lt (hlen ▸ hlt)]
      exact hstack l rid u hl
    · rw [getElem?_append_last] at hl
      cases hl
    · rw [getElem?_append_gt hgt] at hl
      cases hl

theorem rStoreMatches_append_stack {ρ : RStore} {σ : Store}
    (hm : RStoreMatches ρ σ) (rid : RegionId) (rv : RExpr) :
    RStoreMatches (ρ ++ [.stackLive rid rv]) (σ ++ [eraseRExpr rv]) := by
  rcases hm with ⟨hlen, hheap, hstack⟩
  refine ⟨by simp [hlen], ?_, ?_⟩
  · intro l u hl
    rcases Nat.lt_trichotomy l ρ.length with hlt | rfl | hgt
    · rw [getElem?_append_lt hlt] at hl
      rw [getElem?_append_lt (hlen ▸ hlt)]
      exact hheap l u hl
    · rw [getElem?_append_last] at hl
      cases hl
    · rw [getElem?_append_gt hgt] at hl
      cases hl
  · intro l r u hl
    rcases Nat.lt_trichotomy l ρ.length with hlt | rfl | hgt
    · rw [getElem?_append_lt hlt] at hl
      rw [getElem?_append_lt (hlen ▸ hlt)]
      exact hstack l r u hl
    · rw [getElem?_append_last] at hl
      injection hl with hl
      injection hl with _ hl
      subst hl
      rw [hlen, getElem?_append_last]
    · rw [getElem?_append_gt hgt] at hl
      cases hl

theorem rStoreMatches_set_heap {ρ : RStore} {σ : Store} {l : Loc} {old rv : RExpr}
    (hm : RStoreMatches ρ σ) (hold : ρ[l]? = some (.heap old)) :
    RStoreMatches (ρ.set l (.heap rv)) (σ.set l (eraseRExpr rv)) := by
  rcases hm with ⟨hlen, hheap, hstack⟩
  have hlt : l < ρ.length := lt_length_of_getElem?_eq_some hold
  refine ⟨by simp [hlen], ?_, ?_⟩
  · intro j u hj
    by_cases heq : l = j
    · subst heq
      rw [getElem?_set_self hlt] at hj
      injection hj with hj
      injection hj with hj
      subst hj
      exact getElem?_set_self (hlen ▸ hlt)
    · rw [getElem?_set_ne heq] at hj
      rw [getElem?_set_ne heq]
      exact hheap j u hj
  · intro j r u hj
    by_cases heq : l = j
    · subst heq
      rw [getElem?_set_self hlt] at hj
      cases hj
    · rw [getElem?_set_ne heq] at hj
      rw [getElem?_set_ne heq]
      exact hstack j r u hj

theorem rStoreMatches_set_stack {ρ : RStore} {σ : Store} {l : Loc} {rid : RegionId}
    {old rv : RExpr} (hm : RStoreMatches ρ σ) (hold : ρ[l]? = some (.stackLive rid old)) :
    RStoreMatches (ρ.set l (.stackLive rid rv)) (σ.set l (eraseRExpr rv)) := by
  rcases hm with ⟨hlen, hheap, hstack⟩
  have hlt : l < ρ.length := lt_length_of_getElem?_eq_some hold
  refine ⟨by simp [hlen], ?_, ?_⟩
  · intro j u hj
    by_cases heq : l = j
    · subst heq
      rw [getElem?_set_self hlt] at hj
      cases hj
    · rw [getElem?_set_ne heq] at hj
      rw [getElem?_set_ne heq]
      exact hheap j u hj
  · intro j r u hj
    by_cases heq : l = j
    · subst heq
      rw [getElem?_set_self hlt] at hj
      injection hj with hj
      injection hj with _ hj
      subst hj
      exact getElem?_set_self (hlen ▸ hlt)
    · rw [getElem?_set_ne heq] at hj
      rw [getElem?_set_ne heq]
      exact hstack j r u hj

theorem rStoreMatches_popRegion {ρ : RStore} {σ : Store} (rid : RegionId)
    (hm : RStoreMatches ρ σ) : RStoreMatches (popRegion rid ρ) σ := by
  rcases hm with ⟨hlen, hheap, hstack⟩
  refine ⟨by rw [length_popRegion, hlen], ?_, ?_⟩
  · intro l rv hl
    rw [getElem?_popRegion] at hl
    cases hslot : ρ[l]? with
    | none => simp [hslot] at hl
    | some s =>
      rw [hslot] at hl
      cases s with
      | heap u =>
        simp only [ Option.map_some, popRegionSlot, Option.some.injEq, RegionSlot.heap.injEq] at hl
        subst hl
        exact hheap l u hslot
      | stackLive r u =>
        simp only [Option.map_some, popRegionSlot] at hl
        split at hl <;> cases hl
      | stackFreed r =>
        simp [popRegionSlot] at hl
  · intro l r rv hl
    rw [getElem?_popRegion] at hl
    cases hslot : ρ[l]? with
    | none => simp [hslot] at hl
    | some s =>
      rw [hslot] at hl
      cases s with
      | heap u => simp [popRegionSlot] at hl
      | stackLive r0 u =>
        simp only [Option.map_some, popRegionSlot] at hl
        split at hl
        · cases hl
        · injection hl with hl
          injection hl with hr hu
          subst hr; subst hu
          exact hstack l r0 u hslot
      | stackFreed r0 => simp [popRegionSlot] at hl

structure RStepSimBox (Δ : AdtEnv) (Φ : FunEnv) (specs : List FnStackSpec)
    (re : RExpr) : Prop where
  run : ∀ {re' : RExpr} {ρ ρ' : RStore} {n n' : RegionId} {σ : Store},
    RStep Φ specs re ρ n re' ρ' n' →
    RStoreMatches ρ σ →
    (∃ σ' : Store,
      Step Δ Φ emptyPool (eraseRExpr re) σ (eraseRExpr re') σ' .none ∧ RStoreMatches ρ' σ') ∨
    (eraseRExpr re' = eraseRExpr re ∧ RStoreMatches ρ' σ)

structure RStepListSimBox (Δ : AdtEnv) (Φ : FunEnv) (specs : List FnStackSpec)
    (es : List RExpr) : Prop where
  run : ∀ {es' : List RExpr} {ρ ρ' : RStore} {n n' : RegionId} {σ : Store},
    RStepList Φ specs es ρ n es' ρ' n' →
    RStoreMatches ρ σ →
    (∃ σ' : Store,
      StepList Δ Φ emptyPool (eraseRExprList es) σ (eraseRExprList es') σ' .none ∧
        RStoreMatches ρ' σ') ∨
    (eraseRExprList es' = eraseRExprList es ∧ RStoreMatches ρ' σ)

mutual
theorem rstep_simulates_box (Δ : AdtEnv) (Φ : FunEnv) (specs : List FnStackSpec)
    (re : RExpr) : RStepSimBox Δ Φ specs re := by
  refine ⟨fun {re' ρ ρ' n n' σ} hstep hm => ?_⟩
  cases hstep with
  | tupleStep hsl =>
    rcases (rstepList_simulates_box Δ Φ specs _).run hsl hm with ⟨σ', hsl', hm'⟩ | ⟨heq, hm'⟩
    · exact Or.inl ⟨σ', .tupleStep hsl', hm'⟩
    · exact Or.inr ⟨by simp [eraseRExpr, heq], hm'⟩
  | tupleTrap htr =>
    exact Or.inl ⟨σ, .tupleTrap (listFirstTrap_eraseRExprList htr), hm⟩
  | blockEmpty =>
    exact Or.inl ⟨_, .blockEmpty, hm⟩
  | blockSingle =>
    exact Or.inl ⟨_, .blockSingle, hm⟩
  | blockConsStep hs =>
    rcases (rstep_simulates_box Δ Φ specs _).run hs hm with ⟨σ', hs', hm'⟩ | ⟨heq, hm'⟩
    · exact Or.inl ⟨σ', .blockConsStep hs', hm'⟩
    · exact Or.inr ⟨by simp [eraseRExpr, eraseRExprList, heq], hm'⟩
  | blockConsVal hv =>
    exact Or.inl ⟨_, .blockConsVal (isValue_eraseRExpr hv), hm⟩
  | blockConsTrap =>
    exact Or.inl ⟨_, .blockConsTrap, hm⟩
  | applyFn hs =>
    rcases (rstep_simulates_box Δ Φ specs _).run hs hm with ⟨σ', hs', hm'⟩ | ⟨heq, hm'⟩
    · exact Or.inl ⟨σ', .applyFn hs', hm'⟩
    · exact Or.inr ⟨by simp [eraseRExpr, heq], hm'⟩
  | applyFnTrap =>
    exact Or.inl ⟨_, .applyFnTrap, hm⟩
  | applyArgs hv hsl =>
    rcases (rstepList_simulates_box Δ Φ specs _).run hsl hm with ⟨σ', hsl', hm'⟩ | ⟨heq, hm'⟩
    · exact Or.inl ⟨σ', .applyArgs (isValue_eraseRExpr hv) hsl', hm'⟩
    · exact Or.inr ⟨by simp [eraseRExpr, heq], hm'⟩
  | applyArgsTrap hv htr =>
    exact Or.inl ⟨_, .applyArgsTrap (isValue_eraseRExpr hv) (listFirstTrap_eraseRExprList htr), hm⟩
  | applyBeta hvals hlen =>
    left
    refine ⟨_, ?_, hm⟩
    rw [eraseRExpr_rSubstMany, map_rZipParams]
    exact .applyBeta (mem_eraseRExprList_of_isRValue hvals)
      (by rw [length_eraseRExprList, hlen])
  | applyDirArgs hsl =>
    rcases (rstepList_simulates_box Δ Φ specs _).run hsl hm with ⟨σ', hsl', hm'⟩ | ⟨heq, hm'⟩
    · exact Or.inl ⟨σ', .applyDirArgs hsl', hm'⟩
    · exact Or.inr ⟨by simp [eraseRExpr, heq], hm'⟩
  | applyDirTrap htr =>
    exact Or.inl ⟨_, .applyDirTrap (listFirstTrap_eraseRExprList htr), hm⟩
  | applyDirBeta hfd hvals hlen =>
    left
    refine ⟨_, ?_, hm⟩
    simp only [eraseRExpr, eraseRExpr_rSubstMany, map_rZipParams, eraseRExpr_compileExpr]
    exact .applyDirBeta hfd (mem_eraseRExprList_of_isRValue hvals)
      (by rw [length_eraseRExprList, hlen])
  | unStep hs =>
    rcases (rstep_simulates_box Δ Φ specs _).run hs hm with ⟨σ', hs', hm'⟩ | ⟨heq, hm'⟩
    · exact Or.inl ⟨σ', .unStep hs', hm'⟩
    · exact Or.inr ⟨by simp [eraseRExpr, heq], hm'⟩
  | unTrap =>
    exact Or.inl ⟨_, .unTrap, hm⟩
  | unVal hev =>
    exact Or.inl ⟨_, .unVal hev, hm⟩
  | binLeft hs =>
    rcases (rstep_simulates_box Δ Φ specs _).run hs hm with ⟨σ', hs', hm'⟩ | ⟨heq, hm'⟩
    · exact Or.inl ⟨σ', .binLeft hs', hm'⟩
    · exact Or.inr ⟨by simp [eraseRExpr, heq], hm'⟩
  | binLeftTrap =>
    exact Or.inl ⟨_, .binLeftTrap, hm⟩
  | binAndFalse =>
    exact Or.inl ⟨_, .binAndFalse, hm⟩
  | binAndTrue =>
    exact Or.inl ⟨_, .binAndTrue, hm⟩
  | binOrTrue =>
    exact Or.inl ⟨_, .binOrTrue, hm⟩
  | binOrFalse =>
    exact Or.inl ⟨_, .binOrFalse, hm⟩
  | binRight hna hno hv1 hs =>
    rcases (rstep_simulates_box Δ Φ specs _).run hs hm with ⟨σ', hs', hm'⟩ | ⟨heq, hm'⟩
    · exact Or.inl ⟨σ', .binRight hna hno (isValue_eraseRExpr hv1) hs', hm'⟩
    · exact Or.inr ⟨by simp [eraseRExpr, heq], hm'⟩
  | binRightTrap hna hno hv1 =>
    exact Or.inl ⟨_, .binRightTrap hna hno (isValue_eraseRExpr hv1), hm⟩
  | binVal hev =>
    exact Or.inl ⟨_, .binVal hev, hm⟩
  | binTrap hev =>
    exact Or.inl ⟨_, .binTrap hev, hm⟩
  | letStep hs =>
    rcases (rstep_simulates_box Δ Φ specs _).run hs hm with ⟨σ', hs', hm'⟩ | ⟨heq, hm'⟩
    · exact Or.inl ⟨σ', .letStep hs', hm'⟩
    · exact Or.inr ⟨by simp [eraseRExpr, heq], hm'⟩
  | letTrap =>
    exact Or.inl ⟨_, .letTrap, hm⟩
  | letVal hv1 =>
    left
    refine ⟨_, ?_, hm⟩
    rw [eraseRExpr_rSubst]
    exact .letVal (isValue_eraseRExpr hv1)
  | ifStep hs =>
    rcases (rstep_simulates_box Δ Φ specs _).run hs hm with ⟨σ', hs', hm'⟩ | ⟨heq, hm'⟩
    · exact Or.inl ⟨σ', .ifStep hs', hm'⟩
    · exact Or.inr ⟨by simp [eraseRExpr, heq], hm'⟩
  | ifTrap =>
    exact Or.inl ⟨_, .ifTrap, hm⟩
  | ifTrue =>
    exact Or.inl ⟨_, .ifTrue, hm⟩
  | ifFalse =>
    exact Or.inl ⟨_, .ifFalse, hm⟩
  | whileUnfold =>
    exact Or.inl ⟨_, .whileUnfold, hm⟩
  | matchScrut hs =>
    rcases (rstep_simulates_box Δ Φ specs _).run hs hm with ⟨σ', hs', hm'⟩ | ⟨heq, hm'⟩
    · exact Or.inl ⟨σ', .matchScrut hs', hm'⟩
    · exact Or.inr ⟨by simp [eraseRExpr, heq], hm'⟩
  | matchScrutTrap =>
    exact Or.inl ⟨_, .matchScrutTrap, hm⟩
  | matchEmpty hv =>
    exact Or.inl ⟨_, .matchEmpty (isValue_eraseRExpr hv), hm⟩
  | @matchHit v p body rest env _ _ hv hpat =>
    left
    refine ⟨_, ?_, hm⟩
    rw [eraseRExpr_rSubstMany]
    have hpat' := matchPat_eraseRExpr (p := p) hv
    rw [hpat] at hpat'
    exact .matchHit (isValue_eraseRExpr hv) hpat'
  | @matchMiss v p body rest _ _ hv hpat =>
    left
    refine ⟨_, ?_, hm⟩
    have hpat' := matchPat_eraseRExpr (p := p) hv
    rw [hpat] at hpat'
    exact .matchMiss (isValue_eraseRExpr hv) hpat'
  | makeDataStep hsl =>
    rcases (rstepList_simulates_box Δ Φ specs _).run hsl hm with ⟨σ', hsl', hm'⟩ | ⟨heq, hm'⟩
    · exact Or.inl ⟨σ', .makeDataStep hsl', hm'⟩
    · exact Or.inr ⟨by simp [eraseRExpr, heq], hm'⟩
  | makeDataTrap htr =>
    exact Or.inl ⟨_, .makeDataTrap (listFirstTrap_eraseRExprList htr), hm⟩
  | getTagStep hs =>
    rcases (rstep_simulates_box Δ Φ specs _).run hs hm with ⟨σ', hs', hm'⟩ | ⟨heq, hm'⟩
    · exact Or.inl ⟨σ', .getTagStep hs', hm'⟩
    · exact Or.inr ⟨by simp [eraseRExpr, heq], hm'⟩
  | getTagTrap =>
    exact Or.inl ⟨_, .getTagTrap, hm⟩
  | getTagVal hvs =>
    exact Or.inl ⟨_, .getTagVal (mem_eraseRExprList_of_isRValue hvs), hm⟩
  | cellNewStep hs =>
    rcases (rstep_simulates_box Δ Φ specs _).run hs hm with ⟨σ', hs', hm'⟩ | ⟨heq, hm'⟩
    · exact Or.inl ⟨σ', .cellNewStep hs', hm'⟩
    · exact Or.inr ⟨by simp [eraseRExpr, heq], hm'⟩
  | cellNewTrap =>
    exact Or.inl ⟨_, .cellNewTrap, hm⟩
  | cellNewVal hv =>
    left
    refine ⟨_ ++ [eraseRExpr _], ?_, rStoreMatches_append_heap hm _⟩
    simp only [eraseRExpr, hm.1]
    exact .cellNewVal (isValue_eraseRExpr hv)
  | stackCellNewStep hs =>
    rcases (rstep_simulates_box Δ Φ specs _).run hs hm with ⟨σ', hs', hm'⟩ | ⟨heq, hm'⟩
    · exact Or.inl ⟨σ', .cellNewStep hs', hm'⟩
    · exact Or.inr ⟨by simp [eraseRExpr, heq], hm'⟩
  | stackCellNewTrap =>
    exact Or.inl ⟨_, .cellNewTrap, hm⟩
  | stackCellNewVal hv =>
    left
    refine ⟨_ ++ [eraseRExpr _], ?_, rStoreMatches_append_stack hm _ _⟩
    simp only [eraseRExpr, hm.1]
    exact .cellNewVal (isValue_eraseRExpr hv)
  | cellGetStep hs =>
    rcases (rstep_simulates_box Δ Φ specs _).run hs hm with ⟨σ', hs', hm'⟩ | ⟨heq, hm'⟩
    · exact Or.inl ⟨σ', .cellGetStep hs', hm'⟩
    · exact Or.inr ⟨by simp [eraseRExpr, heq], hm'⟩
  | cellGetTrap =>
    exact Or.inl ⟨_, .cellGetTrap, hm⟩
  | cellGetHeap hl =>
    exact Or.inl ⟨_, .cellGetVal (hm.2.1 _ _ hl), hm⟩
  | cellGetStack hl =>
    exact Or.inl ⟨_, .cellGetVal (hm.2.2 _ _ _ hl), hm⟩
  | cellSetLeft hs =>
    rcases (rstep_simulates_box Δ Φ specs _).run hs hm with ⟨σ', hs', hm'⟩ | ⟨heq, hm'⟩
    · exact Or.inl ⟨σ', .cellSetLeft hs', hm'⟩
    · exact Or.inr ⟨by simp [eraseRExpr, heq], hm'⟩
  | cellSetLeftTrap =>
    exact Or.inl ⟨_, .cellSetLeftTrap, hm⟩
  | cellSetRight hv1 hs =>
    rcases (rstep_simulates_box Δ Φ specs _).run hs hm with ⟨σ', hs', hm'⟩ | ⟨heq, hm'⟩
    · exact Or.inl ⟨σ', .cellSetRight (isValue_eraseRExpr hv1) hs', hm'⟩
    · exact Or.inr ⟨by simp [eraseRExpr, heq], hm'⟩
  | cellSetRightTrap hv1 =>
    exact Or.inl ⟨_, .cellSetRightTrap (isValue_eraseRExpr hv1), hm⟩
  | cellSetHeap hl hv =>
    have hlt : _ < σ.length := hm.1 ▸ lt_length_of_getElem?_eq_some hl
    exact Or.inl ⟨σ.set _ (eraseRExpr _),
      .cellSetVal hlt (isValue_eraseRExpr hv),
      rStoreMatches_set_heap hm hl⟩
  | cellSetStack hl hv =>
    have hlt : _ < σ.length := hm.1 ▸ lt_length_of_getElem?_eq_some hl
    exact Or.inl ⟨σ.set _ (eraseRExpr _),
      .cellSetVal hlt (isValue_eraseRExpr hv),
      rStoreMatches_set_stack hm hl⟩
  | spawnStep hs =>
    rcases (rstep_simulates_box Δ Φ specs _).run hs hm with ⟨σ', hs', hm'⟩ | ⟨heq, hm'⟩
    · exact Or.inl ⟨σ', .spawnStep hs', hm'⟩
    · exact Or.inr ⟨by simp [eraseRExpr, heq], hm'⟩
  | spawnTrap =>
    exact Or.inl ⟨_, .spawnTrap, hm⟩
  | awaitStep hs =>
    rcases (rstep_simulates_box Δ Φ specs _).run hs hm with ⟨σ', hs', hm'⟩ | ⟨heq, hm'⟩
    · exact Or.inl ⟨σ', .awaitStep hs', hm'⟩
    · exact Or.inr ⟨by simp [eraseRExpr, heq], hm'⟩
  | awaitTrap =>
    exact Or.inl ⟨_, .awaitTrap, hm⟩
  | concPrimArgs hsl =>
    rcases (rstepList_simulates_box Δ Φ specs _).run hsl hm with ⟨σ', hsl', hm'⟩ | ⟨heq, hm'⟩
    · exact Or.inl ⟨σ', .concPrimArgs hsl', hm'⟩
    · exact Or.inr ⟨by simp [eraseRExpr, heq], hm'⟩
  | concPrimTrap htr =>
    exact Or.inl ⟨_, .concPrimTrap (listFirstTrap_eraseRExprList htr), hm⟩
  | frameStep hs =>
    rcases (rstep_simulates_box Δ Φ specs _).run hs hm with ⟨σ', hs', hm'⟩ | ⟨heq, hm'⟩
    · exact Or.inl ⟨σ', hs', hm'⟩
    · exact Or.inr ⟨heq, hm'⟩
  | frameVal _ =>
    exact Or.inr ⟨rfl, rStoreMatches_popRegion _ hm⟩
  | frameTrap =>
    exact Or.inr ⟨rfl, rStoreMatches_popRegion _ hm⟩
termination_by sizeOf re

theorem rstepList_simulates_box (Δ : AdtEnv) (Φ : FunEnv) (specs : List FnStackSpec)
    (es : List RExpr) : RStepListSimBox Δ Φ specs es := by
  refine ⟨fun hsl hm => ?_⟩
  cases hsl with
  | head hs =>
    rcases (rstep_simulates_box Δ Φ specs _).run hs hm with ⟨σ', hs', hm'⟩ | ⟨heq, hm'⟩
    · exact Or.inl ⟨σ', .head hs', hm'⟩
    · exact Or.inr ⟨by simp [eraseRExprList, heq], hm'⟩
  | tail hv hsl' =>
    rcases (rstepList_simulates_box Δ Φ specs _).run hsl' hm with ⟨σ', hsl'', hm'⟩ | ⟨heq, hm'⟩
    · exact Or.inl ⟨σ', .tail (isValue_eraseRExpr hv) hsl'', hm'⟩
    · exact Or.inr ⟨by simp [eraseRExprList, heq], hm'⟩
termination_by sizeOf es
end

theorem rstep_simulates (Δ : AdtEnv) {Φ : FunEnv} {specs : List FnStackSpec}
    {re re' : RExpr} {ρ ρ' : RStore} {n n' : RegionId} {σ : Store}
    (hstep : RStep Φ specs re ρ n re' ρ' n')
    (hm : RStoreMatches ρ σ) :
    (∃ σ' : Store,
      Step Δ Φ emptyPool (eraseRExpr re) σ (eraseRExpr re') σ' .none ∧ RStoreMatches ρ' σ') ∨
    (eraseRExpr re' = eraseRExpr re ∧ RStoreMatches ρ' σ) :=
  (rstep_simulates_box Δ Φ specs re).run hstep hm

theorem rsteps_simulates (Δ : AdtEnv) {Φ : FunEnv} {specs : List FnStackSpec}
    {re re' : RExpr} {ρ ρ' : RStore} {n n' : RegionId} {σ : Store}
    (hsteps : RSteps Φ specs re ρ n re' ρ' n')
    (hm : RStoreMatches ρ σ) :
    ∃ σ' : Store, Steps Δ Φ (eraseRExpr re) σ (eraseRExpr re') σ' ∧ RStoreMatches ρ' σ' := by
  induction hsteps generalizing σ with
  | refl re ρ n => exact ⟨σ, .refl _ _, hm⟩
  | trans h1 hrest ih =>
    rcases rstep_simulates Δ h1 hm with ⟨σ1, hs1, hm1⟩ | ⟨heq, hm1⟩
    · rcases ih hm1 with ⟨σ', hsrest, hm'⟩
      exact ⟨σ', .trans hs1 hsrest, hm'⟩
    · rcases ih hm1 with ⟨σ', hsrest, hm'⟩
      rw [heq] at hsrest
      exact ⟨σ', hsrest, hm'⟩

/-! ## Part 3.2: Syntactic Confinement Invariants & Escape Soundness Lemmas -/

/-- Extract `l` when `re = .loc l`. -/
def rAsLoc? : RExpr → Option Loc
  | .loc l => some l
  | _ => none

/-- Extract `(rid, init)` when `re = .stackCellNew rid init`. -/
def asStackCellNew? : RExpr → Option (RegionId × RExpr)
  | .stackCellNew rid init => some (rid, init)
  | _ => none

theorem rAsLoc?_eq_some {e : RExpr} {l : Loc} :
    rAsLoc? e = some l ↔ e = .loc l := by
  cases e <;> simp [rAsLoc?]

theorem asStackCellNew?_eq_some {e : RExpr} {rid : RegionId} {init : RExpr} :
    asStackCellNew? e = some (rid, init) ↔ e = .stackCellNew rid init := by
  cases e <;> simp [asStackCellNew?]

/- Runtime `RExpr` counterpart of `onlyDirectCellOps`. -/
mutual
def rOnlyDirectCellOps (x : Ident) : RExpr → Bool
  | .lit _ => true
  | .var y => y != x
  | .loc _ => true
  | .taskRef _ => true
  | .syncRef _ _ => true
  | .tuple es => rOnlyDirectCellOpsList x es
  | .block es => rOnlyDirectCellOpsList x es
  | .lam m ps ret body => !((rFreeVars (.lam m ps ret body)).contains x)
  | .apply fn args => rOnlyDirectCellOps x fn && rOnlyDirectCellOpsList x args
  | .applyDir _ args => rOnlyDirectCellOpsList x args
  | .bin _ e1 e2 => rOnlyDirectCellOps x e1 && rOnlyDirectCellOps x e2
  | .un _ e => rOnlyDirectCellOps x e
  | .let_ y e1 e2 => y != x && rOnlyDirectCellOps x e1 && rOnlyDirectCellOps x e2
  | .if_ c t e => rOnlyDirectCellOps x c && rOnlyDirectCellOps x t && rOnlyDirectCellOps x e
  | .while_ c b => rOnlyDirectCellOps x c && rOnlyDirectCellOps x b
  | .match_ scrut arms => rOnlyDirectCellOps x scrut && rOnlyDirectCellOpsArms x arms
  | .makeData _ _ es => rOnlyDirectCellOpsList x es
  | .getTag e => rOnlyDirectCellOps x e
  | .cellNew e => rOnlyDirectCellOps x e
  | .stackCellNew _ e => rOnlyDirectCellOps x e
  | .cellGet e => if rAsVar? e == some x then true else rOnlyDirectCellOps x e
  | .cellSet e1 e2 =>
    if rAsVar? e1 == some x then
      rOnlyDirectCellOps x e2
    else
      rOnlyDirectCellOps x e1 && rOnlyDirectCellOps x e2
  | .spawn e => rOnlyDirectCellOps x e
  | .await e => rOnlyDirectCellOps x e
  | .concPrim _ args => rOnlyDirectCellOpsList x args
  | .frame _ e => rOnlyDirectCellOps x e
  | .trap _ => true

def rOnlyDirectCellOpsList (x : Ident) : List RExpr → Bool
  | [] => true
  | e :: es => rOnlyDirectCellOps x e && rOnlyDirectCellOpsList x es

def rOnlyDirectCellOpsArms (x : Ident) : List (Pat × RExpr) → Bool
  | [] => true
  | (p, body) :: rest =>
    !((patBoundNames p).contains x) && rOnlyDirectCellOps x body && rOnlyDirectCellOpsArms x rest
end

/- `noRegionSyntax re = true` iff `re` contains no `.stackCellNew` and no `.frame`. -/
mutual
def noRegionSyntax : RExpr → Bool
  | .lit _ => true
  | .var _ => true
  | .loc _ => true
  | .taskRef _ => true
  | .syncRef _ _ => true
  | .tuple es => noRegionSyntaxList es
  | .block es => noRegionSyntaxList es
  | .lam _ _ _ body => noRegionSyntax body
  | .apply fn args => noRegionSyntax fn && noRegionSyntaxList args
  | .applyDir _ args => noRegionSyntaxList args
  | .bin _ e1 e2 => noRegionSyntax e1 && noRegionSyntax e2
  | .un _ e => noRegionSyntax e
  | .let_ _ e1 e2 => noRegionSyntax e1 && noRegionSyntax e2
  | .if_ c t e => noRegionSyntax c && noRegionSyntax t && noRegionSyntax e
  | .while_ c b => noRegionSyntax c && noRegionSyntax b
  | .match_ scrut arms => noRegionSyntax scrut && noRegionSyntaxArms arms
  | .makeData _ _ es => noRegionSyntaxList es
  | .getTag e => noRegionSyntax e
  | .cellNew e => noRegionSyntax e
  | .stackCellNew _ _ => false
  | .cellGet e => noRegionSyntax e
  | .cellSet e1 e2 => noRegionSyntax e1 && noRegionSyntax e2
  | .spawn e => noRegionSyntax e
  | .await e => noRegionSyntax e
  | .concPrim _ args => noRegionSyntaxList args
  | .frame _ _ => false
  | .trap _ => true

def noRegionSyntaxList : List RExpr → Bool
  | [] => true
  | e :: es => noRegionSyntax e && noRegionSyntaxList es

def noRegionSyntaxArms : List (Pat × RExpr) → Bool
  | [] => true
  | (_, body) :: rest => noRegionSyntax body && noRegionSyntaxArms rest
end

/- Collect all `.frame rid` delimiters syntactically present in `re`. -/
mutual
def exprFrames : RExpr → List RegionId
  | .lit _ => []
  | .var _ => []
  | .loc _ => []
  | .taskRef _ => []
  | .syncRef _ _ => []
  | .tuple es => exprFramesList es
  | .block es => exprFramesList es
  | .lam _ _ _ body => exprFrames body
  | .apply fn args => exprFrames fn ++ exprFramesList args
  | .applyDir _ args => exprFramesList args
  | .bin _ e1 e2 => exprFrames e1 ++ exprFrames e2
  | .un _ e => exprFrames e
  | .let_ _ e1 e2 => exprFrames e1 ++ exprFrames e2
  | .if_ c t e => exprFrames c ++ exprFrames t ++ exprFrames e
  | .while_ c b => exprFrames c ++ exprFrames b
  | .match_ scrut arms => exprFrames scrut ++ exprFramesArms arms
  | .makeData _ _ es => exprFramesList es
  | .getTag e => exprFrames e
  | .cellNew e => exprFrames e
  | .stackCellNew _ e => exprFrames e
  | .cellGet e => exprFrames e
  | .cellSet e1 e2 => exprFrames e1 ++ exprFrames e2
  | .spawn e => exprFrames e
  | .await e => exprFrames e
  | .concPrim _ args => exprFramesList args
  | .frame rid e => rid :: exprFrames e
  | .trap _ => []

def exprFramesList : List RExpr → List RegionId
  | [] => []
  | e :: es => exprFrames e ++ exprFramesList es

def exprFramesArms : List (Pat × RExpr) → List RegionId
  | [] => []
  | (_, body) :: rest => exprFrames body ++ exprFramesArms rest
end

/- Closure bodies contain no region syntax (`.frame` / `.stackCellNew`), and
   unstepped `while` loop bodies/conditions contain no `.frame` delimiters. -/
mutual
def staticSyntaxWF : RExpr → Bool
  | .lit _ => true
  | .var _ => true
  | .loc _ => true
  | .taskRef _ => true
  | .syncRef _ _ => true
  | .tuple es => staticSyntaxWFList es
  | .block es => staticSyntaxWFList es
  | .lam _ _ _ body => noRegionSyntax body
  | .apply fn args => staticSyntaxWF fn && staticSyntaxWFList args
  | .applyDir _ args => staticSyntaxWFList args
  | .bin _ e1 e2 => staticSyntaxWF e1 && staticSyntaxWF e2
  | .un _ e => staticSyntaxWF e
  | .let_ _ e1 e2 => staticSyntaxWF e1 && staticSyntaxWF e2
  | .if_ c t e => staticSyntaxWF c && staticSyntaxWF t && staticSyntaxWF e
  | .while_ c b =>
    (exprFrames c).isEmpty && (exprFrames b).isEmpty && staticSyntaxWF c && staticSyntaxWF b
  | .match_ scrut arms => staticSyntaxWF scrut && staticSyntaxWFArms arms
  | .makeData _ _ es => staticSyntaxWFList es
  | .getTag e => staticSyntaxWF e
  | .cellNew e => staticSyntaxWF e
  | .stackCellNew _ e => staticSyntaxWF e
  | .cellGet e => staticSyntaxWF e
  | .cellSet e1 e2 => staticSyntaxWF e1 && staticSyntaxWF e2
  | .spawn e => staticSyntaxWF e
  | .await e => staticSyntaxWF e
  | .concPrim _ args => staticSyntaxWFList args
  | .frame _ e => staticSyntaxWF e
  | .trap _ => true

def staticSyntaxWFList : List RExpr → Bool
  | [] => true
  | e :: es => staticSyntaxWF e && staticSyntaxWFList es

def staticSyntaxWFArms : List (Pat × RExpr) → Bool
  | [] => true
  | (_, body) :: rest => staticSyntaxWF body && staticSyntaxWFArms rest
end

/- Well-formedness of unallocated `.stackCellNew rid init` nodes: every
   `.stackCellNew rid init` appears exclusively as the RHS of
   `.let_ x (.stackCellNew rid init) e2` inside an enclosing `.frame rid`
   (`rid ∈ enclosing`) with `rOnlyDirectCellOps x e2 = true`. -/
mutual
def stackNewWF (enclosing : List RegionId) : RExpr → Bool
  | .lit _ => true
  | .var _ => true
  | .loc _ => true
  | .taskRef _ => true
  | .syncRef _ _ => true
  | .tuple es => stackNewWFList enclosing es
  | .block es => stackNewWFList enclosing es
  | .lam _ _ _ body => stackNewWF [] body
  | .apply fn args => stackNewWF enclosing fn && stackNewWFList enclosing args
  | .applyDir _ args => stackNewWFList enclosing args
  | .bin _ e1 e2 => stackNewWF enclosing e1 && stackNewWF enclosing e2
  | .un _ e => stackNewWF enclosing e
  | .let_ x (.stackCellNew rid init) e2 =>
    enclosing.contains rid && stackNewWF enclosing init &&
      stackNewWF enclosing e2 && rOnlyDirectCellOps x e2
  | .let_ _ e1 e2 => stackNewWF enclosing e1 && stackNewWF enclosing e2
  | .if_ c t e =>
    stackNewWF enclosing c && stackNewWF enclosing t && stackNewWF enclosing e
  | .while_ c b => stackNewWF enclosing c && stackNewWF enclosing b
  | .match_ scrut arms => stackNewWF enclosing scrut && stackNewWFArms enclosing arms
  | .makeData _ _ es => stackNewWFList enclosing es
  | .getTag e => stackNewWF enclosing e
  | .cellNew e => stackNewWF enclosing e
  | .stackCellNew _ _ => false
  | .cellGet e => stackNewWF enclosing e
  | .cellSet e1 e2 => stackNewWF enclosing e1 && stackNewWF enclosing e2
  | .spawn e => stackNewWF enclosing e
  | .await e => stackNewWF enclosing e
  | .concPrim _ args => stackNewWFList enclosing args
  | .frame rid e => stackNewWF (rid :: enclosing) e
  | .trap _ => true

def stackNewWFList (enclosing : List RegionId) : List RExpr → Bool
  | [] => true
  | e :: es => stackNewWF enclosing e && stackNewWFList enclosing es

def stackNewWFArms (enclosing : List RegionId) : List (Pat × RExpr) → Bool
  | [] => true
  | (_, body) :: rest => stackNewWF enclosing body && stackNewWFArms enclosing rest
end

/- Structural confinement predicate for a live stack location `l` owned by
   region `rid`: `.loc l` may ONLY appear when `inReg = true` (inside `.frame rid`)
   as the target of `.cellGet (.loc l)`, `.cellSet (.loc l) e2`, or the 1-step
   transient binding `.let_ x (.loc l) e2` (with `rOnlyDirectCellOps x e2 = true`). -/
mutual
def locConfined (l : Loc) (rid : RegionId) (inReg : Bool) : RExpr → Bool
  | .lit _ => true
  | .var _ => true
  | .loc l' => l' != l
  | .taskRef _ => true
  | .syncRef _ _ => true
  | .tuple es => locConfinedList l rid inReg es
  | .block es => locConfinedList l rid inReg es
  | .lam _ _ _ body => locConfined l rid false body
  | .apply fn args => locConfined l rid inReg fn && locConfinedList l rid inReg args
  | .applyDir _ args => locConfinedList l rid inReg args
  | .bin _ e1 e2 => locConfined l rid inReg e1 && locConfined l rid inReg e2
  | .un _ e => locConfined l rid inReg e
  | .let_ x e1 e2 =>
    if rAsLoc? e1 == some l then
      inReg && locConfined l rid inReg e2 && rOnlyDirectCellOps x e2
    else
      locConfined l rid inReg e1 && locConfined l rid inReg e2
  | .if_ c t e =>
    locConfined l rid inReg c && locConfined l rid inReg t && locConfined l rid inReg e
  | .while_ c b => locConfined l rid inReg c && locConfined l rid inReg b
  | .match_ scrut arms => locConfined l rid inReg scrut && locConfinedArms l rid inReg arms
  | .makeData _ _ es => locConfinedList l rid inReg es
  | .getTag e => locConfined l rid inReg e
  | .cellNew e => locConfined l rid inReg e
  | .stackCellNew _ e => locConfined l rid inReg e
  | .cellGet e1 =>
    if rAsLoc? e1 == some l then
      inReg
    else
      locConfined l rid inReg e1
  | .cellSet e1 e2 =>
    if rAsLoc? e1 == some l then
      inReg && locConfined l rid inReg e2
    else
      locConfined l rid inReg e1 && locConfined l rid inReg e2
  | .spawn e => locConfined l rid inReg e
  | .await e => locConfined l rid inReg e
  | .concPrim _ args => locConfinedList l rid inReg args
  | .frame r e => locConfined l rid (inReg || (r == rid)) e
  | .trap _ => true

def locConfinedList (l : Loc) (rid : RegionId) (inReg : Bool) : List RExpr → Bool
  | [] => true
  | e :: es => locConfined l rid inReg e && locConfinedList l rid inReg es

def locConfinedArms (l : Loc) (rid : RegionId) (inReg : Bool) :
    List (Pat × RExpr) → Bool
  | [] => true
  | (_, body) :: rest => locConfined l rid inReg body && locConfinedArms l rid inReg rest
end

theorem stackNewWF_let_nonStackCellNew (enc : List RegionId) (x : Ident) (e1 e2 : RExpr)
    (h : asStackCellNew? e1 = none) :
    stackNewWF enc (.let_ x e1 e2) = (stackNewWF enc e1 && stackNewWF enc e2) := by
  cases e1 <;> simp [asStackCellNew?] at h <;> rfl

theorem asStackCellNew?_eq_none_of_stackNewWF {enc : List RegionId} {e : RExpr}
    (h : stackNewWF enc e = true) : asStackCellNew? e = none := by
  cases e with
  | stackCellNew _ _ => simp [stackNewWF] at h
  | _ => rfl

theorem rAsLoc?_ne_of_locConfined {l : Loc} {rid : RegionId} {inReg : Bool} {e : RExpr}
    (h : locConfined l rid inReg e = true) : (rAsLoc? e == some l) = false := by
  cases e with
  | loc l' =>
    simp only [locConfined, bne_iff_ne] at h
    simp only [rAsLoc?, beq_eq_false_iff_ne, ne_eq, Option.some.injEq]
    exact h
  | _ => rfl

/-! ### Compilation Lemmas -/

mutual
theorem rFreeVars_compileExpr (svars : List Ident) (rid : RegionId) (e : Expr) :
    rFreeVars (compileExpr svars rid e) = freeVars e := by
  cases e with
  | lit _ | var _ | loc _ | taskRef _ | syncRef _ _ | trap _ => rfl
  | tuple es | block es | applyDir _ es | makeData _ _ es | concPrim _ es =>
    simp [compileExpr, rFreeVars, freeVars, rFreeVars_compileExprList svars rid es]
  | lam m ps ret body =>
    simp [compileExpr, rFreeVars, freeVars, rFreeVars_compileExpr [] rid body]
  | apply fn args =>
    simp [compileExpr, rFreeVars, freeVars,
      rFreeVars_compileExpr svars rid fn, rFreeVars_compileExprList svars rid args]
  | bin _ e1 e2 | while_ e1 e2 | cellSet e1 e2 =>
    simp [compileExpr, rFreeVars, freeVars,
      rFreeVars_compileExpr svars rid e1, rFreeVars_compileExpr svars rid e2]
  | un _ e1 | getTag e1 | cellNew e1 | cellGet e1 | spawn e1 | await e1 =>
    simp [compileExpr, rFreeVars, freeVars, rFreeVars_compileExpr svars rid e1]
  | let_ y e1 e2 =>
    cases hcn : asCellNew? e1 with
    | none =>
      rw [compileExpr_let_nonCellNew _ _ _ _ _ hcn]
      simp [rFreeVars, freeVars,
        rFreeVars_compileExpr svars rid e1, rFreeVars_compileExpr svars rid e2]
    | some init =>
      have he1 := asCellNew?_eq_some.mp hcn
      subst he1
      simp only [compileExpr]
      split <;>
        simp [rFreeVars, freeVars,
          rFreeVars_compileExpr svars rid init, rFreeVars_compileExpr svars rid e2]
  | if_ c t e2 =>
    simp [compileExpr, rFreeVars, freeVars, rFreeVars_compileExpr svars rid c,
      rFreeVars_compileExpr svars rid t, rFreeVars_compileExpr svars rid e2]
  | match_ scrut arms =>
    simp [compileExpr, rFreeVars, freeVars,
      rFreeVars_compileExpr svars rid scrut, rFreeVars_compileExprArms svars rid arms]
termination_by sizeOf e

theorem rFreeVars_compileExprList (svars : List Ident) (rid : RegionId) (es : List Expr) :
    rFreeVarsList (compileExprList svars rid es) = freeVarsList es := by
  cases es with
  | nil => rfl
  | cons e rest =>
    simp [compileExprList, rFreeVarsList, freeVarsList,
      rFreeVars_compileExpr svars rid e, rFreeVars_compileExprList svars rid rest]
termination_by sizeOf es

theorem rFreeVars_compileExprArms (svars : List Ident) (rid : RegionId)
    (arms : List (Pat × Expr)) :
    rFreeVarsArms (compileExprArms svars rid arms) = freeVarsArms arms := by
  cases arms with
  | nil => rfl
  | cons arm rest =>
    cases arm with
    | mk p body =>
      simp [compileExprArms, rFreeVarsArms, freeVarsArms,
        rFreeVars_compileExpr svars rid body, rFreeVars_compileExprArms svars rid rest]
termination_by sizeOf arms
end

mutual
theorem rExprLocs_compileExpr (svars : List Ident) (rid : RegionId) (e : Expr) :
    rExprLocs (compileExpr svars rid e) = exprLocs e := by
  cases e with
  | lit _ | var _ | loc _ | taskRef _ | syncRef _ _ | trap _ => rfl
  | tuple es | block es | applyDir _ es | makeData _ _ es | concPrim _ es =>
    simp [compileExpr, rExprLocs, exprLocs, rExprLocs_compileExprList svars rid es]
  | lam m ps ret body =>
    simp [compileExpr, rExprLocs, exprLocs, rExprLocs_compileExpr [] rid body]
  | apply fn args =>
    simp [compileExpr, rExprLocs, exprLocs,
      rExprLocs_compileExpr svars rid fn, rExprLocs_compileExprList svars rid args]
  | bin _ e1 e2 | while_ e1 e2 | cellSet e1 e2 =>
    simp [compileExpr, rExprLocs, exprLocs,
      rExprLocs_compileExpr svars rid e1, rExprLocs_compileExpr svars rid e2]
  | un _ e1 | getTag e1 | cellNew e1 | cellGet e1 | spawn e1 | await e1 =>
    simp [compileExpr, rExprLocs, exprLocs, rExprLocs_compileExpr svars rid e1]
  | let_ y e1 e2 =>
    cases hcn : asCellNew? e1 with
    | none =>
      rw [compileExpr_let_nonCellNew _ _ _ _ _ hcn]
      simp [rExprLocs, exprLocs,
        rExprLocs_compileExpr svars rid e1, rExprLocs_compileExpr svars rid e2]
    | some init =>
      have he1 := asCellNew?_eq_some.mp hcn
      subst he1
      simp only [compileExpr]
      split <;>
        simp [rExprLocs, exprLocs,
          rExprLocs_compileExpr svars rid init, rExprLocs_compileExpr svars rid e2]
  | if_ c t e2 =>
    simp [compileExpr, rExprLocs, exprLocs, rExprLocs_compileExpr svars rid c,
      rExprLocs_compileExpr svars rid t, rExprLocs_compileExpr svars rid e2]
  | match_ scrut arms =>
    simp [compileExpr, rExprLocs, exprLocs,
      rExprLocs_compileExpr svars rid scrut, rExprLocs_compileExprArms svars rid arms]
termination_by sizeOf e

theorem rExprLocs_compileExprList (svars : List Ident) (rid : RegionId) (es : List Expr) :
    rExprLocsList (compileExprList svars rid es) = exprLocsList es := by
  cases es with
  | nil => rfl
  | cons e rest =>
    simp [compileExprList, rExprLocsList, exprLocsList,
      rExprLocs_compileExpr svars rid e, rExprLocs_compileExprList svars rid rest]
termination_by sizeOf es

theorem rExprLocs_compileExprArms (svars : List Ident) (rid : RegionId)
    (arms : List (Pat × Expr)) :
    rExprLocsArms (compileExprArms svars rid arms) = exprLocsArms arms := by
  cases arms with
  | nil => rfl
  | cons arm rest =>
    cases arm with
    | mk p body =>
      simp [compileExprArms, rExprLocsArms, exprLocsArms,
        rExprLocs_compileExpr svars rid body, rExprLocs_compileExprArms svars rid rest]
termination_by sizeOf arms
end

mutual
theorem rOnlyDirectCellOps_compileExpr (x : Ident) (svars : List Ident) (rid : RegionId)
    (e : Expr) :
    rOnlyDirectCellOps x (compileExpr svars rid e) = onlyDirectCellOps x e := by
  cases e with
  | lit _ | var _ | loc _ | taskRef _ | syncRef _ _ | trap _ => rfl
  | tuple es | block es | applyDir _ es | makeData _ _ es | concPrim _ es =>
    simp [compileExpr, rOnlyDirectCellOps, onlyDirectCellOps,
      rOnlyDirectCellOps_compileExprList x svars rid es]
  | lam m ps ret body =>
    simp [compileExpr, rOnlyDirectCellOps, onlyDirectCellOps,
      rFreeVars, freeVars, rFreeVars_compileExpr [] rid body]
  | apply fn args =>
    simp [compileExpr, rOnlyDirectCellOps, onlyDirectCellOps,
      rOnlyDirectCellOps_compileExpr x svars rid fn,
      rOnlyDirectCellOps_compileExprList x svars rid args]
  | bin _ e1 e2 | while_ e1 e2 =>
    simp [compileExpr, rOnlyDirectCellOps, onlyDirectCellOps,
      rOnlyDirectCellOps_compileExpr x svars rid e1,
      rOnlyDirectCellOps_compileExpr x svars rid e2]
  | un _ e1 | getTag e1 | cellNew e1 | spawn e1 | await e1 =>
    simp [compileExpr, rOnlyDirectCellOps, onlyDirectCellOps,
      rOnlyDirectCellOps_compileExpr x svars rid e1]
  | cellGet e1 =>
    simp [compileExpr, rOnlyDirectCellOps, onlyDirectCellOps,
      rAsVar?_compileExpr, rOnlyDirectCellOps_compileExpr x svars rid e1]
  | cellSet e1 e2 =>
    simp [compileExpr, rOnlyDirectCellOps, onlyDirectCellOps, rAsVar?_compileExpr,
      rOnlyDirectCellOps_compileExpr x svars rid e1,
      rOnlyDirectCellOps_compileExpr x svars rid e2]
  | let_ y e1 e2 =>
    cases hcn : asCellNew? e1 with
    | none =>
      rw [compileExpr_let_nonCellNew _ _ _ _ _ hcn]
      simp [rOnlyDirectCellOps, onlyDirectCellOps,
        rOnlyDirectCellOps_compileExpr x svars rid e1,
        rOnlyDirectCellOps_compileExpr x svars rid e2]
    | some init =>
      have he1 := asCellNew?_eq_some.mp hcn
      subst he1
      simp only [compileExpr]
      split <;>
        simp [rOnlyDirectCellOps, onlyDirectCellOps,
          rOnlyDirectCellOps_compileExpr x svars rid init,
          rOnlyDirectCellOps_compileExpr x svars rid e2]
  | if_ c t e2 =>
    simp [compileExpr, rOnlyDirectCellOps, onlyDirectCellOps,
      rOnlyDirectCellOps_compileExpr x svars rid c,
      rOnlyDirectCellOps_compileExpr x svars rid t,
      rOnlyDirectCellOps_compileExpr x svars rid e2]
  | match_ scrut arms =>
    simp [compileExpr, rOnlyDirectCellOps, onlyDirectCellOps,
      rOnlyDirectCellOps_compileExpr x svars rid scrut,
      rOnlyDirectCellOps_compileExprArms x svars rid arms]
termination_by sizeOf e

theorem rOnlyDirectCellOps_compileExprList (x : Ident) (svars : List Ident) (rid : RegionId)
    (es : List Expr) :
    rOnlyDirectCellOpsList x (compileExprList svars rid es) = onlyDirectCellOpsList x es := by
  cases es with
  | nil => rfl
  | cons e rest =>
    simp [compileExprList, rOnlyDirectCellOpsList, onlyDirectCellOpsList,
      rOnlyDirectCellOps_compileExpr x svars rid e,
      rOnlyDirectCellOps_compileExprList x svars rid rest]
termination_by sizeOf es

theorem rOnlyDirectCellOps_compileExprArms (x : Ident) (svars : List Ident) (rid : RegionId)
    (arms : List (Pat × Expr)) :
    rOnlyDirectCellOpsArms x (compileExprArms svars rid arms) = onlyDirectCellOpsArms x arms := by
  cases arms with
  | nil => rfl
  | cons arm rest =>
    cases arm with
    | mk p body =>
      simp [compileExprArms, rOnlyDirectCellOpsArms, onlyDirectCellOpsArms,
        rOnlyDirectCellOps_compileExpr x svars rid body,
        rOnlyDirectCellOps_compileExprArms x svars rid rest]
termination_by sizeOf arms
end

mutual
theorem noRegionSyntax_compileExpr_nil (rid : RegionId) (e : Expr) :
    noRegionSyntax (compileExpr [] rid e) = true := by
  cases e with
  | lit _ | var _ | loc _ | taskRef _ | syncRef _ _ | trap _ => rfl
  | tuple es | block es | applyDir _ es | makeData _ _ es | concPrim _ es =>
    simp [compileExpr, noRegionSyntax, noRegionSyntax_compileExprList_nil rid es]
  | lam m ps ret body =>
    simp [compileExpr, noRegionSyntax, noRegionSyntax_compileExpr_nil rid body]
  | apply fn args =>
    simp [compileExpr, noRegionSyntax,
      noRegionSyntax_compileExpr_nil rid fn, noRegionSyntax_compileExprList_nil rid args]
  | bin _ e1 e2 | while_ e1 e2 | cellSet e1 e2 =>
    simp [compileExpr, noRegionSyntax,
      noRegionSyntax_compileExpr_nil rid e1, noRegionSyntax_compileExpr_nil rid e2]
  | un _ e1 | getTag e1 | cellNew e1 | cellGet e1 | spawn e1 | await e1 =>
    simp [compileExpr, noRegionSyntax, noRegionSyntax_compileExpr_nil rid e1]
  | let_ y e1 e2 =>
    cases hcn : asCellNew? e1 with
    | none =>
      rw [compileExpr_let_nonCellNew _ _ _ _ _ hcn]
      simp [noRegionSyntax,
        noRegionSyntax_compileExpr_nil rid e1, noRegionSyntax_compileExpr_nil rid e2]
    | some init =>
      have he1 := asCellNew?_eq_some.mp hcn
      subst he1
      simp [compileExpr, noRegionSyntax,
        noRegionSyntax_compileExpr_nil rid init, noRegionSyntax_compileExpr_nil rid e2]
  | if_ c t e2 =>
    simp [compileExpr, noRegionSyntax, noRegionSyntax_compileExpr_nil rid c,
      noRegionSyntax_compileExpr_nil rid t, noRegionSyntax_compileExpr_nil rid e2]
  | match_ scrut arms =>
    simp [compileExpr, noRegionSyntax,
      noRegionSyntax_compileExpr_nil rid scrut, noRegionSyntax_compileExprArms_nil rid arms]
termination_by sizeOf e

theorem noRegionSyntax_compileExprList_nil (rid : RegionId) (es : List Expr) :
    noRegionSyntaxList (compileExprList [] rid es) = true := by
  cases es with
  | nil => rfl
  | cons e rest =>
    simp [compileExprList, noRegionSyntaxList,
      noRegionSyntax_compileExpr_nil rid e, noRegionSyntax_compileExprList_nil rid rest]
termination_by sizeOf es

theorem noRegionSyntax_compileExprArms_nil (rid : RegionId) (arms : List (Pat × Expr)) :
    noRegionSyntaxArms (compileExprArms [] rid arms) = true := by
  cases arms with
  | nil => rfl
  | cons arm rest =>
    cases arm with
    | mk p body =>
      simp [compileExprArms, noRegionSyntaxArms,
        noRegionSyntax_compileExpr_nil rid body, noRegionSyntax_compileExprArms_nil rid rest]
termination_by sizeOf arms
end

mutual
theorem exprFrames_compileExpr (svars : List Ident) (rid : RegionId) (e : Expr) :
    exprFrames (compileExpr svars rid e) = [] := by
  cases e with
  | lit _ | var _ | loc _ | taskRef _ | syncRef _ _ | trap _ => rfl
  | tuple es | block es | applyDir _ es | makeData _ _ es | concPrim _ es =>
    simp [compileExpr, exprFrames, exprFrames_compileExprList svars rid es]
  | lam m ps ret body =>
    simp [compileExpr, exprFrames, exprFrames_compileExpr [] rid body]
  | apply fn args =>
    simp [compileExpr, exprFrames,
      exprFrames_compileExpr svars rid fn, exprFrames_compileExprList svars rid args]
  | bin _ e1 e2 | while_ e1 e2 | cellSet e1 e2 =>
    simp [compileExpr, exprFrames,
      exprFrames_compileExpr svars rid e1, exprFrames_compileExpr svars rid e2]
  | un _ e1 | getTag e1 | cellNew e1 | cellGet e1 | spawn e1 | await e1 =>
    simp [compileExpr, exprFrames, exprFrames_compileExpr svars rid e1]
  | let_ y e1 e2 =>
    cases hcn : asCellNew? e1 with
    | none =>
      rw [compileExpr_let_nonCellNew _ _ _ _ _ hcn]
      simp [exprFrames,
        exprFrames_compileExpr svars rid e1, exprFrames_compileExpr svars rid e2]
    | some init =>
      have he1 := asCellNew?_eq_some.mp hcn
      subst he1
      simp only [compileExpr]
      split <;>
        simp [exprFrames,
          exprFrames_compileExpr svars rid init, exprFrames_compileExpr svars rid e2]
  | if_ c t e2 =>
    simp [compileExpr, exprFrames, exprFrames_compileExpr svars rid c,
      exprFrames_compileExpr svars rid t, exprFrames_compileExpr svars rid e2]
  | match_ scrut arms =>
    simp [compileExpr, exprFrames,
      exprFrames_compileExpr svars rid scrut, exprFrames_compileExprArms svars rid arms]
termination_by sizeOf e

theorem exprFrames_compileExprList (svars : List Ident) (rid : RegionId) (es : List Expr) :
    exprFramesList (compileExprList svars rid es) = [] := by
  cases es with
  | nil => rfl
  | cons e rest =>
    simp [compileExprList, exprFramesList,
      exprFrames_compileExpr svars rid e, exprFrames_compileExprList svars rid rest]
termination_by sizeOf es

theorem exprFrames_compileExprArms (svars : List Ident) (rid : RegionId)
    (arms : List (Pat × Expr)) :
    exprFramesArms (compileExprArms svars rid arms) = [] := by
  cases arms with
  | nil => rfl
  | cons arm rest =>
    cases arm with
    | mk p body =>
      simp [compileExprArms, exprFramesArms,
        exprFrames_compileExpr svars rid body, exprFrames_compileExprArms svars rid rest]
termination_by sizeOf arms
end

mutual
theorem staticSyntaxWF_compileExpr (svars : List Ident) (rid : RegionId) (e : Expr) :
    staticSyntaxWF (compileExpr svars rid e) = true := by
  cases e with
  | lit _ | var _ | loc _ | taskRef _ | syncRef _ _ | trap _ => rfl
  | tuple es | block es | applyDir _ es | makeData _ _ es | concPrim _ es =>
    simp [compileExpr, staticSyntaxWF, staticSyntaxWF_compileExprList svars rid es]
  | lam m ps ret body =>
    simp [compileExpr, staticSyntaxWF, noRegionSyntax_compileExpr_nil rid body]
  | apply fn args =>
    simp [compileExpr, staticSyntaxWF,
      staticSyntaxWF_compileExpr svars rid fn, staticSyntaxWF_compileExprList svars rid args]
  | bin _ e1 e2 | cellSet e1 e2 =>
    simp [compileExpr, staticSyntaxWF,
      staticSyntaxWF_compileExpr svars rid e1, staticSyntaxWF_compileExpr svars rid e2]
  | while_ c b =>
    simp [compileExpr, staticSyntaxWF,
      exprFrames_compileExpr svars rid c, exprFrames_compileExpr svars rid b,
      staticSyntaxWF_compileExpr svars rid c, staticSyntaxWF_compileExpr svars rid b]
  | un _ e1 | getTag e1 | cellNew e1 | cellGet e1 | spawn e1 | await e1 =>
    simp [compileExpr, staticSyntaxWF, staticSyntaxWF_compileExpr svars rid e1]
  | let_ y e1 e2 =>
    cases hcn : asCellNew? e1 with
    | none =>
      rw [compileExpr_let_nonCellNew _ _ _ _ _ hcn]
      simp [staticSyntaxWF,
        staticSyntaxWF_compileExpr svars rid e1, staticSyntaxWF_compileExpr svars rid e2]
    | some init =>
      have he1 := asCellNew?_eq_some.mp hcn
      subst he1
      simp only [compileExpr]
      split <;>
        simp [staticSyntaxWF,
          staticSyntaxWF_compileExpr svars rid init, staticSyntaxWF_compileExpr svars rid e2]
  | if_ c t e2 =>
    simp [compileExpr, staticSyntaxWF, staticSyntaxWF_compileExpr svars rid c,
      staticSyntaxWF_compileExpr svars rid t, staticSyntaxWF_compileExpr svars rid e2]
  | match_ scrut arms =>
    simp [compileExpr, staticSyntaxWF,
      staticSyntaxWF_compileExpr svars rid scrut, staticSyntaxWF_compileExprArms svars rid arms]
termination_by sizeOf e

theorem staticSyntaxWF_compileExprList (svars : List Ident) (rid : RegionId) (es : List Expr) :
    staticSyntaxWFList (compileExprList svars rid es) = true := by
  cases es with
  | nil => rfl
  | cons e rest =>
    simp [compileExprList, staticSyntaxWFList,
      staticSyntaxWF_compileExpr svars rid e, staticSyntaxWF_compileExprList svars rid rest]
termination_by sizeOf es

theorem staticSyntaxWF_compileExprArms (svars : List Ident) (rid : RegionId)
    (arms : List (Pat × Expr)) :
    staticSyntaxWFArms (compileExprArms svars rid arms) = true := by
  cases arms with
  | nil => rfl
  | cons arm rest =>
    cases arm with
    | mk p body =>
      simp [compileExprArms, staticSyntaxWFArms,
        staticSyntaxWF_compileExpr svars rid body, staticSyntaxWF_compileExprArms svars rid rest]
termination_by sizeOf arms
end

mutual
theorem stackNewWF_of_noRegionSyntax (enc : List RegionId) {e : RExpr}
    (h : noRegionSyntax e = true) : stackNewWF enc e = true := by
  cases e with
  | lit _ | var _ | loc _ | taskRef _ | syncRef _ _ | trap _ => rfl
  | stackCellNew _ _ | frame _ _ => simp [noRegionSyntax] at h
  | tuple es | block es | applyDir _ es | makeData _ _ es | concPrim _ es =>
    simp only [noRegionSyntax] at h
    simp [stackNewWF, stackNewWFList_of_noRegionSyntax enc h]
  | lam _ _ _ body =>
    simp only [noRegionSyntax] at h
    simp [stackNewWF, stackNewWF_of_noRegionSyntax [] h]
  | apply fn args =>
    simp only [noRegionSyntax, Bool.and_eq_true] at h
    simp [stackNewWF, stackNewWF_of_noRegionSyntax enc h.1,
      stackNewWFList_of_noRegionSyntax enc h.2]
  | bin _ e1 e2 | while_ e1 e2 | cellSet e1 e2 =>
    simp only [noRegionSyntax, Bool.and_eq_true] at h
    simp [stackNewWF, stackNewWF_of_noRegionSyntax enc h.1, stackNewWF_of_noRegionSyntax enc h.2]
  | un _ e1 | getTag e1 | cellNew e1 | cellGet e1 | spawn e1 | await e1 =>
    simp only [noRegionSyntax] at h
    simp [stackNewWF, stackNewWF_of_noRegionSyntax enc h]
  | let_ y e1 e2 =>
    simp only [noRegionSyntax, Bool.and_eq_true] at h
    have hsc : asStackCellNew? e1 = none := by
      cases e1 <;> simp [noRegionSyntax] at h <;> rfl
    rw [stackNewWF_let_nonStackCellNew enc y e1 e2 hsc]
    simp [stackNewWF_of_noRegionSyntax enc h.1, stackNewWF_of_noRegionSyntax enc h.2]
  | if_ c t e2 =>
    simp only [noRegionSyntax, Bool.and_eq_true] at h
    simp [stackNewWF, stackNewWF_of_noRegionSyntax enc h.1.1,
      stackNewWF_of_noRegionSyntax enc h.1.2, stackNewWF_of_noRegionSyntax enc h.2]
  | match_ scrut arms =>
    simp only [noRegionSyntax, Bool.and_eq_true] at h
    simp [stackNewWF, stackNewWF_of_noRegionSyntax enc h.1,
      stackNewWFArms_of_noRegionSyntax enc h.2]
termination_by sizeOf e

theorem stackNewWFList_of_noRegionSyntax (enc : List RegionId) {es : List RExpr}
    (h : noRegionSyntaxList es = true) : stackNewWFList enc es = true := by
  cases es with
  | nil => rfl
  | cons e rest =>
    simp only [noRegionSyntaxList, Bool.and_eq_true] at h
    simp [stackNewWFList, stackNewWF_of_noRegionSyntax enc h.1,
      stackNewWFList_of_noRegionSyntax enc h.2]
termination_by sizeOf es

theorem stackNewWFArms_of_noRegionSyntax (enc : List RegionId) {arms : List (Pat × RExpr)}
    (h : noRegionSyntaxArms arms = true) : stackNewWFArms enc arms = true := by
  cases arms with
  | nil => rfl
  | cons arm rest =>
    cases arm with
    | mk p body =>
      simp only [noRegionSyntaxArms, Bool.and_eq_true] at h
      simp [stackNewWFArms, stackNewWF_of_noRegionSyntax enc h.1,
        stackNewWFArms_of_noRegionSyntax enc h.2]
termination_by sizeOf arms
end

mutual
theorem stackNewWF_compileExpr (enc : List RegionId) (svars : List Ident) (rid : RegionId)
    (e : Expr)
    (hrid : svars = [] ∨ enc.contains rid = true)
    (hvars : ∀ x ∈ svars, checkStackVarInExpr x e = true ∨ onlyDirectCellOps x e = true) :
    stackNewWF enc (compileExpr svars rid e) = true := by
  cases e with
  | lit _ | var _ | loc _ | taskRef _ | syncRef _ _ | trap _ => rfl
  | lam m ps ret body =>
    simp only [compileExpr, stackNewWF]
    exact stackNewWF_of_noRegionSyntax [] (noRegionSyntax_compileExpr_nil rid body)
  | tuple es | block es | applyDir _ es | makeData _ _ es | concPrim _ es =>
    simp only [compileExpr, stackNewWF]
    apply stackNewWFList_compileExpr enc svars rid es hrid
    intro x hx
    rcases hvars x hx with h1 | h2
    · left; exact h1
    · right; exact h2
  | apply fn args =>
    simp only [compileExpr, stackNewWF, Bool.and_eq_true]
    refine ⟨stackNewWF_compileExpr enc svars rid fn hrid ?_,
            stackNewWFList_compileExpr enc svars rid args hrid ?_⟩
    · intro x hx
      rcases hvars x hx with h1 | h2
      · simp only [checkStackVarInExpr, Bool.and_eq_true] at h1; exact Or.inl h1.1
      · simp only [onlyDirectCellOps, Bool.and_eq_true] at h2; exact Or.inr h2.1
    · intro x hx
      rcases hvars x hx with h1 | h2
      · simp only [checkStackVarInExpr, Bool.and_eq_true] at h1; exact Or.inl h1.2
      · simp only [onlyDirectCellOps, Bool.and_eq_true] at h2; exact Or.inr h2.2
  | bin _ e1 e2 | while_ e1 e2 =>
    simp only [compileExpr, stackNewWF, Bool.and_eq_true]
    refine ⟨stackNewWF_compileExpr enc svars rid e1 hrid ?_,
            stackNewWF_compileExpr enc svars rid e2 hrid ?_⟩
    · intro x hx
      rcases hvars x hx with h1 | h2
      · simp only [checkStackVarInExpr, Bool.and_eq_true] at h1; exact Or.inl h1.1
      · simp only [onlyDirectCellOps, Bool.and_eq_true] at h2; exact Or.inr h2.1
    · intro x hx
      rcases hvars x hx with h1 | h2
      · simp only [checkStackVarInExpr, Bool.and_eq_true] at h1; exact Or.inl h1.2
      · simp only [onlyDirectCellOps, Bool.and_eq_true] at h2; exact Or.inr h2.2
  | un _ e1 | getTag e1 | cellNew e1 | spawn e1 | await e1 =>
    simp only [compileExpr, stackNewWF]
    apply stackNewWF_compileExpr enc svars rid e1 hrid
    intro x hx
    rcases hvars x hx with h1 | h2
    · exact Or.inl h1
    · exact Or.inr h2
  | cellGet e1 =>
    by_cases hvar : ∃ y, e1 = .var y
    · rcases hvar with ⟨y, rfl⟩
      rfl
    · simp only [compileExpr, stackNewWF]
      apply stackNewWF_compileExpr enc svars rid e1 hrid
      intro x hx
      rcases hvars x hx with h1 | h2
      · exact Or.inl h1
      · simp only [onlyDirectCellOps] at h2
        have hne : (asVar? e1 == some x) = false := by
          cases heq : asVar? e1 with
          | none => rfl
          | some y => exact absurd ⟨y, asVar?_eq_some.mp heq⟩ hvar
        rw [hne] at h2
        exact Or.inr h2
  | cellSet e1 e2 =>
    have he2 : stackNewWF enc (compileExpr svars rid e2) = true := by
      apply stackNewWF_compileExpr enc svars rid e2 hrid
      intro x hx
      rcases hvars x hx with h1 | h2
      · simp only [checkStackVarInExpr, Bool.and_eq_true] at h1; exact Or.inl h1.2
      · simp only [onlyDirectCellOps] at h2
        split at h2
        · exact Or.inr h2
        · simp only [Bool.and_eq_true] at h2; exact Or.inr h2.2
    by_cases hvar : ∃ y, e1 = .var y
    · rcases hvar with ⟨y, rfl⟩
      simp [compileExpr, stackNewWF, he2]
    · have he1 : stackNewWF enc (compileExpr svars rid e1) = true := by
        apply stackNewWF_compileExpr enc svars rid e1 hrid
        intro x hx
        rcases hvars x hx with h1 | h2
        · simp only [checkStackVarInExpr, Bool.and_eq_true] at h1; exact Or.inl h1.1
        · simp only [onlyDirectCellOps] at h2
          have hne : (asVar? e1 == some x) = false := by
            cases heq : asVar? e1 with
            | none => rfl
            | some y => exact absurd ⟨y, asVar?_eq_some.mp heq⟩ hvar
          simp only [hne, Bool.false_eq_true, ↓reduceIte, Bool.and_eq_true] at h2
          exact Or.inr h2.1
      simp [compileExpr, stackNewWF, he1, he2]
  | let_ y e1 e2 =>
    cases hcn : asCellNew? e1 with
    | none =>
      rw [compileExpr_let_nonCellNew _ _ _ _ _ hcn]
      have hsc : asStackCellNew? (compileExpr svars rid e1) = none := by
        cases e1 with
        | let_ z d1 d2 =>
          cases hcn2 : asCellNew? d1 with
          | none => rw [compileExpr_let_nonCellNew _ _ _ _ _ hcn2]; rfl
          | some init2 =>
            rw [asCellNew?_eq_some.mp hcn2]
            simp only [compileExpr]
            split <;> rfl
        | _ => rfl
      rw [stackNewWF_let_nonStackCellNew enc y _ _ hsc, Bool.and_eq_true]
      refine ⟨stackNewWF_compileExpr enc svars rid e1 hrid ?_,
              stackNewWF_compileExpr enc svars rid e2 hrid ?_⟩
      · intro x hx
        rcases hvars x hx with h1 | h2
        · rw [checkStackVarInExpr_let_nonCellNew x y e1 e2 hcn] at h1
          simp only [Bool.and_eq_true] at h1; exact Or.inl h1.1.2
        · simp only [onlyDirectCellOps, Bool.and_eq_true] at h2; exact Or.inr h2.1.2
      · intro x hx
        rcases hvars x hx with h1 | h2
        · rw [checkStackVarInExpr_let_nonCellNew x y e1 e2 hcn] at h1
          simp only [Bool.and_eq_true] at h1; exact Or.inl h1.2
        · simp only [onlyDirectCellOps, Bool.and_eq_true] at h2; exact Or.inr h2.2
    | some init =>
      have he1 := asCellNew?_eq_some.mp hcn
      subst he1
      simp only [compileExpr]
      cases hmem : svars.contains y with
      | true =>
        simp only [↓reduceIte]
        have hy_mem : y ∈ svars := List.contains_iff_mem.mp hmem
        have henc : enc.contains rid = true := by
          rcases hrid with rfl | hc
          · cases hy_mem
          · exact hc
        have hy_chk : checkStackVarInExpr y init = true ∧ onlyDirectCellOps y e2 = true := by
          rcases hvars y hy_mem with h1 | h2
          · simp only [checkStackVarInExpr, beq_self_eq_true, ↓reduceIte, Bool.and_eq_true] at h1
            exact h1
          · simp [onlyDirectCellOps] at h2
        have hinit : stackNewWF enc (compileExpr svars rid init) = true := by
          apply stackNewWF_compileExpr enc svars rid init hrid
          intro x hx
          by_cases hxy : y = x
          · subst hxy; exact Or.inl hy_chk.1
          · rcases hvars x hx with h1 | h2
            · simp only [checkStackVarInExpr, beq_iff_eq, hxy, ↓reduceIte, Bool.and_eq_true] at h1
              exact Or.inl h1.1
            · simp only [onlyDirectCellOps, Bool.and_eq_true] at h2
              exact Or.inr h2.1.2
        have he2 : stackNewWF enc (compileExpr svars rid e2) = true := by
          apply stackNewWF_compileExpr enc svars rid e2 hrid
          intro x hx
          by_cases hxy : y = x
          · subst hxy; exact Or.inr hy_chk.2
          · rcases hvars x hx with h1 | h2
            · simp only [checkStackVarInExpr, beq_iff_eq, hxy, ↓reduceIte, Bool.and_eq_true] at h1
              exact Or.inl h1.2
            · simp only [onlyDirectCellOps, Bool.and_eq_true] at h2
              exact Or.inr h2.2
        simp only [stackNewWF, henc, hinit, he2, rOnlyDirectCellOps_compileExpr, hy_chk.2,
          Bool.and_self]
      | false =>
        simp only [Bool.false_eq_true, ↓reduceIte]
        have hinit : stackNewWF enc (compileExpr svars rid init) = true := by
          apply stackNewWF_compileExpr enc svars rid init hrid
          intro x hx
          have hxy : ¬ (y = x) := fun heq => by
            subst heq
            rw [List.contains_iff_mem.mpr hx] at hmem
            cases hmem
          rcases hvars x hx with h1 | h2
          · simp only [checkStackVarInExpr, beq_iff_eq, hxy, ↓reduceIte, Bool.and_eq_true] at h1
            exact Or.inl h1.1
          · simp only [onlyDirectCellOps, Bool.and_eq_true] at h2
            exact Or.inr h2.1.2
        have he2 : stackNewWF enc (compileExpr svars rid e2) = true := by
          apply stackNewWF_compileExpr enc svars rid e2 hrid
          intro x hx
          have hxy : ¬ (y = x) := fun heq => by
            subst heq
            rw [List.contains_iff_mem.mpr hx] at hmem
            cases hmem
          rcases hvars x hx with h1 | h2
          · simp only [checkStackVarInExpr, beq_iff_eq, hxy, ↓reduceIte, Bool.and_eq_true] at h1
            exact Or.inl h1.2
          · simp only [onlyDirectCellOps, Bool.and_eq_true] at h2
            exact Or.inr h2.2
        simp [stackNewWF, hinit, he2]
  | if_ c t e2 =>
    simp only [compileExpr, stackNewWF, Bool.and_eq_true]
    refine ⟨⟨stackNewWF_compileExpr enc svars rid c hrid ?_,
             stackNewWF_compileExpr enc svars rid t hrid ?_⟩,
            stackNewWF_compileExpr enc svars rid e2 hrid ?_⟩
    · intro x hx
      rcases hvars x hx with h1 | h2
      · simp only [checkStackVarInExpr, Bool.and_eq_true] at h1; exact Or.inl h1.1.1
      · simp only [onlyDirectCellOps, Bool.and_eq_true] at h2; exact Or.inr h2.1.1
    · intro x hx
      rcases hvars x hx with h1 | h2
      · simp only [checkStackVarInExpr, Bool.and_eq_true] at h1; exact Or.inl h1.1.2
      · simp only [onlyDirectCellOps, Bool.and_eq_true] at h2; exact Or.inr h2.1.2
    · intro x hx
      rcases hvars x hx with h1 | h2
      · simp only [checkStackVarInExpr, Bool.and_eq_true] at h1; exact Or.inl h1.2
      · simp only [onlyDirectCellOps, Bool.and_eq_true] at h2; exact Or.inr h2.2
  | match_ scrut arms =>
    simp only [compileExpr, stackNewWF, Bool.and_eq_true]
    refine ⟨stackNewWF_compileExpr enc svars rid scrut hrid ?_,
            stackNewWFArms_compileExpr enc svars rid arms hrid ?_⟩
    · intro x hx
      rcases hvars x hx with h1 | h2
      · simp only [checkStackVarInExpr, Bool.and_eq_true] at h1; exact Or.inl h1.1
      · simp only [onlyDirectCellOps, Bool.and_eq_true] at h2; exact Or.inr h2.1
    · intro x hx
      rcases hvars x hx with h1 | h2
      · simp only [checkStackVarInExpr, Bool.and_eq_true] at h1; exact Or.inl h1.2
      · simp only [onlyDirectCellOps, Bool.and_eq_true] at h2; exact Or.inr h2.2
termination_by sizeOf e

theorem stackNewWFList_compileExpr (enc : List RegionId) (svars : List Ident) (rid : RegionId)
    (es : List Expr)
    (hrid : svars = [] ∨ enc.contains rid = true)
    (hvars : ∀ x ∈ svars, checkStackVarInExprList x es = true ∨ onlyDirectCellOpsList x es = true) :
    stackNewWFList enc (compileExprList svars rid es) = true := by
  cases es with
  | nil => rfl
  | cons e rest =>
    simp only [compileExprList, stackNewWFList, Bool.and_eq_true]
    refine ⟨stackNewWF_compileExpr enc svars rid e hrid ?_,
            stackNewWFList_compileExpr enc svars rid rest hrid ?_⟩
    · intro x hx
      rcases hvars x hx with h1 | h2
      · simp only [checkStackVarInExprList, Bool.and_eq_true] at h1; exact Or.inl h1.1
      · simp only [onlyDirectCellOpsList, Bool.and_eq_true] at h2; exact Or.inr h2.1
    · intro x hx
      rcases hvars x hx with h1 | h2
      · simp only [checkStackVarInExprList, Bool.and_eq_true] at h1; exact Or.inl h1.2
      · simp only [onlyDirectCellOpsList, Bool.and_eq_true] at h2; exact Or.inr h2.2
termination_by sizeOf es

theorem stackNewWFArms_compileExpr (enc : List RegionId) (svars : List Ident) (rid : RegionId)
    (arms : List (Pat × Expr))
    (hrid : svars = [] ∨ enc.contains rid = true)
    (hvars : ∀ x ∈ svars, checkStackVarInExprArms x arms = true ∨ onlyDirectCellOpsArms x arms = true) :
    stackNewWFArms enc (compileExprArms svars rid arms) = true := by
  cases arms with
  | nil => rfl
  | cons arm rest =>
    cases arm with
    | mk p body =>
      simp only [compileExprArms, stackNewWFArms, Bool.and_eq_true]
      refine ⟨stackNewWF_compileExpr enc svars rid body hrid ?_,
              stackNewWFArms_compileExpr enc svars rid rest hrid ?_⟩
      · intro x hx
        rcases hvars x hx with h1 | h2
        · simp only [checkStackVarInExprArms, Bool.and_eq_true] at h1; exact Or.inl h1.1.2
        · simp only [onlyDirectCellOpsArms, Bool.and_eq_true] at h2; exact Or.inr h2.1.2
      · intro x hx
        rcases hvars x hx with h1 | h2
        · simp only [checkStackVarInExprArms, Bool.and_eq_true] at h1; exact Or.inl h1.2
        · simp only [onlyDirectCellOpsArms, Bool.and_eq_true] at h2; exact Or.inr h2.2
termination_by sizeOf arms
end

/-! ### Value, Substitution, Pattern, and Confinement Lemmas -/

theorem noRegionSyntax_of_isRValue {v : RExpr} (hv : IsRValue v)
    (hsw : staticSyntaxWF v = true) : noRegionSyntax v = true := by
  induction hv with
  | lit _ | loc _ | taskRef _ | syncRef _ _ => rfl
  | lam _ _ _ _ => exact hsw
  | tuple _ ih =>
    simp only [staticSyntaxWF] at hsw
    simp only [noRegionSyntax]
    have haux : ∀ (es : List RExpr),
        (∀ e ∈ es, staticSyntaxWF e = true → noRegionSyntax e = true) →
        staticSyntaxWFList es = true → noRegionSyntaxList es = true := by
      intro es
      induction es with
      | nil => intro _ _; rfl
      | cons a rest ihl =>
        intro hall hswl
        simp only [staticSyntaxWFList, Bool.and_eq_true] at hswl
        simp [noRegionSyntaxList, hall a (List.Mem.head _) hswl.1,
          ihl (fun x hx => hall x (List.Mem.tail _ hx)) hswl.2]
    exact haux _ ih hsw
  | makeData _ _ _ ih =>
    simp only [staticSyntaxWF] at hsw
    simp only [noRegionSyntax]
    have haux : ∀ (es : List RExpr),
        (∀ e ∈ es, staticSyntaxWF e = true → noRegionSyntax e = true) →
        staticSyntaxWFList es = true → noRegionSyntaxList es = true := by
      intro es
      induction es with
      | nil => intro _ _; rfl
      | cons a rest ihl =>
        intro hall hswl
        simp only [staticSyntaxWFList, Bool.and_eq_true] at hswl
        simp [noRegionSyntaxList, hall a (List.Mem.head _) hswl.1,
          ihl (fun x hx => hall x (List.Mem.tail _ hx)) hswl.2]
    exact haux _ ih hsw

mutual
theorem exprFrames_of_noRegionSyntax {e : RExpr} (h : noRegionSyntax e = true) :
    exprFrames e = [] := by
  cases e with
  | lit _ | var _ | loc _ | taskRef _ | syncRef _ _ | trap _ => rfl
  | stackCellNew _ _ | frame _ _ => simp [noRegionSyntax] at h
  | tuple es | block es | applyDir _ es | makeData _ _ es | concPrim _ es =>
    simp only [noRegionSyntax] at h
    simp [exprFrames, exprFramesList_of_noRegionSyntax h]
  | lam _ _ _ body =>
    simp only [noRegionSyntax] at h
    simp [exprFrames, exprFrames_of_noRegionSyntax h]
  | apply fn args =>
    simp only [noRegionSyntax, Bool.and_eq_true] at h
    simp [exprFrames, exprFrames_of_noRegionSyntax h.1, exprFramesList_of_noRegionSyntax h.2]
  | bin _ e1 e2 | let_ _ e1 e2 | while_ e1 e2 | cellSet e1 e2 =>
    simp only [noRegionSyntax, Bool.and_eq_true] at h
    simp [exprFrames, exprFrames_of_noRegionSyntax h.1, exprFrames_of_noRegionSyntax h.2]
  | un _ e1 | getTag e1 | cellNew e1 | cellGet e1 | spawn e1 | await e1 =>
    simp only [noRegionSyntax] at h
    simp [exprFrames, exprFrames_of_noRegionSyntax h]
  | if_ c t e2 =>
    simp only [noRegionSyntax, Bool.and_eq_true] at h
    simp [exprFrames, exprFrames_of_noRegionSyntax h.1.1,
      exprFrames_of_noRegionSyntax h.1.2, exprFrames_of_noRegionSyntax h.2]
  | match_ scrut arms =>
    simp only [noRegionSyntax, Bool.and_eq_true] at h
    simp [exprFrames, exprFrames_of_noRegionSyntax h.1, exprFramesArms_of_noRegionSyntax h.2]
termination_by sizeOf e

theorem exprFramesList_of_noRegionSyntax {es : List RExpr} (h : noRegionSyntaxList es = true) :
    exprFramesList es = [] := by
  cases es with
  | nil => rfl
  | cons e rest =>
    simp only [noRegionSyntaxList, Bool.and_eq_true] at h
    simp [exprFramesList, exprFrames_of_noRegionSyntax h.1, exprFramesList_of_noRegionSyntax h.2]
termination_by sizeOf es

theorem exprFramesArms_of_noRegionSyntax {arms : List (Pat × RExpr)}
    (h : noRegionSyntaxArms arms = true) : exprFramesArms arms = [] := by
  cases arms with
  | nil => rfl
  | cons arm rest =>
    cases arm with
    | mk p body =>
      simp only [noRegionSyntaxArms, Bool.and_eq_true] at h
      simp [exprFramesArms, exprFrames_of_noRegionSyntax h.1,
        exprFramesArms_of_noRegionSyntax h.2]
termination_by sizeOf arms
end

theorem rOnlyDirectCellOps_of_isRValue_closed (x : Ident) {v : RExpr}
    (hv : IsRValue v) (hcl : rFreeVars v = []) : rOnlyDirectCellOps x v = true := by
  induction hv with
  | lit _ | loc _ | taskRef _ | syncRef _ _ => rfl
  | lam m ps ret body =>
    simp [rOnlyDirectCellOps, hcl]
  | tuple _ ih =>
    simp only [rFreeVars] at hcl
    simp only [rOnlyDirectCellOps]
    have haux : ∀ (es : List RExpr),
        (∀ e ∈ es, rFreeVars e = [] → rOnlyDirectCellOps x e = true) →
        rFreeVarsList es = [] → rOnlyDirectCellOpsList x es = true := by
      intro es
      induction es with
      | nil => intro _ _; rfl
      | cons a rest ihl =>
        intro hall hfv
        simp only [rFreeVarsList, List.append_eq_nil_iff] at hfv
        simp [rOnlyDirectCellOpsList, hall a (List.Mem.head _) hfv.1,
          ihl (fun u hu => hall u (List.Mem.tail _ hu)) hfv.2]
    exact haux _ ih hcl
  | makeData _ _ _ ih =>
    simp only [rFreeVars] at hcl
    simp only [rOnlyDirectCellOps]
    have haux : ∀ (es : List RExpr),
        (∀ e ∈ es, rFreeVars e = [] → rOnlyDirectCellOps x e = true) →
        rFreeVarsList es = [] → rOnlyDirectCellOpsList x es = true := by
      intro es
      induction es with
      | nil => intro _ _; rfl
      | cons a rest ihl =>
        intro hall hfv
        simp only [rFreeVarsList, List.append_eq_nil_iff] at hfv
        simp [rOnlyDirectCellOpsList, hall a (List.Mem.head _) hfv.1,
          ihl (fun u hu => hall u (List.Mem.tail _ hu)) hfv.2]
    exact haux _ ih hcl

mutual
theorem rSubst_not_free {x : Ident} (u : RExpr) {e : RExpr} (hnf : x ∉ rFreeVars e) :
    rSubst x u e = e := by
  cases e with
  | lit _ | loc _ | taskRef _ | syncRef _ _ | trap _ => rfl
  | var y =>
    simp only [rFreeVars, List.mem_singleton] at hnf
    have hne : (y == x) = false := beq_eq_false_iff_ne.mpr (Ne.symm hnf)
    simp [rSubst, hne]
  | tuple es | block es | applyDir _ es | makeData _ _ es | concPrim _ es =>
    simp only [rFreeVars] at hnf
    simp [rSubst, rSubstList_not_free u hnf]
  | lam m ps ret body =>
    simp only [rSubst]
    cases hbound : ps.any (fun p => p.1 == x) with
    | true => rfl
    | false =>
      simp only [Bool.false_eq_true, ↓reduceIte]
      have hnb : x ∉ rFreeVars body := by
        intro hm
        apply hnf
        simp only [rFreeVars, List.mem_filter]
        exact ⟨hm, by simp [hbound]⟩
      rw [rSubst_not_free u hnb]
  | apply fn args =>
    simp only [rFreeVars, List.mem_append, not_or] at hnf
    simp [rSubst, rSubst_not_free u hnf.1, rSubstList_not_free u hnf.2]
  | bin _ e1 e2 | while_ e1 e2 | cellSet e1 e2 =>
    simp only [rFreeVars, List.mem_append, not_or] at hnf
    simp [rSubst, rSubst_not_free u hnf.1, rSubst_not_free u hnf.2]
  | un _ e1 | getTag e1 | cellNew e1 | stackCellNew _ e1 | cellGet e1
  | spawn e1 | await e1 | frame _ e1 =>
    simp only [rFreeVars] at hnf
    simp [rSubst, rSubst_not_free u hnf]
  | let_ y e1 e2 =>
    simp only [rFreeVars, List.mem_append, not_or] at hnf
    simp only [rSubst]
    cases hyx : (y == x) with
    | true =>
      simp [rSubst_not_free u hnf.1]
    | false =>
      have hne2 : x ∉ rFreeVars e2 := by
        intro hm
        apply hnf.2
        simp only [List.mem_filter]
        have hxy : (x != y) = true := bne_iff_ne.mpr (Ne.symm (beq_eq_false_iff_ne.mp hyx))
        exact ⟨hm, hxy⟩
      simp [rSubst_not_free u hnf.1, rSubst_not_free u hne2]
  | if_ c t e2 =>
    simp only [rFreeVars, List.mem_append, not_or] at hnf
    simp [rSubst, rSubst_not_free u hnf.1.1, rSubst_not_free u hnf.1.2, rSubst_not_free u hnf.2]
  | match_ scrut arms =>
    simp only [rFreeVars, List.mem_append, not_or] at hnf
    simp [rSubst, rSubst_not_free u hnf.1, rSubstArms_not_free u hnf.2]
termination_by sizeOf e

theorem rSubstList_not_free {x : Ident} (u : RExpr) {es : List RExpr}
    (hnf : x ∉ rFreeVarsList es) : rSubstList x u es = es := by
  cases es with
  | nil => rfl
  | cons e rest =>
    simp only [rFreeVarsList, List.mem_append, not_or] at hnf
    simp [rSubstList, rSubst_not_free u hnf.1, rSubstList_not_free u hnf.2]
termination_by sizeOf es

theorem rSubstArms_not_free {x : Ident} (u : RExpr) {arms : List (Pat × RExpr)}
    (hnf : x ∉ rFreeVarsArms arms) : rSubstArms x u arms = arms := by
  cases arms with
  | nil => rfl
  | cons arm rest =>
    cases arm with
    | mk p body =>
      simp only [rFreeVarsArms, List.mem_append, not_or] at hnf
      simp only [rSubstArms]
      cases hpb : (patBoundNames p).contains x with
      | true =>
        simp [rSubstArms_not_free u hnf.2]
      | false =>
        have hnb : x ∉ rFreeVars body := by
          intro hm
          apply hnf.1
          simp only [List.mem_filter, hpb]
          exact ⟨hm, rfl⟩
        simp [rSubst_not_free u hnb, rSubstArms_not_free u hnf.2]
termination_by sizeOf arms
end

mutual
theorem rFreeVars_rSubst_subset {x : Ident} {v : RExpr} (hcl : rFreeVars v = [])
    (e : RExpr) : ∀ z ∈ rFreeVars (rSubst x v e), z ∈ rFreeVars e ∧ z ≠ x := by
  cases e with
  | lit _ | loc _ | taskRef _ | syncRef _ _ | trap _ =>
    intro _ hm; cases hm
  | var y =>
    simp only [rSubst]
    cases hyx : (y == x) with
    | true =>
      simp [hcl]
    | false =>
      intro z hz
      simp only [Bool.false_eq_true, ↓reduceIte, rFreeVars, List.mem_singleton] at hz
      subst hz
      exact ⟨List.Mem.head _, beq_eq_false_iff_ne.mp hyx⟩
  | tuple es | block es | applyDir _ es | makeData _ _ es | concPrim _ es =>
    intro z hz
    exact rFreeVarsList_rSubst_subset hcl es z hz
  | lam m ps ret body =>
    simp only [rSubst]
    cases hbound : ps.any (fun p => p.1 == x) with
    | true =>
      simp only [↓reduceIte, rFreeVars, List.mem_filter]
      intro z ⟨hzb, hnotp⟩
      refine ⟨⟨hzb, hnotp⟩, ?_⟩
      intro hzx
      subst hzx
      simp [hbound] at hnotp
    | false =>
      simp only [Bool.false_eq_true, ↓reduceIte, rFreeVars, List.mem_filter]
      intro z ⟨hzsub, hnotp⟩
      have ⟨hzb, hne⟩ := rFreeVars_rSubst_subset hcl body z hzsub
      exact ⟨⟨hzb, hnotp⟩, hne⟩
  | apply fn args =>
    intro z hz
    simp only [rSubst, rFreeVars, List.mem_append] at hz ⊢
    rcases hz with h1 | h2
    · have ⟨ha, hb⟩ := rFreeVars_rSubst_subset hcl fn z h1
      exact ⟨Or.inl ha, hb⟩
    · have ⟨ha, hb⟩ := rFreeVarsList_rSubst_subset hcl args z h2
      exact ⟨Or.inr ha, hb⟩
  | bin _ e1 e2 | while_ e1 e2 | cellSet e1 e2 =>
    intro z hz
    simp only [rSubst, rFreeVars, List.mem_append] at hz ⊢
    rcases hz with h1 | h2
    · have ⟨ha, hb⟩ := rFreeVars_rSubst_subset hcl e1 z h1
      exact ⟨Or.inl ha, hb⟩
    · have ⟨ha, hb⟩ := rFreeVars_rSubst_subset hcl e2 z h2
      exact ⟨Or.inr ha, hb⟩
  | un _ e1 | getTag e1 | cellNew e1 | stackCellNew _ e1 | cellGet e1
  | spawn e1 | await e1 | frame _ e1 =>
    intro z hz
    exact rFreeVars_rSubst_subset hcl e1 z hz
  | let_ y e1 e2 =>
    intro z hz
    simp only [rSubst] at hz
    cases hyx : (y == x) with
    | true =>
      simp only [hyx, ↓reduceIte, rFreeVars, List.mem_append, List.mem_filter] at hz
      simp only [rFreeVars, List.mem_append, List.mem_filter]
      rcases hz with h1 | ⟨h2, hzy⟩
      · have ⟨ha, hb⟩ := rFreeVars_rSubst_subset hcl e1 z h1
        exact ⟨Or.inl ha, hb⟩
      · have hy_eq : y = x := beq_iff_eq.mp hyx
        subst hy_eq
        exact ⟨Or.inr ⟨h2, hzy⟩, bne_iff_ne.mp hzy⟩
    | false =>
      simp only [hyx, Bool.false_eq_true, ↓reduceIte, rFreeVars, List.mem_append,
        List.mem_filter] at hz
      simp only [rFreeVars, List.mem_append, List.mem_filter]
      rcases hz with h1 | ⟨h2, hzy⟩
      · have ⟨ha, hb⟩ := rFreeVars_rSubst_subset hcl e1 z h1
        exact ⟨Or.inl ha, hb⟩
      · have ⟨ha, hb⟩ := rFreeVars_rSubst_subset hcl e2 z h2
        exact ⟨Or.inr ⟨ha, hzy⟩, hb⟩
  | if_ c t e2 =>
    intro z hz
    simp only [rSubst, rFreeVars, List.mem_append] at hz ⊢
    rcases hz with (h1 | h2) | h3
    · have ⟨ha, hb⟩ := rFreeVars_rSubst_subset hcl c z h1
      exact ⟨Or.inl (Or.inl ha), hb⟩
    · have ⟨ha, hb⟩ := rFreeVars_rSubst_subset hcl t z h2
      exact ⟨Or.inl (Or.inr ha), hb⟩
    · have ⟨ha, hb⟩ := rFreeVars_rSubst_subset hcl e2 z h3
      exact ⟨Or.inr ha, hb⟩
  | match_ scrut arms =>
    intro z hz
    simp only [rSubst, rFreeVars, List.mem_append] at hz ⊢
    rcases hz with h1 | h2
    · have ⟨ha, hb⟩ := rFreeVars_rSubst_subset hcl scrut z h1
      exact ⟨Or.inl ha, hb⟩
    · have ⟨ha, hb⟩ := rFreeVarsArms_rSubst_subset hcl arms z h2
      exact ⟨Or.inr ha, hb⟩
termination_by sizeOf e

theorem rFreeVarsList_rSubst_subset {x : Ident} {v : RExpr} (hcl : rFreeVars v = [])
    (es : List RExpr) : ∀ z ∈ rFreeVarsList (rSubstList x v es), z ∈ rFreeVarsList es ∧ z ≠ x := by
  cases es with
  | nil => intro _ hm; cases hm
  | cons e rest =>
    intro z hz
    simp only [rSubstList, rFreeVarsList, List.mem_append] at hz ⊢
    rcases hz with h1 | h2
    · have ⟨ha, hb⟩ := rFreeVars_rSubst_subset hcl e z h1
      exact ⟨Or.inl ha, hb⟩
    · have ⟨ha, hb⟩ := rFreeVarsList_rSubst_subset hcl rest z h2
      exact ⟨Or.inr ha, hb⟩
termination_by sizeOf es

theorem rFreeVarsArms_rSubst_subset {x : Ident} {v : RExpr} (hcl : rFreeVars v = [])
    (arms : List (Pat × RExpr)) :
    ∀ z ∈ rFreeVarsArms (rSubstArms x v arms), z ∈ rFreeVarsArms arms ∧ z ≠ x := by
  cases arms with
  | nil => intro _ hm; cases hm
  | cons arm rest =>
    cases arm with
    | mk p body =>
      intro z hz
      simp only [rSubstArms, rFreeVarsArms, List.mem_append, List.mem_filter] at hz ⊢
      rcases hz with ⟨hb, hnp⟩ | hrest
      · cases hpb : (patBoundNames p).contains x with
        | true =>
          simp only [hpb, ↓reduceIte] at hb
          refine ⟨Or.inl ⟨hb, hnp⟩, ?_⟩
          intro hzx
          subst hzx
          rw [hpb] at hnp
          cases hnp
        | false =>
          simp only [hpb, Bool.false_eq_true, ↓reduceIte] at hb
          have ⟨ha, hne⟩ := rFreeVars_rSubst_subset hcl body z hb
          exact ⟨Or.inl ⟨ha, hnp⟩, hne⟩
      · have ⟨ha, hne⟩ := rFreeVarsArms_rSubst_subset hcl rest z hrest
        exact ⟨Or.inr ha, hne⟩
termination_by sizeOf arms
end

theorem rFreeVars_rSubstMany_subset {bs : List (Ident × RExpr)}
    (hcl : ∀ b ∈ bs, rFreeVars b.2 = []) (e : RExpr) :
    ∀ z ∈ rFreeVars (rSubstMany bs e), z ∈ rFreeVars e ∧ ∀ b ∈ bs, z ≠ b.1 := by
  induction bs generalizing e with
  | nil =>
    intro z hz
    exact ⟨hz, fun _ hm => nomatch hm⟩
  | cons hd tl ih =>
    cases hd with
    | mk x v =>
      intro z hz
      simp only [rSubstMany] at hz
      have ⟨hz1, hnot_tl⟩ := ih (fun b hb => hcl b (List.Mem.tail _ hb)) (rSubst x v e) z hz
      have ⟨hze, hzx⟩ := rFreeVars_rSubst_subset (hcl (x, v) (List.Mem.head _)) e z hz1
      refine ⟨hze, fun b hb => ?_⟩
      rcases List.mem_cons.mp hb with rfl | hbtl
      · exact hzx
      · exact hnot_tl b hbtl

mutual
theorem rExprLocs_rSubst_subset (x : Ident) (v e : RExpr) :
    ∀ l ∈ rExprLocs (rSubst x v e), l ∈ rExprLocs e ∨ l ∈ rExprLocs v := by
  cases e with
  | lit _ | loc _ | taskRef _ | syncRef _ _ | trap _ =>
    intro l hl; exact Or.inl hl
  | var y =>
    simp only [rSubst]
    split
    · intro l hl; exact Or.inr hl
    · intro _ hl; cases hl
  | tuple es | block es | applyDir _ es | makeData _ _ es | concPrim _ es =>
    intro l hl
    exact rExprLocsList_rSubst_subset x v es l hl
  | lam m ps ret body =>
    simp only [rSubst]
    split
    · intro l hl; exact Or.inl hl
    · intro l hl; exact rExprLocs_rSubst_subset x v body l hl
  | apply fn args =>
    intro l hl
    simp only [rSubst, rExprLocs, List.mem_append] at hl ⊢
    rcases hl with h1 | h2
    · exact (rExprLocs_rSubst_subset x v fn l h1).imp Or.inl id
    · exact (rExprLocsList_rSubst_subset x v args l h2).imp Or.inr id
  | bin _ e1 e2 | while_ e1 e2 | cellSet e1 e2 =>
    intro l hl
    simp only [rSubst, rExprLocs, List.mem_append] at hl ⊢
    rcases hl with h1 | h2
    · exact (rExprLocs_rSubst_subset x v e1 l h1).imp Or.inl id
    · exact (rExprLocs_rSubst_subset x v e2 l h2).imp Or.inr id
  | un _ e1 | getTag e1 | cellNew e1 | stackCellNew _ e1 | cellGet e1
  | spawn e1 | await e1 | frame _ e1 =>
    intro l hl
    exact rExprLocs_rSubst_subset x v e1 l hl
  | let_ y e1 e2 =>
    intro l hl
    simp only [rSubst] at hl
    split at hl
    · simp only [rExprLocs, List.mem_append] at hl ⊢
      rcases hl with h1 | h2
      · exact (rExprLocs_rSubst_subset x v e1 l h1).imp Or.inl id
      · exact Or.inl (Or.inr h2)
    · simp only [rExprLocs, List.mem_append] at hl ⊢
      rcases hl with h1 | h2
      · exact (rExprLocs_rSubst_subset x v e1 l h1).imp Or.inl id
      · exact (rExprLocs_rSubst_subset x v e2 l h2).imp Or.inr id
  | if_ c t e2 =>
    intro l hl
    simp only [rSubst, rExprLocs, List.mem_append] at hl ⊢
    rcases hl with (h1 | h2) | h3
    · exact (rExprLocs_rSubst_subset x v c l h1).imp (fun hc => Or.inl (Or.inl hc)) id
    · exact (rExprLocs_rSubst_subset x v t l h2).imp (fun ht => Or.inl (Or.inr ht)) id
    · exact (rExprLocs_rSubst_subset x v e2 l h3).imp Or.inr id
  | match_ scrut arms =>
    intro l hl
    simp only [rSubst, rExprLocs, List.mem_append] at hl ⊢
    rcases hl with h1 | h2
    · exact (rExprLocs_rSubst_subset x v scrut l h1).imp Or.inl id
    · exact (rExprLocsArms_rSubst_subset x v arms l h2).imp Or.inr id
termination_by sizeOf e

theorem rExprLocsList_rSubst_subset (x : Ident) (v : RExpr) (es : List RExpr) :
    ∀ l ∈ rExprLocsList (rSubstList x v es), l ∈ rExprLocsList es ∨ l ∈ rExprLocs v := by
  cases es with
  | nil => intro _ hm; cases hm
  | cons e rest =>
    intro l hl
    simp only [rSubstList, rExprLocsList, List.mem_append] at hl ⊢
    rcases hl with h1 | h2
    · exact (rExprLocs_rSubst_subset x v e l h1).imp Or.inl id
    · exact (rExprLocsList_rSubst_subset x v rest l h2).imp Or.inr id
termination_by sizeOf es

theorem rExprLocsArms_rSubst_subset (x : Ident) (v : RExpr) (arms : List (Pat × RExpr)) :
    ∀ l ∈ rExprLocsArms (rSubstArms x v arms), l ∈ rExprLocsArms arms ∨ l ∈ rExprLocs v := by
  cases arms with
  | nil => intro _ hm; cases hm
  | cons arm rest =>
    cases arm with
    | mk p body =>
      intro l hl
      simp only [rSubstArms, rExprLocsArms, List.mem_append] at hl ⊢
      rcases hl with h1 | h2
      · split at h1
        · exact Or.inl (Or.inl h1)
        · exact (rExprLocs_rSubst_subset x v body l h1).imp Or.inl id
      · exact (rExprLocsArms_rSubst_subset x v rest l h2).imp Or.inr id
termination_by sizeOf arms
end

theorem rExprLocs_rSubstMany_subset (bs : List (Ident × RExpr)) (e : RExpr) :
    ∀ l ∈ rExprLocs (rSubstMany bs e), l ∈ rExprLocs e ∨ ∃ b ∈ bs, l ∈ rExprLocs b.2 := by
  induction bs generalizing e with
  | nil => intro l hl; exact Or.inl hl
  | cons hd tl ih =>
    cases hd with
    | mk x v =>
      intro l hl
      rcases ih (rSubst x v e) l hl with h1 | ⟨b, hb, hlb⟩
      · rcases rExprLocs_rSubst_subset x v e l h1 with he | hv
        · exact Or.inl he
        · exact Or.inr ⟨(x, v), List.Mem.head _, hv⟩
      · exact Or.inr ⟨b, List.Mem.tail _ hb, hlb⟩

mutual
theorem noRegionSyntax_rSubst (x : Ident) {v e : RExpr}
    (hv : noRegionSyntax v = true) (he : noRegionSyntax e = true) :
    noRegionSyntax (rSubst x v e) = true := by
  cases e with
  | lit _ | loc _ | taskRef _ | syncRef _ _ | trap _ => rfl
  | var y =>
    simp only [rSubst]
    split
    · exact hv
    · rfl
  | stackCellNew _ _ | frame _ _ => simp [noRegionSyntax] at he
  | tuple es | block es | applyDir _ es | makeData _ _ es | concPrim _ es =>
    simp only [noRegionSyntax] at he
    simp [rSubst, noRegionSyntax, noRegionSyntaxList_rSubst x hv he]
  | lam m ps ret body =>
    simp only [noRegionSyntax] at he
    simp only [rSubst]
    split
    · exact he
    · exact noRegionSyntax_rSubst x hv he
  | apply fn args =>
    simp only [noRegionSyntax, Bool.and_eq_true] at he
    simp [rSubst, noRegionSyntax,
      noRegionSyntax_rSubst x hv he.1, noRegionSyntaxList_rSubst x hv he.2]
  | bin _ e1 e2 | while_ e1 e2 | cellSet e1 e2 =>
    simp only [noRegionSyntax, Bool.and_eq_true] at he
    simp [rSubst, noRegionSyntax,
      noRegionSyntax_rSubst x hv he.1, noRegionSyntax_rSubst x hv he.2]
  | un _ e1 | getTag e1 | cellNew e1 | cellGet e1 | spawn e1 | await e1 =>
    simp only [noRegionSyntax] at he
    simp [rSubst, noRegionSyntax, noRegionSyntax_rSubst x hv he]
  | let_ y e1 e2 =>
    simp only [noRegionSyntax, Bool.and_eq_true] at he
    simp only [rSubst]
    split
    · simp [noRegionSyntax, noRegionSyntax_rSubst x hv he.1, he.2]
    · simp [noRegionSyntax, noRegionSyntax_rSubst x hv he.1, noRegionSyntax_rSubst x hv he.2]
  | if_ c t e2 =>
    simp only [noRegionSyntax, Bool.and_eq_true] at he
    simp [rSubst, noRegionSyntax, noRegionSyntax_rSubst x hv he.1.1,
      noRegionSyntax_rSubst x hv he.1.2, noRegionSyntax_rSubst x hv he.2]
  | match_ scrut arms =>
    simp only [noRegionSyntax, Bool.and_eq_true] at he
    simp [rSubst, noRegionSyntax,
      noRegionSyntax_rSubst x hv he.1, noRegionSyntaxArms_rSubst x hv he.2]
termination_by sizeOf e

theorem noRegionSyntaxList_rSubst (x : Ident) {v : RExpr} {es : List RExpr}
    (hv : noRegionSyntax v = true) (he : noRegionSyntaxList es = true) :
    noRegionSyntaxList (rSubstList x v es) = true := by
  cases es with
  | nil => rfl
  | cons e rest =>
    simp only [noRegionSyntaxList, Bool.and_eq_true] at he
    simp [rSubstList, noRegionSyntaxList,
      noRegionSyntax_rSubst x hv he.1, noRegionSyntaxList_rSubst x hv he.2]
termination_by sizeOf es

theorem noRegionSyntaxArms_rSubst (x : Ident) {v : RExpr} {arms : List (Pat × RExpr)}
    (hv : noRegionSyntax v = true) (he : noRegionSyntaxArms arms = true) :
    noRegionSyntaxArms (rSubstArms x v arms) = true := by
  cases arms with
  | nil => rfl
  | cons arm rest =>
    cases arm with
    | mk p body =>
      simp only [noRegionSyntaxArms, Bool.and_eq_true] at he
      simp only [rSubstArms, noRegionSyntaxArms, Bool.and_eq_true]
      refine ⟨?_, noRegionSyntaxArms_rSubst x hv he.2⟩
      split
      · exact he.1
      · exact noRegionSyntax_rSubst x hv he.1
termination_by sizeOf arms
end

mutual
theorem exprFrames_rSubst (x : Ident) {v : RExpr} (hv : exprFrames v = []) (e : RExpr) :
    exprFrames (rSubst x v e) = exprFrames e := by
  cases e with
  | lit _ | loc _ | taskRef _ | syncRef _ _ | trap _ => rfl
  | var y =>
    simp only [rSubst]
    split
    · exact hv
    · rfl
  | tuple es | block es | applyDir _ es | makeData _ _ es | concPrim _ es =>
    simp [rSubst, exprFrames, exprFramesList_rSubst x hv es]
  | lam m ps ret body =>
    simp only [rSubst]
    split
    · rfl
    · simp [exprFrames, exprFrames_rSubst x hv body]
  | apply fn args =>
    simp [rSubst, exprFrames, exprFrames_rSubst x hv fn, exprFramesList_rSubst x hv args]
  | bin _ e1 e2 | while_ e1 e2 | cellSet e1 e2 =>
    simp [rSubst, exprFrames, exprFrames_rSubst x hv e1, exprFrames_rSubst x hv e2]
  | un _ e1 | getTag e1 | cellNew e1 | stackCellNew _ e1 | cellGet e1
  | spawn e1 | await e1 | frame _ e1 =>
    simp [rSubst, exprFrames, exprFrames_rSubst x hv e1]
  | let_ y e1 e2 =>
    simp only [rSubst]
    split <;> simp [exprFrames, exprFrames_rSubst x hv e1, exprFrames_rSubst x hv e2]
  | if_ c t e2 =>
    simp [rSubst, exprFrames, exprFrames_rSubst x hv c,
      exprFrames_rSubst x hv t, exprFrames_rSubst x hv e2]
  | match_ scrut arms =>
    simp [rSubst, exprFrames, exprFrames_rSubst x hv scrut, exprFramesArms_rSubst x hv arms]
termination_by sizeOf e

theorem exprFramesList_rSubst (x : Ident) {v : RExpr} (hv : exprFrames v = [])
    (es : List RExpr) : exprFramesList (rSubstList x v es) = exprFramesList es := by
  cases es with
  | nil => rfl
  | cons e rest =>
    simp [rSubstList, exprFramesList,
      exprFrames_rSubst x hv e, exprFramesList_rSubst x hv rest]
termination_by sizeOf es

theorem exprFramesArms_rSubst (x : Ident) {v : RExpr} (hv : exprFrames v = [])
    (arms : List (Pat × RExpr)) :
    exprFramesArms (rSubstArms x v arms) = exprFramesArms arms := by
  cases arms with
  | nil => rfl
  | cons arm rest =>
    cases arm with
    | mk p body =>
      simp only [rSubstArms, exprFramesArms]
      split <;> simp [exprFrames_rSubst x hv body, exprFramesArms_rSubst x hv rest]
termination_by sizeOf arms
end

theorem exprFrames_rSubstMany {bs : List (Ident × RExpr)}
    (hv : ∀ b ∈ bs, exprFrames b.2 = []) (e : RExpr) :
    exprFrames (rSubstMany bs e) = exprFrames e := by
  induction bs generalizing e with
  | nil => rfl
  | cons hd tl ih =>
    cases hd with
    | mk x v =>
      simp only [rSubstMany]
      rw [ih (fun b hb => hv b (List.Mem.tail _ hb)),
          exprFrames_rSubst x (hv (x, v) (List.Mem.head _)) e]

mutual
theorem staticSyntaxWF_rSubst (x : Ident) {v e : RExpr}
    (hsw : staticSyntaxWF v = true) (hnr : noRegionSyntax v = true)
    (he : staticSyntaxWF e = true) :
    staticSyntaxWF (rSubst x v e) = true := by
  cases e with
  | lit _ | loc _ | taskRef _ | syncRef _ _ | trap _ => rfl
  | var y =>
    simp only [rSubst]
    split
    · exact hsw
    · rfl
  | tuple es | block es | applyDir _ es | makeData _ _ es | concPrim _ es =>
    simp only [staticSyntaxWF] at he
    simp [rSubst, staticSyntaxWF, staticSyntaxWFList_rSubst x hsw hnr he]
  | lam m ps ret body =>
    simp only [staticSyntaxWF] at he
    simp only [rSubst]
    split
    · exact he
    · exact noRegionSyntax_rSubst x hnr he
  | apply fn args =>
    simp only [staticSyntaxWF, Bool.and_eq_true] at he
    simp [rSubst, staticSyntaxWF,
      staticSyntaxWF_rSubst x hsw hnr he.1, staticSyntaxWFList_rSubst x hsw hnr he.2]
  | bin _ e1 e2 | cellSet e1 e2 =>
    simp only [staticSyntaxWF, Bool.and_eq_true] at he
    simp [rSubst, staticSyntaxWF,
      staticSyntaxWF_rSubst x hsw hnr he.1, staticSyntaxWF_rSubst x hsw hnr he.2]
  | while_ c b =>
    simp only [staticSyntaxWF, Bool.and_eq_true] at he
    have hvf : exprFrames v = [] := exprFrames_of_noRegionSyntax hnr
    simp [rSubst, staticSyntaxWF, exprFrames_rSubst x hvf c, exprFrames_rSubst x hvf b,
      he.1.1.1, he.1.1.2,
      staticSyntaxWF_rSubst x hsw hnr he.1.2, staticSyntaxWF_rSubst x hsw hnr he.2]
  | un _ e1 | getTag e1 | cellNew e1 | stackCellNew _ e1 | cellGet e1
  | spawn e1 | await e1 | frame _ e1 =>
    simp only [staticSyntaxWF] at he
    simp [rSubst, staticSyntaxWF, staticSyntaxWF_rSubst x hsw hnr he]
  | let_ y e1 e2 =>
    simp only [staticSyntaxWF, Bool.and_eq_true] at he
    simp only [rSubst]
    split
    · simp [staticSyntaxWF, staticSyntaxWF_rSubst x hsw hnr he.1, he.2]
    · simp [staticSyntaxWF, staticSyntaxWF_rSubst x hsw hnr he.1,
        staticSyntaxWF_rSubst x hsw hnr he.2]
  | if_ c t e2 =>
    simp only [staticSyntaxWF, Bool.and_eq_true] at he
    simp [rSubst, staticSyntaxWF, staticSyntaxWF_rSubst x hsw hnr he.1.1,
      staticSyntaxWF_rSubst x hsw hnr he.1.2, staticSyntaxWF_rSubst x hsw hnr he.2]
  | match_ scrut arms =>
    simp only [staticSyntaxWF, Bool.and_eq_true] at he
    simp [rSubst, staticSyntaxWF,
      staticSyntaxWF_rSubst x hsw hnr he.1, staticSyntaxWFArms_rSubst x hsw hnr he.2]
termination_by sizeOf e

theorem staticSyntaxWFList_rSubst (x : Ident) {v : RExpr} {es : List RExpr}
    (hsw : staticSyntaxWF v = true) (hnr : noRegionSyntax v = true)
    (he : staticSyntaxWFList es = true) :
    staticSyntaxWFList (rSubstList x v es) = true := by
  cases es with
  | nil => rfl
  | cons e rest =>
    simp only [staticSyntaxWFList, Bool.and_eq_true] at he
    simp [rSubstList, staticSyntaxWFList,
      staticSyntaxWF_rSubst x hsw hnr he.1, staticSyntaxWFList_rSubst x hsw hnr he.2]
termination_by sizeOf es

theorem staticSyntaxWFArms_rSubst (x : Ident) {v : RExpr} {arms : List (Pat × RExpr)}
    (hsw : staticSyntaxWF v = true) (hnr : noRegionSyntax v = true)
    (he : staticSyntaxWFArms arms = true) :
    staticSyntaxWFArms (rSubstArms x v arms) = true := by
  cases arms with
  | nil => rfl
  | cons arm rest =>
    cases arm with
    | mk p body =>
      simp only [staticSyntaxWFArms, Bool.and_eq_true] at he
      simp only [rSubstArms, staticSyntaxWFArms, Bool.and_eq_true]
      refine ⟨?_, staticSyntaxWFArms_rSubst x hsw hnr he.2⟩
      split
      · exact he.1
      · exact staticSyntaxWF_rSubst x hsw hnr he.1
termination_by sizeOf arms
end

theorem staticSyntaxWF_rSubstMany {bs : List (Ident × RExpr)}
    (hsw : ∀ b ∈ bs, staticSyntaxWF b.2 = true)
    (hnr : ∀ b ∈ bs, noRegionSyntax b.2 = true)
    {e : RExpr} (he : staticSyntaxWF e = true) :
    staticSyntaxWF (rSubstMany bs e) = true := by
  induction bs generalizing e with
  | nil => exact he
  | cons hd tl ih =>
    cases hd with
    | mk x v =>
      exact ih (fun b hb => hsw b (List.Mem.tail _ hb))
        (fun b hb => hnr b (List.Mem.tail _ hb))
        (staticSyntaxWF_rSubst x (hsw (x, v) (List.Mem.head _))
          (hnr (x, v) (List.Mem.head _)) he)

theorem rAsVar?_rSubst_ne_of_isRValue {x z : Ident} {v e : RExpr}
    (hv : IsRValue v) (he : (rAsVar? e == some x) = false) :
    (rAsVar? (rSubst z v e) == some x) = false := by
  cases e with
  | var y =>
    simp only [rSubst]
    cases hyz : (y == z) with
    | true => simp [rAsVar?_of_isRValue hv]
    | false => exact he
  | let_ y e1 e2 =>
    simp only [rSubst]; split <;> rfl
  | lam m ps ret body =>
    simp only [rSubst]; split <;> rfl
  | _ => rfl

mutual
theorem rOnlyDirectCellOps_rSubst_other {x z : Ident} {v e : RExpr}
    (hne : z ≠ x) (hv : IsRValue v) (hcl : rFreeVars v = [])
    (he : rOnlyDirectCellOps x e = true) :
    rOnlyDirectCellOps x (rSubst z v e) = true := by
  cases e with
  | lit _ | loc _ | taskRef _ | syncRef _ _ | trap _ => rfl
  | var y =>
    simp only [rSubst]
    split
    · exact rOnlyDirectCellOps_of_isRValue_closed x hv hcl
    · exact he
  | tuple es | block es | applyDir _ es | makeData _ _ es | concPrim _ es =>
    simp only [rOnlyDirectCellOps] at he
    simp [rSubst, rOnlyDirectCellOps, rOnlyDirectCellOpsList_rSubst_other hne hv hcl he]
  | lam m ps ret body =>
    simp only [rSubst]
    split
    · exact he
    · simp only [rOnlyDirectCellOps] at he ⊢
      cases hmem : (rFreeVars (.lam m ps ret (rSubst z v body))).contains x with
      | false => rfl
      | true =>
        have hx := List.contains_iff_mem.mp hmem
        simp only [rFreeVars, List.mem_filter] at hx
        have ⟨hxb, _⟩ := rFreeVars_rSubst_subset hcl body x hx.1
        have hx_orig : x ∈ rFreeVars (.lam m ps ret body) := by
          simp only [rFreeVars, List.mem_filter]
          exact ⟨hxb, hx.2⟩
        rw [List.contains_iff_mem.mpr hx_orig] at he
        cases he
  | apply fn args =>
    simp only [rOnlyDirectCellOps, Bool.and_eq_true] at he
    simp [rSubst, rOnlyDirectCellOps,
      rOnlyDirectCellOps_rSubst_other hne hv hcl he.1,
      rOnlyDirectCellOpsList_rSubst_other hne hv hcl he.2]
  | bin _ e1 e2 | while_ e1 e2 =>
    simp only [rOnlyDirectCellOps, Bool.and_eq_true] at he
    simp [rSubst, rOnlyDirectCellOps,
      rOnlyDirectCellOps_rSubst_other hne hv hcl he.1,
      rOnlyDirectCellOps_rSubst_other hne hv hcl he.2]
  | un _ e1 | getTag e1 | cellNew e1 | stackCellNew _ e1 | spawn e1 | await e1 | frame _ e1 =>
    simp only [rOnlyDirectCellOps] at he
    simp [rSubst, rOnlyDirectCellOps, rOnlyDirectCellOps_rSubst_other hne hv hcl he]
  | cellGet e1 =>
    simp only [rOnlyDirectCellOps] at he
    cases hvar : (rAsVar? e1 == some x) with
    | true =>
      have heq : e1 = .var x := rAsVar?_eq_some.mp (beq_iff_eq.mp hvar)
      subst heq
      have hxz : (x == z) = false := beq_eq_false_iff_ne.mpr (Ne.symm hne)
      simp [rSubst, hxz, rOnlyDirectCellOps, rAsVar?]
    | false =>
      simp only [hvar, Bool.false_eq_true, ↓reduceIte] at he
      have hvar' := rAsVar?_rSubst_ne_of_isRValue (z := z) hv hvar
      simp [rSubst, rOnlyDirectCellOps, hvar',
        rOnlyDirectCellOps_rSubst_other hne hv hcl he]
  | cellSet e1 e2 =>
    simp only [rOnlyDirectCellOps] at he
    cases hvar : (rAsVar? e1 == some x) with
    | true =>
      have heq : e1 = .var x := rAsVar?_eq_some.mp (beq_iff_eq.mp hvar)
      subst heq
      simp only [rAsVar?, beq_self_eq_true, ↓reduceIte] at he
      have hxz : (x == z) = false := beq_eq_false_iff_ne.mpr (Ne.symm hne)
      simp [rSubst, hxz, rOnlyDirectCellOps, rAsVar?,
        rOnlyDirectCellOps_rSubst_other hne hv hcl he]
    | false =>
      simp only [hvar, Bool.false_eq_true, ↓reduceIte, Bool.and_eq_true] at he
      have hvar' := rAsVar?_rSubst_ne_of_isRValue (z := z) hv hvar
      simp [rSubst, rOnlyDirectCellOps, hvar',
        rOnlyDirectCellOps_rSubst_other hne hv hcl he.1,
        rOnlyDirectCellOps_rSubst_other hne hv hcl he.2]
  | let_ y e1 e2 =>
    simp only [rOnlyDirectCellOps, Bool.and_eq_true] at he
    simp only [rSubst]
    split
    · simp [rOnlyDirectCellOps, he.1.1,
        rOnlyDirectCellOps_rSubst_other hne hv hcl he.1.2, he.2]
    · simp [rOnlyDirectCellOps, he.1.1,
        rOnlyDirectCellOps_rSubst_other hne hv hcl he.1.2,
        rOnlyDirectCellOps_rSubst_other hne hv hcl he.2]
  | if_ c t e2 =>
    simp only [rOnlyDirectCellOps, Bool.and_eq_true] at he
    simp [rSubst, rOnlyDirectCellOps,
      rOnlyDirectCellOps_rSubst_other hne hv hcl he.1.1,
      rOnlyDirectCellOps_rSubst_other hne hv hcl he.1.2,
      rOnlyDirectCellOps_rSubst_other hne hv hcl he.2]
  | match_ scrut arms =>
    simp only [rOnlyDirectCellOps, Bool.and_eq_true] at he
    simp [rSubst, rOnlyDirectCellOps,
      rOnlyDirectCellOps_rSubst_other hne hv hcl he.1,
      rOnlyDirectCellOpsArms_rSubst_other hne hv hcl he.2]
termination_by sizeOf e

theorem rOnlyDirectCellOpsList_rSubst_other {x z : Ident} {v : RExpr} {es : List RExpr}
    (hne : z ≠ x) (hv : IsRValue v) (hcl : rFreeVars v = [])
    (he : rOnlyDirectCellOpsList x es = true) :
    rOnlyDirectCellOpsList x (rSubstList z v es) = true := by
  cases es with
  | nil => rfl
  | cons e rest =>
    simp only [rOnlyDirectCellOpsList, Bool.and_eq_true] at he
    simp [rSubstList, rOnlyDirectCellOpsList,
      rOnlyDirectCellOps_rSubst_other hne hv hcl he.1,
      rOnlyDirectCellOpsList_rSubst_other hne hv hcl he.2]
termination_by sizeOf es

theorem rOnlyDirectCellOpsArms_rSubst_other {x z : Ident} {v : RExpr}
    {arms : List (Pat × RExpr)}
    (hne : z ≠ x) (hv : IsRValue v) (hcl : rFreeVars v = [])
    (he : rOnlyDirectCellOpsArms x arms = true) :
    rOnlyDirectCellOpsArms x (rSubstArms z v arms) = true := by
  cases arms with
  | nil => rfl
  | cons arm rest =>
    cases arm with
    | mk p body =>
      simp only [rOnlyDirectCellOpsArms, Bool.and_eq_true] at he
      simp only [rSubstArms, rOnlyDirectCellOpsArms, Bool.and_eq_true]
      refine ⟨⟨he.1.1, ?_⟩, rOnlyDirectCellOpsArms_rSubst_other hne hv hcl he.2⟩
      split
      · exact he.1.2
      · exact rOnlyDirectCellOps_rSubst_other hne hv hcl he.1.2
termination_by sizeOf arms
end

theorem asStackCellNew?_rSubst_eq_none {z : Ident} {v e : RExpr}
    (hv : IsRValue v) (h : asStackCellNew? e = none) :
    asStackCellNew? (rSubst z v e) = none := by
  cases e with
  | var y =>
    simp only [rSubst]
    split
    · cases hv <;> rfl
    · rfl
  | stackCellNew _ _ => simp [asStackCellNew?] at h
  | lam _ _ _ _ => simp only [rSubst]; split <;> rfl
  | let_ _ _ _ => simp only [rSubst]; split <;> rfl
  | _ => rfl

mutual
theorem stackNewWF_rSubst (enc : List RegionId) (z : Ident) {v e : RExpr}
    (hv : IsRValue v) (hcl : rFreeVars v = []) (hsw : staticSyntaxWF v = true)
    (he : stackNewWF enc e = true) :
    stackNewWF enc (rSubst z v e) = true := by
  cases e with
  | lit _ | loc _ | taskRef _ | syncRef _ _ | trap _ => rfl
  | stackCellNew _ _ => simp [stackNewWF] at he
  | var y =>
    simp only [rSubst]
    split
    · exact stackNewWF_of_noRegionSyntax enc (noRegionSyntax_of_isRValue hv hsw)
    · rfl
  | tuple es | block es | applyDir _ es | makeData _ _ es | concPrim _ es =>
    simp only [stackNewWF] at he
    simp [rSubst, stackNewWF, stackNewWFList_rSubst enc z hv hcl hsw he]
  | lam m ps ret body =>
    simp only [stackNewWF] at he
    simp only [rSubst]
    split
    · exact he
    · exact stackNewWF_rSubst [] z hv hcl hsw he
  | apply fn args =>
    simp only [stackNewWF, Bool.and_eq_true] at he
    simp [rSubst, stackNewWF,
      stackNewWF_rSubst enc z hv hcl hsw he.1,
      stackNewWFList_rSubst enc z hv hcl hsw he.2]
  | bin _ e1 e2 | while_ e1 e2 | cellSet e1 e2 =>
    simp only [stackNewWF, Bool.and_eq_true] at he
    simp [rSubst, stackNewWF,
      stackNewWF_rSubst enc z hv hcl hsw he.1,
      stackNewWF_rSubst enc z hv hcl hsw he.2]
  | un _ e1 | getTag e1 | cellNew e1 | cellGet e1 | spawn e1 | await e1 =>
    simp only [stackNewWF] at he
    simp [rSubst, stackNewWF, stackNewWF_rSubst enc z hv hcl hsw he]
  | frame rid e1 =>
    simp only [stackNewWF] at he
    simp [rSubst, stackNewWF, stackNewWF_rSubst (rid :: enc) z hv hcl hsw he]
  | let_ y e1 e2 =>
    cases hsc : asStackCellNew? e1 with
    | none =>
      rw [stackNewWF_let_nonStackCellNew enc y e1 e2 hsc, Bool.and_eq_true] at he
      simp only [rSubst]
      have hsc' := asStackCellNew?_rSubst_eq_none (z := z) hv hsc
      cases hyz : (y == z) with
      | true =>
        simp only [↓reduceIte]
        rw [stackNewWF_let_nonStackCellNew enc y _ _ hsc']
        simp [stackNewWF_rSubst enc z hv hcl hsw he.1, he.2]
      | false =>
        simp only [Bool.false_eq_true, ↓reduceIte]
        rw [stackNewWF_let_nonStackCellNew enc y _ _ hsc']
        simp [stackNewWF_rSubst enc z hv hcl hsw he.1,
          stackNewWF_rSubst enc z hv hcl hsw he.2]
    | some p =>
      cases p with
      | mk rid init =>
        have he1 := asStackCellNew?_eq_some.mp hsc
        subst he1
        simp only [stackNewWF, Bool.and_eq_true] at he
        simp only [rSubst]
        cases hyz : (y == z) with
        | true =>
          simp only [↓reduceIte, stackNewWF, Bool.and_eq_true]
          exact ⟨⟨⟨he.1.1.1, stackNewWF_rSubst enc z hv hcl hsw he.1.1.2⟩, he.1.2⟩, he.2⟩
        | false =>
          simp only [Bool.false_eq_true, ↓reduceIte, stackNewWF, Bool.and_eq_true]
          have hne : z ≠ y := Ne.symm (beq_eq_false_iff_ne.mp hyz)
          exact ⟨⟨⟨he.1.1.1, stackNewWF_rSubst enc z hv hcl hsw he.1.1.2⟩,
            stackNewWF_rSubst enc z hv hcl hsw he.1.2⟩,
            rOnlyDirectCellOps_rSubst_other hne hv hcl he.2⟩
  | if_ c t e2 =>
    simp only [stackNewWF, Bool.and_eq_true] at he
    simp [rSubst, stackNewWF,
      stackNewWF_rSubst enc z hv hcl hsw he.1.1,
      stackNewWF_rSubst enc z hv hcl hsw he.1.2,
      stackNewWF_rSubst enc z hv hcl hsw he.2]
  | match_ scrut arms =>
    simp only [stackNewWF, Bool.and_eq_true] at he
    simp [rSubst, stackNewWF,
      stackNewWF_rSubst enc z hv hcl hsw he.1,
      stackNewWFArms_rSubst enc z hv hcl hsw he.2]
termination_by sizeOf e

theorem stackNewWFList_rSubst (enc : List RegionId) (z : Ident) {v : RExpr} {es : List RExpr}
    (hv : IsRValue v) (hcl : rFreeVars v = []) (hsw : staticSyntaxWF v = true)
    (he : stackNewWFList enc es = true) :
    stackNewWFList enc (rSubstList z v es) = true := by
  cases es with
  | nil => rfl
  | cons e rest =>
    simp only [stackNewWFList, Bool.and_eq_true] at he
    simp [rSubstList, stackNewWFList,
      stackNewWF_rSubst enc z hv hcl hsw he.1,
      stackNewWFList_rSubst enc z hv hcl hsw he.2]
termination_by sizeOf es

theorem stackNewWFArms_rSubst (enc : List RegionId) (z : Ident) {v : RExpr}
    {arms : List (Pat × RExpr)}
    (hv : IsRValue v) (hcl : rFreeVars v = []) (hsw : staticSyntaxWF v = true)
    (he : stackNewWFArms enc arms = true) :
    stackNewWFArms enc (rSubstArms z v arms) = true := by
  cases arms with
  | nil => rfl
  | cons arm rest =>
    cases arm with
    | mk p body =>
      simp only [stackNewWFArms, Bool.and_eq_true] at he
      simp only [rSubstArms, stackNewWFArms, Bool.and_eq_true]
      refine ⟨?_, stackNewWFArms_rSubst enc z hv hcl hsw he.2⟩
      split
      · exact he.1
      · exact stackNewWF_rSubst enc z hv hcl hsw he.1
termination_by sizeOf arms
end

theorem stackNewWF_rSubstMany (enc : List RegionId) {bs : List (Ident × RExpr)}
    (hv : ∀ b ∈ bs, IsRValue b.2)
    (hcl : ∀ b ∈ bs, rFreeVars b.2 = [])
    (hsw : ∀ b ∈ bs, staticSyntaxWF b.2 = true)
    {e : RExpr} (he : stackNewWF enc e = true) :
    stackNewWF enc (rSubstMany bs e) = true := by
  induction bs generalizing e with
  | nil => exact he
  | cons hd tl ih =>
    cases hd with
    | mk x v =>
      exact ih (fun b hb => hv b (List.Mem.tail _ hb))
        (fun b hb => hcl b (List.Mem.tail _ hb))
        (fun b hb => hsw b (List.Mem.tail _ hb))
        (stackNewWF_rSubst enc x (hv (x, v) (List.Mem.head _))
          (hcl (x, v) (List.Mem.head _)) (hsw (x, v) (List.Mem.head _)) he)

/-! ### `rMatchPat` Well-Formedness Lemma -/

mutual
theorem rMatchPat_wf {p : Pat} {v : RExpr} {env : List (Ident × RExpr)}
    (hv : IsRValue v) (hcl : rFreeVars v = []) (hsw : staticSyntaxWF v = true)
    (hpat : rMatchPat p v = some env) :
    env.map Prod.fst = patBoundNames p ∧
    (∀ b ∈ env, IsRValue b.2 ∧ rFreeVars b.2 = [] ∧ staticSyntaxWF b.2 = true ∧
      (∀ l ∈ rExprLocs b.2, l ∈ rExprLocs v)) := by
  cases p with
  | wild =>
    simp only [rMatchPat, Option.some.injEq] at hpat
    subst hpat
    exact ⟨by simp [patBoundNames], fun _ hm => nomatch hm⟩
  | var x =>
    simp only [rMatchPat, Option.some.injEq] at hpat
    subst hpat
    refine ⟨by simp [patBoundNames], fun b hb => ?_⟩
    rcases List.mem_singleton.mp hb with rfl
    exact ⟨hv, hcl, hsw, fun _ hl => hl⟩
  | lit l1 =>
    cases v with
    | lit l2 =>
      simp only [rMatchPat] at hpat
      split at hpat
      · injection hpat with hpat; subst hpat
        exact ⟨by simp [patBoundNames], fun _ hm => nomatch hm⟩
      · cases hpat
    | _ => simp [rMatchPat] at hpat
  | tuple ps =>
    cases hv with
    | tuple hvs =>
      simp only [rMatchPat] at hpat
      simp only [rFreeVars] at hcl
      simp only [staticSyntaxWF] at hsw
      have ⟨hnames, hbinds⟩ := rMatchPats_wf ps hvs hcl hsw hpat
      refine ⟨by simp [patBoundNames, hnames], hbinds⟩
    | _ => simp [rMatchPat] at hpat
  | ctor adt1 tag1 ps =>
    cases hv with
    | makeData adt2 tag2 hvs =>
      simp only [rMatchPat] at hpat
      split at hpat
      · simp only [rFreeVars] at hcl
        simp only [staticSyntaxWF] at hsw
        have ⟨hnames, hbinds⟩ := rMatchPats_wf ps hvs hcl hsw hpat
        exact ⟨by simp [patBoundNames, hnames], hbinds⟩
      · cases hpat
    | _ => simp [rMatchPat] at hpat
termination_by sizeOf p

theorem rMatchPats_wf (ps : List Pat) {vs : List RExpr} {env : List (Ident × RExpr)}
    (hvs : ∀ u ∈ vs, IsRValue u)
    (hcl : rFreeVarsList vs = [])
    (hsw : staticSyntaxWFList vs = true)
    (hpats : rMatchPats ps vs = some env) :
    env.map Prod.fst = ps.foldr (fun p acc => patBoundNames p ++ acc) [] ∧
    (∀ b ∈ env, IsRValue b.2 ∧ rFreeVars b.2 = [] ∧ staticSyntaxWF b.2 = true ∧
      (∀ l ∈ rExprLocs b.2, l ∈ rExprLocsList vs)) := by
  cases ps with
  | nil =>
    cases vs with
    | nil =>
      simp only [rMatchPats, Option.some.injEq] at hpats
      subst hpats
      exact ⟨rfl, fun _ hm => nomatch hm⟩
    | cons _ _ => simp [rMatchPats] at hpats
  | cons p prest =>
    cases vs with
    | nil => simp [rMatchPats] at hpats
    | cons u urest =>
      simp only [rFreeVarsList, List.append_eq_nil_iff] at hcl
      simp only [staticSyntaxWFList, Bool.and_eq_true] at hsw
      simp only [rMatchPats] at hpats
      cases hm1 : rMatchPat p u with
      | none => simp [hm1] at hpats
      | some b1 =>
        cases hm2 : rMatchPats prest urest with
        | none => simp [hm1, hm2] at hpats
        | some b2 =>
          simp only [hm1, hm2, Option.some.injEq] at hpats
          subst hpats
          have ⟨hn1, hb1⟩ := rMatchPat_wf (hvs u (List.Mem.head _)) hcl.1 hsw.1 hm1
          have ⟨hn2, hb2⟩ := rMatchPats_wf prest (fun w hw => hvs w (List.Mem.tail _ hw))
            hcl.2 hsw.2 hm2
          refine ⟨by simp [List.map_append, hn1, hn2], fun b hb => ?_⟩
          rcases List.mem_append.mp hb with h_in1 | h_in2
          · rcases hb1 b h_in1 with ⟨hv', hcl', hsw', hloc'⟩
            exact ⟨hv', hcl', hsw', fun l hl => List.mem_append.mpr (Or.inl (hloc' l hl))⟩
          · rcases hb2 b h_in2 with ⟨hv', hcl', hsw', hloc'⟩
            exact ⟨hv', hcl', hsw', fun l hl => List.mem_append.mpr (Or.inr (hloc' l hl))⟩
termination_by sizeOf ps
end

/-! ### `locConfined` Key Theorems -/

mutual
theorem not_mem_locs_of_locConfined_false {l : Loc} {rid : RegionId} (e : RExpr) :
    locConfined l rid false e = true → rid ∉ exprFrames e → l ∉ rExprLocs e := by
  intro hc hnf
  cases e with
  | lit _ | var _ | taskRef _ | syncRef _ _ | trap _ =>
    intro hm; cases hm
  | loc l' =>
    simp only [locConfined, bne_iff_ne] at hc
    simp only [rExprLocs, List.mem_singleton]
    exact Ne.symm hc
  | tuple es | block es | applyDir _ es | makeData _ _ es | concPrim _ es =>
    simp only [locConfined] at hc
    simp only [exprFrames] at hnf
    exact not_mem_locsList_of_locConfined_false es hc hnf
  | lam m ps ret body =>
    simp only [locConfined] at hc
    simp only [exprFrames] at hnf
    exact not_mem_locs_of_locConfined_false body hc hnf
  | apply fn args =>
    simp only [locConfined, Bool.and_eq_true] at hc
    simp only [exprFrames, List.mem_append, not_or] at hnf
    simp only [rExprLocs, List.mem_append, not_or]
    exact ⟨not_mem_locs_of_locConfined_false fn hc.1 hnf.1,
           not_mem_locsList_of_locConfined_false args hc.2 hnf.2⟩
  | bin _ e1 e2 | while_ e1 e2 =>
    simp only [locConfined, Bool.and_eq_true] at hc
    simp only [exprFrames, List.mem_append, not_or] at hnf
    simp only [rExprLocs, List.mem_append, not_or]
    exact ⟨not_mem_locs_of_locConfined_false e1 hc.1 hnf.1,
           not_mem_locs_of_locConfined_false e2 hc.2 hnf.2⟩
  | un _ e1 | getTag e1 | cellNew e1 | stackCellNew _ e1 | spawn e1 | await e1 =>
    simp only [locConfined] at hc
    simp only [exprFrames] at hnf
    exact not_mem_locs_of_locConfined_false e1 hc hnf
  | cellGet e1 =>
    simp only [locConfined] at hc
    cases hloc : (rAsLoc? e1 == some l) with
    | true => simp [hloc] at hc
    | false =>
      simp only [hloc, Bool.false_eq_true, ↓reduceIte] at hc
      exact not_mem_locs_of_locConfined_false e1 hc hnf
  | cellSet e1 e2 =>
    simp only [locConfined] at hc
    cases hloc : (rAsLoc? e1 == some l) with
    | true => simp [hloc] at hc
    | false =>
      simp only [hloc, Bool.false_eq_true, ↓reduceIte, Bool.and_eq_true] at hc
      simp only [exprFrames, List.mem_append, not_or] at hnf
      simp only [rExprLocs, List.mem_append, not_or]
      exact ⟨not_mem_locs_of_locConfined_false e1 hc.1 hnf.1,
             not_mem_locs_of_locConfined_false e2 hc.2 hnf.2⟩
  | let_ y e1 e2 =>
    simp only [locConfined] at hc
    cases hloc : (rAsLoc? e1 == some l) with
    | true => simp [hloc] at hc
    | false =>
      simp only [hloc, Bool.false_eq_true, ↓reduceIte, Bool.and_eq_true] at hc
      simp only [exprFrames, List.mem_append, not_or] at hnf
      simp only [rExprLocs, List.mem_append, not_or]
      exact ⟨not_mem_locs_of_locConfined_false e1 hc.1 hnf.1,
             not_mem_locs_of_locConfined_false e2 hc.2 hnf.2⟩
  | if_ c t e2 =>
    simp only [locConfined, Bool.and_eq_true] at hc
    simp only [exprFrames, List.mem_append, not_or] at hnf
    simp only [rExprLocs, List.mem_append, not_or]
    exact ⟨⟨not_mem_locs_of_locConfined_false c hc.1.1 hnf.1.1,
            not_mem_locs_of_locConfined_false t hc.1.2 hnf.1.2⟩,
           not_mem_locs_of_locConfined_false e2 hc.2 hnf.2⟩
  | match_ scrut arms =>
    simp only [locConfined, Bool.and_eq_true] at hc
    simp only [exprFrames, List.mem_append, not_or] at hnf
    simp only [rExprLocs, List.mem_append, not_or]
    exact ⟨not_mem_locs_of_locConfined_false scrut hc.1 hnf.1,
           not_mem_locsArms_of_locConfined_false arms hc.2 hnf.2⟩
  | frame r e1 =>
    simp only [exprFrames, List.mem_cons, not_or] at hnf
    have hne : (r == rid) = false := beq_eq_false_iff_ne.mpr (Ne.symm hnf.1)
    simp only [locConfined, Bool.false_or, hne] at hc
    exact not_mem_locs_of_locConfined_false e1 hc hnf.2

theorem not_mem_locsList_of_locConfined_false {l : Loc} {rid : RegionId} (es : List RExpr) :
    locConfinedList l rid false es = true → rid ∉ exprFramesList es → l ∉ rExprLocsList es := by
  intro hc hnf
  cases es with
  | nil => intro hm; cases hm
  | cons e rest =>
    simp only [locConfinedList, Bool.and_eq_true] at hc
    simp only [exprFramesList, List.mem_append, not_or] at hnf
    simp only [rExprLocsList, List.mem_append, not_or]
    exact ⟨not_mem_locs_of_locConfined_false e hc.1 hnf.1,
           not_mem_locsList_of_locConfined_false rest hc.2 hnf.2⟩

theorem not_mem_locsArms_of_locConfined_false {l : Loc} {rid : RegionId}
    (arms : List (Pat × RExpr)) :
    locConfinedArms l rid false arms = true → rid ∉ exprFramesArms arms →
      l ∉ rExprLocsArms arms := by
  intro hc hnf
  cases arms with
  | nil => intro hm; cases hm
  | cons arm rest =>
    cases arm with
    | mk p body =>
      simp only [locConfinedArms, Bool.and_eq_true] at hc
      simp only [exprFramesArms, List.mem_append, not_or] at hnf
      simp only [rExprLocsArms, List.mem_append, not_or]
      exact ⟨not_mem_locs_of_locConfined_false body hc.1 hnf.1,
             not_mem_locsArms_of_locConfined_false rest hc.2 hnf.2⟩
end

theorem not_mem_locs_of_isRValue_locConfined {l : Loc} {rid : RegionId} {inReg : Bool}
    {v : RExpr} (hv : IsRValue v) (hsw : staticSyntaxWF v = true)
    (hc : locConfined l rid inReg v = true) : l ∉ rExprLocs v := by
  induction hv with
  | lit _ | taskRef _ | syncRef _ _ => intro hm; cases hm
  | loc l' =>
    simp only [locConfined, bne_iff_ne] at hc
    simp only [rExprLocs, List.mem_singleton]
    exact Ne.symm hc
  | lam m ps ret body =>
    simp only [staticSyntaxWF] at hsw
    simp only [locConfined] at hc
    have hnf : rid ∉ exprFrames body := by
      rw [exprFrames_of_noRegionSyntax hsw]
      intro hm; cases hm
    exact not_mem_locs_of_locConfined_false body hc hnf
  | tuple _ ih =>
    simp only [staticSyntaxWF] at hsw
    simp only [locConfined] at hc
    simp only [rExprLocs]
    have haux : ∀ (es : List RExpr),
        (∀ e ∈ es, staticSyntaxWF e = true → locConfined l rid inReg e = true → l ∉ rExprLocs e) →
        staticSyntaxWFList es = true → locConfinedList l rid inReg es = true →
        l ∉ rExprLocsList es := by
      intro es
      induction es with
      | nil => intro _ _ _ hm; cases hm
      | cons a rest ihl =>
        intro hall hswl hcl
        simp only [staticSyntaxWFList, Bool.and_eq_true] at hswl
        simp only [locConfinedList, Bool.and_eq_true] at hcl
        simp only [rExprLocsList, List.mem_append, not_or]
        exact ⟨hall a (List.Mem.head _) hswl.1 hcl.1,
               ihl (fun u hu => hall u (List.Mem.tail _ hu)) hswl.2 hcl.2⟩
    exact haux _ ih hsw hc
  | makeData _ _ _ ih =>
    simp only [staticSyntaxWF] at hsw
    simp only [locConfined] at hc
    simp only [rExprLocs]
    have haux : ∀ (es : List RExpr),
        (∀ e ∈ es, staticSyntaxWF e = true → locConfined l rid inReg e = true → l ∉ rExprLocs e) →
        staticSyntaxWFList es = true → locConfinedList l rid inReg es = true →
        l ∉ rExprLocsList es := by
      intro es
      induction es with
      | nil => intro _ _ _ hm; cases hm
      | cons a rest ihl =>
        intro hall hswl hcl
        simp only [staticSyntaxWFList, Bool.and_eq_true] at hswl
        simp only [locConfinedList, Bool.and_eq_true] at hcl
        simp only [rExprLocsList, List.mem_append, not_or]
        exact ⟨hall a (List.Mem.head _) hswl.1 hcl.1,
               ihl (fun u hu => hall u (List.Mem.tail _ hu)) hswl.2 hcl.2⟩
    exact haux _ ih hsw hc

mutual
theorem locConfined_of_not_mem_locs (l : Loc) (rid : RegionId) (inReg : Bool) (e : RExpr) :
    l ∉ rExprLocs e → locConfined l rid inReg e = true := by
  intro hnl
  cases e with
  | lit _ | var _ | taskRef _ | syncRef _ _ | trap _ => rfl
  | loc l' =>
    simp only [rExprLocs, List.mem_singleton] at hnl
    exact bne_iff_ne.mpr (Ne.symm hnl)
  | tuple es | block es | applyDir _ es | makeData _ _ es | concPrim _ es =>
    simp only [rExprLocs] at hnl
    exact locConfinedList_of_not_mem_locs l rid inReg es hnl
  | lam _ _ _ body =>
    simp only [rExprLocs] at hnl
    exact locConfined_of_not_mem_locs l rid false body hnl
  | apply fn args =>
    simp only [rExprLocs, List.mem_append, not_or] at hnl
    simp [locConfined, locConfined_of_not_mem_locs l rid inReg fn hnl.1,
      locConfinedList_of_not_mem_locs l rid inReg args hnl.2]
  | bin _ e1 e2 | while_ e1 e2 =>
    simp only [rExprLocs, List.mem_append, not_or] at hnl
    simp [locConfined, locConfined_of_not_mem_locs l rid inReg e1 hnl.1,
      locConfined_of_not_mem_locs l rid inReg e2 hnl.2]
  | un _ e1 | getTag e1 | cellNew e1 | stackCellNew _ e1 | spawn e1 | await e1 =>
    simp only [rExprLocs] at hnl
    exact locConfined_of_not_mem_locs l rid inReg e1 hnl
  | cellGet e1 =>
    simp only [rExprLocs] at hnl
    have hc1 := locConfined_of_not_mem_locs l rid inReg e1 hnl
    simp [locConfined, rAsLoc?_ne_of_locConfined hc1, hc1]
  | cellSet e1 e2 =>
    simp only [rExprLocs, List.mem_append, not_or] at hnl
    have hc1 := locConfined_of_not_mem_locs l rid inReg e1 hnl.1
    have hc2 := locConfined_of_not_mem_locs l rid inReg e2 hnl.2
    simp [locConfined, rAsLoc?_ne_of_locConfined hc1, hc1, hc2]
  | let_ y e1 e2 =>
    simp only [rExprLocs, List.mem_append, not_or] at hnl
    have hc1 := locConfined_of_not_mem_locs l rid inReg e1 hnl.1
    have hc2 := locConfined_of_not_mem_locs l rid inReg e2 hnl.2
    simp [locConfined, rAsLoc?_ne_of_locConfined hc1, hc1, hc2]
  | if_ c t e2 =>
    simp only [rExprLocs, List.mem_append, not_or] at hnl
    simp [locConfined, locConfined_of_not_mem_locs l rid inReg c hnl.1.1,
      locConfined_of_not_mem_locs l rid inReg t hnl.1.2,
      locConfined_of_not_mem_locs l rid inReg e2 hnl.2]
  | match_ scrut arms =>
    simp only [rExprLocs, List.mem_append, not_or] at hnl
    simp [locConfined, locConfined_of_not_mem_locs l rid inReg scrut hnl.1,
      locConfinedArms_of_not_mem_locs l rid inReg arms hnl.2]
  | frame r e1 =>
    simp only [rExprLocs] at hnl
    exact locConfined_of_not_mem_locs l rid (inReg || (r == rid)) e1 hnl

theorem locConfinedList_of_not_mem_locs (l : Loc) (rid : RegionId) (inReg : Bool)
    (es : List RExpr) : l ∉ rExprLocsList es → locConfinedList l rid inReg es = true := by
  intro hnl
  cases es with
  | nil => rfl
  | cons e rest =>
    simp only [rExprLocsList, List.mem_append, not_or] at hnl
    simp [locConfinedList, locConfined_of_not_mem_locs l rid inReg e hnl.1,
      locConfinedList_of_not_mem_locs l rid inReg rest hnl.2]

theorem locConfinedArms_of_not_mem_locs (l : Loc) (rid : RegionId) (inReg : Bool)
    (arms : List (Pat × RExpr)) :
    l ∉ rExprLocsArms arms → locConfinedArms l rid inReg arms = true := by
  intro hnl
  cases arms with
  | nil => rfl
  | cons arm rest =>
    cases arm with
    | mk p body =>
      simp only [rExprLocsArms, List.mem_append, not_or] at hnl
      simp [locConfinedArms, locConfined_of_not_mem_locs l rid inReg body hnl.1,
        locConfinedArms_of_not_mem_locs l rid inReg rest hnl.2]
end

mutual
theorem locConfined_rSubst_other (l : Loc) (rid : RegionId) (inReg : Bool) (z : Ident)
    {v : RExpr} (hv : IsRValue v) (hcl : rFreeVars v = []) (hnl : l ∉ rExprLocs v)
    (e : RExpr) : locConfined l rid inReg e = true →
      locConfined l rid inReg (rSubst z v e) = true := by
  intro hc
  cases e with
  | lit _ | loc _ | taskRef _ | syncRef _ _ | trap _ => exact hc
  | var y =>
    simp only [rSubst]
    split
    · exact locConfined_of_not_mem_locs l rid inReg v hnl
    · rfl
  | tuple es | block es | applyDir _ es | makeData _ _ es | concPrim _ es =>
    simp only [locConfined] at hc
    exact locConfinedList_rSubst_other l rid inReg z hv hcl hnl es hc
  | lam m ps ret body =>
    simp only [locConfined] at hc
    simp only [rSubst]
    split
    · exact hc
    · exact locConfined_rSubst_other l rid false z hv hcl hnl body hc
  | apply fn args =>
    simp only [locConfined, Bool.and_eq_true] at hc
    simp [rSubst, locConfined,
      locConfined_rSubst_other l rid inReg z hv hcl hnl fn hc.1,
      locConfinedList_rSubst_other l rid inReg z hv hcl hnl args hc.2]
  | bin _ e1 e2 | while_ e1 e2 =>
    simp only [locConfined, Bool.and_eq_true] at hc
    simp [rSubst, locConfined,
      locConfined_rSubst_other l rid inReg z hv hcl hnl e1 hc.1,
      locConfined_rSubst_other l rid inReg z hv hcl hnl e2 hc.2]
  | un _ e1 | getTag e1 | cellNew e1 | stackCellNew _ e1 | spawn e1 | await e1 =>
    simp only [locConfined] at hc
    exact locConfined_rSubst_other l rid inReg z hv hcl hnl e1 hc
  | frame r e1 =>
    simp only [locConfined] at hc
    exact locConfined_rSubst_other l rid (inReg || (r == rid)) z hv hcl hnl e1 hc
  | cellGet e1 =>
    simp only [locConfined] at hc
    cases hloc : (rAsLoc? e1 == some l) with
    | true =>
      have he1 := rAsLoc?_eq_some.mp (beq_iff_eq.mp hloc)
      subst he1
      simp only [rAsLoc?, beq_self_eq_true, ↓reduceIte] at hc
      simp [rSubst, locConfined, rAsLoc?, hc]
    | false =>
      simp only [hloc, Bool.false_eq_true, ↓reduceIte] at hc
      have hc1' := locConfined_rSubst_other l rid inReg z hv hcl hnl e1 hc
      simp [rSubst, locConfined, rAsLoc?_ne_of_locConfined hc1', hc1']
  | cellSet e1 e2 =>
    simp only [locConfined] at hc
    cases hloc : (rAsLoc? e1 == some l) with
    | true =>
      have he1 := rAsLoc?_eq_some.mp (beq_iff_eq.mp hloc)
      subst he1
      simp only [rAsLoc?, beq_self_eq_true, ↓reduceIte, Bool.and_eq_true] at hc
      rcases hc with ⟨rfl, hc2⟩
      simp [rSubst, locConfined, rAsLoc?,
        locConfined_rSubst_other l rid true z hv hcl hnl e2 hc2]
    | false =>
      simp only [hloc, Bool.false_eq_true, ↓reduceIte, Bool.and_eq_true] at hc
      have hc1' := locConfined_rSubst_other l rid inReg z hv hcl hnl e1 hc.1
      have hc2' := locConfined_rSubst_other l rid inReg z hv hcl hnl e2 hc.2
      simp [rSubst, locConfined, rAsLoc?_ne_of_locConfined hc1', hc1', hc2']
  | let_ y e1 e2 =>
    simp only [locConfined] at hc
    cases hloc : (rAsLoc? e1 == some l) with
    | true =>
      have he1 := rAsLoc?_eq_some.mp (beq_iff_eq.mp hloc)
      subst he1
      simp only [rAsLoc?, beq_self_eq_true, ↓reduceIte, Bool.and_eq_true] at hc
      rcases hc with ⟨⟨rfl, hc2⟩, hd2⟩
      simp only [rSubst]
      cases hyz : (y == z) with
      | true =>
        simp [locConfined, rAsLoc?, hc2, hd2]
      | false =>
        have hne : z ≠ y := Ne.symm (beq_eq_false_iff_ne.mp hyz)
        simp [locConfined, rAsLoc?,
          locConfined_rSubst_other l rid true z hv hcl hnl e2 hc2,
          rOnlyDirectCellOps_rSubst_other hne hv hcl hd2]
    | false =>
      simp only [hloc, Bool.false_eq_true, ↓reduceIte, Bool.and_eq_true] at hc
      have hc1' := locConfined_rSubst_other l rid inReg z hv hcl hnl e1 hc.1
      simp only [rSubst]
      cases hyz : (y == z) with
      | true =>
        simp [locConfined, rAsLoc?_ne_of_locConfined hc1', hc1', hc.2]
      | false =>
        have hc2' := locConfined_rSubst_other l rid inReg z hv hcl hnl e2 hc.2
        simp [locConfined, rAsLoc?_ne_of_locConfined hc1', hc1', hc2']
  | if_ c t e2 =>
    simp only [locConfined, Bool.and_eq_true] at hc
    simp [rSubst, locConfined,
      locConfined_rSubst_other l rid inReg z hv hcl hnl c hc.1.1,
      locConfined_rSubst_other l rid inReg z hv hcl hnl t hc.1.2,
      locConfined_rSubst_other l rid inReg z hv hcl hnl e2 hc.2]
  | match_ scrut arms =>
    simp only [locConfined, Bool.and_eq_true] at hc
    simp [rSubst, locConfined,
      locConfined_rSubst_other l rid inReg z hv hcl hnl scrut hc.1,
      locConfinedArms_rSubst_other l rid inReg z hv hcl hnl arms hc.2]

theorem locConfinedList_rSubst_other (l : Loc) (rid : RegionId) (inReg : Bool) (z : Ident)
    {v : RExpr} (hv : IsRValue v) (hcl : rFreeVars v = []) (hnl : l ∉ rExprLocs v)
    (es : List RExpr) : locConfinedList l rid inReg es = true →
      locConfinedList l rid inReg (rSubstList z v es) = true := by
  intro hc
  cases es with
  | nil => rfl
  | cons e rest =>
    simp only [locConfinedList, Bool.and_eq_true] at hc
    simp [rSubstList, locConfinedList,
      locConfined_rSubst_other l rid inReg z hv hcl hnl e hc.1,
      locConfinedList_rSubst_other l rid inReg z hv hcl hnl rest hc.2]

theorem locConfinedArms_rSubst_other (l : Loc) (rid : RegionId) (inReg : Bool) (z : Ident)
    {v : RExpr} (hv : IsRValue v) (hcl : rFreeVars v = []) (hnl : l ∉ rExprLocs v)
    (arms : List (Pat × RExpr)) : locConfinedArms l rid inReg arms = true →
      locConfinedArms l rid inReg (rSubstArms z v arms) = true := by
  intro hc
  cases arms with
  | nil => rfl
  | cons arm rest =>
    cases arm with
    | mk p body =>
      simp only [locConfinedArms, Bool.and_eq_true] at hc
      simp only [rSubstArms, locConfinedArms, Bool.and_eq_true]
      refine ⟨?_, locConfinedArms_rSubst_other l rid inReg z hv hcl hnl rest hc.2⟩
      split
      · exact hc.1
      · exact locConfined_rSubst_other l rid inReg z hv hcl hnl body hc.1
end

theorem locConfined_rSubstMany_other (l : Loc) (rid : RegionId) (inReg : Bool)
    {bs : List (Ident × RExpr)}
    (hv : ∀ b ∈ bs, IsRValue b.2)
    (hcl : ∀ b ∈ bs, rFreeVars b.2 = [])
    (hnl : ∀ b ∈ bs, l ∉ rExprLocs b.2)
    {e : RExpr} (hc : locConfined l rid inReg e = true) :
    locConfined l rid inReg (rSubstMany bs e) = true := by
  induction bs generalizing e with
  | nil => exact hc
  | cons hd tl ih =>
    cases hd with
    | mk z v =>
      exact ih (fun b hb => hv b (List.Mem.tail _ hb))
        (fun b hb => hcl b (List.Mem.tail _ hb))
        (fun b hb => hnl b (List.Mem.tail _ hb))
        (locConfined_rSubst_other l rid inReg z
          (hv (z, v) (List.Mem.head _))
          (hcl (z, v) (List.Mem.head _))
          (hnl (z, v) (List.Mem.head _)) e hc)

mutual
theorem locConfined_rSubst_self (l : Loc) (rid : RegionId) (x : Ident) (e : RExpr) :
    locConfined l rid true e = true → rOnlyDirectCellOps x e = true →
      locConfined l rid true (rSubst x (.loc l) e) = true := by
  intro hc hd
  cases e with
  | lit _ | loc _ | taskRef _ | syncRef _ _ | trap _ => exact hc
  | var y =>
    simp only [rOnlyDirectCellOps, bne_iff_ne] at hd
    have hyx : (y == x) = false := beq_eq_false_iff_ne.mpr hd
    simp [rSubst, hyx, locConfined]
  | tuple es | block es | applyDir _ es | makeData _ _ es | concPrim _ es =>
    simp only [locConfined] at hc
    simp only [rOnlyDirectCellOps] at hd
    exact locConfinedList_rSubst_self l rid x es hc hd
  | lam m ps ret body =>
    simp only [rOnlyDirectCellOps] at hd
    have hnf : x ∉ rFreeVars (.lam m ps ret body) := by
      intro hm
      rw [List.contains_iff_mem.mpr hm] at hd
      cases hd
    rw [rSubst_not_free (.loc l) hnf]
    exact hc
  | apply fn args =>
    simp only [locConfined, Bool.and_eq_true] at hc
    simp only [rOnlyDirectCellOps, Bool.and_eq_true] at hd
    simp [rSubst, locConfined,
      locConfined_rSubst_self l rid x fn hc.1 hd.1,
      locConfinedList_rSubst_self l rid x args hc.2 hd.2]
  | bin _ e1 e2 | while_ e1 e2 =>
    simp only [locConfined, Bool.and_eq_true] at hc
    simp only [rOnlyDirectCellOps, Bool.and_eq_true] at hd
    simp [rSubst, locConfined,
      locConfined_rSubst_self l rid x e1 hc.1 hd.1,
      locConfined_rSubst_self l rid x e2 hc.2 hd.2]
  | un _ e1 | getTag e1 | cellNew e1 | stackCellNew _ e1 | spawn e1 | await e1 =>
    simp only [locConfined] at hc
    simp only [rOnlyDirectCellOps] at hd
    exact locConfined_rSubst_self l rid x e1 hc hd
  | frame r e1 =>
    simp only [locConfined, Bool.true_or] at hc ⊢
    simp only [rOnlyDirectCellOps] at hd
    exact locConfined_rSubst_self l rid x e1 hc hd
  | cellGet e1 =>
    simp only [rOnlyDirectCellOps] at hd
    cases hvar : (rAsVar? e1 == some x) with
    | true =>
      have he1 := rAsVar?_eq_some.mp (beq_iff_eq.mp hvar)
      subst he1
      simp [rSubst, locConfined, rAsLoc?]
    | false =>
      simp only [hvar, Bool.false_eq_true, ↓reduceIte] at hd
      simp only [locConfined] at hc
      cases hloc : (rAsLoc? e1 == some l) with
      | true =>
        have he1 := rAsLoc?_eq_some.mp (beq_iff_eq.mp hloc)
        subst he1
        simp [rSubst, locConfined, rAsLoc?]
      | false =>
        simp only [hloc, Bool.false_eq_true, ↓reduceIte] at hc
        have hc1' := locConfined_rSubst_self l rid x e1 hc hd
        simp [rSubst, locConfined, rAsLoc?_ne_of_locConfined hc1', hc1']
  | cellSet e1 e2 =>
    simp only [rOnlyDirectCellOps] at hd
    cases hvar : (rAsVar? e1 == some x) with
    | true =>
      have he1 := rAsVar?_eq_some.mp (beq_iff_eq.mp hvar)
      subst he1
      simp only [rAsVar?, beq_self_eq_true, ↓reduceIte] at hd
      simp [locConfined, rAsLoc?] at hc
      have hc2' := locConfined_rSubst_self l rid x e2 hc hd
      simp [rSubst, locConfined, rAsLoc?, hc2']
    | false =>
      simp only [hvar, Bool.false_eq_true, ↓reduceIte, Bool.and_eq_true] at hd
      simp only [locConfined] at hc
      cases hloc : (rAsLoc? e1 == some l) with
      | true =>
        have he1 := rAsLoc?_eq_some.mp (beq_iff_eq.mp hloc)
        subst he1
        simp only [rAsLoc?, beq_self_eq_true, ↓reduceIte, Bool.and_eq_true] at hc
        have hc2' := locConfined_rSubst_self l rid x e2 hc.2 hd.2
        simp [rSubst, locConfined, rAsLoc?, hc2']
      | false =>
        simp only [hloc, Bool.false_eq_true, ↓reduceIte, Bool.and_eq_true] at hc
        have hc1' := locConfined_rSubst_self l rid x e1 hc.1 hd.1
        have hc2' := locConfined_rSubst_self l rid x e2 hc.2 hd.2
        simp [rSubst, locConfined, rAsLoc?_ne_of_locConfined hc1', hc1', hc2']
  | let_ y e1 e2 =>
    simp only [rOnlyDirectCellOps, Bool.and_eq_true] at hd
    have hyx : (y == x) = false := beq_eq_false_iff_ne.mpr (bne_iff_ne.mp hd.1.1)
    have hxy : x ≠ y := Ne.symm (bne_iff_ne.mp hd.1.1)
    simp only [locConfined] at hc
    cases hloc : (rAsLoc? e1 == some l) with
    | true =>
      have he1 := rAsLoc?_eq_some.mp (beq_iff_eq.mp hloc)
      subst he1
      simp only [rAsLoc?, beq_self_eq_true, ↓reduceIte, Bool.and_eq_true] at hc
      have hc2' := locConfined_rSubst_self l rid x e2 hc.1.2 hd.2
      have hdy' := rOnlyDirectCellOps_rSubst_other hxy (.loc l) rfl hc.2
      simp [rSubst, hyx, locConfined, rAsLoc?, hc2', hdy']
    | false =>
      simp only [hloc, Bool.false_eq_true, ↓reduceIte, Bool.and_eq_true] at hc
      have hc1' := locConfined_rSubst_self l rid x e1 hc.1 hd.1.2
      have hc2' := locConfined_rSubst_self l rid x e2 hc.2 hd.2
      simp [rSubst, hyx, locConfined, rAsLoc?_ne_of_locConfined hc1', hc1', hc2']
  | if_ c t e2 =>
    simp only [locConfined, Bool.and_eq_true] at hc
    simp only [rOnlyDirectCellOps, Bool.and_eq_true] at hd
    simp [rSubst, locConfined,
      locConfined_rSubst_self l rid x c hc.1.1 hd.1.1,
      locConfined_rSubst_self l rid x t hc.1.2 hd.1.2,
      locConfined_rSubst_self l rid x e2 hc.2 hd.2]
  | match_ scrut arms =>
    simp only [locConfined, Bool.and_eq_true] at hc
    simp only [rOnlyDirectCellOps, Bool.and_eq_true] at hd
    simp [rSubst, locConfined,
      locConfined_rSubst_self l rid x scrut hc.1 hd.1,
      locConfinedArms_rSubst_self l rid x arms hc.2 hd.2]

theorem locConfinedList_rSubst_self (l : Loc) (rid : RegionId) (x : Ident) (es : List RExpr) :
    locConfinedList l rid true es = true → rOnlyDirectCellOpsList x es = true →
      locConfinedList l rid true (rSubstList x (.loc l) es) = true := by
  intro hc hd
  cases es with
  | nil => rfl
  | cons e rest =>
    simp only [locConfinedList, Bool.and_eq_true] at hc
    simp only [rOnlyDirectCellOpsList, Bool.and_eq_true] at hd
    simp [rSubstList, locConfinedList,
      locConfined_rSubst_self l rid x e hc.1 hd.1,
      locConfinedList_rSubst_self l rid x rest hc.2 hd.2]

theorem locConfinedArms_rSubst_self (l : Loc) (rid : RegionId) (x : Ident)
    (arms : List (Pat × RExpr)) :
    locConfinedArms l rid true arms = true → rOnlyDirectCellOpsArms x arms = true →
      locConfinedArms l rid true (rSubstArms x (.loc l) arms) = true := by
  intro hc hd
  cases arms with
  | nil => rfl
  | cons arm rest =>
    cases arm with
    | mk p body =>
      simp only [locConfinedArms, Bool.and_eq_true] at hc
      simp only [rOnlyDirectCellOpsArms, Bool.and_eq_true] at hd
      have hnp : (patBoundNames p).contains x = false := by
        cases hpb : (patBoundNames p).contains x with
        | false => rfl
        | true =>
          have h1 := hd.1.1
          rw [hpb] at h1
          cases h1
      simp only [rSubstArms, hnp, Bool.false_eq_true, ↓reduceIte, locConfinedArms,
        Bool.and_eq_true]
      exact ⟨locConfined_rSubst_self l rid x body hc.1 hd.1.2,
             locConfinedArms_rSubst_self l rid x rest hc.2 hd.2⟩
end

/-! ### Program Escape Soundness, Distinct Frame Lists, and Dangling-Access Locations -/

/-- Semantic escape-safety contract extracted from `checkProgramEscape`. -/
def EnvEscapeWF (Φ : FunEnv) (specs : List FnStackSpec) : Prop :=
  ∀ (name : Ident) (fd : FunDef), Φ name = some fd →
    exprHasNoLocs fd.body = true ∧
    exprClosedUnderParams fd.params fd.body = true ∧
    (∀ x ∈ lookupStackVars specs name, checkStackVarInExpr x fd.body = true)

theorem checkFunEscape_sound {fd : FunDef} {svars : List Ident}
    (h : checkFunEscape fd svars = .ok ()) :
    exprHasNoLocs fd.body = true ∧
    exprClosedUnderParams fd.params fd.body = true ∧
    (∀ x ∈ svars, checkStackVarInExpr x fd.body = true) := by
  unfold checkFunEscape at h
  cases h1 : exprHasNoLocs fd.body with
  | false => simp [h1] at h
  | true =>
    simp only [h1, Bool.not_true, Bool.false_eq_true, ↓reduceIte] at h
    cases h2 : exprClosedUnderParams fd.params fd.body with
    | false => simp [h2] at h
    | true =>
      simp only [h2, Bool.not_true, Bool.false_eq_true, ↓reduceIte] at h
      cases h3 : noDupIdents svars with
      | false => simp [h3] at h
      | true =>
        simp only [h3, Bool.not_true, Bool.false_eq_true, ↓reduceIte] at h
        cases h4 : svars.any (fun x => fd.params.any (·.1 == x)) with
        | true => simp [h4] at h
        | false =>
          simp only [h4, Bool.false_eq_true, ↓reduceIte] at h
          cases h5 : svars.all (fun x => checkStackCellVar x fd.body) with
          | false => simp [h5] at h
          | true =>
            refine ⟨rfl, rfl, fun x hx => ?_⟩
            have hall := List.all_eq_true.mp h5 x hx
            simp only [checkStackCellVar, Bool.and_eq_true] at hall
            exact hall.2

theorem checkProgramEscapeSpecs_mem {funs : List FunDef} {specs : List FnStackSpec}
    {spec : FnStackSpec}
    (h : checkProgramEscapeSpecs funs specs = .ok ())
    (hmem : spec ∈ specs) :
    ∃ fd, funs.find? (·.name == spec.fnName) = some fd ∧
      checkFunEscape fd spec.vars = .ok () := by
  induction specs with
  | nil => cases hmem
  | cons hd tl ih =>
    simp only [checkProgramEscapeSpecs] at h
    cases hfd : funs.find? (·.name == hd.fnName) with
    | none => simp [hfd] at h
    | some fd =>
      simp only [hfd] at h
      cases hchk : checkFunEscape fd hd.vars with
      | error _ => simp [hchk] at h
      | ok u =>
        simp only [hchk] at h
        rcases List.mem_cons.mp hmem with rfl | htl
        · exact ⟨fd, hfd, hchk⟩
        · exact ih h htl

theorem find?_pred_of_eq_some {α : Type} {xs : List α} {p : α → Bool} {a : α}
    (h : xs.find? p = some a) : p a = true := by
  induction xs with
  | nil => simp at h
  | cons hd tl ih =>
    simp only [List.find?] at h
    cases hp : p hd with
    | true =>
      simp only [hp, Option.some.injEq] at h
      subst h
      exact hp
    | false =>
      simp only [hp] at h
      exact ih h

theorem checkProgramEscape_sound {funs : List FunDef} {specs : List FnStackSpec}
    {Φ : FunEnv}
    (hΦ_eq : ∀ name, Φ name = funs.find? (·.name == name))
    (hesc : checkProgramEscape funs specs = .ok ()) :
    EnvEscapeWF Φ specs := by
  unfold checkProgramEscape at hesc
  cases hall : funs.all (fun fd => exprHasNoLocs fd.body && exprClosedUnderParams fd.params fd.body) with
  | false => simp [hall] at hesc
  | true =>
    simp only [hall, Bool.not_true, Bool.false_eq_true, ↓reduceIte] at hesc
    cases hdup : noDupIdents (specs.map FnStackSpec.fnName) with
    | false => simp [hdup] at hesc
    | true =>
      simp only [hdup, Bool.not_true, Bool.false_eq_true, ↓reduceIte] at hesc
      intro name fd hΦ
      have hfind : funs.find? (·.name == name) = some fd := by rw [← hΦ_eq]; exact hΦ
      have hmem_fd : fd ∈ funs := List.mem_of_find?_eq_some hfind
      have hfd_ok := List.all_eq_true.mp hall fd hmem_fd
      simp only [Bool.and_eq_true] at hfd_ok
      refine ⟨hfd_ok.1, hfd_ok.2, ?_⟩
      unfold lookupStackVars
      cases hsp : specs.find? (·.fnName == name) with
      | none => intro _ hm; cases hm
      | some spec =>
        have hmem_sp : spec ∈ specs := List.mem_of_find?_eq_some hsp
        have hname_eq : spec.fnName = name :=
          beq_iff_eq.mp (find?_pred_of_eq_some (p := fun s : FnStackSpec => s.fnName == name) hsp)
        rcases checkProgramEscapeSpecs_mem hesc hmem_sp with ⟨fd', hfind', hchk'⟩
        rw [hname_eq, hfind] at hfind'
        injection hfind' with hfd_eq
        subst hfd_eq
        exact (checkFunEscape_sound hchk').2.2

structure DanglingLocBox (ρ : RStore) (re : RExpr) : Prop where
  run : DanglingAt ρ re → ∃ l rid, ρ[l]? = some (.stackFreed rid) ∧ l ∈ rExprLocs re

structure DanglingLocListBox (ρ : RStore) (es : List RExpr) : Prop where
  run : DanglingAtList ρ es → ∃ l rid, ρ[l]? = some (.stackFreed rid) ∧ l ∈ rExprLocsList es

mutual
theorem danglingAt_has_freed_loc_box (ρ : RStore) (re : RExpr) :
    DanglingLocBox ρ re := by
  refine ⟨fun hd => ?_⟩
  cases hd with
  | read hslot =>
    exact ⟨_, _, hslot, List.Mem.head _⟩
  | write hslot _ =>
    exact ⟨_, _, hslot, List.mem_append.mpr (Or.inl (List.Mem.head _))⟩
  | @tuple es hdl | @makeData _ _ es hdl | @applyDirArgs _ es hdl | @concPrimArgs _ es hdl =>
    exact (danglingAtList_has_freed_loc_box ρ es).run hdl
  | @blockCons e1 _ _ hd1 | @applyFn e1 _ hd1 | @binLeft _ e1 _ hd1
  | @let_ _ e1 _ hd1 | @match_ e1 _ hd1 | @cellSetLeft e1 _ hd1 =>
    rcases (danglingAt_has_freed_loc_box ρ e1).run hd1 with ⟨l, rid, hslot, hmem⟩
    exact ⟨l, rid, hslot, List.mem_append.mpr (Or.inl hmem)⟩
  | @applyArgs _ args _ hdl =>
    rcases (danglingAtList_has_freed_loc_box ρ args).run hdl with ⟨l, rid, hslot, hmem⟩
    exact ⟨l, rid, hslot, List.mem_append.mpr (Or.inr hmem)⟩
  | @binRight _ _ e2 _ _ _ hd2 | @cellSetRight _ e2 _ hd2 =>
    rcases (danglingAt_has_freed_loc_box ρ e2).run hd2 with ⟨l, rid, hslot, hmem⟩
    exact ⟨l, rid, hslot, List.mem_append.mpr (Or.inr hmem)⟩
  | @if_ c _ _ hd1 =>
    rcases (danglingAt_has_freed_loc_box ρ c).run hd1 with ⟨l, rid, hslot, hmem⟩
    exact ⟨l, rid, hslot, List.mem_append.mpr (Or.inl (List.mem_append.mpr (Or.inl hmem)))⟩
  | @un _ e1 hd1 | @getTag e1 hd1 | @cellNew e1 hd1 | @stackCellNew _ e1 hd1
  | @cellGetStep e1 hd1 | @spawn e1 hd1 | @await e1 hd1 | @frame _ e1 hd1 =>
    exact (danglingAt_has_freed_loc_box ρ e1).run hd1
termination_by sizeOf re

theorem danglingAtList_has_freed_loc_box (ρ : RStore) (es : List RExpr) :
    DanglingLocListBox ρ es := by
  refine ⟨fun hdl => ?_⟩
  cases hdl with
  | @head e1 _ hd1 =>
    rcases (danglingAt_has_freed_loc_box ρ e1).run hd1 with ⟨l, rid, hslot, hmem⟩
    exact ⟨l, rid, hslot, List.mem_append.mpr (Or.inl hmem)⟩
  | @tail _ rest _ hdl' =>
    rcases (danglingAtList_has_freed_loc_box ρ rest).run hdl' with ⟨l, rid, hslot, hmem⟩
    exact ⟨l, rid, hslot, List.mem_append.mpr (Or.inr hmem)⟩
termination_by sizeOf es
end

theorem danglingAt_has_freed_loc {ρ : RStore} {re : RExpr}
    (hd : DanglingAt ρ re) : ∃ l rid, ρ[l]? = some (.stackFreed rid) ∧ l ∈ rExprLocs re :=
  (danglingAt_has_freed_loc_box ρ re).run hd

/-- Disjointness of two lists. -/
def ListDisjoint {α : Type} (xs ys : List α) : Prop :=
  ∀ x ∈ xs, x ∉ ys

/-- Pairwise distinct elements in a list. -/
inductive DistinctList {α : Type} : List α → Prop where
  | nil : DistinctList []
  | cons {x : α} {xs : List α} : x ∉ xs → DistinctList xs → DistinctList (x :: xs)

theorem distinctList_append {α : Type} {xs ys : List α} :
    DistinctList (xs ++ ys) ↔ DistinctList xs ∧ DistinctList ys ∧ ListDisjoint xs ys := by
  induction xs with
  | nil =>
    simp only [List.nil_append]
    exact ⟨fun h => ⟨.nil, h, fun _ hm => nomatch hm⟩, fun h => h.2.1⟩
  | cons a rest ih =>
    simp only [List.cons_append]
    constructor
    · intro h
      cases h with
      | cons hnot hd =>
        simp only [List.mem_append, not_or] at hnot
        rcases ih.mp hd with ⟨hd1, hd2, hdisj⟩
        refine ⟨.cons hnot.1 hd1, hd2, fun x hx => ?_⟩
        rcases List.mem_cons.mp hx with rfl | hr
        · exact hnot.2
        · exact hdisj x hr
    · rintro ⟨hd1, hd2, hdisj⟩
      cases hd1 with
      | cons hna hd_rest =>
        apply DistinctList.cons
        · simp only [List.mem_append, not_or]
          exact ⟨hna, hdisj a (List.Mem.head _)⟩
        · exact ih.mpr ⟨hd_rest, hd2, fun x hx => hdisj x (List.Mem.tail _ hx)⟩

/-- Locations embedded inside a `RegionSlot` (empty for `.stackFreed`). -/
def slotLocs : RegionSlot → List Loc
  | .heap rv => rExprLocs rv
  | .stackLive _ rv => rExprLocs rv
  | .stackFreed _ => []

/-- Well-formedness of values stored in `RStore` slots. -/
def SlotValueWF (bound : Nat) : RegionSlot → Prop
  | .heap rv =>
    IsRValue rv ∧ rFreeVars rv = [] ∧ staticSyntaxWF rv = true ∧
      (∀ l' ∈ rExprLocs rv, l' < bound)
  | .stackLive _ rv =>
    IsRValue rv ∧ rFreeVars rv = [] ∧ staticSyntaxWF rv = true ∧
      (∀ l' ∈ rExprLocs rv, l' < bound)
  | .stackFreed _ => True

theorem slotValueWF_mono {b1 b2 : Nat} (hle : b1 ≤ b2) {s : RegionSlot}
    (hs : SlotValueWF b1 s) : SlotValueWF b2 s := by
  cases s with
  | heap rv | stackLive _ rv =>
    rcases hs with ⟨hv, hcl, hsw, hloc⟩
    exact ⟨hv, hcl, hsw, fun l hl => Nat.lt_of_lt_of_le (hloc l hl) hle⟩
  | stackFreed _ => trivial

theorem slotValueWF_popRegionSlot (rid : RegionId) {b : Nat} {s : RegionSlot}
    (hs : SlotValueWF b s) : SlotValueWF b (popRegionSlot rid s) := by
  cases s with
  | heap _ => exact hs
  | stackLive r _ =>
    simp only [popRegionSlot]
    split
    · trivial
    · exact hs
  | stackFreed _ => trivial

theorem slotLocs_popRegionSlot_subset (rid : RegionId) (s : RegionSlot) :
    ∀ l ∈ slotLocs (popRegionSlot rid s), l ∈ slotLocs s := by
  cases s with
  | heap _ => intro l hl; exact hl
  | stackLive r _ =>
    simp only [popRegionSlot]
    split
    · intro _ hm; cases hm
    · intro l hl; exact hl
  | stackFreed _ => intro _ hm; cases hm

theorem mem_popRegion {rid : RegionId} {ρ : RStore} {s' : RegionSlot}
    (h : s' ∈ popRegion rid ρ) : ∃ s ∈ ρ, s' = popRegionSlot rid s := by
  unfold popRegion at h
  rcases List.mem_map.mp h with ⟨s, hs, rfl⟩
  exact ⟨s, hs, rfl⟩

theorem mem_zip_snd {α β : Type} {xs : List α} {ys : List β} {p : α × β}
    (hp : p ∈ xs.zip ys) : p.2 ∈ ys := by
  induction xs generalizing ys with
  | nil => cases hp
  | cons a xrest ih =>
    cases ys with
    | nil => cases hp
    | cons b yrest =>
      rcases List.mem_cons.mp hp with rfl | hr
      · exact List.Mem.head _
      · exact List.Mem.tail _ (ih hr)

theorem map_fst_zip_eq {α β : Type} {xs : List α} {ys : List β}
    (hlen : xs.length = ys.length) : (xs.zip ys).map Prod.fst = xs := by
  induction xs generalizing ys with
  | nil => rfl
  | cons a xrest ih =>
    cases ys with
    | nil => cases hlen
    | cons b yrest =>
      simp only [List.length_cons, Nat.succ.injEq] at hlen
      simp [ih hlen]

mutual
theorem rMatchPat_locs_subset (p : Pat) (u : RExpr) {env : List (Ident × RExpr)} :
    rMatchPat p u = some env → ∀ b ∈ env, ∀ l ∈ rExprLocs b.2, l ∈ rExprLocs u := by
  intro hpat b hb l hl
  cases p with
  | wild =>
    simp only [rMatchPat, Option.some.injEq] at hpat
    subst hpat; cases hb
  | var x =>
    simp only [rMatchPat, Option.some.injEq] at hpat
    subst hpat
    rcases List.mem_singleton.mp hb with rfl
    exact hl
  | lit l1 =>
    cases u with
    | lit l2 =>
      simp only [rMatchPat] at hpat
      split at hpat
      · injection hpat with hpat; subst hpat; cases hb
      · cases hpat
    | _ => simp [rMatchPat] at hpat
  | tuple ps =>
    cases u with
    | tuple vs =>
      simp only [rMatchPat] at hpat
      exact rMatchPats_locs_subset ps vs hpat b hb l hl
    | _ => simp [rMatchPat] at hpat
  | ctor adt1 tag1 ps =>
    cases u with
    | makeData adt2 tag2 vs =>
      simp only [rMatchPat] at hpat
      split at hpat
      · exact rMatchPats_locs_subset ps vs hpat b hb l hl
      · cases hpat
    | _ => simp [rMatchPat] at hpat

theorem rMatchPats_locs_subset (ps : List Pat) (vs : List RExpr)
    {env : List (Ident × RExpr)} :
    rMatchPats ps vs = some env → ∀ b ∈ env, ∀ l ∈ rExprLocs b.2, l ∈ rExprLocsList vs := by
  intro hpats b hb l hl
  cases ps with
  | nil =>
    cases vs with
    | nil =>
      simp only [rMatchPats, Option.some.injEq] at hpats
      subst hpats; cases hb
    | cons _ _ => simp [rMatchPats] at hpats
  | cons p prest =>
    cases vs with
    | nil => simp [rMatchPats] at hpats
    | cons u urest =>
      simp only [rMatchPats] at hpats
      cases hm1 : rMatchPat p u with
      | none => simp [hm1] at hpats
      | some b1 =>
        cases hm2 : rMatchPats prest urest with
        | none => simp [hm1, hm2] at hpats
        | some b2 =>
          simp only [hm1, hm2, Option.some.injEq] at hpats
          subst hpats
          rcases List.mem_append.mp hb with h1 | h2
          · exact List.mem_append.mpr (Or.inl (rMatchPat_locs_subset p u hm1 b h1 l hl))
          · exact List.mem_append.mpr (Or.inr (rMatchPats_locs_subset prest urest hm2 b h2 l hl))
end

/-! ### Step Lemmas A & D: Store Monotonicity, Slot Transitions, and Dead-Location Avoidance -/

def StoreStepEvol (ρ ρ' : RStore) (n n' : RegionId) : Prop :=
  ρ.length ≤ ρ'.length ∧
  n ≤ n' ∧
  (∀ (l : Loc) (rv : RExpr), ρ[l]? = some (.heap rv) → ∃ rv', ρ'[l]? = some (.heap rv')) ∧
  (∀ (l : Loc) (rid : RegionId) (rv : RExpr), ρ[l]? = some (.stackLive rid rv) →
    (∃ rv', ρ'[l]? = some (.stackLive rid rv')) ∨ ρ'[l]? = some (.stackFreed rid)) ∧
  (∀ (l : Loc) (rid : RegionId), ρ[l]? = some (.stackFreed rid) →
    ρ'[l]? = some (.stackFreed rid)) ∧
  (∀ (l : Loc) (rid : RegionId), ρ.length ≤ l → ρ'[l]? ≠ some (.stackFreed rid))

structure RStepEvolBox (Φ : FunEnv) (specs : List FnStackSpec) (re : RExpr) : Prop where
  run : ∀ {re' : RExpr} {ρ ρ' : RStore} {n n' : RegionId},
    RStep Φ specs re ρ n re' ρ' n' →
    StoreStepEvol ρ ρ' n n' ∧
    (EnvEscapeWF Φ specs → ∀ l, l < ρ.length → l ∉ rExprLocs re → (∀ s ∈ ρ, l ∉ slotLocs s) →
      l ∉ rExprLocs re' ∧ (∀ s' ∈ ρ', l ∉ slotLocs s'))

structure RStepListEvolBox (Φ : FunEnv) (specs : List FnStackSpec) (es : List RExpr) : Prop where
  run : ∀ {es' : List RExpr} {ρ ρ' : RStore} {n n' : RegionId},
    RStepList Φ specs es ρ n es' ρ' n' →
    StoreStepEvol ρ ρ' n n' ∧
    (EnvEscapeWF Φ specs → ∀ l, l < ρ.length → l ∉ rExprLocsList es → (∀ s ∈ ρ, l ∉ slotLocs s) →
      l ∉ rExprLocsList es' ∧ (∀ s' ∈ ρ', l ∉ slotLocs s'))

theorem storeStepEvol_refl (ρ : RStore) (n : RegionId) : StoreStepEvol ρ ρ n n :=
  ⟨Nat.le_refl _, Nat.le_refl _,
   fun _ rv h => ⟨rv, h⟩,
   fun _ _ rv h => Or.inl ⟨rv, h⟩,
   fun _ _ h => h,
   fun _ _ hle hsome => Nat.not_lt.mpr hle (lt_length_of_getElem?_eq_some hsome)⟩

theorem storeStepEvol_popRegion (rid0 : RegionId) (ρ : RStore) (n : RegionId) :
    StoreStepEvol ρ (popRegion rid0 ρ) n n := by
  refine ⟨by rw [length_popRegion]; exact Nat.le_refl _, Nat.le_refl _, ?_, ?_, ?_, ?_⟩
  · intro l rv hl
    exact ⟨rv, by rw [getElem?_popRegion, hl]; rfl⟩
  · intro l rid rv hl
    rw [getElem?_popRegion, hl]
    simp only [Option.map_some, popRegionSlot]
    split
    · rename_i heq
      rw [beq_iff_eq.mp heq]
      exact Or.inr rfl
    · exact Or.inl ⟨rv, rfl⟩
  · intro l rid hl
    rw [getElem?_popRegion, hl]; rfl
  · intro l rid hle hsome
    rw [ ← length_popRegion rid0 ρ] at hle
    exact Nat.not_lt.mpr hle (lt_length_of_getElem?_eq_some hsome)

mutual
theorem rstep_evol_box (Φ : FunEnv) (specs : List FnStackSpec) (re : RExpr) :
    RStepEvolBox Φ specs re := by
  refine ⟨fun {re' ρ ρ' n n'} hstep => ?_⟩
  cases hstep with
  | tupleStep hsl | makeDataStep hsl | applyDirArgs hsl | concPrimArgs hsl =>
    exact (rstepList_evol_box Φ specs _).run hsl
  | tupleTrap _ | blockEmpty | blockConsTrap | applyFnTrap | applyArgsTrap _ _
  | applyDirTrap _ | unTrap | unVal _ | binLeftTrap | binAndFalse | binOrTrue
  | binRightTrap _ _ _ | binVal _ | binTrap _ | letTrap | ifTrap
  | matchScrutTrap | matchEmpty _ | makeDataTrap _ | getTagTrap | getTagVal _
  | cellNewTrap | stackCellNewTrap | cellGetTrap | cellSetLeftTrap
  | cellSetRightTrap _ | spawnTrap | awaitTrap | concPrimTrap _ =>
    exact ⟨storeStepEvol_refl ρ n, fun _ _ _ _ hslot => ⟨(fun hm => nomatch hm), hslot⟩⟩
  | blockSingle =>
    refine ⟨storeStepEvol_refl ρ n, fun _ l _ hnl hslot => ⟨?_, hslot⟩⟩
    simp only [rExprLocs, rExprLocsList, List.append_nil] at hnl
    exact hnl
  | blockConsStep hs =>
    rcases (rstep_evol_box Φ specs _).run hs with ⟨hev, hdead⟩
    refine ⟨hev, fun henv l hlt hnl hslot => ?_⟩
    simp only [rExprLocs, rExprLocsList, List.mem_append, not_or] at hnl ⊢
    rcases hdead henv l hlt hnl.1 hslot with ⟨hn1', hslot'⟩
    exact ⟨⟨hn1', hnl.2⟩, hslot'⟩
  | blockConsVal _ =>
    refine ⟨storeStepEvol_refl ρ n, fun _ l _ hnl hslot => ⟨?_, hslot⟩⟩
    simp only [rExprLocs, rExprLocsList, List.mem_append, not_or] at hnl ⊢
    exact hnl.2
  | applyFn hs =>
    rcases (rstep_evol_box Φ specs _).run hs with ⟨hev, hdead⟩
    refine ⟨hev, fun henv l hlt hnl hslot => ?_⟩
    simp only [rExprLocs, List.mem_append, not_or] at hnl ⊢
    rcases hdead henv l hlt hnl.1 hslot with ⟨hn1', hslot'⟩
    exact ⟨⟨hn1', hnl.2⟩, hslot'⟩
  | applyArgs _ hsl =>
    rcases (rstepList_evol_box Φ specs _).run hsl with ⟨hev, hdead⟩
    refine ⟨hev, fun henv l hlt hnl hslot => ?_⟩
    simp only [rExprLocs, List.mem_append, not_or] at hnl ⊢
    rcases hdead henv l hlt hnl.2 hslot with ⟨hn2', hslot'⟩
    exact ⟨⟨hnl.1, hn2'⟩, hslot'⟩
  | applyBeta _ _ =>
    refine ⟨storeStepEvol_refl ρ n, fun _ l _ hnl hslot => ⟨?_, hslot⟩⟩
    simp only [rExprLocs, List.mem_append, not_or] at hnl
    intro hm
    rcases rExprLocs_rSubstMany_subset _ _ l hm with hb | ⟨b, hb, hlb⟩
    · exact hnl.1 hb
    · have hb2 : b.2 ∈ _ := mem_zip_snd hb
      have hsub : ∀ (es : List RExpr), b.2 ∈ es → l ∈ rExprLocs b.2 → l ∈ rExprLocsList es := by
        intro es hes hloc
        induction es with
        | nil => cases hes
        | cons a tl ihl =>
          rcases List.mem_cons.mp hes with rfl | htl
          · exact List.mem_append.mpr (Or.inl hloc)
          · exact List.mem_append.mpr (Or.inr (ihl htl))
      exact hnl.2 (hsub _ hb2 hlb)
  | applyDirBeta hfd _ _ =>
    refine ⟨⟨Nat.le_refl _, Nat.le_succ _,
      fun _ rv h => ⟨rv, h⟩, fun _ _ rv h => Or.inl ⟨rv, h⟩, fun _ _ h => h,
      fun l _ hle hsome => Nat.not_lt.mpr hle (lt_length_of_getElem?_eq_some hsome)⟩,
      fun henv l _ hnl hslot => ⟨?_, hslot⟩⟩
    have ⟨hnolocs, _, _⟩ := henv _ _ hfd
    simp only [rExprLocs] at hnl ⊢
    intro hm
    rcases rExprLocs_rSubstMany_subset _ _ l hm with hce | ⟨b, hb, hlb⟩
    · rw [rExprLocs_compileExpr] at hce
      have hempty : exprLocs _ = [] := List.isEmpty_iff.mp hnolocs
      rw [hempty] at hce
      cases hce
    · have hb2 : b.2 ∈ _ := mem_zip_snd hb
      have hsub : ∀ (es : List RExpr), b.2 ∈ es → l ∈ rExprLocs b.2 → l ∈ rExprLocsList es := by
        intro es hes hloc
        induction es with
        | nil => cases hes
        | cons a tl ihl =>
          rcases List.mem_cons.mp hes with rfl | htl
          · exact List.mem_append.mpr (Or.inl hloc)
          · exact List.mem_append.mpr (Or.inr (ihl htl))
      exact hnl (hsub _ hb2 hlb)
  | @unStep _ e1 e1' _ _ _ _ hs | @getTagStep e1 e1' _ _ _ _ hs | @cellNewStep e1 e1' _ _ _ _ hs
  | @stackCellNewStep _ e1 e1' _ _ _ _ hs | @cellGetStep e1 e1' _ _ _ _ hs
  | @spawnStep e1 e1' _ _ _ _ hs | @awaitStep e1 e1' _ _ _ _ hs | @frameStep _ e1 e1' _ _ _ _ hs =>
    exact (rstep_evol_box Φ specs e1).run (re' := e1') hs
  | binLeft hs | letStep hs | matchScrut hs | cellSetLeft hs =>
    rcases (rstep_evol_box Φ specs _).run hs with ⟨hev, hdead⟩
    refine ⟨hev, fun henv l hlt hnl hslot => ?_⟩
    simp only [rExprLocs, List.mem_append, not_or] at hnl ⊢
    rcases hdead henv l hlt hnl.1 hslot with ⟨hn1', hslot'⟩
    exact ⟨⟨hn1', hnl.2⟩, hslot'⟩
  | binRight _ _ _ hs | cellSetRight _ hs =>
    rcases (rstep_evol_box Φ specs _).run hs with ⟨hev, hdead⟩
    refine ⟨hev, fun henv l hlt hnl hslot => ?_⟩
    simp only [rExprLocs, List.mem_append, not_or] at hnl ⊢
    rcases hdead henv l hlt hnl.2 hslot with ⟨hn2', hslot'⟩
    exact ⟨⟨hnl.1, hn2'⟩, hslot'⟩
  | binAndTrue | binOrFalse =>
    refine ⟨storeStepEvol_refl ρ n, fun _ l _ hnl hslot => ⟨?_, hslot⟩⟩
    simp only [rExprLocs, List.mem_append, not_or] at hnl
    exact hnl.2
  | letVal _ =>
    refine ⟨storeStepEvol_refl ρ n, fun _ l _ hnl hslot => ⟨?_, hslot⟩⟩
    simp only [rExprLocs, List.mem_append, not_or] at hnl
    intro hm
    rcases rExprLocs_rSubst_subset _ _ _ l hm with h2 | h1
    · exact hnl.2 h2
    · exact hnl.1 h1
  | ifStep hs =>
    rcases (rstep_evol_box Φ specs _).run hs with ⟨hev, hdead⟩
    refine ⟨hev, fun henv l hlt hnl hslot => ?_⟩
    simp only [rExprLocs, List.mem_append, not_or] at hnl ⊢
    rcases hdead henv l hlt hnl.1.1 hslot with ⟨hnc', hslot'⟩
    exact ⟨⟨⟨hnc', hnl.1.2⟩, hnl.2⟩, hslot'⟩
  | ifTrue =>
    refine ⟨storeStepEvol_refl ρ n, fun _ l _ hnl hslot => ⟨?_, hslot⟩⟩
    simp only [rExprLocs, List.mem_append, not_or] at hnl
    exact hnl.1.2
  | ifFalse =>
    refine ⟨storeStepEvol_refl ρ n, fun _ l _ hnl hslot => ⟨?_, hslot⟩⟩
    simp only [rExprLocs, List.mem_append, not_or] at hnl
    exact hnl.2
  | whileUnfold =>
    refine ⟨storeStepEvol_refl ρ n, fun _ l _ hnl hslot => ⟨?_, hslot⟩⟩
    simp only [rExprLocs, List.mem_append, not_or] at hnl
    simp [rExprLocs, rExprLocsList, hnl.1, hnl.2]
  | @matchHit v p body rest env _ _ _ hpat =>
    refine ⟨storeStepEvol_refl ρ n, fun _ l _ hnl hslot => ⟨?_, hslot⟩⟩
    simp only [rExprLocs, rExprLocsArms, List.mem_append, not_or] at hnl
    intro hm
    rcases rExprLocs_rSubstMany_subset _ _ l hm with hb | ⟨b, hb, hlb⟩
    · exact hnl.2.1 hb
    · exact hnl.1 (rMatchPat_locs_subset p v hpat b hb l hlb)
  | matchMiss _ _ =>
    refine ⟨storeStepEvol_refl ρ n, fun _ l _ hnl hslot => ⟨?_, hslot⟩⟩
    simp only [rExprLocs, rExprLocsArms, List.mem_append, not_or] at hnl ⊢
    exact ⟨hnl.1, hnl.2.2⟩
  | @cellNewVal v _ _ _ =>
    refine ⟨⟨by simp, Nat.le_refl _,
      fun j u hj => ⟨u, by rw [getElem?_append_lt (lt_length_of_getElem?_eq_some hj)]; exact hj⟩,
      fun j r u hj => Or.inl ⟨u, by rw [getElem?_append_lt (lt_length_of_getElem?_eq_some hj)]; exact hj⟩,
      fun j r hj => by rw [getElem?_append_lt (lt_length_of_getElem?_eq_some hj)]; exact hj,
      fun j r hle hsome => by
        rcases Nat.lt_or_eq_of_le hle with hgt | heq
        · rw [getElem?_append_gt hgt] at hsome; cases hsome
        · subst heq; rw [getElem?_append_last] at hsome; cases hsome⟩,
      fun _ l hlt hnl hslot => ⟨?_, ?_⟩⟩
    · simp only [rExprLocs, List.mem_singleton]
      exact Nat.ne_of_lt hlt
    · intro s' hs'
      rcases List.mem_append.mp hs' with hs | hs
      · exact hslot s' hs
      · rcases List.mem_singleton.mp hs with rfl
        exact hnl
  | @stackCellNewVal rid v _ _ _ =>
    refine ⟨⟨by simp, Nat.le_refl _,
      fun j u hj => ⟨u, by rw [getElem?_append_lt (lt_length_of_getElem?_eq_some hj)]; exact hj⟩,
      fun j r u hj => Or.inl ⟨u, by rw [getElem?_append_lt (lt_length_of_getElem?_eq_some hj)]; exact hj⟩,
      fun j r hj => by rw [getElem?_append_lt (lt_length_of_getElem?_eq_some hj)]; exact hj,
      fun j r hle hsome => by
        rcases Nat.lt_or_eq_of_le hle with hgt | heq
        · rw [getElem?_append_gt hgt] at hsome; cases hsome
        · subst heq; rw [getElem?_append_last] at hsome; cases hsome⟩,
      fun _ l hlt hnl hslot => ⟨?_, ?_⟩⟩
    · simp only [rExprLocs, List.mem_singleton]
      exact Nat.ne_of_lt hlt
    · intro s' hs'
      rcases List.mem_append.mp hs' with hs | hs
      · exact hslot s' hs
      · rcases List.mem_singleton.mp hs with rfl
        exact hnl
  | cellGetHeap hl =>
    refine ⟨storeStepEvol_refl ρ n, fun _ l _ _ hslot => ⟨?_, hslot⟩⟩
    exact hslot _ (mem_of_getElem?_eq_some hl)
  | cellGetStack hl =>
    refine ⟨storeStepEvol_refl ρ n, fun _ l _ _ hslot => ⟨?_, hslot⟩⟩
    exact hslot _ (mem_of_getElem?_eq_some hl)
  | @cellSetHeap l0 _ v _ _ hl _ =>
    have hlt0 := lt_length_of_getElem?_eq_some hl
    refine ⟨⟨by simp, Nat.le_refl _,
      fun j u hj => by
        by_cases heq : l0 = j
        · subst heq; exact ⟨v, getElem?_set_self hlt0⟩
        · exact ⟨u, by rw [getElem?_set_ne heq]; exact hj⟩,
      fun j r u hj => by
        by_cases heq : l0 = j
        · subst heq; rw [hl] at hj; cases hj
        · exact Or.inl ⟨u, by rw [getElem?_set_ne heq]; exact hj⟩,
      fun j r hj => by
        by_cases heq : l0 = j
        · subst heq; rw [hl] at hj; cases hj
        · rw [getElem?_set_ne heq]; exact hj,
      fun j r hle hsome => by
        have hlen : (ρ.set l0 (.heap v)).length = ρ.length := by simp
        exact Nat.not_lt.mpr (hlen ▸ hle) (lt_length_of_getElem?_eq_some hsome)⟩,
      fun _ l _ hnl hslot => ⟨(fun hm => nomatch hm), ?_⟩⟩
    simp only [rExprLocs, List.mem_append, not_or] at hnl
    intro s' hs'
    rcases mem_set_subset hs' with rfl | hmem
    · exact hnl.2
    · exact hslot s' hmem
  | @cellSetStack l0 rid0 _ v _ _ hl _ =>
    have hlt0 := lt_length_of_getElem?_eq_some hl
    refine ⟨⟨by simp, Nat.le_refl _,
      fun j u hj => by
        by_cases heq : l0 = j
        · subst heq; rw [hl] at hj; cases hj
        · exact ⟨u, by rw [getElem?_set_ne heq]; exact hj⟩,
      fun j r u hj => by
        by_cases heq : l0 = j
        · subst heq
          rw [hl] at hj; injection hj with hj; injection hj with hr _
          subst hr
          exact Or.inl ⟨v, getElem?_set_self hlt0⟩
        · exact Or.inl ⟨u, by rw [getElem?_set_ne heq]; exact hj⟩,
      fun j r hj => by
        by_cases heq : l0 = j
        · subst heq; rw [hl] at hj; cases hj
        · rw [getElem?_set_ne heq]; exact hj,
      fun j r hle hsome => by
        have hlen : (ρ.set l0 (.stackLive rid0 v)).length = ρ.length := by simp
        exact Nat.not_lt.mpr (hlen ▸ hle) (lt_length_of_getElem?_eq_some hsome)⟩,
      fun _ l _ hnl hslot => ⟨(fun hm => nomatch hm), ?_⟩⟩
    simp only [rExprLocs, List.mem_append, not_or] at hnl
    intro s' hs'
    rcases mem_set_subset hs' with rfl | hmem
    · exact hnl.2
    · exact hslot s' hmem
  | @frameVal rid0 _ _ _ _ =>
    refine ⟨storeStepEvol_popRegion rid0 ρ n, fun _ l _ hnl hslot => ⟨hnl, ?_⟩⟩
    intro s' hs'
    rcases mem_popRegion hs' with ⟨s, hs, rfl⟩
    intro hm
    exact hslot s hs (slotLocs_popRegionSlot_subset rid0 s l hm)
  | @frameTrap rid0 _ _ _ =>
    refine ⟨storeStepEvol_popRegion rid0 ρ n, fun _ l _ _ hslot => ⟨(fun hm => nomatch hm), ?_⟩⟩
    intro s' hs'
    rcases mem_popRegion hs' with ⟨s, hs, rfl⟩
    intro hm
    exact hslot s hs (slotLocs_popRegionSlot_subset rid0 s l hm)
termination_by sizeOf re

theorem rstepList_evol_box (Φ : FunEnv) (specs : List FnStackSpec) (es : List RExpr) :
    RStepListEvolBox Φ specs es := by
  refine ⟨fun {es' ρ ρ' n n'} hsl => ?_⟩
  cases hsl with
  | head hs =>
    rcases (rstep_evol_box Φ specs _).run hs with ⟨hev, hdead⟩
    refine ⟨hev, fun henv l hlt hnl hslot => ?_⟩
    simp only [rExprLocsList, List.mem_append, not_or] at hnl ⊢
    rcases hdead henv l hlt hnl.1 hslot with ⟨hn1', hslot'⟩
    exact ⟨⟨hn1', hnl.2⟩, hslot'⟩
  | tail _ hsl' =>
    rcases (rstepList_evol_box Φ specs _).run hsl' with ⟨hev, hdead⟩
    refine ⟨hev, fun henv l hlt hnl hslot => ?_⟩
    simp only [rExprLocsList, List.mem_append, not_or] at hnl ⊢
    rcases hdead henv l hlt hnl.2 hslot with ⟨hn2', hslot'⟩
    exact ⟨⟨hnl.1, hn2'⟩, hslot'⟩
termination_by sizeOf es
end

/-! ### Step Lemma B: Core Syntactic & Store-Value Well-Formedness (`RStepCoreBox`) -/

theorem mem_args_wf {args : List RExpr} {u : RExpr}
    (hu : u ∈ args)
    (hvals : ∀ a ∈ args, IsRValue a)
    (hcl : rFreeVarsList args = [])
    (hsw : staticSyntaxWFList args = true) :
    IsRValue u ∧ rFreeVars u = [] ∧ staticSyntaxWF u = true ∧
      noRegionSyntax u = true ∧ exprFrames u = [] ∧
      (∀ l ∈ rExprLocs u, l ∈ rExprLocsList args) ∧
      (∀ l rid inReg, locConfinedList l rid inReg args = true → l ∉ rExprLocs u) := by
  induction args with
  | nil => cases hu
  | cons a rest ih =>
    simp only [rFreeVarsList, List.append_eq_nil_iff] at hcl
    simp only [staticSyntaxWFList, Bool.and_eq_true] at hsw
    rcases List.mem_cons.mp hu with rfl | hrest
    · have hva := hvals u (List.Mem.head _)
      have hnra := noRegionSyntax_of_isRValue hva hsw.1
      refine ⟨hva, hcl.1, hsw.1, hnra, exprFrames_of_noRegionSyntax hnra,
        fun l hl => List.mem_append.mpr (Or.inl hl),
        fun l rid inReg hcl_list => ?_⟩
      simp only [locConfinedList, Bool.and_eq_true] at hcl_list
      exact not_mem_locs_of_isRValue_locConfined hva hsw.1 hcl_list.1
    · rcases ih hrest (fun x hx => hvals x (List.Mem.tail _ hx)) hcl.2 hsw.2 with
        ⟨hvu, hclu, hswu, hnru, hfu, hlocu, hconfu⟩
      refine ⟨hvu, hclu, hswu, hnru, hfu,
        fun l hl => List.mem_append.mpr (Or.inr (hlocu l hl)),
        fun l rid inReg hcl_list => ?_⟩
      simp only [locConfinedList, Bool.and_eq_true] at hcl_list
      exact hconfu l rid inReg hcl_list.2

mutual
theorem staticSyntaxWF_of_noRegionSyntax (e : RExpr) :
    noRegionSyntax e = true → staticSyntaxWF e = true := by
  intro h
  cases e with
  | lit _ | var _ | loc _ | taskRef _ | syncRef _ _ | trap _ => rfl
  | stackCellNew _ _ | frame _ _ => simp [noRegionSyntax] at h
  | tuple es | block es | applyDir _ es | makeData _ _ es | concPrim _ es =>
    simp only [noRegionSyntax] at h
    exact staticSyntaxWFList_of_noRegionSyntax es h
  | lam _ _ _ body =>
    exact h
  | apply fn args =>
    simp only [noRegionSyntax, Bool.and_eq_true] at h
    simp [staticSyntaxWF, staticSyntaxWF_of_noRegionSyntax fn h.1,
      staticSyntaxWFList_of_noRegionSyntax args h.2]
  | bin _ e1 e2 | let_ _ e1 e2 | cellSet e1 e2 =>
    simp only [noRegionSyntax, Bool.and_eq_true] at h
    simp [staticSyntaxWF, staticSyntaxWF_of_noRegionSyntax e1 h.1,
      staticSyntaxWF_of_noRegionSyntax e2 h.2]
  | while_ c b =>
    simp only [noRegionSyntax, Bool.and_eq_true] at h
    simp [staticSyntaxWF, exprFrames_of_noRegionSyntax h.1, exprFrames_of_noRegionSyntax h.2,
      staticSyntaxWF_of_noRegionSyntax c h.1, staticSyntaxWF_of_noRegionSyntax b h.2]
  | un _ e1 | getTag e1 | cellNew e1 | cellGet e1 | spawn e1 | await e1 =>
    simp only [noRegionSyntax] at h
    exact staticSyntaxWF_of_noRegionSyntax e1 h
  | if_ c t e2 =>
    simp only [noRegionSyntax, Bool.and_eq_true] at h
    simp [staticSyntaxWF, staticSyntaxWF_of_noRegionSyntax c h.1.1,
      staticSyntaxWF_of_noRegionSyntax t h.1.2, staticSyntaxWF_of_noRegionSyntax e2 h.2]
  | match_ scrut arms =>
    simp only [noRegionSyntax, Bool.and_eq_true] at h
    simp [staticSyntaxWF, staticSyntaxWF_of_noRegionSyntax scrut h.1,
      staticSyntaxWFArms_of_noRegionSyntax arms h.2]

theorem staticSyntaxWFList_of_noRegionSyntax (es : List RExpr) :
    noRegionSyntaxList es = true → staticSyntaxWFList es = true := by
  intro h
  cases es with
  | nil => rfl
  | cons e rest =>
    simp only [noRegionSyntaxList, Bool.and_eq_true] at h
    simp [staticSyntaxWFList, staticSyntaxWF_of_noRegionSyntax e h.1,
      staticSyntaxWFList_of_noRegionSyntax rest h.2]

theorem staticSyntaxWFArms_of_noRegionSyntax (arms : List (Pat × RExpr)) :
    noRegionSyntaxArms arms = true → staticSyntaxWFArms arms = true := by
  intro h
  cases arms with
  | nil => rfl
  | cons arm rest =>
    cases arm with
    | mk p body =>
      simp only [noRegionSyntaxArms, Bool.and_eq_true] at h
      simp [staticSyntaxWFArms, staticSyntaxWF_of_noRegionSyntax body h.1,
        staticSyntaxWFArms_of_noRegionSyntax rest h.2]
end

structure RStepCoreBox (Φ : FunEnv) (specs : List FnStackSpec) (re : RExpr) : Prop where
  run : ∀ (enc : List RegionId) {re' : RExpr} {ρ ρ' : RStore} {n n' : RegionId},
    EnvEscapeWF Φ specs →
    RStep Φ specs re ρ n re' ρ' n' →
    (∀ s ∈ ρ, SlotValueWF ρ.length s) →
    rFreeVars re = [] →
    (∀ l ∈ rExprLocs re, l < ρ.length) →
    staticSyntaxWF re = true →
    stackNewWF enc re = true →
    (∀ s' ∈ ρ', SlotValueWF ρ'.length s') ∧
    rFreeVars re' = [] ∧
    (∀ l ∈ rExprLocs re', l < ρ'.length) ∧
    staticSyntaxWF re' = true ∧
    stackNewWF enc re' = true ∧
    (∀ r ∈ exprFrames re', r ∈ exprFrames re ∨ (n ≤ r ∧ r < n'))

structure RStepListCoreBox (Φ : FunEnv) (specs : List FnStackSpec) (es : List RExpr) : Prop where
  run : ∀ (enc : List RegionId) {es' : List RExpr} {ρ ρ' : RStore} {n n' : RegionId},
    EnvEscapeWF Φ specs →
    RStepList Φ specs es ρ n es' ρ' n' →
    (∀ s ∈ ρ, SlotValueWF ρ.length s) →
    rFreeVarsList es = [] →
    (∀ l ∈ rExprLocsList es, l < ρ.length) →
    staticSyntaxWFList es = true →
    stackNewWFList enc es = true →
    (∀ s' ∈ ρ', SlotValueWF ρ'.length s') ∧
    rFreeVarsList es' = [] ∧
    (∀ l ∈ rExprLocsList es', l < ρ'.length) ∧
    staticSyntaxWFList es' = true ∧
    stackNewWFList enc es' = true ∧
    (∀ r ∈ exprFramesList es', r ∈ exprFramesList es ∨ (n ≤ r ∧ r < n'))

mutual
theorem rstep_core_box (Φ : FunEnv) (specs : List FnStackSpec) (re : RExpr) :
    RStepCoreBox Φ specs re := by
  refine ⟨fun enc {re' ρ ρ' n n'} henv hstep hslots hcl hlocs hsw hsn => ?_⟩
  cases hstep with
  | stackCellNewStep _ | stackCellNewTrap | stackCellNewVal _ =>
    simp [stackNewWF] at hsn
  | tupleTrap _ | blockEmpty | blockConsTrap | applyFnTrap | applyArgsTrap _ _
  | applyDirTrap _ | unTrap | unVal _ | binLeftTrap | binAndFalse | binOrTrue
  | binRightTrap _ _ _ | binVal _ | binTrap _ | letTrap | ifTrap
  | matchScrutTrap | matchEmpty _ | makeDataTrap _ | getTagTrap | getTagVal _
  | cellNewTrap | cellGetTrap | cellSetLeftTrap | cellSetRightTrap _
  | spawnTrap | awaitTrap | concPrimTrap _ =>
    exact ⟨hslots, rfl, (fun _ hm => nomatch hm), rfl, rfl, (fun _ hm => nomatch hm)⟩
  | tupleStep hsl | makeDataStep hsl | applyDirArgs hsl | concPrimArgs hsl =>
    exact (rstepList_core_box Φ specs _).run enc henv hsl hslots hcl hlocs hsw hsn
  | blockSingle =>
    simp only [rFreeVars, rFreeVarsList, List.append_nil] at hcl
    simp only [rExprLocs, rExprLocsList, List.append_nil] at hlocs
    simp only [staticSyntaxWF, staticSyntaxWFList, Bool.and_true] at hsw
    simp only [stackNewWF, stackNewWFList, Bool.and_true] at hsn
    exact ⟨hslots, hcl, hlocs, hsw, hsn, fun r hr => Or.inl (by simp [exprFrames, exprFramesList, hr])⟩
  | blockConsStep hs =>
    have hev := ((rstep_evol_box Φ specs _).run hs).1
    simp only [rFreeVars, rFreeVarsList, List.append_eq_nil_iff] at hcl
    simp only [staticSyntaxWF, staticSyntaxWFList, Bool.and_eq_true] at hsw
    simp only [stackNewWF, stackNewWFList, Bool.and_eq_true] at hsn
    rcases (rstep_core_box Φ specs _).run enc henv hs hslots hcl.1
      (fun l hl => hlocs l (List.mem_append.mpr (Or.inl hl))) hsw.1 hsn.1 with
      ⟨hslots', hcl1', hlocs1', hsw1', hsn1', hfr1'⟩
    refine ⟨hslots', ?_, ?_, ?_, ?_, ?_⟩
    · simp [rFreeVars, rFreeVarsList, hcl1', hcl.2.1, hcl.2.2]
    · intro l hl
      rcases List.mem_append.mp hl with h1 | h2
      · exact hlocs1' l h1
      · exact Nat.lt_of_lt_of_le (hlocs l (List.mem_append.mpr (Or.inr h2))) hev.1
    · simp [staticSyntaxWF, staticSyntaxWFList, hsw1', hsw.2.1, hsw.2.2]
    · simp [stackNewWF, stackNewWFList, hsn1', hsn.2.1, hsn.2.2]
    · intro r hr
      simp only [exprFrames, exprFramesList, List.mem_append] at hr ⊢
      rcases hr with h1 | h2
      · exact (hfr1' r h1).imp Or.inl id
      · exact Or.inl (Or.inr h2)
  | blockConsVal _ =>
    simp only [rFreeVars, rFreeVarsList, List.append_eq_nil_iff] at hcl
    simp only [staticSyntaxWF, staticSyntaxWFList, Bool.and_eq_true] at hsw
    simp only [stackNewWF, stackNewWFList, Bool.and_eq_true] at hsn
    refine ⟨hslots, by simp [rFreeVars, rFreeVarsList, hcl.2.1, hcl.2.2],
      fun l hl => hlocs l (List.mem_append.mpr (Or.inr hl)),
      by simp [staticSyntaxWF, staticSyntaxWFList, hsw.2.1, hsw.2.2],
      by simp [stackNewWF, stackNewWFList, hsn.2.1, hsn.2.2],
      fun r hr => Or.inl (List.mem_append.mpr (Or.inr hr))⟩
  | applyFn hs =>
    have hev := ((rstep_evol_box Φ specs _).run hs).1
    simp only [rFreeVars, List.append_eq_nil_iff] at hcl
    simp only [staticSyntaxWF, Bool.and_eq_true] at hsw
    simp only [stackNewWF, Bool.and_eq_true] at hsn
    rcases (rstep_core_box Φ specs _).run enc henv hs hslots hcl.1
      (fun l hl => hlocs l (List.mem_append.mpr (Or.inl hl))) hsw.1 hsn.1 with
      ⟨hslots', hcl1', hlocs1', hsw1', hsn1', hfr1'⟩
    refine ⟨hslots', by simp [rFreeVars, hcl1', hcl.2], ?_,
      by simp [staticSyntaxWF, hsw1', hsw.2],
      by simp [stackNewWF, hsn1', hsn.2], ?_⟩
    · intro l hl
      rcases List.mem_append.mp hl with h1 | h2
      · exact hlocs1' l h1
      · exact Nat.lt_of_lt_of_le (hlocs l (List.mem_append.mpr (Or.inr h2))) hev.1
    · intro r hr
      rcases List.mem_append.mp hr with h1 | h2
      · exact (hfr1' r h1).imp (fun h => List.mem_append.mpr (Or.inl h)) id
      · exact Or.inl (List.mem_append.mpr (Or.inr h2))
  | applyArgs _ hsl =>
    have hev := ((rstepList_evol_box Φ specs _).run hsl).1
    simp only [rFreeVars, List.append_eq_nil_iff] at hcl
    simp only [staticSyntaxWF, Bool.and_eq_true] at hsw
    simp only [stackNewWF, Bool.and_eq_true] at hsn
    rcases (rstepList_core_box Φ specs _).run enc henv hsl hslots hcl.2
      (fun l hl => hlocs l (List.mem_append.mpr (Or.inr hl))) hsw.2 hsn.2 with
      ⟨hslots', hcl2', hlocs2', hsw2', hsn2', hfr2'⟩
    refine ⟨hslots', by simp [rFreeVars, hcl.1, hcl2'], ?_,
      by simp [staticSyntaxWF, hsw.1, hsw2'],
      by simp [stackNewWF, hsn.1, hsn2'], ?_⟩
    · intro l hl
      rcases List.mem_append.mp hl with h1 | h2
      · exact Nat.lt_of_lt_of_le (hlocs l (List.mem_append.mpr (Or.inl h1))) hev.1
      · exact hlocs2' l h2
    · intro r hr
      rcases List.mem_append.mp hr with h1 | h2
      · exact Or.inl (List.mem_append.mpr (Or.inl h1))
      · exact (hfr2' r h2).imp (fun h => List.mem_append.mpr (Or.inr h)) id
  | @applyBeta m ps ret body args _ _ hvals hlen =>
    simp only [rFreeVars, List.append_eq_nil_iff] at hcl
    simp only [staticSyntaxWF, Bool.and_eq_true] at hsw
    simp only [stackNewWF, Bool.and_eq_true] at hsn
    have hbs : ∀ b ∈ rZipParams ps args,
        IsRValue b.2 ∧ rFreeVars b.2 = [] ∧ staticSyntaxWF b.2 = true ∧
          noRegionSyntax b.2 = true ∧ exprFrames b.2 = [] ∧
          (∀ l ∈ rExprLocs b.2, l ∈ rExprLocsList args) := by
      intro b hb
      rcases mem_args_wf (mem_zip_snd hb) hvals hcl.2 hsw.2 with
        ⟨hv, hc, hs, hnr, hf, hloc, _⟩
      exact ⟨hv, hc, hs, hnr, hf, hloc⟩
    refine ⟨hslots, ?_, ?_, ?_, ?_, ?_⟩
    · apply List.eq_nil_iff_forall_not_mem.mpr
      intro z hz
      have ⟨hzb, hnotb⟩ := rFreeVars_rSubstMany_subset (fun b hb => (hbs b hb).2.1) body z hz
      have hfst : (rZipParams ps args).map Prod.fst = ps.map Prod.fst := by
        unfold rZipParams
        exact map_fst_zip_eq (by rw [List.length_map, hlen])
      by_cases hmem_p : z ∈ ps.map Prod.fst
      · rw [← hfst] at hmem_p
        rcases List.mem_map.mp hmem_p with ⟨b, hb, rfl⟩
        exact hnotb b hb rfl
      · have hz_lam : z ∈ (rFreeVars body).filter (fun w => !(ps.any (fun p => p.1 == w))) := by
          simp only [List.mem_filter]
          refine ⟨hzb, ?_⟩
          cases hany : ps.any (fun p => p.1 == z) with
          | false => rfl
          | true =>
            rcases List.any_eq_true.mp hany with ⟨p, hp, hpz⟩
            exact absurd (beq_iff_eq.mp hpz ▸ List.mem_map_of_mem (f := Prod.fst) hp) hmem_p
        rw [hcl.1] at hz_lam
        cases hz_lam
    · intro l hl
      rcases rExprLocs_rSubstMany_subset _ body l hl with hb | ⟨b, hb, hlb⟩
      · exact hlocs l (List.mem_append.mpr (Or.inl hb))
      · exact hlocs l (List.mem_append.mpr (Or.inr ((hbs b hb).2.2.2.2.2 l hlb)))
    · exact staticSyntaxWF_rSubstMany
        (fun b hb => (hbs b hb).2.2.1)
        (fun b hb => (hbs b hb).2.2.2.1)
        (staticSyntaxWF_of_noRegionSyntax body hsw.1)
    · exact stackNewWF_rSubstMany enc
        (fun b hb => (hbs b hb).1)
        (fun b hb => (hbs b hb).2.1)
        (fun b hb => (hbs b hb).2.2.1)
        (stackNewWF_of_noRegionSyntax enc hsw.1)
    · intro r hr
      rw [exprFrames_rSubstMany (fun b hb => (hbs b hb).2.2.2.2.1),
          exprFrames_of_noRegionSyntax hsw.1] at hr
      cases hr
  | @applyDirBeta name fd args ρ n hfd hvals hlen =>
    have ⟨hnolocs, hclosed_fd, hvars_fd⟩ := henv name fd hfd
    have hbs : ∀ b ∈ rZipParams fd.params args,
        IsRValue b.2 ∧ rFreeVars b.2 = [] ∧ staticSyntaxWF b.2 = true ∧
          noRegionSyntax b.2 = true ∧ exprFrames b.2 = [] ∧
          (∀ l ∈ rExprLocs b.2, l ∈ rExprLocsList args) := by
      intro b hb
      rcases mem_args_wf (mem_zip_snd hb) hvals hcl hsw with
        ⟨hv, hc, hs, hnr, hf, hloc, _⟩
      exact ⟨hv, hc, hs, hnr, hf, hloc⟩
    let ce := compileExpr (lookupStackVars specs name) n fd.body
    refine ⟨hslots, ?_, ?_, ?_, ?_, ?_⟩
    · simp only [rFreeVars]
      apply List.eq_nil_iff_forall_not_mem.mpr
      intro z hz
      have ⟨hz_ce, hnotb⟩ := rFreeVars_rSubstMany_subset (fun b hb => (hbs b hb).2.1) ce z hz
      rw [rFreeVars_compileExpr] at hz_ce
      have hp_any : fd.params.any (·.1 == z) = true := List.all_eq_true.mp hclosed_fd z hz_ce
      rcases List.any_eq_true.mp hp_any with ⟨p, hp, hpz⟩
      have hz_mem : z ∈ fd.params.map Prod.fst :=
        beq_iff_eq.mp hpz ▸ List.mem_map_of_mem (f := Prod.fst) hp
      have hfst : (rZipParams fd.params args).map Prod.fst = fd.params.map Prod.fst := by
        unfold rZipParams
        exact map_fst_zip_eq (by rw [List.length_map, hlen])
      rw [← hfst] at hz_mem
      rcases List.mem_map.mp hz_mem with ⟨b, hb, rfl⟩
      exact hnotb b hb rfl
    · intro l hl
      simp only [rExprLocs] at hl
      rcases rExprLocs_rSubstMany_subset _ ce l hl with hce | ⟨b, hb, hlb⟩
      · rw [rExprLocs_compileExpr] at hce
        rw [List.isEmpty_iff.mp hnolocs] at hce
        cases hce
      · exact hlocs l ((hbs b hb).2.2.2.2.2 l hlb)
    · simp only [staticSyntaxWF]
      exact staticSyntaxWF_rSubstMany
        (fun b hb => (hbs b hb).2.2.1)
        (fun b hb => (hbs b hb).2.2.2.1)
        (staticSyntaxWF_compileExpr _ n fd.body)
    · simp only [stackNewWF]
      apply stackNewWF_rSubstMany (n :: enc)
        (fun b hb => (hbs b hb).1)
        (fun b hb => (hbs b hb).2.1)
        (fun b hb => (hbs b hb).2.2.1)
      apply stackNewWF_compileExpr (n :: enc) _ n fd.body
      · right; simp
      · intro x hx; exact Or.inl (hvars_fd x hx)
    · intro r hr
      simp only [exprFrames, exprFrames_rSubstMany (fun b hb => (hbs b hb).2.2.2.2.1),
        exprFrames_compileExpr] at hr
      rw [List.mem_singleton.mp hr]
      exact Or.inr ⟨Nat.le_refl n, Nat.lt_succ_self n⟩
  | @unStep _ e1 e1' _ _ _ _ hs | @getTagStep e1 e1' _ _ _ _ hs | @cellNewStep e1 e1' _ _ _ _ hs
  | @cellGetStep e1 e1' _ _ _ _ hs | @spawnStep e1 e1' _ _ _ _ hs | @awaitStep e1 e1' _ _ _ _ hs =>
    exact (rstep_core_box Φ specs e1).run enc (re' := e1') henv hs hslots hcl hlocs hsw hsn
  | @frameStep rid0 _ _ _ _ _ _ hs =>
    rcases (rstep_core_box Φ specs _).run (rid0 :: enc) henv hs hslots hcl hlocs hsw hsn with
      ⟨hslots', hcl', hlocs', hsw', hsn', hfr'⟩
    refine ⟨hslots', hcl', hlocs', hsw', hsn', fun r hr => ?_⟩
    simp only [exprFrames, List.mem_cons] at hr ⊢
    rcases hr with rfl | hr'
    · exact Or.inl (Or.inl rfl)
    · exact (hfr' r hr').imp Or.inr id
  | binLeft hs | matchScrut hs | cellSetLeft hs =>
    have hev := ((rstep_evol_box Φ specs _).run hs).1
    simp only [rFreeVars, List.append_eq_nil_iff] at hcl
    simp only [staticSyntaxWF, Bool.and_eq_true] at hsw
    simp only [stackNewWF, Bool.and_eq_true] at hsn
    rcases (rstep_core_box Φ specs _).run enc henv hs hslots hcl.1
      (fun l hl => hlocs l (List.mem_append.mpr (Or.inl hl))) hsw.1 hsn.1 with
      ⟨hslots', hcl1', hlocs1', hsw1', hsn1', hfr1'⟩
    refine ⟨hslots', by simp [rFreeVars, hcl1', hcl.2], ?_,
      by simp [staticSyntaxWF, hsw1', hsw.2],
      by simp [stackNewWF, hsn1', hsn.2], ?_⟩
    · intro l hl
      rcases List.mem_append.mp hl with h1 | h2
      · exact hlocs1' l h1
      · exact Nat.lt_of_lt_of_le (hlocs l (List.mem_append.mpr (Or.inr h2))) hev.1
    · intro r hr
      rcases List.mem_append.mp hr with h1 | h2
      · exact (hfr1' r h1).imp (fun h => List.mem_append.mpr (Or.inl h)) id
      · exact Or.inl (List.mem_append.mpr (Or.inr h2))
  | binRight _ _ _ hs | cellSetRight _ hs =>
    have hev := ((rstep_evol_box Φ specs _).run hs).1
    simp only [rFreeVars, List.append_eq_nil_iff] at hcl
    simp only [staticSyntaxWF, Bool.and_eq_true] at hsw
    simp only [stackNewWF, Bool.and_eq_true] at hsn
    rcases (rstep_core_box Φ specs _).run enc henv hs hslots hcl.2
      (fun l hl => hlocs l (List.mem_append.mpr (Or.inr hl))) hsw.2 hsn.2 with
      ⟨hslots', hcl2', hlocs2', hsw2', hsn2', hfr2'⟩
    refine ⟨hslots', by simp [rFreeVars, hcl.1, hcl2'], ?_,
      by simp [staticSyntaxWF, hsw.1, hsw2'],
      by simp [stackNewWF, hsn.1, hsn2'], ?_⟩
    · intro l hl
      rcases List.mem_append.mp hl with h1 | h2
      · exact Nat.lt_of_lt_of_le (hlocs l (List.mem_append.mpr (Or.inl h1))) hev.1
      · exact hlocs2' l h2
    · intro r hr
      rcases List.mem_append.mp hr with h1 | h2
      · exact Or.inl (List.mem_append.mpr (Or.inl h1))
      · exact (hfr2' r h2).imp (fun h => List.mem_append.mpr (Or.inr h)) id
  | binAndTrue | binOrFalse =>
    simp only [rFreeVars, List.append_eq_nil_iff] at hcl
    simp only [staticSyntaxWF, Bool.and_eq_true] at hsw
    simp only [stackNewWF, Bool.and_eq_true] at hsn
    exact ⟨hslots, hcl.2, fun l hl => hlocs l (List.mem_append.mpr (Or.inr hl)),
      hsw.2, hsn.2, fun r hr => Or.inl (List.mem_append.mpr (Or.inr hr))⟩
  | @letStep x e1 e1' e2 _ _ _ _ hs =>
    have hev := ((rstep_evol_box Φ specs _).run hs).1
    simp only [rFreeVars, List.append_eq_nil_iff] at hcl
    simp only [staticSyntaxWF, Bool.and_eq_true] at hsw
    cases hsc : asStackCellNew? e1 with
    | none =>
      rw [stackNewWF_let_nonStackCellNew enc x e1 e2 hsc, Bool.and_eq_true] at hsn
      rcases (rstep_core_box Φ specs _).run enc henv hs hslots hcl.1
        (fun l hl => hlocs l (List.mem_append.mpr (Or.inl hl))) hsw.1 hsn.1 with
        ⟨hslots', hcl1', hlocs1', hsw1', hsn1', hfr1'⟩
      have hsc' := asStackCellNew?_eq_none_of_stackNewWF hsn1'
      refine ⟨hslots', by simp [rFreeVars, hcl1', hcl.2], ?_,
        by simp [staticSyntaxWF, hsw1', hsw.2],
        by rw [stackNewWF_let_nonStackCellNew enc x e1' e2 hsc']; simp [hsn1', hsn.2], ?_⟩
      · intro l hl
        rcases List.mem_append.mp hl with h1 | h2
        · exact hlocs1' l h1
        · exact Nat.lt_of_lt_of_le (hlocs l (List.mem_append.mpr (Or.inr h2))) hev.1
      · intro r hr
        rcases List.mem_append.mp hr with h1 | h2
        · exact (hfr1' r h1).imp (fun h => List.mem_append.mpr (Or.inl h)) id
        · exact Or.inl (List.mem_append.mpr (Or.inr h2))
    | some p =>
      cases p with
      | mk rid0 init =>
        have he1 := asStackCellNew?_eq_some.mp hsc
        subst he1
        simp only [stackNewWF, Bool.and_eq_true] at hsn
        cases hs with
        | stackCellNewStep hs_init =>
          rcases (rstep_core_box Φ specs _).run enc henv hs_init hslots hcl.1
            (fun l hl => hlocs l (List.mem_append.mpr (Or.inl hl))) hsw.1 hsn.1.1.2 with
            ⟨hslots', hcl1', hlocs1', hsw1', hsn1', hfr1'⟩
          refine ⟨hslots', by simp [rFreeVars, hcl1', hcl.2], ?_,
            by simp [staticSyntaxWF, hsw1', hsw.2],
            by simp only [stackNewWF, hsn.1.1.1, hsn1', hsn.1.2, hsn.2, Bool.and_self], ?_⟩
          · intro l hl
            rcases List.mem_append.mp hl with h1 | h2
            · exact hlocs1' l h1
            · exact Nat.lt_of_lt_of_le (hlocs l (List.mem_append.mpr (Or.inr h2))) hev.1
          · intro r hr
            rcases List.mem_append.mp hr with h1 | h2
            · exact (hfr1' r h1).imp (fun h => List.mem_append.mpr (Or.inl h)) id
            · exact Or.inl (List.mem_append.mpr (Or.inr h2))
        | stackCellNewTrap =>
          refine ⟨hslots, by simp [rFreeVars, hcl.2],
            fun l hl => hlocs l (List.mem_append.mpr (Or.inr hl)),
            by simp [staticSyntaxWF, hsw.2],
            by simp [stackNewWF, hsn.1.2],
            fun r hr => Or.inl (List.mem_append.mpr (Or.inr hr))⟩
        | stackCellNewVal hv =>
          refine ⟨?_, by simp [rFreeVars, hcl.2], ?_,
            by simp [staticSyntaxWF, hsw.2],
            by simp [stackNewWF, hsn.1.2],
            fun r hr => Or.inl (List.mem_append.mpr (Or.inr hr))⟩
          · intro s' hs'
            rcases List.mem_append.mp hs' with hs_old | hs_new
            · exact slotValueWF_mono (by simp) (hslots s' hs_old)
            · rcases List.mem_singleton.mp hs_new with rfl
              refine ⟨hv, hcl.1, hsw.1, fun l hl => ?_⟩
              simp only [List.length_append, List.length_singleton]
              exact Nat.lt_succ_of_lt (hlocs l (List.mem_append.mpr (Or.inl hl)))
          · intro l hl
            simp only [rExprLocs, List.singleton_append, List.mem_cons] at hl
            simp only [List.length_append, List.length_singleton]
            rcases hl with rfl | hl2
            · exact Nat.lt_succ_self _
            · exact Nat.lt_succ_of_lt (hlocs l (List.mem_append.mpr (Or.inr hl2)))
  | @letVal x v1 e2 _ _ hv1 =>
    simp only [rFreeVars, List.append_eq_nil_iff] at hcl
    simp only [staticSyntaxWF, Bool.and_eq_true] at hsw
    have hsc : asStackCellNew? v1 = none := by cases hv1 <;> rfl
    rw [stackNewWF_let_nonStackCellNew enc x v1 e2 hsc, Bool.and_eq_true] at hsn
    have hnr1 := noRegionSyntax_of_isRValue hv1 hsw.1
    refine ⟨hslots, ?_, ?_,
      staticSyntaxWF_rSubst x hsw.1 hnr1 hsw.2,
      stackNewWF_rSubst enc x hv1 hcl.1 hsw.1 hsn.2,
      fun r hr => ?_⟩
    · apply List.eq_nil_iff_forall_not_mem.mpr
      intro z hz
      have ⟨hze2, hzx⟩ := rFreeVars_rSubst_subset hcl.1 e2 z hz
      have hmem_filt : z ∈ (rFreeVars e2).filter (· != x) :=
        List.mem_filter.mpr ⟨hze2, bne_iff_ne.mpr hzx⟩
      rw [hcl.2] at hmem_filt
      cases hmem_filt
    · intro l hl
      rcases rExprLocs_rSubst_subset x v1 e2 l hl with h2 | h1
      · exact hlocs l (List.mem_append.mpr (Or.inr h2))
      · exact hlocs l (List.mem_append.mpr (Or.inl h1))
    · rw [exprFrames_rSubst x (exprFrames_of_noRegionSyntax hnr1) e2] at hr
      exact Or.inl (List.mem_append.mpr (Or.inr hr))
  | ifStep hs =>
    have hev := ((rstep_evol_box Φ specs _).run hs).1
    simp only [rFreeVars, List.append_eq_nil_iff] at hcl
    simp only [staticSyntaxWF, Bool.and_eq_true] at hsw
    simp only [stackNewWF, Bool.and_eq_true] at hsn
    rcases (rstep_core_box Φ specs _).run enc henv hs hslots hcl.1.1
      (fun l hl => hlocs l (List.mem_append.mpr (Or.inl (List.mem_append.mpr (Or.inl hl)))))
      hsw.1.1 hsn.1.1 with ⟨hslots', hclc', hlocsc', hswc', hsnc', hfrc'⟩
    refine ⟨hslots', by simp [rFreeVars, hclc', hcl.1.2, hcl.2], ?_,
      by simp [staticSyntaxWF, hswc', hsw.1.2, hsw.2],
      by simp [stackNewWF, hsnc', hsn.1.2, hsn.2], ?_⟩
    · intro l hl
      simp only [rExprLocs, List.mem_append] at hl
      rcases hl with (h1 | h2) | h3
      · exact hlocsc' l h1
      · exact Nat.lt_of_lt_of_le
          (hlocs l (List.mem_append.mpr (Or.inl (List.mem_append.mpr (Or.inr h2))))) hev.1
      · exact Nat.lt_of_lt_of_le (hlocs l (List.mem_append.mpr (Or.inr h3))) hev.1
    · intro r hr
      simp only [exprFrames, List.mem_append] at hr ⊢
      rcases hr with (h1 | h2) | h3
      · exact (hfrc' r h1).imp (fun h => Or.inl (Or.inl h)) id
      · exact Or.inl (Or.inl (Or.inr h2))
      · exact Or.inl (Or.inr h3)
  | ifTrue =>
    simp only [rFreeVars, List.append_eq_nil_iff] at hcl
    simp only [staticSyntaxWF, Bool.and_eq_true] at hsw
    simp only [stackNewWF, Bool.and_eq_true] at hsn
    exact ⟨hslots, hcl.1.2,
      fun l hl => hlocs l (List.mem_append.mpr (Or.inl (List.mem_append.mpr (Or.inr hl)))),
      hsw.1.2, hsn.1.2,
      fun r hr => Or.inl (List.mem_append.mpr (Or.inl (List.mem_append.mpr (Or.inr hr))))⟩
  | ifFalse =>
    simp only [rFreeVars, List.append_eq_nil_iff] at hcl
    simp only [staticSyntaxWF, Bool.and_eq_true] at hsw
    simp only [stackNewWF, Bool.and_eq_true] at hsn
    exact ⟨hslots, hcl.2, fun l hl => hlocs l (List.mem_append.mpr (Or.inr hl)),
      hsw.2, hsn.2, fun r hr => Or.inl (List.mem_append.mpr (Or.inr hr))⟩
  | whileUnfold =>
    simp only [rFreeVars, List.append_eq_nil_iff] at hcl
    simp only [staticSyntaxWF, Bool.and_eq_true] at hsw
    simp only [stackNewWF, Bool.and_eq_true] at hsn
    have hfc : exprFrames _ = [] := List.isEmpty_iff.mp hsw.1.1.1
    have hfb : exprFrames _ = [] := List.isEmpty_iff.mp hsw.1.1.2
    refine ⟨hslots, by simp [rFreeVars, rFreeVarsList, hcl.1, hcl.2], ?_,
      by simp [staticSyntaxWF, staticSyntaxWFList, hfc, hfb, hsw.1.2, hsw.2],
      by simp [stackNewWF, stackNewWFList, hsn.1, hsn.2],
      fun r hr => by simp [exprFrames, exprFramesList, hfc, hfb] at hr⟩
    intro l hl
    simp only [rExprLocs, rExprLocsList, List.append_nil, List.mem_append] at hl
    rcases hl with h1 | (h2 | (h3 | h4))
    · exact hlocs l (List.mem_append.mpr (Or.inl h1))
    · exact hlocs l (List.mem_append.mpr (Or.inr h2))
    · exact hlocs l (List.mem_append.mpr (Or.inl h3))
    · exact hlocs l (List.mem_append.mpr (Or.inr h4))
  | @matchHit v p body rest env _ _ hv hpat =>
    simp only [rFreeVars, rFreeVarsArms, List.append_eq_nil_iff] at hcl
    simp only [staticSyntaxWF, staticSyntaxWFArms, Bool.and_eq_true] at hsw
    simp only [stackNewWF, stackNewWFArms, Bool.and_eq_true] at hsn
    have ⟨hnames, hbinds⟩ := rMatchPat_wf hv hcl.1 hsw.1 hpat
    refine ⟨hslots, ?_, ?_, ?_, ?_, ?_⟩
    · apply List.eq_nil_iff_forall_not_mem.mpr
      intro z hz
      have ⟨hzb, hnotb⟩ := rFreeVars_rSubstMany_subset (fun b hb => (hbinds b hb).2.1) body z hz
      by_cases hmem_p : z ∈ patBoundNames p
      · rw [← hnames] at hmem_p
        rcases List.mem_map.mp hmem_p with ⟨b, hb, rfl⟩
        exact hnotb b hb rfl
      · have hz_arm : z ∈ (rFreeVars body).filter (fun w => !((patBoundNames p).contains w)) := by
          simp only [List.mem_filter]
          refine ⟨hzb, ?_⟩
          cases hc_pb : (patBoundNames p).contains z with
          | false => rfl
          | true => exact absurd (List.contains_iff_mem.mp hc_pb) hmem_p
        rw [hcl.2.1] at hz_arm
        cases hz_arm
    · intro l hl
      rcases rExprLocs_rSubstMany_subset _ body l hl with hb | ⟨b, hb, hlb⟩
      · exact hlocs l (List.mem_append.mpr (Or.inr (List.mem_append.mpr (Or.inl hb))))
      · exact hlocs l (List.mem_append.mpr (Or.inl ((hbinds b hb).2.2.2 l hlb)))
    · exact staticSyntaxWF_rSubstMany
        (fun b hb => (hbinds b hb).2.2.1)
        (fun b hb => noRegionSyntax_of_isRValue (hbinds b hb).1 (hbinds b hb).2.2.1)
        hsw.2.1
    · exact stackNewWF_rSubstMany enc
        (fun b hb => (hbinds b hb).1)
        (fun b hb => (hbinds b hb).2.1)
        (fun b hb => (hbinds b hb).2.2.1)
        hsn.2.1
    · intro r hr
      have hvf : ∀ b ∈ env, exprFrames b.2 = [] := fun b hb =>
        exprFrames_of_noRegionSyntax (noRegionSyntax_of_isRValue (hbinds b hb).1 (hbinds b hb).2.2.1)
      rw [exprFrames_rSubstMany hvf] at hr
      exact Or.inl (List.mem_append.mpr (Or.inr (List.mem_append.mpr (Or.inl hr))))
  | matchMiss _ _ =>
    simp only [rFreeVars, rFreeVarsArms, List.append_eq_nil_iff] at hcl
    simp only [staticSyntaxWF, staticSyntaxWFArms, Bool.and_eq_true] at hsw
    simp only [stackNewWF, stackNewWFArms, Bool.and_eq_true] at hsn
    refine ⟨hslots, by simp [rFreeVars, hcl.1, hcl.2.2], ?_,
      by simp [staticSyntaxWF, hsw.1, hsw.2.2],
      by simp [stackNewWF, hsn.1, hsn.2.2], ?_⟩
    · intro l hl
      rcases List.mem_append.mp hl with h1 | h2
      · exact hlocs l (List.mem_append.mpr (Or.inl h1))
      · exact hlocs l (List.mem_append.mpr (Or.inr (List.mem_append.mpr (Or.inr h2))))
    · intro r hr
      rcases List.mem_append.mp hr with h1 | h2
      · exact Or.inl (List.mem_append.mpr (Or.inl h1))
      · exact Or.inl (List.mem_append.mpr (Or.inr (List.mem_append.mpr (Or.inr h2))))
  | cellNewVal hv =>
    refine ⟨?_, rfl, ?_, rfl, rfl, (fun _ hm => nomatch hm)⟩
    · intro s' hs'
      rcases List.mem_append.mp hs' with hs_old | hs_new
      · exact slotValueWF_mono (by simp) (hslots s' hs_old)
      · rcases List.mem_singleton.mp hs_new with rfl
        refine ⟨hv, hcl, hsw, fun l hl => ?_⟩
        simp only [List.length_append, List.length_singleton]
        exact Nat.lt_succ_of_lt (hlocs l hl)
    · intro l hl
      rcases List.mem_singleton.mp hl with rfl
      simp
  | cellGetHeap hl =>
    rcases hslots _ (mem_of_getElem?_eq_some hl) with ⟨hv, hcl_v, hsw_v, hloc_v⟩
    have hnr_v := noRegionSyntax_of_isRValue hv hsw_v
    exact ⟨hslots, hcl_v, hloc_v, hsw_v, stackNewWF_of_noRegionSyntax enc hnr_v,
      fun r hr => by rw [exprFrames_of_noRegionSyntax hnr_v] at hr; cases hr⟩
  | cellGetStack hl =>
    rcases hslots _ (mem_of_getElem?_eq_some hl) with ⟨hv, hcl_v, hsw_v, hloc_v⟩
    have hnr_v := noRegionSyntax_of_isRValue hv hsw_v
    exact ⟨hslots, hcl_v, hloc_v, hsw_v, stackNewWF_of_noRegionSyntax enc hnr_v,
      fun r hr => by rw [exprFrames_of_noRegionSyntax hnr_v] at hr; cases hr⟩
  | @cellSetHeap _ _ _ _ _ _ hv =>
    simp only [rFreeVars, List.append_eq_nil_iff] at hcl
    simp only [staticSyntaxWF, Bool.and_eq_true] at hsw
    refine ⟨?_, rfl, (fun _ hm => nomatch hm), rfl, rfl, (fun _ hm => nomatch hm)⟩
    intro s' hs'
    simp only [List.length_set]
    rcases mem_set_subset hs' with rfl | hmem
    · exact ⟨hv, hcl.2, hsw.2, fun l hl => hlocs l (List.mem_append.mpr (Or.inr hl))⟩
    · exact hslots s' hmem
  | @cellSetStack _ _ _ _ _ _ _ hv =>
    simp only [rFreeVars, List.append_eq_nil_iff] at hcl
    simp only [staticSyntaxWF, Bool.and_eq_true] at hsw
    refine ⟨?_, rfl, (fun _ hm => nomatch hm), rfl, rfl, (fun _ hm => nomatch hm)⟩
    intro s' hs'
    simp only [List.length_set]
    rcases mem_set_subset hs' with rfl | hmem
    · exact ⟨hv, hcl.2, hsw.2, fun l hl => hlocs l (List.mem_append.mpr (Or.inr hl))⟩
    · exact hslots s' hmem
  | @frameVal rid0 _ _ _ hv =>
    have hnr_v := noRegionSyntax_of_isRValue hv hsw
    refine ⟨?_, hcl,
      fun l hl => by rw [length_popRegion]; exact hlocs l hl,
      hsw, stackNewWF_of_noRegionSyntax enc hnr_v,
      fun r hr => Or.inl (List.Mem.tail _ hr)⟩
    intro s' hs'
    rw [length_popRegion]
    rcases mem_popRegion hs' with ⟨s, hs, rfl⟩
    exact slotValueWF_popRegionSlot rid0 (hslots s hs)
  | @frameTrap rid0 _ _ _ =>
    refine ⟨?_, rfl, (fun _ hm => nomatch hm), rfl, rfl, (fun _ hm => nomatch hm)⟩
    intro s' hs'
    rw [length_popRegion]
    rcases mem_popRegion hs' with ⟨s, hs, rfl⟩
    exact slotValueWF_popRegionSlot rid0 (hslots s hs)
termination_by sizeOf re

theorem rstepList_core_box (Φ : FunEnv) (specs : List FnStackSpec) (es : List RExpr) :
    RStepListCoreBox Φ specs es := by
  refine ⟨fun enc {es' ρ ρ' n n'} henv hsl hslots hcl hlocs hsw hsn => ?_⟩
  cases hsl with
  | head hs =>
    have hev := ((rstep_evol_box Φ specs _).run hs).1
    simp only [rFreeVarsList, List.append_eq_nil_iff] at hcl
    simp only [staticSyntaxWFList, Bool.and_eq_true] at hsw
    simp only [stackNewWFList, Bool.and_eq_true] at hsn
    rcases (rstep_core_box Φ specs _).run enc henv hs hslots hcl.1
      (fun l hl => hlocs l (List.mem_append.mpr (Or.inl hl))) hsw.1 hsn.1 with
      ⟨hslots', hcl1', hlocs1', hsw1', hsn1', hfr1'⟩
    refine ⟨hslots', by simp [rFreeVarsList, hcl1', hcl.2], ?_,
      by simp [staticSyntaxWFList, hsw1', hsw.2],
      by simp [stackNewWFList, hsn1', hsn.2], ?_⟩
    · intro l hl
      rcases List.mem_append.mp hl with h1 | h2
      · exact hlocs1' l h1
      · exact Nat.lt_of_lt_of_le (hlocs l (List.mem_append.mpr (Or.inr h2))) hev.1
    · intro r hr
      rcases List.mem_append.mp hr with h1 | h2
      · exact (hfr1' r h1).imp (fun h => List.mem_append.mpr (Or.inl h)) id
      · exact Or.inl (List.mem_append.mpr (Or.inr h2))
  | tail _ hsl' =>
    have hev := ((rstepList_evol_box Φ specs _).run hsl').1
    simp only [rFreeVarsList, List.append_eq_nil_iff] at hcl
    simp only [staticSyntaxWFList, Bool.and_eq_true] at hsw
    simp only [stackNewWFList, Bool.and_eq_true] at hsn
    rcases (rstepList_core_box Φ specs _).run enc henv hsl' hslots hcl.2
      (fun l hl => hlocs l (List.mem_append.mpr (Or.inr hl))) hsw.2 hsn.2 with
      ⟨hslots', hcl2', hlocs2', hsw2', hsn2', hfr2'⟩
    refine ⟨hslots', by simp [rFreeVarsList, hcl.1, hcl2'], ?_,
      by simp [staticSyntaxWFList, hsw.1, hsw2'],
      by simp [stackNewWFList, hsn.1, hsn2'], ?_⟩
    · intro l hl
      rcases List.mem_append.mp hl with h1 | h2
      · exact Nat.lt_of_lt_of_le (hlocs l (List.mem_append.mpr (Or.inl h1))) hev.1
      · exact hlocs2' l h2
    · intro r hr
      rcases List.mem_append.mp hr with h1 | h2
      · exact Or.inl (List.mem_append.mpr (Or.inl h1))
      · exact (hfr2' r h2).imp (fun h => List.mem_append.mpr (Or.inr h)) id
termination_by sizeOf es
end

/-! ### Step Lemmas C & E: Frame Distinctness & Stack-Location Confinement (`RStepConfineBox`) -/

theorem contains_cons_eq (rid0 rid : RegionId) (enc : List RegionId) :
    (rid0 :: enc).contains rid = (enc.contains rid || (rid0 == rid)) := by
  cases h1 : enc.contains rid with
  | true =>
    simp only [Bool.true_or]
    exact List.contains_iff_mem.mpr (List.Mem.tail _ (List.contains_iff_mem.mp h1))
  | false =>
    simp only [Bool.false_or]
    cases h2 : (rid0 == rid) with
    | true =>
      have heq := beq_iff_eq.mp h2
      subst heq
      exact List.contains_iff_mem.mpr (List.Mem.head _)
    | false =>
      cases hc : (rid0 :: enc).contains rid with
      | false => rfl
      | true =>
        rcases List.mem_cons.mp (List.contains_iff_mem.mp hc) with rfl | hm
        · simp at h2
        · rw [List.contains_iff_mem.mpr hm] at h1; cases h1

theorem distinctList_step_left {xs xs' ys : List RegionId} {n n' : RegionId}
    (hdist : DistinctList (xs ++ ys))
    (hbnd : ∀ r ∈ xs ++ ys, r < n)
    (hd' : DistinctList xs')
    (hbnd' : ∀ r ∈ xs', r < n')
    (hsub' : ∀ r ∈ xs', r ∈ xs ∨ (n ≤ r ∧ r < n'))
    (hle : n ≤ n') :
    DistinctList (xs' ++ ys) ∧
    (∀ r ∈ xs' ++ ys, r < n') ∧
    (∀ rid, rid ∈ xs → rid ∉ xs' → rid ∈ xs ++ ys ∧ rid ∉ xs' ++ ys) := by
  rcases distinctList_append.mp hdist with ⟨_, hd_ys, hdisj⟩
  refine ⟨distinctList_append.mpr ⟨hd', hd_ys, fun r hr' hry => ?_⟩,
    fun r hr => ?_,
    fun rid h_in h_out => ⟨List.mem_append.mpr (Or.inl h_in), fun hm => ?_⟩⟩
  · rcases hsub' r hr' with hr_old | ⟨hn_le, _⟩
    · exact hdisj r hr_old hry
    · exact Nat.not_lt.mpr hn_le (hbnd r (List.mem_append.mpr (Or.inr hry)))
  · rcases List.mem_append.mp hr with h1 | h2
    · exact hbnd' r h1
    · exact Nat.lt_of_lt_of_le (hbnd r (List.mem_append.mpr (Or.inr h2))) hle
  · rcases List.mem_append.mp hm with h1 | h2
    · exact h_out h1
    · exact hdisj rid h_in h2

theorem distinctList_step_right {xs ys ys' : List RegionId} {n n' : RegionId}
    (hdist : DistinctList (xs ++ ys))
    (hbnd : ∀ r ∈ xs ++ ys, r < n)
    (hd' : DistinctList ys')
    (hbnd' : ∀ r ∈ ys', r < n')
    (hsub' : ∀ r ∈ ys', r ∈ ys ∨ (n ≤ r ∧ r < n'))
    (hle : n ≤ n') :
    DistinctList (xs ++ ys') ∧
    (∀ r ∈ xs ++ ys', r < n') ∧
    (∀ rid, rid ∈ ys → rid ∉ ys' → rid ∈ xs ++ ys ∧ rid ∉ xs ++ ys') := by
  rcases distinctList_append.mp hdist with ⟨hd_xs, _, hdisj⟩
  refine ⟨distinctList_append.mpr ⟨hd_xs, hd', fun r hrx hr' => ?_⟩,
    fun r hr => ?_,
    fun rid h_in h_out => ⟨List.mem_append.mpr (Or.inr h_in), fun hm => ?_⟩⟩
  · rcases hsub' r hr' with hr_old | ⟨hn_le, _⟩
    · exact hdisj r hrx hr_old
    · exact Nat.not_lt.mpr hn_le (hbnd r (List.mem_append.mpr (Or.inl hrx)))
  · rcases List.mem_append.mp hr with h1 | h2
    · exact Nat.lt_of_lt_of_le (hbnd r (List.mem_append.mpr (Or.inl h1))) hle
    · exact hbnd' r h2
  · rcases List.mem_append.mp hm with h1 | h2
    · exact hdisj rid h1 h_in
    · exact h_out h2

theorem distinctList_sublist_drop {xs ys : List RegionId} {n : RegionId}
    (hdist : DistinctList (xs ++ ys))
    (hbnd : ∀ r ∈ xs ++ ys, r < n) :
    (DistinctList xs ∧ ∀ r ∈ xs, r < n) ∧ (DistinctList ys ∧ ∀ r ∈ ys, r < n) := by
  rcases distinctList_append.mp hdist with ⟨hdx, hdy, _⟩
  exact ⟨⟨hdx, fun r hr => hbnd r (List.mem_append.mpr (Or.inl hr))⟩,
         ⟨hdy, fun r hr => hbnd r (List.mem_append.mpr (Or.inr hr))⟩⟩

theorem rstep_not_loc {Φ : FunEnv} {specs : List FnStackSpec} {l : Loc}
    {re' : RExpr} {ρ ρ' : RStore} {n n' : RegionId}
    (hs : RStep Φ specs (.loc l) ρ n re' ρ' n') : False := by
  cases hs

structure RStepConfineBox (Φ : FunEnv) (specs : List FnStackSpec) (re : RExpr) : Prop where
  run : ∀ (enc : List RegionId) {re' : RExpr} {ρ ρ' : RStore} {n n' : RegionId},
    EnvEscapeWF Φ specs →
    RStep Φ specs re ρ n re' ρ' n' →
    (∀ s ∈ ρ, SlotValueWF ρ.length s) →
    rFreeVars re = [] →
    (∀ l ∈ rExprLocs re, l < ρ.length) →
    staticSyntaxWF re = true →
    stackNewWF enc re = true →
    (DistinctList (exprFrames re) →
      (∀ r ∈ exprFrames re, r < n) →
      DistinctList (exprFrames re') ∧
      (∀ r ∈ exprFrames re', r < n') ∧
      (∀ (l : Loc) (rid : RegionId) (rv : RExpr) (r' : RegionId),
        ρ[l]? = some (.stackLive rid rv) → ρ'[l]? = some (.stackFreed r') →
        rid ∈ exprFrames re ∧ rid ∉ exprFrames re')) ∧
    (∀ (l : Loc) (rid : RegionId),
      l < ρ.length → (∀ s ∈ ρ, l ∉ slotLocs s) →
      locConfined l rid (enc.contains rid) re = true →
      locConfined l rid (enc.contains rid) re' = true ∧ (∀ s' ∈ ρ', l ∉ slotLocs s')) ∧
    (∀ (l : Loc) (rid : RegionId) (rv' : RExpr),
      ρ.length ≤ l → ρ'[l]? = some (.stackLive rid rv') →
      locConfined l rid (enc.contains rid) re' = true ∧ (∀ s' ∈ ρ', l ∉ slotLocs s'))

structure RStepListConfineBox (Φ : FunEnv) (specs : List FnStackSpec)
    (es : List RExpr) : Prop where
  run : ∀ (enc : List RegionId) {es' : List RExpr} {ρ ρ' : RStore} {n n' : RegionId},
    EnvEscapeWF Φ specs →
    RStepList Φ specs es ρ n es' ρ' n' →
    (∀ s ∈ ρ, SlotValueWF ρ.length s) →
    rFreeVarsList es = [] →
    (∀ l ∈ rExprLocsList es, l < ρ.length) →
    staticSyntaxWFList es = true →
    stackNewWFList enc es = true →
    (DistinctList (exprFramesList es) →
      (∀ r ∈ exprFramesList es, r < n) →
      DistinctList (exprFramesList es') ∧
      (∀ r ∈ exprFramesList es', r < n') ∧
      (∀ (l : Loc) (rid : RegionId) (rv : RExpr) (r' : RegionId),
        ρ[l]? = some (.stackLive rid rv) → ρ'[l]? = some (.stackFreed r') →
        rid ∈ exprFramesList es ∧ rid ∉ exprFramesList es')) ∧
    (∀ (l : Loc) (rid : RegionId),
      l < ρ.length → (∀ s ∈ ρ, l ∉ slotLocs s) →
      locConfinedList l rid (enc.contains rid) es = true →
      locConfinedList l rid (enc.contains rid) es' = true ∧ (∀ s' ∈ ρ', l ∉ slotLocs s')) ∧
    (∀ (l : Loc) (rid : RegionId) (rv' : RExpr),
      ρ.length ≤ l → ρ'[l]? = some (.stackLive rid rv') →
      locConfinedList l rid (enc.contains rid) es' = true ∧ (∀ s' ∈ ρ', l ∉ slotLocs s'))

theorem refl_no_pop {ρ : RStore} {l : Loc} {rid : RegionId} {rv : RExpr} {r' : RegionId}
    (h1 : ρ[l]? = some (.stackLive rid rv)) (h2 : ρ[l]? = some (.stackFreed r')) : False := by
  rw [h1] at h2; cases h2

theorem refl_no_alloc {ρ : RStore} {l : Loc} {rid : RegionId} {rv' : RExpr}
    (hle : ρ.length ≤ l) (h2 : ρ[l]? = some (.stackLive rid rv')) : False :=
  Nat.not_lt.mpr hle (lt_length_of_getElem?_eq_some h2)

mutual
theorem rstep_confine_box (Φ : FunEnv) (specs : List FnStackSpec) (re : RExpr) :
    RStepConfineBox Φ specs re := by
  refine ⟨fun enc {re' ρ ρ' n n'} henv hstep hslots hcl hlocs hsw hsn => ?_⟩
  cases hstep with
  | stackCellNewStep _ | stackCellNewTrap | stackCellNewVal _ =>
    simp [stackNewWF] at hsn
  | tupleTrap _ | blockEmpty | blockConsTrap | applyFnTrap | applyArgsTrap _ _
  | applyDirTrap _ | unTrap | unVal _ | binLeftTrap | binAndFalse | binOrTrue
  | binRightTrap _ _ _ | binVal _ | binTrap _ | letTrap | ifTrap
  | matchScrutTrap | matchEmpty _ | makeDataTrap _ | getTagTrap | getTagVal _
  | cellNewTrap | cellGetTrap | cellSetLeftTrap | cellSetRightTrap _
  | spawnTrap | awaitTrap | concPrimTrap _ =>
    exact ⟨fun _ _ => ⟨.nil, (fun _ hm => nomatch hm),
      fun _ _ _ _ h1 h2 => False.elim (refl_no_pop h1 h2)⟩,
      fun _ _ _ hslot _ => ⟨rfl, hslot⟩,
      fun _ _ _ hle h2 => False.elim (refl_no_alloc hle h2)⟩
  | tupleStep hsl | makeDataStep hsl | applyDirArgs hsl | concPrimArgs hsl =>
    exact (rstepList_confine_box Φ specs _).run enc henv hsl hslots hcl hlocs hsw hsn
  | blockSingle =>
    exact ⟨fun hd hb => ⟨by simp only [exprFrames, exprFramesList, List.append_nil] at hd; exact hd,
      fun r hr => hb r (by simp [exprFrames, exprFramesList, hr]),
      fun _ _ _ _ h1 h2 => False.elim (refl_no_pop h1 h2)⟩,
      fun _ _ _ hslot hc =>
        ⟨by simp only [locConfined, locConfinedList, Bool.and_true] at hc; exact hc, hslot⟩,
      fun _ _ _ hle h2 => False.elim (refl_no_alloc hle h2)⟩
  | @blockConsStep e1 e1' e2 es _ _ _ _ hs =>
    have hev := ((rstep_evol_box Φ specs e1).run hs).1
    simp only [rFreeVars, rFreeVarsList, List.append_eq_nil_iff] at hcl
    simp only [staticSyntaxWF, staticSyntaxWFList, Bool.and_eq_true] at hsw
    simp only [stackNewWF, stackNewWFList, Bool.and_eq_true] at hsn
    have hcore1 := (rstep_core_box Φ specs e1).run enc henv hs hslots hcl.1
      (fun l hl => hlocs l (List.mem_append.mpr (Or.inl hl))) hsw.1 hsn.1
    rcases (rstep_confine_box Φ specs e1).run enc henv hs hslots hcl.1
      (fun l hl => hlocs l (List.mem_append.mpr (Or.inl hl))) hsw.1 hsn.1 with
      ⟨hfr1, hlive1, hnew1⟩
    refine ⟨fun hd hb => ?_, fun l rid hlt hslot hc => ?_, fun l rid rv' hle hnew => ?_⟩
    · rcases distinctList_append.mp hd with ⟨hd1, _, _⟩
      have hb1 : ∀ r ∈ exprFrames e1, r < n :=
        fun r hr => hb r (List.mem_append.mpr (Or.inl hr))
      rcases hfr1 hd1 hb1 with ⟨hd1', hb1', hpop1⟩
      rcases distinctList_step_left hd hb hd1' hb1' hcore1.2.2.2.2.2 hev.2.1 with
        ⟨hd_out, hb_out, hpop_out⟩
      exact ⟨hd_out, hb_out, fun l rid rv r' h1 h2 =>
        hpop_out rid (hpop1 l rid rv r' h1 h2).1 (hpop1 l rid rv r' h1 h2).2⟩
    · simp only [locConfined, locConfinedList, Bool.and_eq_true] at hc ⊢
      rcases hlive1 l rid hlt hslot hc.1 with ⟨hc1', hslot'⟩
      exact ⟨⟨hc1', hc.2⟩, hslot'⟩
    · rcases hnew1 l rid rv' hle hnew with ⟨hc1', hslot'⟩
      have hnl_rest : l ∉ rExprLocsList (e2 :: es) := fun hm =>
        Nat.not_lt.mpr hle (hlocs l (List.mem_append.mpr (Or.inr hm)))
      simp only [locConfined, locConfinedList, Bool.and_eq_true]
      exact ⟨⟨hc1', (Bool.and_eq_true _ _).mp
        (locConfinedList_of_not_mem_locs l rid (enc.contains rid) (e2 :: es) hnl_rest)⟩, hslot'⟩
  | blockConsVal _ =>
    exact ⟨fun hd hb => ⟨(distinctList_sublist_drop hd hb).2.1,
      (distinctList_sublist_drop hd hb).2.2,
      fun _ _ _ _ h1 h2 => False.elim (refl_no_pop h1 h2)⟩,
      fun _ _ _ hslot hc =>
        ⟨by simp only [locConfined, locConfinedList, Bool.and_eq_true] at hc ⊢; exact hc.2, hslot⟩,
      fun _ _ _ hle h2 => False.elim (refl_no_alloc hle h2)⟩
  | @applyFn fn fn' args _ _ _ _ hs =>
    have hev := ((rstep_evol_box Φ specs fn).run hs).1
    simp only [rFreeVars, List.append_eq_nil_iff] at hcl
    simp only [staticSyntaxWF, Bool.and_eq_true] at hsw
    simp only [stackNewWF, Bool.and_eq_true] at hsn
    have hcore1 := (rstep_core_box Φ specs fn).run enc henv hs hslots hcl.1
      (fun l hl => hlocs l (List.mem_append.mpr (Or.inl hl))) hsw.1 hsn.1
    rcases (rstep_confine_box Φ specs fn).run enc henv hs hslots hcl.1
      (fun l hl => hlocs l (List.mem_append.mpr (Or.inl hl))) hsw.1 hsn.1 with
      ⟨hfr1, hlive1, hnew1⟩
    refine ⟨fun hd hb => ?_, fun l rid hlt hslot hc => ?_, fun l rid rv' hle hnew => ?_⟩
    · rcases distinctList_append.mp hd with ⟨hd1, _, _⟩
      have hb1 : ∀ r ∈ exprFrames fn, r < n :=
        fun r hr => hb r (List.mem_append.mpr (Or.inl hr))
      rcases hfr1 hd1 hb1 with ⟨hd1', hb1', hpop1⟩
      rcases distinctList_step_left hd hb hd1' hb1' hcore1.2.2.2.2.2 hev.2.1 with
        ⟨hd_out, hb_out, hpop_out⟩
      exact ⟨hd_out, hb_out, fun l rid rv r' h1 h2 =>
        hpop_out rid (hpop1 l rid rv r' h1 h2).1 (hpop1 l rid rv r' h1 h2).2⟩
    · simp only [locConfined, Bool.and_eq_true] at hc ⊢
      rcases hlive1 l rid hlt hslot hc.1 with ⟨hc1', hslot'⟩
      exact ⟨⟨hc1', hc.2⟩, hslot'⟩
    · rcases hnew1 l rid rv' hle hnew with ⟨hc1', hslot'⟩
      have hnl2 : l ∉ rExprLocsList args := fun hm =>
        Nat.not_lt.mpr hle (hlocs l (List.mem_append.mpr (Or.inr hm)))
      have hc2' := locConfinedList_of_not_mem_locs l rid (enc.contains rid) args hnl2
      simp only [locConfined, Bool.and_eq_true]
      exact ⟨⟨hc1', hc2'⟩, hslot'⟩
  | @applyArgs fn args args' _ _ _ _ _ hsl =>
    have hev := ((rstepList_evol_box Φ specs args).run hsl).1
    simp only [rFreeVars, List.append_eq_nil_iff] at hcl
    simp only [staticSyntaxWF, Bool.and_eq_true] at hsw
    simp only [stackNewWF, Bool.and_eq_true] at hsn
    have hcore2 := (rstepList_core_box Φ specs args).run enc henv hsl hslots hcl.2
      (fun l hl => hlocs l (List.mem_append.mpr (Or.inr hl))) hsw.2 hsn.2
    rcases (rstepList_confine_box Φ specs args).run enc henv hsl hslots hcl.2
      (fun l hl => hlocs l (List.mem_append.mpr (Or.inr hl))) hsw.2 hsn.2 with
      ⟨hfr2, hlive2, hnew2⟩
    refine ⟨fun hd hb => ?_, fun l rid hlt hslot hc => ?_, fun l rid rv' hle hnew => ?_⟩
    · rcases distinctList_append.mp hd with ⟨_, hd2, _⟩
      have hb2 : ∀ r ∈ exprFramesList args, r < n :=
        fun r hr => hb r (List.mem_append.mpr (Or.inr hr))
      rcases hfr2 hd2 hb2 with ⟨hd2', hb2', hpop2⟩
      rcases distinctList_step_right hd hb hd2' hb2' hcore2.2.2.2.2.2 hev.2.1 with
        ⟨hd_out, hb_out, hpop_out⟩
      exact ⟨hd_out, hb_out, fun l rid rv r' h1 h2 =>
        hpop_out rid (hpop2 l rid rv r' h1 h2).1 (hpop2 l rid rv r' h1 h2).2⟩
    · simp only [locConfined, Bool.and_eq_true] at hc ⊢
      rcases hlive2 l rid hlt hslot hc.2 with ⟨hc2', hslot'⟩
      exact ⟨⟨hc.1, hc2'⟩, hslot'⟩
    · rcases hnew2 l rid rv' hle hnew with ⟨hc2', hslot'⟩
      have hnl1 : l ∉ rExprLocs fn := fun hm =>
        Nat.not_lt.mpr hle (hlocs l (List.mem_append.mpr (Or.inl hm)))
      have hc1' := locConfined_of_not_mem_locs l rid (enc.contains rid) fn hnl1
      simp only [locConfined, Bool.and_eq_true]
      exact ⟨⟨hc1', hc2'⟩, hslot'⟩
  | @applyBeta m ps ret body args _ _ hvals _ =>
    simp only [rFreeVars, List.append_eq_nil_iff] at hcl
    simp only [staticSyntaxWF, Bool.and_eq_true] at hsw
    have hbs : ∀ b ∈ rZipParams ps args,
        IsRValue b.2 ∧ rFreeVars b.2 = [] ∧ exprFrames b.2 = [] ∧
          (∀ l rid inReg, locConfinedList l rid inReg args = true → l ∉ rExprLocs b.2) := by
      intro b hb
      rcases mem_args_wf (mem_zip_snd hb) hvals hcl.2 hsw.2 with
        ⟨hv, hc, _, _, hf, _, hconf⟩
      exact ⟨hv, hc, hf, hconf⟩
    have hf_sub : exprFrames (rSubstMany (rZipParams ps args) body) = [] := by
      rw [exprFrames_rSubstMany (fun b hb => (hbs b hb).2.2.1),
          exprFrames_of_noRegionSyntax hsw.1]
    refine ⟨fun _ _ => ⟨hf_sub ▸ .nil,
      (fun r hr => by rw [hf_sub] at hr; cases hr),
      fun _ _ _ _ h1 h2 => False.elim (refl_no_pop h1 h2)⟩,
      fun l rid _ hslot hc => ⟨?_, hslot⟩,
      fun _ _ _ hle h2 => False.elim (refl_no_alloc hle h2)⟩
    simp only [locConfined, Bool.and_eq_true] at hc
    have hnl_body : l ∉ rExprLocs body := by
      apply not_mem_locs_of_locConfined_false body hc.1
      rw [exprFrames_of_noRegionSyntax hsw.1]
      intro hm; cases hm
    exact locConfined_rSubstMany_other l rid (enc.contains rid)
      (fun b hb => (hbs b hb).1)
      (fun b hb => (hbs b hb).2.1)
      (fun b hb => (hbs b hb).2.2.2 l rid (enc.contains rid) hc.2)
      (locConfined_of_not_mem_locs l rid (enc.contains rid) body hnl_body)
  | @applyDirBeta name fd args ρ n hfd hvals _ =>
    have ⟨hnolocs, _, _⟩ := henv name fd hfd
    have hbs : ∀ b ∈ rZipParams fd.params args,
        IsRValue b.2 ∧ rFreeVars b.2 = [] ∧ exprFrames b.2 = [] ∧
          (∀ l rid inReg, locConfinedList l rid inReg args = true → l ∉ rExprLocs b.2) := by
      intro b hb
      rcases mem_args_wf (mem_zip_snd hb) hvals hcl hsw with
        ⟨hv, hc, _, _, hf, _, hconf⟩
      exact ⟨hv, hc, hf, hconf⟩
    have hf_ce :
        exprFrames (rSubstMany (rZipParams fd.params args)
          (compileExpr (lookupStackVars specs name) n fd.body)) = [] := by
      rw [exprFrames_rSubstMany (fun b hb => (hbs b hb).2.2.1), exprFrames_compileExpr]
    refine ⟨fun _ _ => ⟨by simp only [exprFrames, hf_ce]; exact .cons (fun hm => nomatch hm) .nil,
      (fun r hr => by
        simp only [exprFrames, hf_ce, List.mem_singleton] at hr
        rw [hr]; exact Nat.lt_succ_self n),
      fun _ _ _ _ h1 h2 => False.elim (refl_no_pop h1 h2)⟩,
      fun l rid _ hslot hc => ⟨?_, hslot⟩,
      fun _ _ _ hle h2 => False.elim (refl_no_alloc hle h2)⟩
    simp only [locConfined] at hc ⊢
    have hnl_ce : l ∉ rExprLocs (compileExpr (lookupStackVars specs name) n fd.body) := by
      rw [rExprLocs_compileExpr, List.isEmpty_iff.mp hnolocs]
      intro hm; cases hm
    exact locConfined_rSubstMany_other l rid (enc.contains rid || (n == rid))
      (fun b hb => (hbs b hb).1)
      (fun b hb => (hbs b hb).2.1)
      (fun b hb => (hbs b hb).2.2.2 l rid (enc.contains rid) hc)
      (locConfined_of_not_mem_locs l rid (enc.contains rid || (n == rid)) _ hnl_ce)
  | @unStep _ e1 e1' _ _ _ _ hs | @getTagStep e1 e1' _ _ _ _ hs | @cellNewStep e1 e1' _ _ _ _ hs
  | @spawnStep e1 e1' _ _ _ _ hs | @awaitStep e1 e1' _ _ _ _ hs =>
    exact (rstep_confine_box Φ specs e1).run enc (re' := e1') henv hs hslots hcl hlocs hsw hsn
  | @cellGetStep e1 e1' _ _ _ _ hs =>
    rcases (rstep_confine_box Φ specs e1).run enc (re' := e1') henv hs hslots hcl hlocs hsw hsn with
      ⟨hfr, hlive, hnew⟩
    refine ⟨hfr, fun l rid hlt hslot hc => ?_, fun l rid rv' hle hn => ?_⟩
    · simp only [locConfined] at hc ⊢
      have hloc_false : (rAsLoc? e1 == some l) = false := by
        cases hq : rAsLoc? e1 with
        | none => rfl
        | some l' =>
          have heq := rAsLoc?_eq_some.mp hq
          subst heq
          exact False.elim (rstep_not_loc hs)
      simp only [hloc_false, Bool.false_eq_true, ↓reduceIte] at hc
      rcases hlive l rid hlt hslot hc with ⟨hc1', hslot'⟩
      simp only [rAsLoc?_ne_of_locConfined hc1', Bool.false_eq_true, ↓reduceIte]
      exact ⟨hc1', hslot'⟩
    · rcases hnew l rid rv' hle hn with ⟨hc1', hslot'⟩
      simp only [locConfined, rAsLoc?_ne_of_locConfined hc1', Bool.false_eq_true, ↓reduceIte]
      exact ⟨hc1', hslot'⟩
  | @frameStep rid0 e1 e1' _ _ _ _ hs =>
    have hev := ((rstep_evol_box Φ specs e1).run hs).1
    have hcore1 := (rstep_core_box Φ specs e1).run (rid0 :: enc) henv hs hslots hcl hlocs hsw hsn
    rcases (rstep_confine_box Φ specs e1).run (rid0 :: enc) henv hs hslots hcl hlocs hsw hsn with
      ⟨hfr1, hlive1, hnew1⟩
    refine ⟨fun hd hb => ?_, fun l rid hlt hslot hc => ?_, fun l rid rv' hle hn => ?_⟩
    · cases hd with
      | cons hnot_rid0 hd1 =>
        have hb0 : rid0 < n := hb rid0 (List.Mem.head _)
        have hb1 : ∀ r ∈ exprFrames e1, r < n := fun r hr => hb r (List.Mem.tail _ hr)
        rcases hfr1 hd1 hb1 with ⟨hd1', hb1', hpop1⟩
        have hnot_rid0' : rid0 ∉ exprFrames e1' := by
          intro hm
          rcases hcore1.2.2.2.2.2 rid0 hm with h_old | ⟨hn_le, _⟩
          · exact hnot_rid0 h_old
          · exact Nat.not_lt.mpr hn_le hb0
        refine ⟨.cons hnot_rid0' hd1', ?_, ?_⟩
        · intro r hr
          rcases List.mem_cons.mp hr with rfl | hr'
          · exact Nat.lt_of_lt_of_le hb0 hev.2.1
          · exact hb1' r hr'
        · intro l rid rv r' h1 h2
          rcases hpop1 l rid rv r' h1 h2 with ⟨h_in1, h_out1⟩
          have hne_r : rid ≠ rid0 := fun heq => hnot_rid0 (heq ▸ h_in1)
          exact ⟨List.Mem.tail _ h_in1, fun hm => by
            rcases List.mem_cons.mp hm with rfl | hm'
            · exact hne_r rfl
            · exact h_out1 hm'⟩
    · simp only [locConfined] at hc ⊢
      rw [← contains_cons_eq rid0 rid enc] at hc ⊢
      exact hlive1 l rid hlt hslot hc
    · simp only [locConfined]
      rw [← contains_cons_eq rid0 rid enc]
      exact hnew1 l rid rv' hle hn
  | @binLeft _ e1 e1' e2 _ _ _ _ hs | @matchScrut e1 e1' e2 _ _ _ _ hs =>
    have hev := ((rstep_evol_box Φ specs e1).run hs).1
    simp only [rFreeVars, List.append_eq_nil_iff] at hcl
    simp only [staticSyntaxWF, Bool.and_eq_true] at hsw
    simp only [stackNewWF, Bool.and_eq_true] at hsn
    have hcore1 := (rstep_core_box Φ specs e1).run enc henv hs hslots hcl.1
      (fun l hl => hlocs l (List.mem_append.mpr (Or.inl hl))) hsw.1 hsn.1
    rcases (rstep_confine_box Φ specs e1).run enc henv hs hslots hcl.1
      (fun l hl => hlocs l (List.mem_append.mpr (Or.inl hl))) hsw.1 hsn.1 with
      ⟨hfr1, hlive1, hnew1⟩
    refine ⟨fun hd hb => ?_, fun l rid hlt hslot hc => ?_, fun l rid rv' hle hn => ?_⟩
    · rcases distinctList_append.mp hd with ⟨hd1, _, _⟩
      have hb1 : ∀ r ∈ exprFrames e1, r < n :=
        fun r hr => hb r (List.mem_append.mpr (Or.inl hr))
      rcases hfr1 hd1 hb1 with ⟨hd1', hb1', hpop1⟩
      rcases distinctList_step_left hd hb hd1' hb1' hcore1.2.2.2.2.2 hev.2.1 with
        ⟨hd_out, hb_out, hpop_out⟩
      exact ⟨hd_out, hb_out, fun l rid rv r' h1 h2 =>
        hpop_out rid (hpop1 l rid rv r' h1 h2).1 (hpop1 l rid rv r' h1 h2).2⟩
    · simp only [locConfined, Bool.and_eq_true] at hc ⊢
      rcases hlive1 l rid hlt hslot hc.1 with ⟨hc1', hslot'⟩
      exact ⟨⟨hc1', hc.2⟩, hslot'⟩
    · rcases hnew1 l rid rv' hle hn with ⟨hc1', hslot'⟩
      simp only [locConfined, Bool.and_eq_true]
      refine ⟨⟨hc1', ?_⟩, hslot'⟩
      first
      | exact locConfined_of_not_mem_locs l rid (enc.contains rid) e2
          (fun hm => Nat.not_lt.mpr hle (hlocs l (List.mem_append.mpr (Or.inr hm))))
      | exact locConfinedArms_of_not_mem_locs l rid (enc.contains rid) e2
          (fun hm => Nat.not_lt.mpr hle (hlocs l (List.mem_append.mpr (Or.inr hm))))
  | @cellSetLeft e1 e1' e2 _ _ _ _ hs =>
    have hev := ((rstep_evol_box Φ specs e1).run hs).1
    simp only [rFreeVars, List.append_eq_nil_iff] at hcl
    simp only [staticSyntaxWF, Bool.and_eq_true] at hsw
    simp only [stackNewWF, Bool.and_eq_true] at hsn
    have hcore1 := (rstep_core_box Φ specs e1).run enc henv hs hslots hcl.1
      (fun l hl => hlocs l (List.mem_append.mpr (Or.inl hl))) hsw.1 hsn.1
    rcases (rstep_confine_box Φ specs e1).run enc henv hs hslots hcl.1
      (fun l hl => hlocs l (List.mem_append.mpr (Or.inl hl))) hsw.1 hsn.1 with
      ⟨hfr1, hlive1, hnew1⟩
    refine ⟨fun hd hb => ?_, fun l rid hlt hslot hc => ?_, fun l rid rv' hle hn => ?_⟩
    · rcases distinctList_append.mp hd with ⟨hd1, _, _⟩
      have hb1 : ∀ r ∈ exprFrames e1, r < n :=
        fun r hr => hb r (List.mem_append.mpr (Or.inl hr))
      rcases hfr1 hd1 hb1 with ⟨hd1', hb1', hpop1⟩
      rcases distinctList_step_left hd hb hd1' hb1' hcore1.2.2.2.2.2 hev.2.1 with
        ⟨hd_out, hb_out, hpop_out⟩
      exact ⟨hd_out, hb_out, fun l rid rv r' h1 h2 =>
        hpop_out rid (hpop1 l rid rv r' h1 h2).1 (hpop1 l rid rv r' h1 h2).2⟩
    · simp only [locConfined] at hc ⊢
      have hloc_false : (rAsLoc? e1 == some l) = false := by
        cases hq : rAsLoc? e1 with
        | none => rfl
        | some l' =>
          have heq := rAsLoc?_eq_some.mp hq
          subst heq
          exact False.elim (rstep_not_loc hs)
      simp only [hloc_false, Bool.false_eq_true, ↓reduceIte, Bool.and_eq_true] at hc
      rcases hlive1 l rid hlt hslot hc.1 with ⟨hc1', hslot'⟩
      simp only [rAsLoc?_ne_of_locConfined hc1', Bool.false_eq_true, ↓reduceIte, Bool.and_eq_true]
      exact ⟨⟨hc1', hc.2⟩, hslot'⟩
    · rcases hnew1 l rid rv' hle hn with ⟨hc1', hslot'⟩
      have hc2' := locConfined_of_not_mem_locs l rid (enc.contains rid) e2
        (fun hm => Nat.not_lt.mpr hle (hlocs l (List.mem_append.mpr (Or.inr hm))))
      simp only [locConfined, rAsLoc?_ne_of_locConfined hc1', Bool.false_eq_true, ↓reduceIte,
        Bool.and_eq_true]
      exact ⟨⟨hc1', hc2'⟩, hslot'⟩
  | @binRight _ v1 e2 e2' _ _ _ _ _ _ _ hs =>
    have hev := ((rstep_evol_box Φ specs e2).run hs).1
    simp only [rFreeVars, List.append_eq_nil_iff] at hcl
    simp only [staticSyntaxWF, Bool.and_eq_true] at hsw
    simp only [stackNewWF, Bool.and_eq_true] at hsn
    have hcore2 := (rstep_core_box Φ specs e2).run enc henv hs hslots hcl.2
      (fun l hl => hlocs l (List.mem_append.mpr (Or.inr hl))) hsw.2 hsn.2
    rcases (rstep_confine_box Φ specs e2).run enc henv hs hslots hcl.2
      (fun l hl => hlocs l (List.mem_append.mpr (Or.inr hl))) hsw.2 hsn.2 with
      ⟨hfr2, hlive2, hnew2⟩
    refine ⟨fun hd hb => ?_, fun l rid hlt hslot hc => ?_, fun l rid rv' hle hn => ?_⟩
    · rcases distinctList_append.mp hd with ⟨_, hd2, _⟩
      have hb2 : ∀ r ∈ exprFrames e2, r < n :=
        fun r hr => hb r (List.mem_append.mpr (Or.inr hr))
      rcases hfr2 hd2 hb2 with ⟨hd2', hb2', hpop2⟩
      rcases distinctList_step_right hd hb hd2' hb2' hcore2.2.2.2.2.2 hev.2.1 with
        ⟨hd_out, hb_out, hpop_out⟩
      exact ⟨hd_out, hb_out, fun l rid rv r' h1 h2 =>
        hpop_out rid (hpop2 l rid rv r' h1 h2).1 (hpop2 l rid rv r' h1 h2).2⟩
    · simp only [locConfined, Bool.and_eq_true] at hc ⊢
      rcases hlive2 l rid hlt hslot hc.2 with ⟨hc2', hslot'⟩
      exact ⟨⟨hc.1, hc2'⟩, hslot'⟩
    · rcases hnew2 l rid rv' hle hn with ⟨hc2', hslot'⟩
      have hc1' := locConfined_of_not_mem_locs l rid (enc.contains rid) v1
        (fun hm => Nat.not_lt.mpr hle (hlocs l (List.mem_append.mpr (Or.inl hm))))
      simp only [locConfined, Bool.and_eq_true]
      exact ⟨⟨hc1', hc2'⟩, hslot'⟩
  | @cellSetRight v1 e2 e2' _ _ _ _ _ hs =>
    have hev := ((rstep_evol_box Φ specs e2).run hs).1
    simp only [rFreeVars, List.append_eq_nil_iff] at hcl
    simp only [staticSyntaxWF, Bool.and_eq_true] at hsw
    simp only [stackNewWF, Bool.and_eq_true] at hsn
    have hcore2 := (rstep_core_box Φ specs e2).run enc henv hs hslots hcl.2
      (fun l hl => hlocs l (List.mem_append.mpr (Or.inr hl))) hsw.2 hsn.2
    rcases (rstep_confine_box Φ specs e2).run enc henv hs hslots hcl.2
      (fun l hl => hlocs l (List.mem_append.mpr (Or.inr hl))) hsw.2 hsn.2 with
      ⟨hfr2, hlive2, hnew2⟩
    refine ⟨fun hd hb => ?_, fun l rid hlt hslot hc => ?_, fun l rid rv' hle hn => ?_⟩
    · rcases distinctList_append.mp hd with ⟨_, hd2, _⟩
      have hb2 : ∀ r ∈ exprFrames e2, r < n :=
        fun r hr => hb r (List.mem_append.mpr (Or.inr hr))
      rcases hfr2 hd2 hb2 with ⟨hd2', hb2', hpop2⟩
      rcases distinctList_step_right hd hb hd2' hb2' hcore2.2.2.2.2.2 hev.2.1 with
        ⟨hd_out, hb_out, hpop_out⟩
      exact ⟨hd_out, hb_out, fun l rid rv r' h1 h2 =>
        hpop_out rid (hpop2 l rid rv r' h1 h2).1 (hpop2 l rid rv r' h1 h2).2⟩
    · simp only [locConfined] at hc ⊢
      cases hloc : (rAsLoc? v1 == some l) with
      | true =>
        simp only [hloc, ↓reduceIte, Bool.and_eq_true] at hc ⊢
        rcases hlive2 l rid hlt hslot hc.2 with ⟨hc2', hslot'⟩
        exact ⟨⟨hc.1, hc2'⟩, hslot'⟩
      | false =>
        simp only [hloc, Bool.false_eq_true, ↓reduceIte, Bool.and_eq_true] at hc ⊢
        rcases hlive2 l rid hlt hslot hc.2 with ⟨hc2', hslot'⟩
        exact ⟨⟨hc.1, hc2'⟩, hslot'⟩
    · rcases hnew2 l rid rv' hle hn with ⟨hc2', hslot'⟩
      have hc1' := locConfined_of_not_mem_locs l rid (enc.contains rid) v1
        (fun hm => Nat.not_lt.mpr hle (hlocs l (List.mem_append.mpr (Or.inl hm))))
      simp only [locConfined, rAsLoc?_ne_of_locConfined hc1', Bool.false_eq_true, ↓reduceIte,
        Bool.and_eq_true]
      exact ⟨⟨hc1', hc2'⟩, hslot'⟩
  | binAndTrue | binOrFalse =>
    exact ⟨fun hd hb => ⟨(distinctList_sublist_drop hd hb).2.1,
      (distinctList_sublist_drop hd hb).2.2,
      fun _ _ _ _ h1 h2 => False.elim (refl_no_pop h1 h2)⟩,
      fun _ _ _ hslot hc => ⟨by simp only [locConfined, Bool.and_eq_true] at hc; exact hc.2, hslot⟩,
      fun _ _ _ hle h2 => False.elim (refl_no_alloc hle h2)⟩
  | @letStep x e1 e1' e2 _ _ _ _ hs =>
    have hev := ((rstep_evol_box Φ specs e1).run hs).1
    simp only [rFreeVars, List.append_eq_nil_iff] at hcl
    simp only [staticSyntaxWF, Bool.and_eq_true] at hsw
    cases hsc : asStackCellNew? e1 with
    | none =>
      rw [stackNewWF_let_nonStackCellNew enc x e1 e2 hsc, Bool.and_eq_true] at hsn
      have hcore1 := (rstep_core_box Φ specs e1).run enc henv hs hslots hcl.1
        (fun l hl => hlocs l (List.mem_append.mpr (Or.inl hl))) hsw.1 hsn.1
      rcases (rstep_confine_box Φ specs e1).run enc henv hs hslots hcl.1
        (fun l hl => hlocs l (List.mem_append.mpr (Or.inl hl))) hsw.1 hsn.1 with
        ⟨hfr1, hlive1, hnew1⟩
      refine ⟨fun hd hb => ?_, fun l rid hlt hslot hc => ?_, fun l rid rv' hle hn => ?_⟩
      · rcases distinctList_append.mp hd with ⟨hd1, _, _⟩
        have hb1 : ∀ r ∈ exprFrames e1, r < n :=
          fun r hr => hb r (List.mem_append.mpr (Or.inl hr))
        rcases hfr1 hd1 hb1 with ⟨hd1', hb1', hpop1⟩
        rcases distinctList_step_left hd hb hd1' hb1' hcore1.2.2.2.2.2 hev.2.1 with
          ⟨hd_out, hb_out, hpop_out⟩
        exact ⟨hd_out, hb_out, fun l rid rv r' h1 h2 =>
          hpop_out rid (hpop1 l rid rv r' h1 h2).1 (hpop1 l rid rv r' h1 h2).2⟩
      · simp only [locConfined] at hc ⊢
        have hloc_false : (rAsLoc? e1 == some l) = false := by
          cases hq : rAsLoc? e1 with
          | none => rfl
          | some l' =>
            have heq := rAsLoc?_eq_some.mp hq
            subst heq
            exact False.elim (rstep_not_loc hs)
        simp only [hloc_false, Bool.false_eq_true, ↓reduceIte, Bool.and_eq_true] at hc
        rcases hlive1 l rid hlt hslot hc.1 with ⟨hc1', hslot'⟩
        simp only [rAsLoc?_ne_of_locConfined hc1', Bool.false_eq_true, ↓reduceIte, Bool.and_eq_true]
        exact ⟨⟨hc1', hc.2⟩, hslot'⟩
      · rcases hnew1 l rid rv' hle hn with ⟨hc1', hslot'⟩
        have hc2' := locConfined_of_not_mem_locs l rid (enc.contains rid) e2
          (fun hm => Nat.not_lt.mpr hle (hlocs l (List.mem_append.mpr (Or.inr hm))))
        simp only [locConfined, rAsLoc?_ne_of_locConfined hc1', Bool.false_eq_true, ↓reduceIte,
          Bool.and_eq_true]
        exact ⟨⟨hc1', hc2'⟩, hslot'⟩
    | some p =>
      cases p with
      | mk rid0 init =>
        have he1 := asStackCellNew?_eq_some.mp hsc
        subst he1
        simp only [stackNewWF, Bool.and_eq_true] at hsn
        cases hs with
        | @stackCellNewStep _ _ init' _ _ _ _ hs_init =>
          have hcore1 := (rstep_core_box Φ specs init).run enc (re' := init') henv hs_init hslots hcl.1
            (fun l hl => hlocs l (List.mem_append.mpr (Or.inl hl))) hsw.1 hsn.1.1.2
          rcases (rstep_confine_box Φ specs init).run enc (re' := init') henv hs_init hslots hcl.1
            (fun l hl => hlocs l (List.mem_append.mpr (Or.inl hl))) hsw.1 hsn.1.1.2 with
            ⟨hfr1, hlive1, hnew1⟩
          refine ⟨fun hd hb => ?_, fun l rid hlt hslot hc => ?_, fun l rid rv' hle hn => ?_⟩
          · rcases distinctList_append.mp hd with ⟨hd1, _, _⟩
            have hb1 : ∀ r ∈ exprFrames init, r < n :=
              fun r hr => hb r (List.mem_append.mpr (Or.inl hr))
            rcases hfr1 hd1 hb1 with ⟨hd1', hb1', hpop1⟩
            rcases distinctList_step_left hd hb hd1' hb1' hcore1.2.2.2.2.2 hev.2.1 with
              ⟨hd_out, hb_out, hpop_out⟩
            exact ⟨hd_out, hb_out, fun l rid rv r' h1 h2 =>
              hpop_out rid (hpop1 l rid rv r' h1 h2).1 (hpop1 l rid rv r' h1 h2).2⟩
          · have hnone1 : (rAsLoc? (.stackCellNew rid0 init) == some l) = false := rfl
            have hnone2 : (rAsLoc? (.stackCellNew rid0 init') == some l) = false := rfl
            simp only [locConfined, hnone1, hnone2, Bool.false_eq_true, ↓reduceIte,
              Bool.and_eq_true] at hc ⊢
            rcases hlive1 l rid hlt hslot hc.1 with ⟨hc1', hslot'⟩
            exact ⟨⟨hc1', hc.2⟩, hslot'⟩
          · rcases hnew1 l rid rv' hle hn with ⟨hc1', hslot'⟩
            have hc2' := locConfined_of_not_mem_locs l rid (enc.contains rid) e2
              (fun hm => Nat.not_lt.mpr hle (hlocs l (List.mem_append.mpr (Or.inr hm))))
            have hnone2 : (rAsLoc? (.stackCellNew rid0 init') == some l) = false := rfl
            simp only [locConfined, hnone2, Bool.false_eq_true, ↓reduceIte, Bool.and_eq_true]
            exact ⟨⟨hc1', hc2'⟩, hslot'⟩
        | @stackCellNewTrap _ tr _ _ =>
          exact ⟨fun hd hb => ⟨(distinctList_sublist_drop hd hb).2.1,
            (distinctList_sublist_drop hd hb).2.2,
            fun _ _ _ _ h1 h2 => False.elim (refl_no_pop h1 h2)⟩,
            fun l rid _ hslot hc => ⟨by
              have hnone1 : (rAsLoc? (.stackCellNew rid0 (.trap tr)) == some l) = false := rfl
              have hnone2 : (rAsLoc? (.trap tr) == some l) = false := rfl
              simp only [locConfined, hnone1, hnone2, Bool.false_eq_true, ↓reduceIte,
                Bool.true_and] at hc ⊢
              exact hc, hslot⟩,
            fun _ _ _ hle h2 => False.elim (refl_no_alloc hle h2)⟩
        | stackCellNewVal hv =>
          refine ⟨fun hd hb => ⟨by
              have hf0 : exprFrames init = [] :=
                exprFrames_of_noRegionSyntax (noRegionSyntax_of_isRValue hv hsw.1)
              simp only [exprFrames, hf0, List.nil_append] at hd ⊢
              exact hd,
            fun r hr => hb r (List.mem_append.mpr (Or.inr hr)),
            fun l rid rv r' h1 h2 => by
              rw [getElem?_append_lt (lt_length_of_getElem?_eq_some h1), h1] at h2
              cases h2⟩,
            fun l rid hlt hslot hc => ?_,
            fun l rid rv' hle hn => ?_⟩
          · have hnone1 : (rAsLoc? (.stackCellNew rid0 init) == some l) = false := rfl
            simp only [locConfined, hnone1, Bool.false_eq_true, ↓reduceIte, Bool.and_eq_true] at hc
            have hnl_init : l ∉ rExprLocs init :=
              not_mem_locs_of_isRValue_locConfined hv hsw.1 hc.1
            have hne_len : (rAsLoc? (.loc ρ.length) == some l) = false := by
              simp only [rAsLoc?, beq_eq_false_iff_ne, ne_eq, Option.some.injEq]
              exact Nat.ne_of_gt hlt
            have hbne_len : (ρ.length != l) = true := bne_iff_ne.mpr (Nat.ne_of_gt hlt)
            refine ⟨by
              simp only [locConfined, hne_len, Bool.false_eq_true, ↓reduceIte, Bool.and_eq_true]
              exact ⟨hbne_len, hc.2⟩, ?_⟩
            intro s' hs'
            rcases List.mem_append.mp hs' with hs_old | hs_new
            · exact hslot s' hs_old
            · rcases List.mem_singleton.mp hs_new with rfl
              exact hnl_init
          · rcases Nat.lt_or_eq_of_le hle with hgt | heq
            · rw [getElem?_append_gt hgt] at hn; cases hn
            · subst heq
              rw [getElem?_append_last] at hn
              injection hn with hn
              injection hn with hrid hrv
              subst hrid; subst hrv
              have henc_rid0 : enc.contains rid0 = true := hsn.1.1.1
              have hc_e2 : locConfined ρ.length rid0 (enc.contains rid0) e2 = true :=
                locConfined_of_not_mem_locs ρ.length rid0 (enc.contains rid0) e2
                  (fun hm => Nat.lt_irrefl _ (hlocs ρ.length (List.mem_append.mpr (Or.inr hm))))
              refine ⟨by
                simp only [locConfined, rAsLoc?, beq_self_eq_true, ↓reduceIte, Bool.and_eq_true]
                exact ⟨⟨henc_rid0, hc_e2⟩, hsn.2⟩, ?_⟩
              intro s' hs'
              rcases List.mem_append.mp hs' with hs_old | hs_new
              · intro hm
                have hwf_s := hslots s' hs_old
                cases s' with
                | heap u | stackLive _ u =>
                  exact Nat.lt_irrefl _ (hwf_s.2.2.2 _ hm)
                | stackFreed _ => cases hm
              · rcases List.mem_singleton.mp hs_new with rfl
                intro hm
                exact Nat.lt_irrefl _ (hlocs ρ.length (List.mem_append.mpr (Or.inl hm)))
  | @letVal x v1 e2 _ _ hv1 =>
    simp only [rFreeVars, List.append_eq_nil_iff] at hcl
    simp only [staticSyntaxWF, Bool.and_eq_true] at hsw
    have hf1 : exprFrames v1 = [] :=
      exprFrames_of_noRegionSyntax (noRegionSyntax_of_isRValue hv1 hsw.1)
    refine ⟨fun hd hb => ⟨by
        rw [exprFrames_rSubst x hf1 e2]
        exact (distinctList_sublist_drop hd hb).2.1,
      fun r hr => by
        rw [exprFrames_rSubst x hf1 e2] at hr
        exact (distinctList_sublist_drop hd hb).2.2 r hr,
      fun _ _ _ _ h1 h2 => False.elim (refl_no_pop h1 h2)⟩,
      fun l rid _ hslot hc => ⟨?_, hslot⟩,
      fun _ _ _ hle h2 => False.elim (refl_no_alloc hle h2)⟩
    simp only [locConfined] at hc
    cases hloc : (rAsLoc? v1 == some l) with
    | true =>
      have hv1_eq := rAsLoc?_eq_some.mp (beq_iff_eq.mp hloc)
      subst hv1_eq
      simp only [rAsLoc?, beq_self_eq_true, ↓reduceIte, Bool.and_eq_true] at hc
      rcases hc with ⟨⟨henc_eq, hc2⟩, hd2⟩
      rw [henc_eq] at hc2 ⊢
      exact locConfined_rSubst_self l rid x e2 hc2 hd2
    | false =>
      simp only [hloc, Bool.false_eq_true, ↓reduceIte, Bool.and_eq_true] at hc
      have hnl1 : l ∉ rExprLocs v1 :=
        not_mem_locs_of_isRValue_locConfined hv1 hsw.1 hc.1
      exact locConfined_rSubst_other l rid (enc.contains rid) x hv1 hcl.1 hnl1 e2 hc.2
  | @ifStep c c' t e2 _ _ _ _ hs =>
    have hev := ((rstep_evol_box Φ specs c).run hs).1
    simp only [rFreeVars, List.append_eq_nil_iff] at hcl
    simp only [staticSyntaxWF, Bool.and_eq_true] at hsw
    simp only [stackNewWF, Bool.and_eq_true] at hsn
    have hcore_c := (rstep_core_box Φ specs c).run enc henv hs hslots hcl.1.1
      (fun l hl => hlocs l (List.mem_append.mpr (Or.inl (List.mem_append.mpr (Or.inl hl)))))
      hsw.1.1 hsn.1.1
    rcases (rstep_confine_box Φ specs c).run enc henv hs hslots hcl.1.1
      (fun l hl => hlocs l (List.mem_append.mpr (Or.inl (List.mem_append.mpr (Or.inl hl)))))
      hsw.1.1 hsn.1.1 with ⟨hfr_c, hlive_c, hnew_c⟩
    refine ⟨fun hd hb => ?_, fun l rid hlt hslot hc => ?_, fun l rid rv' hle hn => ?_⟩
    · simp only [exprFrames, List.append_assoc] at hd hb ⊢
      rcases distinctList_append.mp hd with ⟨hdc, _, _⟩
      have hbc : ∀ r ∈ exprFrames c, r < n :=
        fun r hr => hb r (List.mem_append.mpr (Or.inl hr))
      rcases hfr_c hdc hbc with ⟨hdc', hbc', hpopc⟩
      rcases distinctList_step_left hd hb hdc' hbc' hcore_c.2.2.2.2.2 hev.2.1 with
        ⟨hd_out, hb_out, hpop_out⟩
      exact ⟨hd_out, hb_out, fun l rid rv r' h1 h2 =>
        hpop_out rid (hpopc l rid rv r' h1 h2).1 (hpopc l rid rv r' h1 h2).2⟩
    · simp only [locConfined, Bool.and_eq_true] at hc ⊢
      rcases hlive_c l rid hlt hslot hc.1.1 with ⟨hcc', hslot'⟩
      exact ⟨⟨⟨hcc', hc.1.2⟩, hc.2⟩, hslot'⟩
    · rcases hnew_c l rid rv' hle hn with ⟨hcc', hslot'⟩
      have hct' := locConfined_of_not_mem_locs l rid (enc.contains rid) t
        (fun hm => Nat.not_lt.mpr hle
          (hlocs l (List.mem_append.mpr (Or.inl (List.mem_append.mpr (Or.inr hm))))))
      have hce' := locConfined_of_not_mem_locs l rid (enc.contains rid) e2
        (fun hm => Nat.not_lt.mpr hle (hlocs l (List.mem_append.mpr (Or.inr hm))))
      simp only [locConfined, Bool.and_eq_true]
      exact ⟨⟨⟨hcc', hct'⟩, hce'⟩, hslot'⟩
  | ifTrue =>
    refine ⟨fun hd hb => ⟨?_, ?_,
        fun _ _ _ _ h1 h2 => False.elim (refl_no_pop h1 h2)⟩,
      fun _ _ _ hslot hc =>
        ⟨by simp only [locConfined, Bool.and_eq_true] at hc; exact hc.1.2, hslot⟩,
      fun _ _ _ hle h2 => False.elim (refl_no_alloc hle h2)⟩
    · exact (distinctList_sublist_drop
        (distinctList_sublist_drop hd hb).1.1
        (distinctList_sublist_drop hd hb).1.2).2.1
    · exact (distinctList_sublist_drop
        (distinctList_sublist_drop hd hb).1.1
        (distinctList_sublist_drop hd hb).1.2).2.2
  | ifFalse =>
    exact ⟨fun hd hb => ⟨(distinctList_sublist_drop hd hb).2.1,
      (distinctList_sublist_drop hd hb).2.2,
      fun _ _ _ _ h1 h2 => False.elim (refl_no_pop h1 h2)⟩,
      fun _ _ _ hslot hc =>
        ⟨by simp only [locConfined, Bool.and_eq_true] at hc; exact hc.2, hslot⟩,
      fun _ _ _ hle h2 => False.elim (refl_no_alloc hle h2)⟩
  | whileUnfold =>
    simp only [staticSyntaxWF, Bool.and_eq_true] at hsw
    have hfc : exprFrames _ = [] := List.isEmpty_iff.mp hsw.1.1.1
    have hfb : exprFrames _ = [] := List.isEmpty_iff.mp hsw.1.1.2
    exact ⟨fun _ _ => ⟨by simp [exprFrames, exprFramesList, hfc, hfb]; exact .nil,
      fun r hr => by simp [exprFrames, exprFramesList, hfc, hfb] at hr,
      fun _ _ _ _ h1 h2 => False.elim (refl_no_pop h1 h2)⟩,
      fun _ _ _ hslot hc => ⟨by
        simp only [locConfined, Bool.and_eq_true] at hc
        simp only [locConfined, locConfinedList, hc.1, hc.2, Bool.and_self], hslot⟩,
      fun _ _ _ hle h2 => False.elim (refl_no_alloc hle h2)⟩
  | @matchHit v p body rest env _ _ hv hpat =>
    simp only [rFreeVars, rFreeVarsArms, List.append_eq_nil_iff] at hcl
    simp only [staticSyntaxWF, staticSyntaxWFArms, Bool.and_eq_true] at hsw
    have ⟨_, hbinds⟩ := rMatchPat_wf hv hcl.1 hsw.1 hpat
    have hvf : ∀ b ∈ env, exprFrames b.2 = [] := fun b hb =>
      exprFrames_of_noRegionSyntax (noRegionSyntax_of_isRValue (hbinds b hb).1 (hbinds b hb).2.2.1)
    refine ⟨fun hd hb => ⟨by
        rw [exprFrames_rSubstMany hvf]
        exact (distinctList_sublist_drop
          (distinctList_sublist_drop hd hb).2.1
          (distinctList_sublist_drop hd hb).2.2).1.1,
      fun r hr => by
        rw [exprFrames_rSubstMany hvf] at hr
        exact (distinctList_sublist_drop
          (distinctList_sublist_drop hd hb).2.1
          (distinctList_sublist_drop hd hb).2.2).1.2 r hr,
      fun _ _ _ _ h1 h2 => False.elim (refl_no_pop h1 h2)⟩,
      fun l rid _ hslot hc => ⟨?_, hslot⟩,
      fun _ _ _ hle h2 => False.elim (refl_no_alloc hle h2)⟩
    simp only [locConfined, locConfinedArms, Bool.and_eq_true] at hc
    have hnl_v : l ∉ rExprLocs v :=
      not_mem_locs_of_isRValue_locConfined hv hsw.1 hc.1
    exact locConfined_rSubstMany_other l rid (enc.contains rid)
      (fun b hb => (hbinds b hb).1)
      (fun b hb => (hbinds b hb).2.1)
      (fun b hb hm => hnl_v ((hbinds b hb).2.2.2 l hm))
      hc.2.1
  | matchMiss _ _ =>
    refine ⟨fun hd hb => ?_, fun _ _ _ hslot hc => ⟨?_, hslot⟩,
      fun _ _ _ hle h2 => False.elim (refl_no_alloc hle h2)⟩
    · rcases distinctList_append.mp hd with ⟨hd_v, hd_arms, hdisj⟩
      rcases distinctList_append.mp hd_arms with ⟨_, hd_rest, _⟩
      refine ⟨distinctList_append.mpr ⟨hd_v, hd_rest,
          fun r hrv hrr => hdisj r hrv (List.mem_append.mpr (Or.inr hrr))⟩,
        fun r hr => ?_,
        fun _ _ _ _ h1 h2 => False.elim (refl_no_pop h1 h2)⟩
      rcases List.mem_append.mp hr with h1 | h2
      · exact hb r (List.mem_append.mpr (Or.inl h1))
      · exact hb r (List.mem_append.mpr (Or.inr (List.mem_append.mpr (Or.inr h2))))
    · simp only [locConfined, locConfinedArms, Bool.and_eq_true] at hc ⊢
      exact ⟨hc.1, hc.2.2⟩
  | cellNewVal hv =>
    refine ⟨fun _ _ => ⟨.nil, (fun _ hm => nomatch hm),
      fun l rid rv r' h1 h2 => by
        rw [getElem?_append_lt (lt_length_of_getElem?_eq_some h1), h1] at h2
        cases h2⟩,
      fun l rid hlt hslot hc => ⟨?_, ?_⟩,
      fun l rid rv' hle hn => ?_⟩
    · exact bne_iff_ne.mpr (Nat.ne_of_gt hlt)
    · have hnl_v : l ∉ rExprLocs _ := not_mem_locs_of_isRValue_locConfined hv hsw hc
      intro s' hs'
      rcases List.mem_append.mp hs' with hs_old | hs_new
      · exact hslot s' hs_old
      · rcases List.mem_singleton.mp hs_new with rfl
        exact hnl_v
    · rcases Nat.lt_or_eq_of_le hle with hgt | heq
      · rw [getElem?_append_gt hgt] at hn; cases hn
      · subst heq; rw [getElem?_append_last] at hn; cases hn
  | cellGetHeap hl =>
    rcases hslots _ (mem_of_getElem?_eq_some hl) with ⟨hv, _, hsw_v, _⟩
    have hf_v := exprFrames_of_noRegionSyntax (noRegionSyntax_of_isRValue hv hsw_v)
    exact ⟨fun _ _ => ⟨hf_v ▸ .nil,
      (fun r hr => by rw [hf_v] at hr; cases hr),
      fun _ _ _ _ h1 h2 => False.elim (refl_no_pop h1 h2)⟩,
      fun l rid _ hslot _ =>
        ⟨locConfined_of_not_mem_locs l rid (enc.contains rid) _
          (hslot _ (mem_of_getElem?_eq_some hl)), hslot⟩,
      fun _ _ _ hle h2 => False.elim (refl_no_alloc hle h2)⟩
  | cellGetStack hl =>
    rcases hslots _ (mem_of_getElem?_eq_some hl) with ⟨hv, _, hsw_v, _⟩
    have hf_v := exprFrames_of_noRegionSyntax (noRegionSyntax_of_isRValue hv hsw_v)
    exact ⟨fun _ _ => ⟨hf_v ▸ .nil,
      (fun r hr => by rw [hf_v] at hr; cases hr),
      fun _ _ _ _ h1 h2 => False.elim (refl_no_pop h1 h2)⟩,
      fun l rid _ hslot _ =>
        ⟨locConfined_of_not_mem_locs l rid (enc.contains rid) _
          (hslot _ (mem_of_getElem?_eq_some hl)), hslot⟩,
      fun _ _ _ hle h2 => False.elim (refl_no_alloc hle h2)⟩
  | @cellSetHeap l0 _ v _ _ hl hv =>
    simp only [staticSyntaxWF, Bool.and_eq_true] at hsw
    refine ⟨fun _ _ => ⟨.nil, (fun _ hm => nomatch hm),
      fun l rid rv r' h1 h2 => by
        by_cases heq : l0 = l
        · subst heq; rw [hl] at h1; cases h1
        · rw [getElem?_set_ne heq, h1] at h2; cases h2⟩,
      fun l rid _ hslot hc => ⟨rfl, ?_⟩,
      fun l rid rv' hle hn => by
        have hlen : (ρ.set l0 (.heap v)).length = ρ.length := by simp
        exact False.elim (Nat.not_lt.mpr (hlen ▸ hle) (lt_length_of_getElem?_eq_some hn))⟩
    have hc_v : locConfined l rid (enc.contains rid) v = true := by
      simp only [locConfined] at hc
      split at hc <;> simp only [Bool.and_eq_true] at hc <;> exact hc.2
    have hnl_v := not_mem_locs_of_isRValue_locConfined hv hsw.2 hc_v
    intro s' hs'
    rcases mem_set_subset hs' with rfl | hmem
    · exact hnl_v
    · exact hslot s' hmem
  | @cellSetStack l0 rid0 _ v _ _ hl hv =>
    have hlt0 := lt_length_of_getElem?_eq_some hl
    simp only [staticSyntaxWF, Bool.and_eq_true] at hsw
    refine ⟨fun _ _ => ⟨.nil, (fun _ hm => nomatch hm),
      fun l rid rv r' h1 h2 => by
        by_cases heq : l0 = l
        · subst heq; rw [getElem?_set_self hlt0] at h2; cases h2
        · rw [getElem?_set_ne heq, h1] at h2; cases h2⟩,
      fun l rid _ hslot hc => ⟨rfl, ?_⟩,
      fun l rid rv' hle hn => by
        have hlen : (ρ.set l0 (.stackLive rid0 v)).length = ρ.length := by simp
        exact False.elim (Nat.not_lt.mpr (hlen ▸ hle) (lt_length_of_getElem?_eq_some hn))⟩
    have hc_v : locConfined l rid (enc.contains rid) v = true := by
      simp only [locConfined] at hc
      split at hc <;> simp only [Bool.and_eq_true] at hc <;> exact hc.2
    have hnl_v := not_mem_locs_of_isRValue_locConfined hv hsw.2 hc_v
    intro s' hs'
    rcases mem_set_subset hs' with rfl | hmem
    · exact hnl_v
    · exact hslot s' hmem
  | @frameVal rid0 re' ρ n hv =>
    have hf_v : exprFrames re' = [] :=
      exprFrames_of_noRegionSyntax (noRegionSyntax_of_isRValue hv hsw)
    refine ⟨fun _ _ => ⟨hf_v ▸ .nil,
      (fun r hr => by rw [hf_v] at hr; cases hr),
      fun l rid rv r' h1 h2 => ?_⟩,
      fun l rid _ hslot hc => ⟨?_, ?_⟩,
      fun l rid rv' hle hn => by
        rw [← length_popRegion rid0 ρ] at hle
        exact False.elim (Nat.not_lt.mpr hle (lt_length_of_getElem?_eq_some hn))⟩
    · rw [getElem?_popRegion, h1] at h2
      simp only [Option.map_some, popRegionSlot] at h2
      split at h2
      · rename_i heq
        have hrid : rid = rid0 := beq_iff_eq.mp heq
        subst hrid
        exact ⟨List.Mem.head _, by rw [hf_v]; intro hm; cases hm⟩
      · cases h2
    · simp only [locConfined] at hc
      have hnl_v := not_mem_locs_of_isRValue_locConfined hv hsw hc
      exact locConfined_of_not_mem_locs l rid (enc.contains rid) re' hnl_v
    · intro s' hs'
      rcases mem_popRegion hs' with ⟨s, hs, rfl⟩
      intro hm
      exact hslot s hs (slotLocs_popRegionSlot_subset rid0 s l hm)
  | @frameTrap rid0 _ _ _ =>
    refine ⟨fun _ _ => ⟨.nil, (fun _ hm => nomatch hm),
      fun l rid rv r' h1 h2 => ?_⟩,
      fun l _ _ hslot _ => ⟨rfl, ?_⟩,
      fun l rid rv' hle hn => by
        rw [← length_popRegion rid0 ρ] at hle
        exact False.elim (Nat.not_lt.mpr hle (lt_length_of_getElem?_eq_some hn))⟩
    · rw [getElem?_popRegion, h1] at h2
      simp only [Option.map_some, popRegionSlot] at h2
      split at h2
      · rename_i heq
        have hrid : rid = rid0 := beq_iff_eq.mp heq
        subst hrid
        exact ⟨List.Mem.head _, fun hm => nomatch hm⟩
      · cases h2
    · intro s' hs'
      rcases mem_popRegion hs' with ⟨s, hs, rfl⟩
      intro hm
      exact hslot s hs (slotLocs_popRegionSlot_subset rid0 s l hm)
termination_by sizeOf re

theorem rstepList_confine_box (Φ : FunEnv) (specs : List FnStackSpec) (es : List RExpr) :
    RStepListConfineBox Φ specs es := by
  refine ⟨fun enc {es' ρ ρ' n n'} henv hsl hslots hcl hlocs hsw hsn => ?_⟩
  cases hsl with
  | @head e1 e1' rest _ _ _ _ hs =>
    have hev := ((rstep_evol_box Φ specs e1).run hs).1
    simp only [rFreeVarsList, List.append_eq_nil_iff] at hcl
    simp only [staticSyntaxWFList, Bool.and_eq_true] at hsw
    simp only [stackNewWFList, Bool.and_eq_true] at hsn
    have hcore1 := (rstep_core_box Φ specs e1).run enc henv hs hslots hcl.1
      (fun l hl => hlocs l (List.mem_append.mpr (Or.inl hl))) hsw.1 hsn.1
    rcases (rstep_confine_box Φ specs e1).run enc henv hs hslots hcl.1
      (fun l hl => hlocs l (List.mem_append.mpr (Or.inl hl))) hsw.1 hsn.1 with
      ⟨hfr1, hlive1, hnew1⟩
    refine ⟨fun hd hb => ?_, fun l rid hlt hslot hc => ?_, fun l rid rv' hle hn => ?_⟩
    · rcases distinctList_append.mp hd with ⟨hd1, _, _⟩
      have hb1 : ∀ r ∈ exprFrames e1, r < n :=
        fun r hr => hb r (List.mem_append.mpr (Or.inl hr))
      rcases hfr1 hd1 hb1 with ⟨hd1', hb1', hpop1⟩
      rcases distinctList_step_left hd hb hd1' hb1' hcore1.2.2.2.2.2 hev.2.1 with
        ⟨hd_out, hb_out, hpop_out⟩
      exact ⟨hd_out, hb_out, fun l rid rv r' h1 h2 =>
        hpop_out rid (hpop1 l rid rv r' h1 h2).1 (hpop1 l rid rv r' h1 h2).2⟩
    · simp only [locConfinedList, Bool.and_eq_true] at hc ⊢
      rcases hlive1 l rid hlt hslot hc.1 with ⟨hc1', hslot'⟩
      exact ⟨⟨hc1', hc.2⟩, hslot'⟩
    · rcases hnew1 l rid rv' hle hn with ⟨hc1', hslot'⟩
      have hc2' := locConfinedList_of_not_mem_locs l rid (enc.contains rid) rest
        (fun hm => Nat.not_lt.mpr hle (hlocs l (List.mem_append.mpr (Or.inr hm))))
      simp only [locConfinedList, Bool.and_eq_true]
      exact ⟨⟨hc1', hc2'⟩, hslot'⟩
  | @tail v1 rest rest' _ _ _ _ _ hsl' =>
    have hev := ((rstepList_evol_box Φ specs rest).run hsl').1
    simp only [rFreeVarsList, List.append_eq_nil_iff] at hcl
    simp only [staticSyntaxWFList, Bool.and_eq_true] at hsw
    simp only [stackNewWFList, Bool.and_eq_true] at hsn
    have hcore2 := (rstepList_core_box Φ specs rest).run enc henv hsl' hslots hcl.2
      (fun l hl => hlocs l (List.mem_append.mpr (Or.inr hl))) hsw.2 hsn.2
    rcases (rstepList_confine_box Φ specs rest).run enc henv hsl' hslots hcl.2
      (fun l hl => hlocs l (List.mem_append.mpr (Or.inr hl))) hsw.2 hsn.2 with
      ⟨hfr2, hlive2, hnew2⟩
    refine ⟨fun hd hb => ?_, fun l rid hlt hslot hc => ?_, fun l rid rv' hle hn => ?_⟩
    · rcases distinctList_append.mp hd with ⟨_, hd2, _⟩
      have hb2 : ∀ r ∈ exprFramesList rest, r < n :=
        fun r hr => hb r (List.mem_append.mpr (Or.inr hr))
      rcases hfr2 hd2 hb2 with ⟨hd2', hb2', hpop2⟩
      rcases distinctList_step_right hd hb hd2' hb2' hcore2.2.2.2.2.2 hev.2.1 with
        ⟨hd_out, hb_out, hpop_out⟩
      exact ⟨hd_out, hb_out, fun l rid rv r' h1 h2 =>
        hpop_out rid (hpop2 l rid rv r' h1 h2).1 (hpop2 l rid rv r' h1 h2).2⟩
    · simp only [locConfinedList, Bool.and_eq_true] at hc ⊢
      rcases hlive2 l rid hlt hslot hc.2 with ⟨hc2', hslot'⟩
      exact ⟨⟨hc.1, hc2'⟩, hslot'⟩
    · rcases hnew2 l rid rv' hle hn with ⟨hc2', hslot'⟩
      have hc1' := locConfined_of_not_mem_locs l rid (enc.contains rid) v1
        (fun hm => Nat.not_lt.mpr hle (hlocs l (List.mem_append.mpr (Or.inl hm))))
      simp only [locConfinedList, Bool.and_eq_true]
      exact ⟨⟨hc1', hc2'⟩, hslot'⟩
termination_by sizeOf es
end

/-! ### Global Runtime Configuration Invariant (`ConfigWF`) & Top-Level Theorems -/

/-- Global well-formedness invariant for region-instrumented configurations `(re, ρ, n)`. -/
structure ConfigWF (Φ : FunEnv) (specs : List FnStackSpec)
    (re : RExpr) (ρ : RStore) (n : RegionId) : Prop where
  env_wf          : EnvEscapeWF Φ specs
  slots_wf        : ∀ s ∈ ρ, SlotValueWF ρ.length s
  closed          : rFreeVars re = []
  locs_bound      : ∀ l ∈ rExprLocs re, l < ρ.length
  static_wf       : staticSyntaxWF re = true
  stack_new_wf    : stackNewWF [] re = true
  frames_distinct : DistinctList (exprFrames re)
  frames_bound    : ∀ r ∈ exprFrames re, r < n
  live_confined   : ∀ (l : Loc) (rid : RegionId) (rv : RExpr),
    ρ[l]? = some (.stackLive rid rv) →
    locConfined l rid false re = true ∧ (∀ s ∈ ρ, l ∉ slotLocs s)
  freed_dead      : ∀ (l : Loc) (rid : RegionId),
    ρ[l]? = some (.stackFreed rid) →
    l ∉ rExprLocs re ∧ (∀ s ∈ ρ, l ∉ slotLocs s)

theorem rstep_preserves_configWF {Φ : FunEnv} {specs : List FnStackSpec}
    {re re' : RExpr} {ρ ρ' : RStore} {n n' : RegionId}
    (hwf : ConfigWF Φ specs re ρ n)
    (hstep : RStep Φ specs re ρ n re' ρ' n') :
    ConfigWF Φ specs re' ρ' n' := by
  rcases (rstep_evol_box Φ specs re).run hstep with ⟨hev, hdead⟩
  rcases (rstep_core_box Φ specs re).run [] hwf.env_wf hstep
    hwf.slots_wf hwf.closed hwf.locs_bound hwf.static_wf hwf.stack_new_wf with
    ⟨hslots', hcl', hlocs', hsw', hsn', _⟩
  rcases (rstep_confine_box Φ specs re).run [] hwf.env_wf hstep
    hwf.slots_wf hwf.closed hwf.locs_bound hwf.static_wf hwf.stack_new_wf with
    ⟨hfr_fn, hlive_fn, hnew_fn⟩
  rcases hfr_fn hwf.frames_distinct hwf.frames_bound with ⟨hd', hb', hpop'⟩
  refine {
    env_wf := hwf.env_wf
    slots_wf := hslots'
    closed := hcl'
    locs_bound := hlocs'
    static_wf := hsw'
    stack_new_wf := hsn'
    frames_distinct := hd'
    frames_bound := hb'
    live_confined := ?_
    freed_dead := ?_
  }
  · intro l rid rv' hl'
    by_cases hlt : l < ρ.length
    · cases h_old : ρ[l]? with
      | none =>
        exact absurd hlt (by
          have h_none : ∀ (xs : RStore) (i : Nat), xs[i]? = none → xs.length ≤ i := by
            intro xs
            induction xs with
            | nil => intro i _; exact Nat.zero_le i
            | cons _ tl iht =>
              intro i hi
              cases i with
              | zero => simp at hi
              | succ j => exact Nat.succ_le_succ (iht j hi)
          exact Nat.not_lt.mpr (h_none ρ l h_old))
      | some s_old =>
        cases s_old with
        | heap u =>
          rcases hev.2.2.1 l u h_old with ⟨u', hu'⟩
          rw [hl'] at hu'; cases hu'
        | stackFreed r0 =>
          have hf' := hev.2.2.2.2.1 l r0 h_old
          rw [hl'] at hf'; cases hf'
        | stackLive r0 u =>
          have hr_eq : r0 = rid := by
            rcases hev.2.2.2.1 l r0 u h_old with ⟨u', hu'⟩ | hf'
            · rw [hl'] at hu'; injection hu' with hu'; injection hu' with hr _; exact hr.symm
            · rw [hl'] at hf'; cases hf'
          subst hr_eq
          rcases hwf.live_confined l r0 u h_old with ⟨hc_old, hslot_old⟩
          exact hlive_fn l r0 hlt hslot_old hc_old
    · exact hnew_fn l rid rv' (Nat.not_lt.mp hlt) hl'
  · intro l rid hf'
    have hlt : l < ρ.length := by
      by_cases h : l < ρ.length
      · exact h
      · exact False.elim (hev.2.2.2.2.2 l rid (Nat.not_lt.mp h) hf')
    cases h_old : ρ[l]? with
    | none =>
      have h_none : ∀ (xs : RStore) (i : Nat), xs[i]? = none → xs.length ≤ i := by
        intro xs
        induction xs with
        | nil => intro i _; exact Nat.zero_le i
        | cons _ tl iht =>
          intro i hi
          cases i with
          | zero => simp at hi
          | succ j => exact Nat.succ_le_succ (iht j hi)
      exact False.elim (Nat.not_lt.mpr (h_none ρ l h_old) hlt)
    | some s_old =>
      cases s_old with
      | heap u =>
        rcases hev.2.2.1 l u h_old with ⟨u', hu'⟩
        rw [hf'] at hu'; cases hu'
      | stackFreed r0 =>
        rcases hwf.freed_dead l r0 h_old with ⟨hnl_old, hslot_old⟩
        exact hdead hwf.env_wf l hlt hnl_old hslot_old
      | stackLive r0 u =>
        rcases hwf.live_confined l r0 u h_old with ⟨hc_old, hslot_old⟩
        rcases hlive_fn l r0 hlt hslot_old hc_old with ⟨hc_new, hslot_new⟩
        have ⟨_, hnot_frame⟩ := hpop' l r0 u rid h_old hf'
        exact ⟨not_mem_locs_of_locConfined_false re' hc_new hnot_frame, hslot_new⟩

theorem rsteps_preserve_configWF {Φ : FunEnv} {specs : List FnStackSpec}
    {re re' : RExpr} {ρ ρ' : RStore} {n n' : RegionId}
    (hwf : ConfigWF Φ specs re ρ n)
    (hsteps : RSteps Φ specs re ρ n re' ρ' n') :
    ConfigWF Φ specs re' ρ' n' := by
  induction hsteps with
  | refl => exact hwf
  | trans h1 _ ih => exact ih (rstep_preserves_configWF hwf h1)

theorem init_configWF {funs : List FunDef} {specs : List FnStackSpec}
    {Φ : FunEnv}
    (hΦ_eq : ∀ name, Φ name = funs.find? (·.name == name))
    (hesc : checkProgramEscape funs specs = .ok ())
    {entry : Ident} {fdEntry : FunDef}
    (hentry : Φ entry = some fdEntry)
    (hparams : fdEntry.params = []) :
    ConfigWF Φ specs
      (.frame 0 (compileExpr (lookupStackVars specs entry) 0 fdEntry.body)) [] 1 := by
  have henv := checkProgramEscape_sound hΦ_eq hesc
  have ⟨hnolocs, hclosed, hvars⟩ := henv entry fdEntry hentry
  refine {
    env_wf := henv
    slots_wf := fun _ hm => nomatch hm
    closed := ?_
    locs_bound := ?_
    static_wf := staticSyntaxWF_compileExpr _ 0 fdEntry.body
    stack_new_wf := ?_
    frames_distinct := ?_
    frames_bound := ?_
    live_confined := fun _ _ _ hm => by simp at hm
    freed_dead := fun _ _ hm => by simp at hm
  }
  · simp only [rFreeVars, rFreeVars_compileExpr]
    apply List.eq_nil_iff_forall_not_mem.mpr
    intro z hz
    have hp := List.all_eq_true.mp hclosed z hz
    rw [hparams] at hp
    simp at hp
  · intro l hl
    simp only [rExprLocs, rExprLocs_compileExpr] at hl
    rw [List.isEmpty_iff.mp hnolocs] at hl
    cases hl
  · simp only [stackNewWF]
    apply stackNewWF_compileExpr [0] _ 0 fdEntry.body
    · right; rfl
    · intro x hx; exact Or.inl (hvars x hx)
  · simp only [exprFrames, exprFrames_compileExpr]
    exact .cons (fun hm => nomatch hm) .nil
  · intro r hr
    simp only [exprFrames, exprFrames_compileExpr, List.mem_singleton] at hr
    subst hr
    exact Nat.zero_lt_one

/-- General Zero Dangling Stack Pointers Theorem for any 0-parameter entry function
    and any `FunEnv` matching `funs`. -/
theorem escape_no_dangling_pointers_gen {funs : List FunDef} {specs : List FnStackSpec}
    {Φ : FunEnv}
    (hΦ_eq : ∀ name, Φ name = funs.find? (·.name == name))
    (hesc : checkProgramEscape funs specs = .ok ())
    {entry : Ident} {fdEntry : FunDef}
    (hentry : Φ entry = some fdEntry)
    (hparams : fdEntry.params = [])
    {re' : RExpr} {ρ' : RStore} {n' : RegionId}
    (hsteps : RSteps Φ specs
      (.frame 0 (compileExpr (lookupStackVars specs entry) 0 fdEntry.body)) [] 1 re' ρ' n') :
    ¬ IsDanglingAccess re' ρ' := by
  have hwf' := rsteps_preserve_configWF (init_configWF hΦ_eq hesc hentry hparams) hsteps
  intro hdang
  rcases danglingAt_has_freed_loc hdang with ⟨l, rid, hfreed, hmem⟩
  exact (hwf'.freed_dead l rid hfreed).1 hmem

/-- **Theorem 2 (Zero Dangling Stack Pointers)**:
    Any Core Geisha program accepted by `checkProgramEscape` never attempts a
    read or write to a deallocated stack-frame region (`¬ IsDanglingAccess`)
    at any reachable execution state. -/
theorem escape_no_dangling_pointers {funs : List FunDef} {specs : List FnStackSpec}
    (hesc : checkProgramEscape funs specs = .ok ())
    {fdMain : FunDef}
    (hmain : funs.find? (·.name == "main") = some fdMain)
    (hparams : fdMain.params = [])
    {re' : RExpr} {ρ' : RStore} {n' : RegionId}
    (hsteps : RSteps (buildFunEnvFromList funs) specs
      (.frame 0 (compileExpr (lookupStackVars specs "main") 0 fdMain.body)) [] 1 re' ρ' n') :
    ¬ IsDanglingAccess re' ρ' :=
  escape_no_dangling_pointers_gen (fun _ => rfl) hesc hmain hparams hsteps

/-! ## Part 3.3: Stack-vs-Heap Observational Simulation (`stack_alloc_simulates_heap`) -/

/-- **Theorem 3 (Stack-vs-Heap Observational Simulation)**:
    Every stack-promoted region execution trace (`RSteps`) of a program passing
    `checkProgramEscape` is simulated by a standard heap-allocated execution
    trace (`Steps`) producing the exact erased expression and a store matching
    every live cell (`RStoreMatches`). -/
theorem stack_alloc_simulates_heap (Δ : AdtEnv) {funs : List FunDef} {specs : List FnStackSpec}
    {Φ : FunEnv}
    (hΦ_eq : ∀ name, Φ name = funs.find? (·.name == name))
    (hesc : checkProgramEscape funs specs = .ok ())
    {fdMain : FunDef}
    (hmain : Φ "main" = some fdMain)
    (hparams : fdMain.params = [])
    {re' : RExpr} {ρ' : RStore} {n' : RegionId}
    (hsteps : RSteps Φ specs
      (.frame 0 (compileExpr (lookupStackVars specs "main") 0 fdMain.body)) [] 1 re' ρ' n') :
    ∃ σ' : Store,
      Steps Δ Φ fdMain.body [] (eraseRExpr re') σ' ∧ RStoreMatches ρ' σ' := by
  have _hnodang : ¬ IsDanglingAccess re' ρ' :=
    escape_no_dangling_pointers_gen hΦ_eq hesc hmain hparams hsteps
  rcases rsteps_simulates Δ hsteps rStoreMatches_nil with ⟨σ', hsim, hmatch⟩
  simp only [eraseRExpr, eraseRExpr_compileExpr] at hsim
  exact ⟨σ', hsim, hmatch⟩

/-! ## Part 3.1: Non-Vacuity Counterexample (`dangling_access_nonvacuous`) -/

/-- Concrete unchecked expression where stack cell `c` allocated in region `0`
    escapes its frame `.frame 0` as a return value and is immediately read by
    the caller via `.cellGet`. -/
def badInit : RExpr :=
  .cellGet (.frame 0 (.let_ "c" (.stackCellNew 0 (.lit (.int 42))) (.var "c")))

/-- **Theorem 1 (Non-Vacuity of `IsDanglingAccess`)**:
    Without `checkProgramEscape`, returning a stack-allocated `Cell` from
    `.frame 0` and dereferencing it steps in 3 transitions to `IsDanglingAccess`. -/
theorem dangling_access_nonvacuous :
    ∃ re' ρ' n', RSteps emptyFunEnv [] badInit [] 1 re' ρ' n' ∧ IsDanglingAccess re' ρ' := by
  refine ⟨.cellGet (.loc 0), [.stackFreed 0], 1, ?_, ?_⟩
  · apply RSteps.trans
    · exact .cellGetStep (.frameStep (.letStep (.stackCellNewVal (.lit (.int 42)))))
    · apply RSteps.trans
      · exact .cellGetStep (.frameStep (.letVal (.loc 0)))
      · apply RSteps.trans
        · exact .cellGetStep (.frameVal (.loc 0))
        · exact .refl _ _ _
  · exact .read (rid := 0) rfl

end CoreGeisha
