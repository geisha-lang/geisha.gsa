import CoreGeisha.Syntax

/-!
# Core Geisha: Small-Step & Concurrent Operational Semantics

Strict left-to-right call-by-value small-step operational semantics
`Step Δ Φ tasks e σ e' σ' spawned` and interleaved concurrent task-pool
semantics `ConcStep Δ Φ tasks σ tasks' σ'` with:
- Wrapping 32-bit two's-complement arithmetic (`Int32`)
- Explicit division/remainder-by-zero traps (`Trap.divByZero`)
- Short-circuit `&&` and `||`
- Deterministic pattern matching (`matchPat`) with explicit `Trap.matchFailure`
- Explicit mutable store operations (`cellNew`, `cellGet`, `cellSet`)
- Concurrent `spawn` (forking a `shared` 0-arg closure into a new task) and
  `await` (joining a completed task's `IsSend` value or propagating its trap)
- Explicit active memory-access characterization (`ActiveCellAccess`, `HasDataRace`)
-/

namespace CoreGeisha

/-- Evaluate a unary operator on a literal value. -/
def evalUnOp : UnOp → Lit → Option Lit
  | .not, .bool b => some (.bool (!b))
  | .neg, .int n => some (.int (-n))
  | .bitNot, .int n => some (.int (~~~n))
  | _, _ => none

/-- Result of evaluating a strict binary operator on two literal values. -/
inductive BinEvalResult where
  | val : Lit → BinEvalResult
  | trap : Trap → BinEvalResult
  deriving Repr, BEq

/-- Evaluate a strict (non-short-circuiting) binary operator on two literals. -/
def evalBinOp : BinOp → Lit → Lit → Option BinEvalResult
  | .add, .int a, .int b => some (.val (.int (a + b)))
  | .sub, .int a, .int b => some (.val (.int (a - b)))
  | .mul, .int a, .int b => some (.val (.int (a * b)))
  | .div, .int a, .int b =>
    if b == 0 then some (.trap .divByZero) else some (.val (.int (a / b)))
  | .rem, .int a, .int b =>
    if b == 0 then some (.trap .divByZero) else some (.val (.int (a % b)))
  | .bitAnd, .int a, .int b => some (.val (.int (a &&& b)))
  | .bitOr, .int a, .int b => some (.val (.int (a ||| b)))
  | .bitXor, .int a, .int b => some (.val (.int (a ^^^ b)))
  | .eqInt, .int a, .int b => some (.val (.bool (a == b)))
  | .neInt, .int a, .int b => some (.val (.bool (a != b)))
  | .ltInt, .int a, .int b => some (.val (.bool (a < b)))
  | .leInt, .int a, .int b => some (.val (.bool (a <= b)))
  | .gtInt, .int a, .int b => some (.val (.bool (b < a)))
  | .geInt, .int a, .int b => some (.val (.bool (b <= a)))
  | .eqBool, .bool a, .bool b => some (.val (.bool (a == b)))
  | .eqStr, .str a, .str b => some (.val (.bool (a == b)))
  | .strConcat, .str a, .str b => some (.val (.str (a ++ b)))
  | _, _, _ => none

/- Deterministic pattern matching of a closed value against a pattern.
   Returns `some bindings` on match, `none` on mismatch. -/
mutual
def matchPat : Pat → Expr → Option (List (Ident × Expr))
  | .wild, _ => some []
  | .var x, v => some [(x, v)]
  | .lit l1, .lit l2 => if l1 == l2 then some [] else none
  | .tuple ps, .tuple vs => matchPats ps vs
  | .ctor adt1 tag1 ps, .makeData adt2 tag2 vs =>
    if adt1 == adt2 && tag1 == tag2 then matchPats ps vs else none
  | _, _ => none

def matchPats : List Pat → List Expr → Option (List (Ident × Expr))
  | [], [] => some []
  | p :: ps, v :: vs =>
    match matchPat p v, matchPats ps vs with
    | some b1, some b2 => some (b1 ++ b2)
    | _, _ => none
  | _, _ => none
end

/-- Helper: a list of expressions whose leftmost non-value is `.trap t`. -/
inductive ListFirstTrap : List Expr → Trap → Prop where
  | head (t : Trap) (rest : List Expr) : ListFirstTrap (.trap t :: rest) t
  | tail {v : Expr} {rest : List Expr} {t : Trap} :
      IsValue v → ListFirstTrap rest t → ListFirstTrap (v :: rest) t

/-- Zip parameter declarations with argument values for simultaneous substitution. -/
def zipParams (ps : List (Ident × Ty)) (vs : List Expr) : List (Ident × Expr) :=
  (ps.map Prod.fst).zip vs

/-- A thread expression is terminal if it is either a value or a defined runtime trap. -/
def IsTerminal (e : Expr) : Prop :=
  IsValue e ∨ ∃ t, e = .trap t

/- Single-thread small-step transition `Step Δ Φ tasks e σ e' σ' spawned`,
   parameterized by a read-only snapshot of the current `tasks` pool (for `spawn`
   fresh `TaskId` allocation and `await` completion inspection), producing an
   optional newly spawned task body `spawned : Option Expr`. -/
mutual
inductive Step (Δ : AdtEnv) (Φ : FunEnv) (tasks : List Expr) :
    Expr → Store → Expr → Store → Option Expr → Prop where
  -- Tuple: strict left-to-right
  | tupleStep {es es' : List Expr} {σ σ' : Store} {sp : Option Expr} :
      StepList Δ Φ tasks es σ es' σ' sp →
      Step Δ Φ tasks (.tuple es) σ (.tuple es') σ' sp
  | tupleTrap {es : List Expr} {t : Trap} {σ : Store} :
      ListFirstTrap es t →
      Step Δ Φ tasks (.tuple es) σ (.trap t) σ none

  -- Block: sequential evaluation
  | blockEmpty {σ : Store} :
      Step Δ Φ tasks (.block []) σ (.lit .unit) σ none
  | blockSingle {e : Expr} {σ : Store} :
      Step Δ Φ tasks (.block [e]) σ e σ none
  | blockConsStep {e1 e1' e2 : Expr} {es : List Expr} {σ σ' : Store} {sp : Option Expr} :
      Step Δ Φ tasks e1 σ e1' σ' sp →
      Step Δ Φ tasks (.block (e1 :: e2 :: es)) σ (.block (e1' :: e2 :: es)) σ' sp
  | blockConsVal {v1 e2 : Expr} {es : List Expr} {σ : Store} :
      IsValue v1 →
      Step Δ Φ tasks (.block (v1 :: e2 :: es)) σ (.block (e2 :: es)) σ none
  | blockConsTrap {t : Trap} {e2 : Expr} {es : List Expr} {σ : Store} :
      Step Δ Φ tasks (.block (.trap t :: e2 :: es)) σ (.trap t) σ none

  -- Closure application: callee first, then args left-to-right, then β-reduction
  | applyFn {fn fn' : Expr} {args : List Expr} {σ σ' : Store} {sp : Option Expr} :
      Step Δ Φ tasks fn σ fn' σ' sp →
      Step Δ Φ tasks (.apply fn args) σ (.apply fn' args) σ' sp
  | applyFnTrap {t : Trap} {args : List Expr} {σ : Store} :
      Step Δ Φ tasks (.apply (.trap t) args) σ (.trap t) σ none
  | applyArgs {fn : Expr} {args args' : List Expr} {σ σ' : Store} {sp : Option Expr} :
      IsValue fn →
      StepList Δ Φ tasks args σ args' σ' sp →
      Step Δ Φ tasks (.apply fn args) σ (.apply fn args') σ' sp
  | applyArgsTrap {fn : Expr} {args : List Expr} {t : Trap} {σ : Store} :
      IsValue fn →
      ListFirstTrap args t →
      Step Δ Φ tasks (.apply fn args) σ (.trap t) σ none
  | applyBeta {m : Mode} {ps : List (Ident × Ty)} {ret : Ty} {body : Expr}
      {args : List Expr} {σ : Store} :
      (∀ a ∈ args, IsValue a) →
      args.length = ps.length →
      Step Δ Φ tasks (.apply (.lam m ps ret body) args) σ (substMany (zipParams ps args) body) σ none

  -- Direct top-level function call (`TmApplyDir`)
  | applyDirArgs {name : Ident} {args args' : List Expr} {σ σ' : Store} {sp : Option Expr} :
      StepList Δ Φ tasks args σ args' σ' sp →
      Step Δ Φ tasks (.applyDir name args) σ (.applyDir name args') σ' sp
  | applyDirTrap {name : Ident} {args : List Expr} {t : Trap} {σ : Store} :
      ListFirstTrap args t →
      Step Δ Φ tasks (.applyDir name args) σ (.trap t) σ none
  | applyDirBeta {name : Ident} {fd : FunDef} {args : List Expr} {σ : Store} :
      Φ name = some fd →
      (∀ a ∈ args, IsValue a) →
      args.length = fd.params.length →
      Step Δ Φ tasks (.applyDir name args) σ (substMany (zipParams fd.params args) fd.body) σ none

  -- Unary operators
  | unStep {op : UnOp} {e e' : Expr} {σ σ' : Store} {sp : Option Expr} :
      Step Δ Φ tasks e σ e' σ' sp →
      Step Δ Φ tasks (.un op e) σ (.un op e') σ' sp
  | unTrap {op : UnOp} {t : Trap} {σ : Store} :
      Step Δ Φ tasks (.un op (.trap t)) σ (.trap t) σ none
  | unVal {op : UnOp} {l l' : Lit} {σ : Store} :
      evalUnOp op l = some l' →
      Step Δ Φ tasks (.un op (.lit l)) σ (.lit l') σ none

  -- Binary operators (short-circuit for && and ||; strict left-to-right for all others)
  | binLeft {op : BinOp} {e1 e1' e2 : Expr} {σ σ' : Store} {sp : Option Expr} :
      Step Δ Φ tasks e1 σ e1' σ' sp →
      Step Δ Φ tasks (.bin op e1 e2) σ (.bin op e1' e2) σ' sp
  | binLeftTrap {op : BinOp} {t : Trap} {e2 : Expr} {σ : Store} :
      Step Δ Φ tasks (.bin op (.trap t) e2) σ (.trap t) σ none
  | binAndFalse {e2 : Expr} {σ : Store} :
      Step Δ Φ tasks (.bin .and (.lit (.bool false)) e2) σ (.lit (.bool false)) σ none
  | binAndTrue {e2 : Expr} {σ : Store} :
      Step Δ Φ tasks (.bin .and (.lit (.bool true)) e2) σ e2 σ none
  | binOrTrue {e2 : Expr} {σ : Store} :
      Step Δ Φ tasks (.bin .or (.lit (.bool true)) e2) σ (.lit (.bool true)) σ none
  | binOrFalse {e2 : Expr} {σ : Store} :
      Step Δ Φ tasks (.bin .or (.lit (.bool false)) e2) σ e2 σ none
  | binRight {op : BinOp} {v1 e2 e2' : Expr} {σ σ' : Store} {sp : Option Expr} :
      op ≠ .and → op ≠ .or →
      IsValue v1 →
      Step Δ Φ tasks e2 σ e2' σ' sp →
      Step Δ Φ tasks (.bin op v1 e2) σ (.bin op v1 e2') σ' sp
  | binRightTrap {op : BinOp} {v1 : Expr} {t : Trap} {σ : Store} :
      op ≠ .and → op ≠ .or →
      IsValue v1 →
      Step Δ Φ tasks (.bin op v1 (.trap t)) σ (.trap t) σ none
  | binVal {op : BinOp} {l1 l2 l' : Lit} {σ : Store} :
      evalBinOp op l1 l2 = some (.val l') →
      Step Δ Φ tasks (.bin op (.lit l1) (.lit l2)) σ (.lit l') σ none
  | binTrap {op : BinOp} {l1 l2 : Lit} {t : Trap} {σ : Store} :
      evalBinOp op l1 l2 = some (.trap t) →
      Step Δ Φ tasks (.bin op (.lit l1) (.lit l2)) σ (.trap t) σ none

  -- Let binding
  | letStep {x : Ident} {e1 e1' e2 : Expr} {σ σ' : Store} {sp : Option Expr} :
      Step Δ Φ tasks e1 σ e1' σ' sp →
      Step Δ Φ tasks (.let_ x e1 e2) σ (.let_ x e1' e2) σ' sp
  | letTrap {x : Ident} {t : Trap} {e2 : Expr} {σ : Store} :
      Step Δ Φ tasks (.let_ x (.trap t) e2) σ (.trap t) σ none
  | letVal {x : Ident} {v1 e2 : Expr} {σ : Store} :
      IsValue v1 →
      Step Δ Φ tasks (.let_ x v1 e2) σ (subst x v1 e2) σ none

  -- Conditional
  | ifStep {c c' t e : Expr} {σ σ' : Store} {sp : Option Expr} :
      Step Δ Φ tasks c σ c' σ' sp →
      Step Δ Φ tasks (.if_ c t e) σ (.if_ c' t e) σ' sp
  | ifTrap {tr : Trap} {t e : Expr} {σ : Store} :
      Step Δ Φ tasks (.if_ (.trap tr) t e) σ (.trap tr) σ none
  | ifTrue {t e : Expr} {σ : Store} :
      Step Δ Φ tasks (.if_ (.lit (.bool true)) t e) σ t σ none
  | ifFalse {t e : Expr} {σ : Store} :
      Step Δ Φ tasks (.if_ (.lit (.bool false)) t e) σ e σ none

  -- While loop (unfolds to `if c { b; while c b } else ()`)
  | whileUnfold {c b : Expr} {σ : Store} :
      Step Δ Φ tasks (.while_ c b) σ (.if_ c (.block [b, .while_ c b]) (.lit .unit)) σ none

  -- Pattern matching
  | matchScrut {s s' : Expr} {arms : List (Pat × Expr)} {σ σ' : Store} {sp : Option Expr} :
      Step Δ Φ tasks s σ s' σ' sp →
      Step Δ Φ tasks (.match_ s arms) σ (.match_ s' arms) σ' sp
  | matchScrutTrap {t : Trap} {arms : List (Pat × Expr)} {σ : Store} :
      Step Δ Φ tasks (.match_ (.trap t) arms) σ (.trap t) σ none
  | matchEmpty {v : Expr} {σ : Store} :
      IsValue v →
      Step Δ Φ tasks (.match_ v []) σ (.trap .matchFailure) σ none
  | matchHit {v : Expr} {p : Pat} {body : Expr} {rest : List (Pat × Expr)}
      {env : List (Ident × Expr)} {σ : Store} :
      IsValue v →
      matchPat p v = some env →
      Step Δ Φ tasks (.match_ v ((p, body) :: rest)) σ (substMany env body) σ none
  | matchMiss {v : Expr} {p : Pat} {body : Expr} {rest : List (Pat × Expr)} {σ : Store} :
      IsValue v →
      matchPat p v = none →
      Step Δ Φ tasks (.match_ v ((p, body) :: rest)) σ (.match_ v rest) σ none

  -- ADT construction & tag inspection
  | makeDataStep {adt : Ident} {tag : Nat} {es es' : List Expr} {σ σ' : Store} {sp : Option Expr} :
      StepList Δ Φ tasks es σ es' σ' sp →
      Step Δ Φ tasks (.makeData adt tag es) σ (.makeData adt tag es') σ' sp
  | makeDataTrap {adt : Ident} {tag : Nat} {es : List Expr} {t : Trap} {σ : Store} :
      ListFirstTrap es t →
      Step Δ Φ tasks (.makeData adt tag es) σ (.trap t) σ none
  | getTagStep {e e' : Expr} {σ σ' : Store} {sp : Option Expr} :
      Step Δ Φ tasks e σ e' σ' sp →
      Step Δ Φ tasks (.getTag e) σ (.getTag e') σ' sp
  | getTagTrap {t : Trap} {σ : Store} :
      Step Δ Φ tasks (.getTag (.trap t)) σ (.trap t) σ none
  | getTagVal {adt : Ident} {tag : Nat} {vs : List Expr} {σ : Store} :
      (∀ v ∈ vs, IsValue v) →
      Step Δ Φ tasks (.getTag (.makeData adt tag vs)) σ (.lit (.int (Int32.ofNat tag))) σ none

  -- Mutable Cell store operations
  | cellNewStep {e e' : Expr} {σ σ' : Store} {sp : Option Expr} :
      Step Δ Φ tasks e σ e' σ' sp →
      Step Δ Φ tasks (.cellNew e) σ (.cellNew e') σ' sp
  | cellNewTrap {t : Trap} {σ : Store} :
      Step Δ Φ tasks (.cellNew (.trap t)) σ (.trap t) σ none
  | cellNewVal {v : Expr} {σ : Store} :
      IsValue v →
      Step Δ Φ tasks (.cellNew v) σ (.loc σ.length) (σ ++ [v]) none
  | cellGetStep {e e' : Expr} {σ σ' : Store} {sp : Option Expr} :
      Step Δ Φ tasks e σ e' σ' sp →
      Step Δ Φ tasks (.cellGet e) σ (.cellGet e') σ' sp
  | cellGetTrap {t : Trap} {σ : Store} :
      Step Δ Φ tasks (.cellGet (.trap t)) σ (.trap t) σ none
  | cellGetVal {l : Loc} {v : Expr} {σ : Store} :
      σ[l]? = some v →
      Step Δ Φ tasks (.cellGet (.loc l)) σ v σ none
  | cellSetLeft {e1 e1' e2 : Expr} {σ σ' : Store} {sp : Option Expr} :
      Step Δ Φ tasks e1 σ e1' σ' sp →
      Step Δ Φ tasks (.cellSet e1 e2) σ (.cellSet e1' e2) σ' sp
  | cellSetLeftTrap {t : Trap} {e2 : Expr} {σ : Store} :
      Step Δ Φ tasks (.cellSet (.trap t) e2) σ (.trap t) σ none
  | cellSetRight {v1 e2 e2' : Expr} {σ σ' : Store} {sp : Option Expr} :
      IsValue v1 →
      Step Δ Φ tasks e2 σ e2' σ' sp →
      Step Δ Φ tasks (.cellSet v1 e2) σ (.cellSet v1 e2') σ' sp
  | cellSetRightTrap {v1 : Expr} {t : Trap} {σ : Store} :
      IsValue v1 →
      Step Δ Φ tasks (.cellSet v1 (.trap t)) σ (.trap t) σ none
  | cellSetVal {l : Loc} {v : Expr} {σ : Store} :
      l < σ.length →
      IsValue v →
      Step Δ Φ tasks (.cellSet (.loc l) v) σ (.lit .unit) (σ.set l v) none

  -- Concurrent task fork (`spawn`) and join (`await`)
  | spawnStep {e e' : Expr} {σ σ' : Store} {sp : Option Expr} :
      Step Δ Φ tasks e σ e' σ' sp →
      Step Δ Φ tasks (.spawn e) σ (.spawn e') σ' sp
  | spawnTrap {t : Trap} {σ : Store} :
      Step Δ Φ tasks (.spawn (.trap t)) σ (.trap t) σ none
  | spawnBeta {ret : Ty} {body : Expr} {σ : Store} :
      Step Δ Φ tasks (.spawn (.lam .shared [] ret body)) σ (.taskRef tasks.length) σ (some body)
  | awaitStep {e e' : Expr} {σ σ' : Store} {sp : Option Expr} :
      Step Δ Φ tasks e σ e' σ' sp →
      Step Δ Φ tasks (.await e) σ (.await e') σ' sp
  | awaitTrap {t : Trap} {σ : Store} :
      Step Δ Φ tasks (.await (.trap t)) σ (.trap t) σ none
  | awaitVal {tid : TaskId} {v : Expr} {σ : Store} :
      tasks[tid]? = some v →
      IsValue v →
      Step Δ Φ tasks (.await (.taskRef tid)) σ v σ none
  | awaitTaskTrap {tid : TaskId} {t : Trap} {σ : Store} :
      tasks[tid]? = some (.trap t) →
      Step Δ Φ tasks (.await (.taskRef tid)) σ (.trap t) σ none

inductive StepList (Δ : AdtEnv) (Φ : FunEnv) (tasks : List Expr) :
    List Expr → Store → List Expr → Store → Option Expr → Prop where
  | head {e e' : Expr} {es : List Expr} {σ σ' : Store} {sp : Option Expr} :
      Step Δ Φ tasks e σ e' σ' sp →
      StepList Δ Φ tasks (e :: es) σ (e' :: es) σ' sp
  | tail {v : Expr} {es es' : List Expr} {σ σ' : Store} {sp : Option Expr} :
      IsValue v →
      StepList Δ Φ tasks es σ es' σ' sp →
      StepList Δ Φ tasks (v :: es) σ (v :: es') σ' sp
end

/-! ## Task-Waiting Characterization & Stuckness -/

/- A thread expression is legitimately waiting on a still-running spawned task
   if its active redex is `.await (.taskRef tid)` for a valid non-terminal `tid`. -/
mutual
inductive BlockedOnTask (tasks : List Expr) : Expr → Prop where
  | awaitWait {tid : TaskId} {et : Expr} :
      tasks[tid]? = some et →
      ¬ IsTerminal et →
      BlockedOnTask tasks (.await (.taskRef tid))
  | tuple {es : List Expr} :
      BlockedOnTaskList tasks es →
      BlockedOnTask tasks (.tuple es)
  | blockCons {e1 e2 : Expr} {es : List Expr} :
      BlockedOnTask tasks e1 →
      BlockedOnTask tasks (.block (e1 :: e2 :: es))
  | applyFn {fn : Expr} {args : List Expr} :
      BlockedOnTask tasks fn →
      BlockedOnTask tasks (.apply fn args)
  | applyArgs {fn : Expr} {args : List Expr} :
      IsValue fn →
      BlockedOnTaskList tasks args →
      BlockedOnTask tasks (.apply fn args)
  | applyDirArgs {name : Ident} {args : List Expr} :
      BlockedOnTaskList tasks args →
      BlockedOnTask tasks (.applyDir name args)
  | un {op : UnOp} {e : Expr} :
      BlockedOnTask tasks e →
      BlockedOnTask tasks (.un op e)
  | binLeft {op : BinOp} {e1 e2 : Expr} :
      BlockedOnTask tasks e1 →
      BlockedOnTask tasks (.bin op e1 e2)
  | binRight {op : BinOp} {v1 e2 : Expr} :
      op ≠ .and → op ≠ .or →
      IsValue v1 →
      BlockedOnTask tasks e2 →
      BlockedOnTask tasks (.bin op v1 e2)
  | let_ {x : Ident} {e1 e2 : Expr} :
      BlockedOnTask tasks e1 →
      BlockedOnTask tasks (.let_ x e1 e2)
  | if_ {c t e : Expr} :
      BlockedOnTask tasks c →
      BlockedOnTask tasks (.if_ c t e)
  | match_ {s : Expr} {arms : List (Pat × Expr)} :
      BlockedOnTask tasks s →
      BlockedOnTask tasks (.match_ s arms)
  | makeData {adt : Ident} {tag : Nat} {es : List Expr} :
      BlockedOnTaskList tasks es →
      BlockedOnTask tasks (.makeData adt tag es)
  | getTag {e : Expr} :
      BlockedOnTask tasks e →
      BlockedOnTask tasks (.getTag e)
  | cellNew {e : Expr} :
      BlockedOnTask tasks e →
      BlockedOnTask tasks (.cellNew e)
  | cellGet {e : Expr} :
      BlockedOnTask tasks e →
      BlockedOnTask tasks (.cellGet e)
  | cellSetLeft {e1 e2 : Expr} :
      BlockedOnTask tasks e1 →
      BlockedOnTask tasks (.cellSet e1 e2)
  | cellSetRight {v1 e2 : Expr} :
      IsValue v1 →
      BlockedOnTask tasks e2 →
      BlockedOnTask tasks (.cellSet v1 e2)
  | spawn {e : Expr} :
      BlockedOnTask tasks e →
      BlockedOnTask tasks (.spawn e)
  | awaitStep {e : Expr} :
      BlockedOnTask tasks e →
      BlockedOnTask tasks (.await e)

inductive BlockedOnTaskList (tasks : List Expr) : List Expr → Prop where
  | head {e : Expr} {es : List Expr} :
      BlockedOnTask tasks e →
      BlockedOnTaskList tasks (e :: es)
  | tail {v : Expr} {es : List Expr} :
      IsValue v →
      BlockedOnTaskList tasks es →
      BlockedOnTaskList tasks (v :: es)
end

/-- A thread is stuck (undefined behavior) if it is neither terminal, nor
    legitimately waiting on a running `Task`, nor able to take a step. -/
def IsStuck (Δ : AdtEnv) (Φ : FunEnv) (tasks : List Expr) (e : Expr) (σ : Store) : Prop :=
  ¬ IsTerminal e ∧ ¬ BlockedOnTask tasks e ∧ ¬ ∃ e' σ' sp, Step Δ Φ tasks e σ e' σ' sp

/-! ## Interleaved Concurrent Task-Pool Semantics & Data Races -/

/-- Nondeterministic interleaved step of any runnable thread `tid` in `tasks`. -/
inductive ConcStep (Δ : AdtEnv) (Φ : FunEnv) : List Expr → Store → List Expr → Store → Prop where
  | stepNone {tasks : List Expr} {tid : Nat} {e e' : Expr} {σ σ' : Store} :
      tasks[tid]? = some e →
      Step Δ Φ tasks e σ e' σ' none →
      ConcStep Δ Φ tasks σ (tasks.set tid e') σ'
  | stepSpawn {tasks : List Expr} {tid : Nat} {e e' spawned : Expr} {σ σ' : Store} :
      tasks[tid]? = some e →
      Step Δ Φ tasks e σ e' σ' (some spawned) →
      ConcStep Δ Φ tasks σ ((tasks.set tid e') ++ [spawned]) σ'

/-- Reflexive-transitive closure of interleaved concurrent transitions `ConcStep`. -/
inductive ConcSteps (Δ : AdtEnv) (Φ : FunEnv) : List Expr → Store → List Expr → Store → Prop where
  | refl (tasks : List Expr) (σ : Store) : ConcSteps Δ Φ tasks σ tasks σ
  | trans {t1 t2 t3 : List Expr} {σ1 σ2 σ3 : Store} :
      ConcStep Δ Φ t1 σ1 t2 σ2 →
      ConcSteps Δ Φ t2 σ2 t3 σ3 →
      ConcSteps Δ Φ t1 σ1 t3 σ3

/-- Sequential single-thread multi-step execution (special case with no task pool). -/
inductive Steps (Δ : AdtEnv) (Φ : FunEnv) : Expr → Store → Expr → Store → Prop where
  | refl (e : Expr) (σ : Store) : Steps Δ Φ e σ e σ
  | trans {e1 e2 e3 : Expr} {σ1 σ2 σ3 : Store} :
      Step Δ Φ [] e1 σ1 e2 σ2 none →
      Steps Δ Φ e2 σ2 e3 σ3 →
      Steps Δ Φ e1 σ1 e3 σ3

/- Active memory access (`isWrite = false` for `cellGet`, `isWrite = true` for
   `cellSet`) at the current redex of a thread expression. -/
mutual
inductive ActiveCellAccess (isWrite : Bool) : Expr → Loc → Prop where
  | read (l : Loc) :
      isWrite = false →
      ActiveCellAccess isWrite (.cellGet (.loc l)) l
  | write (l : Loc) {v : Expr} :
      isWrite = true →
      IsValue v →
      ActiveCellAccess isWrite (.cellSet (.loc l) v) l
  | tuple {es : List Expr} {l : Loc} :
      ActiveCellAccessList isWrite es l →
      ActiveCellAccess isWrite (.tuple es) l
  | blockCons {e1 e2 : Expr} {es : List Expr} {l : Loc} :
      ActiveCellAccess isWrite e1 l →
      ActiveCellAccess isWrite (.block (e1 :: e2 :: es)) l
  | applyFn {fn : Expr} {args : List Expr} {l : Loc} :
      ActiveCellAccess isWrite fn l →
      ActiveCellAccess isWrite (.apply fn args) l
  | applyArgs {fn : Expr} {args : List Expr} {l : Loc} :
      IsValue fn →
      ActiveCellAccessList isWrite args l →
      ActiveCellAccess isWrite (.apply fn args) l
  | applyDirArgs {name : Ident} {args : List Expr} {l : Loc} :
      ActiveCellAccessList isWrite args l →
      ActiveCellAccess isWrite (.applyDir name args) l
  | un {op : UnOp} {e : Expr} {l : Loc} :
      ActiveCellAccess isWrite e l →
      ActiveCellAccess isWrite (.un op e) l
  | binLeft {op : BinOp} {e1 e2 : Expr} {l : Loc} :
      ActiveCellAccess isWrite e1 l →
      ActiveCellAccess isWrite (.bin op e1 e2) l
  | binRight {op : BinOp} {v1 e2 : Expr} {l : Loc} :
      op ≠ .and → op ≠ .or →
      IsValue v1 →
      ActiveCellAccess isWrite e2 l →
      ActiveCellAccess isWrite (.bin op v1 e2) l
  | let_ {x : Ident} {e1 e2 : Expr} {l : Loc} :
      ActiveCellAccess isWrite e1 l →
      ActiveCellAccess isWrite (.let_ x e1 e2) l
  | if_ {c t e : Expr} {l : Loc} :
      ActiveCellAccess isWrite c l →
      ActiveCellAccess isWrite (.if_ c t e) l
  | match_ {s : Expr} {arms : List (Pat × Expr)} {l : Loc} :
      ActiveCellAccess isWrite s l →
      ActiveCellAccess isWrite (.match_ s arms) l
  | makeData {adt : Ident} {tag : Nat} {es : List Expr} {l : Loc} :
      ActiveCellAccessList isWrite es l →
      ActiveCellAccess isWrite (.makeData adt tag es) l
  | getTag {e : Expr} {l : Loc} :
      ActiveCellAccess isWrite e l →
      ActiveCellAccess isWrite (.getTag e) l
  | cellNew {e : Expr} {l : Loc} :
      ActiveCellAccess isWrite e l →
      ActiveCellAccess isWrite (.cellNew e) l
  | cellGetStep {e : Expr} {l : Loc} :
      ActiveCellAccess isWrite e l →
      ActiveCellAccess isWrite (.cellGet e) l
  | cellSetLeft {e1 e2 : Expr} {l : Loc} :
      ActiveCellAccess isWrite e1 l →
      ActiveCellAccess isWrite (.cellSet e1 e2) l
  | cellSetRight {v1 e2 : Expr} {l : Loc} :
      IsValue v1 →
      ActiveCellAccess isWrite e2 l →
      ActiveCellAccess isWrite (.cellSet v1 e2) l
  | spawn {e : Expr} {l : Loc} :
      ActiveCellAccess isWrite e l →
      ActiveCellAccess isWrite (.spawn e) l
  | awaitStep {e : Expr} {l : Loc} :
      ActiveCellAccess isWrite e l →
      ActiveCellAccess isWrite (.await e) l

inductive ActiveCellAccessList (isWrite : Bool) : List Expr → Loc → Prop where
  | head {e : Expr} {es : List Expr} {l : Loc} :
      ActiveCellAccess isWrite e l →
      ActiveCellAccessList isWrite (e :: es) l
  | tail {v : Expr} {es : List Expr} {l : Loc} :
      IsValue v →
      ActiveCellAccessList isWrite es l →
      ActiveCellAccessList isWrite (v :: es) l
end

/-- A concurrent task pool has a **data race** if two distinct threads `i ≠ j`
    are simultaneously poised to access the same `Cell` location `l` with at
    least one write (`cellSet`). -/
def HasDataRace (tasks : List Expr) : Prop :=
  ∃ (i j : Nat) (ei ej : Expr) (b1 b2 : Bool) (l : Loc),
    i ≠ j ∧
    tasks[i]? = some ei ∧
    tasks[j]? = some ej ∧
    ActiveCellAccess b1 ei l ∧
    ActiveCellAccess b2 ej l ∧
    (b1 = true ∨ b2 = true)

end CoreGeisha
