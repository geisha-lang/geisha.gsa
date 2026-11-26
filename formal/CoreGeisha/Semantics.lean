import CoreGeisha.Syntax
import CoreGeisha.Typing

/-!
# Core Geisha: Small-Step & Full Concurrent (`Task` + `MVar` + `Chan` + `Actor`) Semantics

Strict left-to-right call-by-value small-step operational semantics
`Step Δ Φ pool e σ e' σ' eff` and interleaved concurrent pool semantics
`ConcStep Δ Φ pool σ pool' σ'` with:
- Wrapping 32-bit two's-complement arithmetic (`Int32`)
- Explicit division/remainder-by-zero traps (`Trap.divByZero`)
- Short-circuit `&&` and `||`
- Deterministic pattern matching (`matchPat`) with explicit `Trap.matchFailure`
- Explicit mutable store operations (`cellNew`, `cellGet`, `cellSet`)
- Concurrent `Task` (`spawn` / `await`), single-slot synchronized `MVar`,
  bounded & unbounded MPMC `Chan`, and thread-pinned sequential `Actor`s
  encapsulating `!Send` state (`ActorState`, `ActorPhase`)
- Explicit active memory-access characterization (`ActiveCellAccess`, `HasDataRace`)
  across all running tasks and actors (`ThreadId`)
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

/-! ## Concurrent Synchronization & Sequential Actor Pool (`ConcPool`) -/

/-- Entry in the global `Task` table: either a directly scheduled expression
    or a pending future awaiting completion of a sequential `Actor` call. -/
inductive TaskEntry where
  | running (e : Expr)
  | pendingReply
  deriving Repr

/-- Bounded (`cap > 0`) or unbounded (`cap = 0`) typed MPMC channel state. -/
structure ChanState where
  cap    : Nat
  buf    : List Expr
  closed : Bool
  deriving Repr

/-- Queued message in a thread-pinned `Actor`'s FIFO mailbox. -/
structure ActorMsg where
  handler   : Expr
  replyTask : Option TaskId
  deriving Repr

/-- Lifecycle phase of a sequential `Actor` thread. -/
inductive ActorPhase where
  | init (e : Expr)
  | idle (stateVal : Expr)
  | busy (stateVal : Expr) (e : Expr) (reply : Option TaskId)
  | failed (t : Trap)
  deriving Repr

/-- State of a thread-pinned `Actor` (`phase` + FIFO `mailbox`). -/
structure ActorState where
  phase   : ActorPhase
  mailbox : List ActorMsg
  deriving Repr

/-- Global concurrent pool holding all `Task`s, `MVar`s, `Chan`s, and `Actor`s. -/
structure ConcPool where
  tasks  : List TaskEntry := []
  mvars  : List (Option Expr) := []
  chans  : List ChanState := []
  actors : List ActorState := []
  deriving Repr

/-- Empty concurrent pool (for sequential execution). -/
def emptyPool : ConcPool := {}

/-- Initial concurrent pool containing a single root task `e0` (`main`). -/
def initPool (e0 : Expr) : ConcPool :=
  { tasks := [.running e0] }

/-- Heap `Cell` locations syntactically embedded in an `Actor`'s active/idle phase. -/
def actorPhaseLocs : ActorPhase → List Loc
  | .init e => exprLocs e
  | .idle sv => exprLocs sv
  | .busy sv e _ => exprLocs sv ++ exprLocs e
  | .failed _ => []

/-- Atomic pool side-effect emitted by a single thread step `Step`. -/
inductive ConcEff where
  | none : ConcEff
  | spawnTask (body : Expr) : ConcEff
  | allocMVar (init : Option Expr) : ConcEff
  | takeMVar (mid : Nat) : ConcEff
  | putMVar (mid : Nat) (val : Expr) : ConcEff
  | allocChan (cap : Nat) : ConcEff
  | sendChan (cid : Nat) (val : Expr) : ConcEff
  | recvChan (cid : Nat) : ConcEff
  | closeChan (cid : Nat) : ConcEff
  | spawnActor (initExpr : Expr) : ConcEff
  | callActor (aid : Nat) (handler : Expr) : ConcEff
  | sendActor (aid : Nat) (handler : Expr) : ConcEff
  deriving Repr

/-- Apply an atomic `ConcEff` to a `ConcPool`. -/
def applyConcEff (pool : ConcPool) : ConcEff → ConcPool
  | .none => pool
  | .spawnTask body =>
    { pool with tasks := pool.tasks ++ [.running body] }
  | .allocMVar init =>
    { pool with mvars := pool.mvars ++ [init] }
  | .takeMVar mid =>
    { pool with mvars := pool.mvars.set mid none }
  | .putMVar mid val =>
    { pool with mvars := pool.mvars.set mid (some val) }
  | .allocChan cap =>
    { pool with chans := pool.chans ++ [{ cap := cap, buf := [], closed := false }] }
  | .sendChan cid val =>
    match pool.chans[cid]? with
    | some ch => { pool with chans := pool.chans.set cid { ch with buf := ch.buf ++ [val] } }
    | none => pool
  | .recvChan cid =>
    match pool.chans[cid]? with
    | some ch => { pool with chans := pool.chans.set cid { ch with buf := ch.buf.tail } }
    | none => pool
  | .closeChan cid =>
    match pool.chans[cid]? with
    | some ch => { pool with chans := pool.chans.set cid { ch with closed := true } }
    | none => pool
  | .spawnActor initExpr =>
    { pool with actors := pool.actors ++ [{ phase := .init initExpr, mailbox := [] }] }
  | .callActor aid handler =>
    let replyTid := pool.tasks.length
    match pool.actors[aid]? with
    | some act =>
      { pool with
        tasks := pool.tasks ++ [.pendingReply]
        actors := pool.actors.set aid
          { act with mailbox := act.mailbox ++ [{ handler := handler, replyTask := some replyTid }] } }
    | none => pool
  | .sendActor aid handler =>
    match pool.actors[aid]? with
    | some act =>
      { pool with
        actors := pool.actors.set aid
          { act with mailbox := act.mailbox ++ [{ handler := handler, replyTask := none }] } }
    | none => pool

/-- Atomic transition for fully-evaluated `ConcPrim` arguments. -/
inductive StepConcPrim (pool : ConcPool) : ConcPrim → List Expr → Expr → ConcEff → Prop where
  | mvarNew {v : Expr} :
      IsValue v →
      StepConcPrim pool .mvarNew [v] (.syncRef .mvar pool.mvars.length) (.allocMVar (some v))
  | mvarEmpty (τ : Ty) :
      StepConcPrim pool (.mvarEmpty τ) [] (.syncRef .mvar pool.mvars.length) (.allocMVar none)
  | mvarTake {mid : Nat} {v : Expr} :
      pool.mvars[mid]? = some (some v) →
      StepConcPrim pool .mvarTake [.syncRef .mvar mid] v (.takeMVar mid)
  | mvarPut {mid : Nat} {v : Expr} :
      pool.mvars[mid]? = some none →
      IsValue v →
      StepConcPrim pool .mvarPut [.syncRef .mvar mid, v] (.lit .unit) (.putMVar mid v)
  | chanNew (τ : Ty) (n : Int32) :
      StepConcPrim pool (.chanNew τ) [.lit (.int n)]
        (.syncRef .chan pool.chans.length) (.allocChan n.toInt.toNat)
  | chanSendClosed {cid : Nat} {ch : ChanState} {v : Expr} :
      pool.chans[cid]? = some ch →
      ch.closed = true →
      IsValue v →
      StepConcPrim pool .chanSend [.syncRef .chan cid, v] (.lit (.bool false)) .none
  | chanSendOpen {cid : Nat} {ch : ChanState} {v : Expr} :
      pool.chans[cid]? = some ch →
      ch.closed = false →
      (ch.cap = 0 ∨ ch.buf.length < ch.cap) →
      IsValue v →
      StepConcPrim pool .chanSend [.syncRef .chan cid, v] (.lit (.bool true)) (.sendChan cid v)
  | chanRecvVal {optAdt : Ident} {cid : Nat} {ch : ChanState} {v : Expr} {rest : List Expr} :
      pool.chans[cid]? = some ch →
      ch.buf = v :: rest →
      StepConcPrim pool (.chanRecv optAdt) [.syncRef .chan cid] (.makeData optAdt 1 [v]) (.recvChan cid)
  | chanRecvClosed {optAdt : Ident} {cid : Nat} {ch : ChanState} :
      pool.chans[cid]? = some ch →
      ch.buf = [] →
      ch.closed = true →
      StepConcPrim pool (.chanRecv optAdt) [.syncRef .chan cid] (.makeData optAdt 0 []) .none
  | chanClose {cid : Nat} {ch : ChanState} :
      pool.chans[cid]? = some ch →
      StepConcPrim pool .chanClose [.syncRef .chan cid] (.lit .unit) (.closeChan cid)
  | actorSpawn {fn : Expr} :
      IsValue fn →
      StepConcPrim pool .actorSpawn [fn]
        (.syncRef .actor pool.actors.length) (.spawnActor (.apply fn []))
  | actorCall {aid : Nat} {act : ActorState} {fn : Expr} :
      pool.actors[aid]? = some act →
      IsValue fn →
      StepConcPrim pool .actorCall [.syncRef .actor aid, fn]
        (.taskRef pool.tasks.length) (.callActor aid fn)
  | actorSend {aid : Nat} {act : ActorState} {fn : Expr} :
      pool.actors[aid]? = some act →
      IsValue fn →
      StepConcPrim pool .actorSend [.syncRef .actor aid, fn]
        (.lit .unit) (.sendActor aid fn)

/- Single-thread small-step transition `Step Δ Φ pool e σ e' σ' eff`,
   parameterized by a read-only snapshot of the current `pool : ConcPool`,
   producing an optional pool side-effect `eff : ConcEff`. -/
mutual
inductive Step (Δ : AdtEnv) (Φ : FunEnv) (pool : ConcPool) :
    Expr → Store → Expr → Store → ConcEff → Prop where
  -- Tuple: strict left-to-right
  | tupleStep {es es' : List Expr} {σ σ' : Store} {eff : ConcEff} :
      StepList Δ Φ pool es σ es' σ' eff →
      Step Δ Φ pool (.tuple es) σ (.tuple es') σ' eff
  | tupleTrap {es : List Expr} {t : Trap} {σ : Store} :
      ListFirstTrap es t →
      Step Δ Φ pool (.tuple es) σ (.trap t) σ .none

  -- Block: sequential evaluation
  | blockEmpty {σ : Store} :
      Step Δ Φ pool (.block []) σ (.lit .unit) σ .none
  | blockSingle {e : Expr} {σ : Store} :
      Step Δ Φ pool (.block [e]) σ e σ .none
  | blockConsStep {e1 e1' e2 : Expr} {es : List Expr} {σ σ' : Store} {eff : ConcEff} :
      Step Δ Φ pool e1 σ e1' σ' eff →
      Step Δ Φ pool (.block (e1 :: e2 :: es)) σ (.block (e1' :: e2 :: es)) σ' eff
  | blockConsVal {v1 e2 : Expr} {es : List Expr} {σ : Store} :
      IsValue v1 →
      Step Δ Φ pool (.block (v1 :: e2 :: es)) σ (.block (e2 :: es)) σ .none
  | blockConsTrap {t : Trap} {e2 : Expr} {es : List Expr} {σ : Store} :
      Step Δ Φ pool (.block (.trap t :: e2 :: es)) σ (.trap t) σ .none

  -- Closure application: callee first, then args left-to-right, then β-reduction
  | applyFn {fn fn' : Expr} {args : List Expr} {σ σ' : Store} {eff : ConcEff} :
      Step Δ Φ pool fn σ fn' σ' eff →
      Step Δ Φ pool (.apply fn args) σ (.apply fn' args) σ' eff
  | applyFnTrap {t : Trap} {args : List Expr} {σ : Store} :
      Step Δ Φ pool (.apply (.trap t) args) σ (.trap t) σ .none
  | applyArgs {fn : Expr} {args args' : List Expr} {σ σ' : Store} {eff : ConcEff} :
      IsValue fn →
      StepList Δ Φ pool args σ args' σ' eff →
      Step Δ Φ pool (.apply fn args) σ (.apply fn args') σ' eff
  | applyArgsTrap {fn : Expr} {args : List Expr} {t : Trap} {σ : Store} :
      IsValue fn →
      ListFirstTrap args t →
      Step Δ Φ pool (.apply fn args) σ (.trap t) σ .none
  | applyBeta {m : Mode} {ps : List (Ident × Ty)} {ret : Ty} {body : Expr}
      {args : List Expr} {σ : Store} :
      (∀ a ∈ args, IsValue a) →
      args.length = ps.length →
      Step Δ Φ pool (.apply (.lam m ps ret body) args) σ (substMany (zipParams ps args) body) σ .none

  -- Direct top-level function call (`TmApplyDir`)
  | applyDirArgs {name : Ident} {args args' : List Expr} {σ σ' : Store} {eff : ConcEff} :
      StepList Δ Φ pool args σ args' σ' eff →
      Step Δ Φ pool (.applyDir name args) σ (.applyDir name args') σ' eff
  | applyDirTrap {name : Ident} {args : List Expr} {t : Trap} {σ : Store} :
      ListFirstTrap args t →
      Step Δ Φ pool (.applyDir name args) σ (.trap t) σ .none
  | applyDirBeta {name : Ident} {fd : FunDef} {args : List Expr} {σ : Store} :
      Φ name = some fd →
      (∀ a ∈ args, IsValue a) →
      args.length = fd.params.length →
      Step Δ Φ pool (.applyDir name args) σ (substMany (zipParams fd.params args) fd.body) σ .none

  -- Unary operators
  | unStep {op : UnOp} {e e' : Expr} {σ σ' : Store} {eff : ConcEff} :
      Step Δ Φ pool e σ e' σ' eff →
      Step Δ Φ pool (.un op e) σ (.un op e') σ' eff
  | unTrap {op : UnOp} {t : Trap} {σ : Store} :
      Step Δ Φ pool (.un op (.trap t)) σ (.trap t) σ .none
  | unVal {op : UnOp} {l l' : Lit} {σ : Store} :
      evalUnOp op l = some l' →
      Step Δ Φ pool (.un op (.lit l)) σ (.lit l') σ .none

  -- Binary operators (short-circuit for && and ||; strict left-to-right for all others)
  | binLeft {op : BinOp} {e1 e1' e2 : Expr} {σ σ' : Store} {eff : ConcEff} :
      Step Δ Φ pool e1 σ e1' σ' eff →
      Step Δ Φ pool (.bin op e1 e2) σ (.bin op e1' e2) σ' eff
  | binLeftTrap {op : BinOp} {t : Trap} {e2 : Expr} {σ : Store} :
      Step Δ Φ pool (.bin op (.trap t) e2) σ (.trap t) σ .none
  | binAndFalse {e2 : Expr} {σ : Store} :
      Step Δ Φ pool (.bin .and (.lit (.bool false)) e2) σ (.lit (.bool false)) σ .none
  | binAndTrue {e2 : Expr} {σ : Store} :
      Step Δ Φ pool (.bin .and (.lit (.bool true)) e2) σ e2 σ .none
  | binOrTrue {e2 : Expr} {σ : Store} :
      Step Δ Φ pool (.bin .or (.lit (.bool true)) e2) σ (.lit (.bool true)) σ .none
  | binOrFalse {e2 : Expr} {σ : Store} :
      Step Δ Φ pool (.bin .or (.lit (.bool false)) e2) σ e2 σ .none
  | binRight {op : BinOp} {v1 e2 e2' : Expr} {σ σ' : Store} {eff : ConcEff} :
      op ≠ .and → op ≠ .or →
      IsValue v1 →
      Step Δ Φ pool e2 σ e2' σ' eff →
      Step Δ Φ pool (.bin op v1 e2) σ (.bin op v1 e2') σ' eff
  | binRightTrap {op : BinOp} {v1 : Expr} {t : Trap} {σ : Store} :
      op ≠ .and → op ≠ .or →
      IsValue v1 →
      Step Δ Φ pool (.bin op v1 (.trap t)) σ (.trap t) σ .none
  | binVal {op : BinOp} {l1 l2 l' : Lit} {σ : Store} :
      evalBinOp op l1 l2 = some (.val l') →
      Step Δ Φ pool (.bin op (.lit l1) (.lit l2)) σ (.lit l') σ .none
  | binTrap {op : BinOp} {l1 l2 : Lit} {t : Trap} {σ : Store} :
      evalBinOp op l1 l2 = some (.trap t) →
      Step Δ Φ pool (.bin op (.lit l1) (.lit l2)) σ (.trap t) σ .none

  -- Let binding
  | letStep {x : Ident} {e1 e1' e2 : Expr} {σ σ' : Store} {eff : ConcEff} :
      Step Δ Φ pool e1 σ e1' σ' eff →
      Step Δ Φ pool (.let_ x e1 e2) σ (.let_ x e1' e2) σ' eff
  | letTrap {x : Ident} {t : Trap} {e2 : Expr} {σ : Store} :
      Step Δ Φ pool (.let_ x (.trap t) e2) σ (.trap t) σ .none
  | letVal {x : Ident} {v1 e2 : Expr} {σ : Store} :
      IsValue v1 →
      Step Δ Φ pool (.let_ x v1 e2) σ (subst x v1 e2) σ .none

  -- Conditional
  | ifStep {c c' t e : Expr} {σ σ' : Store} {eff : ConcEff} :
      Step Δ Φ pool c σ c' σ' eff →
      Step Δ Φ pool (.if_ c t e) σ (.if_ c' t e) σ' eff
  | ifTrap {tr : Trap} {t e : Expr} {σ : Store} :
      Step Δ Φ pool (.if_ (.trap tr) t e) σ (.trap tr) σ .none
  | ifTrue {t e : Expr} {σ : Store} :
      Step Δ Φ pool (.if_ (.lit (.bool true)) t e) σ t σ .none
  | ifFalse {t e : Expr} {σ : Store} :
      Step Δ Φ pool (.if_ (.lit (.bool false)) t e) σ e σ .none

  -- While loop (unfolds to `if c { b; while c b } else ()`)
  | whileUnfold {c b : Expr} {σ : Store} :
      Step Δ Φ pool (.while_ c b) σ (.if_ c (.block [b, .while_ c b]) (.lit .unit)) σ .none

  -- Pattern matching
  | matchScrut {s s' : Expr} {arms : List (Pat × Expr)} {σ σ' : Store} {eff : ConcEff} :
      Step Δ Φ pool s σ s' σ' eff →
      Step Δ Φ pool (.match_ s arms) σ (.match_ s' arms) σ' eff
  | matchScrutTrap {t : Trap} {arms : List (Pat × Expr)} {σ : Store} :
      Step Δ Φ pool (.match_ (.trap t) arms) σ (.trap t) σ .none
  | matchEmpty {v : Expr} {σ : Store} :
      IsValue v →
      Step Δ Φ pool (.match_ v []) σ (.trap .matchFailure) σ .none
  | matchHit {v : Expr} {p : Pat} {body : Expr} {rest : List (Pat × Expr)}
      {env : List (Ident × Expr)} {σ : Store} :
      IsValue v →
      matchPat p v = some env →
      Step Δ Φ pool (.match_ v ((p, body) :: rest)) σ (substMany env body) σ .none
  | matchMiss {v : Expr} {p : Pat} {body : Expr} {rest : List (Pat × Expr)} {σ : Store} :
      IsValue v →
      matchPat p v = none →
      Step Δ Φ pool (.match_ v ((p, body) :: rest)) σ (.match_ v rest) σ .none

  -- ADT construction & tag inspection
  | makeDataStep {adt : Ident} {tag : Nat} {es es' : List Expr} {σ σ' : Store} {eff : ConcEff} :
      StepList Δ Φ pool es σ es' σ' eff →
      Step Δ Φ pool (.makeData adt tag es) σ (.makeData adt tag es') σ' eff
  | makeDataTrap {adt : Ident} {tag : Nat} {es : List Expr} {t : Trap} {σ : Store} :
      ListFirstTrap es t →
      Step Δ Φ pool (.makeData adt tag es) σ (.trap t) σ .none
  | getTagStep {e e' : Expr} {σ σ' : Store} {eff : ConcEff} :
      Step Δ Φ pool e σ e' σ' eff →
      Step Δ Φ pool (.getTag e) σ (.getTag e') σ' eff
  | getTagTrap {t : Trap} {σ : Store} :
      Step Δ Φ pool (.getTag (.trap t)) σ (.trap t) σ .none
  | getTagVal {adt : Ident} {tag : Nat} {vs : List Expr} {σ : Store} :
      (∀ v ∈ vs, IsValue v) →
      Step Δ Φ pool (.getTag (.makeData adt tag vs)) σ (.lit (.int (Int32.ofNat tag))) σ .none

  -- Mutable Cell store operations
  | cellNewStep {e e' : Expr} {σ σ' : Store} {eff : ConcEff} :
      Step Δ Φ pool e σ e' σ' eff →
      Step Δ Φ pool (.cellNew e) σ (.cellNew e') σ' eff
  | cellNewTrap {t : Trap} {σ : Store} :
      Step Δ Φ pool (.cellNew (.trap t)) σ (.trap t) σ .none
  | cellNewVal {v : Expr} {σ : Store} :
      IsValue v →
      Step Δ Φ pool (.cellNew v) σ (.loc σ.length) (σ ++ [v]) .none
  | cellGetStep {e e' : Expr} {σ σ' : Store} {eff : ConcEff} :
      Step Δ Φ pool e σ e' σ' eff →
      Step Δ Φ pool (.cellGet e) σ (.cellGet e') σ' eff
  | cellGetTrap {t : Trap} {σ : Store} :
      Step Δ Φ pool (.cellGet (.trap t)) σ (.trap t) σ .none
  | cellGetVal {l : Loc} {v : Expr} {σ : Store} :
      σ[l]? = some v →
      Step Δ Φ pool (.cellGet (.loc l)) σ v σ .none
  | cellSetLeft {e1 e1' e2 : Expr} {σ σ' : Store} {eff : ConcEff} :
      Step Δ Φ pool e1 σ e1' σ' eff →
      Step Δ Φ pool (.cellSet e1 e2) σ (.cellSet e1' e2) σ' eff
  | cellSetLeftTrap {t : Trap} {e2 : Expr} {σ : Store} :
      Step Δ Φ pool (.cellSet (.trap t) e2) σ (.trap t) σ .none
  | cellSetRight {v1 e2 e2' : Expr} {σ σ' : Store} {eff : ConcEff} :
      IsValue v1 →
      Step Δ Φ pool e2 σ e2' σ' eff →
      Step Δ Φ pool (.cellSet v1 e2) σ (.cellSet v1 e2') σ' eff
  | cellSetRightTrap {v1 : Expr} {t : Trap} {σ : Store} :
      IsValue v1 →
      Step Δ Φ pool (.cellSet v1 (.trap t)) σ (.trap t) σ .none
  | cellSetVal {l : Loc} {v : Expr} {σ : Store} :
      l < σ.length →
      IsValue v →
      Step Δ Φ pool (.cellSet (.loc l) v) σ (.lit .unit) (σ.set l v) .none

  -- Concurrent task fork (`spawn`) and join (`await`)
  | spawnStep {e e' : Expr} {σ σ' : Store} {eff : ConcEff} :
      Step Δ Φ pool e σ e' σ' eff →
      Step Δ Φ pool (.spawn e) σ (.spawn e') σ' eff
  | spawnTrap {t : Trap} {σ : Store} :
      Step Δ Φ pool (.spawn (.trap t)) σ (.trap t) σ .none
  | spawnBeta {ret : Ty} {body : Expr} {σ : Store} :
      Step Δ Φ pool (.spawn (.lam .shared [] ret body)) σ
        (.taskRef pool.tasks.length) σ (.spawnTask body)
  | awaitStep {e e' : Expr} {σ σ' : Store} {eff : ConcEff} :
      Step Δ Φ pool e σ e' σ' eff →
      Step Δ Φ pool (.await e) σ (.await e') σ' eff
  | awaitTrap {t : Trap} {σ : Store} :
      Step Δ Φ pool (.await (.trap t)) σ (.trap t) σ .none
  | awaitVal {tid : TaskId} {v : Expr} {σ : Store} :
      pool.tasks[tid]? = some (.running v) →
      IsValue v →
      Step Δ Φ pool (.await (.taskRef tid)) σ v σ .none
  | awaitTaskTrap {tid : TaskId} {t : Trap} {σ : Store} :
      pool.tasks[tid]? = some (.running (.trap t)) →
      Step Δ Φ pool (.await (.taskRef tid)) σ (.trap t) σ .none

  -- Concurrent synchronization & Actor primitives (`MVar`, `Chan`, `Actor`)
  | concPrimArgs {op : ConcPrim} {args args' : List Expr} {σ σ' : Store} {eff : ConcEff} :
      StepList Δ Φ pool args σ args' σ' eff →
      Step Δ Φ pool (.concPrim op args) σ (.concPrim op args') σ' eff
  | concPrimTrap {op : ConcPrim} {args : List Expr} {t : Trap} {σ : Store} :
      ListFirstTrap args t →
      Step Δ Φ pool (.concPrim op args) σ (.trap t) σ .none
  | concPrimVal {op : ConcPrim} {args : List Expr} {e' : Expr} {σ : Store} {eff : ConcEff} :
      StepConcPrim pool op args e' eff →
      Step Δ Φ pool (.concPrim op args) σ e' σ eff

inductive StepList (Δ : AdtEnv) (Φ : FunEnv) (pool : ConcPool) :
    List Expr → Store → List Expr → Store → ConcEff → Prop where
  | head {e e' : Expr} {es : List Expr} {σ σ' : Store} {eff : ConcEff} :
      Step Δ Φ pool e σ e' σ' eff →
      StepList Δ Φ pool (e :: es) σ (e' :: es) σ' eff
  | tail {v : Expr} {es es' : List Expr} {σ σ' : Store} {eff : ConcEff} :
      IsValue v →
      StepList Δ Φ pool es σ es' σ' eff →
      StepList Δ Φ pool (v :: es) σ (v :: es') σ' eff
end

/-! ## Synchronization-Waiting Characterization & Stuckness -/

/- A thread expression is legitimately blocked on concurrent synchronization
   (`await` on a running/pending `Task`, `mvarTake` on an empty `MVar`, `mvarPut`
   on a full `MVar`, `chanSend` on a full bounded `Chan`, or `chanRecv` on an
   empty open `Chan`) inside its active evaluation context. -/
mutual
inductive BlockedOnTask (pool : ConcPool) : Expr → Prop where
  | awaitRunning {tid : TaskId} {et : Expr} :
      pool.tasks[tid]? = some (.running et) →
      ¬ IsTerminal et →
      BlockedOnTask pool (.await (.taskRef tid))
  | awaitPending {tid : TaskId} :
      pool.tasks[tid]? = some .pendingReply →
      BlockedOnTask pool (.await (.taskRef tid))
  | mvarTakeWait {mid : Nat} :
      pool.mvars[mid]? = some none →
      BlockedOnTask pool (.concPrim .mvarTake [.syncRef .mvar mid])
  | mvarPutWait {mid : Nat} {old v : Expr} :
      pool.mvars[mid]? = some (some old) →
      IsValue v →
      BlockedOnTask pool (.concPrim .mvarPut [.syncRef .mvar mid, v])
  | chanSendWait {cid : Nat} {ch : ChanState} {v : Expr} :
      pool.chans[cid]? = some ch →
      ch.closed = false →
      ¬ (ch.cap = 0 ∨ ch.buf.length < ch.cap) →
      IsValue v →
      BlockedOnTask pool (.concPrim .chanSend [.syncRef .chan cid, v])
  | chanRecvWait {optAdt : Ident} {cid : Nat} {ch : ChanState} :
      pool.chans[cid]? = some ch →
      ch.buf = [] →
      ch.closed = false →
      BlockedOnTask pool (.concPrim (.chanRecv optAdt) [.syncRef .chan cid])
  | tuple {es : List Expr} :
      BlockedOnTaskList pool es →
      BlockedOnTask pool (.tuple es)
  | blockCons {e1 e2 : Expr} {es : List Expr} :
      BlockedOnTask pool e1 →
      BlockedOnTask pool (.block (e1 :: e2 :: es))
  | applyFn {fn : Expr} {args : List Expr} :
      BlockedOnTask pool fn →
      BlockedOnTask pool (.apply fn args)
  | applyArgs {fn : Expr} {args : List Expr} :
      IsValue fn →
      BlockedOnTaskList pool args →
      BlockedOnTask pool (.apply fn args)
  | applyDirArgs {name : Ident} {args : List Expr} :
      BlockedOnTaskList pool args →
      BlockedOnTask pool (.applyDir name args)
  | un {op : UnOp} {e : Expr} :
      BlockedOnTask pool e →
      BlockedOnTask pool (.un op e)
  | binLeft {op : BinOp} {e1 e2 : Expr} :
      BlockedOnTask pool e1 →
      BlockedOnTask pool (.bin op e1 e2)
  | binRight {op : BinOp} {v1 e2 : Expr} :
      op ≠ .and → op ≠ .or →
      IsValue v1 →
      BlockedOnTask pool e2 →
      BlockedOnTask pool (.bin op v1 e2)
  | let_ {x : Ident} {e1 e2 : Expr} :
      BlockedOnTask pool e1 →
      BlockedOnTask pool (.let_ x e1 e2)
  | if_ {c t e : Expr} :
      BlockedOnTask pool c →
      BlockedOnTask pool (.if_ c t e)
  | match_ {s : Expr} {arms : List (Pat × Expr)} :
      BlockedOnTask pool s →
      BlockedOnTask pool (.match_ s arms)
  | makeData {adt : Ident} {tag : Nat} {es : List Expr} :
      BlockedOnTaskList pool es →
      BlockedOnTask pool (.makeData adt tag es)
  | getTag {e : Expr} :
      BlockedOnTask pool e →
      BlockedOnTask pool (.getTag e)
  | cellNew {e : Expr} :
      BlockedOnTask pool e →
      BlockedOnTask pool (.cellNew e)
  | cellGet {e : Expr} :
      BlockedOnTask pool e →
      BlockedOnTask pool (.cellGet e)
  | cellSetLeft {e1 e2 : Expr} :
      BlockedOnTask pool e1 →
      BlockedOnTask pool (.cellSet e1 e2)
  | cellSetRight {v1 e2 : Expr} :
      IsValue v1 →
      BlockedOnTask pool e2 →
      BlockedOnTask pool (.cellSet v1 e2)
  | spawn {e : Expr} :
      BlockedOnTask pool e →
      BlockedOnTask pool (.spawn e)
  | awaitStep {e : Expr} :
      BlockedOnTask pool e →
      BlockedOnTask pool (.await e)
  | concPrimArgs {op : ConcPrim} {args : List Expr} :
      BlockedOnTaskList pool args →
      BlockedOnTask pool (.concPrim op args)

inductive BlockedOnTaskList (pool : ConcPool) : List Expr → Prop where
  | head {e : Expr} {es : List Expr} :
      BlockedOnTask pool e →
      BlockedOnTaskList pool (e :: es)
  | tail {v : Expr} {es : List Expr} :
      IsValue v →
      BlockedOnTaskList pool es →
      BlockedOnTaskList pool (v :: es)
end

/-- A thread is stuck (undefined behavior) if it is neither terminal, nor
    legitimately waiting on a running `Task`/`MVar`/`Chan`, nor able to take a step. -/
def IsStuck (Δ : AdtEnv) (Φ : FunEnv) (pool : ConcPool) (e : Expr) (σ : Store) : Prop :=
  ¬ IsTerminal e ∧ ¬ BlockedOnTask pool e ∧ ¬ ∃ e' σ' eff, Step Δ Φ pool e σ e' σ' eff

/-! ## Concurrent Pool Well-Typedness (`PoolTyped`) -/

/-- Well-typedness of an `Actor`'s current lifecycle phase under state type `σ_ty`. -/
def ActorPhaseTyped (Δ : AdtEnv) (Φ : FunEnv) (Ψ : StoreTy) (Θ : TaskTy)
    (σ_ty : Ty) : ActorPhase → Prop
  | .init e => HasType Δ Φ Ψ Θ emptyCtx e σ_ty
  | .idle sv => IsValue sv ∧ HasType Δ Φ Ψ Θ emptyCtx sv σ_ty
  | .busy sv e none =>
    IsValue sv ∧ HasType Δ Φ Ψ Θ emptyCtx sv σ_ty ∧ HasType Δ Φ Ψ Θ emptyCtx e .void
  | .busy sv e (some tid) =>
    IsValue sv ∧ HasType Δ Φ Ψ Θ emptyCtx sv σ_ty ∧
    ∃ r_ty, Θ.tasks[tid]? = some r_ty ∧ IsSend Δ r_ty ∧ HasType Δ Φ Ψ Θ emptyCtx e r_ty
  | .failed _ => True

/-- Well-typedness of a queued `ActorMsg` in an `Actor σ_ty`'s mailbox. -/
def ActorMsgTyped (Δ : AdtEnv) (Φ : FunEnv) (Ψ : StoreTy) (Θ : TaskTy)
    (σ_ty : Ty) (msg : ActorMsg) : Prop :=
  IsValue msg.handler ∧
  match msg.replyTask with
  | none => HasType Δ Φ Ψ Θ emptyCtx msg.handler (.fn .shared [σ_ty] .void)
  | some tid =>
    ∃ r_ty, Θ.tasks[tid]? = some r_ty ∧ IsSend Δ r_ty ∧
      HasType Δ Φ Ψ Θ emptyCtx msg.handler (.fn .shared [σ_ty] r_ty)

/-- Well-typedness of the entire concurrent `ConcPool` against `Θ : TaskTy`. -/
structure PoolTyped (Δ : AdtEnv) (Φ : FunEnv) (Ψ : StoreTy) (Θ : TaskTy) (pool : ConcPool) : Prop where
  tasks_len  : pool.tasks.length = Θ.tasks.length
  tasks_ty   : ∀ (tid : TaskId) (τ : Ty), Θ.tasks[tid]? = some τ →
    IsSend Δ τ ∧ ∃ te, pool.tasks[tid]? = some te ∧
      (∀ e, te = .running e → HasType Δ Φ Ψ Θ emptyCtx e τ)
  mvars_len  : pool.mvars.length = Θ.mvars.length
  mvars_ty   : ∀ (mid : Nat) (τ : Ty), Θ.mvars[mid]? = some τ →
    IsSend Δ τ ∧ ∃ slot, pool.mvars[mid]? = some slot ∧
      (∀ v, slot = some v → IsValue v ∧ HasType Δ Φ Ψ Θ emptyCtx v τ)
  chans_len  : pool.chans.length = Θ.chans.length
  chans_ty   : ∀ (cid : Nat) (τ : Ty), Θ.chans[cid]? = some τ →
    IsSend Δ τ ∧ ∃ ch, pool.chans[cid]? = some ch ∧
      (∀ v ∈ ch.buf, IsValue v ∧ HasType Δ Φ Ψ Θ emptyCtx v τ)
  actors_len : pool.actors.length = Θ.actors.length
  actors_ty  : ∀ (aid : Nat) (σ_ty : Ty), Θ.actors[aid]? = some σ_ty →
    ∃ act, pool.actors[aid]? = some act ∧
      ActorPhaseTyped Δ Φ Ψ Θ σ_ty act.phase ∧
      (∀ msg ∈ act.mailbox, ActorMsgTyped Δ Φ Ψ Θ σ_ty msg)

/-! ## Interleaved Concurrent Pool Semantics & Data Races -/

/-- Update a task entry in `pool`. -/
def setPoolTask (pool : ConcPool) (tid : TaskId) (te : TaskEntry) : ConcPool :=
  { pool with tasks := pool.tasks.set tid te }

/-- Update an actor entry in `pool`. -/
def setPoolActor (pool : ConcPool) (aid : Nat) (st : ActorState) : ConcPool :=
  { pool with actors := pool.actors.set aid st }

/-- Update an actor's lifecycle phase in `pool` while preserving its mailbox. -/
def setPoolActorPhase (pool : ConcPool) (aid : Nat) (ph : ActorPhase) : ConcPool :=
  match pool.actors[aid]? with
  | some act => setPoolActor pool aid { act with phase := ph }
  | none => pool

/-- Nondeterministic interleaved step of any runnable `Task` or sequential `Actor` in `pool`. -/
inductive ConcStep (Δ : AdtEnv) (Φ : FunEnv) : ConcPool → Store → ConcPool → Store → Prop where
  | taskStep {pool : ConcPool} {tid : TaskId} {e e' : Expr} {σ σ' : Store} {eff : ConcEff} :
      pool.tasks[tid]? = some (.running e) →
      Step Δ Φ pool e σ e' σ' eff →
      ConcStep Δ Φ pool σ (applyConcEff (setPoolTask pool tid (.running e')) eff) σ'
  | actorInitStep {pool : ConcPool} {aid : Nat} {act : ActorState}
      {e e' : Expr} {σ σ' : Store} {eff : ConcEff} :
      pool.actors[aid]? = some act →
      act.phase = .init e →
      Step Δ Φ pool e σ e' σ' eff →
      ConcStep Δ Φ pool σ (applyConcEff (setPoolActorPhase pool aid (.init e')) eff) σ'
  | actorInitDone {pool : ConcPool} {aid : Nat} {act : ActorState} {sv : Expr} {σ : Store} :
      pool.actors[aid]? = some act →
      act.phase = .init sv →
      IsValue sv →
      ConcStep Δ Φ pool σ (setPoolActorPhase pool aid (.idle sv)) σ
  | actorInitTrap {pool : ConcPool} {aid : Nat} {act : ActorState} {t : Trap} {σ : Store} :
      pool.actors[aid]? = some act →
      act.phase = .init (.trap t) →
      ConcStep Δ Φ pool σ (setPoolActorPhase pool aid (.failed t)) σ
  | actorDequeue {pool : ConcPool} {aid : Nat} {sv : Expr}
      {msg : ActorMsg} {rest : List ActorMsg} {σ : Store} :
      pool.actors[aid]? = some { phase := .idle sv, mailbox := msg :: rest } →
      ConcStep Δ Φ pool σ
        (setPoolActor pool aid
          { phase := .busy sv (.apply msg.handler [sv]) msg.replyTask, mailbox := rest }) σ
  | actorBusyStep {pool : ConcPool} {aid : Nat} {act : ActorState}
      {sv e e' : Expr} {reply : Option TaskId} {σ σ' : Store} {eff : ConcEff} :
      pool.actors[aid]? = some act →
      act.phase = .busy sv e reply →
      Step Δ Φ pool e σ e' σ' eff →
      ConcStep Δ Φ pool σ (applyConcEff (setPoolActorPhase pool aid (.busy sv e' reply)) eff) σ'
  | actorBusyDone {pool : ConcPool} {aid : Nat} {act : ActorState}
      {sv v : Expr} {reply : Option TaskId} {σ : Store} :
      pool.actors[aid]? = some act →
      act.phase = .busy sv v reply →
      IsValue v →
      ConcStep Δ Φ pool σ
        (let p1 := setPoolActorPhase pool aid (.idle sv)
         match reply with
         | none => p1
         | some tid => setPoolTask p1 tid (.running v)) σ
  | actorBusyTrap {pool : ConcPool} {aid : Nat} {act : ActorState}
      {sv : Expr} {t : Trap} {reply : Option TaskId} {σ : Store} :
      pool.actors[aid]? = some act →
      act.phase = .busy sv (.trap t) reply →
      ConcStep Δ Φ pool σ
        (let p1 := setPoolActorPhase pool aid (.failed t)
         match reply with
         | none => p1
         | some tid => setPoolTask p1 tid (.running (.trap t))) σ
  | actorFailedReply {pool : ConcPool} {aid : Nat} {t : Trap}
      {msg : ActorMsg} {rest : List ActorMsg} {σ : Store} :
      pool.actors[aid]? = some { phase := .failed t, mailbox := msg :: rest } →
      ConcStep Δ Φ pool σ
        (let p1 := setPoolActor pool aid { phase := .failed t, mailbox := rest }
         match msg.replyTask with
         | none => p1
         | some tid => setPoolTask p1 tid (.running (.trap t))) σ

/-- Reflexive-transitive closure of interleaved concurrent transitions `ConcStep`. -/
inductive ConcSteps (Δ : AdtEnv) (Φ : FunEnv) : ConcPool → Store → ConcPool → Store → Prop where
  | refl (pool : ConcPool) (σ : Store) : ConcSteps Δ Φ pool σ pool σ
  | trans {p1 p2 p3 : ConcPool} {σ1 σ2 σ3 : Store} :
      ConcStep Δ Φ p1 σ1 p2 σ2 →
      ConcSteps Δ Φ p2 σ2 p3 σ3 →
      ConcSteps Δ Φ p1 σ1 p3 σ3

/-- Sequential single-thread multi-step execution (special case on `emptyPool`). -/
inductive Steps (Δ : AdtEnv) (Φ : FunEnv) : Expr → Store → Expr → Store → Prop where
  | refl (e : Expr) (σ : Store) : Steps Δ Φ e σ e σ
  | trans {e1 e2 e3 : Expr} {σ1 σ2 σ3 : Store} :
      Step Δ Φ emptyPool e1 σ1 e2 σ2 .none →
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
  | concPrimArgs {op : ConcPrim} {args : List Expr} {l : Loc} :
      ActiveCellAccessList isWrite args l →
      ActiveCellAccess isWrite (.concPrim op args) l

inductive ActiveCellAccessList (isWrite : Bool) : List Expr → Loc → Prop where
  | head {e : Expr} {es : List Expr} {l : Loc} :
      ActiveCellAccess isWrite e l →
      ActiveCellAccessList isWrite (e :: es) l
  | tail {v : Expr} {es : List Expr} {l : Loc} :
      IsValue v →
      ActiveCellAccessList isWrite es l →
      ActiveCellAccessList isWrite (v :: es) l
end

/-- Identifier for any concurrently executing thread (`Task` worker or sequential `Actor`). -/
inductive ThreadId where
  | task (tid : TaskId)
  | actor (aid : Nat)
  deriving Repr, BEq, DecidableEq

/-- Currently active expression executing on thread `th` in `pool` (if any). -/
def activeThreadExpr (pool : ConcPool) : ThreadId → Option Expr
  | .task tid =>
    match pool.tasks[tid]? with
    | some (.running e) => some e
    | _ => none
  | .actor aid =>
    match pool.actors[aid]? with
    | some { phase := .init e, .. } => some e
    | some { phase := .busy _ e _, .. } => some e
    | _ => none

/-- A concurrent pool has a **data race** if two distinct threads `th1 ≠ th2`
    (Task-Task, Task-Actor, or Actor-Actor) are simultaneously poised to access
    the same `Cell` location `l` with at least one write (`cellSet`). -/
def HasDataRace (pool : ConcPool) : Prop :=
  ∃ (th1 th2 : ThreadId) (e1 e2 : Expr) (b1 b2 : Bool) (l : Loc),
    th1 ≠ th2 ∧
    activeThreadExpr pool th1 = some e1 ∧
    activeThreadExpr pool th2 = some e2 ∧
    ActiveCellAccess b1 e1 l ∧
    ActiveCellAccess b2 e2 l ∧
    (b1 = true ∨ b2 = true)

end CoreGeisha
