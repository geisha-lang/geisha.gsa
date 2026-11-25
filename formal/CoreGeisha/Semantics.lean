import CoreGeisha.Syntax

/-!
# Core Geisha: Small-Step Operational Semantics

Strict left-to-right call-by-value small-step operational semantics
`Step Δ Φ e σ e' σ'` with:
- Wrapping 32-bit two's-complement arithmetic (`Int32`)
- Explicit division/remainder-by-zero traps (`Trap.divByZero`)
- Short-circuit `&&` and `||`
- Deterministic pattern matching (`matchPat`) with explicit `Trap.matchFailure`
- Explicit mutable store operations (`cellNew`, `cellGet`, `cellSet`)
- Strict trap propagation through all evaluation contexts
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

/- Small-step operational semantics `⟨e, σ⟩ ⟶ ⟨e', σ'⟩`. -/
mutual
inductive Step (Δ : AdtEnv) (Φ : FunEnv) : Expr → Store → Expr → Store → Prop where
  -- Tuple: strict left-to-right
  | tupleStep {es es' : List Expr} {σ σ' : Store} :
      StepList Δ Φ es σ es' σ' →
      Step Δ Φ (.tuple es) σ (.tuple es') σ'
  | tupleTrap {es : List Expr} {t : Trap} {σ : Store} :
      ListFirstTrap es t →
      Step Δ Φ (.tuple es) σ (.trap t) σ

  -- Block: sequential evaluation
  | blockEmpty {σ : Store} :
      Step Δ Φ (.block []) σ (.lit .unit) σ
  | blockSingle {e : Expr} {σ : Store} :
      Step Δ Φ (.block [e]) σ e σ
  | blockConsStep {e1 e1' e2 : Expr} {es : List Expr} {σ σ' : Store} :
      Step Δ Φ e1 σ e1' σ' →
      Step Δ Φ (.block (e1 :: e2 :: es)) σ (.block (e1' :: e2 :: es)) σ'
  | blockConsVal {v1 e2 : Expr} {es : List Expr} {σ : Store} :
      IsValue v1 →
      Step Δ Φ (.block (v1 :: e2 :: es)) σ (.block (e2 :: es)) σ
  | blockConsTrap {t : Trap} {e2 : Expr} {es : List Expr} {σ : Store} :
      Step Δ Φ (.block (.trap t :: e2 :: es)) σ (.trap t) σ

  -- Closure application: callee first, then args left-to-right, then β-reduction
  | applyFn {fn fn' : Expr} {args : List Expr} {σ σ' : Store} :
      Step Δ Φ fn σ fn' σ' →
      Step Δ Φ (.apply fn args) σ (.apply fn' args) σ'
  | applyFnTrap {t : Trap} {args : List Expr} {σ : Store} :
      Step Δ Φ (.apply (.trap t) args) σ (.trap t) σ
  | applyArgs {fn : Expr} {args args' : List Expr} {σ σ' : Store} :
      IsValue fn →
      StepList Δ Φ args σ args' σ' →
      Step Δ Φ (.apply fn args) σ (.apply fn args') σ'
  | applyArgsTrap {fn : Expr} {args : List Expr} {t : Trap} {σ : Store} :
      IsValue fn →
      ListFirstTrap args t →
      Step Δ Φ (.apply fn args) σ (.trap t) σ
  | applyBeta {ps : List (Ident × Ty)} {ret : Ty} {body : Expr} {args : List Expr} {σ : Store} :
      (∀ a ∈ args, IsValue a) →
      args.length = ps.length →
      Step Δ Φ (.apply (.lam ps ret body) args) σ (substMany (zipParams ps args) body) σ

  -- Direct top-level function call (`TmApplyDir`)
  | applyDirArgs {name : Ident} {args args' : List Expr} {σ σ' : Store} :
      StepList Δ Φ args σ args' σ' →
      Step Δ Φ (.applyDir name args) σ (.applyDir name args') σ'
  | applyDirTrap {name : Ident} {args : List Expr} {t : Trap} {σ : Store} :
      ListFirstTrap args t →
      Step Δ Φ (.applyDir name args) σ (.trap t) σ
  | applyDirBeta {name : Ident} {fd : FunDef} {args : List Expr} {σ : Store} :
      Φ name = some fd →
      (∀ a ∈ args, IsValue a) →
      args.length = fd.params.length →
      Step Δ Φ (.applyDir name args) σ (substMany (zipParams fd.params args) fd.body) σ

  -- Unary operators
  | unStep {op : UnOp} {e e' : Expr} {σ σ' : Store} :
      Step Δ Φ e σ e' σ' →
      Step Δ Φ (.un op e) σ (.un op e') σ'
  | unTrap {op : UnOp} {t : Trap} {σ : Store} :
      Step Δ Φ (.un op (.trap t)) σ (.trap t) σ
  | unVal {op : UnOp} {l l' : Lit} {σ : Store} :
      evalUnOp op l = some l' →
      Step Δ Φ (.un op (.lit l)) σ (.lit l') σ

  -- Binary operators (short-circuit for && and ||; strict left-to-right for all others)
  | binLeft {op : BinOp} {e1 e1' e2 : Expr} {σ σ' : Store} :
      Step Δ Φ e1 σ e1' σ' →
      Step Δ Φ (.bin op e1 e2) σ (.bin op e1' e2) σ'
  | binLeftTrap {op : BinOp} {t : Trap} {e2 : Expr} {σ : Store} :
      Step Δ Φ (.bin op (.trap t) e2) σ (.trap t) σ
  | binAndFalse {e2 : Expr} {σ : Store} :
      Step Δ Φ (.bin .and (.lit (.bool false)) e2) σ (.lit (.bool false)) σ
  | binAndTrue {e2 : Expr} {σ : Store} :
      Step Δ Φ (.bin .and (.lit (.bool true)) e2) σ e2 σ
  | binOrTrue {e2 : Expr} {σ : Store} :
      Step Δ Φ (.bin .or (.lit (.bool true)) e2) σ (.lit (.bool true)) σ
  | binOrFalse {e2 : Expr} {σ : Store} :
      Step Δ Φ (.bin .or (.lit (.bool false)) e2) σ e2 σ
  | binRight {op : BinOp} {v1 e2 e2' : Expr} {σ σ' : Store} :
      op ≠ .and → op ≠ .or →
      IsValue v1 →
      Step Δ Φ e2 σ e2' σ' →
      Step Δ Φ (.bin op v1 e2) σ (.bin op v1 e2') σ'
  | binRightTrap {op : BinOp} {v1 : Expr} {t : Trap} {σ : Store} :
      op ≠ .and → op ≠ .or →
      IsValue v1 →
      Step Δ Φ (.bin op v1 (.trap t)) σ (.trap t) σ
  | binVal {op : BinOp} {l1 l2 l' : Lit} {σ : Store} :
      evalBinOp op l1 l2 = some (.val l') →
      Step Δ Φ (.bin op (.lit l1) (.lit l2)) σ (.lit l') σ
  | binTrap {op : BinOp} {l1 l2 : Lit} {t : Trap} {σ : Store} :
      evalBinOp op l1 l2 = some (.trap t) →
      Step Δ Φ (.bin op (.lit l1) (.lit l2)) σ (.trap t) σ

  -- Let binding
  | letStep {x : Ident} {e1 e1' e2 : Expr} {σ σ' : Store} :
      Step Δ Φ e1 σ e1' σ' →
      Step Δ Φ (.let_ x e1 e2) σ (.let_ x e1' e2) σ'
  | letTrap {x : Ident} {t : Trap} {e2 : Expr} {σ : Store} :
      Step Δ Φ (.let_ x (.trap t) e2) σ (.trap t) σ
  | letVal {x : Ident} {v1 e2 : Expr} {σ : Store} :
      IsValue v1 →
      Step Δ Φ (.let_ x v1 e2) σ (subst x v1 e2) σ

  -- Conditional
  | ifStep {c c' t e : Expr} {σ σ' : Store} :
      Step Δ Φ c σ c' σ' →
      Step Δ Φ (.if_ c t e) σ (.if_ c' t e) σ'
  | ifTrap {tr : Trap} {t e : Expr} {σ : Store} :
      Step Δ Φ (.if_ (.trap tr) t e) σ (.trap tr) σ
  | ifTrue {t e : Expr} {σ : Store} :
      Step Δ Φ (.if_ (.lit (.bool true)) t e) σ t σ
  | ifFalse {t e : Expr} {σ : Store} :
      Step Δ Φ (.if_ (.lit (.bool false)) t e) σ e σ

  -- While loop (unfolds to `if c { b; while c b } else ()`)
  | whileUnfold {c b : Expr} {σ : Store} :
      Step Δ Φ (.while_ c b) σ (.if_ c (.block [b, .while_ c b]) (.lit .unit)) σ

  -- Pattern matching
  | matchScrut {s s' : Expr} {arms : List (Pat × Expr)} {σ σ' : Store} :
      Step Δ Φ s σ s' σ' →
      Step Δ Φ (.match_ s arms) σ (.match_ s' arms) σ'
  | matchScrutTrap {t : Trap} {arms : List (Pat × Expr)} {σ : Store} :
      Step Δ Φ (.match_ (.trap t) arms) σ (.trap t) σ
  | matchEmpty {v : Expr} {σ : Store} :
      IsValue v →
      Step Δ Φ (.match_ v []) σ (.trap .matchFailure) σ
  | matchHit {v : Expr} {p : Pat} {body : Expr} {rest : List (Pat × Expr)}
      {env : List (Ident × Expr)} {σ : Store} :
      IsValue v →
      matchPat p v = some env →
      Step Δ Φ (.match_ v ((p, body) :: rest)) σ (substMany env body) σ
  | matchMiss {v : Expr} {p : Pat} {body : Expr} {rest : List (Pat × Expr)} {σ : Store} :
      IsValue v →
      matchPat p v = none →
      Step Δ Φ (.match_ v ((p, body) :: rest)) σ (.match_ v rest) σ

  -- ADT construction & tag inspection
  | makeDataStep {adt : Ident} {tag : Nat} {es es' : List Expr} {σ σ' : Store} :
      StepList Δ Φ es σ es' σ' →
      Step Δ Φ (.makeData adt tag es) σ (.makeData adt tag es') σ'
  | makeDataTrap {adt : Ident} {tag : Nat} {es : List Expr} {t : Trap} {σ : Store} :
      ListFirstTrap es t →
      Step Δ Φ (.makeData adt tag es) σ (.trap t) σ
  | getTagStep {e e' : Expr} {σ σ' : Store} :
      Step Δ Φ e σ e' σ' →
      Step Δ Φ (.getTag e) σ (.getTag e') σ'
  | getTagTrap {t : Trap} {σ : Store} :
      Step Δ Φ (.getTag (.trap t)) σ (.trap t) σ
  | getTagVal {adt : Ident} {tag : Nat} {vs : List Expr} {σ : Store} :
      (∀ v ∈ vs, IsValue v) →
      Step Δ Φ (.getTag (.makeData adt tag vs)) σ (.lit (.int (Int32.ofNat tag))) σ

  -- Mutable Cell store operations
  | cellNewStep {e e' : Expr} {σ σ' : Store} :
      Step Δ Φ e σ e' σ' →
      Step Δ Φ (.cellNew e) σ (.cellNew e') σ'
  | cellNewTrap {t : Trap} {σ : Store} :
      Step Δ Φ (.cellNew (.trap t)) σ (.trap t) σ
  | cellNewVal {v : Expr} {σ : Store} :
      IsValue v →
      Step Δ Φ (.cellNew v) σ (.loc σ.length) (σ ++ [v])
  | cellGetStep {e e' : Expr} {σ σ' : Store} :
      Step Δ Φ e σ e' σ' →
      Step Δ Φ (.cellGet e) σ (.cellGet e') σ'
  | cellGetTrap {t : Trap} {σ : Store} :
      Step Δ Φ (.cellGet (.trap t)) σ (.trap t) σ
  | cellGetVal {l : Loc} {v : Expr} {σ : Store} :
      σ[l]? = some v →
      Step Δ Φ (.cellGet (.loc l)) σ v σ
  | cellSetLeft {e1 e1' e2 : Expr} {σ σ' : Store} :
      Step Δ Φ e1 σ e1' σ' →
      Step Δ Φ (.cellSet e1 e2) σ (.cellSet e1' e2) σ'
  | cellSetLeftTrap {t : Trap} {e2 : Expr} {σ : Store} :
      Step Δ Φ (.cellSet (.trap t) e2) σ (.trap t) σ
  | cellSetRight {v1 e2 e2' : Expr} {σ σ' : Store} :
      IsValue v1 →
      Step Δ Φ e2 σ e2' σ' →
      Step Δ Φ (.cellSet v1 e2) σ (.cellSet v1 e2') σ'
  | cellSetRightTrap {v1 : Expr} {t : Trap} {σ : Store} :
      IsValue v1 →
      Step Δ Φ (.cellSet v1 (.trap t)) σ (.trap t) σ
  | cellSetVal {l : Loc} {v : Expr} {σ : Store} :
      l < σ.length →
      IsValue v →
      Step Δ Φ (.cellSet (.loc l) v) σ (.lit .unit) (σ.set l v)

inductive StepList (Δ : AdtEnv) (Φ : FunEnv) :
    List Expr → Store → List Expr → Store → Prop where
  | head {e e' : Expr} {es : List Expr} {σ σ' : Store} :
      Step Δ Φ e σ e' σ' →
      StepList Δ Φ (e :: es) σ (e' :: es) σ'
  | tail {v : Expr} {es es' : List Expr} {σ σ' : Store} :
      IsValue v →
      StepList Δ Φ es σ es' σ' →
      StepList Δ Φ (v :: es) σ (v :: es') σ'
end

/-- Reflexive-transitive closure of `Step`. -/
inductive Steps (Δ : AdtEnv) (Φ : FunEnv) : Expr → Store → Expr → Store → Prop where
  | refl (e : Expr) (σ : Store) : Steps Δ Φ e σ e σ
  | trans {e1 e2 e3 : Expr} {σ1 σ2 σ3 : Store} :
      Step Δ Φ e1 σ1 e2 σ2 →
      Steps Δ Φ e2 σ2 e3 σ3 →
      Steps Δ Φ e1 σ1 e3 σ3

/-- A configuration is terminal if it is either a value or a defined runtime trap. -/
def IsTerminal (e : Expr) : Prop :=
  IsValue e ∨ ∃ t, e = .trap t

/-- A configuration is stuck (undefined behavior) if it is neither terminal nor able to step. -/
def IsStuck (Δ : AdtEnv) (Φ : FunEnv) (e : Expr) (σ : Store) : Prop :=
  ¬ IsTerminal e ∧ ¬ ∃ e' σ', Step Δ Φ e σ e' σ'

end CoreGeisha
