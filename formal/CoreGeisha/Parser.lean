import CoreGeisha.Syntax
import CoreGeisha.Checker

/-!
# Core Geisha: `.gscore` S-Expression Parser

Parses the serialized Core IR emitted by `geisha.gsa --dump-core <file>` into
`CoreGeisha.Program` (including closure capture modes `local`/`shared` and
concurrent `task`/`spawn`/`await`) for verified checking by `CoreGeisha.checkProgram`.
-/

namespace CoreGeisha.Parser

inductive SExpr where
  | atom : String → SExpr
  | str : String → SExpr
  | list : List SExpr → SExpr
  deriving Repr

private def isSpace (c : Char) : Bool :=
  c == ' ' || c == '\n' || c == '\r' || c == '\t'

private def parseStringLit (cs : List Char) (acc : List Char) : Except String (String × List Char) :=
  match cs with
  | [] => .error "unterminated string literal"
  | '"' :: rest => .ok (String.ofList acc.reverse, rest)
  | '\\' :: 'n' :: rest => parseStringLit rest ('\n' :: acc)
  | '\\' :: 'r' :: rest => parseStringLit rest ('\r' :: acc)
  | '\\' :: 't' :: rest => parseStringLit rest ('\t' :: acc)
  | '\\' :: '"' :: rest => parseStringLit rest ('"' :: acc)
  | '\\' :: '\\' :: rest => parseStringLit rest ('\\' :: acc)
  | '\\' :: c :: rest => parseStringLit rest (c :: acc)
  | c :: rest => parseStringLit rest (c :: acc)

private def readAtom (cs : List Char) (acc : List Char) : String × List Char :=
  match cs with
  | [] => (String.ofList acc.reverse, [])
  | c :: rest =>
    if isSpace c || c == '(' || c == ')' || c == '"' then
      (String.ofList acc.reverse, c :: rest)
    else
      readAtom rest (c :: acc)

private partial def skipWs (cs : List Char) : List Char :=
  match cs with
  | [] => []
  | ';' :: rest =>
    let rest' := rest.dropWhile (fun c => c != '\n')
    skipWs rest'
  | c :: rest =>
    if isSpace c then skipWs rest else c :: rest

mutual
private partial def parseSExpr (cs : List Char) : Except String (SExpr × List Char) :=
  match skipWs cs with
  | [] => .error "unexpected EOF"
  | '(' :: rest =>
    match parseSExprList rest [] with
    | .ok (xs, rest') => .ok (.list xs, rest')
    | .error e => .error e
  | ')' :: _ => .error "unexpected ')'"
  | '"' :: rest =>
    match parseStringLit rest [] with
    | .ok (s, rest') => .ok (.str s, rest')
    | .error e => .error e
  | c :: rest =>
    let (a, rest') := readAtom (c :: rest) []
    .ok (.atom a, rest')

private partial def parseSExprList (cs : List Char) (acc : List SExpr) :
    Except String (List SExpr × List Char) :=
  match skipWs cs with
  | [] => .error "unterminated '('"
  | ')' :: rest => .ok (acc.reverse, rest)
  | other =>
    match parseSExpr other with
    | .error e => .error e
    | .ok (x, rest') => parseSExprList rest' (x :: acc)
end

private def expectStr : SExpr → Except String String
  | .str s => .ok s
  | .atom s => .ok s
  | other => .error s!"expected string, got {repr other}"

private def expectNat : SExpr → Except String Nat
  | .atom s =>
    match s.toNat? with
    | some n => .ok n
    | none => .error s!"expected nat, got '{s}'"
  | other => .error s!"expected nat, got {repr other}"

private def expectInt32 : SExpr → Except String Int32
  | .atom s =>
    match s.toInt? with
    | some n => .ok (Int32.ofInt n)
    | none => .error s!"expected int32, got '{s}'"
  | other => .error s!"expected int32, got {repr other}"

private def parseMode : SExpr → Except String Mode
  | .atom "local" => .ok .local
  | .atom "shared" => .ok .shared
  | other => .error s!"invalid closure mode (expected 'local' or 'shared'): {repr other}"

private partial def parseTy : SExpr → Except String Ty
  | .atom "void" => .ok .void
  | .atom "int" => .ok .int
  | .atom "bool" => .ok .bool
  | .atom "str" => .ok .str
  | .list (.atom "tuple" :: ts) => do
    let ts' ← ts.mapM parseTy
    pure (.tuple ts')
  | .list [.atom "fn", mode, .list ps, ret] => do
    let m ← parseMode mode
    let ps' ← ps.mapM parseTy
    let ret' ← parseTy ret
    pure (.fn m ps' ret')
  | .list [.atom "fn", .list ps, ret] => do
    let ps' ← ps.mapM parseTy
    let ret' ← parseTy ret
    pure (.fn .local ps' ret')
  | .list [.atom "adt", name] => do
    let n ← expectStr name
    pure (.adt n)
  | .list [.atom "cell", t] => do
    let t' ← parseTy t
    pure (.cell t')
  | .list [.atom "task", t] => do
    let t' ← parseTy t
    pure (.task t')
  | other => .error s!"invalid type: {repr other}"

private def parseUnOp : String → Except String UnOp
  | "not" => .ok .not
  | "neg" => .ok .neg
  | "bitNot" => .ok .bitNot
  | s => .error s!"unknown unary op '{s}'"

private def parseBinOp : String → Except String BinOp
  | "add" => .ok .add
  | "sub" => .ok .sub
  | "mul" => .ok .mul
  | "div" => .ok .div
  | "rem" => .ok .rem
  | "bitAnd" => .ok .bitAnd
  | "bitOr" => .ok .bitOr
  | "bitXor" => .ok .bitXor
  | "eqInt" => .ok .eqInt
  | "neInt" => .ok .neInt
  | "ltInt" => .ok .ltInt
  | "leInt" => .ok .leInt
  | "gtInt" => .ok .gtInt
  | "geInt" => .ok .geInt
  | "eqBool" => .ok .eqBool
  | "eqStr" => .ok .eqStr
  | "strConcat" => .ok .strConcat
  | "and" => .ok .and
  | "or" => .ok .or
  | s => .error s!"unknown binary op '{s}'"

private def parseLit : SExpr → Except String Lit
  | .list [.atom "lit-int", n] => do pure (.int (← expectInt32 n))
  | .list [.atom "lit-bool", .atom "true"] => .ok (.bool true)
  | .list [.atom "lit-bool", .atom "false"] => .ok (.bool false)
  | .list [.atom "lit-str", s] => do pure (.str (← expectStr s))
  | .list [.atom "lit-unit"] => .ok .unit
  | other => .error s!"invalid literal: {repr other}"

private partial def parsePat : SExpr → Except String Pat
  | .atom "wild" => .ok .wild
  | .list [.atom "pvar", x] => do pure (.var (← expectStr x))
  | .list [.atom "plit", l] => do pure (.lit (← parseLit l))
  | .list (.atom "ptuple" :: ps) => do pure (.tuple (← ps.mapM parsePat))
  | .list (.atom "pctor" :: adt :: tag :: ps) => do
    let a ← expectStr adt
    let t ← expectNat tag
    let ps' ← ps.mapM parsePat
    pure (.ctor a t ps')
  | other => .error s!"invalid pattern: {repr other}"

private def parseParam : SExpr → Except String (Ident × Ty)
  | .list [x, t] => do pure (← expectStr x, ← parseTy t)
  | other => .error s!"invalid param: {repr other}"

private partial def parseExpr : SExpr → Except String Expr
  | .list [.atom "lit-int", n] => do pure (.lit (.int (← expectInt32 n)))
  | .list [.atom "lit-bool", .atom "true"] => .ok (.lit (.bool true))
  | .list [.atom "lit-bool", .atom "false"] => .ok (.lit (.bool false))
  | .list [.atom "lit-str", s] => do pure (.lit (.str (← expectStr s)))
  | .list [.atom "lit-unit"] => .ok (.lit .unit)
  | .list [.atom "var", x] => do pure (.var (← expectStr x))
  | .list (.atom "tuple" :: es) => do pure (.tuple (← es.mapM parseExpr))
  | .list (.atom "block" :: es) => do pure (.block (← es.mapM parseExpr))
  | .list [.atom "lam", mode, .list ps, ret, body] => do
    let m ← parseMode mode
    let ps' ← ps.mapM parseParam
    let ret' ← parseTy ret
    let body' ← parseExpr body
    pure (.lam m ps' ret' body')
  | .list [.atom "lam", .list ps, ret, body] => do
    let ps' ← ps.mapM parseParam
    let ret' ← parseTy ret
    let body' ← parseExpr body
    pure (.lam .local ps' ret' body')
  | .list (.atom "apply" :: fn :: args) => do
    pure (.apply (← parseExpr fn) (← args.mapM parseExpr))
  | .list (.atom "apply-dir" :: name :: args) => do
    pure (.applyDir (← expectStr name) (← args.mapM parseExpr))
  | .list [.atom "bin", .atom op, e1, e2] => do
    pure (.bin (← parseBinOp op) (← parseExpr e1) (← parseExpr e2))
  | .list [.atom "un", .atom op, e] => do
    pure (.un (← parseUnOp op) (← parseExpr e))
  | .list [.atom "let", x, e1, e2] => do
    pure (.let_ (← expectStr x) (← parseExpr e1) (← parseExpr e2))
  | .list [.atom "if", c, t, e] => do
    pure (.if_ (← parseExpr c) (← parseExpr t) (← parseExpr e))
  | .list [.atom "while", c, b] => do
    pure (.while_ (← parseExpr c) (← parseExpr b))
  | .list (.atom "match" :: scrut :: arms) => do
    let s ← parseExpr scrut
    let arms' ← arms.mapM fun
      | .list [.atom "arm", p, b] => do pure (← parsePat p, ← parseExpr b)
      | other => .error s!"invalid match arm: {repr other}"
    pure (.match_ s arms')
  | .list (.atom "make-data" :: adt :: tag :: es) => do
    pure (.makeData (← expectStr adt) (← expectNat tag) (← es.mapM parseExpr))
  | .list [.atom "get-tag", e] => do pure (.getTag (← parseExpr e))
  | .list [.atom "cell-new", e] => do pure (.cellNew (← parseExpr e))
  | .list [.atom "cell-get", e] => do pure (.cellGet (← parseExpr e))
  | .list [.atom "cell-set", e1, e2] => do pure (.cellSet (← parseExpr e1) (← parseExpr e2))
  | .list [.atom "spawn", e] => do pure (.spawn (← parseExpr e))
  | .list [.atom "await", e] => do pure (.await (← parseExpr e))
  | other => .error s!"invalid expr: {repr other}"

private def parseVariant : SExpr → Except String VariantDef
  | .list (.atom "variant" :: tag :: flds) => do
    pure { tag := ← expectNat tag, fields := ← flds.mapM parseTy }
  | other => .error s!"invalid variant: {repr other}"

private def parseAdt : SExpr → Except String AdtDef
  | .list (.atom "adt" :: name :: vars) => do
    pure { name := ← expectStr name, variants := ← vars.mapM parseVariant }
  | other => .error s!"invalid adt: {repr other}"

private def parseFun : SExpr → Except String FunDef
  | .list [.atom "fun", name, .list ps, ret, body] => do
    pure {
      name := ← expectStr name
      params := ← ps.mapM parseParam
      retTy := ← parseTy ret
      body := ← parseExpr body
    }
  | other => .error s!"invalid fun: {repr other}"

def parseProgram (src : String) : Except String Program := do
  let (sexpr, rest) ← parseSExpr src.toList
  match skipWs rest with
  | [] =>
    match sexpr with
    | .list [.atom "program", .list (.atom "adts" :: adts), .list (.atom "funs" :: funs)] => do
      let adts' ← adts.mapM parseAdt
      let funs' ← funs.mapM parseFun
      pure { adts := adts', funs := funs' }
    | other => .error s!"expected (program (adts ...) (funs ...)), got {repr other}"
  | _ => .error "trailing tokens after top-level program"

end CoreGeisha.Parser
