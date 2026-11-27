import CoreGeisha.Syntax
import CoreGeisha.Escape
import CoreGeisha.Checker

/-!
# Core Geisha: `.gscore` S-Expression Parser

Parses the serialized Core IR emitted by `geisha.gsa --dump-core <file>` into
`CoreGeisha.Program` (including closure capture modes `local`/`shared`,
concurrent `Task`/`MVar`/`Chan`/`Actor` types & primitives, and
`(stack-allocs ...)` escape annotations) for verified checking by
`CoreGeisha.checkProgram`.
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

private def expectInt64 : SExpr → Except String Int64
  | .atom s =>
    match s.toInt? with
    | some n => .ok (Int64.ofInt n)
    | none => .error s!"expected int64, got '{s}'"
  | other => .error s!"expected int64, got {repr other}"

private def expectUInt32 : SExpr → Except String UInt32
  | .atom s =>
    match s.toInt? with
    | some n => .ok (Int32.ofInt n).toUInt32
    | none => .error s!"expected uint32, got '{s}'"
  | other => .error s!"expected uint32, got {repr other}"

private def expectUInt64 : SExpr → Except String UInt64
  | .atom s =>
    match s.toInt? with
    | some n => .ok (Int64.ofInt n).toUInt64
    | none => .error s!"expected uint64, got '{s}'"
  | other => .error s!"expected uint64, got {repr other}"

private def parseMode : SExpr → Except String Mode
  | .atom "local" => .ok .local
  | .atom "shared" => .ok .shared
  | other => .error s!"invalid closure mode (expected 'local' or 'shared'): {repr other}"

private partial def parseTy : SExpr → Except String Ty
  | .atom "void" => .ok .void
  | .atom "int" => .ok .int
  | .atom "int64" => .ok .int64
  | .atom "float" => .ok .float
  | .atom "float32" => .ok .float32
  | .atom "bool" => .ok .bool
  | .atom "char" => .ok .char
  | .atom "str" => .ok .str
  | .atom "ptr" => .ok .ptr
  | .atom "scoped-ptr" => .ok .scopedPtr
  | .atom "arena" => .ok .arena
  | .atom "foreign-ptr" => .ok .foreignPtr
  | .atom "atomic-int" => .ok .atomicInt
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
  | .list [.atom "simd128", spec] => do
    let s ← expectStr spec
    pure (.simd128 s)
  | .list [.atom "simd256", spec] => do
    let s ← expectStr spec
    pure (.simd256 s)
  | .list [.atom "cell", t] => do
    let t' ← parseTy t
    pure (.cell t')
  | .list [.atom "mut-array", t] => do
    let t' ← parseTy t
    pure (.mutArray t')
  | .list [.atom "imm-array", t] => do
    let t' ← parseTy t
    pure (.immArray t')
  | .list [.atom "task", t] => do
    let t' ← parseTy t
    pure (.task t')
  | .list [.atom "mvar", t] => do
    let t' ← parseTy t
    pure (.mvar t')
  | .list [.atom "chan", t] => do
    let t' ← parseTy t
    pure (.chan t')
  | .list [.atom "actor", t] => do
    let t' ← parseTy t
    pure (.actor t')
  | other => .error s!"invalid type: {repr other}"

private def parseConcPrim : SExpr → Except String ConcPrim
  | .atom "mvar-new" => .ok .mvarNew
  | .list [.atom "mvar-empty", t] => do pure (.mvarEmpty (← parseTy t))
  | .atom "mvar-take" => .ok .mvarTake
  | .atom "mvar-put" => .ok .mvarPut
  | .list [.atom "chan-new", t] => do pure (.chanNew (← parseTy t))
  | .atom "chan-send" => .ok .chanSend
  | .list [.atom "chan-recv", optAdt] => do pure (.chanRecv (← expectStr optAdt))
  | .atom "chan-close" => .ok .chanClose
  | .atom "actor-spawn" => .ok .actorSpawn
  | .atom "actor-call" => .ok .actorCall
  | .atom "actor-send" => .ok .actorSend
  | other => .error s!"invalid conc-prim operator: {repr other}"

private def parseUnOp : String → Except String UnOp
  | "not" => .ok .not
  | "neg" => .ok .neg
  | "bitNot" => .ok .bitNot
  | "neg64" => .ok .neg64
  | "bitNot64" => .ok .bitNot64
  | "negFloat" => .ok .negFloat
  | "negFloat32" => .ok .negFloat32
  | "intToI64" => .ok .intToI64
  | "i64ToInt" => .ok .i64ToInt
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
  | "shlInt" => .ok .shlInt
  | "shrInt" => .ok .shrInt
  | "ushrInt" => .ok .ushrInt
  | "eqInt" => .ok .eqInt
  | "neInt" => .ok .neInt
  | "ltInt" => .ok .ltInt
  | "leInt" => .ok .leInt
  | "gtInt" => .ok .gtInt
  | "geInt" => .ok .geInt
  | "add64" => .ok .add64
  | "sub64" => .ok .sub64
  | "mul64" => .ok .mul64
  | "div64" => .ok .div64
  | "rem64" => .ok .rem64
  | "bitAnd64" => .ok .bitAnd64
  | "bitOr64" => .ok .bitOr64
  | "bitXor64" => .ok .bitXor64
  | "shl64" => .ok .shl64
  | "shr64" => .ok .shr64
  | "ushr64" => .ok .ushr64
  | "eq64" => .ok .eq64
  | "ne64" => .ok .ne64
  | "lt64" => .ok .lt64
  | "le64" => .ok .le64
  | "gt64" => .ok .gt64
  | "ge64" => .ok .ge64
  | "addFloat" => .ok .addFloat
  | "subFloat" => .ok .subFloat
  | "mulFloat" => .ok .mulFloat
  | "divFloat" => .ok .divFloat
  | "eqFloat" => .ok .eqFloat
  | "neFloat" => .ok .neFloat
  | "ltFloat" => .ok .ltFloat
  | "leFloat" => .ok .leFloat
  | "gtFloat" => .ok .gtFloat
  | "geFloat" => .ok .geFloat
  | "addF32" => .ok .addF32
  | "subF32" => .ok .subF32
  | "mulF32" => .ok .mulF32
  | "divF32" => .ok .divF32
  | "eqF32" => .ok .eqF32
  | "neF32" => .ok .neF32
  | "ltF32" => .ok .ltF32
  | "leF32" => .ok .leF32
  | "gtF32" => .ok .gtF32
  | "geF32" => .ok .geF32
  | "eqBool" => .ok .eqBool
  | "neBool" => .ok .neBool
  | "bitAndBool" => .ok .bitAndBool
  | "bitOrBool" => .ok .bitOrBool
  | "bitXorBool" => .ok .bitXorBool
  | "eqChar" => .ok .eqChar
  | "neChar" => .ok .neChar
  | "ltChar" => .ok .ltChar
  | "leChar" => .ok .leChar
  | "gtChar" => .ok .gtChar
  | "geChar" => .ok .geChar
  | "eqStr" => .ok .eqStr
  | "neStr" => .ok .neStr
  | "ltStr" => .ok .ltStr
  | "leStr" => .ok .leStr
  | "gtStr" => .ok .gtStr
  | "geStr" => .ok .geStr
  | "strConcat" => .ok .strConcat
  | "and" => .ok .and
  | "or" => .ok .or
  | s => .error s!"unknown binary op '{s}'"

private def parseLit : SExpr → Except String Lit
  | .list [.atom "lit-int", n] => do pure (.int (← expectInt32 n))
  | .list [.atom "lit-int64", n] => do pure (.int64 (← expectInt64 n))
  | .list [.atom "lit-float-bits", n] => do pure (.floatBits (← expectUInt64 n))
  | .list [.atom "lit-f32-bits", n] => do pure (.float32Bits (← expectUInt32 n))
  | .list [.atom "lit-bool", .atom "true"] => .ok (.bool true)
  | .list [.atom "lit-bool", .atom "false"] => .ok (.bool false)
  | .list [.atom "lit-char", n] => do pure (.char (← expectUInt32 n))
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
  | .list [.atom "lit-int64", n] => do pure (.lit (.int64 (← expectInt64 n)))
  | .list [.atom "lit-float-bits", n] => do pure (.lit (.floatBits (← expectUInt64 n)))
  | .list [.atom "lit-f32-bits", n] => do pure (.lit (.float32Bits (← expectUInt32 n)))
  | .list [.atom "lit-bool", .atom "true"] => .ok (.lit (.bool true))
  | .list [.atom "lit-bool", .atom "false"] => .ok (.lit (.bool false))
  | .list [.atom "lit-char", n] => do pure (.lit (.char (← expectUInt32 n)))
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
  | .list (.atom "conc-prim" :: prim :: args) => do
    pure (.concPrim (← parseConcPrim prim) (← args.mapM parseExpr))
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

private def parseExtern : SExpr → Except String ExternDecl
  | .list [.atom "extern", name, .list ps, ret] => do
    pure {
      name := ← expectStr name
      params := ← ps.mapM parseParam
      retTy := ← parseTy ret
    }
  | other => .error s!"invalid extern: {repr other}"

private def parseStackSpec : SExpr → Except String FnStackSpec
  | .list (.atom "fn-stack" :: fnName :: vars) => do
    pure {
      fnName := ← expectStr fnName
      vars := ← vars.mapM expectStr
    }
  | other => .error s!"invalid fn-stack entry: {repr other}"

private def parseVariantGcMaskSpec : SExpr → Except String VariantGcMaskSpec
  | .atom "static" => .ok .staticNullary
  | .atom "unboxed" => .ok .unboxedValue
  | .atom "conservative" => .ok .conservative
  | .list [.atom "mask", n] => do pure (.exactMask (← expectNat n))
  | other => .error s!"invalid vmask spec: {repr other}"

private def parseVmaskEntry : SExpr → Except String (Nat × VariantGcMaskSpec)
  | .list [.atom "vmask", tag, spec] => do
    pure (← expectNat tag, ← parseVariantGcMaskSpec spec)
  | other => .error s!"invalid vmask entry: {repr other}"

private def parseAdtGcMaskSpec : SExpr → Except String AdtGcMaskSpec
  | .list (.atom "adt-masks" :: .atom "cstruct" :: name :: vs) => do
    pure {
      adtName := ← expectStr name
      isCStruct := true
      variants := ← vs.mapM parseVmaskEntry
    }
  | .list (.atom "adt-masks" :: name :: vs) => do
    pure {
      adtName := ← expectStr name
      isCStruct := false
      variants := ← vs.mapM parseVmaskEntry
    }
  | other => .error s!"invalid adt-masks entry: {repr other}"

private def parseProgramSections (sects : List SExpr) : Except String Program := do
  let mut adts : Option (List AdtDef) := none
  let mut funs : Option (List FunDef) := none
  let mut externs : List ExternDecl := []
  let mut stackAllocs : List FnStackSpec := []
  let mut gcMasks : List AdtGcMaskSpec := []
  let mut hasGcMasks : Bool := false
  for s in sects do
    match s with
    | .list (.atom "adts" :: xs) =>
      adts := some (← xs.mapM parseAdt)
    | .list (.atom "externs" :: xs) =>
      externs := ← xs.mapM parseExtern
    | .list (.atom "funs" :: xs) =>
      funs := some (← xs.mapM parseFun)
    | .list (.atom "stack-allocs" :: xs) =>
      stackAllocs := ← xs.mapM parseStackSpec
    | .list (.atom "gc-masks" :: xs) =>
      gcMasks := ← xs.mapM parseAdtGcMaskSpec
      hasGcMasks := true
    | other =>
      throw s!"unknown program section: {repr other}"
  match adts, funs with
  | some a, some f =>
    pure {
      adts := a
      funs := f
      externs := externs
      stackAllocs := stackAllocs
      gcMasks := gcMasks
      hasGcMasks := hasGcMasks
    }
  | _, _ =>
    throw "program requires both (adts ...) and (funs ...) sections"

def parseProgram (src : String) : Except String Program := do
  let (sexpr, rest) ← parseSExpr src.toList
  match skipWs rest with
  | [] =>
    match sexpr with
    | .list (.atom "program" :: sects) => parseProgramSections sects
    | other => .error s!"expected (program ...), got {repr other}"
  | _ => .error "trailing tokens after top-level program"

end CoreGeisha.Parser
