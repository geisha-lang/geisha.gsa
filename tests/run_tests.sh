#!/bin/sh
# End-to-end test suite for the self-hosted Geisha compiler (`geisha.gsa`)
set -eu

CC="${CC:-clang}"
GEISHA_BIN="${GEISHA_BIN:-./build/geisha2}"
GEISHA_RUNTIME="${GEISHA_RUNTIME:-./build/libgeisha_runtime.a}"
export GEISHA_RUNTIME

UNAME_S="$(uname -s)"
UNAME_M="$(uname -m)"
HOST_CC_TARGET=""
HOST_CC_LIBS=""
if [ "$UNAME_S" = "Darwin" ]; then
    export MACOSX_DEPLOYMENT_TARGET=14.0
    case "$UNAME_M" in
        arm64|aarch64) HOST_CC_TARGET="-target arm64-apple-macosx14.0" ;;
        x86_64|amd64)  HOST_CC_TARGET="-target x86_64-apple-macosx14.0" ;;
    esac
else
    HOST_CC_LIBS="-lm"
fi

TMP_DIR="$(mktemp -d "${TMPDIR:-/tmp}/geisha_gsa_tests.XXXXXX")"
trap 'rm -rf "$TMP_DIR"' EXIT

PASS=0

assert_eq() {
    name="$1"
    expected="$2"
    actual="$3"
    if [ "$expected" != "$actual" ]; then
        echo "FAIL [$name]: expected '$expected', got '$actual'" >&2
        exit 1
    fi
    echo "PASS [$name]: $actual"
    PASS=$((PASS + 1))
}

# 1. ADTs, Struct `.field`, Pattern Guards, Mutual Recursion, and `?` Sugar
cat > "$TMP_DIR/t1_lang.gsa" << 'EOF'
use std.result.{Result, Ok, Err}
use std.str.{intToStr, parseInt}

data Point {
    MkPoint { px: Int, py: Int },
}

def isEven(n: Int): Bool = if (n == 0) true else isOdd(n - 1)
def isOdd(n: Int): Bool = if (n == 0) false else isEven(n - 1)

def sumCsv(items: List String): Result Int String = {
    let acc = cellNew(0);
    let cur = cellNew(items);
    while (match cellGet(cur) { Nil -> false, _ -> true }) {
        match cellGet(cur) {
            Cons(s, r) -> {
                let v = parseInt(s)?;
                cellSet(acc, cellGet(acc) + v);
                cellSet(cur, r)
            },
            Nil -> (),
        }
    };
    Ok(cellGet(acc))
}

def classify(p: Point): String = match p {
    MkPoint { px: x, py: y } if (x == y) -> "diag:" + intToStr(p.px + p.py),
    _ -> "other",
}

def main() = {
    let p = MkPoint { px: 7, py: 7 };
    let s1 = match sumCsv(["10", "20", "12"]) { Ok(v) -> v, Err(_) -> -1 };
    let s2 = match sumCsv(["10", "bad", "12"]) { Ok(_) -> "ok", Err(_) -> "err" };
    let b = if (isEven(10) && !isOdd(10)) "even" else "bad";
    printLn(classify(p) + "|" + intToStr(s1) + "|" + s2 + "|" + b)
}
EOF
"$GEISHA_BIN" -o "$TMP_DIR/t1_lang" "$TMP_DIR/t1_lang.gsa"
assert_eq "adt_field_try_mutual_rec" "diag:14|42|err|even" "$("$TMP_DIR/t1_lang")"

# 2. Open Concepts, Custom Symbolic Operators, Prefix `~`, Bitwise Ops & Int64
cat > "$TMP_DIR/t2_ops.gsa" << 'EOF'
use std.str.{intToStr, i64ToStr}
use std.bits.{popCount, trailingZeros}

data Mask { MkMask(Int) }

instance BitOr Mask {
    def (|)(a, b) = match (a, b) { (MkMask(x), MkMask(y)) -> MkMask(x | y) }
}

instance BitNot Mask {
    def (~)(a) = match a { MkMask(x) -> MkMask((~x) & 255) }
}

concept Combine a {
    def (<+>)(x: a, y: a): a
}

instance Combine Int {
    def (<+>)(x, y) = x * 10 + y
}

def applyUnary(f: Int -> Int, x: Int): Int = f(x)

def main() = {
    let m = ~(MkMask(240) | MkMask(12));
    let mv = match m { MkMask(v) -> v };
    let x64 = (intToI64(1) << 40) | intToI64(255);
    let u = (-16) >>> 28;
    let negBits = applyUnary((~), 0);
    let comb = 3 <+> 4;
    printLn(
        intToStr(mv) + "|" +
        i64ToStr(x64) + "|" +
        intToStr(u) + "|" +
        intToStr(negBits) + "|" +
        intToStr(popCount(255)) + "|" +
        intToStr(trailingZeros(16)) + "|" +
        intToStr(comb)
    )
}
EOF
"$GEISHA_BIN" -o "$TMP_DIR/t2_ops" "$TMP_DIR/t2_ops.gsa"
assert_eq "concepts_custom_and_bitwise_ops" "3|1099511628031|15|-1|8|4|34" "$("$TMP_DIR/t2_ops")"

# 3. C `extern` FFI + Float IEEE-754 Bit Intrinsics
cat > "$TMP_DIR/t3_ffi.gsa" << 'EOF'
use std.str.{intToStr, floatToHex16, parseFloat}
use std.result.{Ok, Err}

extern "abs" def c_abs(x: Int): Int
extern "strlen" def c_strlen(s: String): Int64

def main() = {
    let a = c_abs(-99);
    let n = i64ToInt(c_strlen("geisha-ffi"));
    let parsed = match parseFloat("2.5") { Ok(f) -> f * 2.0, Err(_) -> 0.0 };
    printLn(intToStr(a) + "|" + intToStr(n) + "|" + floatToHex16(parsed))
}
EOF
"$GEISHA_BIN" -o "$TMP_DIR/t3_ffi" "$TMP_DIR/t3_ffi.gsa"
assert_eq "c_extern_ffi_and_floats" "99|10|0x4014000000000000" "$("$TMP_DIR/t3_ffi")"

# 4. Multi-file Project Mode (`--src-root`) with `pub use` Re-export
mkdir -p "$TMP_DIR/proj/math"
cat > "$TMP_DIR/proj/math/inner.gsa" << 'EOF'
pub def triple(x: Int): Int = x * 3
EOF
cat > "$TMP_DIR/proj/math/mod.gsa" << 'EOF'
pub mod inner
pub use inner.triple
pub def addOne(x: Int): Int = x + 1
EOF
cat > "$TMP_DIR/proj/mod.gsa" << 'EOF'
mod math
use math.{triple, addOne}
use std.str.intToStr

def main() = printLn(intToStr(addOne(triple(13))))
EOF
"$GEISHA_BIN" --src-root "$TMP_DIR" -o "$TMP_DIR/t4_proj" "$TMP_DIR/proj/mod.gsa"
assert_eq "multifile_modules_pub_use" "40" "$("$TMP_DIR/t4_proj")"

# 5. Concurrency (`Task`, `Chan`, `Actor`)
cat > "$TMP_DIR/t5_conc.gsa" << 'EOF'
use std.task.{spawn, await}
use std.sync.{chanNew, chanSend, chanRecv}
use std.actor.{actorSpawn, actorSend, actorCall, actorStop}
use std.option.{Some, None}
use std.str.intToStr

def main() = {
    let t1 = spawn(() -> 21 * 2);
    let ch = chanNew(4);
    let _ = chanSend(ch, 100);
    let cv = match chanRecv(ch) { Some(x) -> x, None -> 0 };

    let act = actorSpawn(() -> cellNew(10));
    actorSend(act, (st) -> cellSet(st, cellGet(st) + 5));
    let av = await(actorCall(act, (st) -> cellGet(st)));
    actorStop(act);

    printLn(intToStr(await(t1)) + "|" + intToStr(cv) + "|" + intToStr(av))
}
EOF
"$GEISHA_BIN" -o "$TMP_DIR/t5_conc" "$TMP_DIR/t5_conc.gsa"
assert_eq "concurrency_task_chan_actor" "42|100|15" "$("$TMP_DIR/t5_conc")"

# 6. Negative Compile-Time Check: Non-exhaustive Pattern Match Rejected
cat > "$TMP_DIR/t6_bad.gsa" << 'EOF'
use std.option.{Option, Some, None}
def bad(x: Option Int): Int = match x {
    Some(v) -> v,
}
def main() = putNumber(bad(None))
EOF
if "$GEISHA_BIN" -o "$TMP_DIR/t6_bad" "$TMP_DIR/t6_bad.gsa" >/dev/null 2>&1; then
    echo "FAIL [non_exhaustive_rejected]: compiler unexpectedly accepted non-exhaustive match" >&2
    exit 1
fi
echo "PASS [non_exhaustive_rejected]: rejected non-exhaustive match"
PASS=$((PASS + 1))

# 7. `std.codec` + `std.json`: First-class Decoder Pipelines, `Encode` + `:=`, Tagged ADTs & Path Errors
cat > "$TMP_DIR/t7_codec_json.gsa" << 'EOF'
use std.option.{Option, Some, None}
use std.result.{Result, Ok, Err}
use std.str.intToStr
use std.codec.{
    Value, DecodeErr, Decoder, Encode, encode, formatErr,
    object, (:=), (|>),
    succeed, map, int, str, list, at, req, opt, withDefault, tagged
}
use std.json.{toJson, decodeString}

data Player {
    Player { id: String, name: String, hp: Int, title: Option String },
}

data Action {
    Move(String),
    Rest,
}

instance Encode Player {
    def encode(p) = object([
        "id"    := p.id,
        "name"  := p.name,
        "hp"    := p.hp,
        "title" := p.title,
    ])
}

def decodePlayer(): Decoder Player =
    succeed((id) -> (name) -> (hp) -> (title) -> Player {
        id: id, name: name, hp: hp, title: title
    })
        |> req("id", str)
        |> req("name", str)
        |> withDefault("hp", int, 100)
        |> opt("title", str)

def decodeAction(): Decoder Action =
    tagged("type", [
        ("move", map((d) -> Move(d), at("dir", str))),
        ("rest", succeed(Rest)),
    ])

def main() = {
    let p = Player { id: "p1", name: "Linghu", hp: 85, title: Some("Swordsman") };
    let raw = toJson(p);
    let rt = match decodeString(decodePlayer(), raw) {
        Ok(p2) -> p2.id + ":" + p2.name + ":" + intToStr(p2.hp) + ":" + match p2.title { Some(t) -> t, None -> "-" },
        Err(e) -> "ERR:" + formatErr(e),
    };

    // Missing optional + default hp + Unicode escape \u0041 ('A')
    let defRaw = "{\"id\":\"p2\",\"name\":\"\\u0041li\"}";
    let defRes = match decodeString(decodePlayer(), defRaw) {
        Ok(p2) -> p2.name + ":" + intToStr(p2.hp),
        Err(e) -> "ERR:" + formatErr(e),
    };

    // Tagged ADT sum type
    let actRes = match decodeString(decodeAction(), "{\"type\":\"move\",\"dir\":\"north\"}") {
        Ok(Move(d)) -> "move:" + d,
        Ok(Rest) -> "rest",
        Err(e) -> "ERR:" + formatErr(e),
    };

    // Nested JSONPath error reporting
    let badRes = match decodeString(at("items", list(int)), "{\"items\":[1,\"oops\",3]}") {
        Ok(_) -> "unexpected-ok",
        Err(e) -> e.path,
    };

    printLn(rt + "|" + defRes + "|" + actRes + "|" + badRes)
}
EOF
"$GEISHA_BIN" -o "$TMP_DIR/t7_codec_json" "$TMP_DIR/t7_codec_json.gsa"
assert_eq "codec_json_pipeline_and_errors" "p1:Linghu:85:Swordsman|Ali:100|move:north|$.items[1]" "$("$TMP_DIR/t7_codec_json")"

# 8. `sys.fs` (`mkdirAll`/`isDir`/`readDir`), `sys.time`, and `std.rand`
cat > "$TMP_DIR/t8_sys_rand.gsa" << 'EOF'
use std.result.{Ok, Err}
use std.list.{listLen, listAny}
use std.str.intToStr
use sys.fs.{mkdirAll, isDir, writeFile, readFile, readDir, withMmap, mmapLen, mmapByteAt}
use sys.time.{nowMs, monotonicMs}
use std.rand.{fromSeed, fromEntropy, nextInt, nextRange}

def main() = {
    let base = "TMP_FS_DIR_PLACEHOLDER";
    let nested = base + "/a/b";
    let mkOk = match mkdirAll(nested) { Ok(_) -> isDir(nested), Err(_) -> false };
    let _ = writeFile(nested + "/one.txt", "hello-mmap");
    let _ = writeFile(nested + "/two.txt", "2");
    let rfOk = match readFile(nested + "/one.txt") { Ok(s) -> s == "hello-mmap", Err(_) -> false };
    let mmOk = match withMmap(nested + "/one.txt", (m) -> i64ToInt(mmapLen(m)) == 10 && mmapByteAt(m, 0) == 104 && mmapByteAt(m, 9) == 112) {
        Ok(b) -> b,
        Err(_) -> false,
    };
    let dirOk = match readDir(nested) {
        Ok(entries) -> listLen(entries) == 2 && listAny(entries, (e) -> e == "one.txt"),
        Err(_) -> false,
    };

    let tOk = nowMs() > (intToI64(1700000000) * intToI64(1000)) && monotonicMs() >= intToI64(0);

    let r1 = fromSeed(intToI64(42));
    let (a1, r1b) = nextRange(r1, 10, 20);
    let (a2, _) = nextRange(fromSeed(intToI64(42)), 10, 20);
    let (b1, _) = nextInt(r1b, 100);
    let (_, _) = nextInt(fromEntropy(), 100);
    let randOk = (a1 == a2) && (a1 >= 10) && (a1 <= 20) && (b1 >= 0) && (b1 < 100);

    let s = (if (mkOk && rfOk && mmOk) "1" else "0") + (if (dirOk) "1" else "0") + (if (tOk) "1" else "0") + (if (randOk) "1" else "0");
    printLn(s)
}
EOF
sed "s|TMP_FS_DIR_PLACEHOLDER|$TMP_DIR/fs_test|g" "$TMP_DIR/t8_sys_rand.gsa" > "$TMP_DIR/t8_sys_rand_run.gsa"
"$GEISHA_BIN" -o "$TMP_DIR/t8_sys_rand" "$TMP_DIR/t8_sys_rand_run.gsa"
assert_eq "sys_fs_time_and_std_rand" "1111" "$("$TMP_DIR/t8_sys_rand")"

# 9. `sys.net`: Concurrent Loopback TCP + JSON Echo
cat > "$TMP_DIR/t9_tcp_loopback.gsa" << 'EOF'
use std.result.{Ok, Err}
use std.task.{spawn, await}
use std.codec.{object, (:=), at, str}
use std.json.{toJson, decodeString}
use sys.net.{tcpListen, tcpLocalPort, tcpAccept, tcpConnect, tcpRead, tcpWrite, tcpClose, tcpCloseListener}

def main() = {
    let listener = match tcpListen("127.0.0.1", 0) {
        Ok(l) -> l,
        Err(e) -> { printLn("LISTEN_ERR:" + e); l_fail() },
    };
    let port = tcpLocalPort(listener);

    let srv = spawn(() -> {
        let res = match tcpAccept(listener) {
            Err(e) -> "ACCEPT_ERR:" + e,
            Ok(stream) -> {
                let out = match tcpRead(stream, 4096) {
                    Ok(msg) -> match decodeString(at("msg", str), msg) {
                        Ok(word) -> {
                            let reply = toJson(object(["echo" := word + "!"]));
                            let _ = tcpWrite(stream, reply);
                            "srv-ok"
                        },
                        Err(_) -> "decode-err",
                    },
                    Err(_) -> "recv-err",
                };
                tcpClose(stream);
                out
            },
        };
        tcpCloseListener(listener);
        res
    });

    let cliRes = match tcpConnect("127.0.0.1", port) {
        Err(e) -> "CLI_CONN_ERR:" + e,
        Ok(conn) -> {
            let payload = toJson(object(["msg" := "tingfeng"]));
            let _ = tcpWrite(conn, payload);
            let got = match tcpRead(conn, 4096) {
                Ok(reply) -> match decodeString(at("echo", str), reply) {
                    Ok(v) -> v,
                    Err(_) -> "cli-decode-err",
                },
                Err(_) -> "cli-recv-err",
            };
            tcpClose(conn);
            got
        },
    };

    let srvRes = await(srv);
    printLn(srvRes + "|" + cliRes)
}

def l_fail(): sys.net.TcpListener = {
    let _ = arrayGet(arrayNew(0, 0), 0);
    sys.net.TcpListener(-1)
}
EOF
"$GEISHA_BIN" -o "$TMP_DIR/t9_tcp_loopback" "$TMP_DIR/t9_tcp_loopback.gsa"
assert_eq "sys_net_tcp_json_loopback" "srv-ok|tingfeng!" "$("$TMP_DIR/t9_tcp_loopback")"

# 10. Superclasses (`Functor -> Applicative -> Monad`), Multi-Param Concepts & FunDeps (`MonadState s m | m -> s`), and HKT Kinds
cat > "$TMP_DIR/t10_mtl.gsa" << 'EOF'
use std.option.{Option, Some, None}
use std.str.intToStr

concept Functor f {
    def fmap(g: a -> b, fa: f a): f b
}

concept Applicative f : Functor f {
    def pure(x: a): f a,
    def ap(ff: f (a -> b), fa: f a): f b
}

concept Monad m : Applicative m {
    def (>>=)(ma: m a, k: a -> m b): m b
}

concept MonadState s m : Monad m | m -> s {
    def get(): m s,
    def put(st: s): m Void
}

data State s a {
    MkState(s -> (a, s)),
}

def runState(st: State s a, init: s): (a, s) = match st {
    MkState(f) -> f(init),
}

instance Functor (State s) {
    def fmap(g, st) = MkState((s0) -> {
        let (a, s1) = runState(st, s0);
        (g(a), s1)
    })
}

instance Applicative (State s) {
    def pure(x) = MkState((s0) -> (x, s0))
    def ap(sf, sa) = MkState((s0) -> {
        let (f, s1) = runState(sf, s0);
        let (a, s2) = runState(sa, s1);
        (f(a), s2)
    })
}

instance Monad (State s) {
    def (>>=)(ma, k) = MkState((s0) -> {
        let (a, s1) = runState(ma, s0);
        runState(k(a), s1)
    })
}

instance MonadState s (State s) {
    def get() = MkState((s0) -> (s0, s0))
    def put(newS) = MkState((_) -> ((), newS))
}

instance Functor Option {
    def fmap(g, o) = match o { None -> None, Some(x) -> Some(g(x)) }
}

instance Applicative Option {
    def pure(x) = Some(x)
    def ap(ofn, oa) = match (ofn, oa) {
        (Some(f), Some(a)) -> Some(f(a)),
        _ -> None,
    }
}

instance Monad Option {
    def (>>=)(ma, k) = match ma { None -> None, Some(x) -> k(x) }
}

// Uses grandparent `Functor` (`fmap`), parent `Applicative` (`pure`), and `Monad` (`>>=`)
// purely from `Monad m` constraint via superclass expansion!
def tripleViaMonad(mx, step) =
    fmap((z) -> z + 1, mx >>= (x) -> step(x) >>= (y) -> pure(y * 3))

// Polymorphic MTL computation: `s` is inferred as `Int` via `m -> s` FunDep!
def incAndDouble(delta) =
    get() >>= (cur) ->
    put(cur + delta) >>= (_) ->
    get() >>= (after) ->
    pure(after * 2)

// Higher-kinded ADT (`Free : (* -> *) -> * -> *`) verified by kind inference
data Free f a {
    Pure(a),
    Bind(f (Free f a)),
}

def main() = {
    let optRes = tripleViaMonad(Some(4), (x) -> Some(x + 1));
    let optVal = match optRes { Some(v) -> v, None -> -1 };
    let (resVal, finalState) = runState(incAndDouble(5), 10);
    let freeBox: Free Option Int = Pure(7);
    let freeVal = match freeBox { Pure(x) -> x, Bind(_) -> 0 };
    printLn(intToStr(optVal) + "|" + intToStr(resVal) + "|" + intToStr(finalState) + "|" + intToStr(freeVal))
}
EOF
"$GEISHA_BIN" -o "$TMP_DIR/t10_mtl" "$TMP_DIR/t10_mtl.gsa"
assert_eq "hkt_superclasses_fundeps_mtl" "16|30|15|7" "$("$TMP_DIR/t10_mtl")"

# 11. Negative Compile-Time Checks: Kind Mismatch & Missing Superclass Instance
cat > "$TMP_DIR/t8_bad_kind.gsa" << 'EOF'
concept Functor f {
    def fmap(g: a -> b, fa: f a): f b
}
instance Functor Int {
    def fmap(g, x) = x
}
def main() = ()
EOF
if "$GEISHA_BIN" -o "$TMP_DIR/t8_bad_kind" "$TMP_DIR/t8_bad_kind.gsa" >/dev/null 2>&1; then
    echo "FAIL [kind_mismatch_rejected]: compiler unexpectedly accepted Functor Int" >&2
    exit 1
fi
echo "PASS [kind_mismatch_rejected]: rejected kind mismatch (Functor Int)"
PASS=$((PASS + 1))

cat > "$TMP_DIR/t8_bad_super.gsa" << 'EOF'
concept Functor f {
    def fmap(g: a -> b, fa: f a): f b
}
concept Monad m : Functor m {
    def pure(x: a): m a
}
data Box a { MkBox(a) }
instance Monad Box {
    def pure(x) = MkBox(x)
}
def main() = ()
EOF
if "$GEISHA_BIN" -o "$TMP_DIR/t8_bad_super" "$TMP_DIR/t8_bad_super.gsa" >/dev/null 2>&1; then
    echo "FAIL [missing_superclass_rejected]: compiler unexpectedly accepted Monad Box without Functor Box" >&2
    exit 1
fi
echo "PASS [missing_superclass_rejected]: rejected missing superclass instance"
PASS=$((PASS + 1))

# 12. `--target wasm32`: Full Geisha -> LLVM -> wasm32 -> Node.js WebAssembly E2E (ADT + JSON + Host Import/Export)
if [ -f "./build/wasm_rt.o" ] && command -v node >/dev/null 2>&1; then
cat > "$TMP_DIR/t12_wasm.gsa" << 'EOF'
use std.result.{Ok, Err}
use std.codec.{Encode, Decoder, object, (:=), (|>), succeed, req, withDefault, int, str}
use std.json.{toJson, decodeString}

extern "host_notify" def hostNotify(msg: String): Void

data Hero {
    Hero { name: String, hp: Int },
}

instance Encode Hero {
    def encode(h) = object([
        "name" := h.name,
        "hp"   := h.hp,
    ])
}

def decodeHero(): Decoder Hero =
    succeed((name) -> (hp) -> Hero { name: name, hp: hp })
        |> req("name", str)
        |> withDefault("hp", int, 100)

def counter: Cell Int = cellNew(0)

def bump(delta: Int): Int = {
    let next = cellGet(counter) + delta;
    cellSet(counter, next);
    next
}

def handle_json(raw: String): String =
    match decodeString(decodeHero(), raw) {
        Ok(h) -> {
            let boosted = Hero { name: h.name, hp: h.hp + cellGet(counter) };
            let out = toJson(boosted);
            hostNotify(out);
            out
        },
        Err(_) -> "{\"err\":\"bad\"}",
    }

def applyClosure(f: Float -> String, x: Float): String = f(x)

def float_closure_probe(tag: String, w: Float, y0: Float): String = {
    let fmt = (cx: Float) -> tag + ":" + std.str.intToStr(floatToInt(cx + w * 2.0 + y0));
    applyClosure(fmt, 10.5)
}

def scoped_capture_probe(base: Int, scale: Int): Int = {
    let fromArena = withArena((a) -> {
        let p = arenaAlloc(a, intToI64(16));
        scopedPtrWriteF32Le(p, 0, floatToF32(intToFloat(base * scale)));
        f32ToInt(scopedPtrReadF32Le(p, 0))
    });
    let fromAlloca = withAlloca(16, (p) -> {
        scopedPtrWriteF32Le(p, 0, floatToF32(intToFloat(base + scale)));
        f32ToInt(scopedPtrReadF32Le(p, 0))
    });
    let fp = foreignPtrAlloc(intToI64(16));
    let fromForeign = withForeignPtr(fp, (p) -> {
        scopedPtrWriteF32Le(p, 0, floatToF32(intToFloat(scale * 3)));
        f32ToInt(scopedPtrReadF32Le(p, 0))
    });
    let arr = parTabulate(4, (i) -> base + i * scale);
    let fromTab = immArrayGet(arr, 0) + immArrayGet(arr, 1) + immArrayGet(arr, 2) + immArrayGet(arr, 3);
    fromArena + fromAlloca + fromForeign + fromTab
}

def main(): Void = cellSet(counter, 10)
EOF
"$GEISHA_BIN" --target wasm32 --runtime ./build/wasm_rt.o -o "$TMP_DIR/t12_wasm.wasm" "$TMP_DIR/t12_wasm.gsa"
WASM_OUT="$(node -e '
const fs = require("fs");
const bytes = fs.readFileSync(process.argv[1]);
const enc = new TextEncoder();
const dec = new TextDecoder();
let mem, ex, notified = "";
const readStr = (ptr) => {
  const len = ex.gs_wasm_str_len(ptr);
  return dec.decode(new Uint8Array(mem.buffer, ptr, len));
};
const writeStr = (s) => {
  const raw = enc.encode(s);
  const ptr = ex.gs_wasm_alloc(raw.length + 1);
  const view = new Uint8Array(mem.buffer, ptr, raw.length + 1);
  view.set(raw);
  view[raw.length] = 0;
  return ptr;
};
WebAssembly.instantiate(bytes, {
  env: {
    host_notify: (ptr) => { notified = readStr(ptr); },
    gs_log: () => {},
  }
}).then(({ instance }) => {
  ex = instance.exports;
  mem = ex.memory;
  ex.__geisha_init();
  const c = ex.bump(5);
  const resPtr = ex.handle_json(writeStr("{\"name\":\"Tingfeng\"}"));
  const res = readStr(resPtr);
  const syncOk = (notified === res ? "sync" : "diff");
  const clsRes = readStr(ex.float_closure_probe(writeStr("card"), 25.0, 4.5));
  const capRes = ex.scoped_capture_probe(7, 5);
  // Verify frame-boundary mark-sweep GC reclaims transient garbage while preserving global Cell root
  let totalReclaimed = 0;
  for (let i = 0; i < 200; i++) {
    const p = ex.handle_json(writeStr("{\"name\":\"LoopFrame\"}"));
    if (ex.gs_wasm_str_len(p) <= 0) throw new Error("empty json");
    totalReclaimed += ex.gs_wasm_gc_collect();
  }
  const liveAfter = ex.gs_wasm_heap_live();
  const c2 = ex.bump(1);
  const gcOk = (totalReclaimed > 20000 && liveAfter < 4096 && c2 === 16) ? "gc-ok" : ("gc-bad:" + totalReclaimed + ":" + liveAfter + ":" + c2);
  console.log(c + "|" + res + "|" + syncOk + "|" + clsRes + "|" + capRes + "|" + gcOk);
});
' "$TMP_DIR/t12_wasm.wasm")"
assert_eq "wasm32_codec_json_and_host_ffi" '15|{"name":"Tingfeng","hp":115}|sync|card:65|120|gc-ok' "$WASM_OUT"
fi

# 13. Mode-Polymorphic `Send` Closures & Implicit Mode-Lifted ADTs (Positive + 8 Negative Soundness Checks)
cat > "$TMP_DIR/t13_send_modes_ok.gsa" << 'EOF'
use std.option.{Some, None}
use std.list.listMap
use std.str.intToStr
use std.sync.{chanNew, chanSend, chanRecv}
use std.task.{Task, spawn, await, parMap}

// Zero `=>` syntax: `Lens` automatically receives hidden capture-mode parameter!
data Lens s a {
    MkLens { viewL: s -> a, setL: (s, a) -> s },
}

data Pair {
    MkPair { fst: Int, snd: Int },
}

// Mode-polymorphic HOF: accepts both `$Local` and `$Shared` closures
def applyTwice(f: a -> a, x: a): a = f(f(x))

// Higher-order concurrency wrapper: HM automatically infers `f` must be `$Shared`!
def runAsync(f: () -> a): Task a = spawn(f)

// Conditional capture (`SendIf`): works with `Cell Int` locally AND `Int` across threads!
def makeGetter(x: a): () -> a = () -> x

def main() = {
    // 1. Local `$Local` closure with `applyTwice`, `makeGetter`, and local `Lens`
    let localAcc = cellNew(0);
    let localBump = (n: Int) -> {
        cellSet(localAcc, cellGet(localAcc) + 1);
        n + 10
    };
    let r1 = applyTwice(localBump, 5); // 25, localAcc == 2
    let getCell = makeGetter(localAcc);
    let r2 = cellGet(getCell()); // 2

    let dirtyLens = MkLens {
        viewL: (p: Pair) -> {
            cellSet(localAcc, cellGet(localAcc) + 1);
            p.fst
        },
        setL: (p: Pair, v: Int) -> MkPair { fst: v, snd: p.snd },
    };
    let r3 = dirtyLens.viewL(MkPair { fst: 7, snd: 8 }) + cellGet(localAcc); // 7 + 3 = 10

    // 2. Clean `$Shared` closures & `Lens` across `runAsync`, `Chan`, and `parMap`
    let fstLens = MkLens {
        viewL: (p: Pair) -> p.fst,
        setL: (p: Pair, v: Int) -> MkPair { fst: v, snd: p.snd },
    };
    let lensCh = chanNew(2);
    let _ = chanSend(lensCh, fstLens);
    let tLens = runAsync(() -> match chanRecv(lensCh) {
        Some(l) -> {
            let p2 = l.setL(MkPair { fst: 1, snd: 9 }, 40);
            l.viewL(p2) + p2.snd
        },
        None -> 0,
    });

    let tGetter = runAsync(makeGetter(100));

    // 3. Thread-local `Cell` created INSIDE `spawn` with nested `$Local` helper closure
    let tNestedLocal = spawn(() -> {
        let inner = cellNew(10);
        let incInner = () -> cellSet(inner, cellGet(inner) + 6);
        incInner();
        incInner();
        cellGet(inner)
    });

    let mapped = parMap([1, 2, 3], (x) -> applyTwice((y) -> y + 1, x));
    let sumMapped = match mapped {
        Cons(a, Cons(b, Cons(c, Nil))) -> a + b + c,
        _ -> 0,
    };

    printLn(
        intToStr(r1) + "|" +
        intToStr(r2) + "|" +
        intToStr(r3) + "|" +
        intToStr(await(tLens)) + "|" +
        intToStr(await(tGetter)) + "|" +
        intToStr(await(tNestedLocal)) + "|" +
        intToStr(sumMapped)
    )
}
EOF
"$GEISHA_BIN" -o "$TMP_DIR/t13_send_modes_ok" "$TMP_DIR/t13_send_modes_ok.gsa"
assert_eq "typed_send_closures_and_mode_adts" "25|2|10|49|100|22|12" "$("$TMP_DIR/t13_send_modes_ok")"

assert_compile_fails() {
    name="$1"
    src_file="$2"
    if "$GEISHA_BIN" -o "$TMP_DIR/bad_out" "$src_file" >/dev/null 2>&1; then
        echo "FAIL [$name]: compiler unexpectedly accepted unsound concurrent program" >&2
        exit 1
    fi
    echo "PASS [$name]: rejected unsound !Send closure"
    PASS=$((PASS + 1))
}

# 13a. Higher-order `runAsync(f)` wrapper around `spawn(f)` must reject `!Send` closure
cat > "$TMP_DIR/t13_bad_hof.gsa" << 'EOF'
use std.task.{Task, spawn, await}
def runAsync(f: () -> Int): Task Int = spawn(f)
def main() = {
    let c = cellNew(0);
    let _ = await(runAsync(() -> cellGet(c)));
    ()
}
EOF
assert_compile_fails "send_reject_higher_order_spawn" "$TMP_DIR/t13_bad_hof.gsa"

# 13b. Sending a closure that captures `Cell` over `Chan` must be rejected
cat > "$TMP_DIR/t13_bad_chan_fn.gsa" << 'EOF'
use std.sync.{chanNew, chanSend}
def main() = {
    let c = cellNew(0);
    let ch = chanNew(2);
    let _ = chanSend(ch, () -> cellSet(c, 1));
    ()
}
EOF
assert_compile_fails "send_reject_chan_dirty_closure" "$TMP_DIR/t13_bad_chan_fn.gsa"

# 13c. Function-bearing ADT (`BoxFn`) holding a dirty closure must be rejected by `spawn`
cat > "$TMP_DIR/t13_bad_adt_fn.gsa" << 'EOF'
use std.task.{spawn, await}
data BoxFn { MkBox(() -> Int) }
def runBox(b: BoxFn): Int = match b { MkBox(f) -> f() }
def main() = {
    let c = cellNew(7);
    let b = MkBox(() -> cellGet(c));
    let _ = await(spawn(() -> runBox(b)));
    ()
}
EOF
assert_compile_fails "send_reject_dirty_mode_adt" "$TMP_DIR/t13_bad_adt_fn.gsa"

# 13d. Conditional capture (`makeGetter`) instantiated with `Cell` must be rejected by `spawn`
cat > "$TMP_DIR/t13_bad_cond_cap.gsa" << 'EOF'
use std.task.{spawn, await}
def makeGetter(x: a): () -> a = () -> x
def main() = {
    let c = cellNew(1);
    let g = makeGetter(c);
    let _ = await(spawn(() -> { let _ = g(); 0 }));
    ()
}
EOF
assert_compile_fails "send_reject_conditional_capture_cell" "$TMP_DIR/t13_bad_cond_cap.gsa"

# 13e. Returning a closure that captures a thread-local `Cell` out of `spawn` must be rejected
cat > "$TMP_DIR/t13_bad_return_cls.gsa" << 'EOF'
use std.task.{spawn, await}
def main() = {
    let f = await(spawn(() -> {
        let c = cellNew(0);
        () -> cellGet(c)
    }));
    let _ = f();
    ()
}
EOF
assert_compile_fails "send_reject_returning_local_closure_from_spawn" "$TMP_DIR/t13_bad_return_cls.gsa"

# 13f. HKT `State` tainted via `Functor.fmap` with a dirty closure must be rejected by `spawn`
cat > "$TMP_DIR/t13_bad_hkt_state.gsa" << 'EOF'
use std.control.{Functor, fmap}
use std.task.{spawn, await}
data State s a { MkState(s -> (a, s)) }
def runState(st: State s a, init: s): (a, s) = match st { MkState(f) -> f(init) }
instance Functor (State s) {
    def fmap(g, st) = MkState((s0) -> {
        let (a, s1) = runState(st, s0);
        (g(a), s1)
    })
}
def main() = {
    let c = cellNew(0);
    let st0 = MkState((s: Int) -> (s, s));
    let st1 = fmap((x: Int) -> { cellSet(c, x); x }, st0);
    let _ = await(spawn(() -> { let (v, _) = runState(st1, 1); v }));
    ()
}
EOF
assert_compile_fails "send_reject_tainted_hkt_state" "$TMP_DIR/t13_bad_hkt_state.gsa"

# 13g. Forward/mutually-recursive top-level function touching `!Send` global passed to `runAsync`
cat > "$TMP_DIR/t13_bad_global_mutrec.gsa" << 'EOF'
use std.task.{Task, spawn, await}
def runAsync(f: () -> Int): Task Int = spawn(f)
def stepA(): Int = stepB()
def stepB(): Int = cellGet(globalCell)
def globalCell: Cell Int = cellNew(42)
def main() = {
    let _ = await(runAsync(stepA));
    ()
}
EOF
assert_compile_fails "send_reject_mutrec_global_cell_via_hof" "$TMP_DIR/t13_bad_global_mutrec.gsa"

# 13h. `parMap` callback capturing `Cell` must be rejected
cat > "$TMP_DIR/t13_bad_parmap.gsa" << 'EOF'
use std.task.parMap
def main() = {
    let c = cellNew(0);
    let _ = parMap([1, 2, 3], (x) -> { cellSet(c, x); x });
    ()
}
EOF
assert_compile_fails "send_reject_parmap_dirty_callback" "$TMP_DIR/t13_bad_parmap.gsa"

# 14. Generational GC Stress Test: Old->Young Write Barriers (Cell & MutArray), Large Object Munmap, and Multicore STW + FFI
cat > "$TMP_DIR/t14_gc_gen.gsa" << 'EOF'
use std.str.intToStr
use std.task.{spawn, await}

extern "gc_collect_major" def gcCollectMajor(): Void
extern "gc_minor_collection_count" def gcMinorCount(): Int64
extern "gc_major_collection_count" def gcMajorCount(): Int64
extern "gc_heap_live_bytes" def gcLiveBytes(): Int64
extern "strlen" def c_strlen(s: String): Int64

data Tree {
    TLeaf(Int, String),
    TNode(Tree, Tree),
}

def makeTree(d: Int): Tree =
    if (d <= 0) TLeaf(1, "leaf-ok")
    else TNode(makeTree(d - 1), makeTree(d - 1))

def checkTree(t: Tree): Int = match t {
    TLeaf(n, s) -> if (s == "leaf-ok") n else -999999,
    TNode(l, r) -> checkTree(l) + checkTree(r),
}

def main() = {
    // 1. Promote old structures via Major GC
    let oldTree = makeTree(12);
    let oldCell = cellNew("old-init");
    let oldArr = arrayNew(16, "arr-init");
    gcCollectMajor();

    // 2. Mutate Old Cell & Old MutArray with Young objects across many Minor GCs
    let i = cellNew(0);
    while (cellGet(i) < 40000) {
        let k = cellGet(i);
        let youngStr = "y-" + intToStr(k);
        if (k % 100 == 0) {
            cellSet(oldCell, youngStr);
            arraySet(oldArr, k % 16, youngStr)
        } else ();
        cellSet(i, k + 1)
    };

    // 3. Allocate and drop >64KB large objects repeatedly, then Major GC and check live bytes stay bounded
    let j = cellNew(0);
    while (cellGet(j) < 32) {
        let _ = ptrAllocBytes(131072);
        cellSet(j, cellGet(j) + 1)
    };
    gcCollectMajor();
    let liveAfter = i64ToInt(gcLiveBytes());

    // 4. Concurrent threads allocating + lock-free FFI while GCs run
    let t1 = spawn(() -> {
        let acc = cellNew(0);
        let m = cellNew(0);
        while (cellGet(m) < 5000) {
            let s = "thr1-" + intToStr(cellGet(m));
            cellSet(acc, cellGet(acc) + i64ToInt(c_strlen(s)));
            cellSet(m, cellGet(m) + 1)
        };
        cellGet(acc)
    });
    let t2 = spawn(() -> {
        let acc = cellNew(0);
        let m = cellNew(0);
        while (cellGet(m) < 5000) {
            let s = "thr2-" + intToStr(cellGet(m));
            cellSet(acc, cellGet(acc) + i64ToInt(c_strlen(s)));
            cellSet(m, cellGet(m) + 1)
        };
        cellGet(acc)
    });

    let sumWorkers = await(t1) + await(t2);
    let treeOk = checkTree(oldTree);
    let cellOk = cellGet(oldCell);
    let arrOk = arrayGet(oldArr, 39900 % 16);
    let genOk = if (gcMinorCount() > intToI64(0) && gcMajorCount() >= intToI64(2) && liveAfter < 2000000) "gen-ok" else "gen-bad";
    printLn(intToStr(treeOk) + "|" + cellOk + "|" + arrOk + "|" + intToStr(sumWorkers) + "|" + genOk)
}
EOF
"$GEISHA_BIN" -o "$TMP_DIR/t14_gc_gen" "$TMP_DIR/t14_gc_gen.gsa"
assert_eq "generational_gc_write_barrier_and_reclaim" "4096|y-39900|y-39900|87780|gen-ok" "$(GEISHA_GC_HEAP_WORDS=32768 "$TMP_DIR/t14_gc_gen")"

# 15. External library search paths (`-L` / `--lib-path`) across single-file and `--src-root` projects
mkdir -p "$TMP_DIR/extlib/acme" "$TMP_DIR/extapp/src"
cat > "$TMP_DIR/extlib/acme/math2d.gsa" << 'EOF'
pub data Vec2 {
    MkVec2 { x: Int, y: Int },
}
pub def addVec(a: Vec2, b: Vec2): Vec2 = MkVec2 { x: a.x + b.x, y: a.y + b.y }
EOF
cat > "$TMP_DIR/extlib/acme/fmt.gsa" << 'EOF'
use std.str.intToStr
use acme.math2d.{Vec2, addVec}
pub def describeSum(a: Vec2, b: Vec2): String = {
    let s = addVec(a, b);
    "(" + intToStr(s.x) + "," + intToStr(s.y) + ")"
}
EOF
cat > "$TMP_DIR/t15_single_lib.gsa" << 'EOF'
use acme.math2d.MkVec2
use acme.fmt.describeSum
def main(): Void = printLn(describeSum(MkVec2 { x: 3, y: 7 }, MkVec2 { x: 10, y: -2 }))
EOF
"$GEISHA_BIN" -L "$TMP_DIR/extlib" -o "$TMP_DIR/t15_single_lib" "$TMP_DIR/t15_single_lib.gsa"
assert_eq "lib_path_single_file" "(13,5)" "$("$TMP_DIR/t15_single_lib")"

cat > "$TMP_DIR/extapp/src/helper.gsa" << 'EOF'
use acme.math2d.{Vec2, MkVec2}
pub def originOffset(dx: Int, dy: Int): Vec2 = MkVec2 { x: 100 + dx, y: 200 + dy }
EOF
cat > "$TMP_DIR/extapp/src/mod.gsa" << 'EOF'
mod helper
use helper.originOffset
use acme.math2d.MkVec2
use acme.fmt.describeSum
def main(): Void = printLn(describeSum(originOffset(4, 6), MkVec2 { x: -4, y: 14 }))
EOF
"$GEISHA_BIN" --lib-path "$TMP_DIR/extlib" --src-root "$TMP_DIR/extapp" -o "$TMP_DIR/t15_proj_lib" "$TMP_DIR/extapp/src/mod.gsa"
assert_eq "lib_path_project_mode" "(100,220)" "$("$TMP_DIR/t15_proj_lib")"

# 16. Standard library `std.sha256` (NIST FIPS 180-4 vectors) & `std.toml` v1.0 + `std.codec` roundtrip
cat > "$TMP_DIR/t16_toml_sha.gsa" << 'EOF'
use std.result.{Ok, Err}
use std.sha256.{sha256New, sha256Update, sha256FinishHex, sha256Hex}
use std.toml.{parse, stringify, decodeString}
use std.codec.{succeed, (|>), req, at, str, int, bool, list, map, formatErr}
use std.str.intToStr

data ManifestSample {
    MkManifestSample {
        msName: String,
        msPort: Int,
        msDepUrl: String,
        msOwnsMain: Bool,
        msExports: List String,
        msLockSha: String,
    },
}

def main(): Void = {
    let hEmpty = sha256Hex("");
    let hAbc = sha256Hex("abc");
    let hMulti = sha256Hex("abcdbcdecdefdefgefghfghighijhijkijkljklmklmnlmnomnopnopq");
    let sctx = sha256New();
    sha256Update(sctx, "abcdbcdecdefdefgefghfghighij");
    sha256Update(sctx, "hijkijkljklmklmnlmnomnopnopq");
    let hStream = sha256FinishHex(sctx);

    let shaOk =
        hEmpty == "e3b0c44298fc1c149afbf4c8996fb92427ae41e4649b934ca495991b7852b855"
        && hAbc == "ba7816bf8f01cfea414140de5dae2223b00361a396177a9cb410ff61f20015ad"
        && hMulti == "248d6a61d20638b8e5c026930c3e6039a33ce45964ff2167f6ecedd419db06c1"
        && hStream == hMulti;

    let doc = "# Sample TOML v1.0\nname = \"crema\"\nport = 0x1f_90\n\n[deps]\n\"github.com/geisha-lang/codec\" = { git = 'github.com/geisha-lang/codec', version = \"0.2.0\" }\n\n[target.native]\nowns_main = true\nexports = [\n  \"crema_init\", # inline comment\n  \"crema_step\",\n]\n\n[[pkg]]\nname = \"codec\"\nsha256 = \"9f86d081\"\n";

    let dec = succeed((nm) -> (pt) -> (du) -> (om) -> (ex) -> (ls) -> MkManifestSample {
        msName: nm, msPort: pt, msDepUrl: du, msOwnsMain: om, msExports: ex, msLockSha: ls
    })
        |> req("name", str)
        |> req("port", int)
        |> req("deps", at("github.com/geisha-lang/codec", at("git", str)))
        |> req("target", at("native", at("owns_main", bool)))
        |> req("target", at("native", at("exports", list(str))))
        |> req("pkg", map((xs) -> match xs { Cons(h, _) -> h, Nil -> "" }, list(at("sha256", str))));

    match parse(doc) {
        Err(pe) -> printLn("parse-err:" + pe),
        Ok(val) -> {
            let rt = stringify(val);
            match decodeString(dec, rt) {
                Err(de) -> printLn("decode-err:" + formatErr(de)),
                Ok(ms) -> printLn(
                    (if (shaOk) "sha-ok" else "sha-bad")
                    + "|" + ms.msName
                    + "|" + intToStr(ms.msPort)
                    + "|" + ms.msDepUrl
                    + "|" + ms.msLockSha
                ),
            }
        },
    }
}
EOF
"$GEISHA_BIN" -o "$TMP_DIR/t16_toml_sha" "$TMP_DIR/t16_toml_sha.gsa"
assert_eq "stdlib_sha256_and_toml_roundtrip" "sha-ok|crema|8080|github.com/geisha-lang/codec|9f86d081" "$("$TMP_DIR/t16_toml_sha")"

# 17. `mod`-free demand-driven module loader + sibling umbrella (`stage.gsa` + `stage/ik.gsa`) + module aliasing + dead-file skip
mkdir -p "$TMP_DIR/modfree/src/stage"
cat > "$TMP_DIR/modfree/src/stage/ik.gsa" << 'EOF'
pub def solveReach(a: Int, b: Int): Int = a + b
EOF
cat > "$TMP_DIR/modfree/src/stage.gsa" << 'EOF'
pub open stage.ik
pub def stageScale(v: Int): Int = v * 3
EOF
# Unreferenced broken file must NOT be loaded under demand-driven `use` resolution!
cat > "$TMP_DIR/modfree/src/unused_dead.gsa" << 'EOF'
this file has intentional syntax errors and is never imported! @@@
EOF
cat > "$TMP_DIR/modfree/src/main.gsa" << 'EOF'
use stage.{solveReach, stageScale}
use stage.ik as ikMod

def main(): Void = {
    let v = stageScale(solveReach(4, 6)) + ikMod.solveReach(1, 2);
    printLn("modfree:" + std.str.intToStr(v))
}
EOF
"$GEISHA_BIN" --src-root "$TMP_DIR/modfree/src" -o "$TMP_DIR/t17_modfree" "$TMP_DIR/modfree/src/main.gsa"
assert_eq "mod_free_demand_loader_and_sibling_umbrella" "modfree:33" "$("$TMP_DIR/t17_modfree")"

# 18. Decentralized Package Manager (`geisha init/add/fetch/build/run/test`, MVS, static Git index, C host, lockfile tamper check, overrides & Orphan Rule)
export GEISHA_HOME="$TMP_DIR/ghome"
export GEISHA_INDEX="$TMP_DIR/pkg_index.git"

# 18a. Create Git repo `core_math` with tags `v0.1.0` (scale=10) and `v0.2.0` (scale=100)
mkdir -p "$TMP_DIR/repos/core_math_work/src"
cat > "$TMP_DIR/repos/core_math_work/geisha.toml" << 'EOF'
name = "core_math"
version = "0.1.0"
EOF
cat > "$TMP_DIR/repos/core_math_work/src/vec.gsa" << 'EOF'
pub data Vec2 {
    MkVec2 { vx: Int, vy: Int },
}
pub def scaleSum(v: Vec2): Int = (v.vx + v.vy) * 10
EOF
cat > "$TMP_DIR/repos/core_math_work/src/core_math.gsa" << 'EOF'
pub open core_math.vec
EOF
git -C "$TMP_DIR/repos/core_math_work" init -q
git -C "$TMP_DIR/repos/core_math_work" config user.email "test@geisha.local"
git -C "$TMP_DIR/repos/core_math_work" config user.name "Geisha Test"
git -C "$TMP_DIR/repos/core_math_work" add .
git -C "$TMP_DIR/repos/core_math_work" commit -q -m "release v0.1.0"
git -C "$TMP_DIR/repos/core_math_work" tag v0.1.0

cat > "$TMP_DIR/repos/core_math_work/geisha.toml" << 'EOF'
name = "core_math"
version = "0.2.0"
EOF
cat > "$TMP_DIR/repos/core_math_work/src/vec.gsa" << 'EOF'
pub data Vec2 {
    MkVec2 { vx: Int, vy: Int },
}
pub def scaleSum(v: Vec2): Int = (v.vx + v.vy) * 100
EOF
git -C "$TMP_DIR/repos/core_math_work" add .
git -C "$TMP_DIR/repos/core_math_work" commit -q -m "release v0.2.0"
git -C "$TMP_DIR/repos/core_math_work" tag v0.2.0
git clone --bare -q "$TMP_DIR/repos/core_math_work" "$TMP_DIR/repos/core_math.git"

# 18b. Create Git repo `ui_kit` depending on `core_math` 0.2.0 + custom C `main()` host + exported Geisha callback!
mkdir -p "$TMP_DIR/repos/ui_kit_work/src" "$TMP_DIR/repos/ui_kit_work/host"
cat > "$TMP_DIR/repos/ui_kit_work/geisha.toml" << EOF
name = "ui_kit"
version = "0.1.0"

[deps]
core_math = { git = "file://$TMP_DIR/repos/core_math.git", version = "0.2.0" }

[target.native]
c_sources = ["host/bridge.c"]
exports = ["ui_render_frame"]
owns_main = true
boot_symbol = "__geisha_ui_boot"
EOF
cat > "$TMP_DIR/repos/ui_kit_work/src/widget.gsa" << 'EOF'
use core_math.{MkVec2, scaleSum}
pub def computeLayout(n: Int): Int = scaleSum(MkVec2 { vx: n, vy: 0 })
EOF
cat > "$TMP_DIR/repos/ui_kit_work/host/bridge.c" << 'EOF'
#include <stdio.h>
#include <stdint.h>
extern void gc_init_with_stack(int64_t heap_words, void *stack_anchor);
extern void gc_enable_generational(void);
extern void __geisha_ui_boot(void);
extern int32_t ui_render_frame(int32_t input, void *fv);

int main(void) {
    int64_t anchor = 0;
    gc_init_with_stack(65536, &anchor);
    gc_enable_generational();
    __geisha_ui_boot();
    int32_t out = ui_render_frame(7, (void *)0);
    printf("native-host:%d\n", out);
    return 0;
}
EOF
git -C "$TMP_DIR/repos/ui_kit_work" init -q
git -C "$TMP_DIR/repos/ui_kit_work" config user.email "test@geisha.local"
git -C "$TMP_DIR/repos/ui_kit_work" config user.name "Geisha Test"
git -C "$TMP_DIR/repos/ui_kit_work" add .
git -C "$TMP_DIR/repos/ui_kit_work" commit -q -m "release v0.1.0"
git -C "$TMP_DIR/repos/ui_kit_work" tag v0.1.0
git clone --bare -q "$TMP_DIR/repos/ui_kit_work" "$TMP_DIR/repos/ui_kit.git"

# 18c. Create Static Git Index repo (`$GEISHA_INDEX`)
mkdir -p "$TMP_DIR/repos/index_work/packages/c" "$TMP_DIR/repos/index_work/packages/u"
cat > "$TMP_DIR/repos/index_work/packages/c/core_math.toml" << EOF
git = "file://$TMP_DIR/repos/core_math.git"
EOF
cat > "$TMP_DIR/repos/index_work/packages/u/ui_kit.toml" << EOF
git = "file://$TMP_DIR/repos/ui_kit.git"
EOF
git -C "$TMP_DIR/repos/index_work" init -q
git -C "$TMP_DIR/repos/index_work" config user.email "test@geisha.local"
git -C "$TMP_DIR/repos/index_work" config user.name "Geisha Test"
git -C "$TMP_DIR/repos/index_work" add .
git -C "$TMP_DIR/repos/index_work" commit -q -m "init static index"
git clone --bare -q "$TMP_DIR/repos/index_work" "$GEISHA_INDEX"

# 18d. Scaffold `demo_app` with `geisha init`, add `core_math@0.1.0` + `ui_kit` (MVS upgrades `core_math` to `0.2.0`!)
ABS_GEISHA="$(cd "$(dirname "$GEISHA_BIN")" && pwd)/$(basename "$GEISHA_BIN")"
ABS_RUNTIME="$(cd "$(dirname "$GEISHA_RUNTIME")" && pwd)/$(basename "$GEISHA_RUNTIME")"
export GEISHA_RUNTIME="$ABS_RUNTIME"

"$ABS_GEISHA" init "$TMP_DIR/demo_app" >/dev/null
(
    cd "$TMP_DIR/demo_app"
    "$ABS_GEISHA" add core_math --version 0.1.0 >/dev/null
    "$ABS_GEISHA" add ui_kit >/dev/null
)
cat > "$TMP_DIR/demo_app/src/main.gsa" << 'EOF'
use core_math.{MkVec2, scaleSum}
use ui_kit.widget.computeLayout

def bootBias: Cell Int = cellNew(0)

def main(): Void = cellSet(bootBias, 5)

pub def ui_render_frame(n: Int): Int =
    computeLayout(n) + scaleSum(MkVec2 { vx: 0, vy: 1 }) + cellGet(bootBias)
EOF

APP_OUT="$(cd "$TMP_DIR/demo_app" && "$ABS_GEISHA" run)"
assert_eq "pkg_mvs_upgrade_and_native_host" "native-host:805" "$APP_OUT"

# 18e. Delete ALL Git remotes & bare git DBs — verify 100% offline build from content-addressed cache + `geisha.lock`!
rm -rf "$TMP_DIR/repos" "$GEISHA_HOME/git" "$TMP_DIR/demo_app/build"
OFFLINE_OUT="$(cd "$TMP_DIR/demo_app" && "$ABS_GEISHA" run)"
assert_eq "pkg_offline_content_addressed_build" "native-host:805" "$OFFLINE_OUT"

# 18f. Tamper 1 file inside content-addressed cache -> must fail SHA-256 integrity check!
CACHED_VEC="$(find "$GEISHA_HOME/cache/p" -path "*0_2_0*" -name "vec.gsa" | head -n 1)"
cp "$CACHED_VEC" "$TMP_DIR/vec.gsa.bak"
printf "\n// tampered\n" >> "$CACHED_VEC"
rm -rf "$TMP_DIR/demo_app/build"
if (cd "$TMP_DIR/demo_app" && "$ABS_GEISHA" build >/dev/null 2>&1); then
    echo "FAIL [pkg_lockfile_tamper_rejected]: tampered cache was accepted!" >&2
    exit 1
fi
echo "PASS [pkg_lockfile_tamper_rejected]: rejected tampered cache via geisha.lock sha256"
PASS=$((PASS + 1))
mv "$TMP_DIR/vec.gsa.bak" "$CACHED_VEC"

# 18g. Local development override via `geisha.local.toml` (`[overrides]`) without modifying `geisha.lock`!
mkdir -p "$TMP_DIR/local_math/src"
cat > "$TMP_DIR/local_math/geisha.toml" << 'EOF'
name = "core_math"
version = "0.3.0-dev"
EOF
cat > "$TMP_DIR/local_math/src/vec.gsa" << 'EOF'
pub data Vec2 {
    MkVec2 { vx: Int, vy: Int },
}
pub def scaleSum(v: Vec2): Int = (v.vx + v.vy) * 1000
EOF
cat > "$TMP_DIR/local_math/src/core_math.gsa" << 'EOF'
pub open core_math.vec
EOF
LOCK_BEFORE="$(cat "$TMP_DIR/demo_app/geisha.lock")"
cat > "$TMP_DIR/demo_app/geisha.local.toml" << EOF
[overrides]
core_math = { path = "$TMP_DIR/local_math" }
EOF
OVERRIDE_OUT="$(cd "$TMP_DIR/demo_app" && "$ABS_GEISHA" run)"
LOCK_AFTER="$(cat "$TMP_DIR/demo_app/geisha.lock")"
assert_eq "pkg_local_toml_override" "native-host:8005" "$OVERRIDE_OUT"
assert_eq "pkg_local_override_preserves_lockfile" "$LOCK_BEFORE" "$LOCK_AFTER"
rm -f "$TMP_DIR/demo_app/geisha.local.toml"

# 18h. `geisha init --lib` + `geisha test`
"$ABS_GEISHA" init --lib "$TMP_DIR/sample_lib" >/dev/null
LIB_TEST_OUT="$(cd "$TMP_DIR/sample_lib" && "$ABS_GEISHA" test | tail -n 1)"
assert_eq "pkg_init_lib_and_test" "All 1 test target(s) passed." "$LIB_TEST_OUT"

# 18i. Hermetic phantom dependency rejection (`demo_app` drops `core_math` from `[deps]` while `ui_kit` still depends on it)
(cd "$TMP_DIR/demo_app" && "$ABS_GEISHA" remove core_math >/dev/null)
if (cd "$TMP_DIR/demo_app" && "$ABS_GEISHA" build >/dev/null 2>&1); then
    echo "FAIL [pkg_phantom_dep_rejected]: undeclared transitive import was accepted!" >&2
    exit 1
fi
echo "PASS [pkg_phantom_dep_rejected]: blocked undeclared transitive dependency import"
PASS=$((PASS + 1))

# 18j. Cross-package Orphan Instance Rule rejection
mkdir -p "$TMP_DIR/rogue_lib/src" "$TMP_DIR/orphan_app/src"
cat > "$TMP_DIR/rogue_lib/src/bad.gsa" << 'EOF'
use std.codec.{Encode, VInt}
use core_math.Vec2

// Neither `Encode` (stdlib) nor `Vec2` (`core_math`) belongs to `rogue_lib`!
instance Encode Vec2 {
    def encode(v) = VInt(intToI64(v.vx))
}
pub def touch(): Int = 1
EOF
cat > "$TMP_DIR/orphan_app/src/main.gsa" << 'EOF'
use rogue_lib.bad.touch
def main(): Void = printLn(std.str.intToStr(touch()))
EOF
if "$ABS_GEISHA" --src-root "$TMP_DIR/orphan_app/src" \
    --pkg "core_math=$TMP_DIR/local_math/src" \
    --pkg "rogue_lib=$TMP_DIR/rogue_lib/src" \
    --dep "rogue_lib:core_math=core_math" \
    -o "$TMP_DIR/orphan_bin" "$TMP_DIR/orphan_app/src/main.gsa" 2>/dev/null; then
    echo "FAIL [pkg_orphan_instance_rejected]: foreign orphan instance was accepted!" >&2
    exit 1
fi
echo "PASS [pkg_orphan_instance_rejected]: rejected cross-package orphan instance"
PASS=$((PASS + 1))

# 19. Zero-Copy Binary `Ptr` Read/Write + `floatToBits32` / `bits32ToFloat` + `ptrOffset`
cat > "$TMP_DIR/t19_ptr_bin.gsa" << 'EOF'
use std.str.{intToStr, i64ToStr}

def main(): Void = {
    let buf = ptrAllocBytes(64);
    ptrSetByte(buf, 0, 251); // -5 as signed i8
    ptrWriteU16Le(buf, 1, 51321); // unaligned offset 1
    ptrWriteU32Le(buf, 3, 305419896); // 0x12345678 at unaligned offset 3
    ptrWriteI64Le(buf, 7, (intToI64(1) << 40) | intToI64(255)); // unaligned offset 7
    ptrWriteF32Le(buf, 15, 1.5);
    ptrWriteF64Le(buf, 19, 3.25);

    let i8v = ptrReadI8(buf, 0);
    let u16v = ptrReadU16Le(buf, 1);
    let u32v = ptrReadU32Le(buf, 3);
    let i64v = ptrReadI64Le(buf, 7);
    let f32v = floatToInt(ptrReadF32Le(buf, 15) * 10.0);
    let f64v = floatToInt(ptrReadF64Le(buf, 19) * 100.0);
    let offPtr = ptrOffset(buf, 3);
    let u32ViaOff = ptrReadU32Le(offPtr, 0);
    let b32 = floatToBits32(1.5);
    let rt32 = floatToInt(bits32ToFloat(b32) * 10.0);
    printLn(
        intToStr(i8v) + "|" +
        intToStr(u16v) + "|" +
        intToStr(u32v) + "|" +
        intToStr(u32ViaOff) + "|" +
        i64ToStr(i64v) + "|" +
        intToStr(f32v) + "|" +
        intToStr(f64v) + "|" +
        intToStr(rt32)
    )
}
EOF
"$GEISHA_BIN" -o "$TMP_DIR/t19_ptr_bin" "$TMP_DIR/t19_ptr_bin.gsa"
assert_eq "ptr_binary_le_and_f32" "-5|51321|305419896|305419896|1099511628031|15|325|15" "$("$TMP_DIR/t19_ptr_bin")"

# 20. Zero-Overhead `extern noalloc` (no `_setjmp` / `gc_enter_blocking`) + C SIMD-style kernel
cat > "$TMP_DIR/t20_kernel.c" << 'EOF'
#include <stdint.h>
int32_t dot_i8_kernel(const int8_t *a, const int8_t *b, int32_t n) {
    int32_t acc = 0;
    for (int32_t i = 0; i < n; i++) {
        acc += (int32_t)a[i] * (int32_t)b[i];
    }
    return acc;
}
EOF
cat > "$TMP_DIR/t20_noalloc.gsa" << 'EOF'
use std.str.intToStr

extern noalloc "dot_i8_kernel" def c_dot_i8(a: Ptr, b: Ptr, n: Int): Int

def runDot(): Int = {
    let a = ptrAllocBytes(4);
    let b = ptrAllocBytes(4);
    ptrSetByte(a, 0, 3);  ptrSetByte(a, 1, 254); // 3, -2
    ptrSetByte(a, 2, 5);  ptrSetByte(a, 3, 4);
    ptrSetByte(b, 0, 10); ptrSetByte(b, 1, 7);   // 30 - 14 + 10 + 12 = 38
    ptrSetByte(b, 2, 2);  ptrSetByte(b, 3, 3);
    c_dot_i8(a, b, 4)
}

def main(): Void = printLn(intToStr(runDot()))
EOF
"$GEISHA_BIN" -e -o "$TMP_DIR/t20_noalloc.ll" "$TMP_DIR/t20_noalloc.gsa"
if awk '/define .*@runDot\(/,/^}/' "$TMP_DIR/t20_noalloc.ll" | grep -q "gc_enter_blocking"; then
    echo "FAIL [extern_noalloc_ir]: gc_enter_blocking should not be emitted inside runDot for extern noalloc" >&2
    exit 1
fi
if ! grep -q "declare i32 @dot_i8_kernel(ptr, ptr, i32) nounwind" "$TMP_DIR/t20_noalloc.ll"; then
    echo "FAIL [extern_noalloc_ir]: expected nounwind attribute on extern noalloc declaration" >&2
    exit 1
fi
echo "PASS [extern_noalloc_ir]: zero blocking-section overhead verified in LLVM IR"
PASS=$((PASS + 1))
"$CC" $HOST_CC_TARGET -O2 -Wno-override-module -pthread \
    -x ir "$TMP_DIR/t20_noalloc.ll" -x c "$TMP_DIR/t20_kernel.c" -x none "$GEISHA_RUNTIME" $HOST_CC_LIBS \
    -o "$TMP_DIR/t20_noalloc"
assert_eq "extern_noalloc_exec" "38" "$("$TMP_DIR/t20_noalloc")"

# 21. Embedded Static Library (`--no-main --export ... -o libembed.a`) + StableHandle + Multi-Thread C Host + `gcTrim`
cat > "$TMP_DIR/t21_embed.gsa" << 'EOF'
data EngineState {
    MkEngine { counter: Cell Int, label: String },
}

pub def eng_new(initVal: Int, name: String): Int64 = {
    gcSetThresholds(intToI64(262144), intToI64(1048576));
    let st = MkEngine { counter: cellNew(initVal), label: name };
    gcHandleNew(st)
}

pub def eng_add(h: Int64, delta: Int): Int = {
    // Churn temporary allocations to exercise GC while handle stays pinned
    let i = cellNew(0);
    while (cellGet(i) < 200) {
        let _ = ptrAllocBytes(256);
        cellSet(i, cellGet(i) + 1)
    };
    let st: EngineState = gcHandleGet(h);
    let next = cellGet(st.counter) + delta;
    cellSet(st.counter, next);
    next
}

pub def eng_label_len(h: Int64): Int = {
    let st: EngineState = gcHandleGet(h);
    strLen(st.label)
}

pub def eng_trim(): Int64 = {
    gcTrim();
    gcHeapLiveBytes()
}

pub def eng_free(h: Int64): Void = gcHandleFree(h)
EOF
"$GEISHA_BIN" --no-main \
    --export eng_new --export eng_add --export eng_label_len --export eng_trim --export eng_free \
    -o "$TMP_DIR/libt21_embed.a" "$TMP_DIR/t21_embed.gsa"
cat > "$TMP_DIR/t21_host.c" << 'EOF'
#include <pthread.h>
#include <stdint.h>
#include <stdio.h>

extern void __geisha_init(void);
extern int64_t eng_new(int32_t init_val, const char *name, void *fv);
extern int32_t eng_add(int64_t h, int32_t delta, void *fv);
extern int32_t eng_label_len(int64_t h, void *fv);
extern int64_t eng_trim(void *fv);
extern void eng_free(int64_t h, void *fv);

typedef struct { int64_t handle; int32_t out; } WorkerArg;

static void *worker_fn(void *arg) {
    WorkerArg *wa = (WorkerArg *)arg;
    int32_t v = 0;
    for (int i = 0; i < 5; i++) {
        v = eng_add(wa->handle, 3, NULL);
    }
    (void)eng_trim(NULL);
    wa->out = v;
    return NULL;
}

int main(void) {
    /* Deliberately NO gc_init_with_stack / gc_thread_attach from host! */
    __geisha_init();
    int64_t h = eng_new(10, "juxu-core", NULL);
    WorkerArg wa = { .handle = h, .out = 0 };
    pthread_t tid;
    pthread_create(&tid, NULL, worker_fn, &wa);
    pthread_join(tid, NULL);
    int32_t final_val = eng_add(h, 5, NULL);
    int32_t llen = eng_label_len(h, NULL);
    eng_free(h, NULL);
    (void)eng_trim(NULL);
    printf("%d|%d|%d\n", wa.out, final_val, llen);
    return 0;
}
EOF
"$CC" $HOST_CC_TARGET -O2 -pthread \
    "$TMP_DIR/t21_host.c" "$TMP_DIR/libt21_embed.a" $HOST_CC_LIBS -o "$TMP_DIR/t21_host"
assert_eq "embedded_static_lib_handles_and_threads" "25|30|9" "$("$TMP_DIR/t21_host")"

# 22. iOS & iOS Simulator Cross-Compilation Static Libraries (`--target ios` & `--target ios-sim`)
if [ -f "./build/libgeisha_runtime_ios.a" ] && [ -f "./build/libgeisha_runtime_ios_sim.a" ]; then
    "$GEISHA_BIN" --target ios --no-main --export eng_new --export eng_add --export eng_free \
        -o "$TMP_DIR/libt22_ios.a" "$TMP_DIR/t21_embed.gsa"
    "$GEISHA_BIN" --target ios-sim --no-main --export eng_new --export eng_add --export eng_free \
        -o "$TMP_DIR/libt22_iossim.a" "$TMP_DIR/t21_embed.gsa"
    IOS_PLAT="$(otool -l "$TMP_DIR/libt22_ios.a" | grep -m1 'platform ' | awk '{print $2}')"
    SIM_PLAT="$(otool -l "$TMP_DIR/libt22_iossim.a" | grep -m1 'platform ' | awk '{print $2}')"
    assert_eq "ios_static_lib_platform" "2" "$IOS_PLAT"
    assert_eq "ios_sim_static_lib_platform" "7" "$SIM_PLAT"
fi

# 23. Transparent Value-Type ADT Unboxing (Zero-Alloc `BytesView` + Flat `Vec Candidate` + IR Check)
cat > "$TMP_DIR/t23_unbox.gsa" << 'EOF'
use std.vec.{Vec, vecNew, vecPush, vecGetOr, vecLen}
use std.str.intToStr

data BytesView {
    MkView { base: Ptr, off: Int, len: Int },
}

data Candidate {
    MkCand { text: String, score: Float, code: Int },
}

def makeView(p: Ptr, off: Int, len: Int): BytesView =
    MkView { base: p, off: off, len: len }

def viewByteSum(v: BytesView): Int = {
    let acc = cellNew(0);
    let i = cellNew(0);
    while (cellGet(i) < v.len) {
        let idx = cellGet(i);
        cellSet(acc, cellGet(acc) + ptrByteAt(v.base, v.off + idx));
        cellSet(i, idx + 1)
    };
    cellGet(acc)
}

def main(): Void = {
    let raw = ptrAllocBytes(8);
    ptrSetByte(raw, 2, 10);
    ptrSetByte(raw, 3, 20);
    ptrSetByte(raw, 4, 12);
    let v = makeView(raw, 2, 3);
    let sum = viewByteSum(v);

    let cands: Vec Candidate = vecNew();
    let k = cellNew(0);
    while (cellGet(k) < 100) {
        let idx = cellGet(k);
        vecPush(cands, MkCand { text: "cand-" + intToStr(idx), score: intToFloat(idx) * 1.5, code: idx });
        cellSet(k, idx + 1)
    };
    gcTrim();
    let c42 = vecGetOr(cands, 42, MkCand { text: "", score: 0.0, code: -1 });
    printLn(intToStr(sum) + "|" + intToStr(vecLen(cands)) + "|" + c42.text + "|" + intToStr(floatToInt(c42.score)))
}
EOF
"$GEISHA_BIN" -e -o "$TMP_DIR/t23_unbox.ll" "$TMP_DIR/t23_unbox.gsa"
if awk '/define .*@makeView\(/,/^}/' "$TMP_DIR/t23_unbox.ll" | grep -q "gc_alloc"; then
    echo "FAIL [transparent_adt_unbox_ir]: makeView should not call gc_alloc for small non-recursive ADT" >&2
    exit 1
fi
if ! awk '/define .*@makeView\(/,/^}/' "$TMP_DIR/t23_unbox.ll" | grep -q "insertvalue { ptr, i32, i32 }"; then
    echo "FAIL [transparent_adt_unbox_ir]: expected flat LLVM struct { ptr, i32, i32 } for BytesView" >&2
    exit 1
fi
echo "PASS [transparent_adt_unbox_ir]: BytesView compiled to zero-alloc flat { ptr, i32, i32 }"
PASS=$((PASS + 1))
"$GEISHA_BIN" -o "$TMP_DIR/t23_unbox" "$TMP_DIR/t23_unbox.gsa"
assert_eq "transparent_adt_unbox_exec" "42|100|cand-42|63" "$("$TMP_DIR/t23_unbox")"

# 24. Heterogeneous Multi-Parameter Operator Concepts (`Add`/`Sub`/`Mul`/`Div` with `a b -> c` fundep)
cat > "$TMP_DIR/t24_hetero_ops.gsa" << 'EOF'
use std.str.intToStr

data Vec2 {
    MkVec2 { x: Float, y: Float },
}

instance Add Vec2 Vec2 Vec2 {
    def (+)(a: Vec2, b: Vec2): Vec2 = MkVec2 { x: a.x + b.x, y: a.y + b.y }
}

instance Add Vec2 Float Vec2 {
    def (+)(a: Vec2, s: Float): Vec2 = MkVec2 { x: a.x + s, y: a.y + s }
}

instance Add Float Vec2 Vec2 {
    def (+)(s: Float, a: Vec2): Vec2 = MkVec2 { x: s + a.x, y: s + a.y }
}

instance Mul Float Vec2 Vec2 {
    def (*)(s: Float, a: Vec2): Vec2 = MkVec2 { x: s * a.x, y: s * a.y }
}

instance Mul Vec2 Float Vec2 {
    def (*)(a: Vec2, s: Float): Vec2 = MkVec2 { x: a.x * s, y: a.y * s }
}

def main(): Void = {
    let v = MkVec2 { x: 2.0, y: 3.0 };
    let r = (2.0 * v + 1.0) + (v * 3.0);
    // 2.0*(2,3)+1 = (5,7); v*3 = (6,9); sum = (11, 16)
    printLn(intToStr(floatToInt(r.x)) + "|" + intToStr(floatToInt(r.y)))
}
EOF
"$GEISHA_BIN" -o "$TMP_DIR/t24_hetero_ops" "$TMP_DIR/t24_hetero_ops.gsa"
assert_eq "hetero_fundep_ops" "11|16" "$("$TMP_DIR/t24_hetero_ops")"

# 25. First-class `Float32`, `std.math` LLVM intrinsics, 64-bit `Ptr` ops, and Leaf-Loop Safepoint Omission
cat > "$TMP_DIR/t25_f32_math.gsa" << 'EOF'
use std.math.{sqrt, exp, log, tanh, fma, sqrtF32, fmaF32, absF32}
use std.str.intToStr

def dotF32(a: MutArray Float32, b: MutArray Float32, n: Int): Float32 = {
    let acc = cellNew(intToF32(0));
    let i = cellNew(0);
    while (cellGet(i) < n) {
        let idx = cellGet(i);
        cellSet(acc, mathFmaF32(arrayGet(a, idx), arrayGet(b, idx), cellGet(acc)));
        cellSet(i, idx + 1)
    };
    cellGet(acc)
}

def main(): Void = {
    let a = arrayNew(4, intToF32(0));
    let b = arrayNew(4, intToF32(0));
    arraySet(a, 0, floatToF32(1.0)); arraySet(a, 1, floatToF32(2.0));
    arraySet(a, 2, floatToF32(3.0)); arraySet(a, 3, floatToF32(4.0));
    arraySet(b, 0, floatToF32(2.0)); arraySet(b, 1, floatToF32(3.0));
    arraySet(b, 2, floatToF32(4.0)); arraySet(b, 3, floatToF32(5.0));
    let d = dotF32(a, b, 4); // 2 + 6 + 12 + 20 = 40.0

    let p = ptrAllocBytes64(intToI64(16));
    ptrWriteF32Le64(p, intToI64(0), d);
    let dBack = ptrReadF32Le64(p, intToI64(0));

    let s = sqrtF32(floatToF32(16.0)); // 4.0
    let negAbs = absF32(-s);           // 4.0
    let m = floatToInt(sqrt(25.0) + fma(2.0, 3.0, 4.0) + log(exp(3.0)) + tanh(0.0)); // 5 + 10 + 3 + 0 = 18
    printLn(intToStr(f32ToInt(dBack)) + "|" + intToStr(f32ToInt(negAbs)) + "|" + intToStr(m))
}
EOF
"$GEISHA_BIN" -e -o "$TMP_DIR/t25_f32_math.ll" "$TMP_DIR/t25_f32_math.gsa"
if awk '/define .*@dotF32\(/,/^}/' "$TMP_DIR/t25_f32_math.ll" | grep -q "gc_safepoint_slow"; then
    echo "FAIL [leaf_loop_safepoint_ir]: pure numerical leaf loop dotF32 should not emit gc_safepoint_slow" >&2
    exit 1
fi
echo "PASS [leaf_loop_safepoint_ir]: pure numerical leaf loop omits inner safepoint poll"
PASS=$((PASS + 1))
"$GEISHA_BIN" -o "$TMP_DIR/t25_f32_math" "$TMP_DIR/t25_f32_math.gsa"
assert_eq "f32_math_and_ptr64" "40|4|18" "$("$TMP_DIR/t25_f32_math")"

# 26. Two-Phase GC Cleanup (`ForeignPtr` + `withForeignPtr` keep-alive), `withAlloca` (`stacksave`/`stackrestore`), & `withArena`
cat > "$TMP_DIR/t26_scoped_mem.gsa" << 'EOF'
use std.str.intToStr

def allocAndReadForeign(): Int = {
    let fp = foreignPtrAlloc(intToI64(4096));
    let liveBefore = i64ToInt(gcExternalLiveBytes());
    let v = withForeignPtr(fp, (p) -> {
        scopedPtrWriteF32Le(p, 0, floatToF32(42.5));
        f32ToInt(scopedPtrReadF32Le(p, 0) + floatToF32(0.5))
    });
    if (liveBefore >= 4096) v else -1
}

def main(): Void = {
    let fv = allocAndReadForeign();
    let k = cellNew(0);
    while (cellGet(k) < 32) {
        let _ = allocAndReadForeign();
        cellSet(k, cellGet(k) + 1)
    };
    let livePeak = i64ToInt(gcExternalLiveBytes());
    gcTrim();
    let liveAfter = i64ToInt(gcExternalLiveBytes());
    let reclaimedOk = if (livePeak >= 4096 && liveAfter < livePeak) 1 else 0;

    // Exercise withAlloca 5000 times in a loop (would stack-overflow without stacksave/stackrestore)
    let sumAlloca = cellNew(0);
    let i = cellNew(0);
    while (cellGet(i) < 5000) {
        let cur = withAlloca(4096, (p) -> {
            scopedPtrWriteI32Le(p, 0, 1);
            scopedPtrReadI32Le(p, 0)
        });
        cellSet(sumAlloca, cellGet(sumAlloca) + cur);
        cellSet(i, cellGet(i) + 1)
    };

    let arenaRes = withArena((a) -> {
        let p1 = arenaAlloc(a, intToI64(1024));
        let p2 = arenaAlloc(a, intToI64(1024));
        scopedPtrWriteF32Le64(p1, intToI64(0), floatToF32(12.0));
        scopedPtrWriteF32Le64(p2, intToI64(0), floatToF32(30.0));
        f32ToInt(scopedPtrReadF32Le64(p1, intToI64(0)) + scopedPtrReadF32Le64(p2, intToI64(0)))
    });

    printLn(intToStr(fv) + "|" + intToStr(reclaimedOk) + "|" + intToStr(cellGet(sumAlloca)) + "|" + intToStr(arenaRes))
}
EOF
"$GEISHA_BIN" -e -o "$TMP_DIR/t26_scoped_mem.ll" "$TMP_DIR/t26_scoped_mem.gsa"
if ! grep -q "asm sideeffect" "$TMP_DIR/t26_scoped_mem.ll"; then
    echo "FAIL [withForeignPtr_keepalive_ir]: expected compiler keep-alive asm barrier in LLVM IR" >&2
    exit 1
fi
echo "PASS [withForeignPtr_keepalive_ir]: keep-alive barrier verified in LLVM IR"
PASS=$((PASS + 1))
"$GEISHA_BIN" -o "$TMP_DIR/t26_scoped_mem" "$TMP_DIR/t26_scoped_mem.gsa"
assert_eq "scoped_foreign_alloca_arena" "43|1|5000|42" "$("$TMP_DIR/t26_scoped_mem")"

# 27. `$Scoped` Mode Compile-Time Escape Rejections (all 5 must fail to compile)
cat > "$TMP_DIR/t27_esc1.gsa" << 'EOF'
def main(): Void = {
    let _ = withAlloca(64, (p) -> p);
    ()
}
EOF
if "$GEISHA_BIN" -o "$TMP_DIR/t27_esc1" "$TMP_DIR/t27_esc1.gsa" 2>/dev/null; then
    echo "FAIL [scoped_escape_direct]: returning ScopedPtr from withAlloca should be rejected" >&2
    exit 1
fi
cat > "$TMP_DIR/t27_esc2.gsa" << 'EOF'
use std.option.{Option, Some, None}
def main(): Void = {
    let fp = foreignPtrAlloc(intToI64(64));
    let _ = withForeignPtr(fp, (p) -> Some(p));
    ()
}
EOF
if "$GEISHA_BIN" -o "$TMP_DIR/t27_esc2" "$TMP_DIR/t27_esc2.gsa" 2>/dev/null; then
    echo "FAIL [scoped_escape_adt]: returning Some(ScopedPtr) from withForeignPtr should be rejected" >&2
    exit 1
fi
cat > "$TMP_DIR/t27_esc3.gsa" << 'EOF'
def main(): Void = {
    let _ = withArena((a) -> {
        let p = arenaAlloc(a, intToI64(64));
        () -> scopedPtrByteAt(p, 0)
    });
    ()
}
EOF
if "$GEISHA_BIN" -o "$TMP_DIR/t27_esc3" "$TMP_DIR/t27_esc3.gsa" 2>/dev/null; then
    echo "FAIL [scoped_escape_closure]: returning $Scoped closure capturing ScopedPtr should be rejected" >&2
    exit 1
fi
cat > "$TMP_DIR/t27_esc4.gsa" << 'EOF'
use std.option.{Option, Some, None}
def main(): Void = {
    let c = cellNew(None);
    withAlloca(64, (p) -> cellSet(c, Some(p)))
}
EOF
if "$GEISHA_BIN" -o "$TMP_DIR/t27_esc4" "$TMP_DIR/t27_esc4.gsa" 2>/dev/null; then
    echo "FAIL [scoped_escape_cell]: storing ScopedPtr in Cell should be rejected" >&2
    exit 1
fi
cat > "$TMP_DIR/t27_esc5.gsa" << 'EOF'
use std.task.{spawn, await}
def main(): Void = {
    let _ = withAlloca(64, (p) -> {
        let t = spawn(() -> scopedPtrByteAt(p, 0));
        await(t)
    });
    ()
}
EOF
if "$GEISHA_BIN" -o "$TMP_DIR/t27_esc5" "$TMP_DIR/t27_esc5.gsa" 2>/dev/null; then
    echo "FAIL [scoped_escape_spawn]: capturing ScopedPtr in spawn should be rejected" >&2
    exit 1
fi
echo "PASS [scoped_mode_escape_rejected]: all 5 ScopedPtr/Arena escape attempts rejected at compile time"
PASS=$((PASS + 1))

# 28. Thread-Safe `ImmArray` (`Send`) + Data-Parallel `parTabulate`
cat > "$TMP_DIR/t28_imm_par.gsa" << 'EOF'
use std.str.intToStr

def main(): Void = {
    let src = arrayNew(1000, intToF32(0));
    let i = cellNew(0);
    while (cellGet(i) < 1000) {
        let idx = cellGet(i);
        arraySet(src, idx, intToF32(idx));
        cellSet(i, idx + 1)
    };
    let frozen: ImmArray Float32 = arrayFreeze(src);
    // Capture `frozen` (Send!) inside `parTabulate`'s $Shared closure across multicore workers
    let doubled: ImmArray Float32 = parTabulate(1000, (idx) -> immArrayGet(frozen, idx) * floatToF32(2.0));
    let acc = cellNew(intToF32(0));
    let k = cellNew(0);
    while (cellGet(k) < immArrayLen(doubled)) {
        cellSet(acc, cellGet(acc) + immArrayGet(doubled, cellGet(k)));
        cellSet(k, cellGet(k) + 1)
    };
    // sum_{i=0}^{999} 2*i = 999 * 1000 = 999000
    printLn(intToStr(immArrayLen(doubled)) + "|" + intToStr(f32ToInt(cellGet(acc))))
}
EOF
"$GEISHA_BIN" -o "$TMP_DIR/t28_imm_par" "$TMP_DIR/t28_imm_par.gsa"
assert_eq "imm_array_and_par_tabulate" "1000|999000" "$("$TMP_DIR/t28_imm_par")"

# 29. FFI Auto-Borrow (`ForeignPtr` -> `ScopedPtr` at `extern` boundary + mixed `ForeignPtr`/`Arena` `ScopedPtr` + keep-alive IR)
cat > "$TMP_DIR/t29_ffi_kernel.c" << 'EOF'
#include <stdint.h>
void vec_axpy_f32(const float *w, const float *x, float *out, int32_t n) {
    for (int32_t i = 0; i < n; i++) {
        out[i] = w[i] * x[i] + 1.0f;
    }
}
EOF
cat > "$TMP_DIR/t29_ffi_borrow.gsa" << 'EOF'
use std.str.intToStr

extern noalloc "vec_axpy_f32" def c_axpy(w: ScopedPtr, x: ScopedPtr, out: ScopedPtr, n: Int): Void

def runAxpy(): Int = {
    let w = foreignPtrAlloc(intToI64(16));
    let out = foreignPtrAlloc(intToI64(16));
    withForeignPtr(w, (pw) -> {
        scopedPtrWriteF32Le(pw, 0, floatToF32(2.0));
        scopedPtrWriteF32Le(pw, 4, floatToF32(3.0));
        scopedPtrWriteF32Le(pw, 8, floatToF32(4.0));
        scopedPtrWriteF32Le(pw, 12, floatToF32(5.0))
    });
    withArena((a) -> {
        let x = arenaAlloc(a, intToI64(16));
        scopedPtrWriteF32Le(x, 0, floatToF32(10.0));
        scopedPtrWriteF32Le(x, 4, floatToF32(10.0));
        scopedPtrWriteF32Le(x, 8, floatToF32(10.0));
        scopedPtrWriteF32Le(x, 12, floatToF32(10.0));
        // Mix ForeignPtr (`w`, `out`) and Arena ScopedPtr (`x`) directly in one flat extern call!
        c_axpy(w, x, out, 4)
    });
    withForeignPtr(out, (po) ->
        f32ToInt(
            scopedPtrReadF32Le(po, 0) + scopedPtrReadF32Le(po, 4)
            + scopedPtrReadF32Le(po, 8) + scopedPtrReadF32Le(po, 12)
        )
    )
}

def main(): Void = printLn(intToStr(runAxpy()))
EOF
"$GEISHA_BIN" -e -o "$TMP_DIR/t29_ffi_borrow.ll" "$TMP_DIR/t29_ffi_borrow.gsa"
if ! awk '/define .*@runAxpy\(/,/^}/' "$TMP_DIR/t29_ffi_borrow.ll" | grep -q "gc_foreign_ptr_get"; then
    echo "FAIL [ffi_auto_borrow_ir]: expected gc_foreign_ptr_get auto-unwrap in runAxpy" >&2
    exit 1
fi
if ! awk '/define .*@runAxpy\(/,/^}/' "$TMP_DIR/t29_ffi_borrow.ll" | grep -q "asm sideeffect"; then
    echo "FAIL [ffi_auto_borrow_ir]: expected keep-alive asm barrier after extern call in runAxpy" >&2
    exit 1
fi
echo "PASS [ffi_auto_borrow_ir]: ForeignPtr auto-unwrap + keep-alive barrier verified in LLVM IR"
PASS=$((PASS + 1))
"$CC" $HOST_CC_TARGET -O2 -Wno-override-module -pthread \
    -x ir "$TMP_DIR/t29_ffi_borrow.ll" -x c "$TMP_DIR/t29_ffi_kernel.c" -x none "$GEISHA_RUNTIME" $HOST_CC_LIBS \
    -o "$TMP_DIR/t29_ffi_borrow"
# (2*10+1) + (3*10+1) + (4*10+1) + (5*10+1) = 21 + 31 + 41 + 51 = 144
assert_eq "ffi_auto_borrow_exec" "144" "$("$TMP_DIR/t29_ffi_borrow")"

# 30. Zero-Keyword Generic Deriving (`data T : C1, C2 { ... }` & bodyless `instance C T`)
cat > "$TMP_DIR/t30_generic_derive.gsa" << 'EOF'
open std.generic
use std.str.intToStr

// Custom user Concept: DL-style `Params` (mapParams + zipParams) + `Describe` (reads field names!)
concept Params a {
    def mapParams(f: Int -> Int, x: a): a,
    def zipParams(f: (Int, Int) -> Int, x: a, y: a): a
}

instance Params Int {
    def mapParams(f, x) = f(x)
    def zipParams(f, x, y) = f(x, y)
}
instance Params Unit {
    def mapParams(_, u) = u
    def zipParams(_, u, _) = u
}
instance (Params a) => Params (Named a) {
    def mapParams(f, x) = match x { Named(k, v) -> Named(k, mapParams(f, v)) }
    def zipParams(f, x, y) = match (x, y) {
        (Named(k, a), Named(_, b)) -> Named(k, zipParams(f, a, b)),
    }
}
instance (Params a, Params b) => Params (Prod a b) {
    def mapParams(f, x) = match x { Prod(a, b) -> Prod(mapParams(f, a), mapParams(f, b)) }
    def zipParams(f, x, y) = match (x, y) {
        (Prod(a1, b1), Prod(a2, b2)) -> Prod(zipParams(f, a1, a2), zipParams(f, b1, b2)),
    }
}

concept FieldList a {
    def fieldNamesOf(x: a): String
}
instance FieldList Int { def fieldNamesOf(_) = "" }
instance FieldList Unit { def fieldNamesOf(_) = "" }
instance (FieldList a) => FieldList (Named a) {
    def fieldNamesOf(x) = match x { Named(k, _) -> k }
}
instance (FieldList a, FieldList b) => FieldList (Prod a b) {
    def fieldNamesOf(x) = match x { Prod(a, b) -> fieldNamesOf(a) + "," + fieldNamesOf(b) }
}

// Header-colon zero-keyword deriving + record-struct shorthand (no `Mk*`!)
data Linear : Params, Eq, FieldList {
    w: Int,
    b: Int,
}

data MLP : Params, Eq {
    l1: Linear,
    l2: Linear,
}

// Multi-constructor sum ADT deriving `Eq`!
data Act : Eq {
    ReLU,
    GELU,
    SwiGLU(Int),
}

// Polymorphic tuple/newtype shorthand + standalone bodyless `instance`!
data Box a (a)
instance (Eq a) => Eq (Box a)

// Tuple shorthand with inline `: Eq` deriving (both before and after parens)
data Pair2 a b (a, b) : Eq
data Tag : Eq (Int)

def main(): Void = {
    let m1 = MLP { l1: Linear { w: 2, b: 3 }, l2: Linear { w: 4, b: 5 } };
    let m2 = mapParams((x) -> x * 10, m1);
    let m3 = zipParams((a, b) -> a + b, m1, m2);
    let eqM = if (m1 == m1 && !(m1 == m2)) 1 else 0;
    let eqSum = if (ReLU == ReLU && !(ReLU == GELU) && SwiGLU(7) == SwiGLU(7) && !(SwiGLU(7) == SwiGLU(8))) 1 else 0;
    let eqBox = if (Box(42) == Box(42) && !(Box(42) == Box(99)) && Pair2(1, 2) == Pair2(1, 2) && Tag(7) == Tag(7)) 1 else 0;
    let fnames = fieldNamesOf(m1.l1);
    printLn(
        intToStr(m3.l1.w) + "|" + intToStr(m3.l2.b) + "|"
        + intToStr(eqM) + "|" + intToStr(eqSum) + "|" + intToStr(eqBox) + "|" + fnames
    )
}
EOF
"$GEISHA_BIN" -o "$TMP_DIR/t30_generic_derive" "$TMP_DIR/t30_generic_derive.gsa"
assert_eq "generic_zero_keyword_derive" "22|55|1|1|1|w,b" "$("$TMP_DIR/t30_generic_derive")"

# 31. Agent Tooling: `geisha guide`, `geisha doc`, `geisha check` (--json), & `file:line:col` Caret Diagnostics
GUIDE_OUT="$("$GEISHA_BIN" guide)"
if ! printf '%s' "$GUIDE_OUT" | grep -q "Top LLM Pitfalls"; then
    echo "FAIL [geisha_guide]: expected embedded Agent Guide output" >&2
    exit 1
fi
DOC_LIST="$("$GEISHA_BIN" doc)"
if ! printf '%s' "$DOC_LIST" | grep -q "std.option" || ! printf '%s' "$DOC_LIST" | grep -q "sys.fs"; then
    echo "FAIL [geisha_doc_list]: expected std.option and sys.fs in module list" >&2
    exit 1
fi
DOC_OPT="$("$GEISHA_BIN" doc std.option)"
if ! printf '%s' "$DOC_OPT" | grep -q "pub def unwrapOr"; then
    echo "FAIL [geisha_doc_builtin]: expected pub def unwrapOr in std.option" >&2
    exit 1
fi
cat > "$TMP_DIR/t31_doc_sample.gsa" << 'EOF'
/// Adds two integers together.
pub def addNums(a: Int, b: Int): Int = a + b

def secretHelper(x: Int): Int = x
EOF
DOC_FILE_PUB="$("$GEISHA_BIN" doc "$TMP_DIR/t31_doc_sample.gsa")"
if ! printf '%s' "$DOC_FILE_PUB" | grep -q "/// Adds two integers together." || ! printf '%s' "$DOC_FILE_PUB" | grep -q "pub def addNums" || printf '%s' "$DOC_FILE_PUB" | grep -q "secretHelper"; then
    echo "FAIL [geisha_doc_file]: expected doc comment + pub def only" >&2
    exit 1
fi
DOC_FILE_ALL="$("$GEISHA_BIN" doc "$TMP_DIR/t31_doc_sample.gsa" --all)"
if ! printf '%s' "$DOC_FILE_ALL" | grep -q "def secretHelper"; then
    echo "FAIL [geisha_doc_all]: expected private def with --all" >&2
    exit 1
fi

cat > "$TMP_DIR/t31_ok.gsa" << 'EOF'
def main(): Void = printLn("ok")
EOF
CHK_OK="$("$GEISHA_BIN" check --json "$TMP_DIR/t31_ok.gsa")"
if ! printf '%s' "$CHK_OK" | grep -q '"ok":true'; then
    echo "FAIL [geisha_check_ok]: expected ok:true json, got: $CHK_OK" >&2
    exit 1
fi

cat > "$TMP_DIR/t31_bad_type.gsa" << 'EOF'
def main(): Void = {
    let x: Int = "wrong";
    ()
}
EOF
set +e
CHK_BAD="$("$GEISHA_BIN" check "$TMP_DIR/t31_bad_type.gsa" 2>&1)"
CHK_BAD_RC=$?
CHK_BAD_JSON="$("$GEISHA_BIN" check --json "$TMP_DIR/t31_bad_type.gsa")"
CHK_BAD_JSON_RC=$?
set -e
if [ "$CHK_BAD_RC" -eq 0 ] || [ "$CHK_BAD_JSON_RC" -eq 0 ]; then
    echo "FAIL [geisha_check_bad_rc]: expected non-zero exit code on type error" >&2
    exit 1
fi
if ! printf '%s' "$CHK_BAD" | grep -q 't31_bad_type.gsa:2:18: error\[type\]: `"wrong"` has type `String`, expected `Int`' || ! printf '%s' "$CHK_BAD" | grep -q 'line 2: let x: Int = "wrong";'; then
    echo "FAIL [geisha_diag_1d]: expected inline term + expected/found + line output, got: $CHK_BAD" >&2
    exit 1
fi
if ! printf '%s' "$CHK_BAD_JSON" | grep -q '"ok":false' || ! printf '%s' "$CHK_BAD_JSON" | grep -q 't31_bad_type.gsa:2:18'; then
    echo "FAIL [geisha_check_bad_json]: expected ok:false json with line:col, got: $CHK_BAD_JSON" >&2
    exit 1
fi

# Verify per-argument term pinpointing on function calls
cat > "$TMP_DIR/t31_bad_call.gsa" << 'EOF'
def add2(a: Int, b: Int): Int = a + b
def main(): Void = {
    let _ = add2(1, "oops");
    ()
}
EOF
set +e
CHK_CALL="$("$GEISHA_BIN" check "$TMP_DIR/t31_bad_call.gsa" 2>&1)"
CHK_CALL_RC=$?
set -e
if [ "$CHK_CALL_RC" -eq 0 ] || ! printf '%s' "$CHK_CALL" | grep -q 't31_bad_call.gsa:3:21: error\[type\]: `"oops"` has type `String`, expected `Int`'; then
    echo "FAIL [geisha_diag_call_arg]: expected exact argument term pinpointing, got: $CHK_CALL" >&2
    exit 1
fi

# Verify actionable hint on common pitfall (missing `else` in `if`)
cat > "$TMP_DIR/t31_bad_if.gsa" << 'EOF'
def main(): Void = {
    if (true) printLn("hi")
}
EOF
set +e
CHK_IF="$("$GEISHA_BIN" check "$TMP_DIR/t31_bad_if.gsa" 2>&1)"
CHK_IF_RC=$?
set -e
if [ "$CHK_IF_RC" -eq 0 ] || ! printf '%s' "$CHK_IF" | grep -q 'hint: add `else ()`'; then
    echo "FAIL [geisha_diag_hint]: expected actionable else() hint, got: $CHK_IF" >&2
    exit 1
fi
echo "PASS [agent_tooling_and_diagnostics]: geisha guide, doc, check (--json), and 1D file:line:col + near + hint diagnostics verified"
PASS=$((PASS + 1))

# ---- 32. Script Mode: shebang, top-level statements, cached `geisha run`, `geisha eval` ----
SCRIPT_HOME="$TMP_DIR/script_home"
mkdir -p "$SCRIPT_HOME"

# 32a: Top-level script without `def main()` + helper def + `use` + direct arg passthrough + warm cache
cat > "$TMP_DIR/t32_helper.gsa" << 'EOF'
pub def tag(): String = "v1"
EOF

cat > "$TMP_DIR/t32_script.gsa" << 'EOF'
#!/usr/bin/env -S geisha run
use std.str.intToStr
use sys.env.{argCount, argAt}
use t32_helper.tag

def twice(n: Int): Int = n * 2

let n = 21
let arg1 = if (argCount() > 1) argAt(1) else "none"
printLn(tag() + ":" + intToStr(twice(n)) + ":" + arg1)
n + 1
EOF

OUT_S1="$(HOME="$SCRIPT_HOME" "$GEISHA_BIN" run --runtime "$GEISHA_RUNTIME" "$TMP_DIR/t32_script.gsa" --flag42)"
if [ "$OUT_S1" != "v1:42:--flag42" ]; then
    echo "FAIL [script_mode_cold]: expected 'v1:42:--flag42', got '$OUT_S1'" >&2
    exit 1
fi
# Warm cache hit (with different arg)
OUT_S2="$(HOME="$SCRIPT_HOME" "$GEISHA_BIN" run --runtime "$GEISHA_RUNTIME" "$TMP_DIR/t32_script.gsa" --warm)"
if [ "$OUT_S2" != "v1:42:--warm" ]; then
    echo "FAIL [script_mode_warm]: expected 'v1:42:--warm', got '$OUT_S2'" >&2
    exit 1
fi
# Direct executable shebang invocation (`./t32_script.gsa`)
chmod +x "$TMP_DIR/t32_script.gsa"
SCRIPT_BIN_DIR="$TMP_DIR/script_bin"
mkdir -p "$SCRIPT_BIN_DIR"
ln -sf "$(cd "$(dirname "$GEISHA_BIN")" && pwd)/$(basename "$GEISHA_BIN")" "$SCRIPT_BIN_DIR/geisha"
OUT_SHEBANG="$(HOME="$SCRIPT_HOME" PATH="$SCRIPT_BIN_DIR:$PATH" GEISHA_RUNTIME="$GEISHA_RUNTIME" "$TMP_DIR/t32_script.gsa" --shebang)"
if [ "$OUT_SHEBANG" != "v1:42:--shebang" ]; then
    echo "FAIL [script_mode_shebang]: expected 'v1:42:--shebang', got '$OUT_SHEBANG'" >&2
    exit 1
fi
# Modify imported local dependency -> cache must automatically invalidate!
cat > "$TMP_DIR/t32_helper.gsa" << 'EOF'
pub def tag(): String = "v2"
EOF
OUT_S3="$(HOME="$SCRIPT_HOME" "$GEISHA_BIN" run --runtime "$GEISHA_RUNTIME" "$TMP_DIR/t32_script.gsa" --after-edit)"
if [ "$OUT_S3" != "v2:42:--after-edit" ]; then
    echo "FAIL [script_mode_dep_invalidation]: expected 'v2:42:--after-edit', got '$OUT_S3'" >&2
    exit 1
fi

# 32b: `geisha eval` inline snippet with args
OUT_EVAL="$(HOME="$SCRIPT_HOME" "$GEISHA_BIN" eval --runtime "$GEISHA_RUNTIME" 'use sys.env.argAt; let x = "ok"; printLn(x + ":" + argAt(1))' hello)"
if [ "$OUT_EVAL" != "ok:hello" ]; then
    echo "FAIL [geisha_eval]: expected 'ok:hello', got '$OUT_EVAL'" >&2
    exit 1
fi

# 32c: Mixing top-level script statements and explicit `def main()` must error cleanly
cat > "$TMP_DIR/t32_mix_err.gsa" << 'EOF'
printLn("top")
def main(): Void = printLn("main")
EOF
set +e
MIX_ERR="$("$GEISHA_BIN" check "$TMP_DIR/t32_mix_err.gsa" 2>&1)"
MIX_RC=$?
set -e
if [ "$MIX_RC" -eq 0 ] || ! printf '%s' "$MIX_ERR" | grep -q 'cannot mix top-level script statements'; then
    echo "FAIL [script_mode_mix_err]: expected error when mixing top-level stmts and def main, got: $MIX_ERR" >&2
    exit 1
fi

echo "PASS [script_mode]: shebang, top-level statements, cached geisha run (+ dep invalidation), and geisha eval verified"
PASS=$((PASS + 1))

# 33. Shadowed heap Cell write-barrier soundness + >4KB large-object GC survival + gc_set_mem_limit
cat > "$TMP_DIR/t33_gc_shadow_wb.gsa" << 'EOF'
use std.str.intToStr

extern "gc_collect_major" def gcCollectMajor(): Void
extern "gc_set_mem_limit" def gcSetMemLimit(bytes: Int64): Void

def makeHeapCell(init: String): Cell String = cellNew(init)

def mutateShadowed(x: Cell String, n: Int): Int = {
    // Mutate old-gen heap Cell `x` with a freshly allocated young String:
    cellSet(x, "young-" + intToStr(n) + "-" + intToStr(n * 3));
    // Shadow `x` with a pure non-escaping local Cell in the same function:
    let x = cellNew(n + 10);
    cellSet(x, cellGet(x) + 1);
    cellGet(x)
}

def main(): Void = {
    gcSetMemLimit(intToI64(16 * 1024 * 1024));
    let oldCell = makeHeapCell("initial");
    // Promote `oldCell` + a >4KB large Array into Old generation
    let big = arrayNew(2048, "seed");
    arraySet(big, 1023, "mid-" + intToStr(1023));
    gcCollectMajor();

    let r = mutateShadowed(oldCell, 77);
    // Churn nursery to trigger Minor GCs without touching `oldCell` directly on stack
    let i = cellNew(0);
    while (cellGet(i) < 20000) {
        let k = cellGet(i);
        let _tmp = "churn-" + intToStr(k);
        cellSet(i, k + 1)
    };
    printLn(cellGet(oldCell) + "|" + arrayGet(big, 1023) + "|" + intToStr(r))
}
EOF
"$GEISHA_BIN" --runtime "$GEISHA_RUNTIME" -o "$TMP_DIR/t33_gc_shadow_wb" "$TMP_DIR/t33_gc_shadow_wb.gsa"
OUT_T33="$(GEISHA_GC_HEAP_WORDS=8192 "$TMP_DIR/t33_gc_shadow_wb")"
assert_eq "gc_shadow_wb_and_large_obj" "young-77-231|mid-1023|88" "$OUT_T33"
echo "PASS [gc_shadow_wb_and_large_obj]: shadowed heap Cell write barrier, >4KB large object survival, and gc_set_mem_limit verified"
PASS=$((PASS + 1))

# 34. Pure C ABI unified `extern` exports, `extern data` (ARM64 HFA & x86_64 SysV), `cFnPtr`, `extern ptr`, `extern init`, & `sys.ffi`
cat > "$TMP_DIR/t34_cabi_host.c" << 'EOF'
#include <stdint.h>
#include <stdio.h>

typedef struct { double x; double y; } CGPoint;
typedef struct { double w; double h; } CGSize;
typedef struct { CGPoint origin; CGSize size; } CGRect;
typedef struct { int32_t a; double b; } Mixed;
typedef struct { int64_t a; int64_t b; int64_t c; } Big3;

/* Pure C ABI exports from Geisha (NO trailing `void *fv`!) */
extern int32_t gs_pure_add(int32_t a, int32_t b);
extern int32_t defaultNameMul(int32_t a, int32_t b);
extern CGRect gs_scale_rect(CGRect r, double k);
extern Big3 gs_bump_big3(Big3 v);
extern Mixed gs_bump_mixed(Mixed m);

CGRect c_make_rect(CGPoint p, CGSize s) {
    CGRect r;
    r.origin = p;
    r.size = s;
    return r;
}

double c_rect_sum(CGRect r) {
    return r.origin.x + r.origin.y + r.size.w + r.size.h;
}

Big3 c_add_big3(Big3 x, Big3 y) {
    Big3 out;
    out.a = x.a + y.a;
    out.b = x.b + y.b;
    out.c = x.c + y.c;
    return out;
}

Mixed c_make_mixed(int32_t a, double b) {
    Mixed m;
    m.a = a;
    m.b = b;
    return m;
}

double c_apply_rect_cb(double (*cb)(CGRect, int32_t), CGRect r, int32_t bonus) {
    return cb(r, bonus);
}

int32_t c_check_exports(void) {
    int32_t s = gs_pure_add(19, 23);
    int32_t p = defaultNameMul(6, 7);
    CGRect r0 = { { 1.0, 2.0 }, { 3.0, 4.0 } };
    CGRect r1 = gs_scale_rect(r0, 2.0);
    Big3 b0 = { 10, 20, 30 };
    Big3 b1 = gs_bump_big3(b0);
    Mixed m0 = { 5, 2.5 };
    Mixed m1 = gs_bump_mixed(m0);
    int32_t ok = (s == 42)
        && (p == 42)
        && (r1.origin.x == 2.0 && r1.origin.y == 4.0 && r1.size.w == 6.0 && r1.size.h == 8.0)
        && (b1.a == 11 && b1.b == 22 && b1.c == 33)
        && (m1.a == 6 && m1.b == 5.0);
    return ok ? 1 : 0;
}
EOF

cat > "$TMP_DIR/t34_cabi.gsa" << 'EOF'
use std.str.intToStr
use std.option.{Some, None}
use std.sync.{Chan, chanNew, chanSend, chanRecv}
use sys.ffi.{dlOpenSelf, dlSym}

extern "gc_collect_major" def gcCollectMajor(): Void
extern "gc_trim" def gcTrim(): Void

pub extern data CGPoint { x: Float, y: Float }
pub extern data CGSize { w: Float, h: Float }
pub extern data CGRect { origin: CGPoint, size: CGSize }
pub extern data Mixed { a: Int, b: Float }
pub extern data Big3 { a: Int64, b: Int64, c: Int64 }

extern "c_make_rect" def cMakeRect(p: CGPoint, s: CGSize): CGRect
extern "c_rect_sum" def cRectSum(r: CGRect): Float
extern "c_add_big3" def cAddBig3(x: Big3, y: Big3): Big3
extern "c_make_mixed" def cMakeMixed(a: Int, b: Float): Mixed
extern "c_apply_rect_cb" def cApplyRectCb(cb: Ptr, r: CGRect, bonus: Int): Float
extern "c_check_exports" def cCheckExports(): Int
extern ptr def callRectSumPtr(fnPtr: Ptr, r: CGRect): Float

// Verify `@` remains an ordinary infix operator without newline ambiguity
def (@)(a: Int, b: Int): Int = a * 10 + b

def gCtorLog: Cell Int = cellNew(0)
def gCtorChan: Chan String = chanNew(8)
def gCtorItems: Cell (List String) = cellNew(["boot-seed"])

extern init(200) def initSecond(): Void = {
    cellSet(gCtorLog, cellGet(gCtorLog) * 10 + 2);
    let _ = chanSend(gCtorChan, "ctor-second");
    cellSet(gCtorItems, Cons("second", cellGet(gCtorItems)))
}

extern init(100) def initFirst(): Void = {
    cellSet(gCtorLog, cellGet(gCtorLog) * 10 + 1);
    let _ = chanSend(gCtorChan, "ctor-first");
    cellSet(gCtorItems, Cons("first", cellGet(gCtorItems)))
}

pub extern "gs_pure_add" def pureAdd(a: Int, b: Int): Int = a + b
pub extern def defaultNameMul(a: Int, b: Int): Int = a * b

pub extern "gs_scale_rect" def scaleRect(r: CGRect, k: Float): CGRect =
    CGRect {
        origin: CGPoint { x: r.origin.x * k, y: r.origin.y * k },
        size: CGSize { w: r.size.w * k, h: r.size.h * k },
    }

pub extern "gs_bump_big3" def bumpBig3(v: Big3): Big3 =
    Big3 { a: v.a + intToI64(1), b: v.b + intToI64(2), c: v.c + intToI64(3) }

pub extern "gs_bump_mixed" def bumpMixed(m: Mixed): Mixed =
    Mixed { a: m.a + 1, b: m.b * 2.0 }

def rectCallback(r: CGRect, bonus: Int): Float =
    r.origin.x + r.origin.y + r.size.w + r.size.h + intToFloat(bonus)

def main(): Void = {
    let r = cMakeRect(CGPoint { x: 1.5, y: 2.5 }, CGSize { w: 10.0, h: 20.0 });
    let s1 = floatToInt(cRectSum(r));
    let s2 = floatToInt(callRectSumPtr(cFnPtr(cRectSum), r));
    let cbRes = floatToInt(cApplyRectCb(cFnPtr(rectCallback), r, 8));
    let b = cAddBig3(
        Big3 { a: intToI64(10), b: intToI64(20), c: intToI64(30) },
        Big3 { a: intToI64(1), b: intToI64(2), c: intToI64(3) }
    );
    let bSum = i64ToInt(b.a + b.b + b.c);
    let m = cMakeMixed(7, 3.0);
    let mSum = m.a + floatToInt(m.b);
    let expOk = cCheckExports();
    let atOp = 3 @ 7;
    let gsCallMul = defaultNameMul(3, 4);
    let dlOk = match dlSym(dlOpenSelf(), "strlen") {
        Some(_) -> 1,
        None -> 0,
    };
    // Force multiple Minor & Major GC sweeps after `extern init` + `gc_init_with_stack`
    // to verify global roots (`gCtorChan`, `gCtorItems`, `gCtorLog`) survive intact.
    let churn = cellNew(0);
    while (cellGet(churn) < 2000) {
        let k = cellGet(churn);
        let _ = "churn-heap-payload-" + intToStr(k);
        cellSet(churn, k + 1)
    };
    gcCollectMajor();
    gcTrim();
    let ch1 = match chanRecv(gCtorChan) { Some(s) -> s, None -> "missing1" };
    let ch2 = match chanRecv(gCtorChan) { Some(s) -> s, None -> "missing2" };
    let itemsDesc = match cellGet(gCtorItems) {
        Cons(a, Cons(b, Cons(c, Nil))) -> a + "," + b + "," + c,
        _ -> "bad-items",
    };
    printLn(
        intToStr(cellGet(gCtorLog)) + "|"
        + intToStr(s1) + "|" + intToStr(s2) + "|" + intToStr(cbRes) + "|"
        + intToStr(bSum) + "|" + intToStr(mSum) + "|" + intToStr(expOk) + "|" + intToStr(dlOk) + "|" + intToStr(atOp) + "|" + intToStr(gsCallMul) + "|"
        + ch1 + "+" + ch2 + "|" + itemsDesc
    )
}
EOF
"$GEISHA_BIN" -e -o "$TMP_DIR/t34_cabi.ll" "$TMP_DIR/t34_cabi.gsa"
"$CC" $HOST_CC_TARGET -O2 -Wno-override-module -pthread \
    -x ir "$TMP_DIR/t34_cabi.ll" -x c "$TMP_DIR/t34_cabi_host.c" -x none "$GEISHA_RUNTIME" $HOST_CC_LIBS \
    -o "$TMP_DIR/t34_cabi"
assert_eq "cabi_cstruct_export_ctor_cfnptr" "12|34|34|42|66|10|1|1|37|12|ctor-first+ctor-second|second,first,boot-seed" "$(GEISHA_GC_HEAP_WORDS=4096 "$TMP_DIR/t34_cabi")"

# Verify `--no-main` C-exported library initializes globals lazily & thread-safely even when C pthreads call exports without `__geisha_init()`
cat > "$TMP_DIR/t34_lazy_glob.gsa" << 'EOF'
use std.str.intToStr
use std.sync.{AtomicInt, atomicNew, atomicAdd, atomicLoad}

extern "gc_collect_major" def gcCollectMajor(): Void

def makeHeavySeed(): String = {
    let i = cellNew(0);
    let acc = cellNew("lazy");
    while (cellGet(i) < 600) {
        let k = cellGet(i);
        cellSet(acc, "seed-" + intToStr(k));
        cellSet(i, k + 1)
    };
    gcCollectMajor();
    cellGet(acc)
}

def gLazySeed: String = makeHeavySeed()
def gLazyHits: AtomicInt = atomicNew(0)

pub extern "gs_lazy_ping" def lazyPing(delta: Int): Int = {
    let _ = atomicAdd(gLazyHits, delta);
    strLen(gLazySeed)
}

pub extern "gs_lazy_total" def lazyTotal(): Int = atomicLoad(gLazyHits)
EOF
cat > "$TMP_DIR/t34_lazy_glob_host.c" << 'EOF'
#include <pthread.h>
#include <stdint.h>
#include <stdio.h>

extern int32_t gs_lazy_ping(int32_t delta);
extern int32_t gs_lazy_total(void);

static volatile int g_go = 0;

static void *worker_fn(void *arg) {
    int32_t id = (int32_t)(intptr_t)arg;
    while (!__atomic_load_n(&g_go, __ATOMIC_ACQUIRE)) {}
    int32_t len = gs_lazy_ping(id);
    return (void *)(intptr_t)len;
}

int main(void) {
    pthread_t th[4];
    for (int i = 0; i < 4; i++) {
        pthread_create(&th[i], NULL, worker_fn, (void *)(intptr_t)(i + 1));
    }
    __atomic_store_n(&g_go, 1, __ATOMIC_RELEASE);
    int32_t lens_ok = 1;
    for (int i = 0; i < 4; i++) {
        void *ret = NULL;
        pthread_join(th[i], &ret);
        if ((int32_t)(intptr_t)ret != 8) lens_ok = 0;
    }
    printf("%d|%d\n", lens_ok, (int)gs_lazy_total());
    return 0;
}
EOF
"$GEISHA_BIN" -e --no-main -o "$TMP_DIR/t34_lazy_glob.ll" "$TMP_DIR/t34_lazy_glob.gsa"
"$CC" $HOST_CC_TARGET -O2 -Wno-override-module -pthread \
    -x ir "$TMP_DIR/t34_lazy_glob.ll" -x c "$TMP_DIR/t34_lazy_glob_host.c" -x none "$GEISHA_RUNTIME" $HOST_CC_LIBS \
    -o "$TMP_DIR/t34_lazy_glob"
assert_eq "cabi_no_main_concurrent_lazy_globals" "1|10" "$(GEISHA_GC_HEAP_WORDS=4096 "$TMP_DIR/t34_lazy_glob")"

# Negative checks for `extern data`, `extern init`, and `cFnPtr`
cat > "$TMP_DIR/t34_bad_cstruct.gsa" << 'EOF'
extern data Bad { s: String }
def main(): Void = ()
EOF
if "$GEISHA_BIN" check "$TMP_DIR/t34_bad_cstruct.gsa" >/dev/null 2>&1; then
    echo "FAIL [bad_cstruct_rejected]: extern data with String field should be rejected" >&2
    exit 1
fi

cat > "$TMP_DIR/t34_bad_ctor.gsa" << 'EOF'
extern init def badInit(x: Int): Int = x
def main(): Void = ()
EOF
if "$GEISHA_BIN" check "$TMP_DIR/t34_bad_ctor.gsa" >/dev/null 2>&1; then
    echo "FAIL [bad_ctor_rejected]: extern init with non-()->Void signature should be rejected" >&2
    exit 1
fi

cat > "$TMP_DIR/t34_bad_cfnptr.gsa" << 'EOF'
def main(): Void = {
    let f = (x: Int) -> x + 1;
    let _ = cFnPtr(f);
    ()
}
EOF
if "$GEISHA_BIN" -e "$TMP_DIR/t34_bad_cfnptr.gsa" >/dev/null 2>&1; then
    echo "FAIL [bad_cfnptr_rejected]: cFnPtr on local closure should be rejected" >&2
    exit 1
fi
echo "PASS [cabi_primitives]: unified extern export, extern data (HFA/SysV/sret), cFnPtr, extern ptr, extern init, sys.ffi, & negative checks verified"
PASS=$((PASS + 1))

# 35. Direct C/ObjC Runtime interop (`extern data`, multi-sig `extern`, `extern init`, `cFnPtr`) & Apple `.app`/`.appex` Bundles (macOS only)
if [ "$(uname -s)" = "Darwin" ]; then
    MAC_APP_DIR="$TMP_DIR/pure_objc_app"
    mkdir -p "$MAC_APP_DIR/src"
    cat > "$MAC_APP_DIR/geisha.toml" << 'EOF'
name = "pure_objc_app"
version = "0.2.0"
entry = "src/main.gsa"

[target.macos]
bundle_id    = "com.geisha.test.pureobjc"
bundle_name  = "PureObjcTest"
min_os       = "14.0"
frameworks   = ["Foundation", "AppKit"]
link_flags   = ["-lobjc"]
lsui_element = true
codesign     = "-"
EOF
    cat > "$MAC_APP_DIR/src/main.gsa" << 'EOF'
use std.str.intToStr

extern data CGPoint { x: Float, y: Float }
extern data CGSize { w: Float, h: Float }
extern data CGRect { origin: CGPoint, size: CGSize }

extern "objc_getClass" def objcGetClass(name: String): Ptr
extern "sel_registerName" def selReg(name: String): Ptr
extern "objc_allocateClassPair" def objcAllocClass(sup: Ptr, name: String, extra: Int64): Ptr
extern "class_addMethod" def classAddMethod(cls: Ptr, sel: Ptr, imp: Ptr, enc: String): Bool
extern "objc_registerClassPair" def objcRegClass(cls: Ptr): Void
extern "objc_autoreleasePoolPush" def arPush(): Ptr
extern "objc_autoreleasePoolPop" def arPop(p: Ptr): Void

extern "objc_msgSend" def msgSend0(obj: Ptr, sel: Ptr): Ptr
extern "objc_msgSend" def msgSendStr(obj: Ptr, sel: Ptr, s: String): Ptr
extern "objc_msgSend" def msgSendInt0(obj: Ptr, sel: Ptr): Int
extern "objc_msgSend" def msgSendValueWithRect(cls: Ptr, sel: Ptr, rect: CGRect): Ptr
extern "objc_msgSend" def msgSendRectValue(obj: Ptr, sel: Ptr): CGRect

def gBonus: Cell Int = cellNew(32)

def customComputeImp(self: Ptr, _cmd: Ptr): Int = {
    let _ = self;
    let _ = _cmd;
    cellSet(gBonus, cellGet(gBonus) + 10);
    cellGet(gBonus)
}

extern init def registerGeishaObjcClass(): Void = {
    let sup = objcGetClass("NSObject");
    let cls = objcAllocClass(sup, "GeishaNativeTestObj", intToI64(0));
    if (!ptrIsNull(cls)) {
        let _ = classAddMethod(cls, selReg("computeValue"), cFnPtr(customComputeImp), "i@:");
        objcRegClass(cls)
    } else ()
}

def main(): Void = {
    let pool = arPush();

    // 1. NSString UTF-8 round-trip via direct `objc_msgSend`
    let nsStrCls = objcGetClass("NSString");
    let ns = msgSendStr(nsStrCls, selReg("stringWithUTF8String:"), "句序-Slate-Talus");
    let roundtrip = ptrToString(msgSend0(ns, selReg("UTF8String")));

    // 2. CGRect HFA pass & return through real Apple Foundation `NSValue` via multi-sig `objc_msgSend`
    let nsValCls = objcGetClass("NSValue");
    let inRect = CGRect { origin: CGPoint { x: 12.0, y: 34.0 }, size: CGSize { w: 100.0, h: 200.0 } };
    let valObj = msgSendValueWithRect(nsValCls, selReg("valueWithRect:"), inRect);
    let outRect = msgSendRectValue(valObj, selReg("rectValue"));
    let rectSum = floatToInt(outRect.origin.x + outRect.origin.y + outRect.size.w + outRect.size.h);

    // 3. Dynamic ObjC subclass registered in `extern init`
    let testCls = objcGetClass("GeishaNativeTestObj");
    let inst = msgSend0(msgSend0(testCls, selReg("alloc")), selReg("init"));
    let computed = msgSendInt0(inst, selReg("computeValue"));

    printLn(roundtrip + "|" + intToStr(rectSum) + "|" + intToStr(computed));
    arPop(pool)
}
EOF
    ABS_GEISHA_BIN="$(cd "$(dirname "$GEISHA_BIN")" && pwd)/$(basename "$GEISHA_BIN")"
    ABS_GEISHA_RT="$(cd "$(dirname "$GEISHA_RUNTIME")" && pwd)/$(basename "$GEISHA_RUNTIME")"
    (cd "$MAC_APP_DIR" && "$ABS_GEISHA_BIN" build --target macos-app --runtime "$ABS_GEISHA_RT")
    APP_BUNDLE="$MAC_APP_DIR/build/PureObjcTest.app"
    if [ ! -f "$APP_BUNDLE/Contents/Info.plist" ] || [ ! -x "$APP_BUNDLE/Contents/MacOS/PureObjcTest" ]; then
        echo "FAIL [macos_app_bundle]: missing Info.plist or executable in $APP_BUNDLE" >&2
        exit 1
    fi
    plutil -lint "$APP_BUNDLE/Contents/Info.plist" >/dev/null
    codesign --verify "$APP_BUNDLE"
    OUT_MAC_APP="$("$APP_BUNDLE/Contents/MacOS/PureObjcTest")"
    assert_eq "pure_geisha_objc_macos_app" "句序-Slate-Talus|346|42" "$OUT_MAC_APP"
    echo "PASS [pure_geisha_objc_macos_app]: zero-.m pure Geisha macOS .app bundle + NSString + CGRect objc_msgSend + extern init subclass verified!"
    PASS=$((PASS + 1))

    # Also verify pure-Geisha iOS Simulator `.appex` extension packaging when iOS sim runtime is built
    if [ -f "build/libgeisha_runtime_ios_sim.a" ]; then
        ABS_IOS_SIM_RT="$(pwd)/build/libgeisha_runtime_ios_sim.a"
        IOS_EXT_DIR="$TMP_DIR/pure_ios_ext"
        mkdir -p "$IOS_EXT_DIR/src"
        cat > "$IOS_EXT_DIR/geisha.toml" << 'EOF'
name = "pure_ios_ext"
version = "0.1.0"
entry = "src/main.gsa"

[target.ios]
bundle_id       = "com.geisha.test.keyboard"
bundle_name     = "GeishaKeyboard"
min_os          = "16.0"
frameworks      = ["Foundation", "UIKit"]
link_flags      = ["-lobjc"]
is_extension    = true
extension_point = "com.apple.keyboard-service"
principal_class = "GeishaKeyboardController"
codesign        = "-"
EOF
        cat > "$IOS_EXT_DIR/src/main.gsa" << 'EOF'
extern "objc_getClass" def objcGetClass(name: String): Ptr
extern "objc_allocateClassPair" def objcAllocClass(sup: Ptr, name: String, extra: Int64): Ptr
extern "objc_registerClassPair" def objcRegClass(cls: Ptr): Void

extern init def registerKeyboardController(): Void = {
    let sup = objcGetClass("UIInputViewController");
    let cls = objcAllocClass(sup, "GeishaKeyboardController", intToI64(0));
    if (!ptrIsNull(cls)) objcRegClass(cls) else ()
}
EOF
        (cd "$IOS_EXT_DIR" && "$ABS_GEISHA_BIN" build --target ios-sim-app --runtime "$ABS_IOS_SIM_RT")
        EXT_BUNDLE="$IOS_EXT_DIR/build/GeishaKeyboard.appex"
        if [ ! -f "$EXT_BUNDLE/Info.plist" ] || [ ! -x "$EXT_BUNDLE/GeishaKeyboard" ]; then
            echo "FAIL [ios_sim_appex_bundle]: missing Info.plist or binary in $EXT_BUNDLE" >&2
            exit 1
        fi
        plutil -lint "$EXT_BUNDLE/Info.plist" >/dev/null
        if ! grep -q "GeishaKeyboardController" "$EXT_BUNDLE/Info.plist" || ! grep -q "com.apple.keyboard-service" "$EXT_BUNDLE/Info.plist"; then
            echo "FAIL [ios_sim_appex_plist]: missing NSExtensionPrincipalClass or NSExtensionPointIdentifier in Info.plist" >&2
            exit 1
        fi
        echo "PASS [ios_sim_appex_bundle]: pure Geisha iOS Simulator .appex extension with extern init UIInputViewController subclass built and signed!"
        PASS=$((PASS + 1))
    fi
fi

# 36. Radix/Separator Literals (`0x`/`0o`/`0b`/`_`), `sys.fs` Atomic Writes, `sys.proc` Subprocesses, `std.toml.patch`, & `geisha.local.toml` Target Overrides
cat > "$TMP_DIR/t36_sys_and_toml.gsa" << 'EOF'
use std.option.{Option, Some, None}
use std.result.{Result, Ok, Err}
use std.str.{intToStr, strStartsWith}
use std.codec.{Value, VBool, VInt, VFloat, VStr, VArr, VObj}
use std.toml.{parse as tomlParse, patch as tomlPatch}
use sys.fs.{
    readFile, writeFileAtomic, writeFileAtomicMode, renameFile, chmod, fileMtimeMs
}
use sys.proc.{
    Stdio, Null, Piped, EnvMode, ReplaceEnv, Signal, SigTerm,
    ExitStatus, Exited, Signaled, Output,
    command, cmdCwd, cmdEnv, cmdEnvMode, cmdStdio, cmdOwnGroup,
    spawn, childWait, childSignal, pipeWrite, pipeClose, pipeReadAll,
    run, runTimeout
}

def hasSubstr(hay: String, needle: String): Bool = {
    let hl = strLen(hay);
    let nl = strLen(needle);
    if (nl == 0) true
    else if (nl > hl) false
    else {
        let limit = hl - nl;
        let i = cellNew(0);
        let found = cellNew(false);
        while (cellGet(i) <= limit && !cellGet(found)) {
            let cur = cellGet(i);
            if (strStartsWith(strSlice(hay, cur, cur + nl), needle)) {
                cellSet(found, true)
            } else {
                cellSet(i, cur + 1)
            }
        };
        cellGet(found)
    }
}

def classifyMode(m: Int): String = match m {
    0o600 -> "priv",
    0o755 -> "exec",
    -0x80 -> "neg128",
    _ -> "other",
}

def main(): Result Void String = {
    // 1. Radix & `_`-separated numeric literals + pattern matching
    let hexMask = 0x_DEAD_BEEF;
    let hi16 = (hexMask >>> 16) & 0xFFFF;
    let octPerm = 0o600;
    let binBits = 0b_1010_0101;
    let decSep = 1_000_000;
    let minI32 = -0x8000_0000;
    let fltSep = 1_000.25_0 + 1.5e1_0 - 1.5e10;
    let patRes = classifyMode(0o600) + ":" + classifyMode(0o755) + ":" + classifyMode(-0x80);

    // 2. `sys.fs`: atomic write with explicit 0o600, mode preservation on overwrite, chmod, rename, mtime
    let baseDir = sysArgv(1);
    let secretPath = baseDir + "/secret.toml";
    let movedPath = baseDir + "/secret_moved.toml";
    writeFileAtomicMode(secretPath, "token = 1\n", 0o600)?;
    writeFileAtomic(secretPath, "token = 2\n")?;
    let secretText = readFile(secretPath)?;
    let mtime = fileMtimeMs(secretPath)?;
    let execPath = baseDir + "/script.sh";
    writeFileAtomic(execPath, "#!/bin/sh\nexit 0\n")?;
    chmod(execPath, 0o755)?;
    renameFile(secretPath, movedPath)?;
    let movedText = readFile(movedPath)?;

    // 3. `sys.proc`:
    // 3a. `run` with `cmdCwd`, `OverrideEnv`, empty arg `""`, and >128KB simultaneous stdout+stderr (no deadlock!)
    let pyDual =
        "import os, sys; "
        + "a1 = sys.argv[1]; a2 = sys.argv[2]; "
        + "cwd_base = os.path.basename(os.getcwd()); "
        + "ev = os.environ.get('GS_TEST_VAR', ''); "
        + "sys.stdout.write(cwd_base + '|' + str(len(a1)) + '|' + a2 + '|' + ev + '|'); "
        + " chunk = 'O' * 4096; echunk = 'E' * 4096;\n"
        + "for _ in range(36):\n"
        + "    sys.stdout.write(chunk); sys.stdout.flush()\n"
        + "    sys.stderr.write(echunk); sys.stderr.flush()\n";
    let cmd1 = cmdEnv(cmdCwd(command("python3", ["-c", pyDual, "", "arg2"]), baseDir), [("GS_TEST_VAR", "override_val")]);
    let out1 = run(cmd1)?;
    let dualOk =
        out1.status == Exited(0)
        && strLen(out1.stderr) == 147456
        && hasSubstr(out1.stdout, "t36_work|0|arg2|override_val|")
        && strLen(out1.stdout) > 147456;

    // 3b. `ReplaceEnv` clean environment check
    let outClean = run(cmdEnvMode(
        command("python3", ["-c", "import os; print(os.environ.get('ONLY_KEY','') + ':' + str(len(os.environ)))"]),
        ReplaceEnv([("ONLY_KEY", "pure")])
    ))?;

    // 3c. Streaming `spawn` + `stdin` pipe write + `stdout` read + `childWait`
    let catChild = spawn(cmdStdio(command("cat", []), Piped, Piped, Null))?;
    let pipeOut = match (catChild.stdin, catChild.stdout) {
        (Some(pin), Some(pout)) -> {
            pipeWrite(pin, "hello-geisha-pipe")?;
            pipeClose(pin);
            pipeReadAll(pout)?
        },
        _ -> "missing_pipes",
    };
    let catSt = childWait(catChild)?;

    // 3d. `runTimeout` killing entire process group cleanly (`Ok(None)`)
    let toRes = runTimeout(command("sh", ["-c", "sleep 30"]), 80)?;
    let timeoutOk = match toRes {
        None -> true,
        Some(_) -> false,
    };

    // 3e. `childSignal` with `SigTerm`
    let sigChild = spawn(cmdOwnGroup(cmdStdio(command("sleep", ["30"]), Null, Null, Null), true))?;
    childSignal(sigChild, SigTerm)?;
    let sigSt = childWait(sigChild)?;
    let sigOk = sigSt == Signaled(15);

    // 4. `std.toml.patch`: comment-preserving in-place edit (Talus-style config)
    let origToml =
        "# User custom header comment\n"
        + "modifiers = [\"option\"]\n\n"
        + "[layout]\n"
        + "# Keep golden ratio\n"
        + "master_ratio = 0.6 # inline note\n"
        + "obsolete_key = 99\n\n"
        + "[deps]\n"
        + "# Core UI\n"
        + "crema = { git = \"github.com/geisha-lang/crema\", version = \"0.1.0\" }\n\n"
        + "[rules.app_workspaces]\n"
        + "\"com.tencent.xinWeChat\" = \"聊天\"\n\n"
        + "[[rules.float_windows]]\n"
        + "# WeChat viewer rule\n"
        + "app = \"com.tencent.xinWeChat\"\n"
        + "titles = [\"图片\"]\n";

    let targetVal = VObj([
        ("modifiers", VArr([VStr("option"), VStr("command")])),
        ("layout", VObj([
            ("master_ratio", VFloat(0.55)),
            ("outer_gap", VInt(intToI64(8))),
        ])),
        ("deps", VObj([
            ("crema", VObj([("git", VStr("github.com/geisha-lang/crema")), ("version", VStr("0.2.0"))])),
            ("objc", VObj([("git", VStr("github.com/geisha-lang/objc.gsa")), ("version", VStr("0.1.0"))])),
        ])),
        ("rules", VObj([
            ("app_workspaces", VObj([
                ("com.tencent.xinWeChat", VStr("聊天")),
            ])),
            ("float_windows", VArr([
                VObj([("app", VStr("com.tencent.xinWeChat")), ("titles", VArr([VStr("图片"), VStr("视频")]))]),
                VObj([("app", VStr("com.apple.Finder")), ("titles", VArr([VStr("简介")]))]),
            ])),
        ])),
        ("extra", VObj([("enabled", VBool(true))])),
    ]);

    let patchedToml = tomlPatch(origToml, targetVal)?;
    let reparsed = tomlParse(patchedToml)?;
    let commentsKept =
        hasSubstr(patchedToml, "# User custom header comment")
        && hasSubstr(patchedToml, "# Keep golden ratio")
        && hasSubstr(patchedToml, "master_ratio = 0.55 # inline note")
        && hasSubstr(patchedToml, "# Core UI")
        && hasSubstr(patchedToml, "# WeChat viewer rule")
        && !hasSubstr(patchedToml, "obsolete_key");
    // Re-patching an unchanged value should return the exact string untouched
    let idempToml = tomlPatch(patchedToml, reparsed)?;
    let patchOk = commentsKept && (idempToml == patchedToml);

    printLn(
        intToStr(hi16) + "|"
        + intToStr(octPerm) + "|"
        + intToStr(binBits) + "|"
        + intToStr(decSep) + "|"
        + (if (minI32 == -2147483647 - 1) "minOk" else "minBad") + "|"
        + intToStr(floatToInt(fltSep * 4.0)) + "|"
        + patRes + "|"
        + (if (secretText == "token = 2\n" && movedText == "token = 2\n" && mtime > intToI64(0)) "fsOk" else "fsBad") + "|"
        + (if (dualOk) "dualOk" else "dualBad") + "|"
        + (if (hasSubstr(outClean.stdout, "pure:")) "envOk" else "envBad") + "|"
        + pipeOut + ":" + (if (catSt == Exited(0)) "0" else "1") + "|"
        + (if (timeoutOk && sigOk) "sigToOk" else "sigToBad") + "|"
        + (if (patchOk) "tomlPatchOk" else "tomlPatchBad")
    );
    Ok(())
}
EOF
mkdir -p "$TMP_DIR/t36_work"
"$GEISHA_BIN" -o "$TMP_DIR/t36_sys_and_toml" "$TMP_DIR/t36_sys_and_toml.gsa"
T36_OUT="$("$TMP_DIR/t36_sys_and_toml" "$TMP_DIR/t36_work")"
assert_eq "literals_sysfs_sysproc_tomlpatch" "57005|384|165|1000000|minOk|4001|priv:exec:neg128|fsOk|dualOk|envOk|hello-geisha-pipe:0|sigToOk|tomlPatchOk" "$T36_OUT"

# Verify exact POSIX file modes on disk (0o600 preserved across writeFileAtomic + rename, and 0o755 via chmod)
MODES_OUT="$(python3 - "$TMP_DIR/t36_work/secret_moved.toml" "$TMP_DIR/t36_work/script.sh" << 'PY'
import os, sys
m1 = oct(os.stat(sys.argv[1]).st_mode & 0o777)
m2 = oct(os.stat(sys.argv[2]).st_mode & 0o777)
print(f"{m1}|{m2}")
PY
)"
assert_eq "sysfs_atomic_mode_and_chmod_bits" "0o600|0o755" "$MODES_OUT"

# Negative lex/parse checks for malformed radix & separator literals
for bad_lit in "0x" "0o78" "0b102" "123_" "0x1_0000_0000"; do
    cat > "$TMP_DIR/t36_bad_lit.gsa" << EOF
def main(): Int = $bad_lit
EOF
    if "$GEISHA_BIN" check "$TMP_DIR/t36_bad_lit.gsa" >/dev/null 2>&1; then
        echo "FAIL [bad_numeric_literal]: '$bad_lit' should be rejected" >&2
        exit 1
    fi
done

# Verify `geisha add` / `geisha remove` comment preservation & `geisha.local.toml` `[target.*]` overrides
LOCAL_OVR_PROJ="$TMP_DIR/t36_local_ovr"
mkdir -p "$LOCAL_OVR_PROJ/src" "$LOCAL_OVR_PROJ/native" "$TMP_DIR/t36_dep_lib/src"
cat > "$TMP_DIR/t36_dep_lib/geisha.toml" << 'EOF'
name = "t36_dep_lib"
version = "0.1.0"
EOF
cat > "$TMP_DIR/t36_dep_lib/src/t36_dep_lib.gsa" << 'EOF'
pub def bonus(): Int = 0x2A
EOF
cat > "$LOCAL_OVR_PROJ/native/val.c" << 'EOF'
#include <stdint.h>
#ifndef LOCAL_OVR_NUM
#define LOCAL_OVR_NUM 0
#endif
int32_t c_local_ovr_num(void) { return LOCAL_OVR_NUM; }
EOF
cat > "$LOCAL_OVR_PROJ/geisha.toml" << 'EOF'
# Top project comment preserved across geisha add/remove
name = "t36_local_ovr"
version = "0.1.0"

[target.native]
# Native C helper comment
c_sources = ["native/val.c"]
EOF
cat > "$LOCAL_OVR_PROJ/geisha.local.toml" << 'EOF'
[target.native]
c_flags = ["-DLOCAL_OVR_NUM=777"]
EOF
cat > "$LOCAL_OVR_PROJ/src/main.gsa" << 'EOF'
use std.str.intToStr
use t36_dep_lib.bonus

extern "c_local_ovr_num" def localNum(): Int

def main(): Void = printLn(intToStr(localNum() + bonus()))
EOF
ABS_GEISHA_36="$(cd "$(dirname "$GEISHA_BIN")" && pwd)/$(basename "$GEISHA_BIN")"
ABS_RT_36="$(cd "$(dirname "$GEISHA_RUNTIME")" && pwd)/$(basename "$GEISHA_RUNTIME")"
(cd "$LOCAL_OVR_PROJ" && "$ABS_GEISHA_36" add --path "$TMP_DIR/t36_dep_lib" --as t36_dep_lib >/dev/null)
if ! grep -q "# Top project comment preserved" "$LOCAL_OVR_PROJ/geisha.toml" || ! grep -q "# Native C helper comment" "$LOCAL_OVR_PROJ/geisha.toml"; then
    echo "FAIL [geisha_add_preserves_comments]: comments lost in geisha.toml after geisha add" >&2
    exit 1
fi
T36_PROJ_BIN="$(cd "$LOCAL_OVR_PROJ" && "$ABS_GEISHA_36" build --runtime "$ABS_RT_36" >/dev/null && ./build/t36_local_ovr)"
assert_eq "geisha_local_toml_target_override" "819" "$T36_PROJ_BIN"
(cd "$LOCAL_OVR_PROJ" && "$ABS_GEISHA_36" remove t36_dep_lib >/dev/null)
if ! grep -q "# Top project comment preserved" "$LOCAL_OVR_PROJ/geisha.toml" || grep -q "t36_dep_lib" "$LOCAL_OVR_PROJ/geisha.toml"; then
    echo "FAIL [geisha_remove_preserves_comments]: comments lost or dep remained after geisha remove" >&2
    exit 1
fi
echo "PASS [syslib_literals_toml_patch]: 0x/0o/0b/_ literals, sys.fs atomic writes, sys.proc poll/timeout/signals, std.toml.patch, & geisha.local.toml verified"
PASS=$((PASS + 1))

# 38. DWARF Debug Info (`-g` / `--debug`, `-O0`, LLVM 20 verifier, macOS dSYM / Linux ELF, LLDB + geisha_lldb.py)
cat > "$TMP_DIR/t37_dwarf.gsa" << 'EOF'
use std.option.{Option, Some, None}
use std.result.{Result, Ok, Err}
use std.str.intToStr
use std.vec.{Vec, vecNew, vecPush, vecLen}

data Pair {
    MkPair { px: Int, py: Int },
}

data Shape {
    Circle(Int),
    Rect(Int, Int),
}

def makeAdder(base: Int): Int -> Int = {
    let offset = base + 1;
    (x: Int) -> x + offset
}

def fact(n: Int): Int = {
    if (n <= 1) 1
    else {
        let sub = fact(n - 1);
        n * sub
    }
}

def shapeArea(sh: Shape): Int = match sh {
    Circle(r) -> r * r,
    Rect(w, h) -> {
        let area = w * h;
        area
    },
}

def inspectAll(
    p: Pair,
    s: String,
    sh: Shape,
    v: Vec Int,
    vp: Vec (Int, Int),
    optSome: Option Int,
    optNone: Option Int,
    xs: List Int,
    resOpt: Result Int (Option String)
): Int = {
    let f = makeAdder(10);
    let y = f(5);
    let n = vecLen(v) + vecLen(vp);
    let f4 = fact(4);
    let (da, db) = (11, 22);
    let a = shapeArea(Rect(3, 4));
    let _ = (optSome, optNone, xs, resOpt);
    p.px + p.py + y + n + f4 + da + db + a
}

def main(): Void = {
    let p = MkPair { px: 10, py: 20 };
    let msg = "hello geisha";
    let sh = Circle(7);
    let v = vecNew();
    vecPush(v, 100);
    vecPush(v, 200);
    vecPush(v, 300);
    let vp: Vec (Int, Int) = vecNew();
    vecPush(vp, (1, 2));
    vecPush(vp, (3, 4));
    let resOpt: Result Int (Option String) = Ok(42);
    let ans = inspectAll(p, msg, sh, v, vp, Some(42), None, [1, 2, 3], resOpt);
    printLn(msg + ":" + intToStr(ans))
}
EOF
"$GEISHA_BIN" -e -o "$TMP_DIR/t37_nodbg.ll" "$TMP_DIR/t37_dwarf.gsa"
if grep -q "!DICompileUnit" "$TMP_DIR/t37_nodbg.ll"; then
    echo "FAIL [dwarf_opt_in]: unexpected DWARF metadata emitted without -g" >&2
    exit 1
fi
"$GEISHA_BIN" -g -e -o "$TMP_DIR/t37_dbg.ll" "$TMP_DIR/t37_dwarf.gsa"
for tok in "!DICompileUnit" "!DISubprogram" "!DILocation" "@llvm.dbg.declare" "!DILocalVariable"; do
    if ! grep -q "$tok" "$TMP_DIR/t37_dbg.ll"; then
        echo "FAIL [dwarf_ir_metadata]: missing $tok in -g IR" >&2
        exit 1
    fi
done
OPT_BIN=""
for cand in /opt/homebrew/opt/llvm@20/bin/opt /opt/homebrew/opt/llvm/bin/opt /usr/lib/llvm-20/bin/opt opt-20 opt; do
    if command -v "$cand" >/dev/null 2>&1; then
        OPT_BIN="$cand"
        break
    fi
done
if [ -n "$OPT_BIN" ]; then
    "$OPT_BIN" -passes=verify -disable-output "$TMP_DIR/t37_dbg.ll"
fi
"$GEISHA_BIN" -g --runtime "$GEISHA_RUNTIME" -o "$TMP_DIR/t37_dwarf" "$TMP_DIR/t37_dwarf.gsa"
assert_eq "dwarf_debug_run" "hello geisha:120" "$("$TMP_DIR/t37_dwarf")"
if [ "$UNAME_S" = "Darwin" ] && [ ! -d "$TMP_DIR/t37_dwarf.dSYM" ]; then
    echo "FAIL [dwarf_macos_dsym]: expected $TMP_DIR/t37_dwarf.dSYM to be generated" >&2
    exit 1
fi
"$GEISHA_BIN" -g -O2 --runtime "$GEISHA_RUNTIME" -o "$TMP_DIR/t37_dwarf_o2" "$TMP_DIR/t37_dwarf.gsa"
assert_eq "dwarf_debug_o2_run" "hello geisha:120" "$("$TMP_DIR/t37_dwarf_o2")"
assert_eq "dwarf_geisha_run_g" "hello geisha:120" "$("$GEISHA_BIN" run -g --runtime "$GEISHA_RUNTIME" "$TMP_DIR/t37_dwarf.gsa")"
if command -v lldb >/dev/null 2>&1; then
    LLDB_SCRIPT_PATH="$(pwd)/tools/geisha_lldb.py"
    LLDB_OUT="$(lldb -b \
        -o "command script import $LLDB_SCRIPT_PATH" \
        -o "b t37_dwarf.gsa:17" \
        -o "b t37_dwarf.gsa:24" \
        -o "b t37_dwarf.gsa:32" \
        -o "b t37_dwarf.gsa:54" \
        -o "run" \
        -o "frame variable" \
        -o "c" \
        -o "frame variable" \
        -o "c" \
        -o "bt" \
        -o "frame variable" \
        -o "c" \
        -o "c" \
        -o "c" \
        -o "frame variable" \
        -o "c" \
        -o "frame variable" \
        "$TMP_DIR/t37_dwarf" 2>&1 || true)"
    for needle in \
        "t37_dwarf.gsa:24" \
        "t37_dwarf.gsa:32" \
        "t37_dwarf.gsa:54" \
        "(int) offset = 11" \
        "(int) x = 5" \
        "(int) w = 3" \
        "(int) h = 4" \
        "(int) da = 11" \
        "(int) db = 22" \
        "px = 10, py = 20" \
        "\"hello geisha\"" \
        "Vec(len=3) [100, 200, 300]" \
        "Vec(len=2) [(1, 2), (3, 4)]" \
        "Shape(tag=0, payload=7)" \
        "optSome = 0x" \
        "Some(42)" \
        "optNone = 0x" \
        "None" \
        "[1, 2, 3]" \
        "tag=0, payload=42"; do
        if ! printf "%s" "$LLDB_OUT" | grep -Fq "$needle"; then
            echo "FAIL [dwarf_lldb_e2e]: missing '$needle' in LLDB output:" >&2
            printf "%s\n" "$LLDB_OUT" >&2
            exit 1
        fi
    done
    if printf "%s" "$LLDB_OUT" | grep -Fq "resOpt = 0x" && printf "%s" "$LLDB_OUT" | grep "resOpt = " | grep -Fq "None"; then
        echo "FAIL [dwarf_lldb_e2e]: Result Int (Option String) misidentified as None!" >&2
        printf "%s\n" "$LLDB_OUT" >&2
        exit 1
    fi
    echo "PASS [dwarf_lldb_e2e]: LLDB breakpoints, recursive bt, closure captures, match PatVar bindings, Vec(Int,Int), Option/List/Result/Shape formatters verified"
    PASS=$((PASS + 1))
else
    echo "PASS [dwarf_ir_and_build]: DWARF IR metadata and debug build verified (lldb not installed)"
    PASS=$((PASS + 1))
fi

# 38b. Verify single-file vs project-mode (`geisha build -g --target wasm32`) DWARF section parity
WASM_DBG_PROJ="$TMP_DIR/t38_wasm_dbg"
mkdir -p "$WASM_DBG_PROJ/src"
cat > "$WASM_DBG_PROJ/geisha.toml" << 'EOF'
name = "t38_wasm_dbg"
version = "0.1.0"
EOF
cat > "$WASM_DBG_PROJ/src/main.gsa" << 'EOF'
pub def addOne(x: Int): Int = x + 1
def main(): Void = { let _ = addOne(41); () }
EOF
ABS_GEISHA_38="$(cd "$(dirname "$GEISHA_BIN")" && pwd)/$(basename "$GEISHA_BIN")"
"$ABS_GEISHA_38" -g -c --target wasm32 -o "$TMP_DIR/t38_single.o" "$WASM_DBG_PROJ/src/main.gsa"
(cd "$WASM_DBG_PROJ" && "$ABS_GEISHA_38" build -g -c --target wasm32 -o "$TMP_DIR/t38_proj.o")
for wobj in "$TMP_DIR/t38_single.o" "$TMP_DIR/t38_proj.o"; do
    if ! grep -aq "debug_info" "$wobj" || ! grep -aq "debug_line" "$wobj"; then
        echo "FAIL [dwarf_wasm_parity]: missing .debug_info/.debug_line in $wobj" >&2
        exit 1
    fi
done
echo "PASS [dwarf_wasm_parity]: single-file and project-mode geisha build -g --target wasm32 both emit .debug_info/.debug_line"
PASS=$((PASS + 1))

# 37. Incremental Multi-CGU Build, Content-Addressed `.o` Cache Hit/Invalidation, `c_sources` Cache & `--opt`/`--dev`/`--release`/`--single-cgu`
INC_PROJ="$TMP_DIR/t37_inc_cgu"
mkdir -p "$INC_PROJ/src" "$INC_PROJ/native" "$INC_PROJ/vendor"
cat > "$INC_PROJ/geisha.toml" << 'EOF'
name = "t37_inc_cgu"
version = "0.1.0"

[target.native]
c_sources = ["native/helper.c"]
c_flags = ["-isystem", "vendor"]
EOF
cat > "$INC_PROJ/vendor/sysval.h" << 'EOF'
#define VENDOR_SYS_BONUS 0
EOF
cat > "$INC_PROJ/native/cost\$us.def" << 'EOF'
0
EOF
cat > "$INC_PROJ/native/num.def" << 'EOF'
100
EOF
cat > "$INC_PROJ/native/helper.c" << 'EOF'
#include <stdint.h>
#include <sysval.h>
int32_t c_inc_bonus(void) {
    int32_t a =
#include "num.def"
    ;
    int32_t b =
#include "cost$us.def"
    ;
    return a + b + VENDOR_SYS_BONUS;
}
EOF
cat > "$INC_PROJ/src/types.gsa" << 'EOF'
pub data Pair {
    MkPair { a: Int, b: Int },
}
pub def pairSum(p: Pair): Int = p.a + p.b
pub def pairDiff(p: Pair): Int = p.a - p.b
pub def pairProd(p: Pair): Int = p.a * p.b
pub def pairScale(p: Pair, k: Int): Pair = MkPair { a: p.a * k, b: p.b * k }
pub def pairSwap(p: Pair): Pair = MkPair { a: p.b, b: p.a }
EOF
cat > "$INC_PROJ/src/mod_a.gsa" << 'EOF'
use types.{Pair, MkPair, pairSum, pairScale}
pub def a1(x: Int): Int = x + 1
pub def a2(x: Int): Int = a1(x) + 2
pub def a3(x: Int): Int = a2(x) + 3
pub def a4(x: Int): Int = a3(x) + 4
pub def a5(p: Pair): Int = pairSum(pairScale(p, 2)) + a4(0)
EOF
cat > "$INC_PROJ/src/mod_b.gsa" << 'EOF'
use types.{Pair, MkPair, pairSum, pairDiff, pairProd, pairSwap}
pub def b1(x: Int): Int = x + 10
pub def b2(x: Int): Int = b1(x) + 20
pub def b3(x: Int): Int = b2(x) + 30
pub def b4(x: Int): Int = b3(x) + 40
pub def b5(p: Pair): Int = pairSum(pairSwap(p)) + pairDiff(p) + pairProd(p) + b4(0)
EOF
cat > "$INC_PROJ/src/main.gsa" << 'EOF'
use std.str.intToStr
use types.{Pair, MkPair}
use mod_a.a5
use mod_b.b5

extern "c_inc_bonus" def cBonus(): Int

pub def m1(x: Int): Int = x + 1
pub def m2(x: Int): Int = m1(x) + 1
pub def m3(x: Int): Int = m2(x) + 1

def main(): Void = {
    let p = MkPair { a: 5, b: 3 };
    printLn(intToStr(a5(p) + b5(p) + cBonus() + m3(0)))
}
EOF
ABS_GEISHA_37="$(cd "$(dirname "$GEISHA_BIN")" && pwd)/$(basename "$GEISHA_BIN")"
ABS_RT_37="$(cd "$(dirname "$GEISHA_RUNTIME")" && pwd)/$(basename "$GEISHA_RUNTIME")"

# 37a. Cold --dev (-O0) multi-CGU build
T37_COLD_LOG="$(cd "$INC_PROJ" && GEISHA_CACHE_STATS=1 "$ABS_GEISHA_37" build --dev --runtime "$ABS_RT_37" 2>&1)"
assert_eq "inc_cgu_cold_dev_output" "254" "$("$INC_PROJ/build/t37_inc_cgu")"
if ! echo "$T37_COLD_LOG" | grep -q "cgu_hit=0 " || ! echo "$T37_COLD_LOG" | grep -q "native_miss=1 " || ! echo "$T37_COLD_LOG" | grep -q "opt=-O0"; then
    echo "FAIL [inc_cgu_cold_stats]: unexpected stats: $T37_COLD_LOG" >&2
    exit 1
fi

# 37b. Warm unchanged repeat build -> whole-project cache hit
T37_WARM_LOG="$(cd "$INC_PROJ" && GEISHA_CACHE_STATS=1 "$ABS_GEISHA_37" build --dev --runtime "$ABS_RT_37" 2>&1)"
if ! echo "$T37_WARM_LOG" | grep -q "project_hit=1"; then
    echo "FAIL [inc_cgu_project_hit]: expected project_hit=1, got: $T37_WARM_LOG" >&2
    exit 1
fi

# 37c. Edit single module body (mod_a.gsa) -> only 1 CGU misses, all others + native C .o hit cache
cat > "$INC_PROJ/src/mod_a.gsa" << 'EOF'
use types.{Pair, MkPair, pairSum, pairScale}
pub def a1(x: Int): Int = x + 11
pub def a2(x: Int): Int = a1(x) + 2
pub def a3(x: Int): Int = a2(x) + 3
pub def a4(x: Int): Int = a3(x) + 4
pub def a5(p: Pair): Int = pairSum(pairScale(p, 2)) + a4(0)
EOF
T37_MODA_LOG="$(cd "$INC_PROJ" && GEISHA_CACHE_STATS=1 "$ABS_GEISHA_37" build --dev --runtime "$ABS_RT_37" 2>&1)"
assert_eq "inc_cgu_edit_mod_a_output" "264" "$("$INC_PROJ/build/t37_inc_cgu")"
if ! echo "$T37_MODA_LOG" | grep -q "cgu_miss=1 " || ! echo "$T37_MODA_LOG" | grep -q "native_hit=1 " || ! echo "$T37_MODA_LOG" | grep -q "native_miss=0 "; then
    echo "FAIL [inc_cgu_edit_mod_a_stats]: expected cgu_miss=1 & native_hit=1, got: $T37_MODA_LOG" >&2
    exit 1
fi

# 37d. Edit non-.h C `#include "num.def"`, `-isystem vendor/sysval.h`, & `cost$us.def` (`$$` in `.d`), plus no-.d wrapper fallback
cat > "$INC_PROJ/native/num.def" << 'EOF'
200
EOF
T37_C_LOG="$(cd "$INC_PROJ" && GEISHA_CACHE_STATS=1 "$ABS_GEISHA_37" build --dev --runtime "$ABS_RT_37" 2>&1)"
assert_eq "inc_cgu_edit_c_def_include_output" "364" "$("$INC_PROJ/build/t37_inc_cgu")"
if ! echo "$T37_C_LOG" | grep -q "cgu_miss=0 " || ! echo "$T37_C_LOG" | grep -q "native_miss=1 "; then
    echo "FAIL [inc_cgu_edit_c_def_stats]: expected cgu_miss=0 & native_miss=1 on num.def edit, got: $T37_C_LOG" >&2
    exit 1
fi
cat > "$INC_PROJ/vendor/sysval.h" << 'EOF'
#define VENDOR_SYS_BONUS 5
EOF
T37_ISYS_LOG="$(cd "$INC_PROJ" && GEISHA_CACHE_STATS=1 "$ABS_GEISHA_37" build --dev --runtime "$ABS_RT_37" 2>&1)"
assert_eq "inc_cgu_edit_isystem_header_output" "369" "$("$INC_PROJ/build/t37_inc_cgu")"
if echo "$T37_ISYS_LOG" | grep -q "project_hit=1" || ! echo "$T37_ISYS_LOG" | grep -q "cgu_miss=0 " || ! echo "$T37_ISYS_LOG" | grep -q "native_miss=1 "; then
    echo "FAIL [inc_cgu_edit_isystem_stats]: expected -isystem edit to invalidate native & project cache, got: $T37_ISYS_LOG" >&2
    exit 1
fi
cat > "$INC_PROJ/native/cost\$us.def" << 'EOF'
7
EOF
T37_DOLLAR_LOG="$(cd "$INC_PROJ" && GEISHA_CACHE_STATS=1 "$ABS_GEISHA_37" build --dev --runtime "$ABS_RT_37" 2>&1)"
assert_eq "inc_cgu_edit_dollar_def_output" "376" "$("$INC_PROJ/build/t37_inc_cgu")"
if echo "$T37_DOLLAR_LOG" | grep -q "project_hit=1" || ! echo "$T37_DOLLAR_LOG" | grep -q "cgu_miss=0 " || ! echo "$T37_DOLLAR_LOG" | grep -q "native_miss=1 "; then
    echo "FAIL [inc_cgu_edit_dollar_def_stats]: expected cost\$us.def edit to invalidate native & project cache, got: $T37_DOLLAR_LOG" >&2
    exit 1
fi
# Wrapper named `clang` that strips `-MD -MF <file>` (produces no `.d`) must never publish C .o or project cache
mkdir -p "$INC_PROJ/fakebin"
cat > "$INC_PROJ/fakebin/clang" << EOF
#!/bin/sh
out=""
skip=0
set -- "\$@"
filtered=""
for a in "\$@"; do
    if [ "\$skip" = "1" ]; then skip=0; continue; fi
    if [ "\$a" = "-MD" ] || [ "\$a" = "-MMD" ]; then continue; fi
    if [ "\$a" = "-MF" ]; then skip=1; continue; fi
    exec_args="\$exec_args \$(printf '%s' "\$a" | sed "s/'/'\\\\''/g; s/^/'/; s/\$/'/")"
done
eval "exec $CC \$exec_args"
EOF
chmod +x "$INC_PROJ/fakebin/clang"
(cd "$INC_PROJ" && CC="$INC_PROJ/fakebin/clang" "$ABS_GEISHA_37" build --dev --runtime "$ABS_RT_37" >/dev/null)
assert_eq "inc_cgu_nod_wrapper_build1" "376" "$("$INC_PROJ/build/t37_inc_cgu")"
cat > "$INC_PROJ/native/num.def" << 'EOF'
201
EOF
T37_NOD_LOG="$(cd "$INC_PROJ" && CC="$INC_PROJ/fakebin/clang" GEISHA_CACHE_STATS=1 "$ABS_GEISHA_37" build --dev --runtime "$ABS_RT_37" 2>&1)"
assert_eq "inc_cgu_nod_wrapper_build2" "377" "$("$INC_PROJ/build/t37_inc_cgu")"
if echo "$T37_NOD_LOG" | grep -q "project_hit=1" || ! echo "$T37_NOD_LOG" | grep -q "native_hit=0 "; then
    echo "FAIL [inc_cgu_nod_wrapper_cache]: no-.d wrapper must skip C .o & project cache, got: $T37_NOD_LOG" >&2
    exit 1
fi
# Reset vendor/dollar/num back so subsequent 37e arithmetic stays exact (200 + 0 + 0)
cat > "$INC_PROJ/vendor/sysval.h" << 'EOF'
#define VENDOR_SYS_BONUS 0
EOF
cat > "$INC_PROJ/native/cost\$us.def" << 'EOF'
0
EOF
cat > "$INC_PROJ/native/num.def" << 'EOF'
200
EOF

# 37e. Edit shared ADT layout in types.gsa -> dependent CGUs cleanly invalidate & recompile
cat > "$INC_PROJ/src/types.gsa" << 'EOF'
pub data Pair {
    MkPair { a: Int, b: Int, c: Int },
}
pub def pairSum(p: Pair): Int = p.a + p.b + p.c
pub def pairDiff(p: Pair): Int = p.a - p.b
pub def pairProd(p: Pair): Int = p.a * p.b
pub def pairScale(p: Pair, k: Int): Pair = MkPair { a: p.a * k, b: p.b * k, c: p.c * k }
pub def pairSwap(p: Pair): Pair = MkPair { a: p.b, b: p.a, c: p.c }
EOF
cat > "$INC_PROJ/src/main.gsa" << 'EOF'
use std.str.intToStr
use types.{Pair, MkPair}
use mod_a.a5
use mod_b.b5

extern "c_inc_bonus" def cBonus(): Int

pub def m1(x: Int): Int = x + 1
pub def m2(x: Int): Int = m1(x) + 1
pub def m3(x: Int): Int = m2(x) + 1

def main(): Void = {
    let p = MkPair { a: 5, b: 3, c: 10 };
    printLn(intToStr(a5(p) + b5(p) + cBonus() + m3(0)))
}
EOF
T37_TYPE_LOG="$(cd "$INC_PROJ" && GEISHA_CACHE_STATS=1 "$ABS_GEISHA_37" build --dev --runtime "$ABS_RT_37" 2>&1)"
assert_eq "inc_cgu_edit_type_layout_output" "394" "$("$INC_PROJ/build/t37_inc_cgu")"
if echo "$T37_TYPE_LOG" | grep -q "cgu_miss=0 "; then
    echo "FAIL [inc_cgu_edit_type_invalidation]: expected CGU invalidation on ADT layout change, got: $T37_TYPE_LOG" >&2
    exit 1
fi

# 37f. --release (-O2), --dev -> --release -> --dev round-trip (must NOT false-hit stale O2 bin), --opt=1/3, --single-cgu, --opt=9/unknown-flag rejection, `geisha run --dev script.gsa`, and `geisha check`
T37_REL_LOG="$(cd "$INC_PROJ" && GEISHA_CACHE_STATS=1 "$ABS_GEISHA_37" build --release --runtime "$ABS_RT_37" 2>&1)"
assert_eq "inc_cgu_release_output" "394" "$("$INC_PROJ/build/t37_inc_cgu")"
if ! echo "$T37_REL_LOG" | grep -q "opt=-O2"; then
    echo "FAIL [inc_cgu_release_opt]: expected opt=-O2, got: $T37_REL_LOG" >&2
    exit 1
fi
T37_RT_DEV_LOG="$(cd "$INC_PROJ" && GEISHA_CACHE_STATS=1 "$ABS_GEISHA_37" build --dev --runtime "$ABS_RT_37" 2>&1)"
assert_eq "inc_cgu_roundtrip_dev_output" "394" "$("$INC_PROJ/build/t37_inc_cgu")"
if echo "$T37_RT_DEV_LOG" | grep -q "project_hit=1"; then
    echo "FAIL [inc_cgu_roundtrip_dev_false_hit]: --dev after --release must not false-hit stale O2 binary, got: $T37_RT_DEV_LOG" >&2
    exit 1
fi
if ! echo "$T37_RT_DEV_LOG" | grep -q "cgu_miss=0 " || ! echo "$T37_RT_DEV_LOG" | grep -q "opt=-O0"; then
    echo "FAIL [inc_cgu_roundtrip_dev_relink]: expected cached -O0 CGU relink (cgu_miss=0 opt=-O0), got: $T37_RT_DEV_LOG" >&2
    exit 1
fi
T37_RT_DEV2_LOG="$(cd "$INC_PROJ" && GEISHA_CACHE_STATS=1 "$ABS_GEISHA_37" build --dev --runtime "$ABS_RT_37" 2>&1)"
if ! echo "$T37_RT_DEV2_LOG" | grep -q "project_hit=1"; then
    echo "FAIL [inc_cgu_roundtrip_dev_warm]: expected project_hit=1 on consecutive --dev, got: $T37_RT_DEV2_LOG" >&2
    exit 1
fi
T37_OPT3_LOG="$(cd "$INC_PROJ" && GEISHA_CACHE_STATS=1 "$ABS_GEISHA_37" build --opt=3 --runtime "$ABS_RT_37" 2>&1)"
assert_eq "inc_cgu_opt3_output" "394" "$("$INC_PROJ/build/t37_inc_cgu")"
if ! echo "$T37_OPT3_LOG" | grep -q "opt=-O3"; then
    echo "FAIL [inc_cgu_opt3_stats]: expected opt=-O3, got: $T37_OPT3_LOG" >&2
    exit 1
fi
T37_OPTS_LOG="$(cd "$INC_PROJ" && GEISHA_CACHE_STATS=1 "$ABS_GEISHA_37" build -Os --runtime "$ABS_RT_37" 2>&1)"
assert_eq "inc_cgu_opts_output" "394" "$("$INC_PROJ/build/t37_inc_cgu")"
if ! echo "$T37_OPTS_LOG" | grep -q "opt=-Os"; then
    echo "FAIL [inc_cgu_opts_stats]: expected opt=-Os, got: $T37_OPTS_LOG" >&2
    exit 1
fi
T37_DBG_LOG="$(cd "$INC_PROJ" && GEISHA_CACHE_STATS=1 "$ABS_GEISHA_37" build --dev -g --runtime "$ABS_RT_37" 2>&1)"
assert_eq "inc_cgu_debug_flag_output" "394" "$("$INC_PROJ/build/t37_inc_cgu")"
if echo "$T37_DBG_LOG" | grep -q "project_hit=1" || ! echo "$T37_DBG_LOG" | grep -q "cgu_hit=0 "; then
    echo "FAIL [inc_cgu_debug_cache_sep]: -g must separate CGU/project cache keys from non-debug builds, got: $T37_DBG_LOG" >&2
    exit 1
fi
if [ "$(uname -s)" = "Darwin" ]; then
    T37_DSYM_DWARF="$INC_PROJ/build/t37_inc_cgu.dSYM/Contents/Resources/DWARF/t37_inc_cgu"
    if [ ! -f "$T37_DSYM_DWARF" ]; then
        echo "FAIL [inc_cgu_dsym_created]: expected $T37_DSYM_DWARF after build --dev -g" >&2
        exit 1
    fi
    rm -f "$T37_DSYM_DWARF"
    T37_DSYM_REBUILD="$(cd "$INC_PROJ" && GEISHA_CACHE_STATS=1 "$ABS_GEISHA_37" build --dev -g --runtime "$ABS_RT_37" 2>&1)"
    if echo "$T37_DSYM_REBUILD" | grep -q "project_hit=1" || ! echo "$T37_DSYM_REBUILD" | grep -q "cgu_miss=0 "; then
        echo "FAIL [inc_cgu_dsym_restore]: deleting .dSYM DWARF must bypass project_hit and relink with cgu_miss=0, got: $T37_DSYM_REBUILD" >&2
        exit 1
    fi
    if [ ! -f "$T37_DSYM_DWARF" ]; then
        echo "FAIL [inc_cgu_dsym_restored_file]: expected $T37_DSYM_DWARF to be restored" >&2
        exit 1
    fi
    T37_DSYM_WARM="$(cd "$INC_PROJ" && GEISHA_CACHE_STATS=1 "$ABS_GEISHA_37" build --dev -g --runtime "$ABS_RT_37" 2>&1)"
    if ! echo "$T37_DSYM_WARM" | grep -q "project_hit=1"; then
        echo "FAIL [inc_cgu_dsym_warm]: expected project_hit=1 once .dSYM is present, got: $T37_DSYM_WARM" >&2
        exit 1
    fi
fi
if (cd "$INC_PROJ" && "$ABS_GEISHA_37" build --opt=9 --runtime "$ABS_RT_37" >/dev/null 2>&1); then
    echo "FAIL [inc_cgu_bad_opt9]: --opt=9 should be rejected" >&2
    exit 1
fi
if (cd "$INC_PROJ" && "$ABS_GEISHA_37" build --bogus-flag --runtime "$ABS_RT_37" >/dev/null 2>&1); then
    echo "FAIL [inc_cgu_unknown_flag]: unknown --bogus-flag on build should be rejected" >&2
    exit 1
fi
cat > "$TMP_DIR/t37_script.gsa" << 'EOF'
def main(): Void = printLn("script-dev-ok")
EOF
T37_SCR_COLD="$(GEISHA_CACHE_STATS=1 "$ABS_GEISHA_37" run --dev --no-cache --runtime "$ABS_RT_37" "$TMP_DIR/t37_script.gsa" 2>&1)"
if ! echo "$T37_SCR_COLD" | grep -q "script-dev-ok" || ! echo "$T37_SCR_COLD" | grep -q "script_hit=0 opt=-O0"; then
    echo "FAIL [inc_cgu_run_dev_nocache]: expected script-dev-ok & script_hit=0 opt=-O0, got: $T37_SCR_COLD" >&2
    exit 1
fi
T37_SCR_WARM="$(GEISHA_CACHE_STATS=1 "$ABS_GEISHA_37" run --dev --runtime "$ABS_RT_37" "$TMP_DIR/t37_script.gsa" 2>&1)"
if ! echo "$T37_SCR_WARM" | grep -q "script-dev-ok" || ! echo "$T37_SCR_WARM" | grep -q "script_hit=1 opt=-O0"; then
    echo "FAIL [inc_cgu_run_dev_warm]: expected script-dev-ok & script_hit=1 opt=-O0, got: $T37_SCR_WARM" >&2
    exit 1
fi
T37_SCGU_LOG="$(cd "$INC_PROJ" && GEISHA_CACHE_STATS=1 "$ABS_GEISHA_37" build --single-cgu --no-cache --runtime "$ABS_RT_37" 2>&1)"
assert_eq "inc_cgu_single_cgu_output" "394" "$("$INC_PROJ/build/t37_inc_cgu")"
if ! echo "$T37_SCGU_LOG" | grep -q "cgu_total=1 "; then
    echo "FAIL [inc_cgu_single_cgu_stats]: expected cgu_total=1, got: $T37_SCGU_LOG" >&2
    exit 1
fi
(cd "$INC_PROJ" && "$ABS_GEISHA_37" check >/dev/null)
echo "PASS [incremental_cgu_cache_and_opt]: multi-CGU parallel cache, single-module & C & ADT invalidation, --dev/--release round-trip, --opt=0..3/9, run --dev, & --single-cgu verified"
PASS=$((PASS + 1))

# --- Test 37: `geisha bench` microbenchmarking framework & `std.bench` ---
ABS_GEISHA_37="$(cd "$(dirname "$GEISHA_BIN")" && pwd)/$(basename "$GEISHA_BIN")"
ABS_RT_37="$(cd "$(dirname "$GEISHA_RUNTIME")" && pwd)/$(basename "$GEISHA_RUNTIME")"

# 37a: `geisha doc std.bench` exposes polymorphic blackBox, measure, bench, BenchStats
DOC_BENCH="$("$GEISHA_BIN" doc std.bench)"
for sym in "def blackBox(" "def blackBoxBarrier(" "def measure(" "def bench(" "data BenchStats" "def formatStatsJsonInFile("; do
    if ! printf '%s\n' "$DOC_BENCH" | grep -q "$sym"; then
        echo "FAIL [bench_doc]: missing '$sym' in 'geisha doc std.bench'" >&2
        exit 1
    fi
done

# 37b: Verify polymorphic `__blackBox` emits `@gs_bench_black_box_mem` / `@gs_bench_black_box_void`
#      and works on primitives, Tuples, Option, and custom user `data` structs without Orphan Rule issues
cat > "$TMP_DIR/t37_blackbox.gsa" << 'EOF'
use std.bench.{blackBox, blackBoxBarrier}
use std.option.{Option, Some, None}
use std.str.{intToStr, i64ToStr, boolToStr}

data PairBox {
    x: Int,
    y: Float,
}

def pureWork(n: Int): Int = {
    let acc = cellNew(0);
    let i = cellNew(1);
    while (cellGet(i) <= n) {
        cellSet(acc, cellGet(acc) + cellGet(i));
        cellSet(i, cellGet(i) + 1)
    };
    cellGet(acc)
}

def main(): Void = {
    let a = blackBox(pureWork(100));
    let b = blackBox(intToI64(42));
    let c = blackBox(3.5);
    let d = blackBox(true);
    let s = blackBox("ok");
    let o = match blackBox(Some(7)) { Some(v) -> v, None -> 0 };
    let (t1, t2) = blackBox((11, 2.5));
    let pb = blackBox(PairBox { x: 9, y: 1.5 });
    blackBoxBarrier();
    printLn(
        intToStr(a) + "|" + i64ToStr(b) + "|" + intToStr(floatToInt(c * 2.0))
        + "|" + boolToStr(d) + "|" + s + "|" + intToStr(o)
        + "|" + intToStr(t1 + floatToInt(t2 * 2.0))
        + "|" + intToStr(pb.x + floatToInt(pb.y * 2.0))
    )
}
EOF
"$GEISHA_BIN" -e -o "$TMP_DIR/t37_blackbox.ll" "$TMP_DIR/t37_blackbox.gsa"
if ! grep -q "@gs_bench_black_box_mem" "$TMP_DIR/t37_blackbox.ll" || ! grep -q "@gs_bench_black_box_void" "$TMP_DIR/t37_blackbox.ll"; then
    echo "FAIL [bench_blackbox_ir]: expected @gs_bench_black_box_mem and @gs_bench_black_box_void in LLVM IR" >&2
    exit 1
fi
"$GEISHA_BIN" -o "$TMP_DIR/t37_blackbox" "$TMP_DIR/t37_blackbox.gsa"
T37_BB_OUT="$("$TMP_DIR/t37_blackbox")"
assert_eq "bench_blackbox_values" "5050|42|7|true|ok|7|16|12" "$T37_BB_OUT"

# 37b-wasm: Verify `std.bench.blackBox` compiles & links for `--target wasm32` with ZERO wasm-ld signature warnings
cat > "$TMP_DIR/t37_blackbox_wasm.gsa" << 'EOF'
use std.bench.{blackBox, blackBoxBarrier}

pub def run_wasm_bb(n: Int): Int = {
    let s = blackBox("hello");
    let p = blackBox((n, strLen(s)));
    blackBoxBarrier();
    let (a, b) = p;
    a + b
}

def main(): Void = { let _ = run_wasm_bb(10); () }
EOF
WASM_BB_ERR="$("$GEISHA_BIN" --target wasm32 --export run_wasm_bb -o "$TMP_DIR/t37_blackbox_wasm.wasm" "$TMP_DIR/t37_blackbox_wasm.gsa" 2>&1)"
if printf '%s\n' "$WASM_BB_ERR" | grep -qi "signature_mismatch\|warning"; then
    echo "FAIL [bench_wasm32_clean_link]: unexpected wasm-ld warning:" >&2
    echo "$WASM_BB_ERR" >&2
    exit 1
fi
if [ ! -s "$TMP_DIR/t37_blackbox_wasm.wasm" ]; then
    echo "FAIL [bench_wasm32_clean_link]: wasm output missing or empty" >&2
    exit 1
fi

# 37c: Standalone single-file mode with `bench_*` functions (no `main`)
cat > "$TMP_DIR/t37_standalone_fns.gsa" << 'EOF'
use std.bench.blackBox

def sumTo(n: Int): Int = {
    let acc = cellNew(0);
    let i = cellNew(1);
    while (cellGet(i) <= n) {
        cellSet(acc, cellGet(acc) + cellGet(i));
        cellSet(i, cellGet(i) + 1)
    };
    cellGet(acc)
}

def fib(n: Int): Int = if (n <= 1) n else fib(n - 1) + fib(n - 2)

def bench_sum_1000(): Void = {
    let _ = blackBox(sumTo(blackBox(1000)));
    ()
}

def bench_fib_14(): Int = blackBox(fib(blackBox(14)))
EOF
T37_TEXT="$("$GEISHA_BIN" bench "$TMP_DIR/t37_standalone_fns.gsa" --iters 30 --warmup 2 --rounds 5 --runtime "$GEISHA_RUNTIME")"
for tok in "bench_sum_1000" "bench_fib_14" "mean:" "median:" "min:" "max:" "ops/s" "30 iters x 5 rounds"; do
    if ! printf '%s\n' "$T37_TEXT" | grep -q "$tok"; then
        echo "FAIL [bench_standalone_text]: missing '$tok' in output:" >&2
        echo "$T37_TEXT" >&2
        exit 1
    fi
done

T37_JSON="$("$GEISHA_BIN" bench "$TMP_DIR/t37_standalone_fns.gsa" --iters 30 --warmup 2 --rounds 5 --json --runtime "$GEISHA_RUNTIME")"
python3 - "$T37_JSON" << 'PY'
import json, sys
data = json.loads(sys.argv[1])
assert data["ok"] is True, data
bs = data["benchmarks"]
assert len(bs) == 2, bs
assert [b["name"] for b in bs] == ["bench_sum_1000", "bench_fib_14"], bs
for b in bs:
    assert b["iters"] == 30, b
    assert b["rounds"] == 5, b
    assert b["total_ns"] > 0, b
    assert b["min_ns"] <= b["median_ns"] <= b["max_ns"], b
    assert b["mean_ns"] > 0, b
    assert b["ops_per_sec"] > 0, b
    assert b["file"].endswith("t37_standalone_fns.gsa"), b
PY

T37_FILT_JSON="$("$GEISHA_BIN" bench "$TMP_DIR/t37_standalone_fns.gsa" fib --iters 15 --warmup 1 --rounds 3 --json --runtime "$GEISHA_RUNTIME")"
python3 - "$T37_FILT_JSON" << 'PY'
import json, sys
data = json.loads(sys.argv[1])
assert data["ok"] is True
bs = data["benchmarks"]
assert len(bs) == 1 and bs[0]["name"] == "bench_fib_14", bs
assert bs[0]["iters"] == 15 and bs[0]["rounds"] == 3, bs
PY

# 37d: Standalone script with explicit `main()` calling `std.bench.{bench, benchGroup}`
cat > "$TMP_DIR/t37_standalone_main.gsa" << 'EOF'
use std.bench.{bench, benchGroup, blackBox}

def work(n: Int): Int = {
    let s = cellNew(0);
    let i = cellNew(0);
    while (cellGet(i) < n) {
        cellSet(s, cellGet(s) + cellGet(i));
        cellSet(i, cellGet(i) + 1)
    };
    cellGet(s)
}

def main(): Void = {
    let _ = bench("custom_loop", () -> { let _ = blackBox(work(blackBox(500))); () });
    let _ = benchGroup("grp", [
        ("a", () -> { let _ = blackBox(work(blackBox(200))); () }),
        ("b", () -> { let _ = blackBox(work(blackBox(400))); () }),
    ]);
    ()
}
EOF
T37_MAIN_JSON="$("$GEISHA_BIN" bench "$TMP_DIR/t37_standalone_main.gsa" --filter grp/ --iters 20 --warmup 1 --rounds 3 --json --runtime "$GEISHA_RUNTIME")"
python3 - "$T37_MAIN_JSON" << 'PY'
import json, sys
data = json.loads(sys.argv[1])
assert data["ok"] is True
bs = data["benchmarks"]
assert [b["name"] for b in bs] == ["grp/a", "grp/b"], bs
assert all(b["iters"] == 20 and b["rounds"] == 3 for b in bs), bs
PY

# 37e: Project mode (`geisha.toml` + `src/` + `benches/*.gsa`, auto-calibrated iters)
BENCH_PROJ="$TMP_DIR/t37_bench_proj"
mkdir -p "$BENCH_PROJ/src" "$BENCH_PROJ/benches"
cat > "$BENCH_PROJ/geisha.toml" << 'EOF'
name = "t37_bench_proj"
version = "0.1.0"
EOF
cat > "$BENCH_PROJ/src/t37_bench_proj.gsa" << 'EOF'
pub def triSum(n: Int): Int = {
    let acc = cellNew(0);
    let i = cellNew(1);
    while (cellGet(i) <= n) {
        cellSet(acc, cellGet(acc) + cellGet(i));
        cellSet(i, cellGet(i) + 1)
    };
    cellGet(acc)
}
EOF
cat > "$BENCH_PROJ/benches/core_bench.gsa" << 'EOF'
use t37_bench_proj.triSum
use std.bench.blackBox

def bench_tri_sum_500(): Void = {
    let _ = blackBox(triSum(blackBox(500)));
    ()
}
EOF
T37_PROJ_JSON="$(cd "$BENCH_PROJ" && "$ABS_GEISHA_37" bench --warmup 2 --rounds 5 --json --runtime "$ABS_RT_37")"
python3 - "$T37_PROJ_JSON" << 'PY'
import json, sys
data = json.loads(sys.argv[1])
assert data["ok"] is True, data
bs = data["benchmarks"]
assert len(bs) == 1 and bs[0]["name"] == "bench_tri_sum_500", bs
assert bs[0]["iters"] >= 1 and bs[0]["rounds"] == 5, bs
assert bs[0]["mean_ns"] > 0 and bs[0]["ops_per_sec"] > 0, bs
PY

# 37f: Error diagnostics line-number alignment, negative checks & `--json` error contract
cat > "$TMP_DIR/t37_line_err.gsa" << 'EOF'
#!/usr/bin/env -S geisha bench
use std.bench.blackBox

def bench_bad_type(): Int = {
    let x: Int = "not_an_int";
    blackBox(x)
}
EOF
T37_LINE_ERR="$("$GEISHA_BIN" bench "$TMP_DIR/t37_line_err.gsa" --runtime "$GEISHA_RUNTIME" 2>&1 || true)"
if ! printf '%s\n' "$T37_LINE_ERR" | grep -q "t37_line_err.gsa:5:"; then
    echo "FAIL [bench_line_alignment]: expected exact 't37_line_err.gsa:5:' diagnostic, got:" >&2
    echo "$T37_LINE_ERR" >&2
    exit 1
fi

# Reject `bench_*` with parameters
cat > "$TMP_DIR/t37_bad_param.gsa" << 'EOF'
def bench_with_arg(n: Int): Int = n + 1
EOF
if "$GEISHA_BIN" bench "$TMP_DIR/t37_bad_param.gsa" --runtime "$GEISHA_RUNTIME" >/dev/null 2>&1; then
    echo "FAIL [bench_reject_params]: expected bench_with_arg(n) to be rejected" >&2
    exit 1
fi

# Reject mixing `bench_*` with top-level script statements
cat > "$TMP_DIR/t37_mixed_script.gsa" << 'EOF'
let top = 123
def bench_never_run(): Int = top
EOF
if "$GEISHA_BIN" bench "$TMP_DIR/t37_mixed_script.gsa" --runtime "$GEISHA_RUNTIME" >/dev/null 2>&1; then
    echo "FAIL [bench_reject_mixed_script]: expected mixed top-level let + bench_* to be rejected" >&2
    exit 1
fi

# Reject unknown compiler flags on `geisha bench` (e.g. `--target wasm32`) + verify `--json` error contract
T37_BAD_FLAG_JSON="$("$GEISHA_BIN" bench --target wasm32 --json --runtime "$GEISHA_RUNTIME" 2>/dev/null || true)"
python3 - "$T37_BAD_FLAG_JSON" << 'PY'
import json, sys
data = json.loads(sys.argv[1])
assert data["ok"] is False, data
assert "unknown option" in data["error"] and "--target" in data["error"], data
PY

# 37g: Explicit `main()` printing `{progress}`, non-bench JSON, plain text, control-char bench name, and >2^31 ns stats under `--json`
cat > "$TMP_DIR/t37_progress.gsa" << 'EOF'
use std.bench.{bench, blackBox, BenchStats, formatStatsJson}
use std.buf.{bufNew, bufPushStr, bufPushByte, bufToString}

def main(): Void = {
    printLn("{progress}");
    printLn("{\"msg\":\"not_a_bench\"}");
    printLn("{\"name\":\"progress\",\"mean_ns\":01,\"ops_per_sec\":0}");
    printLn("{\"name\":\"bad_num\",\"iters\":1,\"rounds\":1,\"total_ns\":1,\"mean_ns\":-01,\"median_ns\":1,\"min_ns\":1,\"max_ns\":1,\"ops_per_sec\":1}");
    printLn("plain log line");
    let b = bufNew();
    bufPushStr(b, "ctrl_");
    bufPushByte(b, 7);
    let ctrlName = bufToString(b);
    let _ = bench("ok_bench", () -> { let _ = blackBox(1 + 2); () });
    let _ = bench(ctrlName, () -> { let _ = blackBox(3 + 4); () });
    let largeStats = BenchStats {
        name: "large_2_2s",
        iters: 1,
        rounds: 1,
        totalNs: intToI64(1000000) * intToI64(2214) + intToI64(861000),
        meanNs: 2214861000.0,
        medianNs: 2214861000.0,
        minNs: 2214861000.0,
        maxNs: 2214861000.0,
        opsPerSec: 0.451495,
    };
    printLn(formatStatsJson(largeStats));
    ()
}
EOF
T37_PROG_JSON="$("$GEISHA_BIN" bench "$TMP_DIR/t37_progress.gsa" --iters 10 --warmup 1 --rounds 2 --json --runtime "$GEISHA_RUNTIME" 2>"$TMP_DIR/t37_progress.stderr")"
python3 - "$T37_PROG_JSON" "$TMP_DIR/t37_progress.stderr" << 'PY'
import json, sys
data = json.loads(sys.argv[1])
assert data["ok"] is True, data
bs = data["benchmarks"]
assert [b["name"] for b in bs] == ["ok_bench", "ctrl_\x07", "large_2_2s"], bs
lg = bs[2]
assert lg["total_ns"] == 2214861000, lg
assert lg["mean_ns"] == 2214861000.0, lg
assert lg["median_ns"] == 2214861000.0, lg
assert lg["min_ns"] == 2214861000.0, lg
assert lg["max_ns"] == 2214861000.0, lg
stderr_text = open(sys.argv[2], encoding="utf-8").read()
assert "{progress}" in stderr_text, stderr_text
assert '{"msg":"not_a_bench"}' in stderr_text, stderr_text
assert '{"name":"progress","mean_ns":01,"ops_per_sec":0}' in stderr_text, stderr_text
assert '{"name":"bad_num","iters":1,"rounds":1,"total_ns":1,"mean_ns":-01,"median_ns":1,"min_ns":1,"max_ns":1,"ops_per_sec":1}' in stderr_text, stderr_text
assert "plain log line" in stderr_text, stderr_text
PY

# 37h: Auto-discovery in `src/` must propagate span-bearing error for parameterized `bench_bad(x)` even when valid `bench_ok` exists
MIXED_SRC_PROJ="$TMP_DIR/t37_mixed_src_proj"
mkdir -p "$MIXED_SRC_PROJ/src"
cat > "$MIXED_SRC_PROJ/geisha.toml" << 'EOF'
name = "t37_mixed_src_proj"
version = "0.1.0"
EOF
cat > "$MIXED_SRC_PROJ/src/good.gsa" << 'EOF'
def bench_ok(): Int = 42
EOF
cat > "$MIXED_SRC_PROJ/src/bad.gsa" << 'EOF'
def bench_bad(x: Int): Int = x + 1
EOF
if (cd "$MIXED_SRC_PROJ" && "$ABS_GEISHA_37" bench --iters 5 --warmup 1 --rounds 1 --runtime "$ABS_RT_37" >"$TMP_DIR/t37_mixed_src.out" 2>&1); then
    echo "FAIL [bench_src_autodiscover_param_err]: expected non-zero exit when src/ contains bench_bad(x)" >&2
    exit 1
fi
T37_MIXED_ERR="$(cat "$TMP_DIR/t37_mixed_src.out")"
if ! printf '%s\n' "$T37_MIXED_ERR" | grep -q "bad.gsa:1:" || ! printf '%s\n' "$T37_MIXED_ERR" | grep -q "bench_bad"; then
    echo "FAIL [bench_src_autodiscover_param_err]: expected span diagnostic for bad.gsa:1: bench_bad, got:" >&2
    echo "$T37_MIXED_ERR" >&2
    exit 1
fi

echo "PASS [geisha_bench]: polymorphic __blackBox (native+wasm32), standalone/project modes, line-aligned diagnostics, & --json error contract verified"
PASS=$((PASS + 1))

# 38. `geisha fmt`: Canonical formatter, comment preservation, full syntax, idempotency, `--check` & project scan
FMT_DIR="$TMP_DIR/t38_fmt"
mkdir -p "$FMT_DIR/src/sub"
cat > "$FMT_DIR/geisha.toml" << 'EOF'
name = "t37_fmt"
version = "0.1.0"
EOF

cat > "$FMT_DIR/src/main.gsa" << 'EOF'
#!/usr/bin/env -S geisha run


// Top file comment
/// Module-level doc comment
use std.option.{ Option,Some,None }
use std.result.{Result,Ok,Err}
use std.str.{intToStr,parseInt}
open std.generic

/* Multi-line
   block comment */
/// Record with deriving
pub data User:Eq,Ord{
name:String,
  age:Int,
}

pub data Wrapper a(a)
pub data Pipe(Int):Eq

pub data Shape{
Circle(Int),
  Rect{w:Int,h:Int},
Empty,
}

pub type PairInt=(Int,Int)

pub concept Combinable a:Eq a{
def (<+>)(x:a,y:a):a
}

pub instance Combinable Int{
def (<+>)(x,y)=x+y
}

extern "abs" def c_abs(x:Int):Int

/// Helper with match, guards, destructuring, lambdas, `?`, radix literals & inline comments
pub def compute(
xs:List (Int,String),
u:User
):Result Int String={
let acc=cellNew(0x0A_00);// trailing comment
let (a,b)=(1_000,0o10);
let mask=0b1010_0101;
let f=(v:Int)->v*2;
let i=cellNew(0);
while(cellGet(i)<2){
cellSet(acc,cellGet(acc)+f(cellGet(i)));
cellSet(i,cellGet(i)+1)
};
let v=parseInt("42")?;
let sh=Rect{w:3,h:4};
let s=match sh{
Rect{w:rw,h:rh} if(rw>0)->rw*rh,
Rect{w:_,h:_}->0,
Circle(r)->r*r,
Empty-> -1,
};
let cond=if(a>b)(if(!false)s else 0)else -1;
Ok(cellGet(acc)+a+b+mask+v+cond+c_abs(-5)+(3<+>4)+u.age)
}

def main():Void={
let u=User{name:"Ada",age:30};
let res=match compute([(1,"a")],u){
Ok(n)->intToStr(n),
Err(e)->e,
};
printLn(res)
}
EOF

# Unformatted helper in subdirectory to verify recursive project discovery
cat > "$FMT_DIR/src/sub/helper.gsa" << 'EOF'
/// Submodule helper
pub def   addPair( p: (Int,Int) ):Int={
let (x,y)=p;
x+y   /* inline */
}
EOF

# 37a. Typecheck & run BEFORE formatting
"$GEISHA_BIN" check "$FMT_DIR/src/main.gsa" >/dev/null
"$GEISHA_BIN" -o "$FMT_DIR/before_bin" "$FMT_DIR/src/main.gsa"
BEFORE_OUT="$("$FMT_DIR/before_bin")"

# 37b. `--check` must fail (non-zero) on unformatted project
if (cd "$FMT_DIR" && "$ABS_GEISHA_36" fmt --check >/dev/null 2>&1); then
    echo "FAIL [geisha_fmt_check_dirty]: expected non-zero exit code on unformatted project" >&2
    exit 1
fi

# 37c. Default `geisha fmt` (project scan) formats all `.gsa` files in-place
(cd "$FMT_DIR" && "$ABS_GEISHA_36" fmt)
# `--check` must now exit 0
(cd "$FMT_DIR" && "$ABS_GEISHA_36" fmt --check)

# 37d. Idempotency: second `fmt --write` produces byte-for-byte identical files
cp "$FMT_DIR/src/main.gsa" "$FMT_DIR/main.pass1.gsa"
cp "$FMT_DIR/src/sub/helper.gsa" "$FMT_DIR/helper.pass1.gsa"
"$GEISHA_BIN" fmt --write "$FMT_DIR/src/main.gsa" "$FMT_DIR/src/sub/helper.gsa"
diff -u "$FMT_DIR/main.pass1.gsa" "$FMT_DIR/src/main.gsa"
diff -u "$FMT_DIR/helper.pass1.gsa" "$FMT_DIR/src/sub/helper.gsa"

# 37e. Verify comments, shebang, radix literals, and canonical spacing were preserved/applied
python3 - "$FMT_DIR/src/main.gsa" "$FMT_DIR/src/sub/helper.gsa" << 'PY'
import sys
main_src = open(sys.argv[1], encoding="utf-8").read()
helper_src = open(sys.argv[2], encoding="utf-8").read()
required_main = [
    "#!/usr/bin/env -S geisha run",
    "// Top file comment",
    "/// Module-level doc comment",
    "use std.option.{Option, Some, None}",
    "/* Multi-line\n   block comment */",
    "pub data User : Eq, Ord {",
    "pub data Wrapper a (a)",
    "pub data Pipe(Int) : Eq",
    "pub concept Combinable a : Eq a {",
    "    def (<+>)(x: a, y: a): a",
    "    xs: List (Int, String),",
    "): Result Int String = {",
    "    let acc = cellNew(0x0A_00); // trailing comment",
    "    let (a, b) = (1_000, 0o10);",
    "    let mask = 0b1010_0101;",
    "    let f = (v: Int) -> v * 2;",
    "    while (cellGet(i) < 2) {",
    "    let cond = if (a > b) (if (!false) s else 0) else -1;",
    "    Ok(cellGet(acc) + a + b + mask + v + cond + c_abs(-5) + (3 <+> 4) + u.age)",
]
for needle in required_main:
    assert needle in main_src, f"missing expected formatted snippet in main.gsa: {needle!r}\n---\n{main_src}"
assert "\n\n\n" not in main_src, "consecutive blank lines were not collapsed"
assert "pub def addPair(p: (Int, Int)): Int = {" in helper_src, f"unexpected helper.gsa:\n{helper_src}"
assert "x + y /* inline */" in helper_src, f"inline block comment lost in helper.gsa:\n{helper_src}"
PY

# 37f. Typecheck & run AFTER formatting — must produce identical output
"$GEISHA_BIN" check "$FMT_DIR/src/main.gsa" >/dev/null
"$GEISHA_BIN" check "$FMT_DIR/src/sub/helper.gsa" >/dev/null
"$GEISHA_BIN" -o "$FMT_DIR/after_bin" "$FMT_DIR/src/main.gsa"
AFTER_OUT="$("$FMT_DIR/after_bin")"
assert_eq "geisha_fmt_semantic_equivalence" "$BEFORE_OUT" "$AFTER_OUT"

# 37g. Syntax-broken file must be rejected without modifying the file
cat > "$FMT_DIR/broken.gsa" << 'EOF'
def broken(x: Int = {
EOF
cp "$FMT_DIR/broken.gsa" "$FMT_DIR/broken.orig.gsa"
if "$GEISHA_BIN" fmt "$FMT_DIR/broken.gsa" >/dev/null 2>&1; then
    echo "FAIL [geisha_fmt_broken_rejected]: expected non-zero exit on syntax error" >&2
    exit 1
fi
diff -u "$FMT_DIR/broken.orig.gsa" "$FMT_DIR/broken.gsa"

# 37h. P0/P1/P2 regression suite: cross-line cond unary `-2147483648`, unary chains, `inType` edge cases, braceless `let`/`if`, CLI flags & atomic chmod
cat > "$FMT_DIR/edge_cases.gsa" << 'EOF'
#!/usr/bin/env -S geisha run
use std.option.{Option, Some, None}
use std.str.intToStr

pub data Database { Database(Int64) }

pub data MultiData {
EApp(
Option (List Int),
String
),
}

pub type MultiAlias =
List (Int, String)

def minI32If(flag: Bool): Int =
if (flag)
-2147483648
else 0

def unaryChains(x: Int, b: Bool): (Int, Int, Bool, Int, Bool) =
(~ -x, - -x, ! !b, ~-x, !!b)

def constrainedRet: forall a. (Eq a) => a -> Option (List a) = (x) -> Some([x])

def inc(x: Int): Int = x + 1

def applyFn(
f: Int -> Option (List Int),
x: Int
): Option (List Int) = f(x)

def singleDefLambda(x: Int): Int = ((v: Int) -> inc(v))(x)

def crossLineRet(x: Int):
Option (List Int) = Some([x])

def bracelessLet(x: Int): Int =
let y = x + 1 in
y * 2

def inlineLetIf(flag: Bool): Int = {
let pick = if (flag) 1
else 2;
pick
}

def main(): Void = {
let m = minI32If(true);
let (u1, u2, u3, u4, u5) = unaryChains(5, true);
let _ = constrainedRet(1);
let _ = applyFn((n: Int) -> crossLineRet(n), 3);
let s = singleDefLambda(10) + bracelessLet(4) + inlineLetIf(false);
printLn(
intToStr(m) + "|" + intToStr(u1) + "|" + intToStr(u2) + "|"
+ (if (u3 && u5) "1" else "0") + "|" + intToStr(u4) + "|" + intToStr(s)
)
}
EOF
chmod 0755 "$FMT_DIR/edge_cases.gsa"
"$GEISHA_BIN" check "$FMT_DIR/edge_cases.gsa" >/dev/null
"$GEISHA_BIN" -o "$FMT_DIR/edge_before" "$FMT_DIR/edge_cases.gsa"
EDGE_BEFORE="$("$FMT_DIR/edge_before")"

"$GEISHA_BIN" fmt --write "$FMT_DIR/edge_cases.gsa"
"$GEISHA_BIN" fmt --check "$FMT_DIR/edge_cases.gsa"
"$GEISHA_BIN" check "$FMT_DIR/edge_cases.gsa" >/dev/null
"$GEISHA_BIN" -o "$FMT_DIR/edge_after" "$FMT_DIR/edge_cases.gsa"
EDGE_AFTER="$("$FMT_DIR/edge_after")"
assert_eq "geisha_fmt_edge_semantic_equivalence" "$EDGE_BEFORE" "$EDGE_AFTER"

python3 - "$FMT_DIR/edge_cases.gsa" << 'PY'
import os, sys
p = sys.argv[1]
src = open(p, encoding="utf-8").read()
mode = oct(os.stat(p).st_mode & 0o777)
assert mode == "0o755", f"expected 0o755 preserved via writeFileAtomic, got {mode}"
required = [
    "pub data Database { Database(Int64) }",
    "        Option (List Int),\n",
    "pub type MultiAlias =\n    List (Int, String)\n",
    "    if (flag)\n        -2147483648\n    else 0\n",
    "    (~ -x, - -x, ! !b, ~-x, !!b)\n",
    "def constrainedRet: forall a. (Eq a) => a -> Option (List a) = (x) -> Some([x])",
    "    f: Int -> Option (List Int),\n",
    "def singleDefLambda(x: Int): Int = ((v: Int) -> inc(v))(x)",
    "def crossLineRet(x: Int):\n    Option (List Int) = Some([x])\n",
    "def bracelessLet(x: Int): Int =\n    let y = x + 1 in\n    y * 2\n",
    "    let pick = if (flag) 1\n        else 2;\n",
]
for needle in required:
    assert needle in src, f"missing expected formatted edge case: {needle!r}\n---\n{src}"
PY

# `--write --stdout` must be rejected
if "$GEISHA_BIN" fmt --write --stdout "$FMT_DIR/edge_cases.gsa" >/dev/null 2>&1; then
    echo "FAIL [geisha_fmt_write_stdout_conflict]: expected error when combining --write and --stdout" >&2
    exit 1
fi

# `--stdout` on empty file must emit 0 bytes (no spurious newline)
: > "$FMT_DIR/empty.gsa"
EMPTY_BYTES="$("$GEISHA_BIN" fmt --stdout "$FMT_DIR/empty.gsa" | wc -c | tr -d ' ')"
assert_eq "geisha_fmt_stdout_empty_file" "0" "$EMPTY_BYTES"

# 37i. Adjacent postfix `?` (`Ok(nested()? ?)`) must stay separated and remain valid after formatting
cat > "$FMT_DIR/double_try.gsa" << 'EOF'
use std.result.{Result, Ok, Err}
use std.str.intToStr

def nested(): Result (Result Int String) String = Ok(Ok(42))

def unwrapTwice(): Result Int String = Ok(nested()? ?)

def main(): Void = match unwrapTwice() {
    Ok(n) -> printLn(intToStr(n)),
    Err(e) -> printLn(e),
}
EOF
"$GEISHA_BIN" check "$FMT_DIR/double_try.gsa" >/dev/null
"$GEISHA_BIN" fmt --write "$FMT_DIR/double_try.gsa"
"$GEISHA_BIN" fmt --check "$FMT_DIR/double_try.gsa"
"$GEISHA_BIN" check "$FMT_DIR/double_try.gsa" >/dev/null
python3 - "$FMT_DIR/double_try.gsa" << 'PY'
import sys
src = open(sys.argv[1], encoding="utf-8").read()
assert "Ok(nested()? ?)" in src, f"expected separated postfix '?' in:\n{src}"
assert "nested()??" not in src, f"postfix '?' merged into '??' in:\n{src}"
PY

# 37j. Directory scan must NOT follow directory/file symlinks outside target tree, and explicit unreadable dir must error
OUTSIDE_FMT_DIR="$TMP_DIR/t38_outside"
mkdir -p "$OUTSIDE_FMT_DIR"
cat > "$OUTSIDE_FMT_DIR/escape.gsa" << 'EOF'
def   outsideFn(x:Int):Int=x+1
EOF
cp "$OUTSIDE_FMT_DIR/escape.gsa" "$OUTSIDE_FMT_DIR/escape.orig.gsa"
ln -s "$OUTSIDE_FMT_DIR" "$FMT_DIR/src/ext_dir_link"
ln -s "$OUTSIDE_FMT_DIR/escape.gsa" "$FMT_DIR/src/ext_file_link.gsa"
"$GEISHA_BIN" fmt --check "$FMT_DIR/src"
"$GEISHA_BIN" fmt "$FMT_DIR/src"
diff -u "$OUTSIDE_FMT_DIR/escape.orig.gsa" "$OUTSIDE_FMT_DIR/escape.gsa"
rm -f "$FMT_DIR/src/ext_dir_link" "$FMT_DIR/src/ext_file_link.gsa"

if [ "$(id -u)" -ne 0 ]; then
    UNREADABLE_DIR="$TMP_DIR/t38_unreadable"
    mkdir -p "$UNREADABLE_DIR"
    chmod 0000 "$UNREADABLE_DIR"
    if "$GEISHA_BIN" fmt "$UNREADABLE_DIR" >/dev/null 2>&1; then
        chmod 0755 "$UNREADABLE_DIR"
        echo "FAIL [geisha_fmt_unreadable_dir]: expected error when readDir fails on explicit directory" >&2
        exit 1
    fi
    chmod 0755 "$UNREADABLE_DIR"
fi

echo "PASS [geisha_fmt_suite]: comments, full syntax, idempotency, --check, --write, --stdout, edge regressions, & semantic equivalence verified"
PASS=$((PASS + 1))

# 39. Built-in Language Server (`geisha lsp`) JSON-RPC 2.0 stdio round-trip
python3 tests/test_lsp.py "$GEISHA_BIN"
python3 tests/test_watch.py "$GEISHA_BIN"
PASS=$((PASS + 1))

# 40. Wasm32 Size Optimization Mode, --target js (ES Module + .d.ts + [target.js]), & geisha-playground.wasm
if command -v node >/dev/null 2>&1; then
    # 37a. Wasm32 size optimization (--opt z --strip --slim-runtime) & backward-compat default exports
    if [ -f "./build/wasm_rt.o" ]; then
        cat > "$TMP_DIR/t37_add.gsa" << 'EOF'
pub extern "add" def add(a: Int, b: Int): Int = a + b
def main(): Void = ()
EOF
        "$GEISHA_BIN" --target wasm32 --runtime ./build/wasm_rt.o -o "$TMP_DIR/t37_add_default.wasm" "$TMP_DIR/t37_add.gsa"
        "$GEISHA_BIN" --target wasm32 --opt z --strip --slim-runtime --runtime ./build/wasm_rt.o -o "$TMP_DIR/t37_add_slim.wasm" "$TMP_DIR/t37_add.gsa"
        SLIM_BYTES="$(wc -c < "$TMP_DIR/t37_add_slim.wasm" | tr -d ' ')"
        if [ "$SLIM_BYTES" -ge 512 ]; then
            echo "FAIL [wasm32_slim_size]: expected < 512 bytes, got $SLIM_BYTES" >&2
            exit 1
        fi
        T37_WASM_OUT="$(node -e '
            const fs = require("fs");
            (async () => {
                const d = await WebAssembly.instantiate(fs.readFileSync(process.argv[1]), { env: {} });
                const s = await WebAssembly.instantiate(fs.readFileSync(process.argv[2]), { env: {} });
                const hasDefaultGc = typeof d.instance.exports.gs_wasm_gc_collect === "function" && typeof d.instance.exports.gs_wasm_alloc === "function";
                const noSlimGc = s.instance.exports.gs_wasm_gc_collect === undefined;
                console.log([d.instance.exports.add(19, 23), s.instance.exports.add(19, 23), hasDefaultGc, noSlimGc].join("|"));
            })();
        ' "$TMP_DIR/t37_add_default.wasm" "$TMP_DIR/t37_add_slim.wasm")"
        assert_eq "wasm32_size_mode_and_compat" "42|42|true|true" "$T37_WASM_OUT"
        echo "PASS [wasm32_slim_bytes]: t37_add_slim.wasm = ${SLIM_BYTES} B (< 512 B)"
        PASS=$((PASS + 1))
    fi

    # 38b. --target js ES Module + .d.ts end-to-end semantics (Int32 wrap, Int64 BigInt, self-TCO, ADT/guards, closures, UTF-8, std.json, eval order, 1e20 float, duplicate `_` params, withAlloca, gcHandle, extern init, 100KB MRU strByteAt)
    cat > "$TMP_DIR/t37_js.gsa" << 'EOF'
use std.str.{intToStr, i64ToStr}
use std.buf.{bufNew, bufPushStr, bufToString}
use std.json.{parse as jsonParse, stringify as jsonStringify}
use std.result.{Result, Ok, Err}
use std.option.{Option, Some, None}

pub data Point {
    MkPoint { x: Int, y: Int },
}

pub data Shape {
    Circle(Int),
    Rect { w: Int, h: Int },
    Empty,
}

def gInitFlag: Cell Int = cellNew(0)

extern init def setupJsCtor(): Void = cellSet(gInitFlag, 77)

def sumTail(n: Int, acc: Int64): Int64 =
    if (n <= 0) acc
    else sumTail(n - 1, acc + intToI64(n))

def makeAdder(base: Int): Int -> Int =
    (x: Int) -> base + x

pub def constFirst(x: Int, _: Int, _: Int): Int = x

pub def applyStrCallback(f: String -> String): String = f("é")

pub def setFirstInt(arr: MutArray Int, v: Int): Void = arraySet(arr, 0, v)

pub def setFirstStr(arr: MutArray String, s: String): Void = arraySet(arr, 0, s)

pub def makeCounter(): () -> Int = {
    let n = cellNew(0);
    () -> {
        let next = cellGet(n) + 1;
        cellSet(n, next);
        next
    }
}

pub extern "area" def area(s: Shape): Int = match s {
    Circle(r) if (r > 0) -> r * r * 3,
    Rect { w: w, h: h } -> w * h,
    _ -> 0,
}

pub extern "makePoint" def makePoint(x: Int, y: Int): Point =
    MkPoint { x: x, y: y }

pub extern "jsonRoundtrip" def jsonRoundtrip(raw: String): String = match jsonParse(raw) {
    Ok(v) -> jsonStringify(v),
    Err(e) -> "ERR:" + e,
}

def testEvalOrder(): Int = {
    let c = cellNew(1);
    let r1 = cellGet(c) + { cellSet(c, 99); 10 };
    let c2 = cellNew(5);
    let xs = Cons(cellGet(c2), { cellSet(c2, 50); Nil });
    let r2 = match xs { Cons(h, _) -> h, Nil -> 0 };
    r1 * 100 + r2
}

def testBigFloat(): Bool = {
    let big = 1.0e20;
    big > 1.0e19 && big < 1.0e21
}

def testAllocaAndHandles(): Int = {
    let v = withAlloca(16, (p) -> {
        scopedPtrWriteI32Le(p, 0, 1234);
        scopedPtrReadI32Le(p, 0)
    });
    let h = gcHandleNew("pin");
    let got: String = gcHandleGet(h);
    gcHandleFree(h);
    if (got == "pin") v else -1
}

def testLargeStrLinear(): Int = {
    let b = bufNew();
    let i = cellNew(0);
    while (cellGet(i) < 10000) {
        bufPushStr(b, "0123456789");
        cellSet(i, cellGet(i) + 1)
    };
    let big = bufToString(b);
    let n = strLen(big);
    let sum = cellNew(0);
    let k = cellNew(0);
    while (cellGet(k) < n) {
        cellSet(sum, cellGet(sum) + (strByteAt(big, cellGet(k)) - 48));
        cellSet(k, cellGet(k) + 1)
    };
    cellGet(sum)
}

def testUtf8RawByteSliceAndFromBytes(): String = {
    let e = "é";
    let b0 = strSlice(e, 0, 1);
    let b1 = strSlice(e, 1, 2);
    let rejoined = b0 + b1;
    let rawArr = arrayNew(3, 0);
    arraySet(rawArr, 0, 255);
    arraySet(rawArr, 1, 0);
    arraySet(rawArr, 2, 65);
    let rawStr = strFromBytes(rawArr, 3);
    intToStr(strLen(b0)) + ":"
    + (if (rejoined == e) "eq" else "neq") + ":"
    + intToStr(strLen(rawStr)) + ":"
    + intToStr(strByteAt(rawStr, 0)) + ":"
    + intToStr(strByteAt(rawStr, 1)) + ":"
    + intToStr(strByteAt(rawStr, 2))
}

def main(): Void = {
    let wrap = 2147483647 + 1;
    let minDiv = (-2147483647 - 1) / -1;
    let tco = sumTail(100000, intToI64(0));
    let add10 = makeAdder(10);
    let cjkBytes = strLen("你好");
    let arr = parTabulate(4, (i: Int) -> i * i);
    let p = makePoint(3, 4);
    let a = area(Rect { w: p.x, h: p.y });
    let j = jsonRoundtrip("{\"k\":[1,true,\"ok\"]}");
    let ev = testEvalOrder();
    let bf = if (testBigFloat()) "fOk" else "fBad";
    let ah = testAllocaAndHandles();
    let cf = constFirst(9, 1, 2);
    let ls = testLargeStrLinear();
    let utf8Raw = testUtf8RawByteSliceAndFromBytes();
    printLn(
        intToStr(wrap) + "|"
        + intToStr(minDiv) + "|"
        + i64ToStr(tco) + "|"
        + intToStr(add10(32)) + "|"
        + intToStr(cjkBytes) + "|"
        + intToStr(immArrayGet(arr, 3)) + "|"
        + intToStr(a) + "|"
        + j + "|"
        + intToStr(ev) + "|"
        + bf + "|"
        + intToStr(ah) + "|"
        + intToStr(cf) + "|"
        + intToStr(cellGet(gInitFlag)) + "|"
        + intToStr(ls) + "|"
        + utf8Raw
    )
}
EOF
    "$GEISHA_BIN" --target js -o "$TMP_DIR/t37_js.mjs" "$TMP_DIR/t37_js.gsa"
    if [ ! -f "$TMP_DIR/t37_js.d.ts" ]; then
        echo "FAIL [js_dts_missing]: expected $TMP_DIR/t37_js.d.ts" >&2
        exit 1
    fi
    if ! grep -q "export declare function area(" "$TMP_DIR/t37_js.d.ts" || ! grep -q "export declare function constFirst(x: number, _: number, __2: number)" "$TMP_DIR/t37_js.d.ts" || ! grep -q "export type Shape" "$TMP_DIR/t37_js.d.ts" || ! grep -q "readonly w: number" "$TMP_DIR/t37_js.d.ts"; then
        echo "FAIL [js_dts_content]: unexpected .d.ts content:" >&2
        cat "$TMP_DIR/t37_js.d.ts" >&2
        exit 1
    fi
    T37_JS_MAIN="$(node "$TMP_DIR/t37_js.mjs")"
    assert_eq "js_target_main_semantics" '-2147483648|-2147483648|5000050000|42|6|9|12|{"k":[1,true,"ok"]}|1105|fOk|1234|9|77|450000|1:eq:3:255:0:65' "$T37_JS_MAIN"

    T37_JS_EXPORTS="$(node --input-type=module -e '
        import * as mod from "'"$TMP_DIR"'/t37_js.mjs";
        const pt = mod.makePoint(5, 6);
        const a1 = mod.area({ $: 0, _0: 4 });
        const a2 = mod.area({ $: 1, w: pt.x, h: pt.y });
        const jr = mod.jsonRoundtrip("{\"msg\":\"é你好\"}");
        const cb = mod.applyStrCallback((s) => (typeof s) + ":" + s + ":" + s.length);
        const ma = [1, 2];
        mod.setFirstInt(ma, 42);
        const msa = ["old"];
        mod.setFirstStr(msa, "é");
        const cnt = mod.makeCounter();
        console.log([pt.x, pt.y, a1, a2, mod.constFirst(88, 1, 2), jr, cb, ma[0], msa[0], cnt(), cnt()].join("|"));
    ')"
    # Note: importing module auto-runs main() first line, so check last line
    T37_JS_EXP_LAST="$(printf "%s\n" "$T37_JS_EXPORTS" | tail -n 1)"
    assert_eq "js_target_esm_exports" '5|6|48|30|88|{"msg":"é你好"}|string:é:1|42|é|1|2' "$T37_JS_EXP_LAST"

    # 38c. Verify downstream dep `[target.wasm32]` slim_runtime does NOT pollute root app, and invalid opt is rejected
    if [ -f "./build/wasm_rt.o" ]; then
        POLLUTE_DEP="$TMP_DIR/t38_dep"
        POLLUTE_ROOT="$TMP_DIR/t38_root"
        mkdir -p "$POLLUTE_DEP/src" "$POLLUTE_ROOT/src"
        cat > "$POLLUTE_DEP/geisha.toml" << 'EOF'
name = "t38_dep"
version = "0.1.0"

[target.wasm32]
slim_runtime = true
strip = true
opt = "z"
EOF
        cat > "$POLLUTE_DEP/src/t38_dep.gsa" << 'EOF'
pub def depVal(): Int = 7
EOF
        cat > "$POLLUTE_ROOT/geisha.toml" << EOF
name = "t38_root"
version = "0.1.0"

[deps]
t38_dep = { path = "$POLLUTE_DEP" }

[target.wasm32]
opt = "z"
strip = false
EOF
        cat > "$POLLUTE_ROOT/src/main.gsa" << 'EOF'
use t38_dep.depVal
pub extern "get_v" def getV(): Int = depVal()
def main(): Void = ()
EOF
        ABS_GEISHA_38="$(cd "$(dirname "$GEISHA_BIN")" && pwd)/$(basename "$GEISHA_BIN")"
        ABS_WRT_38="$(pwd)/build/wasm_rt.o"
        (cd "$POLLUTE_ROOT" && "$ABS_GEISHA_38" build --target wasm32 --runtime "$ABS_WRT_38" >/dev/null)
        T38_ISOL_OUT="$(node -e '
            const fs = require("fs");
            (async () => {
                const { instance } = await WebAssembly.instantiate(fs.readFileSync(process.argv[1]), { env: {} });
                console.log([instance.exports.get_v(), typeof instance.exports.gs_wasm_gc_collect === "function"].join("|"));
            })();
        ' "$POLLUTE_ROOT/build/t38_root.wasm")"
        assert_eq "wasm32_dep_flag_isolation" "7|true" "$T38_ISOL_OUT"

        # Invalid opt in geisha.toml must be rejected
        BAD_OPT_PROJ="$TMP_DIR/t38_bad_opt"
        mkdir -p "$BAD_OPT_PROJ/src"
        cat > "$BAD_OPT_PROJ/geisha.toml" << 'EOF'
name = "t38_bad_opt"
version = "0.1.0"

[target.wasm32]
opt = "bogus"
EOF
        cat > "$BAD_OPT_PROJ/src/main.gsa" << 'EOF'
def main(): Void = ()
EOF
        if (cd "$BAD_OPT_PROJ" && "$ABS_GEISHA_38" build --target wasm32 --runtime "$ABS_WRT_38" >/dev/null 2>&1); then
            echo "FAIL [wasm32_invalid_opt]: expected invalid opt='bogus' to be rejected" >&2
            exit 1
        fi
    fi

    # 38d. geisha.toml `[target.js]` via `geisha build --target js`
    JS_PROJ="$TMP_DIR/t37_js_proj"
    mkdir -p "$JS_PROJ/src"
    cat > "$JS_PROJ/geisha.toml" << 'EOF'
name = "t37_js_proj"
version = "0.1.0"

[target.js]
exports = ["doubleIt"]
dts = true
owns_main = true
EOF
    cat > "$JS_PROJ/src/main.gsa" << 'EOF'
pub def doubleIt(x: Int): Int = x * 2
def main(): Void = printLn("SHOULD_NOT_AUTO_RUN")
EOF
    ABS_GEISHA_37="$(cd "$(dirname "$GEISHA_BIN")" && pwd)/$(basename "$GEISHA_BIN")"
    (cd "$JS_PROJ" && "$ABS_GEISHA_37" build --target js >/dev/null)
    if [ ! -f "$JS_PROJ/build/t37_js_proj.mjs" ] || [ ! -f "$JS_PROJ/build/t37_js_proj.d.ts" ]; then
        echo "FAIL [js_pkg_build]: expected build/t37_js_proj.mjs and .d.ts" >&2
        exit 1
    fi
    T37_PROJ_JS_OUT="$(node --input-type=module -e '
        import { doubleIt } from "'"$JS_PROJ"'/build/t37_js_proj.mjs";
        console.log(String(doubleIt(21)));
    ')"
    assert_eq "js_pkg_build_target_js" "42" "$T37_PROJ_JS_OUT"

    # 37d. geisha-playground.wasm end-to-end client-side compile + run in Node
    if [ -f "./build/wasm_rt.o" ] && [ -f "./src/playground.gsa" ]; then
        PG_WASM="$TMP_DIR/geisha-playground.wasm"
        "$GEISHA_BIN" --src-root src --target wasm32 --opt z --strip --runtime ./build/wasm_rt.o -o "$PG_WASM" src/playground.gsa
        T37_PG_OUT="$(node --input-type=module -e '
            import fs from "node:fs";
            import { createGeishaPlayground } from "./playground/geisha-playground.mjs";
            const pg = await createGeishaPlayground(fs.readFileSync(process.argv[1]));
            const okChk = pg.check("def f(x: Int): Int = x + 1\ndef main(): Void = ()");
            const badChk = pg.check("def bad(x: Int): String = x + 1");
            const runRes = await pg.runJs("use std.str.intToStr\nuse std.list.listLen\npub def inc(x: Int): Int = x + 1\ndef main(): Void = printLn(\"pg:\" + intToStr(inc(listLen([10, 20, 30]))))");
            console.log([okChk.ok, badChk.ok, badChk.error.includes("expected `String`"), runRes.ok, runRes.dts.includes("export declare function inc("), runRes.stdout.join(",")].join("|"));
        ' "$PG_WASM")"
        assert_eq "geisha_playground_wasm_e2e" "true|false|true|true|true|pg:4" "$T37_PG_OUT"
    fi

    # 39f. Cross-PR CLI contract: `--target js` + `-e` must error, and `-Oz` / `--opt=z` / `--dev` / `--release` accepted
    if "$GEISHA_BIN" --target js -e "$TMP_DIR/t37_js.gsa" >/dev/null 2>&1; then
        echo "FAIL [js_emit_llvm_mutex]: expected '--target js -e' to be rejected" >&2
        exit 1
    fi
    if [ -f "./build/wasm_rt.o" ]; then
        "$GEISHA_BIN" --target wasm32 -Oz --slim-runtime --runtime ./build/wasm_rt.o -o "$TMP_DIR/t39_oz.wasm" "$TMP_DIR/t37_add.gsa"
        "$GEISHA_BIN" --target wasm32 --opt=z --slim-runtime --runtime ./build/wasm_rt.o -o "$TMP_DIR/t39_optz.wasm" "$TMP_DIR/t37_add.gsa"
        "$GEISHA_BIN" --target wasm32 --dev --runtime ./build/wasm_rt.o -o "$TMP_DIR/t39_dev.wasm" "$TMP_DIR/t37_add.gsa"
        "$GEISHA_BIN" --target wasm32 --release --runtime ./build/wasm_rt.o -o "$TMP_DIR/t39_rel.wasm" "$TMP_DIR/t37_add.gsa"
        "$GEISHA_BIN" --dev -o "$TMP_DIR/t39_native_dev" "$TMP_DIR/t37_add.gsa"
        "$GEISHA_BIN" -O3 -o "$TMP_DIR/t39_native_o3" "$TMP_DIR/t37_add.gsa"
        "$GEISHA_BIN" --no-main --dev -o "$TMP_DIR/t39_dev_lib.a" "$TMP_DIR/t37_add.gsa"
        echo "PASS [cli_opt_contract_and_js_emit_mutex]: -Oz/--opt=z/--dev/--release/-O3 (native+staticlib+wasm32) and --target js -e exclusion verified"
        PASS=$((PASS + 1))
    fi
fi

# --- Test 41: Portable paths, symlink-safe `removeDirAll`, POSIX `a\b` atomic write, Win64 C ABI & `gc_enter_blocking_capture` root survival ---
mkdir -p "$TMP_DIR/t39_outside" "$TMP_DIR/t39_fs/sub/deep/leaf" "$TMP_DIR/t39_fs/empty_dir"
printf 'keep-outside-safe' > "$TMP_DIR/t39_outside/secret.txt"
ln -s "$TMP_DIR/t39_outside" "$TMP_DIR/t39_fs/sub/link_to_outside"
ln -s "$TMP_DIR/t39_outside" "$TMP_DIR/t39_fs/trailing_sym"
ln -s "$TMP_DIR/t39_nonexistent_target_xyz" "$TMP_DIR/t39_fs/sub/dangling_link"

cat > "$TMP_DIR/t39_win_prep.gsa" << 'EOF'
use std.path.{
    isAbsPath, pathDirname, pathBasename, pathJoin,
    isAbsPathWin, pathJoinWin, pathDirnameWin, pathBasenameWin, pathStemWin, pathWithExtWin
}
use std.result.{Ok, Err}
use sys.fs.{mkdirAll, writeFile, writeFileAtomic, readFile, fileExists, isDir, removeDir, removeDirAll}
use sys.env.argAt

def b2s(b: Bool): String = if (b) "1" else "0"

def main(): Void = {
    let base = argAt(1);
    let outsideFile = argAt(2);
    let tree = pathJoin(base, "sub/deep/leaf");
    let _ = writeFile(pathJoin(tree, "hello.txt"), "ok");
    let emptyD = pathJoin(base, "empty_dir");
    let rmEmptyOk = removeDir(emptyD) && !isDir(emptyD);
    // Must remove directory symlink even when passed with trailing `/` WITHOUT touching target!
    let rmTrailingSymOk = removeDirAll(pathJoin(base, "trailing_sym") + "/") && !fileExists(pathJoin(base, "trailing_sym"));
    // Must remove directory tree + symlinks (including dangling) WITHOUT touching external symlink target!
    let rmTreeOk = removeDirAll(pathJoin(base, "sub")) && !isDir(pathJoin(base, "sub"));
    let outsideIntact = match readFile(outsideFile) {
        Ok(s) -> s == "keep-outside-safe",
        Err(_) -> false,
    };

    // POSIX legal filename containing backslash `a\b` must succeed with writeFileAtomic & std.path
    let bsDir = pathJoin(base, "bs_test");
    let _ = mkdirAll(bsDir);
    let bsFile = pathJoin(bsDir, "a\\b");
    let bsAtomicOk = match writeFileAtomic(bsFile, "backslash-ok") {
        Ok(_) -> match readFile(bsFile) {
            Ok(s) -> s == "backslash-ok",
            Err(_) -> false,
        },
        Err(_) -> false,
    };
    let posixBsPathOk = !isAbsPath("\\root\\x") && pathDirname("a\\b") == "." && pathBasename("a\\b") == "a\\b";

    // Explicit Windows-style path helpers
    let p1 = "C:\\Users\\dev\\app.gsa";
    let p2 = "C:\\";
    let p3 = "C:/foo/bar/";
    printLn(
        b2s(isAbsPathWin(p1)) + "|"
        + b2s(isAbsPathWin("C:rel")) + "|"
        + b2s(isAbsPathWin("\\root\\x")) + "|"
        + pathDirnameWin(p1) + "|"
        + pathBasenameWin(p1) + "|"
        + pathStemWin(p1) + "|"
        + pathWithExtWin(p1, "exe") + "|"
        + pathDirnameWin(p2) + "|"
        + pathJoinWin(p2, "bin") + "|"
        + pathDirnameWin(p3) + "|"
        + pathBasenameWin(p3) + "|"
        + b2s(rmEmptyOk) + "|"
        + b2s(rmTrailingSymOk) + "|"
        + b2s(rmTreeOk) + "|"
        + b2s(outsideIntact) + "|"
        + b2s(bsAtomicOk) + "|"
        + b2s(posixBsPathOk)
    )
}
EOF
"$GEISHA_BIN" -o "$TMP_DIR/t39_win_prep" "$TMP_DIR/t39_win_prep.gsa"
assert_eq "win_paths_symlink_remove_and_posix_backslash" \
    "1|0|1|C:\\Users\\dev|app.gsa|app|C:\\Users\\dev\\app.exe|C:\\|C:\\bin|C:/foo|bar|1|1|1|1|1|1" \
    "$("$TMP_DIR/t39_win_prep" "$TMP_DIR/t39_fs" "$TMP_DIR/t39_outside/secret.txt")"

# Verify relative GEISHA_HOME works with `geisha fetch` (git archive --output absolute path)
REL_HOME_WORK="$TMP_DIR/t39_rel_home_work"
mkdir -p "$REL_HOME_WORK/dep_repo/src" "$REL_HOME_WORK/app/src"
cat > "$REL_HOME_WORK/dep_repo/geisha.toml" << 'EOF'
name = "rel_dep"
version = "0.1.0"
EOF
cat > "$REL_HOME_WORK/dep_repo/src/rel_dep.gsa" << 'EOF'
pub def ans(): Int = 42
EOF
git -C "$REL_HOME_WORK/dep_repo" init -q
git -C "$REL_HOME_WORK/dep_repo" config user.email "ci@geisha.test"
git -C "$REL_HOME_WORK/dep_repo" config user.name "Geisha CI"
git -C "$REL_HOME_WORK/dep_repo" add .
git -C "$REL_HOME_WORK/dep_repo" commit -q -m "init"
git -C "$REL_HOME_WORK/dep_repo" tag v0.1.0
cat > "$REL_HOME_WORK/app/geisha.toml" << EOF
name = "rel_app"
version = "0.1.0"

[deps]
rel_dep = { git = "file://$REL_HOME_WORK/dep_repo", version = "0.1.0" }
EOF
cat > "$REL_HOME_WORK/app/src/main.gsa" << 'EOF'
use std.str.intToStr
use rel_dep.ans
def main(): Void = printLn(intToStr(ans()))
EOF
ABS_GEISHA_39="$(cd "$(dirname "$GEISHA_BIN")" && pwd)/$(basename "$GEISHA_BIN")"
ABS_RT_39="$(cd "$(dirname "$GEISHA_RUNTIME")" && pwd)/$(basename "$GEISHA_RUNTIME")"
REL_FETCH_OUT="$(cd "$REL_HOME_WORK/app" && env PWD="$TMP_DIR" GEISHA_HOME="local-cache" "$ABS_GEISHA_39" fetch >/dev/null && env PWD="$TMP_DIR" GEISHA_HOME="local-cache" "$ABS_GEISHA_39" build --runtime "$ABS_RT_39" >/dev/null && ./build/rel_app)"
assert_eq "relative_geisha_home_fetch_and_build" "42" "$REL_FETCH_OUT"

# Verify Win64 C ABI struct lowering & zero raw `_setjmp` in emitted LLVM IR
cat > "$TMP_DIR/t39_win64_abi.gsa" << 'EOF'
use std.option.None
use std.result.{Ok, Err}
use loader.{loadSingleSourceProgramWithPkgsNamed, MkPkgSpec}
use infer.inferProgram
use core.lowerToCore
use codegen.emitProgramLlvmIrForTarget

def containsSub(hay: String, needle: String): Bool = {
    let hn = strLen(hay);
    let nn = strLen(needle);
    if (nn == 0) true
    else if (nn > hn) false
    else {
        let i = cellNew(0);
        let found = cellNew(false);
        while (cellGet(i) <= hn - nn && !cellGet(found)) {
            if (strSlice(hay, cellGet(i), cellGet(i) + nn) == needle) cellSet(found, true)
            else cellSet(i, cellGet(i) + 1)
        };
        cellGet(found)
    }
}

def main(): Void = {
    let src =
        "extern data Box8 { x: Float }\n"
        + "extern data Vec3 { a: Int, b: Int, c: Int }\n"
        + "extern data Pair16 { x: Float, y: Float }\n"
        + "extern \"c_box8\" def c_box8(v: Box8): Box8\n"
        + "extern \"c_vec3\" def c_vec3(v: Vec3): Vec3\n"
        + "extern \"c_pair16\" def c_pair16(v: Pair16): Pair16\n"
        + "def main(): Void = {\n"
        + "    let _ = c_box8(Box8 { x: 1.0 });\n"
        + "    let _ = c_vec3(Vec3 { a: 1, b: 2, c: 3 });\n"
        + "    let _ = c_pair16(Pair16 { x: 1.0, y: 2.0 });\n"
        + "    ()\n"
        + "}\n";
    let spec = MkPkgSpec { pkgId: "", pkgName: "", srcRoots: Nil, deps: Nil };
    match loadSingleSourceProgramWithPkgsNamed("win64.gsa", src, spec, Nil, Nil) {
        Err(e) -> printLn("LOAD_ERR:" + e),
        Ok(defs) -> match inferProgram(defs) {
            Err(e) -> printLn("INF_ERR:" + e),
            Ok(inf) -> match lowerToCore(inf) {
                Err(e) -> printLn("CORE_ERR:" + e),
                Ok(cp) -> {
                    let ir = emitProgramLlvmIrForTarget(cp, false, "x86_64", "windows", Nil, false, None);
                    let okBox8 = containsSub(ir, "declare i64 @c_box8(i64)");
                    let okVec3 = containsSub(ir, "declare void @c_vec3(ptr sret({ i32, i32, i32 }) align 4, ptr)");
                    let okPair16 = containsSub(ir, "declare void @c_pair16(ptr sret({ double, double }) align 8, ptr)");
                    let noByval = !containsSub(ir, "byval(");
                    let noSetjmp = !containsSub(ir, "@_setjmp");
                    let hasCapture = containsSub(ir, "call void @gc_enter_blocking_capture()");
                    printLn(
                        (if (okBox8) "1" else "0") + "|"
                        + (if (okVec3) "1" else "0") + "|"
                        + (if (okPair16) "1" else "0") + "|"
                        + (if (noByval) "1" else "0") + "|"
                        + (if (noSetjmp) "1" else "0") + "|"
                        + (if (hasCapture) "1" else "0")
                    )
                },
            },
        },
    }
}
EOF
"$GEISHA_BIN" --src-root src -o "$TMP_DIR/t39_win64_abi" "$TMP_DIR/t39_win64_abi.gsa"
assert_eq "win64_c_abi_and_blocking_capture" "1|1|1|1|1|1" "$("$TMP_DIR/t39_win64_abi")"

# Verify `gc_enter_blocking_capture()` preserves callee-saved register GC roots under `-O2` across a blocking FFI call + major GC
cat > "$TMP_DIR/t39_blocking_roots.c" << 'EOF'
#include <pthread.h>
#include <stdint.h>
#include <stdio.h>
#include <string.h>
#include "gc.h"

static void *collector_thread(void *arg)
{
    (void)arg;
    gc_thread_attach(__builtin_frame_address(0));
    gc_collect_major();
    gc_collect_major();
    gc_thread_detach();
    return NULL;
}

__attribute__((noinline)) static void blocking_ffi_clobber_below_sp(void)
{
    /* Overwrite 512 bytes of stack below caller SP_F while another thread runs major GC */
    volatile uint64_t scratch[64];
    for (int i = 0; i < 64; i++) scratch[i] = 0xDEADBEEFCAFEBABEULL;
    pthread_t t;
    if (pthread_create(&t, NULL, collector_thread, NULL) == 0) {
        pthread_join(t, NULL);
    }
    (void)scratch[0];
}

__attribute__((noinline)) static int test_reg_roots(void)
{
    /* Allocate 4 distinct heap objects whose only live references are kept in callee-saved GPRs */
    uint64_t *a = (uint64_t *)gc_alloc_atomic(32);
    uint64_t *b = (uint64_t *)gc_alloc_atomic(32);
    uint64_t *c = (uint64_t *)gc_alloc_atomic(32);
    uint64_t *d = (uint64_t *)gc_alloc_atomic(32);
    a[0] = 0x1111222233334444ULL;
    b[0] = 0x5555666677778888ULL;
    c[0] = 0x9999AAAABBBBCCCCULL;
    d[0] = 0xDDDDEEEEFFFF0001ULL;

    /* Force pointers into registers across the blocking capture + FFI call */
    __asm__ volatile("" : "+r"(a), "+r"(b), "+r"(c), "+r"(d) :: "memory");
    gc_enter_blocking_capture();
    blocking_ffi_clobber_below_sp();
    gc_leave_blocking();

    int ok = gc_is_obj_marked(a) && gc_is_obj_marked(b) && gc_is_obj_marked(c) && gc_is_obj_marked(d)
          && a[0] == 0x1111222233334444ULL
          && b[0] == 0x5555666677778888ULL
          && c[0] == 0x9999AAAABBBBCCCCULL
          && d[0] == 0xDDDDEEEEFFFF0001ULL;
    return ok ? 1 : 0;
}

int main(void)
{
    uint64_t anchor = 0;
    gc_init_with_stack(131072, &anchor);
    gc_enable_generational();
    int ok = test_reg_roots();
    printf("%d\n", ok);
    return ok ? 0 : 1;
}
EOF
"$CC" $HOST_CC_TARGET -O2 -Iruntime/include -pthread "$TMP_DIR/t39_blocking_roots.c" "$GEISHA_RUNTIME" $HOST_CC_LIBS -o "$TMP_DIR/t39_blocking_roots"
assert_eq "blocking_capture_callee_saved_roots_O2" "1" "$("$TMP_DIR/t39_blocking_roots")"

# ---- Test: explicit WASM_LD (including path with spaces) passes unquoted to -fuse-ld= ----
REAL_WASM_LD=""
for cand in \
    /opt/homebrew/opt/lld/bin/wasm-ld \
    /opt/homebrew/opt/lld@20/bin/wasm-ld \
    /usr/local/opt/lld/bin/wasm-ld \
    /usr/local/opt/lld@20/bin/wasm-ld \
    /usr/lib/llvm-20/bin/wasm-ld \
    "$(command -v wasm-ld 2>/dev/null || true)"; do
    if [ -n "$cand" ] && [ -x "$cand" ]; then
        REAL_WASM_LD="$cand"
        break
    fi
done
if [ -n "$REAL_WASM_LD" ] && [ -f build/wasm_rt.o ]; then
    mkdir -p "$TMP_DIR/ld with space"
    ln -sf "$REAL_WASM_LD" "$TMP_DIR/ld with space/wasm-ld"
    cat > "$TMP_DIR/t40_wasm_ld.gsa" <<'EOF'
pub def add(a: Int, b: Int): Int = a + b
def main(): Void = ()
EOF
    WASM_LD="$TMP_DIR/ld with space/wasm-ld" "$GEISHA_BIN" --target wasm32 --runtime build/wasm_rt.o -o "$TMP_DIR/t40_wasm_ld.wasm" "$TMP_DIR/t40_wasm_ld.gsa"
    if [ -s "$TMP_DIR/t40_wasm_ld.wasm" ]; then
        assert_eq "wasm_ld_env_with_spaces" "ok" "ok"
    else
        assert_eq "wasm_ld_env_with_spaces" "ok" "missing wasm output"
    fi
fi

echo "[Test 41] Numeric parsing/round-trip, IntMap avalanche, NaN != NaN, JS sys/path externs & zeroed arrayNew..."
cat > "$TMP_DIR/t41_semantics.gsa" << 'EOF'
use std.option.{Option, Some, None}
use std.result.{Result, Ok, Err}
use std.str.{parseInt, parseInt64, parseFloat, floatToStr, i64ToStr, intToStr, boolToStr}
use std.map.{intMapNew, intMapInsert, intMapGet}
use std.codec.{Value, VFloat, VInt, VObj}
use std.json.{parse as jsonParse, stringify as jsonStringify}
use std.toml.{parse as tomlParse, stringify as tomlStringify}
use std.path.pathJoin
use sys.io.{print, eprint}

def isErrRes(r: Result a b): Bool = match r {
    Err(_) -> true,
    Ok(_) -> false,
}

def main(): Void = {
    // 1. Strict Int64 & Int overflow checks (including 2^64 wrap-to-zero regression)
    let ov1 = isErrRes(parseInt64("9223372036854775808"));
    let ov2 = isErrRes(parseInt64("-9223372036854775809"));
    let ov3 = isErrRes(parseInt64("18446744073709551616"));
    let ov4 = isErrRes(parseInt("18446744073709551616"));
    let ov5 = isErrRes(jsonParse("18446744073709551616"));
    let ov6 = isErrRes(tomlParse("x = 18446744073709551616\n"));
    let ov7 = isErrRes(tomlParse("x = 0x1_0000_0000_0000_0000\n"));
    let okMin = match parseInt64("-9223372036854775808") {
        Ok(v) -> i64ToStr(v) == "-9223372036854775808",
        Err(_) -> false,
    };
    let okMax = match parseInt64("9223372036854775807") {
        Ok(v) -> i64ToStr(v) == "9223372036854775807",
        Err(_) -> false,
    };

    // 2. Float lossless round-trip (tiny, >= 2^31, 0.1+0.2, -0.0) & JSON non-finite handling
    let tiny = 0.0000001;
    let huge = 1234567890123.5;
    let ulp = 0.1 + 0.2;
    let negZ = -0.0;
    let rtTiny = match jsonParse(jsonStringify(VFloat(tiny))) {
        Ok(VFloat(x)) -> floatToBits64(x) == floatToBits64(tiny),
        _ -> false,
    };
    let rtHuge = match jsonParse(jsonStringify(VFloat(huge))) {
        Ok(VFloat(x)) -> floatToBits64(x) == floatToBits64(huge),
        _ -> false,
    };
    let rtUlp = match parseFloat(floatToStr(ulp)) {
        Ok(x) -> floatToBits64(x) == floatToBits64(ulp),
        _ -> false,
    };
    let rtNegZ = floatToStr(negZ) == "-0.0";
    let nanVal = mathSqrt(-1.0);
    let jsonNan = jsonStringify(VFloat(nanVal)) == "null" && isErrRes(jsonParse("1e500"));
    let tomlRt = match tomlParse(tomlStringify(VObj([("a", VFloat(tiny)), ("b", VFloat(huge)), ("c", VFloat(nanVal))]))) {
        Ok(VObj(Cons((_, VFloat(a)), Cons((_, VFloat(b)), Cons((_, VFloat(c)), Nil))))) ->
            floatToBits64(a) == floatToBits64(tiny) && floatToBits64(b) == floatToBits64(huge) && (c != c),
        _ -> false,
    };

    // 3. IEEE-754 NaN != NaN & NaN == NaN consistency across backends
    let nanOk = (nanVal != nanVal) && !(nanVal == nanVal);
    let nan32 = floatToF32(nanVal);
    let nan32Ok = (nan32 != nan32) && !(nan32 == nan32);

    // 4. IntMap hash distribution on consecutive & stride-16 keys
    let mp = intMapNew();
    let i = cellNew(0);
    while (cellGet(i) < 1024) {
        let k = cellGet(i) * 16;
        intMapInsert(mp, k, cellGet(i) + 1);
        cellSet(i, cellGet(i) + 1)
    };
    let mapOk = match (intMapGet(mp, 0), intMapGet(mp, 16368), intMapGet(mp, 16384)) {
        (Some(1), Some(1024), None) -> true,
        _ -> false,
    };

    // 5. arrayNew zero-bit-pattern specialization (small + large > 4096B) & -0.0 preservation
    let smallZ = arrayNew(16, 0);
    let largeZ = arrayNew(2048, intToI64(0));
    let negZeroArr = arrayNew(4, -0.0);
    let arrOk =
        arrayGet(smallZ, 0) == 0 && arrayGet(smallZ, 15) == 0
        && arrayGet(largeZ, 0) == intToI64(0) && arrayGet(largeZ, 2047) == intToI64(0)
        && floatToBits64(arrayGet(negZeroArr, 3)) == floatToBits64(-0.0);

    // 6. std.path & sys.io across native and JS targets
    let pOk = strLen(pathJoin("a", "b")) == 3;
    let allOk =
        ov1 && ov2 && ov3 && ov4 && ov5 && ov6 && ov7 && okMin && okMax
        && rtTiny && rtHuge && rtUlp && rtNegZ && jsonNan && tomlRt
        && nanOk && nan32Ok && mapOk && arrOk && pOk;
    eprint("");
    print(boolToStr(allOk) + "\n")
}
EOF
"$GEISHA_BIN" --src-root src -o "$TMP_DIR/t41_semantics" "$TMP_DIR/t41_semantics.gsa"
assert_eq "semantics_native_O2" "true" "$("$TMP_DIR/t41_semantics")"
if command -v node >/dev/null 2>&1; then
    "$GEISHA_BIN" --src-root src --target js -o "$TMP_DIR/t41_semantics.mjs" "$TMP_DIR/t41_semantics.gsa"
    assert_eq "semantics_js_esm" "true" "$(node "$TMP_DIR/t41_semantics.mjs")"
fi
if [ "${WASM_AVAILABLE:-0}" = "1" ] && command -v node >/dev/null 2>&1; then
    cat > "$TMP_DIR/t41_wasm_sem.gsa" << 'EOF'
use std.result.{Result, Ok, Err}
use std.str.{parseInt64, parseFloat, floatToStr}
use std.json.{parse as jsonParse, stringify as jsonStringify}
use std.codec.{Value, VFloat}

pub def checkWasmSemantics(): Int = {
    let ov = match parseInt64("18446744073709551616") { Err(_) -> true, Ok(_) -> false };
    let tiny = 0.0000001;
    let huge = 1234567890123.5;
    let ulp = 0.1 + 0.2;
    let rt1 = match jsonParse(jsonStringify(VFloat(tiny))) { Ok(VFloat(x)) -> floatToBits64(x) == floatToBits64(tiny), _ -> false };
    let rt2 = match jsonParse(jsonStringify(VFloat(huge))) { Ok(VFloat(x)) -> floatToBits64(x) == floatToBits64(huge), _ -> false };
    let rt3 = match parseFloat(floatToStr(ulp)) { Ok(x) -> floatToBits64(x) == floatToBits64(ulp), _ -> false };
    let nanVal = mathSqrt(-1.0);
    let nanOk = (nanVal != nanVal) && !(nanVal == nanVal);
    let zArr = arrayNew(2048, intToI64(0));
    let arrOk = arrayGet(zArr, 2047) == intToI64(0);
    if (ov && rt1 && rt2 && rt3 && nanOk && arrOk) 1 else 0
}
EOF
    "$GEISHA_BIN" --src-root src --target wasm32 --runtime "${WASM_RT:-build/wasm_rt.o}" --export checkWasmSemantics -o "$TMP_DIR/t41_wasm_sem.wasm" "$TMP_DIR/t41_wasm_sem.gsa"
    T41_WASM_OUT="$(node -e '
        const fs = require("fs");
        (async () => {
            const m = await WebAssembly.instantiate(fs.readFileSync(process.argv[1]), { env: { gs_log: () => {} } });
            if (typeof m.instance.exports.__geisha_init === "function") m.instance.exports.__geisha_init();
            console.log(m.instance.exports.checkWasmSemantics());
        })();
    ' "$TMP_DIR/t41_wasm_sem.wasm")"
    assert_eq "semantics_wasm32" "1" "$T41_WASM_OUT"
fi

echo "[Test 42] CLI run/eval exit code propagation, decoded sys.proc.shell, parTabulate & GC page coalescing..."
ABS_GEISHA_42="$(cd "$(dirname "$GEISHA_BIN")" && pwd)/$(basename "$GEISHA_BIN")"
ABS_RT_42="$(cd "$(dirname "$GEISHA_RUNTIME")" && pwd)/$(basename "$GEISHA_RUNTIME")"
cat > "$TMP_DIR/t42_exit7.gsa" << 'EOF'
use sys.proc.{exit, shell}
use std.str.intToStr

def main(): Void = {
    let shCode = shell("exit 7");
    if (shCode != 7) {
        printLn("bad-shell:" + intToStr(shCode));
        exit(99)
    } else {
        exit(7)
    }
}
EOF
set +e
GEISHA_HOME="$TMP_DIR/ghome_exit" GEISHA_RUNTIME="$ABS_RT_42" "$ABS_GEISHA_42" run "$TMP_DIR/t42_exit7.gsa"
RC_SCRIPT_COLD=$?
GEISHA_HOME="$TMP_DIR/ghome_exit" GEISHA_RUNTIME="$ABS_RT_42" "$ABS_GEISHA_42" run "$TMP_DIR/t42_exit7.gsa"
RC_SCRIPT_HOT=$?
GEISHA_HOME="$TMP_DIR/ghome_exit" GEISHA_RUNTIME="$ABS_RT_42" "$ABS_GEISHA_42" run -g "$TMP_DIR/t42_exit7.gsa"
RC_SCRIPT_DBG=$?
GEISHA_HOME="$TMP_DIR/ghome_exit" GEISHA_RUNTIME="$ABS_RT_42" "$ABS_GEISHA_42" eval 'use sys.proc.exit; exit(7)'
RC_EVAL_7=$?
mkdir -p "$TMP_DIR/proj_exit7/src"
cat > "$TMP_DIR/proj_exit7/geisha.toml" << 'EOF'
name = "proj_exit7"
version = "0.1.0"
EOF
cp "$TMP_DIR/t42_exit7.gsa" "$TMP_DIR/proj_exit7/src/main.gsa"
(cd "$TMP_DIR/proj_exit7" && GEISHA_HOME="$TMP_DIR/ghome_exit" GEISHA_RUNTIME="$ABS_RT_42" "$ABS_GEISHA_42" run)
RC_PROJ_7=$?
set -e
assert_eq "cli_exit_codes_and_shell_decoded" "7|7|7|7|7" "$RC_SCRIPT_COLD|$RC_SCRIPT_HOT|$RC_SCRIPT_DBG|$RC_EVAL_7|$RC_PROJ_7"

cat > "$TMP_DIR/t42_rt_perf.gsa" << 'EOF'
use std.str.intToStr

def main(): Void = {
    // Exercise small parTabulate fast path (n < 64) + GC slab page coalesced release
    let sum = cellNew(0);
    let r = cellNew(0);
    while (cellGet(r) < 500) {
        let arr = parTabulate(8, (i) -> i + 1);
        cellSet(sum, cellGet(sum) + immArrayGet(arr, 7));
        let k = cellNew(0);
        while (cellGet(k) < 64) {
            let tmp = arrayNew(256, cellGet(k));
            cellSet(sum, cellGet(sum) + arrayGet(tmp, 0) - cellGet(k));
            cellSet(k, cellGet(k) + 1)
        };
        cellSet(r, cellGet(r) + 1)
    };
    gcTrim();
    printLn(intToStr(cellGet(sum)))
}
EOF
"$ABS_GEISHA_42" --runtime "$ABS_RT_42" -o "$TMP_DIR/t42_rt_perf" "$TMP_DIR/t42_rt_perf.gsa"
assert_eq "par_tabulate_small_and_gc_coalesce" "4000" "$("$TMP_DIR/t42_rt_perf")"

echo "[Test 43] Strict 32-bit Int literal diagnostics & cross-module Core leaf inlining / SIMD fabs..."
cat > "$TMP_DIR/t43_bad_int1.gsa" << 'EOF'
def main(): Void = { let x = 3000000000; let _ = x; () }
EOF
cat > "$TMP_DIR/t43_bad_int2.gsa" << 'EOF'
def main(): Void = { let x = 18446744073709551616; let _ = x; () }
EOF
cat > "$TMP_DIR/t43_bad_int3.gsa" << 'EOF'
def main(): Void = { let x = -2147483649; let _ = x; () }
EOF
for bf in "$TMP_DIR/t43_bad_int1.gsa" "$TMP_DIR/t43_bad_int2.gsa" "$TMP_DIR/t43_bad_int3.gsa"; do
    set +e
    T43_ERR="$("$GEISHA_BIN" check "$bf" 2>&1)"
    T43_RC=$?
    set -e
    if [ "$T43_RC" -eq 0 ] || ! printf "%s" "$T43_ERR" | grep -q "out of 32-bit Int range" || ! printf "%s" "$T43_ERR" | grep -q "append '.0' for Float"; then
        echo "FAIL [strict_int32_literal_diag]: expected range error with hint for $bf, got rc=$T43_RC: $T43_ERR" >&2
        exit 1
    fi
done
echo "PASS [strict_int32_literal_diag]: out-of-range decimal integer literals rejected with span hint"
PASS=$((PASS + 1))

cat > "$TMP_DIR/t43_leaf_simd.gsa" << 'EOF'
use std.math.{abs, fma}
use std.bits.popCount
use std.option.{Option, Some, None, unwrapOr}
use std.str.{intToStr, floatToStr}

def clampF(x: Float, lo: Float, hi: Float): Float =
    if (x < lo) lo else if (x > hi) hi else x

def stepMetric(x: Float): Float = clampF(fma(abs(x), 1.0, 0.0), 0.0, 100.0)

def sumAbsArr(arr: MutArray Float, n: Int): Float = {
    let acc = cellNew(0.0);
    let i = cellNew(0);
    while (cellGet(i) < n) {
        let idx = cellGet(i);
        cellSet(acc, cellGet(acc) + abs(arrayGet(arr, idx)));
        cellSet(i, idx + 1)
    };
    cellGet(acc)
}

def main(): Void = {
    let min32 = -2147483648;
    let max32 = 2147483647;
    let arr = arrayNew(64, -2.5);
    arraySet(arr, 7, 12.5);
    let s = sumAbsArr(arr, 64);
    let m = stepMetric(-150.0) + stepMetric(42.5);
    let pc = popCount(255) + unwrapOr(Some(10), 0) + unwrapOr(None, 5) + (min32 + max32);
    printLn(floatToStr(s) + "|" + floatToStr(m) + "|" + intToStr(pc))
}
EOF
"$GEISHA_BIN" -e -o "$TMP_DIR/t43_leaf_simd.ll" "$TMP_DIR/t43_leaf_simd.gsa"
T43_REL_FN="$(sed -n '/^define .*@sumAbsArr(/,/^}/p' "$TMP_DIR/t43_leaf_simd.ll")"
if [ -z "$T43_REL_FN" ] || printf "%s\n" "$T43_REL_FN" | grep -q '@std\.math\.abs' || ! printf "%s\n" "$T43_REL_FN" | grep -q '@llvm\.fabs\.f64'; then
    echo "FAIL [leaf_inline_std_math_abs]: expected std.math.abs to inline to @llvm.fabs.f64 in sumAbsArr IR" >&2
    exit 1
fi
if printf "%s\n" "$T43_REL_FN" | grep -q '@gc_safepoint_slow'; then
    echo "FAIL [leaf_inline_no_loop_safepoint]: expected zero @gc_safepoint_slow in inlined sumAbsArr loop" >&2
    exit 1
fi
"$GEISHA_BIN" -g -e -o "$TMP_DIR/t43_leaf_dbg.ll" "$TMP_DIR/t43_leaf_simd.gsa"
T43_DBG_FN="$(sed -n '/^define .*@sumAbsArr(/,/^}/p' "$TMP_DIR/t43_leaf_dbg.ll")"
if [ -z "$T43_DBG_FN" ] || ! printf "%s\n" "$T43_DBG_FN" | grep -q '@std\.math\.abs'; then
    echo "FAIL [leaf_inline_disabled_in_debug]: expected -g debug build to preserve @std.math.abs call" >&2
    exit 1
fi
"$GEISHA_BIN" --runtime "$GEISHA_RUNTIME" -o "$TMP_DIR/t43_leaf_simd" "$TMP_DIR/t43_leaf_simd.gsa"
assert_eq "leaf_inline_native_run" "170.0|142.5|22" "$("$TMP_DIR/t43_leaf_simd")"
if command -v node >/dev/null 2>&1; then
    "$GEISHA_BIN" --target js -o "$TMP_DIR/t43_leaf_simd.mjs" "$TMP_DIR/t43_leaf_simd.gsa"
    assert_eq "leaf_inline_js_run" "170.0|142.5|22" "$(node "$TMP_DIR/t43_leaf_simd.mjs")"
fi

echo "All $PASS end-to-end test suites passed!"
