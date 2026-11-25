#!/bin/sh
# End-to-end test suite for the self-hosted Geisha compiler (`geisha.gsa`)
set -eu

GEISHA_BIN="${GEISHA_BIN:-./build/geisha2}"
GEISHA_RUNTIME="${GEISHA_RUNTIME:-./build/libgeisha_runtime.a}"
export GEISHA_RUNTIME

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

# 9. `sys.net` + `std.ws`: RFC 6455 Handshake & Concurrent Loopback WebSocket + JSON Echo
cat > "$TMP_DIR/t9_ws_loopback.gsa" << 'EOF'
use std.result.{Ok, Err}
use std.task.{spawn, await}
use std.codec.{object, (:=), at, str}
use std.json.{toJson, decodeString}
use sys.net.{tcpListen, tcpLocalPort, tcpAccept, tcpCloseListener}
use std.ws.{
    WsText, WsClose, wsAcceptKey, wsAccept, wsConnect,
    wsRecv, wsSendText, wsSendTextMasked, wsSendClose, wsClose
}

def main() = {
    // RFC 6455 Section 1.3 official test vector
    let keyCheck = wsAcceptKey("dGhlIHNhbXBsZSBub25jZQ==");

    let listener = match tcpListen("127.0.0.1", 0) {
        Ok(l) -> l,
        Err(e) -> { printLn("LISTEN_ERR:" + e); l_fail() },
    };
    let port = tcpLocalPort(listener);

    let srv = spawn(() -> {
        let res = match tcpAccept(listener) {
            Err(e) -> "ACCEPT_ERR:" + e,
            Ok(stream) -> match wsAccept(stream) {
                Err(e) -> "WS_ACCEPT_ERR:" + e,
                Ok(conn) -> {
                    let out = match wsRecv(conn) {
                        Ok(WsText(msg)) -> match decodeString(at("msg", str), msg) {
                            Ok(word) -> {
                                let reply = toJson(object(["echo" := word + "!"]));
                                let _ = wsSendText(conn, reply);
                                "srv-ok"
                            },
                            Err(_) -> "decode-err",
                        },
                        _ -> "recv-err",
                    };
                    let _ = wsRecv(conn);
                    wsClose(conn);
                    out
                },
            },
        };
        tcpCloseListener(listener);
        res
    });

    let cliRes = match wsConnect("127.0.0.1", port, "/ws") {
        Err(e) -> "CLI_CONN_ERR:" + e,
        Ok(conn) -> {
            let payload = toJson(object(["msg" := "tingfeng"]));
            let _ = wsSendTextMasked(conn, payload);
            let got = match wsRecv(conn) {
                Ok(WsText(reply)) -> match decodeString(at("echo", str), reply) {
                    Ok(v) -> v,
                    Err(_) -> "cli-decode-err",
                },
                _ -> "cli-recv-err",
            };
            let _ = wsSendClose(conn, 1000, "bye");
            wsClose(conn);
            got
        },
    };

    let srvRes = await(srv);
    printLn(keyCheck + "|" + srvRes + "|" + cliRes)
}

def l_fail(): sys.net.TcpListener = {
    let _ = arrayGet(arrayNew(0, 0), 0);
    sys.net.TcpListener(-1)
}
EOF
"$GEISHA_BIN" -o "$TMP_DIR/t9_ws_loopback" "$TMP_DIR/t9_ws_loopback.gsa"
assert_eq "net_and_ws_json_loopback" "s3pPLMBiTxaQ9kYGzzhZRbK+xOo=|srv-ok|tingfeng!" "$("$TMP_DIR/t9_ws_loopback")"

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
  console.log(c + "|" + res + "|" + syncOk + "|" + clsRes + "|" + gcOk);
});
' "$TMP_DIR/t12_wasm.wasm")"
assert_eq "wasm32_codec_json_and_host_ffi" '15|{"name":"Tingfeng","hp":115}|sync|card:65|gc-ok' "$WASM_OUT"
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

echo "All $PASS end-to-end test suites passed!"
