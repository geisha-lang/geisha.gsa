#!/bin/sh
# End-to-end test suite for the self-hosted Geisha compiler (`geisha.gs`)
set -eu

GEISHA_BIN="${GEISHA_BIN:-./build/geisha2}"
GEISHA_RUNTIME="${GEISHA_RUNTIME:-./build/libgeisha_runtime.a}"
export GEISHA_RUNTIME

TMP_DIR="$(mktemp -d "${TMPDIR:-/tmp}/geisha_gs_tests.XXXXXX")"
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
cat > "$TMP_DIR/t1_lang.gs" << 'EOF'
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
"$GEISHA_BIN" -o "$TMP_DIR/t1_lang" "$TMP_DIR/t1_lang.gs"
assert_eq "adt_field_try_mutual_rec" "diag:14|42|err|even" "$("$TMP_DIR/t1_lang")"

# 2. Open Concepts, Custom Symbolic Operators, Prefix `~`, Bitwise Ops & Int64
cat > "$TMP_DIR/t2_ops.gs" << 'EOF'
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
"$GEISHA_BIN" -o "$TMP_DIR/t2_ops" "$TMP_DIR/t2_ops.gs"
assert_eq "concepts_custom_and_bitwise_ops" "3|1099511628031|15|-1|8|4|34" "$("$TMP_DIR/t2_ops")"

# 3. C `extern` FFI + Float IEEE-754 Bit Intrinsics
cat > "$TMP_DIR/t3_ffi.gs" << 'EOF'
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
"$GEISHA_BIN" -o "$TMP_DIR/t3_ffi" "$TMP_DIR/t3_ffi.gs"
assert_eq "c_extern_ffi_and_floats" "99|10|0x4014000000000000" "$("$TMP_DIR/t3_ffi")"

# 4. Multi-file Project Mode (`--src-root`) with `pub use` Re-export
mkdir -p "$TMP_DIR/proj/math"
cat > "$TMP_DIR/proj/math/inner.gs" << 'EOF'
pub def triple(x: Int): Int = x * 3
EOF
cat > "$TMP_DIR/proj/math/mod.gs" << 'EOF'
pub mod inner
pub use inner.triple
pub def addOne(x: Int): Int = x + 1
EOF
cat > "$TMP_DIR/proj/mod.gs" << 'EOF'
mod math
use math.{triple, addOne}
use std.str.intToStr

def main() = printLn(intToStr(addOne(triple(13))))
EOF
"$GEISHA_BIN" --src-root "$TMP_DIR" -o "$TMP_DIR/t4_proj" "$TMP_DIR/proj/mod.gs"
assert_eq "multifile_modules_pub_use" "40" "$("$TMP_DIR/t4_proj")"

# 5. Concurrency (`Task`, `Chan`, `Actor`)
cat > "$TMP_DIR/t5_conc.gs" << 'EOF'
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
"$GEISHA_BIN" -o "$TMP_DIR/t5_conc" "$TMP_DIR/t5_conc.gs"
assert_eq "concurrency_task_chan_actor" "42|100|15" "$("$TMP_DIR/t5_conc")"

# 6. Negative Compile-Time Check: Non-exhaustive Pattern Match Rejected
cat > "$TMP_DIR/t6_bad.gs" << 'EOF'
use std.option.{Option, Some, None}
def bad(x: Option Int): Int = match x {
    Some(v) -> v,
}
def main() = putNumber(bad(None))
EOF
if "$GEISHA_BIN" -o "$TMP_DIR/t6_bad" "$TMP_DIR/t6_bad.gs" >/dev/null 2>&1; then
    echo "FAIL [non_exhaustive_rejected]: compiler unexpectedly accepted non-exhaustive match" >&2
    exit 1
fi
echo "PASS [non_exhaustive_rejected]: rejected non-exhaustive match"
PASS=$((PASS + 1))

echo "All $PASS end-to-end test suites passed!"
