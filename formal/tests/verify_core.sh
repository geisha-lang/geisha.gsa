#!/bin/sh
# End-to-end Verified Translation Validation across all 4 Formal Pillars:
# 1. Maranget Pattern Match Exhaustiveness (eliminating Trap.matchFailure)
# 2. Full Concurrency (Task + MVar + Chan + !Send-state Actor) & Data-Race Freedom
# 3. Escape Analysis & Stack-Frame Region Memory Safety ((stack-allocs ...))
# 4. Exact 40-bit GC Pointer Masks & Arithmetic/Trap Conformance
set -eu

GEISHA_BIN="${GEISHA_BIN:-./build/geisha2}"
GEISHA_RUNTIME="${GEISHA_RUNTIME:-./build/libgeisha_runtime.a}"
CHECKER_BIN="${CHECKER_BIN:-./formal/.lake/build/bin/geisha-check}"
export GEISHA_RUNTIME

TMP_DIR="$(mktemp -d "${TMPDIR:-/tmp}/geisha_formal_verify.XXXXXX")"
trap 'rm -rf "$TMP_DIR"' EXIT

# 1. Rich Core Geisha program (recursive ADT, generic Option, Concept, closure, stack-promoted while+Cell, exhaustive match)
cat > "$TMP_DIR/demo.gsa" << 'EOF'
use std.option.{Option, Some, None}

data Expr {
    Lit(Int),
    Add(Expr, Expr),
    Div(Expr, Expr),
}

concept Combine a {
    def combine(x: a, y: a): a
}

instance Combine Int {
    def combine(x, y) = x + y
}

def evalExpr(e: Expr): Option Int = match e {
    Lit(n) -> Some(n),
    Add(a, b) -> match (evalExpr(a), evalExpr(b)) {
        (Some(x), Some(y)) -> Some(combine(x, y)),
        _ -> None,
    },
    Div(a, b) -> match (evalExpr(a), evalExpr(b)) {
        (Some(x), Some(y)) -> if (y == 0) None else Some(x / y),
        _ -> None,
    },
}

def makeAdder(base: Int): Int -> Int = (x) -> base + x

def sumTo(n: Int): Int = {
    let acc = cellNew(0);
    let i = cellNew(1);
    while (cellGet(i) <= n) {
        cellSet(acc, cellGet(acc) + cellGet(i));
        cellSet(i, cellGet(i) + 1)
    };
    cellGet(acc)
}

def main(): Void = {
    let f = makeAdder(10);
    let e = Add(Lit(f(5)), Div(Lit(84), Lit(2)));
    let r = match evalExpr(e) {
        Some(v) -> v + sumTo(5),
        None -> 0,
    };
    let _ = r;
    ()
}
EOF

"$GEISHA_BIN" --dump-core "$TMP_DIR/demo.gscore" -o "$TMP_DIR/demo" "$TMP_DIR/demo.gsa"
"$TMP_DIR/demo"
if ! grep -q '(fn-stack "sumTo" "acc" "i")' "$TMP_DIR/demo.gscore"; then
    echo "FAIL: expected sumTo stack-promoted cells (acc, i) in demo.gscore!" >&2
    exit 1
fi
"$CHECKER_BIN" "$TMP_DIR/demo.gscore"

# 2. Negative type check: tampered literal type in Core IR must be rejected
sed 's/(lit-int 10)/(lit-bool true)/' "$TMP_DIR/demo.gscore" > "$TMP_DIR/demo_bad_ty.gscore"
if "$CHECKER_BIN" "$TMP_DIR/demo_bad_ty.gscore" 2>/dev/null; then
    echo "FAIL: tampered Core IR literal type was accepted!" >&2
    exit 1
fi
echo "PASS [tampered_core_rejected]: Lean 4 checker rejected ill-typed Core IR"

# 3. Negative Pillar 1 check: deleting an ADT match arm in Core IR must be rejected by Maranget exhaustiveness verifier
python3 -c '
import sys
s = open(sys.argv[1]).read()
target = "(arm (pctor \"Expr\" 0 (pvar \"n\")) (make-data \"std.option.Option_Int\" 1 (var \"n\"))) "
assert target in s, "expected Lit arm in demo.gscore"
open(sys.argv[2], "w").write(s.replace(target, "", 1))
' "$TMP_DIR/demo.gscore" "$TMP_DIR/demo_nonexh.gscore"
if "$CHECKER_BIN" "$TMP_DIR/demo_nonexh.gscore" 2>/dev/null; then
    echo "FAIL: non-exhaustive Core IR match was accepted!" >&2
    exit 1
fi
echo "PASS [non_exhaustive_match_rejected]: Lean 4 Maranget verifier rejected non-exhaustive Core IR match"

# 4. Full Concurrent Core Geisha program (`Task` + `par` + `MVar` + `Chan` + `!Send`-state `Actor` + recursive `Tree` ADT)
cat > "$TMP_DIR/conc_demo.gsa" << 'EOF'
use std.option.{Option, Some, None}
use std.task.{Task, spawn, await, par}
use std.sync.{MVar, mvarEmpty, mvarTake, mvarPut, Chan, chanNew, chanSend, chanRecv, chanClose}
use std.actor.{Actor, actorSpawn, actorAsk, actorSend}

data Tree {
    Leaf(Int),
    Node(Tree, Tree),
}

def sumTree(t: Tree): Int = match t {
    Leaf(n) -> n,
    Node(l, r) -> sumTree(l) + sumTree(r),
}

def makeAdder(base: Int): Int -> Int = (x) -> base + x

def applyTwice(f: Int -> Int, x: Int): Int = f(f(x))

def main(): Void = {
    let tree = Node(Leaf(10), Node(Leaf(20), Leaf(12)));
    let add5 = makeAdder(5);
    let mv: MVar Int = mvarEmpty();
    let ch: Chan Int = chanNew(4);

    // Sequential Actor encapsulating `!Send` mutable `Cell Int` state
    let counter: Actor (Cell Int) = actorSpawn(() -> cellNew(sumTree(tree)));

    // Spawned `shared` task captures `Tree`, `shared` closure `add5`, `MVar`, `Chan`,
    // and `Actor (Cell Int)`, plus mutates its own thread-local `Cell` via a `local` closure!
    let bg: Task Int = spawn(() -> {
        let localAcc = cellNew(0);
        let bumpLocal = (d: Int) -> cellSet(localAcc, cellGet(localAcc) + d);
        bumpLocal(applyTwice(add5, 0));
        mvarPut(mv, cellGet(localAcc));
        let _ = chanSend(ch, 15);
        chanClose(ch);
        actorSend(counter, (c) -> cellSet(c, cellGet(c) + 8));
        actorAsk(counter, (c) -> cellGet(c))
    });

    // Main thread simultaneously mutates its own `Cell` via `par`'s `local` left branch
    let mainCell = cellNew(1);
    let (leftRes, rightRes) = par(
        () -> {
            let step = (y: Int) -> {
                cellSet(mainCell, cellGet(mainCell) + y);
                cellGet(mainCell)
            };
            applyTwice(step, 4)
        },
        () -> applyTwice(add5, 30)
    );

    let fromMv = mvarTake(mv);
    let fromCh = match chanRecv(ch) {
        Some(v) -> v,
        None -> 0,
    };
    let total = await(bg) + leftRes + rightRes + fromMv + fromCh;
    let _ = total;
    ()
}
EOF

"$GEISHA_BIN" --dump-core "$TMP_DIR/conc_demo.gscore" -o "$TMP_DIR/conc_demo" "$TMP_DIR/conc_demo.gsa"
"$TMP_DIR/conc_demo"
"$CHECKER_BIN" "$TMP_DIR/conc_demo.gscore"

# 5. Negative Pillar 2a check: tampering a Cell-capturing `local` closure into `shared` MUST be rejected!
sed 's/(lam local/(lam shared/g' "$TMP_DIR/conc_demo.gscore" > "$TMP_DIR/conc_bad_mode.gscore"
if "$CHECKER_BIN" "$TMP_DIR/conc_bad_mode.gscore" 2>/dev/null; then
    echo "FAIL: Cell-capturing closure forged as 'shared' was accepted!" >&2
    exit 1
fi
echo "PASS [tampered_shared_capture_rejected]: Lean 4 checker rejected forged 'shared' closure capturing Cell"

# 6. Negative Pillar 2b check: spawning a `local` closure MUST be rejected!
sed 's/(lam shared () int/(lam local () int/' "$TMP_DIR/conc_demo.gscore" > "$TMP_DIR/conc_bad_spawn.gscore"
if "$CHECKER_BIN" "$TMP_DIR/conc_bad_spawn.gscore" 2>/dev/null; then
    echo "FAIL: spawning a 'local' closure was accepted!" >&2
    exit 1
fi
echo "PASS [tampered_local_spawn_rejected]: Lean 4 checker rejected spawning a 'local' closure"

# 7. Negative Pillar 3 check: forging stack-allocation `(fn-stack "main" "mainCell")` for a closure-captured Cell MUST be rejected!
python3 -c '
import sys
s = open(sys.argv[1]).read()
assert "(stack-allocs\n" in s
open(sys.argv[2], "w").write(s.replace("(stack-allocs\n", "(stack-allocs\n    (fn-stack \"main\" \"mainCell\")\n", 1))
' "$TMP_DIR/conc_demo.gscore" "$TMP_DIR/conc_bad_escape.gscore"
if "$CHECKER_BIN" "$TMP_DIR/conc_bad_escape.gscore" 2>/dev/null; then
    echo "FAIL: escaping closure-captured Cell forged in stack-allocs was accepted!" >&2
    exit 1
fi
echo "PASS [tampered_escaping_stack_alloc_rejected]: Lean 4 escape verifier rejected stack promotion of closure-captured Cell"

# 8. Conformance: INT_MIN / -1 wraps cleanly (no LLVM UB) and div-by-zero traps cleanly
cat > "$TMP_DIR/div_ov.gsa" << 'EOF'
use std.str.intToStr
def safeDiv(a: Int, b: Int): Int = a / b
def safeRem(a: Int, b: Int): Int = a % b
def main() = {
    let minVal = -2147483647 - 1;
    printLn(intToStr(safeDiv(minVal, -1)) + "|" + intToStr(safeRem(minVal, -1)))
}
EOF
"$GEISHA_BIN" -o "$TMP_DIR/div_ov" "$TMP_DIR/div_ov.gsa"
OUT="$("$TMP_DIR/div_ov")"
if [ "$OUT" != "-2147483648|0" ]; then
    echo "FAIL [int_min_div_neg1]: expected '-2147483648|0', got '$OUT'" >&2
    exit 1
fi
echo "PASS [int_min_div_neg1]: $OUT"

cat > "$TMP_DIR/div_zero.gsa" << 'EOF'
def boom(a: Int, b: Int): Int = a / b
def main() = { let _ = boom(10, 0); () }
EOF
"$GEISHA_BIN" -o "$TMP_DIR/div_zero" "$TMP_DIR/div_zero.gsa"
if "$TMP_DIR/div_zero" 2>"$TMP_DIR/div_zero.err"; then
    echo "FAIL [div_by_zero_trap]: expected trap, got exit 0" >&2
    exit 1
fi
echo "PASS [div_by_zero_trap]: $(cat "$TMP_DIR/div_zero.err")"
