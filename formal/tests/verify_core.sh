#!/bin/sh
# End-to-end Verified Translation Validation across all Formal Pillars & Guardrails:
# 1. Maranget Pattern Match Exhaustiveness (eliminating Trap.matchFailure)
# 2. Full Concurrency (Task + MVar + Chan + !Send-state Actor) & Data-Race Freedom
# 3. Unfiltered Escape Analysis & Stack-Frame Region Memory Safety ((stack-allocs ...))
# 4. Live Codegen 40-bit GC Pointer Masks ((gc-masks ...)) & Differential Small-Step Evaluation (--eval)
# 5. Full E2E Language-Surface Suite + ~20,000-line Self-Hosted Compiler Translation Validation
set -eu

GEISHA_BIN="${GEISHA_BIN:-./build/geisha2}"
GEISHA_RUNTIME="${GEISHA_RUNTIME:-./build/libgeisha_runtime.a}"
CHECKER_BIN="${CHECKER_BIN:-./formal/.lake/build/bin/geisha-check}"
export GEISHA_RUNTIME

TMP_DIR="$(mktemp -d "${TMPDIR:-/tmp}/geisha_formal_verify.XXXXXX")"
trap 'rm -rf "$TMP_DIR"' EXIT

# 0. Static anti-bypass guardrail: core_dump.gsa MUST NOT silently pre-filter escFnStackVars
if grep -qE 'checkStackVarInCoreDump|onlyDirectCellOpsDump' src/core_dump.gsa; then
    echo "FAIL [no_silent_escape_filter]: src/core_dump.gsa must emit raw escFnStackVars without pre-filtering!" >&2
    exit 1
fi
if ! grep -q 'isKnownCoreIntrinsic' src/core_dump.gsa; then
    echo "FAIL [fail_closed_intrinsic_allowlist]: src/core_dump.gsa must enforce isKnownCoreIntrinsic allowlist!" >&2
    exit 1
fi
echo "PASS [anti_bypass_guardrails]: raw unfiltered stack-allocs & fail-closed intrinsic allowlist enforced"

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
if ! grep -q '(gc-masks' "$TMP_DIR/demo.gscore"; then
    echo "FAIL: expected live (gc-masks ...) section in demo.gscore!" >&2
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

# 3b. Negative Pillar 4 check: tampering live codegen GC pointer mask bits in (gc-masks ...) MUST be rejected!
python3 -c '
import sys
s = open(sys.argv[1]).read()
target = "(adt-masks \"Expr\" (vmask 0 (mask 0)) (vmask 1 (mask 6)) (vmask 2 (mask 6)))"
assert target in s, f"expected Expr gc-masks entry in demo.gscore"
# Drop pointer bit 2 (word 2 of Add(Expr, Expr)) so GC would miss the second child pointer
open(sys.argv[2], "w").write(s.replace(target, "(adt-masks \"Expr\" (vmask 0 (mask 0)) (vmask 1 (mask 2)) (vmask 2 (mask 6)))", 1))
# Forge bit 0 (tag word) as a pointer on Lit(Int)
open(sys.argv[3], "w").write(s.replace(target, "(adt-masks \"Expr\" (vmask 0 (mask 1)) (vmask 1 (mask 6)) (vmask 2 (mask 6)))", 1))
' "$TMP_DIR/demo.gscore" "$TMP_DIR/demo_bad_gcmask1.gscore" "$TMP_DIR/demo_bad_gcmask2.gscore"
if "$CHECKER_BIN" "$TMP_DIR/demo_bad_gcmask1.gscore" 2>/dev/null; then
    echo "FAIL: tampered GC pointer mask dropping pointer field bit was accepted!" >&2
    exit 1
fi
if "$CHECKER_BIN" "$TMP_DIR/demo_bad_gcmask2.gscore" 2>/dev/null; then
    echo "FAIL: tampered GC pointer mask setting tag-word bit 0 was accepted!" >&2
    exit 1
fi
echo "PASS [tampered_gc_masks_rejected]: Lean 4 LP64 GC layout oracle rejected wrong pointer masks"

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

# 8b. Operational Semantics Differential Testing (`geisha-check --eval` vs Native LLVM Binary):
#     Evaluates pure Core IR via Lean's proven `runSteps` small-step reducer and asserts
#     bit-for-bit agreement with the compiled native binary!
cat > "$TMP_DIR/diff_sem.gsa" << 'EOF'
use std.option.{Option, Some, None}

data Pack {
    MkPack(Int, Int, String),
}

data SeqTree {
    SLeaf(Int),
    SBranch(SeqTree, SeqTree),
}

def foldSeqTree(t: SeqTree): Int = match t {
    SLeaf(v) -> v,
    SBranch(l, r) -> foldSeqTree(l) * 3 + foldSeqTree(r),
}

def classifyGuard(p: Pack): Int = match p {
    MkPack(a, b, tag) if (a > b && tag == "hi") -> a - b,
    MkPack(a, b, _) -> a + b,
}

def computeConformance(): String = {
    let min32 = -2147483647 - 1;
    let max32 = 2147483647;
    let wrapAdd = max32 + 1;
    let wrapDiv = min32 / (-1);
    let wrapRem = min32 % (-1);
    let sh1 = (-16) >> 2;
    let sh2 = (-16) >>> 28;
    let shMask = 1 << 35;
    let bitMix = ((0x5A ^ 0x0F) & (~0x03)) | 0x100;
    let sc1 = if (false && (1 / 0 == 0)) 99 else 11;
    let sc2 = if (true || (1 / 0 == 0)) 22 else 88;
    let cCmp = if ('A' < 'Z' && 'z' > 'a' && 'x' == 'x') 7 else 0;
    let sCmp = if ("ab" + "cd" == "abcd" && "abc" < "abd" && "z" > "a") 9 else 0;
    let acc = cellNew(0);
    let k = cellNew(1);
    while (cellGet(k) <= 6) {
        let cur = cellGet(k);
        let f = (x: Int) -> x * cur + 1;
        cellSet(acc, cellGet(acc) + f(2));
        cellSet(k, cur + 1)
    };
    let treeVal = foldSeqTree(SBranch(SLeaf(4), SBranch(SLeaf(5), SLeaf(2))));
    let g1 = classifyGuard(MkPack(10, 3, "hi"));
    let g2 = classifyGuard(MkPack(10, 3, "lo"));
    let ok =
        wrapAdd == min32
        && wrapDiv == min32
        && wrapRem == 0
        && sh1 == -4
        && sh2 == 15
        && shMask == 8
        && bitMix == 340
        && sc1 + sc2 == 33
        && cCmp == 7
        && sCmp == 9
        && cellGet(acc) == 48
        && treeVal == 29
        && g1 == 7
        && g2 == 13;
    if (ok) "CONFORMANCE_OK:29:48:340" else "CONFORMANCE_MISMATCH"
}

def main(): Void = printLn(computeConformance())
EOF
"$GEISHA_BIN" --dump-core "$TMP_DIR/diff_sem.gscore" -o "$TMP_DIR/diff_sem" "$TMP_DIR/diff_sem.gsa"
"$CHECKER_BIN" "$TMP_DIR/diff_sem.gscore"
NATIVE_DIFF_OUT="$("$TMP_DIR/diff_sem")"
LEAN_DIFF_OUT="$("$CHECKER_BIN" --eval computeConformance "$TMP_DIR/diff_sem.gscore")"
if [ "$NATIVE_DIFF_OUT" != "$LEAN_DIFF_OUT" ] || [ "$NATIVE_DIFF_OUT" != "CONFORMANCE_OK:29:48:340" ]; then
    echo "FAIL [differential_semantics]: native='$NATIVE_DIFF_OUT' vs lean='$LEAN_DIFF_OUT'" >&2
    exit 1
fi
echo "PASS [differential_semantics]: native binary == Lean small-step --eval ($LEAN_DIFF_OUT)"

# 9. Full-spectrum Core translation validation: Int64, Float, Float32, Char, MutArray,
#    Arena/ForeignPtr/ScopedPtr FFI, pattern guards, global Cell, while+`?`, and shadowed param Cell
cat > "$TMP_DIR/full_ext.gsa" << 'EOF'
use std.option.{Option, Some, None}
use std.result.{Result, Ok, Err}

def gCounter: Cell Int = cellNew(10)

def bumpGlobalAndShadow(x: Cell Int, n: Int): Int = {
    cellSet(gCounter, cellGet(gCounter) + n);
    let x = cellNew(n * 2);
    let i = cellNew(0);
    while (cellGet(i) < 3) {
        let loopCell = cellNew(cellGet(i) + 1);
        cellSet(x, cellGet(x) + cellGet(loopCell));
        cellSet(i, cellGet(i) + 1)
    };
    cellGet(x)
}

def scanWhileTry(xs: List Int): Result Int String = {
    let acc = cellNew(0);
    let cur = cellNew(xs);
    while (match cellGet(cur) { Nil -> false, _ -> true }) {
        match cellGet(cur) {
            Cons(v, rest) if (v >= 0) -> {
                cellSet(acc, cellGet(acc) + v);
                cellSet(cur, rest)
            },
            Cons(_, _) -> {
                let _ = Err("neg")?;
                ()
            },
            Nil -> (),
        }
    };
    Ok(cellGet(acc))
}

def main(): Void = {
    let i64v = (intToI64(7) << 4) + intToI64(3);
    let fv = 3.5 * 2.0 - 1.0;
    let f32v = floatToF32(fv) + floatToF32(1.5);
    let ch = 'G';
    let arr = arrayNew(4, i64ToInt(i64v));
    arraySet(arr, 1, floatToInt(fv) + f32ToInt(f32v));
    let arenaByte = withArena((a) -> {
        let p = arenaAlloc(a, intToI64(16));
        scopedPtrSetByte(p, 0, charToInt(ch));
        scopedPtrByteAt(p, 0)
    });
    let pBox = cellNew(1);
    let s1 = bumpGlobalAndShadow(pBox, arenaByte - 70);
    let s2 = match scanWhileTry([1, 2, 3]) {
        Ok(v) -> v,
        Err(_) -> 0,
    };
    let _ = arrayGet(arr, 1) + s1 + s2 + cellGet(gCounter);
    ()
}
EOF
"$GEISHA_BIN" --dump-core "$TMP_DIR/full_ext.gscore" -o "$TMP_DIR/full_ext" "$TMP_DIR/full_ext.gsa"
"$TMP_DIR/full_ext"
"$CHECKER_BIN" "$TMP_DIR/full_ext.gscore"

# 10. Full Language-Surface E2E Suite Translation Validation:
#     Extract every positive standalone `.gsa` test program from `tests/run_tests.sh`
#     (covering HKT, FunDeps, MTL, generic derive, Float32, Ptr/ScopedPtr/Arena/ForeignPtr,
#     ImmArray/parTabulate, @repr(C) structs, cFnPtr, radix/_ literals, sys.fs, sys.proc,
#     std.toml.patch, codec.json, Task/MVar/Chan/Actor, etc.) and verify each with Lean 4!
mkdir -p "$TMP_DIR/e2e_suite"
python3 - tests/run_tests.sh "$TMP_DIR/e2e_suite" << 'PY'
import os, re, sys

src = open(sys.argv[1], encoding="utf-8").read()
out_dir = sys.argv[2]
pat = re.compile(r'cat > "\$TMP_DIR/([A-Za-z0-9_]+\.gsa)" << \'EOF\'\n(.*?)\nEOF\n((?:[^\n]*\n){1,4})', re.S)

extracted = []
for m in pat.finditer(src):
    name, body, tail = m.group(1), m.group(2), m.group(3)
    tail_lines = [ln.strip() for ln in tail.splitlines() if ln.strip()]
    is_pos = False
    is_nomain = False
    for ln in tail_lines:
        if ln.startswith('if "$GEISHA_BIN"') or ln.startswith('assert_compile_fails'):
            break
        if ln.startswith('"$GEISHA_BIN"'):
            if not ln.startswith('"$GEISHA_BIN" check ') and "--pkg" not in tail and "--src-root" not in tail and " -L " not in tail:
                is_pos = True
                if "--no-main" in tail:
                    is_nomain = True
            break
    if is_pos:
        out_path = os.path.join(out_dir, name)
        with open(out_path, "w", encoding="utf-8") as f:
            f.write(body + "\n")
        extracted.append((name, is_nomain))

if len(extracted) < 20:
    print(f"FAIL: expected >= 20 positive E2E .gsa programs, found {len(extracted)}", file=sys.stderr)
    sys.exit(1)

with open(os.path.join(out_dir, "manifest.txt"), "w", encoding="utf-8") as mf:
    for name, is_nomain in extracted:
        mf.write(f"{name} {'1' if is_nomain else '0'}\n")
PY

E2E_COUNT=0
while read -r gsa_name is_nomain; do
    gsa_path="$TMP_DIR/e2e_suite/$gsa_name"
    gscore_path="$TMP_DIR/e2e_suite/${gsa_name}.gscore"
    ll_path="$TMP_DIR/e2e_suite/${gsa_name}.ll"
    if [ "$is_nomain" = "1" ]; then
        "$GEISHA_BIN" --no-main --dump-core "$gscore_path" -e -o "$ll_path" "$gsa_path"
    else
        "$GEISHA_BIN" --dump-core "$gscore_path" -e -o "$ll_path" "$gsa_path"
    fi
    "$CHECKER_BIN" "$gscore_path" >/dev/null
    E2E_COUNT=$((E2E_COUNT + 1))
done < "$TMP_DIR/e2e_suite/manifest.txt"
echo "PASS [e2e_suite_translation_validation]: all $E2E_COUNT positive E2E language-surface programs verified by Lean 4 geisha-check"

# 11. Full Self-Hosting Compiler Translation Validation:
#     Dump and mechanically verify the entire ~20,000-line self-hosted Geisha compiler (`src/geisha.gsa`)!
"$GEISHA_BIN" build --dump-core "$TMP_DIR/compiler.gscore" -e -o "$TMP_DIR/compiler.ll"
"$CHECKER_BIN" "$TMP_DIR/compiler.gscore"
echo "PASS [self_hosted_compiler_verified]: entire src/geisha.gsa compiler verified by Lean 4 geisha-check"

# 12. Lean 4 VCG Soundness Self-Check + Live Compiler-to-Lean Cross-Verification
"$CHECKER_BIN" --verify-vcg

cat > "$TMP_DIR/vcg_pos.gsa" << 'EOF'
def safeDiv(a: Int, b: Int): Int
    requires b != 0
    = a / b

def maskedShift(x: Int, k: Int): Int =
    x << k

def main(): Void = {
    let _ = safeDiv(10, 2);
    let _ = maskedShift(1, 35);
    ()
}
EOF
"$GEISHA_BIN" verify --dump-core "$TMP_DIR/vcg_pos.gscore" "$TMP_DIR/vcg_pos.gsa" >/dev/null
"$CHECKER_BIN" --verify-vcg "$TMP_DIR/vcg_pos.gscore"

cat > "$TMP_DIR/vcg_neg_float.gsa" << 'EOF'
def cmpFloat(x: Float, y: Float): Bool = x == y
def main(): Void = ()
EOF
"$GEISHA_BIN" verify --dump-core "$TMP_DIR/vcg_neg_float.gscore" "$TMP_DIR/vcg_neg_float.gsa" >/dev/null 2>&1 || true
test -s "$TMP_DIR/vcg_neg_float.gscore"
if "$CHECKER_BIN" --verify-vcg "$TMP_DIR/vcg_neg_float.gscore" 2>/dev/null; then
    echo "FAIL [vcg_cross_neg_float]: Lean VCG accepted unmodeled Float equality!" >&2
    exit 1
fi

cat > "$TMP_DIR/vcg_neg_while.gsa" << 'EOF'
def unannotatedLoop(n: Int): Int = {
    let i = cellNew(0);
    while (cellGet(i) < n) {
        cellSet(i, cellGet(i) + 1)
    };
    cellGet(i)
}
def main(): Void = ()
EOF
"$GEISHA_BIN" verify --dump-core "$TMP_DIR/vcg_neg_while.gscore" "$TMP_DIR/vcg_neg_while.gsa" >/dev/null 2>&1 || true
test -s "$TMP_DIR/vcg_neg_while.gscore"
if "$CHECKER_BIN" --verify-vcg "$TMP_DIR/vcg_neg_while.gscore" 2>/dev/null; then
    echo "FAIL [vcg_cross_neg_while]: Lean VCG accepted unannotated while loop!" >&2
    exit 1
fi

# R2 + R5: Modeled but contract-violating programs (even uncalled by `main`) MUST be rejected by BOTH `geisha verify` AND `geisha-check --verify-vcg`!
cat > "$TMP_DIR/vcg_bad_ens.gsa" << 'EOF'
def badEns(x: Int): Int
    ensures r -> r != 7
= x
def main(): Void = ()
EOF
if "$GEISHA_BIN" verify --dump-core "$TMP_DIR/vcg_bad_ens.gscore" "$TMP_DIR/vcg_bad_ens.gsa" >/dev/null 2>&1; then
    echo "FAIL [vcg_cross_bad_ens_compiler]: geisha verify accepted violated ensures!" >&2
    exit 1
fi
test -s "$TMP_DIR/vcg_bad_ens.gscore"
if "$CHECKER_BIN" --verify-vcg "$TMP_DIR/vcg_bad_ens.gscore" 2>/dev/null; then
    echo "FAIL [vcg_cross_bad_ens_lean]: Lean geisha-check --verify-vcg accepted violated ensures!" >&2
    exit 1
fi

cat > "$TMP_DIR/vcg_div_zero.gsa" << 'EOF'
def divZero(): Int = 1 / 0
def main(): Void = ()
EOF
if "$GEISHA_BIN" verify --dump-core "$TMP_DIR/vcg_div_zero.gscore" "$TMP_DIR/vcg_div_zero.gsa" >/dev/null 2>&1; then
    echo "FAIL [vcg_cross_div_zero_compiler]: geisha verify accepted 1 / 0!" >&2
    exit 1
fi
test -s "$TMP_DIR/vcg_div_zero.gscore"
if "$CHECKER_BIN" --verify-vcg "$TMP_DIR/vcg_div_zero.gscore" 2>/dev/null; then
    echo "FAIL [vcg_cross_div_zero_lean]: Lean geisha-check --verify-vcg accepted 1 / 0!" >&2
    exit 1
fi

cat > "$TMP_DIR/vcg_zero_bad_inv.gsa" << 'EOF'
def zeroBadInv(): Void = {
    while (false)
        invariant false
    { () }
}
def main(): Void = ()
EOF
if "$GEISHA_BIN" verify --dump-core "$TMP_DIR/vcg_zero_bad_inv.gscore" "$TMP_DIR/vcg_zero_bad_inv.gsa" >/dev/null 2>&1; then
    echo "FAIL [vcg_cross_zero_inv_compiler]: geisha verify accepted entry invariant false!" >&2
    exit 1
fi
test -s "$TMP_DIR/vcg_zero_bad_inv.gscore"
if "$CHECKER_BIN" --verify-vcg "$TMP_DIR/vcg_zero_bad_inv.gscore" 2>/dev/null; then
    echo "FAIL [vcg_cross_zero_inv_lean]: Lean geisha-check --verify-vcg accepted entry invariant false!" >&2
    exit 1
fi

# T1: Local Cell<Int> across while loop (havocCells preserves cellTys -> typed sym, no .getD .int)
cat > "$TMP_DIR/vcg_local_cell.gsa" << 'EOF'
def localCellWhile(): Int
    ensures r -> r == r
= {
    let c = cellNew(0);
    while (false)
        invariant true
    { () };
    cellGet(c)
}
def main(): Void = ()
EOF
"$GEISHA_BIN" verify --dump-core "$TMP_DIR/vcg_local_cell.gscore" "$TMP_DIR/vcg_local_cell.gsa" >/dev/null
"$CHECKER_BIN" --verify-vcg "$TMP_DIR/vcg_local_cell.gscore"

# T2: Int64 shift by 32-bit Int count (<< 64) and Int <-> Int64 casts
cat > "$TMP_DIR/vcg_i64_casts.gsa" << 'EOF'
def shift64(x: Int64): Int64
    ensures r -> r == x
= x << 64

def roundtripI64(x: Int): Int64
    ensures r -> i64ToInt(r) == x
= intToI64(x)

def main(): Void = ()
EOF
"$GEISHA_BIN" verify --dump-core "$TMP_DIR/vcg_i64_casts.gscore" "$TMP_DIR/vcg_i64_casts.gsa" >/dev/null
"$CHECKER_BIN" --verify-vcg "$TMP_DIR/vcg_i64_casts.gscore"

# T3: Mutual recursion SCC decreases (positive + non-decreasing negative + missing-decreases negative)
cat > "$TMP_DIR/vcg_mutrec_pos.gsa" << 'EOF'
def isEven(n: Int): Bool
    requires n >= 0
    decreases n
= if (n == 0) { true } else { isOdd(n - 1) }

def isOdd(n: Int): Bool
    requires n >= 0
    decreases n
= if (n == 0) { false } else { isEven(n - 1) }

def main(): Void = ()
EOF
"$GEISHA_BIN" verify --dump-core "$TMP_DIR/vcg_mutrec_pos.gscore" "$TMP_DIR/vcg_mutrec_pos.gsa" >/dev/null
"$CHECKER_BIN" --verify-vcg "$TMP_DIR/vcg_mutrec_pos.gscore"

cat > "$TMP_DIR/vcg_mutrec_nondec.gsa" << 'EOF'
def badEven(n: Int): Bool
    requires n >= 0
    decreases n
= if (n == 0) { true } else { badOdd(n) }

def badOdd(n: Int): Bool
    requires n >= 0
    decreases n
= if (n == 0) { false } else { badEven(n - 1) }

def main(): Void = ()
EOF
if "$GEISHA_BIN" verify --dump-core "$TMP_DIR/vcg_mutrec_nondec.gscore" "$TMP_DIR/vcg_mutrec_nondec.gsa" >/dev/null 2>&1; then
    echo "FAIL [vcg_cross_mutrec_nondec_compiler]: geisha verify accepted non-decreasing mutual recursion!" >&2
    exit 1
fi
test -s "$TMP_DIR/vcg_mutrec_nondec.gscore"
if "$CHECKER_BIN" --verify-vcg "$TMP_DIR/vcg_mutrec_nondec.gscore" 2>/dev/null; then
    echo "FAIL [vcg_cross_mutrec_nondec_lean]: Lean geisha-check --verify-vcg accepted non-decreasing mutual recursion!" >&2
    exit 1
fi

cat > "$TMP_DIR/vcg_mutrec_missing.gsa" << 'EOF'
def missEven(n: Int): Bool
    requires n >= 0
    decreases n
= if (n == 0) { true } else { missOdd(n - 1) }

def missOdd(n: Int): Bool
    requires n >= 0
= if (n == 0) { false } else { missEven(n - 1) }

def main(): Void = ()
EOF
if "$GEISHA_BIN" verify --dump-core "$TMP_DIR/vcg_mutrec_missing.gscore" "$TMP_DIR/vcg_mutrec_missing.gsa" >/dev/null 2>&1; then
    echo "FAIL [vcg_cross_mutrec_missing_compiler]: geisha verify accepted mutual recursion missing decreases!" >&2
    exit 1
fi
test -s "$TMP_DIR/vcg_mutrec_missing.gscore"
if "$CHECKER_BIN" --verify-vcg "$TMP_DIR/vcg_mutrec_missing.gscore" 2>/dev/null; then
    echo "FAIL [vcg_cross_mutrec_missing_lean]: Lean geisha-check --verify-vcg accepted mutual recursion missing decreases!" >&2
    exit 1
fi

# Z6b: Shadowed user `assume` MUST NOT act as built-in path assumption in geisha verify OR Lean geisha-check --verify-vcg
cat > "$TMP_DIR/vcg_shadow_assume.gsa" << 'EOF'
def assume(b: Bool): Void = ()
def observe(x: Int): Int
    ensures r -> r == 1
= { assume(x == 1); x }
def main(): Void = { let _ = observe(7); () }
EOF
if "$GEISHA_BIN" verify --dump-core "$TMP_DIR/vcg_shadow_assume.gscore" "$TMP_DIR/vcg_shadow_assume.gsa" >/dev/null 2>&1; then
    echo "FAIL [vcg_shadow_assume_compiler]: geisha verify accepted bogus ensures via shadowed def assume!" >&2
    exit 1
fi
test -s "$TMP_DIR/vcg_shadow_assume.gscore"
if "$CHECKER_BIN" --verify-vcg "$TMP_DIR/vcg_shadow_assume.gscore" 2>/dev/null; then
    echo "FAIL [vcg_shadow_assume_lean]: Lean geisha-check --verify-vcg accepted bogus ensures via shadowed def assume!" >&2
    exit 1
fi

# Z6b/Z8 direct `.gscore` regressions (must fail in VCG, NEVER in Parser!):
# 1. Versioned `(vcg-format 2)` with bare `(fun "assume" ...)` -> deflected to `$bare$assume`, refuted by Z3
cat > "$TMP_DIR/vcg_bare_shadow_assume.gscore" << 'EOF'
(program
  (vcg-format 2)
  (adts)
  (externs)
  (funs
    (fun "assume" (("b" bool)) void (lit-unit))
    (fun "observe" (("x" int)) int
      (let "__gs_res"
        (block
          (apply-dir "assume" (bin eqInt (var "x") (lit-int 1)))
          (var "x"))
        (block
          (let "r" (var "__gs_res")
            (apply-dir "__gs_ensures" (bin eqInt (var "r") (lit-int 1))))
          (var "__gs_res"))))
    (fun "main" () void (lit-unit))))
EOF
if "$CHECKER_BIN" --verify-vcg "$TMP_DIR/vcg_bare_shadow_assume.gscore" 2>"$TMP_DIR/vcg_err.txt"; then
    echo "FAIL [vcg_bare_shadow_assume_lean]: Lean geisha-check --verify-vcg accepted bare shadowed (fun \"assume\" ...)!" >&2
    exit 1
fi
if ! grep -q "^VCG " "$TMP_DIR/vcg_err.txt"; then
    echo "FAIL [vcg_bare_shadow_assume_err]: expected VCG diagnostic (not PARSE ERROR), got:" >&2
    cat "$TMP_DIR/vcg_err.txt" >&2
    exit 1
fi

# 2. Versioned `(vcg-format 2)` with bare `(extern "assume" (("p0" bool)) void)` -> VCG ERROR (fail-closed)
cat > "$TMP_DIR/vcg_bare_extern_assume_v2.gscore" << 'EOF'
(program
  (vcg-format 2)
  (adts)
  (externs (extern "assume" (("p0" bool)) void))
  (funs
    (fun "observe" (("x" int)) int
      (let "__gs_res"
        (block
          (apply-dir "assume" (bin eqInt (var "x") (lit-int 1)))
          (var "x"))
        (block
          (let "r" (var "__gs_res")
            (apply-dir "__gs_ensures" (bin eqInt (var "r") (lit-int 1))))
          (var "__gs_res"))))
    (fun "main" () void (lit-unit))))
EOF
if "$CHECKER_BIN" --verify-vcg "$TMP_DIR/vcg_bare_extern_assume_v2.gscore" 2>"$TMP_DIR/vcg_err.txt"; then
    echo "FAIL [vcg_bare_extern_assume_v2_lean]: Lean geisha-check --verify-vcg accepted bare (extern \"assume\" ...)!" >&2
    exit 1
fi
if ! grep -q "^VCG ERROR" "$TMP_DIR/vcg_err.txt"; then
    echo "FAIL [vcg_bare_extern_assume_v2_err]: expected '^VCG ERROR' (not PARSE ERROR), got:" >&2
    cat "$TMP_DIR/vcg_err.txt" >&2
    exit 1
fi

# 3. Unversioned legacy `.gscore` with `(extern "__gs_builtin_assume" ...)` (base2-ordinary-extern) -> VCG ERROR
cat > "$TMP_DIR/vcg_legacy_builtin_extern.gscore" << 'EOF'
(program
  (adts)
  (externs (extern "__gs_builtin_assume" (("p0" bool)) void))
  (funs
    (fun "observe" (("x" int)) int
      (let "__gs_res"
        (block
          (apply-dir "__gs_builtin_assume" (bin eqInt (var "x") (lit-int 1)))
          (var "x"))
        (block
          (let "r" (var "__gs_res")
            (apply-dir "__gs_ensures" (bin eqInt (var "r") (lit-int 1))))
          (var "__gs_res"))))
    (fun "main" () void (lit-unit))))
EOF
if "$CHECKER_BIN" --verify-vcg "$TMP_DIR/vcg_legacy_builtin_extern.gscore" 2>"$TMP_DIR/vcg_err.txt"; then
    echo "FAIL [vcg_legacy_builtin_extern_lean]: Lean geisha-check --verify-vcg accepted unversioned legacy __gs_builtin_assume!" >&2
    exit 1
fi
if ! grep -q "^VCG ERROR" "$TMP_DIR/vcg_err.txt"; then
    echo "FAIL [vcg_legacy_builtin_extern_err]: expected '^VCG ERROR' (not PARSE ERROR), got:" >&2
    cat "$TMP_DIR/vcg_err.txt" >&2
    exit 1
fi

# 4. Unversioned legacy `.gscore` with `(extern "assume" ...)` -> VCG ERROR
cat > "$TMP_DIR/vcg_legacy_bare_extern.gscore" << 'EOF'
(program
  (adts)
  (externs (extern "assume" (("p0" bool)) void))
  (funs
    (fun "observe" (("x" int)) int
      (let "__gs_res"
        (block
          (apply-dir "assume" (bin eqInt (var "x") (lit-int 1)))
          (var "x"))
        (block
          (let "r" (var "__gs_res")
            (apply-dir "__gs_ensures" (bin eqInt (var "r") (lit-int 1))))
          (var "__gs_res"))))
    (fun "main" () void (lit-unit))))
EOF
if "$CHECKER_BIN" --verify-vcg "$TMP_DIR/vcg_legacy_bare_extern.gscore" 2>"$TMP_DIR/vcg_err.txt"; then
    echo "FAIL [vcg_legacy_bare_extern_lean]: Lean geisha-check --verify-vcg accepted unversioned legacy extern assume!" >&2
    exit 1
fi
if ! grep -q "^VCG ERROR" "$TMP_DIR/vcg_err.txt"; then
    echo "FAIL [vcg_legacy_bare_extern_err]: expected '^VCG ERROR' (not PARSE ERROR), got:" >&2
    cat "$TMP_DIR/vcg_err.txt" >&2
    exit 1
fi

# D1: Production compiler verified kernels (`src/verified_kernels.gsa`) 100% cross-verified by Z3 and Lean 4 VCG
"$GEISHA_BIN" verify --src-root . --dump-core "$TMP_DIR/verified_kernels.gscore" src/verified_kernels.gsa
"$CHECKER_BIN" --verify-vcg "$TMP_DIR/verified_kernels.gscore"
echo "PASS [vcg_live_cross_verification]: geisha verify --dump-core <-> Lean geisha-check --verify-vcg cross-checked (positive + fail-closed + violated ensures/divZero/entryInv + T1 local cell + T2 Int64 shift/casts + T3 mutual-rec decreases + Z6b shadowed assume + D1 src/verified_kernels.gsa)"
