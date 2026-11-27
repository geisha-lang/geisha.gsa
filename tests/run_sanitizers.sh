#!/bin/sh
# End-to-end Sanitizer Stress Suite (ASan + UBSan & TSan) for Geisha Runtime + Generated LLVM IR
#
# Verifies both `runtime/` C sources AND compiler-emitted LLVM IR (`geisha -e`) under:
# 1. AddressSanitizer + UndefinedBehaviorSanitizer (`-fsanitize=address,undefined`)
#    with aggressive generational GC (`GEISHA_GC_HEAP_WORDS=4096`), ForeignPtr cleanups,
#    ScopedPtr/Arena zero-copy FFI borrows, >4KB large objects, and shadowed Cell write barriers.
# 2. ThreadSanitizer (`-fsanitize=thread`)
#    with concurrent `Task` work-helping, `MVar`, bounded/unbounded `Chan`, `!Send` `Actor`,
#    `parTabulate` pointer-array writes, and high-frequency STW Minor/Major GC collections.
set -eu

CC="${CC:-clang}"
GEISHA_BIN="${GEISHA_BIN:-./build/geisha2}"

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

TMP_DIR="$(mktemp -d "${TMPDIR:-/tmp}/geisha_sanitizers.XXXXXX")"
trap 'rm -rf "$TMP_DIR"' EXIT

COMMON_CFLAGS="$HOST_CC_TARGET -O1 -g -fno-omit-frame-pointer -Wall -Wextra"
RT_CFLAGS="$COMMON_CFLAGS -Iruntime/include"
ASAN_FLAGS="-fsanitize=address,undefined -fsanitize-address-use-after-return=never -fno-sanitize-recover=all"
TSAN_FLAGS="-fsanitize=thread -fno-sanitize-recover=all"

echo "[1/4] Building runtime with ASan + UBSan..."
for src in runtime/base.c runtime/gs_sys.c runtime/runtime/gc_bitmap.c runtime/runtime/gs_conc.c; do
    obj="$TMP_DIR/asan_$(basename "$src" .c).o"
    "$CC" $RT_CFLAGS $ASAN_FLAGS -c "$src" -o "$obj"
done
ar rcs "$TMP_DIR/libgeisha_rt_asan.a" "$TMP_DIR"/asan_*.o

echo "[2/4] Building runtime with TSan..."
for src in runtime/base.c runtime/gs_sys.c runtime/runtime/gc_bitmap.c runtime/runtime/gs_conc.c; do
    obj="$TMP_DIR/tsan_$(basename "$src" .c).o"
    "$CC" $RT_CFLAGS $TSAN_FLAGS -c "$src" -o "$obj"
done
ar rcs "$TMP_DIR/libgeisha_rt_tsan.a" "$TMP_DIR"/tsan_*.o

cat > "$TMP_DIR/ffi_helper.c" << 'EOF'
#include <stdint.h>
int32_t san_sum_i32(const int32_t *buf, int32_t n) {
    int32_t acc = 0;
    for (int32_t i = 0; i < n; i++) {
        acc += buf[i];
    }
    return acc;
}
EOF
"$CC" $RT_CFLAGS $ASAN_FLAGS -c "$TMP_DIR/ffi_helper.c" -o "$TMP_DIR/asan_ffi_helper.o"

# Workload A: Heap + Generational Write Barrier + Large Object + ForeignPtr + Arena + ADT/Closure GC Stress
cat > "$TMP_DIR/san_heap_stress.gsa" << 'EOF'
use std.option.{Option, Some, None}
use std.str.intToStr

extern "gc_collect_major" def gcCollectMajor(): Void
extern "gc_trim" def gcTrim(): Void
extern "gc_set_mem_limit" def gcSetMemLimit(bytes: Int64): Void
extern noalloc "san_sum_i32" def c_sum_i32(p: ScopedPtr, n: Int): Int

data Tree {
    Leaf(String),
    Branch(Int, Tree, Tree),
}

def buildTree(depth: Int, tag: Int): Tree =
    if (depth <= 0) Leaf("L:" + intToStr(tag))
    else Branch(tag, buildTree(depth - 1, tag * 2), buildTree(depth - 1, tag * 2 + 1))

def treeLen(t: Tree): Int = match t {
    Leaf(s) -> strLen(s),
    Branch(_, l, r) -> treeLen(l) + treeLen(r),
}

def mutateOldAndShadow(box: Cell Tree, round: Int): Int = {
    cellSet(box, buildTree(4, round));
    let box = cellNew(round * 2);
    cellSet(box, cellGet(box) + 1);
    cellGet(box)
}

def ffiAndArenaRound(seed: Int): Int = {
    let fp = foreignPtrAlloc(intToI64(64));
    withForeignPtr(fp, (p) -> {
        let i = cellNew(0);
        while (cellGet(i) < 16) {
            let k = cellGet(i);
            scopedPtrWriteI32Le(p, k * 4, (seed + k) & 127);
            cellSet(i, k + 1)
        }
    });
    let s1 = c_sum_i32(fp, 16);
    let s2 = withArena((a) -> {
        let buf = arenaAlloc(a, intToI64(128));
        let j = cellNew(0);
        while (cellGet(j) < 16) {
            let k = cellGet(j);
            scopedPtrWriteI32Le(buf, k * 4, 2);
            cellSet(j, k + 1)
        };
        c_sum_i32(buf, 16)
    });
    s1 + s2
}

def main(): Void = {
    gcSetMemLimit(intToI64(12 * 1024 * 1024));
    let oldCell = cellNew(buildTree(3, 1));
    let stackTreeCell = cellNew(Leaf("stack-root"));
    let largeArr = arrayNew(1500, Some("init"));
    gcCollectMajor();

    let acc = cellNew(0);
    let r = cellNew(0);
    while (cellGet(r) < 120) {
        let k = cellGet(r);
        let v1 = mutateOldAndShadow(oldCell, k) + mutateOldAndShadow(stackTreeCell, k + 3);
        arraySet(largeArr, (k * 13) % 1500, Some("item-" + intToStr(k)));
        let v2 = ffiAndArenaRound(k);
        cellSet(acc, cellGet(acc) + v1 + v2);
        if (k % 40 == 39) gcTrim() else ();
        cellSet(r, k + 1)
    };

    let tailStr = match arrayGet(largeArr, (119 * 13) % 1500) {
        Some(s) -> s,
        None -> "none",
    };
    let ok = treeLen(cellGet(oldCell)) > 40 && tailStr == "item-119" && cellGet(acc) > 10000;
    printLn(if (ok) "ASAN_HEAP_OK" else "ASAN_HEAP_BAD")
}
EOF

# Workload B: Multicore Concurrency + Generational Write Barrier + STW Safepoint Stress
cat > "$TMP_DIR/san_conc_stress.gsa" << 'EOF'
use std.option.{Option, Some, None}
use std.task.{Task, spawn, await, par}
use std.sync.{MVar, mvarEmpty, mvarPut, mvarTake, Chan, chanNew, chanSend, chanRecv, chanClose}
use std.actor.{Actor, actorSpawn, actorSend, actorCall, actorStop}
use std.str.intToStr

extern "gc_collect_major" def gcCollectMajor(): Void

data Packet {
    MkPacket(Int, String),
}

def workerLoop(id: Int, rounds: Int, ch: Chan Packet, act: Actor (Cell (List String))): Int = {
    let localHold = cellNew("seed-" + intToStr(id));
    let sum = cellNew(0);
    let i = cellNew(0);
    while (cellGet(i) < rounds) {
        let k = cellGet(i);
        let tag = intToStr(id) + ":" + intToStr(k);
        cellSet(localHold, tag);
        let _ = chanSend(ch, MkPacket(k + 1, tag));
        if (k % 8 == 0) {
            actorSend(act, (st) -> cellSet(st, Cons(tag, cellGet(st))))
        } else ();
        cellSet(sum, cellGet(sum) + strLen(cellGet(localHold)));
        cellSet(i, k + 1)
    };
    cellGet(sum)
}

def main(): Void = {
    let oldArr = arrayNew(1024, "old");
    gcCollectMajor();

    let ch: Chan Packet = chanNew(16);
    let mv: MVar Int = mvarEmpty();
    let act: Actor (Cell (List String)) = actorSpawn(() -> cellNew(Nil));

    // Spawn 4 producer tasks + 1 consumer task while main runs parTabulate & mutates oldArr
    let t0 = spawn(() -> workerLoop(0, 80, ch, act));
    let t1 = spawn(() -> workerLoop(1, 80, ch, act));
    let t2 = spawn(() -> workerLoop(2, 80, ch, act));
    let t3 = spawn(() -> workerLoop(3, 80, ch, act));

    let consumer = spawn(() -> {
        let total = cellNew(0);
        let seen = cellNew(0);
        while (cellGet(seen) < 320) {
            match chanRecv(ch) {
                Some(MkPacket(v, s)) -> {
                    cellSet(total, cellGet(total) + v + strLen(s));
                    cellSet(seen, cellGet(seen) + 1)
                },
                None -> cellSet(seen, 320),
            }
        };
        mvarPut(mv, cellGet(total));
        cellGet(total)
    });

    // Concurrently run parTabulate allocating heap Strings across worker threads
    // AND mutate Old-generation `oldArr` triggering sticky write barriers!
    let round = cellNew(0);
    let tabSum = cellNew(0);
    while (cellGet(round) < 6) {
        let r = cellGet(round);
        arraySet(oldArr, r * 100, "mut-" + intToStr(r));
        let arr = parTabulate(128, (idx) -> "elem-" + intToStr(r) + "-" + intToStr(idx));
        cellSet(tabSum, cellGet(tabSum) + immArrayLen(arr) + strLen(immArrayGet(arr, 127)));
        cellSet(round, r + 1)
    };

    let (pL, pR) = par(
        () -> await(t0) + await(t1),
        () -> await(t2) + await(t3)
    );
    chanClose(ch);
    let closedNone = match chanRecv(ch) { Some(_) -> false, None -> true };
    let consVal = await(consumer);
    let mvVal = mvarTake(mv);
    let actCount = await(actorCall(act, (st) -> {
        let n = cellNew(0);
        let cur = cellNew(cellGet(st));
        while (match cellGet(cur) { Nil -> false, _ -> true }) {
            match cellGet(cur) {
                Cons(_, rest) -> {
                    cellSet(n, cellGet(n) + 1);
                    cellSet(cur, rest)
                },
                Nil -> (),
            }
        };
        cellGet(n)
    }));
    actorStop(act);

    let ok = closedNone && pL > 0 && pR > 0 && consVal == mvVal && consVal > 10000
             && actCount == 40 && cellGet(tabSum) > 768
             && arrayGet(oldArr, 500) == "mut-5";
    printLn(if (ok) "CONC_SAN_OK" else "CONC_SAN_BAD")
}
EOF

"$GEISHA_BIN" -e -o "$TMP_DIR/san_heap_stress.ll" "$TMP_DIR/san_heap_stress.gsa"
"$GEISHA_BIN" -e -o "$TMP_DIR/san_conc_stress.ll" "$TMP_DIR/san_conc_stress.gsa"

echo "[3/4] Compiling & running ASan + UBSan stress suite (heap + FFI + concurrency)..."
"$CC" $COMMON_CFLAGS $ASAN_FLAGS -Wno-override-module -pthread \
    -x ir "$TMP_DIR/san_heap_stress.ll" \
    -x none "$TMP_DIR/asan_ffi_helper.o" "$TMP_DIR/libgeisha_rt_asan.a" $HOST_CC_LIBS \
    -o "$TMP_DIR/san_heap_asan"

"$CC" $COMMON_CFLAGS $ASAN_FLAGS -Wno-override-module -pthread \
    -x ir "$TMP_DIR/san_conc_stress.ll" \
    -x none "$TMP_DIR/libgeisha_rt_asan.a" $HOST_CC_LIBS \
    -o "$TMP_DIR/san_conc_asan"

ASAN_ENV="detect_stack_use_after_return=0:detect_leaks=0:halt_on_error=1"
UBSAN_ENV="print_stacktrace=1:halt_on_error=1"

OUT_A1="$(ASAN_OPTIONS="$ASAN_ENV" UBSAN_OPTIONS="$UBSAN_ENV" GEISHA_GC_HEAP_WORDS=4096 "$TMP_DIR/san_heap_asan")"
if [ "$OUT_A1" != "ASAN_HEAP_OK" ]; then
    echo "FAIL [asan_heap_stress]: expected ASAN_HEAP_OK, got '$OUT_A1'" >&2
    exit 1
fi
echo "PASS [asan_ubsan_heap_stress]: $OUT_A1"

OUT_A2="$(ASAN_OPTIONS="$ASAN_ENV" UBSAN_OPTIONS="$UBSAN_ENV" GEISHA_GC_HEAP_WORDS=4096 GEISHA_THREADS=4 "$TMP_DIR/san_conc_asan")"
if [ "$OUT_A2" != "CONC_SAN_OK" ]; then
    echo "FAIL [asan_conc_stress]: expected CONC_SAN_OK, got '$OUT_A2'" >&2
    exit 1
fi
echo "PASS [asan_ubsan_conc_stress]: $OUT_A2"

echo "[4/4] Compiling & running TSan concurrency + generational GC stress suite..."
"$CC" $COMMON_CFLAGS $TSAN_FLAGS -Wno-override-module -pthread \
    -x ir "$TMP_DIR/san_conc_stress.ll" \
    -x none "$TMP_DIR/libgeisha_rt_tsan.a" $HOST_CC_LIBS \
    -o "$TMP_DIR/san_conc_tsan"

TSAN_ENV="halt_on_error=1:second_deadlock_stack=1"
OUT_T1="$(TSAN_OPTIONS="$TSAN_ENV" GEISHA_GC_HEAP_WORDS=4096 GEISHA_THREADS=4 "$TMP_DIR/san_conc_tsan")"
if [ "$OUT_T1" != "CONC_SAN_OK" ]; then
    echo "FAIL [tsan_conc_stress]: expected CONC_SAN_OK, got '$OUT_T1'" >&2
    exit 1
fi
echo "PASS [tsan_conc_gc_stress]: $OUT_T1"

echo "All ASan + UBSan + TSan runtime & LLVM IR stress checks passed with zero diagnostics!"
