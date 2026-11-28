#!/usr/bin/env python3
"""End-to-end & adversarial test suite for Geisha contracts (M1) and SMT static verifier (M2)."""

from __future__ import annotations

import json
import os
import shutil
import subprocess
import sys
import tempfile
from pathlib import Path


def run(cmd: list[str], env: dict[str, str] | None = None) -> subprocess.CompletedProcess[str]:
    return subprocess.run(cmd, capture_output=True, text=True, env=env)


def main() -> int:
    if len(sys.argv) < 2:
        print("usage: test_verify.py <geisha-bin>", file=sys.stderr)
        return 2
    geisha = sys.argv[1]
    runtime = os.environ.get("GEISHA_RUNTIME", "./build/libgeisha_runtime.a")
    repo_root = Path(__file__).resolve().parent.parent

    with tempfile.TemporaryDirectory(prefix="geisha_verify_test_") as td:
        tmp = Path(td)

        # ------------------------------------------------------------------
        # 1. M1: Direct & transitive purity checking
        # ------------------------------------------------------------------
        impure_direct = tmp / "impure_direct.gsa"
        impure_direct.write_text(
            "def bad(x: Int): Int\n"
            "    requires { printLn(\"side effect\"); x > 0 }\n"
            "= x\n"
            "def main() = ()\n",
            encoding="utf-8",
        )
        r = run([geisha, "check", str(impure_direct)])
        assert r.returncode != 0 and "Purity error" in r.stderr, f"expected direct purity error:\n{r.stderr}"

        impure_trans = tmp / "impure_trans.gsa"
        impure_trans.write_text(
            "def bump(c: Cell Int): Bool = { cellSet(c, cellGet(c) + 1); true }\n"
            "def bad(c: Cell Int): Int\n"
            "    requires bump(c)\n"
            "= cellGet(c)\n"
            "def main() = ()\n",
            encoding="utf-8",
        )
        r = run([geisha, "check", str(impure_trans)])
        assert r.returncode != 0 and "Purity error" in r.stderr, f"expected transitive purity error:\n{r.stderr}"

        impure_extern = tmp / "impure_extern.gsa"
        impure_extern.write_text(
            "extern \"gs_sys_getpid\" def c_pid(): Int\n"
            "def bad(x: Int): Int\n"
            "    requires c_pid() > 0\n"
            "= x\n"
            "def main() = ()\n",
            encoding="utf-8",
        )
        r = run([geisha, "check", str(impure_extern)])
        assert r.returncode != 0 and "Purity error" in r.stderr, f"expected extern purity error:\n{r.stderr}"

        impure_concept = tmp / "impure_concept.gsa"
        impure_concept.write_text(
            "concept Sneaky a { sneak: a -> Bool }\n"
            "instance Sneaky (Cell Int) {\n"
            "    def sneak(c: Cell Int): Bool = { cellSet(c, cellGet(c) + 1); true }\n"
            "}\n"
            "def f(c: Cell Int): Int\n"
            "    requires sneak(c)\n"
            "= cellGet(c)\n"
            "def main() = ()\n",
            encoding="utf-8",
        )
        r = run([geisha, "check", str(impure_concept)])
        assert r.returncode != 0 and "Purity error" in r.stderr, f"expected concept instance purity error:\n{r.stderr}"
        print("PASS [contracts_purity_direct_transitive_extern_concept]")

        # ------------------------------------------------------------------
        # 2. M1: Type checking & internal __gs_* symbols are NOT exposed to user code
        # ------------------------------------------------------------------
        bad_ty = tmp / "bad_ty.gsa"
        bad_ty.write_text(
            "def bad(x: Int): Int\n"
            "    requires x + 1\n"
            "= x\n"
            "def main() = ()\n",
            encoding="utf-8",
        )
        r = run([geisha, "check", str(bad_ty)])
        assert r.returncode != 0, "expected type error on non-Bool requires"

        bad_internal = tmp / "bad_internal.gsa"
        bad_internal.write_text(
            "def main() = __gs_contract_fail(\"nope\")\n",
            encoding="utf-8",
        )
        r = run([geisha, "check", str(bad_internal)])
        assert r.returncode != 0, "user code must not be able to call internal __gs_contract_fail"
        print("PASS [contracts_typecheck_and_no_internal_leak]")

        # ------------------------------------------------------------------
        # 3. M1: --contracts=erase vs --contracts=check, `?` early return, while clause order, strict decreases, instance & extern contracts
        # ------------------------------------------------------------------
        rt_try = tmp / "rt_try_ensures.gsa"
        rt_try.write_text(
            "use std.result.{Result, Ok, Err}\n"
            "def failOnZero(x: Int): Result Int String = if (x == 0) Err(\"zero\") else Ok(x)\n"
            "def wrap(x: Int): Result Int String\n"
            "    ensures r -> match r { Ok(_) -> true, Err(_) -> false }\n"
            "= {\n"
            "    let v = failOnZero(x)?;\n"
            "    Ok(v + 1)\n"
            "}\n"
            "def main() = match wrap(0) { Ok(_) -> printLn(\"ok\"), Err(_) -> printLn(\"err\") }\n",
            encoding="utf-8",
        )
        bin_try_chk = tmp / "rt_try_chk"
        r = run([geisha, "--contracts=check", "--runtime", runtime, "-o", str(bin_try_chk), str(rt_try)])
        assert r.returncode == 0, f"rt_try build failed: {r.stderr}"
        r = run([str(bin_try_chk)])
        assert r.returncode != 0 and "Contract error: ensures violated" in r.stderr, f"`?` early return must trigger ensures check:\n{r.stderr}"

        # While with `decreases` before `invariant` + runtime strict decrease failure
        rt_while_dec = tmp / "rt_while_dec.gsa"
        rt_while_dec.write_text(
            "def stuck(n: Int): Void = {\n"
            "    let i = cellNew(0);\n"
            "    while (cellGet(i) < n)\n"
            "        decreases n - cellGet(i)\n"
            "        invariant cellGet(i) >= 0\n"
            "    {\n"
            "        ()\n"
            "    }\n"
            "}\n"
            "def main() = stuck(1)\n",
            encoding="utf-8",
        )
        bin_wd = tmp / "rt_while_dec"
        r = run([geisha, "--contracts=check", "--runtime", runtime, "-o", str(bin_wd), str(rt_while_dec)])
        assert r.returncode == 0, f"rt_while_dec build failed: {r.stderr}"
        r = run([str(bin_wd)])
        assert r.returncode != 0 and "Contract error: decreases violated" in r.stderr, f"non-decreasing loop must fail under --contracts=check:\n{r.stderr}"

        # Instance method & extern export contracts parse and check
        inst_ext = tmp / "inst_ext.gsa"
        inst_ext.write_text(
            "concept Pos a { pos: a -> Int }\n"
            "instance Pos Int {\n"
            "    def pos(x: Int): Int\n"
            "        requires x >= 0\n"
            "        ensures r -> r >= 0\n"
            "    = x\n"
            "}\n"
            "pub extern \"my_pos_inc\" def posInc(x: Int): Int\n"
            "    requires x >= 0\n"
            "    requires x < 100\n"
            "    ensures r -> r > x\n"
            "= x + 1\n"
            "def main() = ()\n",
            encoding="utf-8",
        )
        r = run([geisha, "check", str(inst_ext)])
        assert r.returncode == 0, f"instance/extern contracts check failed:\n{r.stderr}"

        # geisha run script cache must NOT leak erase binary into --contracts=check
        rt_fail = tmp / "rt_fail.gsa"
        rt_fail.write_text(
            "use std.str.intToStr\n"
            "def onlyPos(x: Int): Int\n"
            "    requires x > 0\n"
            "= x + 1\n"
            "def main() = printLn(intToStr(onlyPos(-5)))\n",
            encoding="utf-8",
        )
        r_e = run([geisha, "run", "--runtime", runtime, str(rt_fail)])
        assert r_e.returncode == 0 and r_e.stdout.strip() == "-4", f"geisha run erase failed: {r_e.stdout} {r_e.stderr}"
        r_c = run([geisha, "run", "--contracts=check", "--runtime", runtime, str(rt_fail)])
        assert r_c.returncode != 0 and "Contract error: requires violated" in r_c.stderr, f"geisha run --contracts=check leaked erase cache:\n{r_c.stdout}\n{r_c.stderr}"

        # Project-mode `geisha.toml` whole-project cache must NOT leak erase binary into --contracts=check
        proj_dir = tmp / "proj_cache_test"
        (proj_dir / "src").mkdir(parents=True)
        (proj_dir / "geisha.toml").write_text('name = "proj_cache_test"\nversion = "0.1.0"\n', encoding="utf-8")
        (proj_dir / "src" / "main.gsa").write_text(
            "use std.str.intToStr\n"
            "def onlyPos(x: Int): Int\n"
            "    requires x > 0\n"
            "= x + 1\n"
            "def main() = printLn(intToStr(onlyPos(-5)))\n",
            encoding="utf-8",
        )
        geisha_abs = str(Path(geisha).resolve())
        runtime_abs = str(Path(runtime).resolve())
        r_pe = subprocess.run([geisha_abs, "run", "--runtime", runtime_abs], cwd=proj_dir, capture_output=True, text=True)
        assert r_pe.returncode == 0 and r_pe.stdout.strip() == "-4", f"project geisha run erase failed:\n{r_pe.stdout}\n{r_pe.stderr}"
        r_pc = subprocess.run([geisha_abs, "run", "--contracts=check", "--runtime", runtime_abs], cwd=proj_dir, capture_output=True, text=True)
        assert r_pc.returncode != 0 and "Contract error: requires violated" in r_pc.stderr, f"project geisha run --contracts=check leaked whole-project erase cache:\n{r_pc.stdout}\n{r_pc.stderr}"

        # --contracts=check with --dump-core and --target js
        core_out = tmp / "rt_fail.gscore"
        r_dc = run([geisha, "--contracts=check", "--dump-core", str(core_out), "-e", "-o", str(tmp / "rt_fail.ll"), str(rt_fail)])
        assert r_dc.returncode == 0 and core_out.exists(), f"--contracts=check --dump-core failed:\n{r_dc.stderr}"
        js_out = tmp / "rt_fail.mjs"
        r_js = run([geisha, "--contracts=check", "--target", "js", "--no-dts", "-o", str(js_out), str(rt_fail)])
        assert r_js.returncode == 0 and "Contract error:" in js_out.read_text(encoding="utf-8"), f"--contracts=check --target js failed:\n{r_js.stderr}"

        # geisha fmt preserves 4-space contract indent & `ensures |r|` idempotently
        fmt_src = tmp / "fmt_contracts.gsa"
        fmt_src.write_text(
            "pub def clampNonNeg(x: Int): Int\n"
            "    requires x > -100\n"
            "    ensures |r| r >= 0\n"
            "= if (x < 0) 0 else x\n",
            encoding="utf-8",
            newline="\n",
        )
        r_fmt = run([geisha, "fmt", "--stdout", str(fmt_src)])
        assert r_fmt.returncode == 0, f"fmt failed: {r_fmt.stderr}"
        assert "    requires x > -100\n    ensures |r| r >= 0\n" in r_fmt.stdout, f"fmt mangled contracts:\n{r_fmt.stdout}"
        r_fmt_chk = run([geisha, "fmt", "--check", str(fmt_src)])
        assert r_fmt_chk.returncode == 0, f"fmt not idempotent on contracts:\n{r_fmt.stdout}"

        # geisha doc displays contracts
        r_doc = run([geisha, "doc", str(fmt_src)])
        assert r_doc.returncode == 0 and "requires x > -100" in r_doc.stdout and "ensures |r| r >= 0" in r_doc.stdout, f"geisha doc missing contracts:\n{r_doc.stdout}"
        print("PASS [contracts_runtime_try_while_cache_dump_js_fmt_doc]")

        # ------------------------------------------------------------------
        # 4. M2: SMT Verification (`geisha verify`) via Z3
        # ------------------------------------------------------------------
        z3_bin = shutil.which("z3")
        if not z3_bin:
            print("SKIP [smt_verify]: z3 not installed in PATH")
            return 0

        # 4a. Proved suite (overflow-safe under BitVec32!)
        ok_verify = tmp / "ok_verify.gsa"
        ok_verify.write_text(
            "def safeDiv(a: Int, b: Int): Int\n"
            "    requires b != 0\n"
            "= a / b\n"
            "\n"
            "def clampNonNeg(x: Int): Int\n"
            "    ensures |r| r >= 0\n"
            "= if (x < 0) 0 else x\n"
            "\n"
            "def callModular(x: Int): Int\n"
            "    ensures r -> r >= 0\n"
            "= {\n"
            "    let y = clampNonNeg(x);\n"
            "    assert(y >= 0);\n"
            "    let _ = safeDiv(y, 2);\n"
            "    y\n"
            "}\n"
            "\n"
            "def fillArray(arr: MutArray Int): Void = {\n"
            "    let n = arrayLen(arr);\n"
            "    let i = cellNew(0);\n"
            "    while (cellGet(i) < n)\n"
            "        invariant 0 <= cellGet(i) && cellGet(i) <= n\n"
            "        decreases n - cellGet(i)\n"
            "    {\n"
            "        arraySet(arr, cellGet(i), 1);\n"
            "        cellSet(i, cellGet(i) + 1)\n"
            "    }\n"
            "}\n"
            "\n"
            "def countDown(n: Int): Int\n"
            "    requires n >= 0\n"
            "    decreases n\n"
            "    ensures r -> r == 0\n"
            "= if (n == 0) 0 else countDown(n - 1)\n"
            "\n"
            "def main() = ()\n",
            encoding="utf-8",
        )
        r = run([geisha, "verify", "--solver", z3_bin, str(ok_verify)])
        assert r.returncode == 0 and "VERIFIED:" in r.stdout, f"expected VERIFIED:\n{r.stdout}\n{r.stderr}"
        r_json = run([geisha, "verify", "--json", "--solver", z3_bin, str(ok_verify)])
        assert r_json.returncode == 0
        payload = json.loads(r_json.stdout)
        assert payload["ok"] is True and payload["failed"] == 0 and payload["unknown"] == 0 and payload["proved"] >= 10, f"unexpected json: {payload}"
        print(f"PASS [smt_verify_proved]: {payload['proved']} obligations proved across {payload['functions']} functions")

        # 4a-bis. ADT & match precision suite (5a: branch let facts, 5b: tag range + repeated match + Option Bool, 5c: custom data)
        adt_verify = tmp / "adt_verify.gsa"
        adt_verify.write_text(
            "use std.option.{Option, Some, None}\n"
            "data Pair { MkPair(Int, Int) }\n"
            "\n"
            "def matchLetBranch(x: Int): Int\n"
            "    ensures r -> r == 11\n"
            "= match Some(x) {\n"
            "    Some(_) -> { let y = 10 + 1; y },\n"
            "    None -> 11,\n"
            "}\n"
            "\n"
            "def matchTagRangeAndRepeat(x: Option Int): Void = {\n"
            "    let a = match x { Some(_) -> 1, None -> 0 };\n"
            "    let b = match x { None -> 0, Some(_) -> 1 };\n"
            "    assert(a == b);\n"
            "    match x {\n"
            "        Some(u) -> match x {\n"
            "            Some(v) -> assert(u == v),\n"
            "            None -> (),\n"
            "        },\n"
            "        None -> (),\n"
            "    }\n"
            "}\n"
            "\n"
            "def matchOptionBool(ob: Option Bool): Int\n"
            "    ensures r -> r == 1\n"
            "= match ob {\n"
            "    Some(b) -> if (b) 1 else 1,\n"
            "    None -> 1,\n"
            "}\n"
            "\n"
            "def customDataPair(): Void = {\n"
            "    let p = MkPair(3, 4);\n"
            "    let s = match p { MkPair(a, b) -> a + b };\n"
            "    assert(s == 7)\n"
            "}\n"
            "\n"
            "def main() = ()\n",
            encoding="utf-8",
        )
        r_adt = run([geisha, "verify", "--solver", z3_bin, str(adt_verify)])
        assert r_adt.returncode == 0 and "VERIFIED:" in r_adt.stdout, f"ADT/match precision suite failed:\n{r_adt.stdout}\n{r_adt.stderr}"
        print("PASS [smt_verify_adt_match_precision]")

        # 4b. Adversarial soundness suite (all MUST fail or return unknown, NEVER vacuous VERIFIED!)
        adversarial_cases = [
            (
                "p0_1_match_ensures_false",
                "use std.option.{Option, Some, None}\n"
                "def f(x: Int): Option Int\n"
                "    ensures |res| match res { Some(_) -> false, None -> false }\n"
                "= Some(x)\n"
                "def main() = ()\n",
            ),
            (
                "p0_1_match_subexpr_assert_div0",
                "use std.option.{Option, Some, None}\n"
                "def f(x: Option Int): Int = match x { Some(v) -> { assert(false); v / 0 }, None -> 1 / 0 }\n"
                "def main() = ()\n",
            ),
            (
                "p0_1_float_assert_no_vacuous_pass",
                "def f(): Void = assert(1.0 == 2.0)\n"
                "def main() = ()\n",
            ),
            (
                "p0_1_contract_wf_div0",
                "def f(x: Int): Int\n"
                "    requires 1 / 0 == 0\n"
                "= x\n"
                "def main() = ()\n",
            ),
            (
                "p0_2_i32_overflow",
                "def brokenOverflow(x: Int): Int\n"
                "    requires x > 0\n"
                "    ensures r -> r > 0\n"
                "= x + 1\n"
                "def main() = ()\n",
            ),
            (
                "p0_2_truncating_rem_neg_index",
                "def badModIdx(arr: ImmArray Int, x: Int): Int\n"
                "    requires immArrayLen(arr) == 4\n"
                "= immArrayGet(arr, x % 4)\n"
                "def main() = ()\n",
            ),
            (
                "p0_3_if_mutarray_merge",
                "def f(): Void = {\n"
                "    let a = arrayNew(2, 0);\n"
                "    if (true) arraySet(a, 0, 42) else arraySet(a, 0, 42);\n"
                "    assert(arrayGet(a, 0) == 0)\n"
                "}\n"
                "def main() = ()\n",
            ),
            (
                "p0_3_while_mutarray_havoc",
                "def f(): Void = {\n"
                "    let a = arrayNew(2, 0);\n"
                "    let i = cellNew(0);\n"
                "    while (cellGet(i) < 1)\n"
                "        invariant 0 <= cellGet(i) && cellGet(i) <= 1\n"
                "    {\n"
                "        arraySet(a, 0, 99);\n"
                "        cellSet(i, cellGet(i) + 1)\n"
                "    };\n"
                "    assert(arrayGet(a, 0) == 0)\n"
                "}\n"
                "def main() = ()\n",
            ),
            (
                "p0_4_cell_param_precond",
                "def needPosCell(c: Cell Int): Int\n"
                "    requires cellGet(c) >= 0\n"
                "= cellGet(c)\n"
                "def caller(): Int = {\n"
                "    let c = cellNew(-5);\n"
                "    needPosCell(c)\n"
                "}\n"
                "def main() = ()\n",
            ),
            (
                "p0_4_cell_callee_mutation_havoc",
                "def bump(c: Cell Int): Void = cellSet(c, cellGet(c) + 1)\n"
                "def caller(): Void = {\n"
                "    let c = cellNew(0);\n"
                "    bump(c);\n"
                "    assert(cellGet(c) == 0)\n"
                "}\n"
                "def main() = ()\n",
            ),
            (
                "p0_4_shadowed_cell_binding",
                "def f(): Void = {\n"
                "    let x = cellNew(10);\n"
                "    { let x = cellNew(99); cellSet(x, 100) };\n"
                "    assert(cellGet(x) == 100)\n"
                "}\n"
                "def main() = ()\n",
            ),
            (
                "p0_4_aliased_cell_mutation",
                "def f(): Void = {\n"
                "    let c1 = cellNew(0);\n"
                "    let c2 = c1;\n"
                "    cellSet(c2, 42);\n"
                "    assert(cellGet(c1) == 0)\n"
                "}\n"
                "def main() = ()\n",
            ),
            (
                "p0_5_mutual_recursion_decreases",
                "def ping(n: Int): Int\n"
                "    requires n >= 0\n"
                "    decreases n\n"
                "= pong(n)\n"
                "def pong(n: Int): Int = ping(n)\n"
                "def main() = ()\n",
            ),
            (
                "p1_3_uninstantiated_poly_fn",
                "pub def badPoly(xs: ImmArray a, i: Int): a = immArrayGet(xs, i)\n"
                "def main() = ()\n",
            ),
            (
                "r2_p0_mut_param_aliasing",
                "def overwriteSecond(a: Cell Int, b: Cell Int): Void\n"
                "    ensures cellGet(a) == 10\n"
                "= {\n"
                "    cellSet(a, 10);\n"
                "    cellSet(b, 99)\n"
                "}\n"
                "def callerExploit(): Void = {\n"
                "    let c = cellNew(0);\n"
                "    overwriteSecond(c, c);\n"
                "    assert(cellGet(c) == 10)\n"
                "}\n"
                "def main() = ()\n",
            ),
            (
                "r2_p0_instance_method_verified",
                "concept Bad a { bad: a -> Int }\n"
                "instance Bad Int {\n"
                "    def bad(x: Int): Int\n"
                "        ensures r -> false\n"
                "    = x / 0\n"
                "}\n"
                "def main() = { let _ = bad(5); () }\n",
            ),
            (
                "s1_bad_shift32_unmasked",
                "def badShift32(x: Int): Int\n"
                "    requires x == 32\n"
                "    ensures r -> r == 0\n"
                "= 1 << x\n"
                "def main() = ()\n",
            ),
            (
                "s1_bad_shift64_unmasked",
                "def badShift64(x: Int): Int64\n"
                "    requires x == 64\n"
                "    ensures r -> r == intToI64(0)\n"
                "= intToI64(1) << x\n"
                "def main() = ()\n",
            ),
            (
                "s2_short_circuit_and_no_side_effect",
                "def f(): Void = {\n"
                "    let c = cellNew(0);\n"
                "    let _ = false && { cellSet(c, 42); true };\n"
                "    assert(cellGet(c) == 42)\n"
                "}\n"
                "def main() = ()\n",
            ),
            (
                "s2_short_circuit_or_no_side_effect",
                "def f(): Void = {\n"
                "    let c = cellNew(0);\n"
                "    let _ = true || { cellSet(c, 42); false };\n"
                "    assert(cellGet(c) == 42)\n"
                "}\n"
                "def main() = ()\n",
            ),
            (
                "s3_float_nan_eq_unmodeled",
                "def nanEq(x: Float): Bool\n"
                "    ensures r -> r\n"
                "= x == x\n"
                "def main() = ()\n",
            ),
            (
                "s4_while_let_alias_cell_mutation",
                "def f(): Void = {\n"
                "    let c = cellNew(0);\n"
                "    let i = cellNew(0);\n"
                "    while (cellGet(i) < 1)\n"
                "        invariant 0 <= cellGet(i) && cellGet(i) <= 1\n"
                "    {\n"
                "        let alias = c;\n"
                "        cellSet(alias, 99);\n"
                "        cellSet(i, cellGet(i) + 1)\n"
                "    };\n"
                "    assert(cellGet(c) == 0)\n"
                "}\n"
                "def main() = ()\n",
            ),
            (
                "s4_while_match_alias_cell_mutation",
                "use std.option.{Option, Some, None}\n"
                "def f(): Void = {\n"
                "    let c = cellNew(0);\n"
                "    let i = cellNew(0);\n"
                "    while (cellGet(i) < 1)\n"
                "        invariant 0 <= cellGet(i) && cellGet(i) <= 1\n"
                "    {\n"
                "        match Some(c) {\n"
                "            Some(alias) -> cellSet(alias, 99),\n"
                "            None -> (),\n"
                "        };\n"
                "        cellSet(i, cellGet(i) + 1)\n"
                "    };\n"
                "    assert(cellGet(c) == 0)\n"
                "}\n"
                "def main() = ()\n",
            ),
            (
                "s4_while_cond_side_effect",
                "def f(): Void = {\n"
                "    let c = cellNew(0);\n"
                "    let i = cellNew(0);\n"
                "    while ({ cellSet(c, 99); cellGet(i) < 1 })\n"
                "        invariant 0 <= cellGet(i) && cellGet(i) <= 1\n"
                "    {\n"
                "        cellSet(i, cellGet(i) + 1)\n"
                "    };\n"
                "    assert(cellGet(c) == 0)\n"
                "}\n"
                "def main() = ()\n",
            ),
        ]

        for name, code in adversarial_cases:
            f = tmp / f"{name}.gsa"
            f.write_text(code, encoding="utf-8")
            rj = run([geisha, "verify", "--json", "--solver", z3_bin, str(f)])
            assert rj.returncode == 1, f"adversarial case [{name}] MUST fail (exit 1), got {rj.returncode}:\n{rj.stdout}\n{rj.stderr}"
            jp = json.loads(rj.stdout)
            assert jp["ok"] is False and (jp["failed"] + jp["unknown"]) > 0, f"adversarial case [{name}] vacuously passed: {jp}"
        print(f"PASS [smt_verify_adversarial]: all {len(adversarial_cases)} soundness counterexamples rejected")

        # Positive S1-S4 semantic alignment tests
        s_pos_file = tmp / "s1_s4_positive.gsa"
        s_pos_file.write_text(
            "def shift32Masked(x: Int): Int\n"
            "    requires x == 32\n"
            "    ensures r -> r == 1\n"
            "= 1 << x\n"
            "\n"
            "def shift64Masked(x: Int): Int64\n"
            "    requires x == 64\n"
            "    ensures r -> r == intToI64(1)\n"
            "= intToI64(1) << x\n"
            "\n"
            "def convRoundTrip(x: Int): Int\n"
            "    ensures r -> r == x\n"
            "= i64ToInt(intToI64(x))\n"
            "\n"
            "def charOrder(): Bool\n"
            "    ensures r -> r\n"
            "= 'a' < 'z'\n"
            "\n"
            "def shortCircuitPreservesCell(): Void = {\n"
            "    let c = cellNew(0);\n"
            "    let _ = false && { cellSet(c, 42); true };\n"
            "    assert(cellGet(c) == 0)\n"
            "}\n"
            "\n"
            "def main() = ()\n",
            encoding="utf-8",
        )
        rp = run([geisha, "verify", "--json", "--solver", z3_bin, str(s_pos_file)])
        assert rp.returncode == 0, f"positive S1-S4 tests failed:\n{rp.stdout}\n{rp.stderr}"
        jp_pos = json.loads(rp.stdout)
        assert jp_pos["ok"] is True and jp_pos["failed"] == 0 and jp_pos["unknown"] == 0, f"unexpected: {jp_pos}"
        print("PASS [smt_verify_s1_s4_positive]: masked shifts, intToI64/i64ToInt, Char cmp, short-circuit verified")

        # Astra A1-A6 regression tests
        a_adv_cases = [
            (
                "a1_try_while_unannotated",
                "use std.result.{Result, Ok, Err}\n"
                "def step(x: Int): Result Int String = if (x > 0) Ok(x - 1) else Err(\"neg\")\n"
                "def loopTry(n: Int): Result Int String = {\n"
                "    let c = cellNew(n);\n"
                "    while (cellGet(c) > 0) {\n"
                "        let nxt = step(cellGet(c))?;\n"
                "        cellSet(c, nxt)\n"
                "    };\n"
                "    Ok(cellGet(c))\n"
                "}\n"
                "def main() = ()\n",
            ),
            (
                "a2_wrapped_cell_tuple_havoc",
                "def mutatePair(p: (Cell Int, Int)): Void = {\n"
                "    let (c, _) = p;\n"
                "    cellSet(c, 99)\n"
                "}\n"
                "def caller(): Void = {\n"
                "    let c = cellNew(0);\n"
                "    mutatePair((c, 7));\n"
                "    assert(cellGet(c) == 0)\n"
                "}\n"
                "def main() = ()\n",
            ),
            (
                "a2_wrapped_cell_adt_havoc",
                "data Wrap { MkWrap(Cell Int) }\n"
                "def mutateWrap(w: Wrap): Void = match w {\n"
                "    MkWrap(c) -> cellSet(c, 99),\n"
                "}\n"
                "def caller(): Void = {\n"
                "    let c = cellNew(0);\n"
                "    mutateWrap(MkWrap(c));\n"
                "    assert(cellGet(c) == 0)\n"
                "}\n"
                "def main() = ()\n",
            ),
            (
                "a2_wrapped_cell_alias",
                "def twoPairs(p1: (Cell Int, Int), p2: (Cell Int, Int)): Int\n"
                "    ensures r -> r == 1\n"
                "= 1\n"
                "def caller(): Int = {\n"
                "    let c = cellNew(0);\n"
                "    twoPairs((c, 1), (c, 2))\n"
                "}\n"
                "def main() = ()\n",
            ),
            (
                "a3_match_guard_mutation",
                "def guardMut(x: Int): Void = {\n"
                "    let c = cellNew(0);\n"
                "    match x {\n"
                "        _ if ({ cellSet(c, 99); false }) -> (),\n"
                "        _ -> assert(cellGet(c) == 0),\n"
                "    }\n"
                "}\n"
                "def main() = ()\n",
            ),
            (
                "a4_unmodeled_dividend_div_zero",
                "def f(x: Float): Int = floatToInt(x) / 0\n"
                "def main() = ()\n",
            ),
            (
                "a4_unmodeled_divisor",
                "def f(x: Float): Int = 10 / floatToInt(x)\n"
                "def main() = ()\n",
            ),
            (
                "a4_unmodeled_array_new_len",
                "def f(x: Float): Int = {\n"
                "    let a = arrayNew(floatToInt(x), 0);\n"
                "    arrayLen(a)\n"
                "}\n"
                "def main() = ()\n",
            ),
            (
                "a5_entry_decreases_negative",
                "def negDec(n: Int): Int\n"
                "    decreases n\n"
                "= if (n <= 0) 0 else negDec(n - 1)\n"
                "def main() = ()\n",
            ),
            (
                "r3_while_indirect_if_alias",
                "def indirectAlias(n: Int): Void = {\n"
                "    let c = cellNew(0);\n"
                "    let i = cellNew(0);\n"
                "    while (cellGet(i) < n)\n"
                "        invariant cellGet(i) >= 0\n"
                "    {\n"
                "        let alias = if (true) c else c;\n"
                "        cellSet(alias, 99);\n"
                "        cellSet(i, cellGet(i) + 1)\n"
                "    };\n"
                "    assert(cellGet(c) == 0)\n"
                "}\n"
                "def main() = ()\n",
            ),
            (
                "r3_while_match_pat_alias",
                "use std.option.{Option, Some, None}\n"
                "def patAlias(n: Int): Void = {\n"
                "    let c = cellNew(0);\n"
                "    let i = cellNew(0);\n"
                "    while (cellGet(i) < n)\n"
                "        invariant cellGet(i) >= 0\n"
                "    {\n"
                "        match Some(c) {\n"
                "            Some(alias) -> cellSet(alias, 99),\n"
                "            None -> (),\n"
                "        };\n"
                "        cellSet(i, cellGet(i) + 1)\n"
                "    };\n"
                "    assert(cellGet(c) == 0)\n"
                "}\n"
                "def main() = ()\n",
            ),
        ]
        for name, code in a_adv_cases:
            f = tmp / f"{name}.gsa"
            f.write_text(code, encoding="utf-8")
            rj = run([geisha, "verify", "--json", "--solver", z3_bin, str(f)])
            assert rj.returncode == 1, f"Astra adversarial case [{name}] MUST fail (exit 1), got {rj.returncode}:\n{rj.stdout}\n{rj.stderr}"
            jp = json.loads(rj.stdout)
            assert jp["ok"] is False and (jp["failed"] + jp["unknown"]) > 0, f"Astra case [{name}] vacuously passed: {jp}"
        print(f"PASS [smt_verify_a1_a5_adversarial]: all {len(a_adv_cases)} Astra A1-A5 soundness cases rejected")

        # A1 runtime 3-path test for `while` with `?` under `--contracts=check`
        a1_rt = tmp / "a1_try_while_rt.gsa"
        a1_rt.write_text(
            "use std.result.{Result, Ok, Err}\n"
            "def maybeStep(x: Int): Result Int String = if (x == 2) Err(\"stop\") else Ok(x - 1)\n"
            "def runLoop(n: Int): Result Int String\n"
            "    ensures r -> true\n"
            "= {\n"
            "    let c = cellNew(n);\n"
            "    while (cellGet(c) > 0)\n"
            "        invariant cellGet(c) >= 0\n"
            "        decreases cellGet(c)\n"
            "    {\n"
            "        let nxt = maybeStep(cellGet(c))?;\n"
            "        cellSet(c, nxt)\n"
            "    };\n"
            "    Ok(cellGet(c))\n"
            "}\n"
            "def main(): Void = {\n"
            "    // 0 iterations: entry invariant holds, decreases not checked\n"
            "    let _ = runLoop(0);\n"
            "    // early Err exit on x==2: skips back-edge invariant/decreases\n"
            "    let _ = runLoop(2);\n"
            "    // normal iteration 1 -> 0: checks decreases & back-edge invariant\n"
            "    let _ = runLoop(1);\n"
            "    ()\n"
            "}\n",
            encoding="utf-8",
        )
        a1_bin = tmp / ("a1_try_while_rt.exe" if sys.platform == "win32" else "a1_try_while_rt")
        rc_a1 = run([geisha, "--contracts=check", "--runtime", runtime, "-o", str(a1_bin), str(a1_rt)])
        assert rc_a1.returncode == 0, f"A1 runtime compile failed:\n{rc_a1.stdout}\n{rc_a1.stderr}"
        rr_a1 = run([str(a1_bin)])
        assert rr_a1.returncode == 0, f"A1 runtime 3-path test failed:\n{rr_a1.stdout}\n{rr_a1.stderr}"

        # A5 duplicate `decreases` compile error (def & while)
        for kind, code in [
            ("dup_def_dec", "def f(n: Int): Int\n    decreases n\n    decreases n + 1\n= n\ndef main() = ()\n"),
            ("dup_while_dec", "def f(n: Int): Void = {\n    let i = cellNew(n);\n    while (cellGet(i) > 0)\n        decreases cellGet(i)\n        decreases cellGet(i) + 1\n    { cellSet(i, cellGet(i) - 1) }\n}\ndef main() = ()\n"),
        ]:
            df = tmp / f"{kind}.gsa"
            df.write_text(code, encoding="utf-8")
            rc_d = run([geisha, "check", str(df)])
            assert rc_d.returncode != 0 and "at most one `decreases` clause" in (rc_d.stdout + rc_d.stderr), (
                f"A5 {kind} should fail with duplicate decreases diagnostic, got:\n{rc_d.stdout}\n{rc_d.stderr}"
            )

        # A6: user var named `loc_count` appears in counterexample, `doc` shows instance contracts, `fmt` indents while/instance contracts idempotently
        a6_loc = tmp / "a6_loc_count.gsa"
        a6_loc.write_text(
            "def checkLoc(loc_count: Int): Int\n"
            "    ensures r -> r > 0\n"
            "= loc_count\n"
            "def main() = ()\n",
            encoding="utf-8",
        )
        r_loc = run([geisha, "verify", "--json", "--solver", z3_bin, str(a6_loc)])
        assert r_loc.returncode == 1
        assert "loc_count" in r_loc.stdout, f"A6: expected `loc_count` in counterexample model, got:\n{r_loc.stdout}"

        a6_doc = tmp / "a6_inst_doc.gsa"
        a6_doc.write_text(
            "pub concept SafeDiv a {\n"
            "    def sdiv(x: a, y: a): a\n"
            "}\n"
            "pub instance SafeDiv Int {\n"
            "    def sdiv(x, y)\n"
            "        requires y != 0\n"
            "    = x / y\n"
            "}\n"
            "def main() = ()\n",
            encoding="utf-8",
        )
        r_doc = run([geisha, "doc", str(a6_doc)])
        assert r_doc.returncode == 0 and "requires y != 0" in r_doc.stdout, f"A6 doc missing instance contract:\n{r_doc.stdout}\n{r_doc.stderr}"

        a6_fmt = tmp / "a6_fmt.gsa"
        a6_fmt.write_text(
            "def f(n: Int): Void = {\n"
            "    let i = cellNew(0);\n"
            "    while (cellGet(i) < n)\n"
            "        invariant cellGet(i) >= 0\n"
            "    {\n"
            "        cellSet(i, cellGet(i) + 1)\n"
            "    }\n"
            "}\n",
            encoding="utf-8",
            newline="\n",
        )
        r_fmt1 = run([geisha, "fmt", "--stdout", str(a6_fmt)])
        assert r_fmt1.returncode == 0 and "        invariant cellGet(i) >= 0" in r_fmt1.stdout, f"A6 fmt indent wrong:\n{r_fmt1.stdout}\n{r_fmt1.stderr}"
        a6_fmt2 = tmp / "a6_fmt2.gsa"
        a6_fmt2.write_text(r_fmt1.stdout, encoding="utf-8", newline="\n")
        r_fmt2 = run([geisha, "fmt", "--stdout", str(a6_fmt2)])
        assert r_fmt2.returncode == 0 and r_fmt2.stdout == r_fmt1.stdout, f"A6 fmt not idempotent:\n{r_fmt1.stdout}\n---\n{r_fmt2.stdout}"
        print("PASS [smt_verify_a1_a6_polish]: A1 runtime 3-path, A5 duplicate decreases, A6 loc_count/doc/fmt verified")

        # ------------------------------------------------------------------
        # D1: Production verified kernels (`src/verified_kernels.gsa`) + `--fn` filter
        # ------------------------------------------------------------------
        vk_path = repo_root / "src" / "verified_kernels.gsa"
        r_vk = run([geisha, "verify", "--json", "--solver", z3_bin, "--src-root", str(repo_root), str(vk_path)])
        assert r_vk.returncode == 0, f"D1 verified_kernels.gsa verify failed:\n{r_vk.stdout}\n{r_vk.stderr}"
        vk_json = json.loads(r_vk.stdout)
        assert vk_json["ok"] is True and vk_json["failed"] == 0 and vk_json["unknown"] == 0 and vk_json["proved"] >= 30, (
            f"D1 unexpected verified_kernels summary: {vk_json}"
        )
        r_vk_fn = run([
            geisha, "verify", "--json", "--solver", z3_bin, "--src-root", str(repo_root),
            "--fn", "uleb32Byte", "--fn", "clampOffset", str(vk_path),
        ])
        assert r_vk_fn.returncode == 0, f"D1 --fn filter failed:\n{r_vk_fn.stdout}\n{r_vk_fn.stderr}"
        vk_fn_json = json.loads(r_vk_fn.stdout)
        assert vk_fn_json["ok"] is True and 0 < vk_fn_json["proved"] < vk_json["proved"], (
            f"D1 --fn filter did not restrict obligations: {vk_fn_json} vs {vk_json}"
        )
        r_vk_miss = run([
            geisha, "verify", "--json", "--solver", z3_bin, "--src-root", str(repo_root),
            "--fn", "definitely_not_a_real_fn_xyz", str(vk_path),
        ])
        assert r_vk_miss.returncode != 0, f"D1 --fn nonexistent should fail, got 0:\n{r_vk_miss.stdout}"
        print(f"PASS [d1_verified_kernels]: {vk_json['proved']} obligations proved, --fn filter verified")

        # ------------------------------------------------------------------
        # D3: Verification-Driven Optimization (`--verified-opt`) + 3 Soundness Iron Laws
        # ------------------------------------------------------------------
        d3_pos = tmp / "d3_pos.gsa"
        d3_pos.write_text(
            "use std.str.{intToStr}\n"
            "def safeDiv(a: Int, b: Int): Int\n"
            "    requires b != 0\n"
            "= a / b\n"
            "def safeIdx(arr: MutArray Int, i: Int): Int\n"
            "    requires i >= 0 && i < arrayLen(arr)\n"
            "= arrayGet(arr, i)\n"
            "def safeAlloc(n: Int): Int\n"
            "    requires n >= 0\n"
            "= {\n"
            "    let a = arrayNew(n, 7);\n"
            "    arrayLen(a)\n"
            "}\n"
            "def runAll(a: Int, b: Int): Int = {\n"
            "    let arr = arrayNew(4, 7);\n"
            "    let v = safeIdx(arr, 2);\n"
            "    let _ = safeAlloc(4);\n"
            "    if (b != 0) v + safeDiv(a, b) else v\n"
            "}\n"
            "def main(): Void = {\n"
            "    let r1 = runAll(100, 5);\n"
            "    let r2 = runAll(-2147483648, -1);\n"
            "    printLn(intToStr(r1) + \":\" + intToStr(r2))\n"
            "}\n",
            encoding="utf-8",
            newline="\n",
        )
        d3_pos_ll = tmp / "d3_pos.ll"
        r_d3_ir = run([geisha, "--verified-opt", "--solver", z3_bin, "-e", "-o", str(d3_pos_ll), str(d3_pos)])
        assert r_d3_ir.returncode == 0, f"D3 positive IR compile failed:\n{r_d3_ir.stdout}\n{r_d3_ir.stderr}"
        pos_ir = d3_pos_ll.read_text(encoding="utf-8")
        def fn_ir_block(ir_text: str, fn_name: str) -> str:
            marker = f"@{fn_name}("
            pos = 0
            start = -1
            while True:
                idx = ir_text.find(marker, pos)
                if idx == -1:
                    break
                line_start = ir_text.rfind("\n", 0, idx) + 1
                if ir_text[line_start:idx].startswith("define "):
                    start = line_start
                    break
                pos = idx + 1
            assert start != -1, f"definition of @{fn_name} not found in IR"
            end = ir_text.find("\n}", start)
            assert end != -1, f"end of @{fn_name} not found in IR"
            return ir_text[start:end + 2]
        safe_div_ir = fn_ir_block(pos_ir, "safeDiv")
        assert "call void @llvm.assume(i1" in safe_div_ir, f"D3 safeDiv missing @llvm.assume:\n{safe_div_ir}"
        assert "div.zero" not in safe_div_ir, f"D3 safeDiv did not elide div.zero:\n{safe_div_ir}"
        assert "div.ov" in safe_div_ir, f"D3 safeDiv MUST preserve INT_MIN/-1 div.ov guard:\n{safe_div_ir}"
        safe_idx_ir = fn_ir_block(pos_ir, "safeIdx")
        assert "call void @llvm.assume(i1" in safe_idx_ir, f"D3 safeIdx missing @llvm.assume:\n{safe_idx_ir}"
        assert "arr.oob_trap" not in safe_idx_ir, f"D3 safeIdx did not elide arr.oob_trap:\n{safe_idx_ir}"
        safe_alloc_ir = fn_ir_block(pos_ir, "safeAlloc")
        assert "call void @llvm.assume(i1" in safe_alloc_ir, f"D3 safeAlloc missing @llvm.assume:\n{safe_alloc_ir}"
        assert "arr.bad_len" not in safe_alloc_ir, f"D3 safeAlloc did not elide arr.bad_len:\n{safe_alloc_ir}"

        d3_pos_bin = tmp / ("d3_pos.exe" if sys.platform == "win32" else "d3_pos")
        r_d3_bin = run([geisha, "--verified-opt", "--solver", z3_bin, "--runtime", runtime, "-O2", "-o", str(d3_pos_bin), str(d3_pos)])
        assert r_d3_bin.returncode == 0, f"D3 positive -O2 build failed:\n{r_d3_bin.stdout}\n{r_d3_bin.stderr}"
        r_d3_run = run([str(d3_pos_bin)])
        assert r_d3_run.returncode == 0 and r_d3_run.stdout.strip() == "27:-2147483641", (
            f"D3 positive -O2 run mismatch (expected 27:-2147483641):\nrc={r_d3_run.returncode}\nout={r_d3_run.stdout!r}\nerr={r_d3_run.stderr!r}"
        )

        # D3 Adversarial Negative 1 (Iron Law 1: unverified caller MUST exclude callee with `requires`)
        d3_neg1 = tmp / "d3_neg_unverified_caller.gsa"
        d3_neg1.write_text(
            "def idxWithReq(arr: MutArray Int, i: Int): Int\n"
            "    requires i >= 0 && i < arrayLen(arr)\n"
            "= arrayGet(arr, i)\n"
            "def main(): Void = {\n"
            "    let arr = arrayNew(4, 1);\n"
            "    let _ = idxWithReq(arr, 99);\n"
            "    ()\n"
            "}\n",
            encoding="utf-8",
            newline="\n",
        )
        d3_neg1_ll = tmp / "d3_neg1.ll"
        r_n1_ir = run([geisha, "--verified-opt", "--solver", z3_bin, "-e", "-o", str(d3_neg1_ll), str(d3_neg1)])
        assert r_n1_ir.returncode == 0, f"D3 neg1 IR compile failed:\n{r_n1_ir.stdout}\n{r_n1_ir.stderr}"
        n1_ir = fn_ir_block(d3_neg1_ll.read_text(encoding="utf-8"), "idxWithReq")
        assert "arr.oob_trap" in n1_ir, f"D3 Iron Law 1 violated: unverified caller elided arr.oob_trap!\n{n1_ir}"
        assert "llvm.assume" not in n1_ir, f"D3 Iron Law 1 violated: unverified caller emitted @llvm.assume!\n{n1_ir}"
        d3_neg1_bin = tmp / ("d3_neg1.exe" if sys.platform == "win32" else "d3_neg1")
        r_n1_bin = run([geisha, "--verified-opt", "--solver", z3_bin, "--runtime", runtime, "-O2", "-o", str(d3_neg1_bin), str(d3_neg1)])
        assert r_n1_bin.returncode == 0
        r_n1_run = run([str(d3_neg1_bin)])
        assert r_n1_run.returncode != 0, f"D3 Iron Law 1 violated: OOB access did NOT trap! rc={r_n1_run.returncode}"

        # D3 Adversarial Negative 2 (Iron Law 2: function containing `assume(...)` MUST be excluded)
        d3_neg2 = tmp / "d3_neg_assume.gsa"
        d3_neg2.write_text(
            "def idxWithAssume(arr: MutArray Int, i: Int): Int = {\n"
            "    assume(i >= 0 && i < arrayLen(arr));\n"
            "    arrayGet(arr, i)\n"
            "}\n"
            "def main(): Void = {\n"
            "    let arr = arrayNew(4, 1);\n"
            "    let _ = idxWithAssume(arr, 99);\n"
            "    ()\n"
            "}\n",
            encoding="utf-8",
            newline="\n",
        )
        d3_neg2_ll = tmp / "d3_neg2.ll"
        r_n2_ir = run([geisha, "--verified-opt", "--solver", z3_bin, "-e", "-o", str(d3_neg2_ll), str(d3_neg2)])
        assert r_n2_ir.returncode == 0, f"D3 neg2 IR compile failed:\n{r_n2_ir.stdout}\n{r_n2_ir.stderr}"
        n2_ir = fn_ir_block(d3_neg2_ll.read_text(encoding="utf-8"), "idxWithAssume")
        assert "arr.oob_trap" in n2_ir, f"D3 Iron Law 2 violated: assume() elided arr.oob_trap!\n{n2_ir}"
        assert "llvm.assume" not in n2_ir, f"D3 Iron Law 2 violated: assume() emitted @llvm.assume!\n{n2_ir}"
        d3_neg2_bin = tmp / ("d3_neg2.exe" if sys.platform == "win32" else "d3_neg2")
        r_n2_bin = run([geisha, "--verified-opt", "--solver", z3_bin, "--runtime", runtime, "-O2", "-o", str(d3_neg2_bin), str(d3_neg2)])
        assert r_n2_bin.returncode == 0
        r_n2_run = run([str(d3_neg2_bin)])
        assert r_n2_run.returncode != 0, f"D3 Iron Law 2 violated: assume() OOB access did NOT trap! rc={r_n2_run.returncode}"

        # D3 Cache Isolation: `geisha run` vs `geisha run --verified-opt`
        r_run_plain = run([geisha, "run", "--runtime", runtime, str(d3_pos)])
        assert r_run_plain.returncode == 0 and r_run_plain.stdout.strip() == "27:-2147483641", (
            f"D3 plain geisha run failed:\n{r_run_plain.stdout}\n{r_run_plain.stderr}"
        )
        r_run_vopt = run([geisha, "run", "--verified-opt", "--solver", z3_bin, "--runtime", runtime, str(d3_pos)])
        assert r_run_vopt.returncode == 0 and r_run_vopt.stdout.strip() == "27:-2147483641", (
            f"D3 --verified-opt geisha run failed:\n{r_run_vopt.stdout}\n{r_run_vopt.stderr}"
        )

        # V1 Adversarial: unverified callee & assume-tainted callee with false `ensures` MUST NOT poison caller
        for v1_name, v1_code in [
            (
                "v1_unverified_callee_ensures",
                "def lie(x: Int): Int\n"
                "    ensures _ -> x == 0\n"
                "= x\n"
                "def victim(i: Int): Int = {\n"
                "    let arr = arrayNew(4, 7);\n"
                "    let _ = lie(i);\n"
                "    arrayGet(arr, i)\n"
                "}\n"
                "def main(): Void = { let _ = victim(99); () }\n",
            ),
            (
                "v1_assume_callee_ensures",
                "def lieAssume(x: Int): Int\n"
                "    ensures _ -> x == 0\n"
                "= { assume(x == 0); x }\n"
                "def victim(i: Int): Int = {\n"
                "    let arr = arrayNew(4, 7);\n"
                "    let _ = lieAssume(i);\n"
                "    arrayGet(arr, i)\n"
                "}\n"
                "def main(): Void = { let _ = victim(99); () }\n",
            ),
        ]:
            v1_src = tmp / f"{v1_name}.gsa"
            v1_src.write_text(v1_code, encoding="utf-8", newline="\n")
            v1_ll = tmp / f"{v1_name}.ll"
            r_v1_ir = run([geisha, "--verified-opt", "--solver", z3_bin, "-e", "-o", str(v1_ll), str(v1_src)])
            assert r_v1_ir.returncode == 0, f"V1 {v1_name} IR compile failed:\n{r_v1_ir.stdout}\n{r_v1_ir.stderr}"
            vic_ir = fn_ir_block(v1_ll.read_text(encoding="utf-8"), "victim")
            assert "arr.oob_trap" in vic_ir, f"V1 {v1_name}: false callee ensures elided arr.oob_trap in victim!\n{vic_ir}"
            v1_bin = tmp / (f"{v1_name}.exe" if sys.platform == "win32" else v1_name)
            r_v1_bin = run([geisha, "--verified-opt", "--solver", z3_bin, "--runtime", runtime, "-O2", "-o", str(v1_bin), str(v1_src)])
            assert r_v1_bin.returncode == 0
            r_v1_run = run([str(v1_bin)])
            assert r_v1_run.returncode != 0, f"V1 {v1_name}: OOB access in victim did NOT trap! rc={r_v1_run.returncode}"

        # V2 Adversarial: zero-caller `requires` & `--no-main` MUST NOT elide bounds checks
        v2_src = tmp / "v2_nomain_req.gsa"
        v2_src.write_text(
            "pub def fastGet(arr: MutArray Int, i: Int): Int\n"
            "    requires 0 <= i && i < arrayLen(arr)\n"
            "= arrayGet(arr, i)\n",
            encoding="utf-8",
            newline="\n",
        )
        v2_ll = tmp / "v2_nomain_req.ll"
        r_v2_ir = run([geisha, "--verified-opt", "--no-main", "--solver", z3_bin, "-e", "-o", str(v2_ll), str(v2_src)])
        assert r_v2_ir.returncode == 0, f"V2 --no-main IR compile failed:\n{r_v2_ir.stdout}\n{r_v2_ir.stderr}"
        fg_ir = fn_ir_block(v2_ll.read_text(encoding="utf-8"), "fastGet")
        assert "arr.oob_trap" in fg_ir and "llvm.assume" not in fg_ir, (
            f"V2 violated: --no-main / zero-caller elided check or emitted @llvm.assume!\n{fg_ir}"
        )

        # V3 Regression: tail-recursive function with `ensures` MUST keep `tail call` TCO under `--verified-opt`
        v3_src = tmp / "v3_tco.gsa"
        v3_src.write_text(
            "def countDown(n: Int): Int\n"
            "    requires n >= 0\n"
            "    ensures r -> r == 0\n"
            "    decreases n\n"
            "= if (n <= 0) 0 else countDown(n - 1)\n"
            "def main(): Void = { let _ = countDown(10); () }\n",
            encoding="utf-8",
            newline="\n",
        )
        v3_ll = tmp / "v3_tco.ll"
        r_v3_ir = run([geisha, "--verified-opt", "--solver", z3_bin, "-e", "-o", str(v3_ll), str(v3_src)])
        assert r_v3_ir.returncode == 0, f"V3 TCO IR compile failed:\n{r_v3_ir.stdout}\n{r_v3_ir.stderr}"
        cd_ir = fn_ir_block(v3_ll.read_text(encoding="utf-8"), "countDown")
        assert "tail call" in cd_ir, f"V3 violated: countDown lost tail call TCO under --verified-opt!\n{cd_ir}"

        # W1 Adversarial: non-let `arrayNew` / `arrayNewZeroed` MUST emit length>=0 VC and preserve `arr.bad_len`
        w1_src = tmp / "w1_nonlet_arraynew.gsa"
        w1_src.write_text(
            "def direct(n: Int): MutArray Int = arrayNew(n, 0)\n"
            "def nested(n: Int): Int = arrayLen(arrayNew(n, 0))\n"
            "def zeroed(n: Int): MutArray Int = arrayNewZeroed(n)\n"
            "def main(): Void = {\n"
            "    let _ = direct(2);\n"
            "    let _ = nested(2);\n"
            "    let _ = zeroed(2);\n"
            "    ()\n"
            "}\n",
            encoding="utf-8",
            newline="\n",
        )
        r_w1_v = run([geisha, "verify", "--json", "--solver", z3_bin, str(w1_src)])
        assert r_w1_v.returncode == 1, f"W1 verify MUST fail (exit 1), got {r_w1_v.returncode}:\n{r_w1_v.stdout}\n{r_w1_v.stderr}"
        w1_j = json.loads(r_w1_v.stdout)
        assert w1_j["failed"] >= 3, f"W1 expected >=3 failed bounds VCs (direct/nested/zeroed), got: {w1_j}"
        w1_ll = tmp / "w1_nonlet_arraynew.ll"
        r_w1_ir = run([geisha, "--verified-opt", "--solver", z3_bin, "-e", "-o", str(w1_ll), str(w1_src)])
        assert r_w1_ir.returncode == 0, f"W1 IR compile failed:\n{r_w1_ir.stdout}\n{r_w1_ir.stderr}"
        w1_ir_txt = w1_ll.read_text(encoding="utf-8")
        for fn_nm in ("direct", "nested", "zeroed"):
            blk = fn_ir_block(w1_ir_txt, fn_nm)
            assert "arr.bad_len" in blk, f"W1 violated: {fn_nm} elided arr.bad_len without requires n >= 0!\n{blk}"

        # W2 Adversarial: implicit non-aliasing precondition on mutable params MUST participate in upward call-graph fixed-point
        w2_src = tmp / "w2_alias_precond.gsa"
        w2_src.write_text(
            "def readAfter(a: Cell Int, b: Cell Int): Int = {\n"
            "    cellSet(a, 1);\n"
            "    cellSet(b, 2);\n"
            "    assert(cellGet(a) == 1);\n"
            "    cellGet(a)\n"
            "}\n"
            "def main(): Void = { let c = cellNew(0); let _ = readAfter(c, c); () }\n",
            encoding="utf-8",
            newline="\n",
        )
        w2_ll = tmp / "w2_alias_precond.ll"
        r_w2_ir = run([geisha, "--verified-opt", "--solver", z3_bin, "-e", "-o", str(w2_ll), str(w2_src)])
        assert r_w2_ir.returncode == 0, f"W2 IR compile failed:\n{r_w2_ir.stdout}\n{r_w2_ir.stderr}"
        ra_ir = fn_ir_block(w2_ll.read_text(encoding="utf-8"), "readAfter")
        assert "llvm.assume" not in ra_ir, f"W2 violated: aliased caller emitted false @llvm.assume in readAfter!\n{ra_ir}"
        w2_exp_ll = tmp / "w2_alias_export.ll"
        r_w2_exp = run([geisha, "--verified-opt", "--export", "readAfter", "--solver", z3_bin, "-e", "-o", str(w2_exp_ll), str(w2_src)])
        assert r_w2_exp.returncode == 0
        ra_exp_ir = fn_ir_block(w2_exp_ll.read_text(encoding="utf-8"), "readAfter")
        assert "llvm.assume" not in ra_exp_ir, f"W2 violated: exported readAfter emitted @llvm.assume!\n{ra_exp_ir}"

        # W3 Adversarial: side-effecting `assert(...)` MUST fail verification (unknown) and NOT poison caller with false `ensures`
        w3_src = tmp / "w3_impure_assert.gsa"
        w3_src.write_text(
            "def readCell(): Int\n"
            "    ensures r -> r == 7\n"
            "= {\n"
            "    let c = cellNew(2);\n"
            "    assert({ cellSet(c, 7); true });\n"
            "    cellGet(c)\n"
            "}\n"
            "def callerOfReadCell(): Int = {\n"
            "    let v = readCell();\n"
            "    assert(v == 7);\n"
            "    v\n"
            "}\n"
            "def main(): Void = { let _ = callerOfReadCell(); () }\n",
            encoding="utf-8",
            newline="\n",
        )
        r_w3_v = run([geisha, "verify", "--json", "--solver", z3_bin, str(w3_src)])
        assert r_w3_v.returncode == 1, f"W3 verify MUST fail (exit 1), got {r_w3_v.returncode}:\n{r_w3_v.stdout}\n{r_w3_v.stderr}"
        w3_ll = tmp / "w3_impure_assert.ll"
        r_w3_ir = run([geisha, "--verified-opt", "--solver", z3_bin, "-e", "-o", str(w3_ll), str(w3_src)])
        assert r_w3_ir.returncode == 0, f"W3 IR compile failed:\n{r_w3_ir.stdout}\n{r_w3_ir.stderr}"
        caller_ir = fn_ir_block(w3_ll.read_text(encoding="utf-8"), "callerOfReadCell")
        assert "llvm.assume" not in caller_ir, f"W3 violated: side-effecting assert poisoned callerOfReadCell with @llvm.assume!\n{caller_ir}"

        # W4 CLI: `geisha eval` and `geisha eval --verified-opt`
        r_eval1 = run([geisha, "eval", "--runtime", runtime, 'printLn("eval-ok")'])
        assert r_eval1.returncode == 0 and r_eval1.stdout.strip() == "eval-ok", (
            f"W4 plain eval failed:\n{r_eval1.stdout}\n{r_eval1.stderr}"
        )
        r_eval2 = run([geisha, "eval", "--verified-opt", "--solver", z3_bin, "--runtime", runtime, 'printLn("eval-vopt-ok")'])
        assert r_eval2.returncode == 0 and r_eval2.stdout.strip() == "eval-vopt-ok", (
            f"W4 --verified-opt eval failed:\n{r_eval2.stdout}\n{r_eval2.stderr}"
        )

        # X1-X3 Adversarial: branch-merged Cell / Option(Cell) references & unknown-loc havoc/aliasing
        for x_name, x_target_fn, x_code in [
            (
                "x1_single_fn_if_cell",
                "singleFnIfCell",
                "def singleFnIfCell(b: Bool): Int\n"
                "    ensures r -> r == 1\n"
                "= {\n"
                "    let c = cellNew(1);\n"
                "    let alias = if (b) c else cellNew(2);\n"
                "    cellSet(alias, 99);\n"
                "    assert(cellGet(c) == 1);\n"
                "    cellGet(c)\n"
                "}\n"
                "def main(): Void = { let _ = singleFnIfCell(true); () }\n",
            ),
            (
                "x2_sneaky_alias_if",
                "readAfter",
                "def readAfter(a: Cell Int, b: Cell Int): Int = {\n"
                "    cellSet(a, 1);\n"
                "    cellSet(b, 2);\n"
                "    assert(cellGet(a) == 1);\n"
                "    cellGet(a)\n"
                "}\n"
                "def main(): Void = {\n"
                "    let c = cellNew(0);\n"
                "    let a = if (true) c else c;\n"
                "    let _ = readAfter(a, c);\n"
                "    ()\n"
                "}\n",
            ),
            (
                "x3_match_opt_cell_alias",
                "matchOptCell",
                "use std.option.{Option, Some, None}\n"
                "def matchOptCell(b: Bool): Int = {\n"
                "    let c = cellNew(1);\n"
                "    match (if (b) Some(c) else None) {\n"
                "        Some(alias) -> { cellSet(alias, 99); assert(cellGet(c) == 1); cellGet(c) },\n"
                "        None -> cellGet(c),\n"
                "    }\n"
                "}\n"
                "def main(): Void = { let _ = matchOptCell(true); () }\n",
            ),
        ]:
            x_src = tmp / f"{x_name}.gsa"
            x_src.write_text(x_code, encoding="utf-8", newline="\n")
            r_xv = run([geisha, "verify", "--json", "--solver", z3_bin, str(x_src)])
            assert r_xv.returncode == 1, f"X1-X3 {x_name} verify MUST fail (exit 1), got {r_xv.returncode}:\n{r_xv.stdout}\n{r_xv.stderr}"
            x_ll = tmp / f"{x_name}.ll"
            r_xir = run([geisha, "--verified-opt", "--solver", z3_bin, "-e", "-o", str(x_ll), str(x_src)])
            assert r_xir.returncode == 0, f"X1-X3 {x_name} IR compile failed:\n{r_xir.stdout}\n{r_xir.stderr}"
            x_blk = fn_ir_block(x_ll.read_text(encoding="utf-8"), x_target_fn)
            assert "llvm.assume" not in x_blk, f"X1-X3 {x_name} emitted false @llvm.assume in {x_target_fn}!\n{x_blk}"

        # Y1-Y2 Adversarial: shadowed pattern vars on unknown scrutinee & nested Cell(Cell)/MutArray(Cell)
        for y_name, y_target_fn, y_code in [
            (
                "y1_shadow_option",
                "observe",
                "use std.option.{Option, Some, None}\n"
                "def observe(b: Bool): Int = {\n"
                "    let x = 1;\n"
                "    let picked = if (b) Some(7) else None;\n"
                "    match picked {\n"
                "        Some(x) -> { assert(x == 1); x },\n"
                "        None -> x,\n"
                "    }\n"
                "}\n"
                "def main(): Void = { let _ = observe(true); () }\n",
            ),
            (
                "y1_shadow_nested_tuple",
                "observeTuple",
                "use std.option.{Option, Some, None}\n"
                "def observeTuple(b: Bool): Int = {\n"
                "    let x = 1;\n"
                "    let y = 2;\n"
                "    let picked = if (b) Some((7, 8)) else None;\n"
                "    match picked {\n"
                "        Some((x, y)) -> { assert(x == 1 && y == 2); x + y },\n"
                "        None -> x + y,\n"
                "    }\n"
                "}\n"
                "def main(): Void = { let _ = observeTuple(true); () }\n",
            ),
            (
                "y2_nested_cell_havoc",
                "observe",
                "def update(box: Cell (Cell Int)): Void = cellSet(cellGet(box), 7)\n"
                "def observe(): Int = {\n"
                "    let value = cellNew(1);\n"
                "    let box = cellNew(value);\n"
                "    update(box);\n"
                "    assert(cellGet(value) == 1);\n"
                "    cellGet(value)\n"
                "}\n"
                "def main(): Void = { let _ = observe(); () }\n",
            ),
            (
                "y2_nested_cell_alias",
                "twoArg",
                "def twoArg(box: Cell (Cell Int), direct: Cell Int): Int = {\n"
                "    cellSet(direct, 1);\n"
                "    cellSet(cellGet(box), 9);\n"
                "    assert(cellGet(direct) == 1);\n"
                "    cellGet(direct)\n"
                "}\n"
                "def main(): Void = {\n"
                "    let v = cellNew(0);\n"
                "    let b = cellNew(v);\n"
                "    let _ = twoArg(b, v);\n"
                "    ()\n"
                "}\n",
            ),
            (
                "y2_mutarray_cell_havoc",
                "observeArr",
                "def mutateArr(xs: MutArray (Cell Int)): Void = {\n"
                "    if (arrayLen(xs) > 0) cellSet(arrayGet(xs, 0), 7) else ()\n"
                "}\n"
                "def observeArr(): Int = {\n"
                "    let value = cellNew(1);\n"
                "    let xs = arrayNew(1, value);\n"
                "    mutateArr(xs);\n"
                "    assert(cellGet(value) == 1);\n"
                "    cellGet(value)\n"
                "}\n"
                "def main(): Void = { let _ = observeArr(); () }\n",
            ),
        ]:
            y_src = tmp / f"{y_name}.gsa"
            y_src.write_text(y_code, encoding="utf-8", newline="\n")
            r_yv = run([geisha, "verify", "--json", "--solver", z3_bin, str(y_src)])
            assert r_yv.returncode == 1, f"Y1-Y2 {y_name} verify MUST fail (exit 1), got {r_yv.returncode}:\n{r_yv.stdout}\n{r_yv.stderr}"
            y_ll = tmp / f"{y_name}.ll"
            r_yir = run([geisha, "--verified-opt", "--solver", z3_bin, "-e", "-o", str(y_ll), str(y_src)])
            assert r_yir.returncode == 0, f"Y1-Y2 {y_name} IR compile failed:\n{r_yir.stdout}\n{r_yir.stderr}"
            y_blk = fn_ir_block(y_ll.read_text(encoding="utf-8"), y_target_fn)
            assert "llvm.assume" not in y_blk, f"Y1-Y2 {y_name} emitted false @llvm.assume in {y_target_fn}!\n{y_blk}"

        # Y3 Positive: `arrayNewZeroed` on `MutArray Bool` and `MutArray Int64` proves 100% cleanly
        y3_src = tmp / "y3_zerosorts.gsa"
        y3_src.write_text(
            "def checkZeroBool(n: Int): Bool\n"
            "    requires n > 0\n"
            "    ensures r -> !r\n"
            "= {\n"
            "    let a: MutArray Bool = arrayNewZeroed(n);\n"
            "    arrayGet(a, 0)\n"
            "}\n"
            "def checkZeroI64(n: Int): Int64\n"
            "    requires n > 0\n"
            "    ensures r -> r == intToI64(0)\n"
            "= {\n"
            "    let a: MutArray Int64 = arrayNewZeroed(n);\n"
            "    arrayGet(a, 0)\n"
            "}\n"
            "def main(): Void = ()\n",
            encoding="utf-8",
            newline="\n",
        )
        r_y3 = run([geisha, "verify", "--json", "--solver", z3_bin, str(y3_src)])
        assert r_y3.returncode == 0, f"Y3 zerosorts verify failed:\n{r_y3.stdout}\n{r_y3.stderr}"
        y3_j = json.loads(r_y3.stdout)
        assert y3_j["ok"] is True and y3_j["failed"] == 0 and y3_j["unknown"] == 0 and y3_j["proved"] >= 6, (
            f"Y3 zerosorts unexpected summary: {y3_j}"
        )

        # Y4 Negative: `geisha eval --timeout -1` MUST reject non-positive timeout
        r_y4 = run([geisha, "eval", "--timeout", "-1", "1"])
        assert r_y4.returncode != 0 and "positive integer" in (r_y4.stdout + r_y4.stderr), (
            f"Y4 eval --timeout -1 should fail with positive-integer diagnostic:\nrc={r_y4.returncode}\nout={r_y4.stdout}\nerr={r_y4.stderr}"
        )

        # Z1-Z3 Adversarial: transitive ambient heap effects (global Cell, Int-wrapped global write,
        # while-loop global write, callee-ensures downward pruning, and gcHandleNew/gcHandleGet)
        for z_name, z_target_fn, z_code in [
            (
                "z1_escaped_global",
                "observe",
                "def slot: Cell (Cell Int) = cellNew(cellNew(0))\n"
                "def remember(c: Cell Int): Void = cellSet(slot, c)\n"
                "def writeSaved(): Void = cellSet(cellGet(slot), 7)\n"
                "def observe(): Int = {\n"
                "    let c = cellNew(0);\n"
                "    remember(c);\n"
                "    cellSet(c, 1);\n"
                "    writeSaved();\n"
                "    assert(cellGet(c) == 1);\n"
                "    cellGet(c)\n"
                "}\n"
                "def main(): Void = { let _ = observe(); () }\n",
            ),
            (
                "z1_wrapped_global",
                "observe",
                "def slot: Cell (Cell Int) = cellNew(cellNew(0))\n"
                "def remember(c: Cell Int): Void = cellSet(slot, c)\n"
                "def writeGlobal(v: Int): Void = cellSet(cellGet(slot), v)\n"
                "def writeSaved(v: Int): Void = writeGlobal(v)\n"
                "def observe(): Int = {\n"
                "    let c = cellNew(0);\n"
                "    remember(c);\n"
                "    cellSet(c, 1);\n"
                "    writeSaved(7);\n"
                "    assert(cellGet(c) == 1);\n"
                "    cellGet(c)\n"
                "}\n"
                "def main(): Void = { let _ = observe(); () }\n",
            ),
            (
                "z1_loop_global",
                "observe",
                "def slot: Cell (Cell Int) = cellNew(cellNew(0))\n"
                "def remember(c: Cell Int): Void = cellSet(slot, c)\n"
                "def writeGlobal(v: Int): Void = cellSet(cellGet(slot), v)\n"
                "def writeSaved(v: Int): Void = writeGlobal(v)\n"
                "def observe(): Int = {\n"
                "    let c = cellNew(0);\n"
                "    remember(c);\n"
                "    cellSet(c, 1);\n"
                "    let flag = cellNew(true);\n"
                "    while (cellGet(flag))\n"
                "        invariant true\n"
                "    {\n"
                "        writeSaved(7);\n"
                "        cellSet(flag, false)\n"
                "    };\n"
                "    assert(cellGet(c) == 1);\n"
                "    cellGet(c)\n"
                "}\n"
                "def main(): Void = { let _ = observe(); () }\n",
            ),
            (
                "z1_victim_callee_ensures",
                "victimCaller",
                "def slot: Cell (Cell Int) = cellNew(cellNew(0))\n"
                "def remember(c: Cell Int): Void = cellSet(slot, c)\n"
                "def writeSaved(): Void = cellSet(cellGet(slot), 7)\n"
                "def bogusHelper(): Int\n"
                "    ensures r -> r == 1\n"
                "= {\n"
                "    let c = cellNew(0);\n"
                "    remember(c);\n"
                "    cellSet(c, 1);\n"
                "    writeSaved();\n"
                "    cellGet(c)\n"
                "}\n"
                "def victimCaller(): Int = {\n"
                "    let v = bogusHelper();\n"
                "    assert(v == 1);\n"
                "    v\n"
                "}\n"
                "def main(): Void = { let _ = victimCaller(); () }\n",
            ),
            (
                "z1_handle_escape",
                "observeHandle",
                "def writeByHandle(h: Int64): Void = cellSet(gcHandleGet(h), 7)\n"
                "def observeHandle(): Int = {\n"
                "    let c = cellNew(0);\n"
                "    let h = gcHandleNew(c);\n"
                "    cellSet(c, 1);\n"
                "    writeByHandle(h);\n"
                "    assert(cellGet(c) == 1);\n"
                "    cellGet(c)\n"
                "}\n"
                "def main(): Void = { let _ = observeHandle(); () }\n",
            ),
        ]:
            z_src = tmp / f"{z_name}.gsa"
            z_src.write_text(z_code, encoding="utf-8", newline="\n")
            r_zv = run([geisha, "verify", "--json", "--solver", z3_bin, str(z_src)])
            assert r_zv.returncode == 1, f"Z1 {z_name} verify MUST fail (exit 1), got {r_zv.returncode}:\n{r_zv.stdout}\n{r_zv.stderr}"
            z_ll = tmp / f"{z_name}.ll"
            r_zir = run([geisha, "--verified-opt", "--solver", z3_bin, "-e", "-o", str(z_ll), str(z_src)])
            assert r_zir.returncode == 0, f"Z1 {z_name} IR compile failed:\n{r_zir.stdout}\n{r_zir.stderr}"
            z_blk = fn_ir_block(z_ll.read_text(encoding="utf-8"), z_target_fn)
            assert "call void @llvm.assume" not in z_blk, f"Z1 {z_name} emitted false @llvm.assume in {z_target_fn}!\n{z_blk}"

        # Z4 Adversarial: extern C functions whose names start with intrinsic prefixes
        # (`math`, `bit`, `bits`, `float`, `f32`, `intToF`) MUST NEVER be treated as local-only intrinsics.
        for ext_nm in ["mathNotify", "bitNotify", "bitsNotify", "floatNotify", "f32Notify", "intToFNotify"]:
            z4_src = tmp / f"z4_{ext_nm}.gsa"
            z4_src.write_text(
                f'extern "review_notify" def {ext_nm}(): Void\n'
                "def slot: Cell (Cell Int) = cellNew(cellNew(0))\n"
                "def remember(c: Cell Int): Void = cellSet(slot, c)\n"
                "def observe(): Int = {\n"
                "    let c = cellNew(0);\n"
                "    remember(c);\n"
                "    cellSet(c, 1);\n"
                f"    {ext_nm}();\n"
                "    assert(cellGet(c) == 1);\n"
                "    cellGet(c)\n"
                "}\n"
                "def main(): Void = { let _ = observe(); () }\n",
                encoding="utf-8",
                newline="\n",
            )
            r_z4v = run([geisha, "verify", "--json", "--solver", z3_bin, str(z4_src)])
            assert r_z4v.returncode == 1, f"Z4 {ext_nm} verify MUST fail (exit 1), got {r_z4v.returncode}:\n{r_z4v.stdout}\n{r_z4v.stderr}"
            z4_ll = tmp / f"z4_{ext_nm}.ll"
            r_z4ir = run([geisha, "--verified-opt", "--solver", z3_bin, "-e", "-o", str(z4_ll), str(z4_src)])
            assert r_z4ir.returncode == 0, f"Z4 {ext_nm} IR compile failed:\n{r_z4ir.stdout}\n{r_z4ir.stderr}"
            z4_blk = fn_ir_block(z4_ll.read_text(encoding="utf-8"), "observe")
            assert "call void @llvm.assume" not in z4_blk, f"Z4 {ext_nm} emitted false @llvm.assume in observe!\n{z4_blk}"

        # Z4 Positive control: genuine pure intrinsics (`bitAnd`, `mathAbs`) MUST NOT trigger spurious cell havoc
        z4_pos_src = tmp / "z4_pure_intrinsics.gsa"
        z4_pos_src.write_text(
            "def observePure(): Int = {\n"
            "    let c = cellNew(1);\n"
            "    let _ = bitAnd(3, 1);\n"
            "    let _ = mathAbs(1.0);\n"
            "    assert(cellGet(c) == 1);\n"
            "    cellGet(c)\n"
            "}\n"
            "def main(): Void = { let _ = observePure(); () }\n",
            encoding="utf-8",
            newline="\n",
        )
        r_z4pv = run([geisha, "verify", "--json", "--solver", z3_bin, str(z4_pos_src)])
        assert r_z4pv.returncode == 0, f"Z4 pure intrinsics verify failed:\n{r_z4pv.stdout}\n{r_z4pv.stderr}"
        z4p_j = json.loads(r_z4pv.stdout)
        assert z4p_j["ok"] is True and z4p_j["failed"] == 0 and z4p_j["unknown"] == 0 and z4p_j["proved"] >= 1, (
            f"Z4 pure intrinsics unexpected summary: {z4p_j}"
        )
        z4p_ll = tmp / "z4_pure_intrinsics.ll"
        r_z4pir = run([geisha, "--verified-opt", "--solver", z3_bin, "-e", "-o", str(z4p_ll), str(z4_pos_src)])
        assert r_z4pir.returncode == 0, f"Z4 pure intrinsics IR compile failed:\n{r_z4pir.stdout}\n{r_z4pir.stderr}"
        z4p_blk = fn_ir_block(z4p_ll.read_text(encoding="utf-8"), "observePure")
        assert "call void @llvm.assume" in z4p_blk, f"Z4 pure intrinsics should still emit @llvm.assume in observePure!\n{z4p_blk}"

        # Z5 Adversarial: explicit `extern` or user `def` declarations MUST shadow built-in intrinsics
        # (`assert`, `bitAnd`, etc.) consistently across verifier, contract lowering, and LLVM codegen.
        z5_c = tmp / "z5_stubs.c"
        z5_c.write_text(
            "#include <stdint.h>\n"
            "void review_assert(int32_t b) { (void)b; }\n"
            "int32_t review_add(int32_t a, int32_t b) { return a + b; }\n",
            encoding="utf-8",
            newline="\n",
        )
        z5_obj = tmp / "z5_stubs.o"
        cc = os.environ.get("CC", "clang")
        cc_base = [cc, "-target", "arm64-apple-macosx14.0"] if sys.platform == "darwin" else [cc]
        r_cc = run([*cc_base, "-c", str(z5_c), "-o", str(z5_obj)])
        assert r_cc.returncode == 0, f"Z5 C stub compile failed:\n{r_cc.stdout}\n{r_cc.stderr}"

        def link_with_z5_stub(ll_path: Path, out_bin: Path) -> None:
            cmd = [*cc_base, "-O2", "-Wno-override-module"]
            if sys.platform != "win32":
                cmd.append("-pthread")
            cmd.extend(["-x", "ir", str(ll_path), "-x", "none", str(z5_obj), runtime])
            if sys.platform.startswith("linux"):
                cmd.append("-lm")
            cmd.extend(["-o", str(out_bin)])
            r_lk = run(cmd)
            assert r_lk.returncode == 0, f"Z5 link failed ({out_bin.name}):\n{r_lk.stdout}\n{r_lk.stderr}"

        # Z5a: `extern "review_assert" def assert(b: Bool): Void`
        z5a_src = tmp / "z5_exact_extern_assert.gsa"
        z5a_src.write_text(
            "use std.str.intToStr\n"
            'extern "review_assert" def assert(b: Bool): Void\n'
            "def observe(): Int = { assert(false); 7 }\n"
            "def main(): Void = printLn(intToStr(observe()))\n",
            encoding="utf-8",
            newline="\n",
        )
        z5a_ll = tmp / "z5a_vopt.ll"
        r_z5a_ir = run([geisha, "--verified-opt", "--solver", z3_bin, "-e", "-o", str(z5a_ll), str(z5a_src)])
        assert r_z5a_ir.returncode == 0, f"Z5a IR compile failed:\n{r_z5a_ir.stdout}\n{r_z5a_ir.stderr}"
        z5a_blk = fn_ir_block(z5a_ll.read_text(encoding="utf-8"), "observe")
        assert "call void @review_assert" in z5a_blk, f"Z5a missing @review_assert call!\n{z5a_blk}"
        assert "call void @llvm.assume" not in z5a_blk, f"Z5a emitted false @llvm.assume!\n{z5a_blk}"
        for mode_lbl, extra_flags in [
            ("default", []),
            ("check", ["--contracts=check"]),
            ("vopt", ["--verified-opt", "--solver", z3_bin]),
        ]:
            z5a_m_ll = tmp / f"z5a_{mode_lbl}.ll"
            z5a_bin = tmp / (f"z5a_{mode_lbl}.exe" if sys.platform == "win32" else f"z5a_{mode_lbl}")
            r_z5a_b = run([geisha, *extra_flags, "-e", "-o", str(z5a_m_ll), str(z5a_src)])
            assert r_z5a_b.returncode == 0, f"Z5a ({mode_lbl}) IR build failed:\n{r_z5a_b.stdout}\n{r_z5a_b.stderr}"
            link_with_z5_stub(z5a_m_ll, z5a_bin)
            r_z5a_r = run([str(z5a_bin)])
            assert r_z5a_r.returncode == 0 and r_z5a_r.stdout.strip() == "7", (
                f"Z5a ({mode_lbl}) expected exit 0 and '7', got rc={r_z5a_r.returncode} out={r_z5a_r.stdout!r} err={r_z5a_r.stderr!r}"
            )

        # Z5b: `extern "review_add" def bitAnd(a: Int, b: Int): Int`
        z5b_src = tmp / "z5_exact_extern_bitand.gsa"
        z5b_src.write_text(
            "use std.str.intToStr\n"
            'extern "review_add" def bitAnd(a: Int, b: Int): Int\n'
            "def observe(a: Int, b: Int): Int = bitAnd(a, b)\n"
            "def main(): Void = printLn(intToStr(observe(3, 5)))\n",
            encoding="utf-8",
            newline="\n",
        )
        for mode_lbl, extra_flags in [("default", []), ("vopt", ["--verified-opt", "--solver", z3_bin])]:
            z5b_m_ll = tmp / f"z5b_{mode_lbl}.ll"
            z5b_bin = tmp / (f"z5b_{mode_lbl}.exe" if sys.platform == "win32" else f"z5b_{mode_lbl}")
            r_z5b_b = run([geisha, *extra_flags, "-e", "-o", str(z5b_m_ll), str(z5b_src)])
            assert r_z5b_b.returncode == 0, f"Z5b ({mode_lbl}) IR build failed:\n{r_z5b_b.stdout}\n{r_z5b_b.stderr}"
            link_with_z5_stub(z5b_m_ll, z5b_bin)
            r_z5b_r = run([str(z5b_bin)])
            assert r_z5b_r.returncode == 0 and r_z5b_r.stdout.strip() == "8", (
                f"Z5b ({mode_lbl}) expected '8' (review_add), got rc={r_z5b_r.returncode} out={r_z5b_r.stdout!r} err={r_z5b_r.stderr!r}"
            )

        # Z5c: user `def assert(b: Bool): Void = ()`
        z5c_src = tmp / "z5_user_def_assert.gsa"
        z5c_src.write_text(
            "use std.str.intToStr\n"
            "def assert(b: Bool): Void = ()\n"
            "def observe(): Int = { assert(false); 7 }\n"
            "def main(): Void = printLn(intToStr(observe()))\n",
            encoding="utf-8",
            newline="\n",
        )
        z5c_ll = tmp / "z5c_vopt.ll"
        r_z5c_ir = run([geisha, "--verified-opt", "--solver", z3_bin, "-e", "-o", str(z5c_ll), str(z5c_src)])
        assert r_z5c_ir.returncode == 0, f"Z5c IR compile failed:\n{r_z5c_ir.stdout}\n{r_z5c_ir.stderr}"
        z5c_blk = fn_ir_block(z5c_ll.read_text(encoding="utf-8"), "observe")
        assert "call void @llvm.assume" not in z5c_blk, f"Z5c emitted false @llvm.assume!\n{z5c_blk}"
        z5c_bin = tmp / "z5c_check"
        r_z5c_b = run([geisha, "--contracts=check", "--runtime", runtime, "-o", str(z5c_bin), str(z5c_src)])
        assert r_z5c_b.returncode == 0, f"Z5c --contracts=check build failed:\n{r_z5c_b.stdout}\n{r_z5c_b.stderr}"
        r_z5c_r = run([str(z5c_bin)])
        assert r_z5c_r.returncode == 0 and r_z5c_r.stdout.strip() == "7", (
            f"Z5c --contracts=check expected '7', got rc={r_z5c_r.returncode} out={r_z5c_r.stdout!r} err={r_z5c_r.stderr!r}"
        )

        # Z5d: genuine built-in `assert(false)` MUST still fail verify and emit no `@llvm.assume`
        z5d_src = tmp / "z5_builtin_assert_false.gsa"
        z5d_src.write_text(
            "def observe(): Int = { assert(false); 7 }\n"
            "def main(): Void = { let _ = observe(); () }\n",
            encoding="utf-8",
            newline="\n",
        )
        r_z5d_v = run([geisha, "verify", "--json", "--solver", z3_bin, str(z5d_src)])
        assert r_z5d_v.returncode == 1, f"Z5d builtin assert(false) MUST fail verify, got {r_z5d_v.returncode}"
        z5d_ll = tmp / "z5d_vopt.ll"
        r_z5d_ir = run([geisha, "--verified-opt", "--solver", z3_bin, "-e", "-o", str(z5d_ll), str(z5d_src)])
        assert r_z5d_ir.returncode == 0
        z5d_blk = fn_ir_block(z5d_ll.read_text(encoding="utf-8"), "observe")
        assert "call void @llvm.assume" not in z5d_blk, f"Z5d builtin assert(false) emitted false @llvm.assume!\n{z5d_blk}"

        # Z6a/Z6c Adversarial: root-module private shadowing (`bitAnd`, `assert`, `cellGet`, `assume`)
        # MUST NOT leak into unimporting sibling modules (`helper.gsa`) or `<builtin>/std.*`,
        # and `--target wasm-gc --contracts=check` must trap on failed assertions.
        z6_mod_dir = tmp / "z6_mod"
        z6_mod_dir.mkdir()
        (z6_mod_dir / "helper.gsa").write_text(
            "pub def libraryBits(a: Int, b: Int): Int = bitAnd(a, b)\n"
            "pub def libraryCheck(b: Bool): Void = assert(b)\n",
            encoding="utf-8",
            newline="\n",
        )
        (z6_mod_dir / "entry.gsa").write_text(
            "use helper.{libraryBits, libraryCheck}\n"
            "use std.str.intToStr\n"
            "def bitAnd(a: Int, b: Int): Int = a + b\n"
            "def assert(b: Bool): Void = ()\n"
            "def main(): Void = { printLn(intToStr(libraryBits(3, 5))); libraryCheck(false) }\n",
            encoding="utf-8",
            newline="\n",
        )
        # Native erase & --verified-opt: helper.libraryBits(3, 5) MUST print 1 (not 8)
        for lbl, extra_flags in [("erase", []), ("vopt", ["--verified-opt", "--solver", z3_bin])]:
            z6_bin = tmp / (f"z6_entry_{lbl}.exe" if sys.platform == "win32" else f"z6_entry_{lbl}")
            r_z6b = run([geisha, *extra_flags, "--src-root", str(z6_mod_dir), "--runtime", runtime, "-o", str(z6_bin), str(z6_mod_dir / "entry.gsa")])
            assert r_z6b.returncode == 0, f"Z6a ({lbl}) build failed:\n{r_z6b.stdout}\n{r_z6b.stderr}"
            r_z6r = run([str(z6_bin)])
            assert r_z6r.returncode == 0 and r_z6r.stdout.strip() == "1", (
                f"Z6a ({lbl}) expected '1', got rc={r_z6r.returncode} out={r_z6r.stdout!r} err={r_z6r.stderr!r}"
            )
        # Native --contracts=check: helper.libraryBits(3, 5) prints 1 AND helper.libraryCheck(false) traps!
        z6_chk_bin = tmp / ("z6_entry_check.exe" if sys.platform == "win32" else "z6_entry_check")
        r_z6cb = run([geisha, "--contracts=check", "--src-root", str(z6_mod_dir), "--runtime", runtime, "-o", str(z6_chk_bin), str(z6_mod_dir / "entry.gsa")])
        assert r_z6cb.returncode == 0, f"Z6a (check) build failed:\n{r_z6cb.stdout}\n{r_z6cb.stderr}"
        r_z6cr = run([str(z6_chk_bin)])
        assert r_z6cr.returncode != 0 and r_z6cr.stdout.strip() == "1" and "Contract error:" in (r_z6cr.stdout + r_z6cr.stderr), (
            f"Z6a (check) expected trap after printing '1', got rc={r_z6cr.returncode} out={r_z6cr.stdout!r} err={r_z6cr.stderr!r}"
        )

        # Z6a: root-module `def cellGet(x: Int): Int = x + 1` with `use std.str.intToStr` MUST compile, verify 2/2, and print 7
        z6_cell_src = tmp / "z6_user_cell_std.gsa"
        z6_cell_src.write_text(
            "use std.str.intToStr\n"
            "def cellGet(x: Int): Int\n"
            "    ensures r -> r == x + 1\n"
            "= x + 1\n"
            "def observe(): Int = { let x = cellGet(6); assert(x == 7); x }\n"
            "def main(): Void = printLn(intToStr(observe()))\n",
            encoding="utf-8",
            newline="\n",
        )
        r_z6cv = run([geisha, "verify", "--json", "--solver", z3_bin, str(z6_cell_src)])
        assert r_z6cv.returncode == 0, f"Z6a user_cell_std verify failed:\n{r_z6cv.stdout}\n{r_z6cv.stderr}"
        z6c_j = json.loads(r_z6cv.stdout)
        assert z6c_j["ok"] is True and z6c_j["failed"] == 0 and z6c_j["unknown"] == 0 and z6c_j["proved"] >= 2, (
            f"Z6a user_cell_std unexpected summary: {z6c_j}"
        )
        z6c_bin = tmp / ("z6_user_cell_std.exe" if sys.platform == "win32" else "z6_user_cell_std")
        r_z6c_b = run([geisha, "--runtime", runtime, "-o", str(z6c_bin), str(z6_cell_src)])
        assert r_z6c_b.returncode == 0, f"Z6a user_cell_std build failed:\n{r_z6c_b.stdout}\n{r_z6c_b.stderr}"
        r_z6c_r = run([str(z6c_bin)])
        assert r_z6c_r.returncode == 0 and r_z6c_r.stdout.strip() == "7", (
            f"Z6a user_cell_std expected '7', got rc={r_z6c_r.returncode} out={r_z6c_r.stdout!r}"
        )

        # Z6a/Z6c: JS & WasmGC `--contracts=check` with root-module shadowing
        node_bin = shutil.which("node")
        if node_bin is not None:
            z6_js = tmp / "z6_entry_check.mjs"
            r_z6js = run([geisha, "--target", "js", "--contracts=check", "--src-root", str(z6_mod_dir), "-o", str(z6_js), str(z6_mod_dir / "entry.gsa")])
            assert r_z6js.returncode == 0, f"Z6a JS check build failed:\n{r_z6js.stdout}\n{r_z6js.stderr}"
            r_z6jsr = run([node_bin, str(z6_js)])
            assert r_z6jsr.returncode != 0 and r_z6jsr.stdout.strip() == "1", (
                f"Z6a JS check expected trap after '1', got rc={r_z6jsr.returncode} out={r_z6jsr.stdout!r} err={r_z6jsr.stderr!r}"
            )

            (z6_mod_dir / "wasm_entry.gsa").write_text(
                "use helper.{libraryBits, libraryCheck}\n"
                "def bitAnd(a: Int, b: Int): Int = a + b\n"
                "def assert(b: Bool): Void = ()\n"
                "pub def probe(): Int = libraryBits(3, 5)\n"
                "pub def demand(): Void = libraryCheck(false)\n"
                "def main(): Void = ()\n",
                encoding="utf-8",
                newline="\n",
            )
            z6_wgc = tmp / "z6_wgc_check.wasm"
            r_z6w = run([geisha, "--target", "wasm-gc", "--contracts=check", "--src-root", str(z6_mod_dir), "-o", str(z6_wgc), str(z6_mod_dir / "wasm_entry.gsa")])
            assert r_z6w.returncode == 0, f"Z6c WasmGC check build failed:\n{r_z6w.stdout}\n{r_z6w.stderr}"
            z6_wgc_runner = tmp / "z6_wgc_run.mjs"
            z6_wgc_runner.write_text(
                f"import {{ probe, demand }} from {(tmp / 'z6_wgc_check.mjs').as_uri()!r};\n"
                "const p = probe();\n"
                "if (p !== 1) { console.error('BAD_PROBE', p); process.exit(2); }\n"
                "let trapped = false;\n"
                "try { demand(); } catch (e) { trapped = true; }\n"
                "if (!trapped) { console.error('NO_TRAP'); process.exit(3); }\n"
                "console.log('WGC_Z6_OK');\n",
                encoding="utf-8",
                newline="\n",
            )
            r_z6wr = run([node_bin, str(z6_wgc_runner)])
            assert r_z6wr.returncode == 0 and "WGC_Z6_OK" in r_z6wr.stdout, (
                f"Z6c WasmGC check runner failed:\nrc={r_z6wr.returncode}\nout={r_z6wr.stdout}\nerr={r_z6wr.stderr}"
            )

        # Z7a Adversarial: `--target wasm32 --verified-opt` WITHOUT `--export` still exports
        # default-exported root functions (`isDefaultWasmExport`), so `requires y > 0` MUST NOT
        # allow eliminating `div.zero` or emitting `@llvm.assume`.
        z7a_src = tmp / "z7a_wasm_default_export.gsa"
        z7a_src.write_text(
            "pub def bitAnd(x: Int, y: Int): Int\n"
            "    requires y > 0\n"
            "= x / y\n"
            "pub def divPositive(x: Int, y: Int): Int\n"
            "    requires y > 0\n"
            "= x / y\n"
            "def main(): Void = { let _ = bitAnd(10, 2); let _ = divPositive(10, 2); () }\n",
            encoding="utf-8",
            newline="\n",
        )
        z7a_ll = tmp / "z7a_wasm.ll"
        r_z7a = run([geisha, "--target", "wasm32", "--verified-opt", "--solver", z3_bin, "-e", "-o", str(z7a_ll), str(z7a_src)])
        assert r_z7a.returncode == 0, f"Z7a wasm32 --verified-opt IR failed:\n{r_z7a.stdout}\n{r_z7a.stderr}"
        z7a_ir = z7a_ll.read_text(encoding="utf-8")
        for z7_fn in ['"$root.bitAnd"', "divPositive"]:
            z7_blk = fn_ir_block(z7a_ir, z7_fn)
            assert "div.zero" in z7_blk, f"Z7a default wasm32 export {z7_fn} elided div.zero!\n{z7_blk}"
            assert "call void @llvm.assume" not in z7_blk, f"Z7a default wasm32 export {z7_fn} emitted @llvm.assume!\n{z7_blk}"

        # Z7c: Native `-c --no-main --export bitAnd` AND `pub extern def bitAnd` on root-shadowed
        # `bitAnd(a, b) = a + b` MUST export C symbol `bitAnd` (not `$root.bitAnd`) and return 8.
        z7c_call_c = tmp / "z7c_call_export.c"
        z7c_call_c.write_text(
            "#include <stdint.h>\n"
            "#include <stdio.h>\n"
            "extern int32_t bitAnd(int32_t a, int32_t b);\n"
            "int main(void) { printf(\"%d\\n\", bitAnd(3, 5)); return 0; }\n",
            encoding="utf-8",
            newline="\n",
        )
        for z7c_lbl, z7c_code, z7c_flags in [
            (
                "cli_export",
                "pub def bitAnd(a: Int, b: Int): Int = a + b\n",
                ["-c", "--no-main", "--export", "bitAnd"],
            ),
            (
                "pub_extern",
                "pub extern def bitAnd(a: Int, b: Int): Int = a + b\n",
                ["-c", "--no-main"],
            ),
        ]:
            z7c_gsa = tmp / f"z7c_{z7c_lbl}.gsa"
            z7c_gsa.write_text(z7c_code, encoding="utf-8", newline="\n")
            z7c_obj = tmp / f"z7c_{z7c_lbl}.o"
            r_z7co = run([geisha, *z7c_flags, "-o", str(z7c_obj), str(z7c_gsa)])
            assert r_z7co.returncode == 0, f"Z7c ({z7c_lbl}) compile -c failed:\n{r_z7co.stdout}\n{r_z7co.stderr}"
            z7c_bin = tmp / (f"z7c_{z7c_lbl}.exe" if sys.platform == "win32" else f"z7c_{z7c_lbl}")
            lk_cmd = [*cc_base, "-O2", str(z7c_call_c), str(z7c_obj), runtime]
            if sys.platform != "win32":
                lk_cmd.append("-pthread")
            if sys.platform.startswith("linux"):
                lk_cmd.append("-lm")
            lk_cmd.extend(["-o", str(z7c_bin)])
            r_z7cl = run(lk_cmd)
            assert r_z7cl.returncode == 0, f"Z7c ({z7c_lbl}) C client link failed:\n{r_z7cl.stdout}\n{r_z7cl.stderr}"
            r_z7cr = run([str(z7c_bin)])
            assert r_z7cr.returncode == 0 and r_z7cr.stdout.strip() == "8", (
                f"Z7c ({z7c_lbl}) expected '8', got rc={r_z7cr.returncode} out={r_z7cr.stdout!r} err={r_z7cr.stderr!r}"
            )

        print("PASS [d3_verified_opt]: positive IR/O2 + Iron Law 1 & 2 + V1-V3 + W1-W4 + X1-X3 + Y1-Y4 + Z1-Z7 adversarial/TCO/eval/zerosorts/mod-shadow/wasmgc-check/wasm-default-exp/native-exp + cache isolation verified")

    # ------------------------------------------------------------------
    # D2: Compiler self-check with `--contracts=check` (`geisha_checked`)
    # (Runs on all platforms, independent of Z3)
    # ------------------------------------------------------------------
    with tempfile.TemporaryDirectory(prefix="geisha_d2_") as td2:
        tmp2 = Path(td2)
        checked_bin = tmp2 / ("geisha_checked.exe" if sys.platform == "win32" else "geisha_checked")
        r_chk_build = run([
            geisha, "--contracts=check", "--src-root", str(repo_root),
            "--runtime", runtime, "-O2", "-o", str(checked_bin),
            str(repo_root / "src" / "geisha.gsa"),
        ])
        assert r_chk_build.returncode == 0, f"D2 geisha_checked build failed:\n{r_chk_build.stdout}\n{r_chk_build.stderr}"
        # Verify contracts are genuinely live (not erased) in geisha_checked
        bin_bytes = checked_bin.read_bytes()
        assert b"Contract error:" in bin_bytes, "D2 geisha_checked binary missing live 'Contract error:' strings!"
        # Self-check the entire compiler under live runtime contracts
        r_self = run([str(checked_bin), "check", "--src-root", str(repo_root), str(repo_root / "src" / "geisha.gsa")])
        assert r_self.returncode == 0, f"D2 geisha_checked self-check failed:\n{r_self.stdout}\n{r_self.stderr}"
        # Multi-backend codegen under live runtime contracts (native IR, wasm-gc, js)
        mini = tmp2 / "d2_mini.gsa"
        mini.write_text(
            "use std.str.{intToStr}\n"
            "def add(a: Int, b: Int): Int = a + b\n"
            "def main(): Void = printLn(intToStr(add(20, 22)))\n",
            encoding="utf-8",
            newline="\n",
        )
        r_nat = run([str(checked_bin), "-e", "-o", str(tmp2 / "mini.ll"), str(mini)])
        assert r_nat.returncode == 0, f"D2 native codegen failed:\n{r_nat.stdout}\n{r_nat.stderr}"
        r_wgc = run([str(checked_bin), "--target", "wasm-gc", "-o", str(tmp2 / "mini.wasm"), str(mini)])
        assert r_wgc.returncode == 0, f"D2 wasm-gc codegen failed:\n{r_wgc.stdout}\n{r_wgc.stderr}"
        r_js = run([str(checked_bin), "--target", "js", "-o", str(tmp2 / "mini.mjs"), str(mini)])
        assert r_js.returncode == 0, f"D2 js codegen failed:\n{r_js.stdout}\n{r_js.stderr}"
        print("PASS [d2_geisha_checked]: live contracts embedded, self-check + native/wasm-gc/js codegen passed")

    return 0


if __name__ == "__main__":
    raise SystemExit(main())
