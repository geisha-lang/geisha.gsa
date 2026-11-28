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

        bad_internal_dollar = tmp / "bad_internal_dollar.gsa"
        bad_internal_dollar.write_text(
            "def main() = $gs$contract_fail(\"nope\")\n",
            encoding="utf-8",
        )
        r = run([geisha, "check", str(bad_internal_dollar)])
        assert r.returncode != 0, "user code must not be able to call internal $gs$contract_fail"
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
        # D1: Production verified kernels in-place inside host compiler modules + `--fn` filter
        # ------------------------------------------------------------------
        host_kernel_specs = [
            (
                repo_root / "src" / "diag.gsa",
                ["clampOffset", "clampSpanEnd", "hexDigitUpperByte", "hexNibbleVal"],
            ),
            (
                repo_root / "src" / "codegen.gsa",
                ["alignUp8", "alignUp16", "bitmapWordIdx", "bitmapBitMask"],
            ),
            (
                repo_root / "src" / "codegen_wasmgc.gsa",
                [
                    "uleb32Next", "uleb32Byte", "uleb32Len",
                    "sleb32Done", "sleb32Next", "sleb32Byte", "sleb32Len",
                    "sleb64Done", "sleb64Next", "sleb64Byte", "sleb64Len",
                ],
            ),
            (
                repo_root / "src" / "core.gsa",
                [
                    "coFreshNextId", "coFreshBatchEnd", "coFlatTotalArity",
                    "coSpecSlotStepArity", "coAnfInFloatPrefix", "coPatSeqStatus", "coInlineBudgetAllows",
                ],
            ),
        ]
        total_vk_proved = 0
        for host_path, fn_names in host_kernel_specs:
            fn_args: list[str] = []
            for fn_nm in fn_names:
                fn_args.extend(["--fn", fn_nm])
            r_vk = run([geisha, "verify", "--json", "--solver", z3_bin, "--src-root", str(repo_root), *fn_args, str(host_path)])
            assert r_vk.returncode == 0, f"D1 {host_path.name} verify failed:\n{r_vk.stdout}\n{r_vk.stderr}"
            vk_json = json.loads(r_vk.stdout)
            assert vk_json["ok"] is True and vk_json["failed"] == 0 and vk_json["unknown"] == 0 and vk_json["proved"] >= len(fn_names), (
                f"D1 unexpected {host_path.name} summary: {vk_json}"
            )
            total_vk_proved += vk_json["proved"]
        assert total_vk_proved >= 40, f"D1 expected >= 40 proved kernel obligations across host modules, got {total_vk_proved}"
        r_vk_sub = run([
            geisha, "verify", "--json", "--solver", z3_bin, "--src-root", str(repo_root),
            "--fn", "clampOffset", str(repo_root / "src" / "diag.gsa"),
        ])
        assert r_vk_sub.returncode == 0
        vk_sub_json = json.loads(r_vk_sub.stdout)
        assert vk_sub_json["ok"] is True and vk_sub_json["functions"] == 1 and vk_sub_json["proved"] >= 1
        r_vk_miss = run([
            geisha, "verify", "--json", "--solver", z3_bin, "--src-root", str(repo_root),
            "--fn", "definitely_not_a_real_fn_xyz", str(repo_root / "src" / "diag.gsa"),
        ])
        assert r_vk_miss.returncode != 0, f"D1 --fn nonexistent should fail, got 0:\n{r_vk_miss.stdout}"
        print(f"PASS [d1_verified_kernels]: {total_vk_proved} obligations proved in-place across 4 compiler host modules, --fn filter verified")

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

        # D4: Interoperability between `--verified-opt` (`safeFns` check elision + `@llvm.assume`)
        # and Core HOF optimizations (`$spec$` loop specialization + `$flat$` closure devirtualization)
        d4_src = tmp / "d4_hof_verified_opt.gsa"
        d4_src.write_text(
            "use std.option.{Option, Some, None}\n"
            "use std.str.intToStr\n"
            "def safeScale(x: Int, d: Int): Int\n"
            "    requires d != 0\n"
            "= (x * 10) / d\n"
            "def verifiedEntry(x: Int): Int = {\n"
            "    let c = if (x < 0) 0 else if (x > 1000) 1000 else x;\n"
            "    safeScale(c, 5)\n"
            "}\n"
            "def foldScaleLoop(xs: List Int, acc: Int, cb: Int -> Int): Int = match xs {\n"
            "    Nil -> acc,\n"
            "    Cons(h, t) -> foldScaleLoop(t, acc + cb(h), cb),\n"
            "}\n"
            "def runMixed(bias: Int): Int = {\n"
            "    let b = match Some(bias) { Some(v) -> v, None -> 0 };\n"
            "    let cls = (elem: Int) -> verifiedEntry(elem) + b;\n"
            "    let loopCls = (z: Int) -> {\n"
            "        let cur = cellNew(0);\n"
            "        while (cellGet(cur) < z) {\n"
            "            cellSet(cur, cellGet(cur) + b)\n"
            "        };\n"
            "        cellGet(cur)\n"
            "    };\n"
            "    foldScaleLoop([1, 2, 3, 4], 0, cls) + loopCls(5)\n"
            "}\n"
            "def main(): Void = printLn(intToStr(runMixed(3)))\n",
            encoding="utf-8",
            newline="\n",
        )
        d4_ll = tmp / "d4_hof_verified_opt.ll"
        r_d4_ir = run([geisha, "--verified-opt", "--solver", z3_bin, "-O2", "-e", "-o", str(d4_ll), str(d4_src)])
        assert r_d4_ir.returncode == 0, f"D4 HOF + --verified-opt IR failed:\n{r_d4_ir.stdout}\n{r_d4_ir.stderr}"
        d4_ir_txt = d4_ll.read_text(encoding="utf-8")
        d4_scale_blk = fn_ir_block(d4_ir_txt, "safeScale")
        assert "call void @llvm.assume(i1" in d4_scale_blk, f"D4 safeScale missing @llvm.assume:\n{d4_scale_blk}"
        assert "div.zero" not in d4_scale_blk, f"D4 safeScale did not elide div.zero:\n{d4_scale_blk}"
        assert "foldScaleLoop$spec$" in d4_ir_txt, "D4 expected foldScaleLoop$spec$ specialization under --verified-opt -O2!"
        assert "$flat$" in d4_ir_txt, "D4 expected $flat$ closure devirtualization under --verified-opt -O2!"
        d4_bin = tmp / ("d4_hof_verified_opt.exe" if sys.platform == "win32" else "d4_hof_verified_opt")
        r_d4_b = run([geisha, "--verified-opt", "--solver", z3_bin, "--runtime", runtime, "-O2", "-o", str(d4_bin), str(d4_src)])
        assert r_d4_b.returncode == 0, f"D4 HOF + --verified-opt build failed:\n{r_d4_b.stdout}\n{r_d4_b.stderr}"
        r_d4_r = run([str(d4_bin)])
        assert r_d4_r.returncode == 0 and r_d4_r.stdout.strip() == "38", (
            f"D4 expected '38', got rc={r_d4_r.returncode} out={r_d4_r.stdout!r} err={r_d4_r.stderr!r}"
        )
        # D4b: Verified tiny leaf (`plusOne` in `safeFns`) MUST NOT be inlined into an unverified
        # caller (`caller` excluded due to `assume(true)`) or global initializer under `--verified-opt -O2`.
        d4b_src = tmp / "d4b_leaf_boundary.gsa"
        d4b_src.write_text(
            "use std.str.intToStr\n"
            "def plusOne(x: Int): Int\n"
            "    ensures r -> r == x + 1\n"
            "= x + 1\n"
            "def caller(x: Int): Int = { assume(true); plusOne(x) }\n"
            "def main(): Void = printLn(intToStr(caller(cellGet(cellNew(4)))))\n",
            encoding="utf-8",
            newline="\n",
        )
        d4b_ll = tmp / "d4b_leaf_boundary.ll"
        r_d4b_ir = run([geisha, "--verified-opt", "--solver", z3_bin, "-O2", "-e", "-o", str(d4b_ll), str(d4b_src)])
        assert r_d4b_ir.returncode == 0, f"D4b leaf boundary IR failed:\n{r_d4b_ir.stdout}\n{r_d4b_ir.stderr}"
        d4b_caller_blk = fn_ir_block(d4b_ll.read_text(encoding="utf-8"), "caller")
        assert "@plusOne(" in d4b_caller_blk, (
            f"D4b safeFns tiny leaf plusOne was inlined into unverified caller!\n{d4b_caller_blk}"
        )
        print("PASS [d4_hof_opt_verification]: --verified-opt safeScale elision + safeFns boundary + $spec$ & $flat$ HOF specialization verified")

        # ------------------------------------------------------------------
        # E1: `geisha test` & `geisha test --doc` enable `--contracts=check` by default
        # ------------------------------------------------------------------
        e1_proj = tmp / "e1_test_contracts"
        (e1_proj / "src").mkdir(parents=True)
        (e1_proj / "tests").mkdir(parents=True)
        (e1_proj / "geisha.toml").write_text('name = "e1_test_contracts"\nversion = "0.1.0"\n', encoding="utf-8")
        (e1_proj / "src" / "main.gsa").write_text(
            "/// ```geisha\n"
            "/// assert(1 + 1 == 3)\n"
            "/// ```\n"
            "pub def brokenDocFn(x: Int): Int\n"
            "    requires x > 0\n"
            "= x + 1\n"
            "def main(): Void = ()\n",
            encoding="utf-8",
            newline="\n",
        )
        (e1_proj / "tests" / "test_contracts_live.gsa").write_text(
            "def posOnly(x: Int): Int\n"
            "    requires x > 0\n"
            "= x\n"
            "def main(): Void = { let _ = posOnly(-3); () }\n",
            encoding="utf-8",
            newline="\n",
        )
        r_e1_t = subprocess.run([geisha_abs, "test", "--runtime", runtime_abs], cwd=e1_proj, capture_output=True, text=True)
        assert r_e1_t.returncode != 0 and "Contract error:" in (r_e1_t.stdout + r_e1_t.stderr), (
            f"E1 `geisha test` must enforce contracts by default:\nrc={r_e1_t.returncode}\nout={r_e1_t.stdout}\nerr={r_e1_t.stderr}"
        )
        r_e1_te = subprocess.run([geisha_abs, "test", "--contracts=erase", "--runtime", runtime_abs], cwd=e1_proj, capture_output=True, text=True)
        assert r_e1_te.returncode == 0, f"E1 `geisha test --contracts=erase` should elide contracts:\n{r_e1_te.stdout}\n{r_e1_te.stderr}"
        r_e1_doc = subprocess.run([geisha_abs, "test", "--doc", "--runtime", runtime_abs], cwd=e1_proj, capture_output=True, text=True)
        assert r_e1_doc.returncode != 0, f"E1 `geisha test --doc` must enforce assert/contracts by default:\n{r_e1_doc.stdout}\n{r_e1_doc.stderr}"
        r_e1_doce = subprocess.run([geisha_abs, "test", "--doc", "--contracts=erase", "--runtime", runtime_abs], cwd=e1_proj, capture_output=True, text=True)
        assert r_e1_doce.returncode == 0, f"E1 `geisha test --doc --contracts=erase` should pass:\n{r_e1_doce.stdout}\n{r_e1_doce.stderr}"
        print("PASS [e1_test_and_doctest_default_contracts]")

        # ------------------------------------------------------------------
        # E2: In-place `[pub] verified def`, `--all`, `geisha fmt`, `geisha doc`, and non-fn rejection
        # ------------------------------------------------------------------
        e2_mixed = tmp / "e2_mixed_verified.gsa"
        e2_mixed.write_text(
            "pub verified def clampUnit(x: Int): Int\n"
            "    ensures r -> 0 <= r && r <= 100\n"
            "= if (x < 0) 0 else if (x > 100) 100 else x\n"
            "\n"
            "verified def doubleBounded(x: Int): Int\n"
            "    requires 0 <= x && x <= 50\n"
            "    ensures r -> 0 <= r && r <= 100 && r == x * 2\n"
            "= x * 2\n"
            "\n"
            "pub def unverifiedCrash(x: Int): Int = 100 / x\n"
            "\n"
            "def main(): Void = ()\n",
            encoding="utf-8",
            newline="\n",
        )
        r_e2_def = run([geisha, "verify", "--json", "--solver", z3_bin, str(e2_mixed)])
        assert r_e2_def.returncode == 0, f"E2 selective `verified def` failed:\n{r_e2_def.stdout}\n{r_e2_def.stderr}"
        e2_j = json.loads(r_e2_def.stdout)
        assert e2_j["ok"] is True and e2_j["functions"] == 2 and e2_j["proved"] == 2, f"E2 unexpected selective summary: {e2_j}"
        r_e2_all = run([geisha, "verify", "--all", "--json", "--solver", z3_bin, str(e2_mixed)])
        assert r_e2_all.returncode == 1, f"E2 `--all` must also check unverifiedCrash and catch div_by_zero:\n{r_e2_all.stdout}"
        r_e2_doc = run([geisha, "doc", str(e2_mixed)])
        assert r_e2_doc.returncode == 0 and "pub verified def clampUnit" in r_e2_doc.stdout, (
            f"E2 `geisha doc` missing `pub verified def`:\n{r_e2_doc.stdout}"
        )
        r_e2_fmt = run([geisha, "fmt", "--stdout", str(e2_mixed)])
        assert r_e2_fmt.returncode == 0 and "pub verified def clampUnit" in r_e2_fmt.stdout and "\nverified def doubleBounded" in r_e2_fmt.stdout, (
            f"E2 `geisha fmt` mangled `verified def`:\n{r_e2_fmt.stdout}"
        )
        e2_bad_const = tmp / "e2_bad_const.gsa"
        e2_bad_const.write_text("verified def NOT_A_FN: Int = 42\ndef main() = ()\n", encoding="utf-8")
        r_e2_bad = run([geisha, "check", str(e2_bad_const)])
        assert r_e2_bad.returncode != 0 and "at byte " not in (r_e2_bad.stdout + r_e2_bad.stderr), (
            f"E2 non-function `verified def` must be rejected cleanly:\n{r_e2_bad.stdout}\n{r_e2_bad.stderr}"
        )
        print("PASS [e2_inplace_verified_def_all_doc_fmt]")

        # ------------------------------------------------------------------
        # E3: Concept-constrained generic seeding (`Ord`/`Eq`/`Add` + fundep) & unseedable `unknown`
        # ------------------------------------------------------------------
        e3_pos = tmp / "e3_generic_pos.gsa"
        e3_pos.write_text(
            "pub def genericMax(a: t, b: t): t\n"
            "    ensures r -> r >= a && r >= b && (r == a || r == b)\n"
            "= if (a >= b) a else b\n"
            "\n"
            "pub def genericDouble(x: t): t\n"
            "    ensures r -> r == x + x\n"
            "= x + x\n"
            "\n"
            "def main(): Void = ()\n",
            encoding="utf-8",
            newline="\n",
        )
        r_e3p = run([geisha, "verify", "--json", "--solver", z3_bin, str(e3_pos)])
        assert r_e3p.returncode == 0, f"E3 constrained generic positive failed:\n{r_e3p.stdout}\n{r_e3p.stderr}"
        e3p_j = json.loads(r_e3p.stdout)
        assert e3p_j["ok"] is True and e3p_j["proved"] >= 2, f"E3 expected seeded obligations, got {e3p_j}"
        r_e3_fn = run([geisha, "verify", "--json", "--solver", z3_bin, "--fn", "genericMax", str(e3_pos)])
        assert r_e3_fn.returncode == 0 and json.loads(r_e3_fn.stdout)["proved"] == 1

        e3_bug = tmp / "e3_generic_bug.gsa"
        e3_bug.write_text(
            "pub def badGenericClamp(x: t, lo: t, hi: t): t\n"
            "    requires lo <= hi\n"
            "    ensures r -> lo <= r && r <= hi\n"
            "= if (x < lo) lo else if (x > hi) lo - hi else x\n"
            "def main(): Void = ()\n",
            encoding="utf-8",
            newline="\n",
        )
        r_e3b = run([geisha, "verify", "--json", "--solver", z3_bin, str(e3_bug)])
        assert r_e3b.returncode == 1 and json.loads(r_e3b.stdout)["failed"] >= 1, (
            f"E3 broken constrained generic MUST be caught (not silently skipped!):\n{r_e3b.stdout}"
        )

        e3_unseed = tmp / "e3_unseedable_poly.gsa"
        e3_unseed.write_text(
            "concept Exotic a { exoticVal: a -> Int }\n"
            "pub def uncalledExotic(x: a): Int\n"
            "    ensures r -> r > 0\n"
            "= exoticVal(x)\n"
            "def main(): Void = ()\n",
            encoding="utf-8",
            newline="\n",
        )
        r_e3u = run([geisha, "verify", "--json", "--solver", z3_bin, str(e3_unseed)])
        assert r_e3u.returncode == 1 and json.loads(r_e3u.stdout)["unknown"] >= 1, (
            f"E3 unseedable generic MUST report unknown instead of vacuous VERIFIED:\n{r_e3u.stdout}"
        )
        print("PASS [e3_constrained_generic_seeding_and_unseedable_guard]")

        # ------------------------------------------------------------------
        # E4: Composite types (`Option`/`Result`/`Tuple`/`Struct`/Sum) & zero fake counterexamples
        # ------------------------------------------------------------------
        e4_comp = tmp / "e4_composites.gsa"
        e4_comp.write_text(
            "use std.option.{Option, Some, None}\n"
            "use std.result.{Result, Ok, Err}\n"
            "\n"
            "data RangeSpan { RangeSpan { lo: Int, hi: Int } }\n"
            "data Either { Left(Int), Right(Bool) }\n"
            "\n"
            "def safeHead(arr: ImmArray Int): Option Int\n"
            "    ensures r -> match r {\n"
            "        Some(v) -> immArrayLen(arr) > 0 && v == immArrayGet(arr, 0),\n"
            "        None -> immArrayLen(arr) == 0,\n"
            "    }\n"
            "= if (immArrayLen(arr) > 0) Some(immArrayGet(arr, 0)) else None\n"
            "\n"
            "def minMax(a: Int, b: Int): (Int, Int)\n"
            "    ensures p -> match p {\n"
            "        (lo, hi) -> lo <= hi && ((lo == a && hi == b) || (lo == b && hi == a)),\n"
            "    }\n"
            "= if (a <= b) (a, b) else (b, a)\n"
            "\n"
            "def orderedSpan(a: Int, b: Int): RangeSpan\n"
            "    ensures s -> s.lo <= s.hi\n"
            "= if (a <= b) RangeSpan { lo: a, hi: b } else RangeSpan { lo: b, hi: a }\n"
            "\n"
            "def checkNonNeg(x: Int): Result Int String\n"
            "    ensures r -> match r {\n"
            "        Ok(v) -> x >= 0 && v == x,\n"
            "        Err(msg) -> x < 0 && strLen(msg) > 0,\n"
            "    }\n"
            "= if (x >= 0) Ok(x) else Err(\"negative\")\n"
            "\n"
            "def bumpIfNonNeg(x: Int): Result Int String\n"
            "    requires x < 1000\n"
            "    ensures r -> match r {\n"
            "        Ok(v) -> x >= 0 && v == x + 1,\n"
            "        Err(_) -> x < 0,\n"
            "    }\n"
            "= {\n"
            "    let base = checkNonNeg(x)?;\n"
            "    Ok(base + 1)\n"
            "}\n"
            "\n"
            "def evalEither(flag: Bool): Int\n"
            "    ensures r -> r == 7\n"
            "= {\n"
            "    let e = if (flag) Left(7) else Right(true);\n"
            "    match e {\n"
            "        Left(n) -> n,\n"
            "        Right(b) -> if (b) 7 else 0,\n"
            "    }\n"
            "}\n"
            "\n"
            "def main(): Void = ()\n",
            encoding="utf-8",
            newline="\n",
        )
        r_e4 = run([geisha, "verify", "--json", "--solver", z3_bin, str(e4_comp)])
        assert r_e4.returncode == 0, f"E4 composite verification failed:\n{r_e4.stdout}\n{r_e4.stderr}"
        e4_j = json.loads(r_e4.stdout)
        assert e4_j["ok"] is True and e4_j["failed"] == 0 and e4_j["unknown"] == 0 and e4_j["proved"] >= 7, f"E4 unexpected: {e4_j}"

        # Unmodeled Float return MUST report `unknown` without a fabricated counterexample, and failed counterexamples hide `.tmp*`/`.iff_*`
        e4_unmod = tmp / "e4_unmod_no_fake_ce.gsa"
        e4_unmod.write_text(
            "def halfFloat(x: Float): Float\n"
            "    ensures r -> r == x\n"
            "= x\n"
            "def main(): Void = ()\n",
            encoding="utf-8",
            newline="\n",
        )
        r_e4u = run([geisha, "verify", "--json", "--solver", z3_bin, str(e4_unmod)])
        assert r_e4u.returncode == 1
        e4u_j = json.loads(r_e4u.stdout)
        assert e4u_j["failed"] == 0 and e4u_j["unknown"] == 1 and "counterexample" not in e4u_j["obligations"][0], (
            f"E4 unmodeled return emitted fake failed counterexample: {e4u_j}"
        )

        e4_ce_clean = tmp / "e4_ce_clean.gsa"
        e4_ce_clean.write_text(
            "def badIff(a: Bool, b: Bool): Bool\n"
            "    ensures r -> r\n"
            "= { let _ = (a <==> b); a && b }\n"
            "def main(): Void = ()\n",
            encoding="utf-8",
            newline="\n",
        )
        r_e4c = run([geisha, "verify", "--json", "--solver", z3_bin, str(e4_ce_clean)])
        assert r_e4c.returncode == 1
        e4c_ce = json.loads(r_e4c.stdout)["obligations"][0].get("counterexample", {})
        assert all(not k.startswith((".", "__", "$")) for k in e4c_ce), f"E4 internal var leaked into counterexample: {e4c_ce}"
        print("PASS [e4_composite_types_and_no_fake_counterexamples]")

        # ------------------------------------------------------------------
        # E5: Pure helper 1-step unfolding + UF congruence + `--verified-opt` & heap-read soundness
        # ------------------------------------------------------------------
        e5_pure = tmp / "e5_pure_helpers.gsa"
        e5_pure.write_text(
            "use std.option.{Option, Some, None}\n"
            "\n"
            "def inByteRange(x: Int): Bool = 0 <= x && x < 256\n"
            "def sq(x: Int): Int = x * x\n"
            "def maybePos(x: Int): Option Int = if (x > 0) Some(x) else None\n"
            "\n"
            "def fib(n: Int): Int\n"
            "    requires n >= 0\n"
            "    decreases n\n"
            "= if (n <= 1) n else fib(n - 1) + fib(n - 2)\n"
            "\n"
            "def usePureHelpers(a: Int, b: Int, n: Int): Int\n"
            "    requires inByteRange(a) && a == b && n >= 0\n"
            "    ensures r -> 0 <= r && r < 256\n"
            "= {\n"
            "    assert(sq(a) == sq(b));\n"
            "    assert(fib(n) == fib(n));\n"
            "    assert(fib(0) == 0 && fib(1) == 1);\n"
            "    match maybePos(5) {\n"
            "        Some(v) -> assert(v == 5),\n"
            "        None -> assert(false),\n"
            "    };\n"
            "    a\n"
            "}\n"
            "def main(): Void = ()\n",
            encoding="utf-8",
            newline="\n",
        )
        r_e5 = run([geisha, "verify", "--json", "--solver", z3_bin, str(e5_pure)])
        assert r_e5.returncode == 0, f"E5 pure helper unfolding & congruence failed:\n{r_e5.stdout}\n{r_e5.stderr}"
        assert json.loads(r_e5.stdout)["ok"] is True

        # Adversarial: heap-reading helper MUST NOT get pure mathematical UF across cellSet!
        e5_heap_uf = tmp / "e5_heap_reader.gsa"
        e5_heap_uf.write_text(
            "def readIt(c: Cell Int): Int = cellGet(c)\n"
            "def badCaller(): Void = {\n"
            "    let c = cellNew(1);\n"
            "    let v1 = readIt(c);\n"
            "    cellSet(c, 2);\n"
            "    let v2 = readIt(c);\n"
            "    assert(v1 == v2)\n"
            "}\n"
            "def main(): Void = ()\n",
            encoding="utf-8",
            newline="\n",
        )
        r_e5h = run([geisha, "verify", "--json", "--solver", z3_bin, str(e5_heap_uf)])
        assert r_e5h.returncode == 1 and json.loads(r_e5h.stdout)["failed"] >= 1, (
            f"E5 heap-reading helper unsoundly treated as state-independent UF:\n{r_e5h.stdout}"
        )

        # Adversarial `--verified-opt`: unproved trapping/diverging helper MUST NOT unlock `@llvm.assume` in caller
        e5_vopt_adv = tmp / "e5_vopt_unproved_helper.gsa"
        e5_vopt_adv.write_text(
            "def unprovedPure(x: Int): Int = 100 / x\n"
            "def victimCaller(): Int = {\n"
            "    let v = unprovedPure(0);\n"
            "    assert(v == unprovedPure(0));\n"
            "    v\n"
            "}\n"
            "def main(): Void = { let _ = victimCaller(); () }\n",
            encoding="utf-8",
            newline="\n",
        )
        e5_vopt_ll = tmp / "e5_vopt.ll"
        r_e5_ir = run([geisha, "--verified-opt", "--solver", z3_bin, "-e", "-o", str(e5_vopt_ll), str(e5_vopt_adv)])
        assert r_e5_ir.returncode == 0
        e5_vic_blk = fn_ir_block(e5_vopt_ll.read_text(encoding="utf-8"), "victimCaller")
        assert "call void @llvm.assume" not in e5_vic_blk, f"E5 unproved pure helper leaked @llvm.assume!\n{e5_vic_blk}"
        print("PASS [e5_pure_helper_unfolding_uf_and_vopt_guard]")

        # ------------------------------------------------------------------
        # E6: `old(expr)` pre-state snapshots & `==>` / `<==>` in `verify` and `--contracts=check`
        # ------------------------------------------------------------------
        e6_old = tmp / "e6_old_and_implies.gsa"
        e6_old.write_text(
            "def addInPlace(c: Cell Int, delta: Int): Void\n"
            "    requires cellGet(c) >= 0 && cellGet(c) <= 1000 && delta >= 0 && delta <= 1000\n"
            "    ensures cellGet(c) == old(cellGet(c)) + delta\n"
            "= cellSet(c, cellGet(c) + delta)\n"
            "\n"
            "def bumpSlot(arr: MutArray Int, idx: Int): Void\n"
            "    requires 0 <= idx && idx < arrayLen(arr) && arrayGet(arr, idx) < 10000\n"
            "    ensures arrayGet(arr, idx) == old(arrayGet(arr, idx)) + 1\n"
            "= arraySet(arr, idx, arrayGet(arr, idx) + 1)\n"
            "\n"
            "def shortCircuitImplies(x: Int): Bool\n"
            "    ensures r -> r\n"
            "= (x != 0 && x != -2147483648 ==> (x / x == 1)) && ((false ==> false ==> true) <==> true)\n"
            "\n"
            "def modularOldCaller(): Void = {\n"
            "    let c = cellNew(10);\n"
            "    addInPlace(c, 5);\n"
            "    assert(cellGet(c) == 15);\n"
            "    let a = arrayNew(2, 20);\n"
            "    bumpSlot(a, 1);\n"
            "    assert(arrayGet(a, 1) == 21)\n"
            "}\n"
            "\n"
            "def main(): Void = {\n"
            "    modularOldCaller();\n"
            "    assert(shortCircuitImplies(0));\n"
            "    assert(shortCircuitImplies(7))\n"
            "}\n",
            encoding="utf-8",
            newline="\n",
        )
        r_e6v = run([geisha, "verify", "--json", "--solver", z3_bin, str(e6_old)])
        assert r_e6v.returncode == 0, f"E6 old() + ==> verify failed:\n{r_e6v.stdout}\n{r_e6v.stderr}"
        assert json.loads(r_e6v.stdout)["ok"] is True
        e6_bin = tmp / ("e6_old_chk.exe" if sys.platform == "win32" else "e6_old_chk")
        r_e6b = run([geisha, "--contracts=check", "--runtime", runtime, "-o", str(e6_bin), str(e6_old)])
        assert r_e6b.returncode == 0, f"E6 --contracts=check build failed:\n{r_e6b.stdout}\n{r_e6b.stderr}"
        r_e6r = run([str(e6_bin)])
        assert r_e6r.returncode == 0, f"E6 --contracts=check execution failed:\n{r_e6r.stdout}\n{r_e6r.stderr}"

        # Runtime `--contracts=check` MUST catch violated `old(arrayGet(arr, idx))` postcondition!
        e6_bad_rt = tmp / "e6_bad_old_rt.gsa"
        e6_bad_rt.write_text(
            "def wrongBump(arr: MutArray Int, idx: Int): Void\n"
            "    requires 0 <= idx && idx < arrayLen(arr)\n"
            "    ensures arrayGet(arr, idx) == old(arrayGet(arr, idx)) + 1\n"
            "= arraySet(arr, idx, arrayGet(arr, idx) + 2)\n"
            "def main(): Void = { let a = arrayNew(2, 10); wrongBump(a, 0) }\n",
            encoding="utf-8",
            newline="\n",
        )
        e6_bad_bin = tmp / ("e6_bad_old.exe" if sys.platform == "win32" else "e6_bad_old")
        assert run([geisha, "--contracts=check", "--runtime", runtime, "-o", str(e6_bad_bin), str(e6_bad_rt)]).returncode == 0
        r_e6_bad_run = run([str(e6_bad_bin)])
        assert r_e6_bad_run.returncode != 0 and "Contract error: ensures violated" in (r_e6_bad_run.stdout + r_e6_bad_run.stderr)

        # Negative static checks for invalid `old(...)`
        for bad_old_lbl, bad_old_code in [
            ("old_in_body", "def f(x: Int): Int = old(x)\ndef main() = ()\n"),
            ("nested_old", "def f(c: Cell Int): Void\n    ensures cellGet(c) == old(old(cellGet(c)))\n= ()\ndef main() = ()\n"),
            ("old_ret_bind", "def f(x: Int): Int\n    ensures r -> r == old(r)\n= x\ndef main() = ()\n"),
        ]:
            bo_path = tmp / f"e6_{bad_old_lbl}.gsa"
            bo_path.write_text(bad_old_code, encoding="utf-8")
            assert run([geisha, "check", str(bo_path)]).returncode != 0, f"E6 {bad_old_lbl} must fail typecheck"
        print("PASS [e6_old_snapshots_and_implication]")

        # ------------------------------------------------------------------
        # E7: First-order quantifiers (`forall` / `exists`) in `verify`, `--contracts=check`, and `fmt`
        # ------------------------------------------------------------------
        e7_quant = tmp / "e7_quantifiers.gsa"
        e7_quant.write_text(
            "def zeroFill(arr: MutArray Int): Void\n"
            "    ensures forall (k: Int) -> (0 <= k && k < arrayLen(arr)) ==> arrayGet(arr, k) == 0\n"
            "= {\n"
            "    let n = arrayLen(arr);\n"
            "    let i = cellNew(0);\n"
            "    while (cellGet(i) < n)\n"
            "        invariant 0 <= cellGet(i) && cellGet(i) <= n\n"
            "        invariant forall (k: Int) -> (0 <= k && k < cellGet(i)) ==> arrayGet(arr, k) == 0\n"
            "        decreases n - cellGet(i)\n"
            "    {\n"
            "        arraySet(arr, cellGet(i), 0);\n"
            "        cellSet(i, cellGet(i) + 1)\n"
            "    }\n"
            "}\n"
            "\n"
            "def witnessExists(): Int\n"
            "    ensures r -> r == 7\n"
            "= {\n"
            "    let exists = 7;\n"
            "    let a = arrayNew(3, 0);\n"
            "    arraySet(a, 1, 42);\n"
            "    assert(exists (k: Int) -> 0 <= k && k < arrayLen(a) && arrayGet(a, k) == 42);\n"
            "    exists\n"
            "}\n"
            "\n"
            "def main(): Void = {\n"
            "    let a = arrayNew(4, 9);\n"
            "    zeroFill(a);\n"
            "    let _ = witnessExists();\n"
            "    ()\n"
            "}\n",
            encoding="utf-8",
            newline="\n",
        )
        r_e7v = run([geisha, "verify", "--json", "--solver", z3_bin, str(e7_quant)])
        assert r_e7v.returncode == 0, f"E7 quantifier verify failed:\n{r_e7v.stdout}\n{r_e7v.stderr}"
        assert json.loads(r_e7v.stdout)["ok"] is True

        # Format idempotence on `forall` / `exists` / `==>`
        r_e7_fmt1 = run([geisha, "fmt", "--stdout", str(e7_quant)])
        assert r_e7_fmt1.returncode == 0
        e7_fmt_copy = tmp / "e7_quant_fmt.gsa"
        e7_fmt_copy.write_text(r_e7_fmt1.stdout, encoding="utf-8", newline="\n")
        r_e7_fmt2 = run([geisha, "fmt", "--stdout", str(e7_fmt_copy)])
        assert r_e7_fmt2.returncode == 0 and r_e7_fmt2.stdout == r_e7_fmt1.stdout, "E7 fmt not idempotent on quantifiers!"

        # Runtime `--contracts=check` on bounded `forall` / `exists` (positive + violated trap)
        e7_bin = tmp / ("e7_quant_chk.exe" if sys.platform == "win32" else "e7_quant_chk")
        assert run([geisha, "--contracts=check", "--runtime", runtime, "-o", str(e7_bin), str(e7_quant)]).returncode == 0
        assert run([str(e7_bin)]).returncode == 0

        e7_bad_rt = tmp / "e7_bad_quant_rt.gsa"
        e7_bad_rt.write_text(
            "def checkAllPos(arr: ImmArray Int): Void\n"
            "    requires forall (i: Int) -> (0 <= i && i < immArrayLen(arr)) ==> immArrayGet(arr, i) > 0\n"
            "= ()\n"
            "def main(): Void = {\n"
            "    let a = arrayNew(3, 5);\n"
            "    arraySet(a, 2, -1);\n"
            "    checkAllPos(arrayFreeze(a))\n"
            "}\n",
            encoding="utf-8",
            newline="\n",
        )
        e7_bad_bin = tmp / ("e7_bad_quant.exe" if sys.platform == "win32" else "e7_bad_quant")
        assert run([geisha, "--contracts=check", "--runtime", runtime, "-o", str(e7_bad_bin), str(e7_bad_rt)]).returncode == 0
        r_e7_br = run([str(e7_bad_bin)])
        assert r_e7_br.returncode != 0 and "Contract error: requires violated" in (r_e7_br.stdout + r_e7_br.stderr)

        # Negative: unguarded arrayGet inside `forall` MUST fail implicit bounds check!
        e7_oob_q = tmp / "e7_oob_quant.gsa"
        e7_oob_q.write_text(
            "def badQuantBounds(arr: ImmArray Int): Void\n"
            "    requires forall (i: Int) -> immArrayGet(arr, i) == 0\n"
            "= ()\n"
            "def main(): Void = ()\n",
            encoding="utf-8",
            newline="\n",
        )
        r_e7_oob = run([geisha, "verify", "--json", "--solver", z3_bin, str(e7_oob_q)])
        assert r_e7_oob.returncode == 1 and json.loads(r_e7_oob.stdout)["failed"] >= 1
        print("PASS [e7_quantifiers_static_runtime_and_fmt]")

        # ------------------------------------------------------------------
        # E8: `String` / `Char` / Bitwise intrinsics & `stdlib` (`std.char`, `std.bits`) verification
        # ------------------------------------------------------------------
        e8_intr = tmp / "e8_intrinsics.gsa"
        e8_intr.write_text(
            "use std.char.{isDigitByte, isAlpha}\n"
            "use std.bits.{popCount, trailingZeros, leadingZeros, setFlag, clearFlag}\n"
            "\n"
            "def firstAsciiByte(s: String): Int\n"
            "    requires strLen(s) > 0\n"
            "    ensures r -> 0 <= r && r < 256\n"
            "= strByteAt(s, 0)\n"
            "\n"
            "def checkIntrinsics(x: Int, ch: Char): Void = {\n"
            "    assert(strLen(\"geisha\") == 6 && strByteAt(\"geisha\", 0) == 103);\n"
            "    let sub = strSlice(\"geisha\", 1, 4);\n"
            "    assert(strLen(sub) == 3);\n"
            "    assert(0 <= charToInt(ch) && charToInt(ch) < 256);\n"
            "    assert(isDigitByte(53) && !isDigitByte(65) && isAlpha('Z'));\n"
            "    let pc = popCount(x);\n"
            "    let tz = trailingZeros(x);\n"
            "    let lz = leadingZeros(x);\n"
            "    assert(0 <= pc && pc <= 32 && 0 <= tz && tz <= 32 && 0 <= lz && lz <= 32);\n"
            "    assert(popCount(0) == 0 && trailingZeros(0) == 32 && leadingZeros(0) == 32);\n"
            "    assert((setFlag(x, 4) & 4) == 4 && (clearFlag(x, 4) & 4) == 0)\n"
            "}\n"
            "def main(): Void = ()\n",
            encoding="utf-8",
            newline="\n",
        )
        r_e8 = run([geisha, "verify", "--json", "--solver", z3_bin, str(e8_intr)])
        assert r_e8.returncode == 0, f"E8 intrinsics & stdlib contracts verify failed:\n{r_e8.stdout}\n{r_e8.stderr}"
        assert json.loads(r_e8.stdout)["ok"] is True

        # Unguarded `strByteAt(s, 0)` without `strLen(s) > 0` MUST fail bounds check
        e8_oob = tmp / "e8_str_oob.gsa"
        e8_oob.write_text("def badFirst(s: String): Int = strByteAt(s, 0)\ndef main() = ()\n", encoding="utf-8")
        assert run([geisha, "verify", "--json", "--solver", z3_bin, str(e8_oob)]).returncode == 1

        # Verify `stdlib/std/char.gsa` and `stdlib/std/bits.gsa` directly!
        for std_rel in ["stdlib/std/char.gsa", "stdlib/std/bits.gsa"]:
            r_std = run([geisha, "verify", "--json", "--solver", z3_bin, str(repo_root / std_rel)])
            assert r_std.returncode == 0 and json.loads(r_std.stdout)["ok"] is True, (
                f"E8 stdlib `{std_rel}` verify failed:\n{r_std.stdout}\n{r_std.stderr}"
            )
        print("PASS [e8_string_char_bits_intrinsics_and_stdlib]")

        # ------------------------------------------------------------------
        # E9: Astra Round 1 regressions (UF identity, multi-binder & guarded
        # quantifiers/old() in `--contracts=check`, termination gate for pure
        # reflection, nested same-ADT, exact popcount/ctz/clz, empty-root dump)
        # ------------------------------------------------------------------
        # 9.0 Lossless UF function identity (`m.f` vs `m_f` must NOT collide!)
        e9_uf_dir = tmp / "e9_uf_pkg"
        (e9_uf_dir / "m").mkdir(parents=True)
        (e9_uf_dir / "m" / "mod.gsa").write_text(
            "pub def f(x: Int): Int = x + 1\n",
            encoding="utf-8",
            newline="\n",
        )
        e9_uf_main = e9_uf_dir / "main.gsa"
        e9_uf_main.write_text(
            "use m.f\n"
            "// Recurse with `decreases` > 1 step so Z3 relies on UF congruence at depth 2!\n"
            "def m_f(n: Int, x: Int): Int\n"
            "    requires n >= 0\n"
            "    decreases n\n"
            "= if (n == 0) x + 2 else m_f(n - 1, x)\n"
            "def m2(n: Int, x: Int): Int\n"
            "    requires n >= 0\n"
            "    decreases n\n"
            "= if (n == 0) f(x) else m2(n - 1, x)\n"
            "\n"
            "verified def mustNotCollide(n: Int, x: Int): Void\n"
            "    requires n >= 2\n"
            "    ensures m_f(n, x) == m2(n, x)\n"
            "= ()\n"
            "def main(): Void = ()\n",
            encoding="utf-8",
            newline="\n",
        )
        # Also test direct module `a.b` vs `a_b` with depth-2 pure recursion so 1-step unfolding stops at UF!
        (e9_uf_dir / "a").mkdir(parents=True)
        (e9_uf_dir / "a" / "mod.gsa").write_text(
            "pub def b(n: Int): Int\n"
            "    requires n >= 0\n"
            "    decreases n\n"
            "= if (n == 0) 1 else b(n - 1)\n",
            encoding="utf-8",
            newline="\n",
        )
        e9_uf_collide = e9_uf_dir / "collide.gsa"
        e9_uf_collide.write_text(
            "use a.{b}\n"
            "def a_b(n: Int): Int\n"
            "    requires n >= 0\n"
            "    decreases n\n"
            "= if (n == 0) 2 else a_b(n - 1)\n"
            "verified def checkDistinct(n: Int): Void\n"
            "    requires n >= 2\n"
            "    ensures b(n) == a_b(n)\n"
            "= ()\n"
            "def main(): Void = ()\n",
            encoding="utf-8",
            newline="\n",
        )
        r_uf_col = run([geisha, "verify", "--json", "--solver", z3_bin, "--src-root", str(e9_uf_dir), str(e9_uf_collide)])
        assert r_uf_col.returncode == 1 and json.loads(r_uf_col.stdout)["failed"] >= 1, (
            f"E9 UF collision (`a.b` vs `a_b`) falsely proved equality:\n{r_uf_col.stdout}\n{r_uf_col.stderr}"
        )

        # 9.1–9.4 Four runtime `--contracts=check` + static `verify` parity reproducers from Astra Round 1
        e9_parity = tmp / "e9_check_parity.gsa"
        e9_parity.write_text(
            "def positive(x: Int): Int\n"
            "    requires x > 0\n"
            "= x\n"
            "\n"
            "verified def pair(): Void\n"
            "    ensures !(exists (i: Int, j: Int) -> 0 <= i && i <= 1 && 0 <= j && j <= 1 && i + j == 3)\n"
            "= ()\n"
            "\n"
            "verified def advance(a: MutArray Int, pos: Cell Int): Void\n"
            "    requires arrayLen(a) == 2 && cellGet(pos) == 0 && arrayGet(a, 0) == 10\n"
            "    ensures forall (i: Int) -> (0 <= i && i < 1) ==> old(arrayGet(a, i + cellGet(pos))) == 10\n"
            "= cellSet(pos, 1)\n"
            "\n"
            "verified def guardedOld(x: Int): Int\n"
            "    ensures r -> (x > 0) ==> r == old(positive(x))\n"
            "= x\n"
            "\n"
            "verified def guardedOldArr(a: MutArray Int, idx: Int): Void\n"
            "    ensures (0 <= idx && idx < arrayLen(a)) ==> arrayGet(a, idx) == old(arrayGet(a, idx)) + 1\n"
            "= if (0 <= idx && idx < arrayLen(a)) arraySet(a, idx, arrayGet(a, idx) + 1) else ()\n"
            "\n"
            "verified def boundedShortCircuit(x: Int): Void\n"
            "    ensures forall (i: Int) -> (x > 0 && 0 <= i && i < positive(x)) ==> i < x\n"
            "= ()\n"
            "\n"
            "def main(): Void = {\n"
            "    pair();\n"
            "    let a = arrayNew(2, 20);\n"
            "    arraySet(a, 0, 10);\n"
            "    advance(a, cellNew(0));\n"
            "    assert(guardedOld(0) == 0 && guardedOld(5) == 5);\n"
            "    guardedOldArr(a, -1);\n"
            "    guardedOldArr(a, 1);\n"
            "    boundedShortCircuit(0);\n"
            "    boundedShortCircuit(3)\n"
            "}\n",
            encoding="utf-8",
            newline="\n",
        )
        r_e9_pv = run([geisha, "verify", "--json", "--solver", z3_bin, str(e9_parity)])
        assert r_e9_pv.returncode == 0 and json.loads(r_e9_pv.stdout)["ok"] is True, (
            f"E9 parity static verify failed:\n{r_e9_pv.stdout}\n{r_e9_pv.stderr}"
        )
        e9_pbin = tmp / ("e9_parity.exe" if sys.platform == "win32" else "e9_parity")
        r_e9_pb = run([geisha, "--contracts=check", "--runtime", runtime, "-o", str(e9_pbin), str(e9_parity)])
        assert r_e9_pb.returncode == 0, f"E9 parity --contracts=check build failed:\n{r_e9_pb.stdout}\n{r_e9_pb.stderr}"
        r_e9_pr = run([str(e9_pbin)])
        assert r_e9_pr.returncode == 0, f"E9 parity --contracts=check execution failed:\n{r_e9_pr.stdout}\n{r_e9_pr.stderr}"

        # Unbounded quantifier in `--contracts=check` must report a clean compile diagnostic instead of silently returning `true`!
        e9_unb = tmp / "e9_unbounded_chk.gsa"
        e9_unb.write_text(
            "def badUnbounded(): Void\n"
            "    ensures !(exists (x: Int) -> x == 42)\n"
            "= ()\n"
            "def main(): Void = badUnbounded()\n",
            encoding="utf-8",
            newline="\n",
        )
        r_e9_unb = run([geisha, "--contracts=check", "--runtime", runtime, "-o", str(tmp / "e9_unb_bin"), str(e9_unb)])
        assert r_e9_unb.returncode != 0 and "cannot execute unbounded" in (r_e9_unb.stdout + r_e9_unb.stderr), (
            f"E9 unbounded quantifier in --contracts=check must emit diagnostic:\n{r_e9_unb.stdout}\n{r_e9_unb.stderr}"
        )

        # 9.5 Non-terminating recursive function without `decreases` MUST NOT get pure reflection (`uf(x) == uf(x) + 1` vacuity)!
        e9_nonterm = tmp / "e9_nonterm_reflect.gsa"
        e9_nonterm.write_text(
            "def badRec(x: Int): Int = badRec(x) + 1\n"
            "verified def exploit(): Void = {\n"
            "    let _ = badRec(0);\n"
            "    assert(false)\n"
            "}\n"
            "def main(): Void = ()\n",
            encoding="utf-8",
            newline="\n",
        )
        r_e9_nt = run([geisha, "verify", "--json", "--solver", z3_bin, str(e9_nonterm)])
        assert r_e9_nt.returncode == 1 and json.loads(r_e9_nt.stdout)["failed"] >= 1, (
            f"E9 non-terminating pure recursion vacuously proved `assert(false)`:\n{r_e9_nt.stdout}\n{r_e9_nt.stderr}"
        )

        # 9.6 & 9.7 Nested same-ADT (`Option (Option Int)`) + exact `bitPopCount`/`bitCtz`/`bitClz` (32 & 64 bit)
        e9_exact = tmp / "e9_nested_and_bits.gsa"
        e9_exact.write_text(
            "use std.option.{Option, Some, None}\n"
            "\n"
            "verified def wrapNested(flag: Bool): Option (Option Int)\n"
            "    ensures r -> match r { Some(Some(x)) -> flag && x == 7, None -> !flag, _ -> false }\n"
            "= if (flag) Some(Some(7)) else None\n"
            "\n"
            "verified def exactBits(x: Int): Int\n"
            "    ensures r -> r == 1\n"
            "= {\n"
            "    assert(bitPopCount(1) == 1 && bitPopCount(7) == 3 && bitPopCount(-1) == 32);\n"
            "    assert(bitCtz(8) == 3 && bitCtz(1) == 0 && bitCtz(0) == 32);\n"
            "    assert(bitClz(1) == 31 && bitClz(4) == 29 && bitClz(-1) == 0);\n"
            "    assert(bitPopCount64(intToI64(5)) == 2 && bitCtz64(intToI64(8)) == 3 && bitClz64(intToI64(1)) == 63);\n"
            "    if (x != 0) {\n"
            "        assert(bitPopCount(x & (x - 1)) == bitPopCount(x) - 1)\n"
            "    } else ();\n"
            "    bitPopCount(1)\n"
            "}\n"
            "def main(): Void = { let _ = wrapNested(true); let _ = exactBits(6); () }\n",
            encoding="utf-8",
            newline="\n",
        )
        r_e9_ex = run([geisha, "verify", "--json", "--solver", z3_bin, str(e9_exact)])
        assert r_e9_ex.returncode == 0 and json.loads(r_e9_ex.stdout)["ok"] is True, (
            f"E9 nested Option(Option Int) & exact bit-counts verify failed:\n{r_e9_ex.stdout}\n{r_e9_ex.stderr}"
        )

        # 9.8 Empty selected roots in `geisha verify --dump-core` must NOT leak unrelated `main`!
        e9_empty = tmp / "e9_empty_roots.gsa"
        e9_empty_dump = tmp / "e9_empty_roots.gscore"
        e9_empty.write_text(
            "concept Exotic a { rank: a -> Int }\n"
            "verified def magnitude(x: a): Int\n"
            "    ensures r -> r == rank(x)\n"
            "= rank(x)\n"
            "def main(): Void = printLn(\"sibling\")\n",
            encoding="utf-8",
            newline="\n",
        )
        r_e9_emp = run([geisha, "verify", "--json", "--solver", z3_bin, "--dump-core", str(e9_empty_dump), str(e9_empty)])
        assert r_e9_emp.returncode == 1 and json.loads(r_e9_emp.stdout)["unknown"] >= 1
        emp_sexp = e9_empty_dump.read_text(encoding="utf-8")
        assert "(fun \"main\"" not in emp_sexp and "\"sibling\"" not in emp_sexp, (
            f"E9 empty selected roots leaked `main` into `.gscore`:\n{emp_sexp}"
        )

        # ------------------------------------------------------------------
        # E10: Astra Round 2 regressions (dependent guard before upper bound,
        # global-Cell helper in `old(...)`, `requires` helper predicate facts,
        # generic `Bool` quantifier specialization, `ImmArray (Cell Int)` in `old`)
        # ------------------------------------------------------------------
        # 10.1 Dependent guard `inRange(i, n)` + opaque dependent guard before `i < positive(n)` (Native + JS!)
        e10_dep = tmp / "e10_dep_guard.gsa"
        e10_dep.write_text(
            "def positive(n: Int): Int\n"
            "    requires n > 0\n"
            "= n\n"
            "def inRange(i: Int, n: Int): Bool = i < n\n"
            "verified def checkRange(n: Int): Void\n"
            "    ensures forall (i: Int) -> (0 <= i && inRange(i, n) && i < positive(n)) ==> i < n\n"
            "= ()\n"
            "def main(): Void = { checkRange(3); checkRange(0); printLn(\"ok\") }\n",
            encoding="utf-8",
            newline="\n",
        )
        r_e10_dv = run([geisha, "verify", "--json", "--solver", z3_bin, str(e10_dep)])
        assert r_e10_dv.returncode == 0 and json.loads(r_e10_dv.stdout)["ok"] is True
        e10_dbin = tmp / ("e10_dep.exe" if sys.platform == "win32" else "e10_dep")
        assert run([geisha, "--contracts=check", "--runtime", runtime, "-o", str(e10_dbin), str(e10_dep)]).returncode == 0
        r_e10_dn = run([str(e10_dbin)])
        assert r_e10_dn.returncode == 0 and r_e10_dn.stdout.strip() == "ok"
        if shutil.which("node"):
            e10_djs = tmp / "e10_dep.mjs"
            assert run([geisha, "--contracts=check", "--target", "js", "-o", str(e10_djs), str(e10_dep)]).returncode == 0
            r_e10_dj = run(["node", str(e10_djs)])
            assert r_e10_dj.returncode == 0 and r_e10_dj.stdout.strip() == "ok"

        # 10.2 Read-only helper reading module-level `Cell` inside `old(current())` (Native + JS!)
        e10_glob = tmp / "e10_global_old.gsa"
        e10_glob.write_text(
            "def counter: Cell Int = cellNew(10)\n"
            "def current(): Int = cellGet(counter)\n"
            "def increment(): Void\n"
            "    ensures current() == old(current()) + 1\n"
            "= cellSet(counter, current() + 1)\n"
            "def main(): Void = { increment(); printLn(\"ok\") }\n",
            encoding="utf-8",
            newline="\n",
        )
        e10_gbin = tmp / ("e10_glob.exe" if sys.platform == "win32" else "e10_glob")
        r_e10_gb = run([geisha, "--contracts=check", "--runtime", runtime, "-o", str(e10_gbin), str(e10_glob)])
        assert r_e10_gb.returncode == 0, f"E10 global old build failed:\n{r_e10_gb.stdout}\n{r_e10_gb.stderr}"
        r_e10_gn = run([str(e10_gbin)])
        assert r_e10_gn.returncode == 0 and r_e10_gn.stdout.strip() == "ok", (
            f"E10 global old native run failed:\n{r_e10_gn.stdout}\n{r_e10_gn.stderr}"
        )
        if shutil.which("node"):
            e10_gjs = tmp / "e10_glob.mjs"
            assert run([geisha, "--contracts=check", "--target", "js", "-o", str(e10_gjs), str(e10_glob)]).returncode == 0
            r_e10_gj = run(["node", str(e10_gjs)])
            assert r_e10_gj.returncode == 0 and r_e10_gj.stdout.strip() == "ok"

        # 10.3 `requires positive(x)` pure helper predicate facts preserved in domain-guarded unfolding!
        e10_dom = tmp / "e10_domain_pred.gsa"
        e10_dom.write_text(
            "def positive(x: Int): Bool = x > 0\n"
            "def identity(x: Int): Int\n"
            "    requires positive(x)\n"
            "= x\n"
            "verified def client(x: Int): Int\n"
            "    requires x > 0\n"
            "    ensures r -> r == x\n"
            "= identity(x)\n"
            "def main(): Void = { let _ = client(1); printLn(\"ok\") }\n",
            encoding="utf-8",
            newline="\n",
        )
        r_e10_dom = run([geisha, "verify", "--json", "--solver", z3_bin, str(e10_dom)])
        assert r_e10_dom.returncode == 0 and json.loads(r_e10_dom.stdout)["ok"] is True, (
            f"E10 requires helper predicate verify failed:\n{r_e10_dom.stdout}\n{r_e10_dom.stderr}"
        )

        # 10.4 Generic quantifier specialized to `Bool` + 10.5 `ImmArray (Cell Int)` in `old(...)`
        e10_poly_imm = tmp / "e10_poly_and_imm.gsa"
        e10_poly_imm.write_text(
            "def identity(x: a): a\n"
            "    ensures r -> forall (v: a) -> (v == x) ==> v == r\n"
            "= x\n"
            "def setFirst(items: ImmArray (Cell Int)): Void\n"
            "    requires immArrayLen(items) > 0\n"
            "    ensures cellGet(immArrayGet(items, 0)) == old(cellGet(immArrayGet(items, 0))) + 1\n"
            "= { let c = immArrayGet(items, 0); cellSet(c, cellGet(c) + 1) }\n"
            "def main(): Void = {\n"
            "    setFirst(arrayFreeze(arrayNew(1, cellNew(10))));\n"
            "    printLn(if (identity(true)) \"ok\" else \"unexpected\")\n"
            "}\n",
            encoding="utf-8",
            newline="\n",
        )
        e10_pibin = tmp / ("e10_pi.exe" if sys.platform == "win32" else "e10_pi")
        r_e10_pib = run([geisha, "--contracts=check", "--runtime", runtime, "-o", str(e10_pibin), str(e10_poly_imm)])
        assert r_e10_pib.returncode == 0, f"E10 poly Bool & ImmArray(Cell Int) build failed:\n{r_e10_pib.stdout}\n{r_e10_pib.stderr}"
        r_e10_pir = run([str(e10_pibin)])
        assert r_e10_pir.returncode == 0 and r_e10_pir.stdout.strip() == "ok", (
            f"E10 poly Bool & ImmArray(Cell Int) run failed:\n{r_e10_pir.stdout}\n{r_e10_pir.stderr}"
        )

        # ------------------------------------------------------------------
        # E11: Astra Round 3 regressions (capture-free bound unfolding,
        # mid-conjunction independent guard after dependent guard,
        # conditional `if` bound preceded by dependent guard + negative controls — Native + JS!)
        # ------------------------------------------------------------------
        e11_r3 = tmp / "e11_round3.gsa"
        e11_r3.write_text(
            "verified def positive(n: Int): Int\n"
            "    requires n > 0\n"
            "    ensures r -> r == n && r > 0\n"
            "= n\n"
            "\n"
            "// 11.1 Local bindings (`let n`, `let i`, renamed `padding`) MUST NOT capture caller/quantifier vars!\n"
            "def withinSameCaller(i: Int, limit: Int): Bool =\n"
            "    i < { let n = 2; limit + n }\n"
            "def withinSameQuant(i: Int, limit: Int): Bool =\n"
            "    i < { let i = 2; limit + i }\n"
            "def withinRenamed(i: Int, limit: Int): Bool =\n"
            "    i < { let padding = 2; limit + padding }\n"
            "verified def hasLastExplicitCap(n: Int): Void\n"
            "    requires n == 4\n"
            "    ensures exists (i: Int) -> 0 <= i && withinSameCaller(i, n) && i < 8 && i == 5\n"
            "= ()\n"
            "verified def hasLastNoCap(n: Int): Void\n"
            "    requires n == 4\n"
            "    ensures exists (i: Int) -> 0 <= i && withinSameCaller(i, n) && i == 5\n"
            "    ensures exists (i: Int) -> 0 <= i && withinSameQuant(i, n) && i == 5\n"
            "    ensures exists (i: Int) -> 0 <= i && withinRenamed(i, n) && i == 5\n"
            "= ()\n"
            "\n"
            "// 11.2 Mid-conjunction `positive(mask) > 0` after `(i & mask) != 0` MUST NOT hoist before loop!\n"
            "verified def checkMidGuard(mask: Int): Void\n"
            "    requires mask >= 0\n"
            "    ensures forall (i: Int) -> (0 <= i && (i & mask) != 0 && positive(mask) > 0 && i < 4) ==> i < 4\n"
            "= ()\n"
            "\n"
            "// 11.3 Conditional `if (mask < 2) positive(mask) else 2` upper bound after `(i & mask) != 0`!\n"
            "verified def checkCondBound(mask: Int): Void\n"
            "    requires mask >= 0\n"
            "    ensures forall (i: Int) -> (0 <= i && (i & mask) != 0 && i < (if (mask < 2) positive(mask) else 2)) ==> i >= 0\n"
            "= ()\n"
            "\n"
            "def main(): Void = {\n"
            "    hasLastExplicitCap(4);\n"
            "    hasLastNoCap(4);\n"
            "    checkMidGuard(1);\n"
            "    checkMidGuard(0);\n"
            "    checkCondBound(2);\n"
            "    checkCondBound(1);\n"
            "    checkCondBound(0);\n"
            "    printLn(\"ok\")\n"
            "}\n",
            encoding="utf-8",
            newline="\n",
        )
        r_e11_v = run([geisha, "verify", "--json", "--solver", z3_bin, str(e11_r3)])
        assert r_e11_v.returncode == 0 and json.loads(r_e11_v.stdout)["ok"] is True, (
            f"E11 Round 3 static verify failed:\n{r_e11_v.stdout}\n{r_e11_v.stderr}"
        )
        e11_bin = tmp / ("e11_r3.exe" if sys.platform == "win32" else "e11_r3")
        r_e11_b = run([geisha, "--contracts=check", "--runtime", runtime, "-o", str(e11_bin), str(e11_r3)])
        assert r_e11_b.returncode == 0, f"E11 Round 3 native build failed:\n{r_e11_b.stdout}\n{r_e11_b.stderr}"
        r_e11_n = run([str(e11_bin)])
        assert r_e11_n.returncode == 0 and r_e11_n.stdout.strip() == "ok", (
            f"E11 Round 3 native run failed:\n{r_e11_n.stdout}\n{r_e11_n.stderr}"
        )
        if shutil.which("node"):
            e11_js = tmp / "e11_r3.mjs"
            r_e11_jb = run([geisha, "--contracts=check", "--target", "js", "-o", str(e11_js), str(e11_r3)])
            assert r_e11_jb.returncode == 0, f"E11 Round 3 JS build failed:\n{r_e11_jb.stdout}\n{r_e11_jb.stderr}"
            r_e11_jr = run(["node", str(e11_js)])
            assert r_e11_jr.returncode == 0 and r_e11_jr.stdout.strip() == "ok", (
                f"E11 Round 3 JS run failed:\n{r_e11_jr.stdout}\n{r_e11_jr.stderr}"
            )

        # 11.4 Adversarial negative controls:
        #   (a) out-of-range witness `i == 6` (`withinSameCaller(6, 4)` is false) MUST fail ensures!
        #   (b) non-vacuous `(i >= 5000)` before `i < (if (mask < 2) positive(mask) else 2)` with `mask = 0`
        #       MUST reach `i = 5000` (beyond 4096!) and abort with `requires violated` in Native AND JS!
        for neg_nm, neg_src_txt, exp_msg in [
            (
                "e11_neg_cap",
                "def within(i: Int, limit: Int): Bool = i < { let n = 2; limit + n }\n"
                "def badLast(n: Int): Void\n"
                "    ensures exists (i: Int) -> 0 <= i && within(i, n) && i < 8 && i == 6\n"
                "= ()\n"
                "def main(): Void = badLast(4)\n",
                "ensures violated",
            ),
            (
                "e11_neg_high_witness",
                "def positive(n: Int): Int\n"
                "    requires n > 0\n"
                "= n\n"
                "def badCond(mask: Int): Void\n"
                "    ensures forall (i: Int) -> (0 <= i && i >= 5000 && i < (if (mask < 2) positive(mask) else 2)) ==> i >= 0\n"
                "= ()\n"
                "def main(): Void = badCond(0)\n",
                "requires violated",
            ),
        ]:
            neg_f = tmp / f"{neg_nm}.gsa"
            neg_f.write_text(neg_src_txt, encoding="utf-8", newline="\n")
            neg_b = tmp / (f"{neg_nm}.exe" if sys.platform == "win32" else neg_nm)
            assert run([geisha, "--contracts=check", "--runtime", runtime, "-o", str(neg_b), str(neg_f)]).returncode == 0
            r_nb = run([str(neg_b)])
            assert r_nb.returncode != 0 and exp_msg in (r_nb.stdout + r_nb.stderr), (
                f"E11 {neg_nm} native expected {exp_msg!r}, got rc={r_nb.returncode}: {r_nb.stdout}\n{r_nb.stderr}"
            )
            if shutil.which("node"):
                neg_j = tmp / f"{neg_nm}.mjs"
                assert run([geisha, "--contracts=check", "--target", "js", "-o", str(neg_j), str(neg_f)]).returncode == 0
                r_nj = run(["node", str(neg_j)])
                assert r_nj.returncode != 0 and exp_msg in (r_nj.stdout + r_nj.stderr), (
                    f"E11 {neg_nm} JS expected {exp_msg!r}, got rc={r_nj.returncode}: {r_nj.stdout}\n{r_nj.stderr}"
                )
        # ------------------------------------------------------------------
        # E12: Astra Round 4 regressions (strict INT_MAX/INT_MIN empty-endpoint
        # short-circuiting + contracted range predicates preserving live contract checks!)
        # ------------------------------------------------------------------
        e12_r4 = tmp / "e12_round4.gsa"
        e12_r4.write_text(
            "def successor(n: Int): Int\n"
            "    requires n < 2147483647\n"
            "= n + 1\n"
            "verified def checkNext(n: Int): Void\n"
            "    ensures forall (i: Int) -> (i > n && i <= successor(n)) ==> i > n\n"
            "= ()\n"
            "\n"
            "def prev(n: Int): Int\n"
            "    requires n > -2147483648\n"
            "= n - 1\n"
            "verified def checkPrev(n: Int): Void\n"
            "    ensures forall (i: Int) -> (i < n && i >= prev(n)) ==> i < n\n"
            "= ()\n"
            "\n"
            "def below(i: Int, cap: Int): Bool\n"
            "    ensures r -> r == (i < cap)\n"
            "= i < cap\n"
            "verified def four(): Void\n"
            "    ensures exists (i: Int) -> 0 <= i && below(i, 4) && i == 3\n"
            "= ()\n"
            "\n"
            "def main(): Void = {\n"
            "    checkNext(4);\n"
            "    checkNext(2147483647);\n"
            "    checkPrev(4);\n"
            "    checkPrev(-2147483648);\n"
            "    four();\n"
            "    printLn(\"ok\")\n"
            "}\n",
            encoding="utf-8",
            newline="\n",
        )
        r_e12_v = run([geisha, "verify", "--json", "--solver", z3_bin, str(e12_r4)])
        assert r_e12_v.returncode == 0 and json.loads(r_e12_v.stdout)["ok"] is True, (
            f"E12 Round 4 static verify failed:\n{r_e12_v.stdout}\n{r_e12_v.stderr}"
        )
        e12_bin = tmp / ("e12_r4.exe" if sys.platform == "win32" else "e12_r4")
        r_e12_b = run([geisha, "--contracts=check", "--runtime", runtime, "-o", str(e12_bin), str(e12_r4)])
        assert r_e12_b.returncode == 0, f"E12 Round 4 native build failed:\n{r_e12_b.stdout}\n{r_e12_b.stderr}"
        r_e12_n = run([str(e12_bin)])
        assert r_e12_n.returncode == 0 and r_e12_n.stdout.strip() == "ok", (
            f"E12 Round 4 native run failed:\n{r_e12_n.stdout}\n{r_e12_n.stderr}"
        )
        if shutil.which("node"):
            e12_js = tmp / "e12_r4.mjs"
            r_e12_jb = run([geisha, "--contracts=check", "--target", "js", "-o", str(e12_js), str(e12_r4)])
            assert r_e12_jb.returncode == 0, f"E12 Round 4 JS build failed:\n{r_e12_jb.stdout}\n{r_e12_jb.stderr}"
            r_e12_jr = run(["node", str(e12_js)])
            assert r_e12_jr.returncode == 0 and r_e12_jr.stdout.strip() == "ok", (
                f"E12 Round 4 JS run failed:\n{r_e12_jr.stdout}\n{r_e12_jr.stderr}"
            )

        # 12.2 Contracted predicate helpers MUST still execute their own contracts on boundary/empty calls!
        for neg_nm, neg_src_txt, exp_msg in [
            (
                "e12_pred_ens_boundary",
                "def badBelow(i: Int, cap: Int): Bool\n"
                "    ensures r -> i < 4\n"
                "= i < cap\n"
                "def caller(): Void\n"
                "    ensures forall (i: Int) -> (0 <= i && badBelow(i, 4)) ==> i < 4\n"
                "= ()\n"
                "def main(): Void = caller()\n",
                "ensures violated",
            ),
            (
                "e12_pred_ens_empty",
                "def badBelow0(i: Int, cap: Int): Bool\n"
                "    ensures r -> cap > 0\n"
                "= i < cap\n"
                "def caller0(): Void\n"
                "    ensures forall (i: Int) -> (0 <= i && badBelow0(i, 0)) ==> false\n"
                "= ()\n"
                "def main(): Void = caller0()\n",
                "ensures violated",
            ),
        ]:
            neg_f = tmp / f"{neg_nm}.gsa"
            neg_f.write_text(neg_src_txt, encoding="utf-8", newline="\n")
            neg_b = tmp / (f"{neg_nm}.exe" if sys.platform == "win32" else neg_nm)
            assert run([geisha, "--contracts=check", "--runtime", runtime, "-o", str(neg_b), str(neg_f)]).returncode == 0
            r_nb = run([str(neg_b)])
            assert r_nb.returncode != 0 and exp_msg in (r_nb.stdout + r_nb.stderr), (
                f"E12 {neg_nm} native expected {exp_msg!r}, got rc={r_nb.returncode}: {r_nb.stdout}\n{r_nb.stderr}"
            )
            if shutil.which("node"):
                neg_j = tmp / f"{neg_nm}.mjs"
                assert run([geisha, "--contracts=check", "--target", "js", "-o", str(neg_j), str(neg_f)]).returncode == 0
                r_nj = run(["node", str(neg_j)])
                assert r_nj.returncode != 0 and exp_msg in (r_nj.stdout + r_nj.stderr), (
                    f"E12 {neg_nm} JS expected {exp_msg!r}, got rc={r_nj.returncode}: {r_nj.stdout}\n{r_nj.stderr}"
                )
        print("PASS [e9_astra_round1_round2_round3_round4_regressions]")

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
        # Multi-backend codegen under live runtime contracts (native IR, wasm-gc, js),
        # exercising HOF combinator opt, `$spec$`, `$flat$`, and known-match reduction live!
        mini = tmp2 / "d2_mini.gsa"
        mini.write_text(
            "use std.option.{Option, Some, None}\n"
            "use std.str.{intToStr}\n"
            "def foldLoop(xs: List Int, acc: Int, cb: Int -> Int): Int = match xs {\n"
            "    Nil -> acc,\n"
            "    Cons(h, t) -> foldLoop(t, acc + cb(h), cb),\n"
            "}\n"
            "def compute(k: Int): Int = {\n"
            "    let bias = match Some(k) { Some(v) -> v, None -> 0 };\n"
            "    let stepCls = (z: Int) -> {\n"
            "        let c = cellNew(0);\n"
            "        while (cellGet(c) < z) { cellSet(c, cellGet(c) + bias) };\n"
            "        cellGet(c)\n"
            "    };\n"
            "    foldLoop([1, 2, 3], 0, (x: Int) -> x * 2 + bias) + stepCls(5)\n"
            "}\n"
            "def main(): Void = printLn(intToStr(compute(4)))\n",
            encoding="utf-8",
            newline="\n",
        )
        r_nat = run([str(checked_bin), "-O2", "-e", "-o", str(tmp2 / "mini.ll"), str(mini)])
        assert r_nat.returncode == 0, f"D2 native codegen failed:\n{r_nat.stdout}\n{r_nat.stderr}"
        mini_ll_txt = (tmp2 / "mini.ll").read_text(encoding="utf-8")
        assert "foldLoop$spec$" in mini_ll_txt and "$flat$" in mini_ll_txt, (
            "D2 geisha_checked -O2 missing live $spec$ / $flat$ optimization!"
        )
        r_wgc = run([str(checked_bin), "-O2", "--target", "wasm-gc", "-o", str(tmp2 / "mini.wasm"), str(mini)])
        assert r_wgc.returncode == 0, f"D2 wasm-gc codegen failed:\n{r_wgc.stdout}\n{r_wgc.stderr}"
        r_js = run([str(checked_bin), "-O2", "--target", "js", "-o", str(tmp2 / "mini.mjs"), str(mini)])
        assert r_js.returncode == 0, f"D2 js codegen failed:\n{r_js.stdout}\n{r_js.stderr}"
        print("PASS [d2_geisha_checked]: live contracts embedded, self-check + native/wasm-gc/js codegen passed")

    return 0


if __name__ == "__main__":
    raise SystemExit(main())
