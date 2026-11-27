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
        ]

        for name, code in adversarial_cases:
            f = tmp / f"{name}.gsa"
            f.write_text(code, encoding="utf-8")
            rj = run([geisha, "verify", "--json", "--solver", z3_bin, str(f)])
            assert rj.returncode == 1, f"adversarial case [{name}] MUST fail (exit 1), got {rj.returncode}:\n{rj.stdout}\n{rj.stderr}"
            jp = json.loads(rj.stdout)
            assert jp["ok"] is False and (jp["failed"] + jp["unknown"]) > 0, f"adversarial case [{name}] vacuously passed: {jp}"
        print(f"PASS [smt_verify_adversarial_14]: all {len(adversarial_cases)} soundness counterexamples rejected")

    return 0


if __name__ == "__main__":
    raise SystemExit(main())
