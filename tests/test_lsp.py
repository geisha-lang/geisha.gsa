#!/usr/bin/env python3
"""End-to-end JSON-RPC 2.0 stdio test suite for `geisha lsp`."""

from __future__ import annotations

import json
import os
import subprocess
import sys
import tempfile
from pathlib import Path


class LspClient:
    def __init__(self, geisha_bin: str, cwd: str, extra_args: list[str] | None = None) -> None:
        cmd = [geisha_bin, "lsp"] + (extra_args or [])
        self.proc = subprocess.Popen(
            cmd,
            stdin=subprocess.PIPE,
            stdout=subprocess.PIPE,
            stderr=subprocess.PIPE,
            cwd=cwd,
        )
        self.next_id = 1
        self.notifications: list[dict] = []

    def send(self, payload: dict) -> None:
        body = json.dumps(payload).encode("utf-8")
        header = f"Content-Length: {len(body)}\r\n\r\n".encode("ascii")
        assert self.proc.stdin is not None
        self.proc.stdin.write(header + body)
        self.proc.stdin.flush()

    def read_message(self) -> dict:
        assert self.proc.stdout is not None
        content_len = None
        while True:
            line = self.proc.stdout.readline()
            if not line:
                stderr_out = self.proc.stderr.read().decode("utf-8", errors="replace") if self.proc.stderr else ""
                raise RuntimeError(f"Unexpected EOF from geisha lsp (stderr={stderr_out!r})")
            decoded = line.decode("ascii").strip()
            if decoded == "":
                if content_len is not None:
                    break
                continue
            if ":" in decoded:
                k, v = decoded.split(":", 1)
                if k.strip().lower() == "content-length":
                    content_len = int(v.strip())
        assert content_len is not None
        body = self.proc.stdout.read(content_len)
        return json.loads(body.decode("utf-8"))

    def request(self, method: str, params: dict | None = None) -> dict:
        req_id = self.next_id
        self.next_id += 1
        msg: dict = {"jsonrpc": "2.0", "id": req_id, "method": method}
        if params is not None:
            msg["params"] = params
        self.send(msg)
        while True:
            resp = self.read_message()
            if "id" in resp and resp["id"] == req_id:
                return resp
            self.notifications.append(resp)

    def notify(self, method: str, params: dict | None = None) -> None:
        msg: dict = {"jsonrpc": "2.0", "method": method}
        if params is not None:
            msg["params"] = params
        self.send(msg)

    def wait_notification(self, method: str) -> dict:
        for i, n in enumerate(self.notifications):
            if n.get("method") == method:
                return self.notifications.pop(i)
        while True:
            msg = self.read_message()
            if msg.get("method") == method:
                return msg
            self.notifications.append(msg)

    def wait_diag_for(self, uri: str) -> list[dict]:
        # Drain matching diagnostic notification for `uri`
        for i, n in enumerate(self.notifications):
            if n.get("method") == "textDocument/publishDiagnostics" and n.get("params", {}).get("uri") == uri:
                self.notifications.pop(i)
                return n["params"]["diagnostics"]
        while True:
            msg = self.read_message()
            if msg.get("method") == "textDocument/publishDiagnostics" and msg.get("params", {}).get("uri") == uri:
                return msg["params"]["diagnostics"]
            self.notifications.append(msg)


def path_to_uri(p: Path) -> str:
    return p.resolve().as_uri()


def main() -> int:
    geisha_bin = sys.argv[1] if len(sys.argv) > 1 else os.environ.get("GEISHA_BIN", "build/geisha2")
    geisha_bin = str(Path(geisha_bin).resolve())

    # 0. CLI argument validation: reject unknown flags & positional args immediately (no hang), accept --stdio
    bad_flag = subprocess.run([geisha_bin, "lsp", "--bogus"], stdin=subprocess.DEVNULL, capture_output=True, text=True, timeout=5)
    assert bad_flag.returncode != 0 and "--bogus" in bad_flag.stderr, f"expected error on --bogus: {bad_flag}"
    bad_pos = subprocess.run([geisha_bin, "lsp", "extra.gsa"], stdin=subprocess.DEVNULL, capture_output=True, text=True, timeout=5)
    assert bad_pos.returncode != 0 and "extra.gsa" in bad_pos.stderr, f"expected error on positional arg: {bad_pos}"

    with tempfile.TemporaryDirectory(prefix="geisha_lsp_test_") as td:
        root = Path(td)
        helper_path = root / "helper.gsa"
        helper_src = (
            "/// A boxed integer wrapper.\n"
            "pub data Boxed {\n"
            "    Wrap(Int),\n"
            "    Empty,\n"
            "}\n"
            "\n"
            "/// Multiply an integer by two.\n"
            "pub def doubleVal(n: Int): Int = n * 2\n"
        )
        helper_path.write_text(helper_src, encoding="utf-8")

        main_path = root / "main.gsa"
        main_src = (
            "use std.str.{intToStr}\n"
            "use helper.{Boxed, Wrap, Empty, doubleVal}\n"
            "\n"
            "/// A 2D integer point.\n"
            "pub data Point { x: Int, y: Int }\n"
            "\n"
            "pub data Shape {\n"
            "    Circle(Int),\n"
            "    Rect { w: Int, h: Int },\n"
            "}\n"
            "\n"
            "pub concept Describable a {\n"
            "    describe: a -> String\n"
            "}\n"
            "\n"
            "/// Add two integers together.\n"
            "def addNums(a: Int, b: Int): Int = a + b\n"
            "\n"
            "def unwrapBox(bx: Boxed): Int = match bx {\n"
            "    Wrap(val) -> val + 1,\n"
            "    Empty -> 0,\n"
            "}\n"
            "\n"
            "def main(): Void = {\n"
            "    let (px, py) = (10, 20);\n"
            "    let total = addNums(px, doubleVal(py)) + unwrapBox(Wrap(5));\n"
            "    printLn(intToStr(total))\n"
            "}\n"
        )
        main_path.write_text(main_src, encoding="utf-8")

        main_uri = path_to_uri(main_path)
        helper_uri = path_to_uri(helper_path)

        client = LspClient(geisha_bin, str(root), extra_args=["--stdio"])

        # 1. initialize + initialized
        init_resp = client.request("initialize", {
            "processId": os.getpid(),
            "rootUri": path_to_uri(root),
            "capabilities": {},
        })
        assert "result" in init_resp, f"initialize failed: {init_resp}"
        caps = init_resp["result"]["capabilities"]
        assert caps["hoverProvider"] is True
        assert caps["definitionProvider"] is True
        assert caps["documentSymbolProvider"] is True
        assert caps["completionProvider"]["triggerCharacters"] == ["."]
        assert init_resp["result"]["serverInfo"]["name"] == "geisha-lsp"
        client.notify("initialized", {})

        # 2. didOpen valid file -> 0 diagnostics
        client.notify("textDocument/didOpen", {
            "textDocument": {
                "uri": main_uri,
                "languageId": "geisha",
                "version": 1,
                "text": main_src,
            }
        })
        diag_ok = client.wait_notification("textDocument/publishDiagnostics")
        assert diag_ok["params"]["uri"] == main_uri
        assert diag_ok["params"]["diagnostics"] == [], f"expected 0 diagnostics, got: {diag_ok}"

        # 3. documentSymbol (and word-boundary selectionRange)
        sym_resp = client.request("textDocument/documentSymbol", {
            "textDocument": {"uri": main_uri},
        })
        syms = sym_resp["result"]
        sym_names = [s["name"] for s in syms]
        for expected in ("Point", "Shape", "Describable", "addNums", "unwrapBox", "main"):
            assert expected in sym_names, f"missing symbol {expected!r} in {sym_names}"
        shape_sym = next(s for s in syms if s["name"] == "Shape")
        variant_names = [c["name"] for c in shape_sym.get("children", [])]
        assert "Circle" in variant_names and "Rect" in variant_names, f"missing Shape variants: {variant_names}"
        desc_sym = next(s for s in syms if s["name"] == "Describable")
        method_names = [c["name"] for c in desc_sym.get("children", [])]
        assert "describe" in method_names, f"missing concept method: {method_names}"
        add_sym = next(s for s in syms if s["name"] == "addNums")
        assert add_sym["selectionRange"]["start"] == {"line": 16, "character": 4}, f"unexpected selectionRange: {add_sym}"

        # 4. hover on `addNums` call (line 25, col 18) -> inferred type + `///` doc
        hover_add = client.request("textDocument/hover", {
            "textDocument": {"uri": main_uri},
            "position": {"line": 25, "character": 18},
        })
        assert hover_add["result"] is not None, "hover on addNums returned null"
        hover_add_md = hover_add["result"]["contents"]["value"]
        assert "Int" in hover_add_md and "Add two integers together." in hover_add_md, f"unexpected hover: {hover_add_md}"

        # 4b. hover on `doubleVal` call (line 25, col 31) -> cross-file inferred type + `///` doc
        hover_dbl = client.request("textDocument/hover", {
            "textDocument": {"uri": main_uri},
            "position": {"line": 25, "character": 31},
        })
        assert hover_dbl["result"] is not None, "hover on doubleVal returned null"
        hover_dbl_md = hover_dbl["result"]["contents"]["value"]
        assert "Int" in hover_dbl_md and "Multiply an integer by two." in hover_dbl_md, f"unexpected hover: {hover_dbl_md}"

        # 4c. hover on `total` in `intToStr(total)` (line 26, col 22) -> inferred `Int`
        hover_tot = client.request("textDocument/hover", {
            "textDocument": {"uri": main_uri},
            "position": {"line": 26, "character": 22},
        })
        assert hover_tot["result"] is not None, "hover on total returned null"
        assert "Int" in hover_tot["result"]["contents"]["value"], f"unexpected hover on total: {hover_tot}"

        # 5. definition: top-level, cross-file fn, local param, local let, match pattern var, destructured let, cross-file pattern ctor
        def_add = client.request("textDocument/definition", {
            "textDocument": {"uri": main_uri},
            "position": {"line": 25, "character": 18},
        })
        assert def_add["result"]["uri"] == main_uri
        assert def_add["result"]["range"]["start"]["line"] == 16, f"unexpected addNums def: {def_add}"

        def_dbl = client.request("textDocument/definition", {
            "textDocument": {"uri": main_uri},
            "position": {"line": 25, "character": 31},
        })
        assert def_dbl["result"]["uri"] == helper_uri
        assert def_dbl["result"]["range"]["start"]["line"] == 7, f"unexpected doubleVal def: {def_dbl}"

        # Local param `a` in `def addNums(a: Int, b: Int): Int = a + b` (line 16, col 35 -> col 12)
        def_param = client.request("textDocument/definition", {
            "textDocument": {"uri": main_uri},
            "position": {"line": 16, "character": 35},
        })
        assert def_param["result"]["uri"] == main_uri
        assert def_param["result"]["range"]["start"] == {"line": 16, "character": 12}, f"unexpected param def: {def_param}"

        # Local `let total` usage on line 26, col 22 -> line 25, col 8
        def_let = client.request("textDocument/definition", {
            "textDocument": {"uri": main_uri},
            "position": {"line": 26, "character": 22},
        })
        assert def_let["result"]["uri"] == main_uri
        assert def_let["result"]["range"]["start"] == {"line": 25, "character": 8}, f"unexpected let def: {def_let}"

        # Match pattern binder `val` usage on line 19, col 18 -> line 19, col 9
        def_patvar = client.request("textDocument/definition", {
            "textDocument": {"uri": main_uri},
            "position": {"line": 19, "character": 18},
        })
        assert def_patvar["result"]["uri"] == main_uri
        assert def_patvar["result"]["range"]["start"] == {"line": 19, "character": 9}, f"unexpected patvar def: {def_patvar}"

        # Destructured `let (px, py)` usage `px` on line 25, col 25 -> line 24, col 9
        def_destr = client.request("textDocument/definition", {
            "textDocument": {"uri": main_uri},
            "position": {"line": 25, "character": 25},
        })
        assert def_destr["result"]["uri"] == main_uri
        assert def_destr["result"]["range"]["start"] == {"line": 24, "character": 9}, f"unexpected destructured let def: {def_destr}"

        # Cross-module pattern constructor `Wrap` on line 19, col 5 -> helper.gsa line 1
        def_ctor = client.request("textDocument/definition", {
            "textDocument": {"uri": main_uri},
            "position": {"line": 19, "character": 5},
        })
        assert def_ctor["result"] is not None, "cross-module pattern ctor definition returned null"
        assert def_ctor["result"]["uri"] == helper_uri, f"expected {helper_uri}, got {def_ctor}"
        assert def_ctor["result"]["range"]["start"]["line"] == 1, f"unexpected Boxed/Wrap def: {def_ctor}"

        # 6. completion: `std.`, `sys.`, `std.str.`, local defs, and preludePrimSpecs (`MutArray`, `immArrayGet`, no `__conc*`)
        comp_src = main_src + "\ndef _c1() = std.\ndef _c2() = sys.\ndef _c3() = std.str.\ndef _c4() = add\ndef _c5() = arrayN\ndef _c6() = immArray\n"
        client.notify("textDocument/didChange", {
            "textDocument": {"uri": main_uri, "version": 2},
            "contentChanges": [{"text": comp_src}],
        })
        _ = client.wait_notification("textDocument/publishDiagnostics")

        comp_std = client.request("textDocument/completion", {
            "textDocument": {"uri": main_uri},
            "position": {"line": 29, "character": 16},
        })
        std_labels = {it["label"] for it in comp_std["result"]["items"]}
        assert {"str", "json", "list", "vec", "map", "option", "result"}.issubset(std_labels)

        comp_sys = client.request("textDocument/completion", {
            "textDocument": {"uri": main_uri},
            "position": {"line": 30, "character": 16},
        })
        sys_labels = {it["label"] for it in comp_sys["result"]["items"]}
        assert {"io", "fs", "env", "proc"}.issubset(sys_labels)

        comp_str = client.request("textDocument/completion", {
            "textDocument": {"uri": main_uri},
            "position": {"line": 31, "character": 20},
        })
        str_labels = {it["label"] for it in comp_str["result"]["items"]}
        assert {"intToStr", "strStartsWith", "strJoin"}.issubset(str_labels)

        comp_local = client.request("textDocument/completion", {
            "textDocument": {"uri": main_uri},
            "position": {"line": 32, "character": 15},
        })
        local_labels = {it["label"] for it in comp_local["result"]["items"]}
        assert "addNums" in local_labels

        comp_arr = client.request("textDocument/completion", {
            "textDocument": {"uri": main_uri},
            "position": {"line": 33, "character": 18},
        })
        arr_item = next(it for it in comp_arr["result"]["items"] if it["label"] == "arrayNew")
        assert "MutArray" in arr_item["detail"], f"expected MutArray in arrayNew detail, got: {arr_item}"

        comp_imm = client.request("textDocument/completion", {
            "textDocument": {"uri": main_uri},
            "position": {"line": 34, "character": 20},
        })
        imm_labels = {it["label"] for it in comp_imm["result"]["items"]}
        assert "immArrayGet" in imm_labels and not any(l.startswith("__") for l in imm_labels)

        # 7. UTF-8 (CJK + 4-byte emoji surrogate pair) & CRLF position accuracy
        crlf_path = root / "utf8_crlf.gsa"
        # Line 0: `def greet(n: Int): Int = n + 1\r\n`
        # Line 1: `def main(): Void = { let _ = "你好🚀"; let v = greet(7); () }\r\n`
        # UTF-16 columns on line 1:
        # `def main(): Void = { let _ = "` -> 30 chars
        # `你` (1) + `好` (1) + `🚀` (2) = 4 UTF-16 units -> col 34
        # `"; let v = ` -> 11 chars -> `greet` starts at UTF-16 col 45!
        crlf_src = "def greet(n: Int): Int = n + 1\r\ndef main(): Void = { let _ = \"你好🚀\"; let v = greet(7); () }\r\n"
        crlf_path.write_bytes(crlf_src.encode("utf-8"))
        crlf_uri = path_to_uri(crlf_path)
        client.notify("textDocument/didOpen", {
            "textDocument": {"uri": crlf_uri, "languageId": "geisha", "version": 1, "text": crlf_src},
        })
        diag_crlf = client.wait_diag_for(crlf_uri)
        assert diag_crlf == [], f"unexpected CRLF diagnostics: {diag_crlf}"
        def_utf8 = client.request("textDocument/definition", {
            "textDocument": {"uri": crlf_uri},
            "position": {"line": 1, "character": 46},
        })
        assert def_utf8["result"] is not None, "UTF-8/CRLF definition returned null"
        assert def_utf8["result"]["range"]["start"]["line"] == 0, f"unexpected UTF-8/CRLF def: {def_utf8}"

        # 8. didChange with type error -> publishDiagnostics with exact line & severity 1
        client.notifications.clear()
        bad_src = (
            "def main(): Void = {\n"
            "    let bad: Int = \"oops\";\n"
            "    ()\n"
            "}\n"
        )
        client.notify("textDocument/didChange", {
            "textDocument": {"uri": main_uri, "version": 3},
            "contentChanges": [{"text": bad_src}],
        })
        diags = client.wait_diag_for(main_uri)
        assert len(diags) == 1 and diags[0]["severity"] == 1 and diags[0]["source"] == "geisha"
        assert diags[0]["range"]["start"]["line"] == 1
        assert "Int" in diags[0]["message"] and "String" in diags[0]["message"]

        # 9. didChange back to valid -> clears diagnostics
        client.notify("textDocument/didChange", {
            "textDocument": {"uri": main_uri, "version": 4},
            "contentChanges": [{"text": main_src}],
        })
        diag_clear = client.wait_diag_for(main_uri)
        assert diag_clear == []

        # 10. unknown method -> -32601
        unk = client.request("geisha/nonExistentMethod", {})
        assert unk["error"]["code"] == -32601

        # 11. didClose removes cached doc state (subsequent hover returns null)
        client.notify("textDocument/didClose", {"textDocument": {"uri": main_uri}})
        _ = client.wait_diag_for(main_uri)
        hover_after_close = client.request("textDocument/hover", {
            "textDocument": {"uri": main_uri},
            "position": {"line": 25, "character": 18},
        })
        assert hover_after_close["result"] is None, f"expected null hover after didClose, got: {hover_after_close}"

        # 11b. Project `tests/spec.gsa` importing own package (`use demo_lib.hello`) -> 0 diagnostics, cross-file def, no geisha.lock written
        proj_dir = root / "demo_lib_proj"
        (proj_dir / "src").mkdir(parents=True)
        (proj_dir / "tests").mkdir(parents=True)
        (proj_dir / "geisha.toml").write_text('name = "demo_lib"\nversion = "0.1.0"\n', encoding="utf-8")
        lib_path = proj_dir / "src" / "demo_lib.gsa"
        lib_path.write_text("/// Return 42.\npub def hello(): Int = 42\n", encoding="utf-8")
        spec_path = proj_dir / "tests" / "spec.gsa"
        spec_src = "use demo_lib.hello\n\ndef main(): Void = {\n    let v = hello();\n    ()\n}\n"
        spec_path.write_text(spec_src, encoding="utf-8")
        spec_uri = path_to_uri(spec_path)
        lib_uri = path_to_uri(lib_path)
        client.notify("textDocument/didOpen", {
            "textDocument": {"uri": spec_uri, "languageId": "geisha", "version": 1, "text": spec_src},
        })
        diag_spec = client.wait_diag_for(spec_uri)
        assert diag_spec == [], f"expected 0 diagnostics for self-pkg test import, got: {diag_spec}"
        assert not (proj_dir / "geisha.lock").exists(), "LSP must not write geisha.lock during read-only analysis"
        def_self = client.request("textDocument/definition", {
            "textDocument": {"uri": spec_uri},
            "position": {"line": 3, "character": 13},
        })
        assert def_self["result"] is not None and def_self["result"]["uri"] == lib_uri, f"expected def in {lib_uri}, got: {def_self}"

        # 11c. Multi-file unsaved in-memory overlay & dependency diagnostic URI attribution
        ov_dir = root / "overlay_proj"
        ov_dir.mkdir(parents=True)
        a_path = ov_dir / "a.gsa"
        b_path = ov_dir / "b.gsa"
        a_disk = "pub def value(): Int = 42\n"
        b_src = "use a.value\n\ndef main(): Void = {\n    let s: String = value();\n    ()\n}\n"
        a_path.write_text(a_disk, encoding="utf-8")
        b_path.write_text(b_src, encoding="utf-8")
        a_uri = path_to_uri(a_path)
        b_uri = path_to_uri(b_path)

        client.notify("textDocument/didOpen", {
            "textDocument": {"uri": a_uri, "languageId": "geisha", "version": 1, "text": a_disk},
        })
        assert client.wait_diag_for(a_uri) == []
        client.notify("textDocument/didOpen", {
            "textDocument": {"uri": b_uri, "languageId": "geisha", "version": 1, "text": b_src},
        })
        b_diags_init = client.wait_diag_for(b_uri)
        assert len(b_diags_init) == 1 and "Int" in b_diags_init[0]["message"], f"expected Int/String mismatch in b.gsa, got: {b_diags_init}"

        # Unsaved edit to a.gsa changes return type to String -> b.gsa diagnostics automatically clear!
        client.notifications.clear()
        a_unsaved_ok = "pub def value(): String = \"ok\"\n"
        client.notify("textDocument/didChange", {
            "textDocument": {"uri": a_uri, "version": 2},
            "contentChanges": [{"text": a_unsaved_ok}],
        })
        assert client.wait_diag_for(a_uri) == []
        assert client.wait_diag_for(b_uri) == [], "expected b.gsa diagnostics to clear using unsaved a.gsa overlay"

        # Unsaved type error in a.gsa -> error attributed to a.gsa URI, b.gsa stays clean
        client.notifications.clear()
        a_unsaved_err = "pub def value(): String = 999\n"
        client.notify("textDocument/didChange", {
            "textDocument": {"uri": a_uri, "version": 3},
            "contentChanges": [{"text": a_unsaved_err}],
        })
        a_err_diags = client.wait_diag_for(a_uri)
        assert len(a_err_diags) == 1 and a_err_diags[0]["range"]["start"]["line"] == 0, f"expected error on a.gsa: {a_err_diags}"
        b_clean = client.wait_diag_for(b_uri)
        assert b_clean == [], f"expected dependency error attributed to a.gsa rather than b.gsa, got: {b_clean}"

        # 12. shutdown -> requests return -32600; exit -> rc == 0
        shut = client.request("shutdown")
        assert shut["result"] is None
        post_shut = client.request("textDocument/hover", {
            "textDocument": {"uri": crlf_uri},
            "position": {"line": 0, "character": 4},
        })
        assert post_shut["error"]["code"] == -32600, f"expected -32600 after shutdown, got: {post_shut}"
        client.notify("exit")
        rc = client.proc.wait(timeout=10)
        assert rc == 0, f"expected exit code 0, got {rc}"

    print("PASS [geisha_lsp]: JSON-RPC stdio round-trip (diagnostics, hover, definition, documentSymbol, completion, UTF-8/CRLF, didClose, shutdown) verified!")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
