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
        assert caps["referencesProvider"] is True
        assert caps["renameProvider"]["prepareProvider"] is True
        assert caps["inlayHintProvider"] is True
        assert "quickfix" in caps["codeActionProvider"]["codeActionKinds"]
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

        # 11d. Directory symlink project: unsaved overlay still hits canonical path & preserves client symlink URI
        real_proj = root / "real_sym_proj"
        (real_proj / "src").mkdir(parents=True)
        (real_proj / "geisha.toml").write_text('name = "sym_proj"\nversion = "0.1.0"\n', encoding="utf-8")
        (real_proj / "src" / "dep.gsa").write_text("pub def msg(): Int = 1\n", encoding="utf-8")
        app_src = "use dep.msg\n\ndef main(): Void = {\n    let s: String = msg();\n    ()\n}\n"
        (real_proj / "src" / "app.gsa").write_text(app_src, encoding="utf-8")
        link_proj = root / "link_sym_proj"
        os.symlink(real_proj, link_proj)
        # Deliberately construct non-resolved symlink URIs (just like VS Code opening a symlinked folder)
        dep_link_uri = "file://" + str(link_proj / "src" / "dep.gsa")
        app_link_uri = "file://" + str(link_proj / "src" / "app.gsa")

        client.notifications.clear()
        client.notify("textDocument/didOpen", {
            "textDocument": {"uri": dep_link_uri, "languageId": "geisha", "version": 1, "text": "pub def msg(): Int = 1\n"},
        })
        assert client.wait_diag_for(dep_link_uri) == []
        client.notify("textDocument/didOpen", {
            "textDocument": {"uri": app_link_uri, "languageId": "geisha", "version": 1, "text": app_src},
        })
        app_init = client.wait_diag_for(app_link_uri)
        assert len(app_init) == 1 and "Int" in app_init[0]["message"], f"expected Int/String error via symlink, got: {app_init}"

        # Unsaved edit via symlink URI updates canonical overlay -> app.gsa via symlink clears!
        # Also shift `msg` to line 2 in the unsaved buffer so definition verifies BOTH symlink URI & unsaved range!
        client.notifications.clear()
        client.notify("textDocument/didChange", {
            "textDocument": {"uri": dep_link_uri, "version": 2},
            "contentChanges": [{"text": "// shifted in unsaved buffer\n\npub def msg(): String = \"ok\"\n"}],
        })
        assert client.wait_diag_for(dep_link_uri) == []
        assert client.wait_diag_for(app_link_uri) == [], "expected symlinked app.gsa to clear via canonicalized overlay"
        def_sym = client.request("textDocument/definition", {
            "textDocument": {"uri": app_link_uri},
            "position": {"line": 3, "character": 22},
        })
        assert def_sym["result"] is not None, "symlink cross-file definition returned null"
        assert def_sym["result"]["uri"] == dep_link_uri, f"expected symlink URI {dep_link_uri}, got {def_sym}"
        assert def_sym["result"]["range"]["start"]["line"] == 2, f"expected unsaved buffer line 2, got {def_sym}"

        # Unsaved error in symlinked dep.gsa -> diagnostic preserves client's symlink URI
        client.notifications.clear()
        client.notify("textDocument/didChange", {
            "textDocument": {"uri": dep_link_uri, "version": 3},
            "contentChanges": [{"text": "pub def msg(): String = 123\n"}],
        })
        dep_link_err = client.wait_diag_for(dep_link_uri)
        assert len(dep_link_err) == 1 and dep_link_err[0]["range"]["start"]["line"] == 0, f"expected error on symlink URI {dep_link_uri}: {dep_link_err}"
        assert client.wait_diag_for(app_link_uri) == []

        # 11e. Scope-aware references & rename (shadowing, sibling functions, struct fields, cross-file & unsaved overlay)
        ref_dir = root / "refactor_proj"
        ref_dir.mkdir(parents=True)
        lib_ref_path = ref_dir / "geom.gsa"
        lib_ref_src = (
            "pub data Vec2 { x: Int, y: Int }\n"
            "pub data Other { x: Int }\n"
            "pub data Color {\n"
            "    Red,\n"
            "    Blue(Int),\n"
            "}\n"
            "pub def scale(v: Vec2, factor: Int): Int = v.x * factor + v.y\n"
        )
        app_ref_path = ref_dir / "app.gsa"
        app_ref_src = (
            "use geom.{Vec2, Other, Color, Red, Blue, scale}\n"
            "\n"
            "def scopedShadow(): Int = {\n"
            "    let x = 1;\n"
            "    let y = x + 2;\n"
            "    let x = 10;\n"
            "    x + y\n"
            "}\n"
            "\n"
            "def siblingScope(): Int = {\n"
            "    let x = 99;\n"
            "    x\n"
            "}\n"
            "\n"
            "def useGeom(c: Color): Int = {\n"
            "    let p = Vec2 { x: 3, y: 4 };\n"
            "    let o = Other { x: 5 };\n"
            "    let explicit: Int = p.x + o.x;\n"
            "    let res = scale(p, 2) + explicit;\n"
            "    match c {\n"
            "        Red -> res,\n"
            "        Blue(n) -> res + n,\n"
            "    }\n"
            "}\n"
        )
        lib_ref_path.write_text(lib_ref_src, encoding="utf-8")
        app_ref_path.write_text(app_ref_src, encoding="utf-8")
        lib_ref_uri = path_to_uri(lib_ref_path)
        app_ref_uri = path_to_uri(app_ref_path)

        client.notifications.clear()
        client.notify("textDocument/didOpen", {
            "textDocument": {"uri": lib_ref_uri, "languageId": "geisha", "version": 1, "text": lib_ref_src},
        })
        assert client.wait_diag_for(lib_ref_uri) == []
        client.notify("textDocument/didOpen", {
            "textDocument": {"uri": app_ref_uri, "languageId": "geisha", "version": 1, "text": app_ref_src},
        })
        assert client.wait_diag_for(app_ref_uri) == []

        # References on outer `x` (line 3, col 8: `let x = 1;`): only line 3 & line 4 (NOT line 5/6 or sibling line 10/11)
        refs_outer_incl = client.request("textDocument/references", {
            "textDocument": {"uri": app_ref_uri},
            "position": {"line": 3, "character": 8},
            "context": {"includeDeclaration": True},
        })
        outer_lines = sorted(r["range"]["start"]["line"] for r in refs_outer_incl["result"])
        assert outer_lines == [3, 4], f"expected outer x refs on lines [3, 4], got {refs_outer_incl}"

        refs_outer_excl = client.request("textDocument/references", {
            "textDocument": {"uri": app_ref_uri},
            "position": {"line": 3, "character": 8},
            "context": {"includeDeclaration": False},
        })
        outer_excl_lines = sorted(r["range"]["start"]["line"] for r in refs_outer_excl["result"])
        assert outer_excl_lines == [4], f"expected outer x refs (excl decl) on [4], got {refs_outer_excl}"

        # References on inner shadowed `x` (line 5, col 8): only lines 5 & 6
        refs_inner = client.request("textDocument/references", {
            "textDocument": {"uri": app_ref_uri},
            "position": {"line": 5, "character": 8},
            "context": {"includeDeclaration": True},
        })
        inner_lines = sorted(r["range"]["start"]["line"] for r in refs_inner["result"])
        assert inner_lines == [5, 6], f"expected inner x refs on [5, 6], got {refs_inner}"

        # References on Vec2.x field (line 17, col 26: `p.x`): geom.gsa decl + v.x + app.gsa Vec2{x:3} + p.x (NOT Other.x!)
        refs_field = client.request("textDocument/references", {
            "textDocument": {"uri": app_ref_uri},
            "position": {"line": 17, "character": 26},
            "context": {"includeDeclaration": True},
        })
        field_uris_lines = sorted((r["uri"], r["range"]["start"]["line"]) for r in refs_field["result"])
        assert (lib_ref_uri, 0) in field_uris_lines and (lib_ref_uri, 6) in field_uris_lines, f"missing geom.gsa Vec2.x refs: {field_uris_lines}"
        assert (app_ref_uri, 15) in field_uris_lines and (app_ref_uri, 17) in field_uris_lines, f"missing app.gsa Vec2.x refs: {field_uris_lines}"
        assert (lib_ref_uri, 1) not in field_uris_lines and (app_ref_uri, 16) not in field_uris_lines, f"Other.x leaked into Vec2.x refs: {field_uris_lines}"

        # prepareRename: rejects keyword `let`, accepts `scale`
        prep_kw = client.request("textDocument/prepareRename", {
            "textDocument": {"uri": app_ref_uri},
            "position": {"line": 3, "character": 5},
        })
        assert prep_kw["result"] is None, f"expected null prepareRename on keyword 'let', got {prep_kw}"

        prep_scale = client.request("textDocument/prepareRename", {
            "textDocument": {"uri": app_ref_uri},
            "position": {"line": 18, "character": 16},
        })
        assert prep_scale["result"] is not None and prep_scale["result"]["placeholder"] == "scale", f"unexpected prepareRename: {prep_scale}"

        # rename: rejects keyword and invalid identifier with -32602
        bad_ren_kw = client.request("textDocument/rename", {
            "textDocument": {"uri": app_ref_uri},
            "position": {"line": 18, "character": 16},
            "newName": "match",
        })
        assert "error" in bad_ren_kw and bad_ren_kw["error"]["code"] == -32602, f"expected -32602 for keyword rename: {bad_ren_kw}"

        bad_ren_id = client.request("textDocument/rename", {
            "textDocument": {"uri": app_ref_uri},
            "position": {"line": 18, "character": 16},
            "newName": "123bad",
        })
        assert "error" in bad_ren_id and bad_ren_id["error"]["code"] == -32602, f"expected -32602 for invalid ident rename: {bad_ren_id}"

        # Cross-file rename of `scale` -> `scaleVec` across geom.gsa and app.gsa
        ren_scale = client.request("textDocument/rename", {
            "textDocument": {"uri": app_ref_uri},
            "position": {"line": 18, "character": 16},
            "newName": "scaleVec",
        })
        changes_scale = ren_scale["result"]["changes"]
        assert lib_ref_uri in changes_scale and app_ref_uri in changes_scale, f"expected cross-file rename edits: {changes_scale}"
        assert len(changes_scale[lib_ref_uri]) == 1 and changes_scale[lib_ref_uri][0]["newText"] == "scaleVec"
        assert len(changes_scale[app_ref_uri]) == 2, f"expected import + call edits in app.gsa, got: {changes_scale[app_ref_uri]}"

        # Cross-file rename of enum variant `Blue` -> `Cyan`
        ren_var = client.request("textDocument/rename", {
            "textDocument": {"uri": app_ref_uri},
            "position": {"line": 21, "character": 10},
            "newName": "Cyan",
        })
        changes_var = ren_var["result"]["changes"]
        assert lib_ref_uri in changes_var and app_ref_uri in changes_var, f"expected cross-file variant rename: {changes_var}"

        # Unsaved overlay cross-file rename: add another call to `scale` in unsaved app.gsa buffer
        app_ref_unsaved = app_ref_src + "\ndef extraCall(v: Vec2): Int = scale(v, 3)\n"
        client.notify("textDocument/didChange", {
            "textDocument": {"uri": app_ref_uri, "version": 2},
            "contentChanges": [{"text": app_ref_unsaved}],
        })
        assert client.wait_diag_for(app_ref_uri) == []
        ren_overlay = client.request("textDocument/rename", {
            "textDocument": {"uri": lib_ref_uri},
            "position": {"line": 6, "character": 9},
            "newName": "scaleVec",
        })
        assert len(ren_overlay["result"]["changes"][app_ref_uri]) == 3, f"expected 3 edits in unsaved overlay app.gsa, got: {ren_overlay}"

        # 11f. Inlay Hints: inferred `let` types (skipping explicit annotations) & function call parameter names
        hints_resp = client.request("textDocument/inlayHint", {
            "textDocument": {"uri": app_ref_uri},
            "range": {"start": {"line": 14, "character": 0}, "end": {"line": 23, "character": 0}},
        })
        hints = hints_resp["result"]
        type_hints = [(h["position"]["line"], h["label"]) for h in hints if h["kind"] == 1]
        param_hints = [(h["position"]["line"], h["label"]) for h in hints if h["kind"] == 2]
        assert any(l == 15 and "Vec2" in lbl for l, lbl in type_hints), f"expected Vec2 inlay hint on line 15: {type_hints}"
        assert any(l == 18 and "Int" in lbl for l, lbl in type_hints), f"expected Int inlay hint on line 18: {type_hints}"
        assert not any(l == 17 for l, _ in type_hints), f"explicitly annotated `let explicit: Int` on line 17 must not get type hint: {type_hints}"
        assert (18, "v:") in param_hints and (18, "factor:") in param_hints, f"expected parameter hints v: and factor: on line 18: {param_hints}"

        # 11g. Code Actions (Quick Fixes): unused var prefix `_`, missing match arm skeleton, auto-import
        qa_dir = root / "quickfix_proj"
        qa_dir.mkdir(parents=True)
        (qa_dir / "myutil.gsa").write_text("pub def magicNum(): Int = 77\n", encoding="utf-8")

        # 11g-1: Unused variable -> prefix `_`
        unused_path = qa_dir / "unused.gsa"
        unused_src = "def f(): Int = {\n    let temp = 42;\n    1\n}\n"
        unused_path.write_text(unused_src, encoding="utf-8")
        unused_uri = path_to_uri(unused_path)
        client.notify("textDocument/didOpen", {
            "textDocument": {"uri": unused_uri, "languageId": "geisha", "version": 1, "text": unused_src},
        })
        assert client.wait_diag_for(unused_uri) == []
        ca_unused = client.request("textDocument/codeAction", {
            "textDocument": {"uri": unused_uri},
            "range": {"start": {"line": 1, "character": 8}, "end": {"line": 1, "character": 12}},
            "context": {"diagnostics": []},
        })
        unused_actions = ca_unused["result"]
        assert any("_temp" in a["edit"]["changes"][unused_uri][0]["newText"] for a in unused_actions), f"expected _temp quickfix: {unused_actions}"

        # 11g-2: Missing match branch skeleton
        match_path = qa_dir / "missing_match.gsa"
        match_src = (
            "data Toggle { On, Off }\n"
            "def f(t: Toggle): Void = match t {\n"
            "    On -> (),\n"
            "}\n"
        )
        match_path.write_text(match_src, encoding="utf-8")
        match_uri = path_to_uri(match_path)
        client.notify("textDocument/didOpen", {
            "textDocument": {"uri": match_uri, "languageId": "geisha", "version": 1, "text": match_src},
        })
        match_diags = client.wait_diag_for(match_uri)
        assert len(match_diags) == 1 and "Off" in match_diags[0]["message"], f"expected missing Off diag: {match_diags}"
        ca_match = client.request("textDocument/codeAction", {
            "textDocument": {"uri": match_uri},
            "range": match_diags[0]["range"],
            "context": {"diagnostics": match_diags},
        })
        match_actions = ca_match["result"]
        assert any("Off -> ()" in a["edit"]["changes"][match_uri][0]["newText"] for a in match_actions), f"expected missing match arm quickfix: {match_actions}"

        # 11g-3: Missing symbol auto-import (both builtin std.str and sibling myutil)
        imp_path = qa_dir / "missing_imp.gsa"
        imp_src = "def f(): String = intToStr(1)\n"
        imp_path.write_text(imp_src, encoding="utf-8")
        imp_uri = path_to_uri(imp_path)
        client.notify("textDocument/didOpen", {
            "textDocument": {"uri": imp_uri, "languageId": "geisha", "version": 1, "text": imp_src},
        })
        imp_diags = client.wait_diag_for(imp_uri)
        assert len(imp_diags) == 1 and "intToStr" in imp_diags[0]["message"], f"expected undefined intToStr diag: {imp_diags}"
        ca_imp = client.request("textDocument/codeAction", {
            "textDocument": {"uri": imp_uri},
            "range": imp_diags[0]["range"],
            "context": {"diagnostics": imp_diags},
        })
        imp_actions = ca_imp["result"]
        assert any("use std.str.intToStr" in a["edit"]["changes"][imp_uri][0]["newText"] for a in imp_actions), f"expected std.str.intToStr auto-import: {imp_actions}"

        imp2_src = "def f(): Int = magicNum()\n"
        client.notify("textDocument/didChange", {
            "textDocument": {"uri": imp_uri, "version": 2},
            "contentChanges": [{"text": imp2_src}],
        })
        imp2_diags = client.wait_diag_for(imp_uri)
        assert len(imp2_diags) == 1 and "magicNum" in imp2_diags[0]["message"]
        ca_imp2 = client.request("textDocument/codeAction", {
            "textDocument": {"uri": imp_uri},
            "range": imp2_diags[0]["range"],
            "context": {"diagnostics": imp2_diags},
        })
        imp2_actions = ca_imp2["result"]
        assert any("use myutil.magicNum" in a["edit"]["changes"][imp_uri][0]["newText"] for a in imp2_actions), f"expected myutil.magicNum auto-import: {imp2_actions}"

        # 11h. Regression tests: variable capture rejection, same-name aliased imports across modules, nested module auto-import
        def apply_edits(text: str, edits: list[dict]) -> str:
            # Apply LSP TextEdits in reverse document order
            lines = text.splitlines(keepends=True)
            def pos_to_idx(l: int, c: int) -> int:
                return sum(len(lines[i]) for i in range(l)) + c
            indexed = sorted(
                ((pos_to_idx(e["range"]["start"]["line"], e["range"]["start"]["character"]),
                  pos_to_idx(e["range"]["end"]["line"], e["range"]["end"]["character"]),
                  e["newText"]) for e in edits),
                key=lambda x: (x[0], x[1]),
                reverse=True,
            )
            out = text
            for s, e, nt in indexed:
                out = out[:s] + nt + out[e:]
            return out

        # 11h-1: Variable capture rejection on rename (forward capture, reverse capture, duplicate param)
        cap_path = qa_dir / "capture.gsa"
        cap_src = (
            "def f(x: Int): Int = {\n"
            "    let y = 9;\n"
            "    x + y\n"
            "}\n"
            "def g(a: Int, b: Int): Int = a + b\n"
        )
        cap_path.write_text(cap_src, encoding="utf-8")
        cap_uri = path_to_uri(cap_path)
        client.notify("textDocument/didOpen", {
            "textDocument": {"uri": cap_uri, "languageId": "geisha", "version": 1, "text": cap_src},
        })
        assert client.wait_diag_for(cap_uri) == []
        # Rename param `x` -> `y` (would be captured by `let y = 9`)
        cap_fwd = client.request("textDocument/rename", {
            "textDocument": {"uri": cap_uri},
            "position": {"line": 0, "character": 6},
            "newName": "y",
        })
        assert "error" in cap_fwd and cap_fwd["error"]["code"] == -32602, f"expected -32602 on forward capture: {cap_fwd}"
        # Rename `let y` -> `x` (would capture param `x` in `x + y`)
        cap_rev = client.request("textDocument/rename", {
            "textDocument": {"uri": cap_uri},
            "position": {"line": 1, "character": 8},
            "newName": "x",
        })
        assert "error" in cap_rev and cap_rev["error"]["code"] == -32602, f"expected -32602 on reverse capture: {cap_rev}"
        # Rename param `a` -> `b` (duplicate parameter)
        cap_dup = client.request("textDocument/rename", {
            "textDocument": {"uri": cap_uri},
            "position": {"line": 4, "character": 6},
            "newName": "b",
        })
        assert "error" in cap_dup and cap_dup["error"]["code"] == -32602, f"expected -32602 on duplicate param: {cap_dup}"

        # 11h-2: Cross-file same-named imports with explicit `as` aliases (`use a.{load as loadA}` + `use b.{load as loadB}`)
        al_dir = root / "alias_proj"
        al_dir.mkdir(parents=True)
        ma_path = al_dir / "a.gsa"
        mb_path = al_dir / "b.gsa"
        mmain_path = al_dir / "main.gsa"
        ma_src = "pub def load(): Int = 1\n"
        mb_src = "pub def load(): Int = 2\n"
        mmain_src = (
            "use a.{load as loadA}\n"
            "use b.{load as loadB}\n"
            "def main(): Int = loadA() + loadB()\n"
        )
        ma_path.write_text(ma_src, encoding="utf-8")
        mb_path.write_text(mb_src, encoding="utf-8")
        mmain_path.write_text(mmain_src, encoding="utf-8")
        ma_uri = path_to_uri(ma_path)
        mb_uri = path_to_uri(mb_path)
        mmain_uri = path_to_uri(mmain_path)
        client.notifications.clear()
        for u, t in ((ma_uri, ma_src), (mb_uri, mb_src), (mmain_uri, mmain_src)):
            client.notify("textDocument/didOpen", {
                "textDocument": {"uri": u, "languageId": "geisha", "version": 1, "text": t},
            })
            assert client.wait_diag_for(u) == []

        # References on `a.load` must NOT include `b.gsa` or line 1 (`use b.{load as loadB}`)
        refs_a = client.request("textDocument/references", {
            "textDocument": {"uri": ma_uri},
            "position": {"line": 0, "character": 8},
            "context": {"includeDeclaration": True},
        })
        refs_a_uris = {r["uri"] for r in refs_a["result"]}
        assert mb_uri not in refs_a_uris, f"b.gsa leaked into a.load references: {refs_a}"
        mmain_ref_lines = sorted(r["range"]["start"]["line"] for r in refs_a["result"] if r["uri"] == mmain_uri)
        assert mmain_ref_lines == [0, 2], f"expected a.load refs in main.gsa on lines [0, 2], got {refs_a}"

        # Rename `a.load` -> `fetchA`: only rewrites `a.gsa` and `load` in `use a.{load as loadA}`, preserving `loadA` and leaving `b` untouched!
        ren_a = client.request("textDocument/rename", {
            "textDocument": {"uri": ma_uri},
            "position": {"line": 0, "character": 8},
            "newName": "fetchA",
        })
        ch_a = ren_a["result"]["changes"]
        assert mb_uri not in ch_a, f"b.gsa must not be edited when renaming a.load: {ch_a}"
        new_ma = apply_edits(ma_src, ch_a[ma_uri])
        new_mmain = apply_edits(mmain_src, ch_a[mmain_uri])
        assert new_ma == "pub def fetchA(): Int = 1\n", f"unexpected renamed a.gsa: {new_ma!r}"
        assert new_mmain == (
            "use a.{fetchA as loadA}\n"
            "use b.{load as loadB}\n"
            "def main(): Int = loadA() + loadB()\n"
        ), f"unexpected renamed main.gsa: {new_mmain!r}"
        # Verify renamed files typecheck cleanly with 0 diagnostics!
        client.notifications.clear()
        client.notify("textDocument/didChange", {"textDocument": {"uri": ma_uri, "version": 2}, "contentChanges": [{"text": new_ma}]})
        assert client.wait_diag_for(ma_uri) == []
        client.notify("textDocument/didChange", {"textDocument": {"uri": mmain_uri, "version": 2}, "contentChanges": [{"text": new_mmain}]})
        assert client.wait_diag_for(mmain_uri) == []

        # 11h-3: Nested module auto-import quick fix (`src/nested/helper.gsa` -> `use nested.helper.widgetMagic`) + verify 0 diagnostics after applying!
        nest_dir = root / "nested_imp_proj"
        (nest_dir / "src" / "nested").mkdir(parents=True)
        (nest_dir / "geisha.toml").write_text('name = "nested_imp"\nversion = "0.1.0"\n', encoding="utf-8")
        (nest_dir / "src" / "nested" / "helper.gsa").write_text("pub def widgetMagic(): Int = 88\n", encoding="utf-8")
        nmain_path = nest_dir / "src" / "main.gsa"
        nmain_src = "def main(): Int = widgetMagic()\n"
        nmain_path.write_text(nmain_src, encoding="utf-8")
        nmain_uri = path_to_uri(nmain_path)
        client.notifications.clear()
        client.notify("textDocument/didOpen", {
            "textDocument": {"uri": nmain_uri, "languageId": "geisha", "version": 1, "text": nmain_src},
        })
        ndiags = client.wait_diag_for(nmain_uri)
        assert len(ndiags) == 1 and "widgetMagic" in ndiags[0]["message"]
        ca_nest = client.request("textDocument/codeAction", {
            "textDocument": {"uri": nmain_uri},
            "range": ndiags[0]["range"],
            "context": {"diagnostics": ndiags},
        })
        nest_act = next(
            (a for a in ca_nest["result"] if "use nested.helper.widgetMagic" in a["edit"]["changes"][nmain_uri][0]["newText"]),
            None,
        )
        assert nest_act is not None, f"expected nested.helper auto-import quickfix, got: {ca_nest}"
        fixed_nmain = apply_edits(nmain_src, nest_act["edit"]["changes"][nmain_uri])
        client.notify("textDocument/didChange", {
            "textDocument": {"uri": nmain_uri, "version": 2},
            "contentChanges": [{"text": fixed_nmain}],
        })
        assert client.wait_diag_for(nmain_uri) == [], f"applied nested auto-import still has diagnostics! source:\n{fixed_nmain}"

        # 11h-4: Recursive type self-reference preserved when includeDeclaration=False, and type rename does NOT touch unrelated expression bodies
        rec_path = qa_dir / "rec_type.gsa"
        rec_src = (
            "use std.option.{Option, Some, None}\n"
            "data Node { val: Int, next: Option Node }\n"
            "def f(n: Node): Int = n.val\n"
        )
        rec_path.write_text(rec_src, encoding="utf-8")
        rec_uri = path_to_uri(rec_path)
        client.notify("textDocument/didOpen", {
            "textDocument": {"uri": rec_uri, "languageId": "geisha", "version": 1, "text": rec_src},
        })
        assert client.wait_diag_for(rec_uri) == []
        refs_rec_excl = client.request("textDocument/references", {
            "textDocument": {"uri": rec_uri},
            "position": {"line": 1, "character": 6},
            "context": {"includeDeclaration": False},
        })
        rec_excl_positions = sorted((r["range"]["start"]["line"], r["range"]["start"]["character"]) for r in refs_rec_excl["result"])
        assert (1, 35) in rec_excl_positions and (2, 9) in rec_excl_positions, f"expected recursive self-ref (1,35) & sig ref (2,9), got {rec_excl_positions}"
        assert (1, 5) not in rec_excl_positions, f"declaration header (1,5) must be excluded when includeDeclaration=False: {rec_excl_positions}"

        # 11h-5: Top-level same-module rename collision rejected (-32602)
        col_path = qa_dir / "collision.gsa"
        col_src = "def first(): Int = 1\ndef second(): Int = 2\ndef main(): Int = first() + second()\n"
        col_path.write_text(col_src, encoding="utf-8")
        col_uri = path_to_uri(col_path)
        client.notify("textDocument/didOpen", {
            "textDocument": {"uri": col_uri, "languageId": "geisha", "version": 1, "text": col_src},
        })
        assert client.wait_diag_for(col_uri) == []
        col_ren = client.request("textDocument/rename", {
            "textDocument": {"uri": col_uri},
            "position": {"line": 0, "character": 5},
            "newName": "second",
        })
        assert "error" in col_ren and col_ren["error"]["code"] == -32602, f"expected -32602 on top-level collision: {col_ren}"

        # 11h-6: `UseAlias` (`use m1.load as loadA`), multi-line `UseMulti` with comments (`use m1.{\n // comment\n load as chosen,\n}`),
        # and multi-line string containing `use m1.load as example` (must NOT be modified!)
        ml_dir = root / "multiline_alias_proj"
        ml_dir.mkdir(parents=True)
        m1_path = ml_dir / "m1.gsa"
        u1_path = ml_dir / "u1.gsa"
        u2_path = ml_dir / "u2.gsa"
        m1_src = "pub def load(): Int = 7\n"
        u1_src = (
            "use m1.load as loadA\n"
            "def f(): Int = {\n"
            "    let doc = \"example:\\nuse m1.load as example\\n\";\n"
            "    let _ = doc;\n"
            "    loadA()\n"
            "}\n"
        )
        u2_src = (
            "use m1.{\n"
            "    // comment before imported symbol\n"
            "    load as chosen,\n"
            "}\n"
            "pub mod inner {\n"
            "    use m1.load as innerLoad\n"
            "    pub def h(): Int = innerLoad()\n"
            "}\n"
            "def g(): Int = chosen() + inner.h()\n"
        )
        m1_path.write_text(m1_src, encoding="utf-8")
        u1_path.write_text(u1_src, encoding="utf-8")
        u2_path.write_text(u2_src, encoding="utf-8")
        m1_uri = path_to_uri(m1_path)
        u1_uri = path_to_uri(u1_path)
        u2_uri = path_to_uri(u2_path)
        client.notifications.clear()
        for u, t in ((m1_uri, m1_src), (u1_uri, u1_src), (u2_uri, u2_src)):
            client.notify("textDocument/didOpen", {
                "textDocument": {"uri": u, "languageId": "geisha", "version": 1, "text": t},
            })
            assert client.wait_diag_for(u) == []
        ren_ml = client.request("textDocument/rename", {
            "textDocument": {"uri": m1_uri},
            "position": {"line": 0, "character": 8},
            "newName": "loadV2",
        })
        ch_ml = ren_ml["result"]["changes"]
        new_m1 = apply_edits(m1_src, ch_ml[m1_uri])
        new_u1 = apply_edits(u1_src, ch_ml[u1_uri])
        new_u2 = apply_edits(u2_src, ch_ml[u2_uri])
        assert new_m1 == "pub def loadV2(): Int = 7\n", f"unexpected m1: {new_m1!r}"
        assert new_u1 == (
            "use m1.loadV2 as loadA\n"
            "def f(): Int = {\n"
            "    let doc = \"example:\\nuse m1.load as example\\n\";\n"
            "    let _ = doc;\n"
            "    loadA()\n"
            "}\n"
        ), f"unexpected u1 (string literal must NOT be modified!): {new_u1!r}"
        assert new_u2 == (
            "use m1.{\n"
            "    // comment before imported symbol\n"
            "    loadV2 as chosen,\n"
            "}\n"
            "pub mod inner {\n"
            "    use m1.loadV2 as innerLoad\n"
            "    pub def h(): Int = innerLoad()\n"
            "}\n"
            "def g(): Int = chosen() + inner.h()\n"
        ), f"unexpected u2: {new_u2!r}"
        client.notifications.clear()
        for u, t in ((m1_uri, new_m1), (u1_uri, new_u1), (u2_uri, new_u2)):
            client.notify("textDocument/didChange", {"textDocument": {"uri": u, "version": 2}, "contentChanges": [{"text": t}]})
            assert client.wait_diag_for(u) == []

        # 11h-7: Inline `ModSub` lexical scope conflict check:
        # (a) Unaliased `use m2.load` + `def fetchA` in same `pub mod inner` -> rejected (-32602)
        # (b) `def fetchA` in independent sibling `pub mod other` -> allowed!
        # (c) Aliased `use m2.load as loadA` + `def fetchA` in same `pub mod inner` -> allowed!
        ms_dir = root / "modsub_conflict_proj"
        ms_dir.mkdir(parents=True)
        m2_path = ms_dir / "m2.gsa"
        ms_user_path = ms_dir / "ms_user.gsa"
        m2_src = "pub def load(): Int = 7\n"
        ms_conflict_src = (
            "pub mod inner {\n"
            "    use m2.load\n"
            "    def fetchA(): Int = 93\n"
            "    pub def run(): Int = load() + fetchA()\n"
            "}\n"
        )
        m2_path.write_text(m2_src, encoding="utf-8")
        ms_user_path.write_text(ms_conflict_src, encoding="utf-8")
        m2_uri = path_to_uri(m2_path)
        ms_user_uri = path_to_uri(ms_user_path)
        client.notifications.clear()
        client.notify("textDocument/didOpen", {"textDocument": {"uri": m2_uri, "languageId": "geisha", "version": 1, "text": m2_src}})
        assert client.wait_diag_for(m2_uri) == []
        client.notify("textDocument/didOpen", {"textDocument": {"uri": ms_user_uri, "languageId": "geisha", "version": 1, "text": ms_conflict_src}})
        assert client.wait_diag_for(ms_user_uri) == []

        # (a) Same ModSub conflict -> must reject with -32602
        ren_ms_bad = client.request("textDocument/rename", {
            "textDocument": {"uri": m2_uri},
            "position": {"line": 0, "character": 8},
            "newName": "fetchA",
        })
        assert "error" in ren_ms_bad and ren_ms_bad["error"]["code"] == -32602, f"expected -32602 on ModSub unaliased conflict: {ren_ms_bad}"

        # (b) Independent sibling ModSub with `fetchA` -> allowed!
        ms_sibling_src = (
            "pub mod inner {\n"
            "    use m2.load\n"
            "    pub def run(): Int = load()\n"
            "}\n"
            "pub mod other {\n"
            "    pub def fetchA(): Int = 93\n"
            "}\n"
        )
        client.notifications.clear()
        client.notify("textDocument/didChange", {"textDocument": {"uri": ms_user_uri, "version": 2}, "contentChanges": [{"text": ms_sibling_src}]})
        assert client.wait_diag_for(ms_user_uri) == []
        ren_ms_sib = client.request("textDocument/rename", {
            "textDocument": {"uri": m2_uri},
            "position": {"line": 0, "character": 8},
            "newName": "fetchA",
        })
        assert "result" in ren_ms_sib and ms_user_uri in ren_ms_sib["result"]["changes"], f"expected sibling ModSub rename allowed: {ren_ms_sib}"

        # (c) Explicit alias `use m2.load as loadA` + `def fetchA` in same ModSub -> allowed!
        ms_alias_src = (
            "pub mod inner {\n"
            "    use m2.load as loadA\n"
            "    def fetchA(): Int = 93\n"
            "    pub def run(): Int = loadA() + fetchA()\n"
            "}\n"
        )
        client.notifications.clear()
        client.notify("textDocument/didChange", {"textDocument": {"uri": ms_user_uri, "version": 3}, "contentChanges": [{"text": ms_alias_src}]})
        assert client.wait_diag_for(ms_user_uri) == []
        ren_ms_al = client.request("textDocument/rename", {
            "textDocument": {"uri": m2_uri},
            "position": {"line": 0, "character": 8},
            "newName": "fetchA",
        })
        assert "result" in ren_ms_al and ms_user_uri in ren_ms_al["result"]["changes"], f"expected aliased ModSub rename allowed: {ren_ms_al}"
        new_ms_al = apply_edits(ms_alias_src, ren_ms_al["result"]["changes"][ms_user_uri])
        assert "use m2.fetchA as loadA" in new_ms_al and "loadA() + fetchA()" in new_ms_al, f"unexpected aliased ModSub rename: {new_ms_al!r}"

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

    print("PASS [geisha_lsp]: JSON-RPC stdio round-trip (diagnostics, hover, definition, references, prepareRename/rename, inlayHint, codeAction, documentSymbol, completion, UTF-8/CRLF, didClose, shutdown) verified!")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
