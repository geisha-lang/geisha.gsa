// Geisha Client-Side Playground Host (`playground/geisha-playground.mjs`)
//
// Zero-dependency ES Module loader for `geisha-playground.wasm` that works in
// both browsers (via `fetch` + `WebAssembly.instantiateStreaming`) and Node.js
// (via `BufferSource` / `Uint8Array`).
// Provides `check(source)`, `compileJs(source)`, and `runJs(source)` with
// automatic frame-boundary Mark-Sweep GC.

export async function createGeishaPlayground(wasmSource) {
  const enc = new TextEncoder();
  const dec = new TextDecoder("utf-8");
  let ex = null;

  // Virtual no-op POSIX stubs for unreachable `sys.fs` branches in `loader.gsa`
  const envImports = {
    access: () => -1,
    gs_sys_file_exists: () => 0,
    fopen: () => 0,
    fclose: () => 0,
    fread: () => 0n,
    fwrite: () => 0n,
    remove: () => -1,
    gs_sys_is_dir: () => 0,
    gs_sys_mkdir: () => -1,
    gs_sys_dir_open: () => 0,
    gs_sys_dir_next: () => 0,
    gs_sys_dir_close: () => 0,
    gs_sys_file_size: () => -1n,
    gs_sys_mmap_open: () => 0,
    gs_sys_mmap_close: () => -1,
    gs_sys_write_atomic: () => -1,
    gs_sys_rename: () => -1,
    gs_sys_chmod: () => -1,
    gs_sys_file_mtime_ms: () => -1n,
    gs_sys_realpath: () => 0,
    realpath: () => 0,
    free: () => {},
    gs_log: () => {},
  };

  let instance;
  if (wasmSource instanceof ArrayBuffer || ArrayBuffer.isView(wasmSource)) {
    ({ instance } = await WebAssembly.instantiate(wasmSource, { env: envImports }));
  } else if (typeof wasmSource === "string" || wasmSource instanceof URL) {
    const resp = await fetch(wasmSource);
    if (!resp.ok) throw new Error(`Failed to fetch playground wasm: ${resp.status}`);
    if (typeof WebAssembly.instantiateStreaming === "function") {
      try {
        ({ instance } = await WebAssembly.instantiateStreaming(resp.clone(), { env: envImports }));
      } catch (_) {
        const bytes = await resp.arrayBuffer();
        ({ instance } = await WebAssembly.instantiate(bytes, { env: envImports }));
      }
    } else {
      const bytes = await resp.arrayBuffer();
      ({ instance } = await WebAssembly.instantiate(bytes, { env: envImports }));
    }
  } else {
    throw new TypeError("createGeishaPlayground expects a URL, string, ArrayBuffer, or TypedArray");
  }

  ex = instance.exports;
  ex.__geisha_init();

  function writeStr(str) {
    const raw = enc.encode(String(str ?? ""));
    const ptr = ex.gs_wasm_alloc(raw.length + 1) >>> 0;
    const view = new Uint8Array(ex.memory.buffer, ptr, raw.length + 1);
    view.set(raw);
    view[raw.length] = 0;
    return ptr;
  }

  function readStr(ptr) {
    const p = ptr >>> 0;
    if (!p) return "";
    const len = ex.gs_wasm_str_len(p) >>> 0;
    return len ? dec.decode(new Uint8Array(ex.memory.buffer, p, len)) : "";
  }

  function withGc(fn) {
    try {
      return fn();
    } finally {
      if (typeof ex.gs_wasm_gc_collect === "function") {
        ex.gs_wasm_gc_collect();
      }
    }
  }

  function check(source) {
    return withGc(() => JSON.parse(readStr(ex.geisha_check(writeStr(source)))));
  }

  function compileJs(source) {
    return withGc(() => JSON.parse(readStr(ex.geisha_compile_js(writeStr(source)))));
  }

  async function runJs(source) {
    const compiled = compileJs(source);
    if (!compiled.ok) return { ok: false, error: compiled.error, stdout: [] };
    const stdout = [];
    let partial = "";
    const flushPartial = () => {
      if (partial.length > 0) {
        stdout.push(partial);
        partial = "";
      }
    };
    const prevPrint = globalThis.__geisha_print;
    const prevWrite = globalThis.__geisha_write;
    globalThis.__geisha_print = (line) => {
      flushPartial();
      stdout.push(String(line));
    };
    globalThis.__geisha_write = (chunk) => {
      const parts = (partial + String(chunk)).split("\n");
      partial = parts.pop();
      for (const p of parts) stdout.push(p);
    };
    try {
      // Strip top-level `export ` for strict-mode Function evaluation
      const runnable = compiled.js
        .replace(/^export function /gm, "function ")
        .replace(/^export const /gm, "const ");
      const fn = new Function('"use strict";\n' + runnable);
      fn();
      flushPartial();
      return { ok: true, stdout, js: compiled.js, dts: compiled.dts };
    } catch (err) {
      flushPartial();
      return { ok: false, error: String(err && err.stack ? err.stack : err), stdout, js: compiled.js, dts: compiled.dts };
    } finally {
      if (prevPrint === undefined) delete globalThis.__geisha_print;
      else globalThis.__geisha_print = prevPrint;
      if (prevWrite === undefined) delete globalThis.__geisha_write;
      else globalThis.__geisha_write = prevWrite;
    }
  }

  return { check, compileJs, runJs, exports: ex };
}
