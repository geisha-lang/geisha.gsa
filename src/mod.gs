// Self-Hosting Geisha Compiler CLI Driver (`geisha.gs`)
//
// Usage:
//   geisha [options] <input.gs>
//
// Options:
//   -e, --emit-llvm        Emit LLVM 20 textual IR (.ll) to stdout (or `-o <file.ll>`)
//   -c, --compile-only     Compile to native object file (`.o`) without linking
//   -o <output>            Output path (executable, `.o`, or `.ll`)
//   --src-root <dir>       Multi-file module root directory
//   --runtime <path.a>     Path to `libgeisha_runtime.a` (or `$GEISHA_RUNTIME`)
//   -h, --help             Print usage help

mod ast
mod lexer
mod parser
mod stdlib_bundle
mod loader
mod infer
mod core
mod codegen

use std.option.{Option, Some, None}
use std.result.{Result, Ok, Err}
use std.buf.{bufNew, bufPushStr, bufPushByte, bufToString}
use std.path.{pathStem, pathJoin, pathDirname}
use sys.env.{argCount, argAt, getEnv}
use sys.fs.{readFile, writeFile, removeFile, fileExists}
use sys.io.eprintLn
use sys.proc.{exit, shell}
use loader.{loadSingleSourceProgram, loadProjectProgram}
use infer.inferProgram
use core.lowerToCore
use codegen.emitProgramLlvmIr

data CliOpts {
    MkCliOpts {
        optEmitIr: Bool,
        optCompileOnly: Bool,
        optOutPath: Option String,
        optSrcRoot: Option String,
        optRuntime: Option String,
        optInput: Option String,
        optHelp: Bool,
    },
}

def shellQuote(s: String): String = {
    let b = bufNew();
    bufPushByte(b, 39);
    let n = strLen(s);
    let i = cellNew(0);
    while (cellGet(i) < n) {
        let c = strByteAt(s, cellGet(i));
        if (c == 39) bufPushStr(b, "'\\''")
        else bufPushByte(b, c);
        cellSet(i, cellGet(i) + 1)
    };
    bufPushByte(b, 39);
    bufToString(b)
}

def parseCliArgs(): Result CliOpts String = {
    let emitIr = cellNew(false);
    let compOnly = cellNew(false);
    let outPath: Cell (Option String) = cellNew(None);
    let srcRoot: Cell (Option String) = cellNew(None);
    let rtPath: Cell (Option String) = cellNew(None);
    let inPath: Cell (Option String) = cellNew(None);
    let showHelp = cellNew(false);
    let errOpt: Cell (Option String) = cellNew(None);

    let argc = argCount();
    let i = cellNew(1);
    while (cellGet(i) < argc && match cellGet(errOpt) { None -> true, Some(_) -> false }) {
        let a = argAt(cellGet(i));
        if (a == "-h" || a == "--help") {
            cellSet(showHelp, true);
            cellSet(i, cellGet(i) + 1)
        } else if (a == "-e" || a == "--emit-llvm") {
            cellSet(emitIr, true);
            cellSet(i, cellGet(i) + 1)
        } else if (a == "-c" || a == "--compile-only") {
            cellSet(compOnly, true);
            cellSet(i, cellGet(i) + 1)
        } else if (a == "-o" || a == "--output") {
            if (cellGet(i) + 1 >= argc) {
                cellSet(errOpt, Some("Missing argument after '" + a + "'"))
            } else {
                cellSet(outPath, Some(argAt(cellGet(i) + 1)));
                cellSet(i, cellGet(i) + 2)
            }
        } else if (a == "--src-root") {
            if (cellGet(i) + 1 >= argc) {
                cellSet(errOpt, Some("Missing directory after '--src-root'"))
            } else {
                cellSet(srcRoot, Some(argAt(cellGet(i) + 1)));
                cellSet(i, cellGet(i) + 2)
            }
        } else if (a == "--runtime") {
            if (cellGet(i) + 1 >= argc) {
                cellSet(errOpt, Some("Missing archive path after '--runtime'"))
            } else {
                cellSet(rtPath, Some(argAt(cellGet(i) + 1)));
                cellSet(i, cellGet(i) + 2)
            }
        } else if (strLen(a) > 0 && strByteAt(a, 0) == 45) {
            cellSet(errOpt, Some("Unknown option: '" + a + "'"))
        } else {
            cellSet(inPath, Some(a));
            cellSet(i, cellGet(i) + 1)
        }
    };

    match cellGet(errOpt) {
        Some(e) -> Err(e),
        None -> Ok(MkCliOpts {
            optEmitIr: cellGet(emitIr),
            optCompileOnly: cellGet(compOnly),
            optOutPath: cellGet(outPath),
            optSrcRoot: cellGet(srcRoot),
            optRuntime: cellGet(rtPath),
            optInput: cellGet(inPath),
            optHelp: cellGet(showHelp),
        }),
    }
}

def resolveRuntimeArchive(explicitOpt: Option String): Result String String =
    match explicitOpt {
        Some(p) ->
            if (fileExists(p)) Ok(p)
            else Err("Runtime archive not found at '" + p + "'"),
        None -> match getEnv("GEISHA_RUNTIME") {
            Some(envP) ->
                if (fileExists(envP)) Ok(envP)
                else Err("GEISHA_RUNTIME archive not found at '" + envP + "'"),
            None -> {
                let exeDir = pathDirname(argAt(0));
                let cand1 = pathJoin(exeDir, "libgeisha_runtime.a");
                let cand2 = "build/libgeisha_runtime.a";
                let cand3 = pathJoin(pathDirname(exeDir), "build/libgeisha_runtime.a");
                if (fileExists(cand1)) Ok(cand1)
                else if (fileExists(cand2)) Ok(cand2)
                else if (fileExists(cand3)) Ok(cand3)
                else Err("Could not locate libgeisha_runtime.a; pass --runtime <path> or set GEISHA_RUNTIME")
            },
        },
    }

def compileInputToIr(inputFile: String, srcRootOpt: Option String): Result String String = {
    let rawDefs = match srcRootOpt {
        Some(root) -> loadProjectProgram(inputFile, root)?,
        None -> {
            let src = readFile(inputFile)?;
            loadSingleSourceProgram(src)?
        },
    };
    let inf = inferProgram(rawDefs)?;
    let coreProg = lowerToCore(inf)?;
    Ok(emitProgramLlvmIr(coreProg))
}

def printUsage(): Void = {
    printLn("geisha — Self-hosting Geisha compiler (LLVM 20 IR backend)");
    printLn("");
    printLn("Usage: geisha [options] <input.gs>");
    printLn("");
    printLn("Options:");
    printLn("  -e, --emit-llvm      Emit LLVM 20 textual IR (.ll) to stdout or -o <file.ll>");
    printLn("  -c, --compile-only   Compile to native object file (.o) without linking");
    printLn("  -o <output>          Write output to <output>");
    printLn("  --src-root <dir>     Multi-file module source root directory");
    printLn("  --runtime <path.a>   Path to libgeisha_runtime.a (or $GEISHA_RUNTIME)");
    printLn("  -h, --help           Show this help message")
}

def runDriver(): Result Void String = {
    let opts = parseCliArgs()?;
    if (opts.optHelp) {
        printUsage();
        Ok(())
    } else {
        let inputFile = match opts.optInput {
            Some(p) -> p,
            None -> returnErr("No input .gs file specified (run with --help for usage)")?,
        };
        let llText = compileInputToIr(inputFile, opts.optSrcRoot)?;

        if (opts.optEmitIr) {
            match opts.optOutPath {
                Some(outLl) -> writeFile(outLl, llText),
                None -> {
                    printLn(llText);
                    Ok(())
                },
            }
        } else if (opts.optCompileOnly) {
            let outObj = match opts.optOutPath {
                Some(p) -> p,
                None -> pathStem(inputFile) + ".o",
            };
            let tmpLl = outObj + ".tmp.ll";
            writeFile(tmpLl, llText)?;
            let ccBin = match getEnv("CC") { Some(c) -> c, None -> "cc" };
            let cmd = "MACOSX_DEPLOYMENT_TARGET=14.0 " + ccBin + " -O2 -Wno-override-module -x ir -c "
                      + shellQuote(tmpLl) + " -o " + shellQuote(outObj);
            let rc = shell(cmd);
            let _ = removeFile(tmpLl);
            if (rc == 0) Ok(())
            else Err("C/LLVM backend failed while compiling object '" + outObj + "'")
        } else {
            let outBin = match opts.optOutPath {
                Some(p) -> p,
                None -> pathStem(inputFile),
            };
            let rtArchive = resolveRuntimeArchive(opts.optRuntime)?;
            let tmpLl = outBin + ".tmp.ll";
            writeFile(tmpLl, llText)?;
            let ccBin = match getEnv("CC") { Some(c) -> c, None -> "cc" };
            let cmd = "MACOSX_DEPLOYMENT_TARGET=14.0 " + ccBin + " -O2 -Wno-override-module -pthread -x ir "
                      + shellQuote(tmpLl) + " -x none " + shellQuote(rtArchive) + " -o " + shellQuote(outBin);
            let rc = shell(cmd);
            let _ = removeFile(tmpLl);
            if (rc == 0) Ok(())
            else Err("C/LLVM backend failed while linking executable '" + outBin + "'")
        }
    }
}

def returnErr(msg: String): Result String String = Err(msg)

def main(): Void = match runDriver() {
    Ok(_) -> (),
    Err(msg) -> {
        eprintLn("Compiling error:\n" + msg);
        exit(1)
    },
}
