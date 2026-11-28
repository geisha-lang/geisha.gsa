import CoreGeisha

open CoreGeisha

def main (args : List String) : IO UInt32 := do
  match args with
  | ["--verify-vcg"] =>
    match runVcgSelfCheck with
    | .error err =>
      IO.eprintln s!"VCG SELF-CHECK ERROR: {err}"
      return 1
    | .ok msg =>
      IO.println msg
      return 0
  | ["--verify-vcg", path] =>
    let src ← IO.FS.readFile path
    match Parser.parseProgram src with
    | .error err =>
      IO.eprintln s!"PARSE ERROR ({path}): {err}"
      return 1
    | .ok prog =>
      match verifyGscoreProgram prog.funs prog.externs prog.vcgFormat with
      | .error err =>
        IO.eprintln s!"VCG ERROR ({path}): {err}"
        return 1
      | .ok (fnCount, obs) =>
        let mut closedProved : Nat := 0
        let mut smtProved : Nat := 0
        for (fnName, ob) in obs do
          if !sformHasSym ob then
            match evalSFormClosed ob with
            | some true => closedProved := closedProved + 1
            | some false =>
              IO.eprintln s!"VCG REFUTED (Lean kernel) in '{fnName}': obligation evaluated to false"
              return 1
            | none =>
              IO.eprintln s!"VCG UNKNOWN (Lean kernel) in '{fnName}': closed obligation could not be decided"
              return 1
          else
            match emitObSmt2 ob with
            | none =>
              IO.eprintln s!"VCG FAIL-CLOSED in '{fnName}': obligation could not be exported to SMT-LIB2"
              return 1
            | some smtScript =>
              let child ← IO.Process.spawn {
                cmd := "z3"
                args := #["-in"]
                stdin := .piped
                stdout := .piped
                stderr := .piped
              }
              let (stdin, child) ← child.takeStdin
              stdin.putStr smtScript
              stdin.flush
              let stdout ← child.stdout.readToEnd
              let stderr ← child.stderr.readToEnd
              let exitCode ← child.wait
              let firstLine := (stdout.splitOn "\n").headD "" |>.trimAscii.toString
              if exitCode == 0 && firstLine == "unsat" then
                smtProved := smtProved + 1
              else
                IO.eprintln s!"VCG REFUTED/UNKNOWN (Z3: '{firstLine}', exit {exitCode}) in '{fnName}': {stderr.trimAscii.toString}"
                return 1
        IO.println s!"VERIFIED VCG GSCORE OK ({fnCount} functions, {obs.length} VCs proved: {closedProved} in Lean kernel, {smtProved} via Z3): {path}"
        return 0
  | [path] =>
    let src ← IO.FS.readFile path
    match Parser.parseProgram src with
    | .error err =>
      IO.eprintln s!"PARSE ERROR ({path}): {err}"
      return 1
    | .ok prog =>
      match checkProgram prog with
      | .error err =>
        IO.eprintln s!"VERIFICATION ERROR ({path}): {err}"
        return 1
      | .ok () =>
        let stackVarCount := prog.stackAllocs.foldl (fun acc s => acc + s.vars.length) 0
        let gcMaskCount := prog.gcMasks.foldl (fun acc s => acc + s.variants.length) 0
        IO.println s!"VERIFIED OK: {path} ({prog.adts.length} ADTs, {prog.funs.length} functions, {prog.externs.length} externs, {stackVarCount} stack-promoted cells, {gcMaskCount} LP64 GC variant masks — guaranteed ¬IsStuck, ¬MatchFailure, ¬HasDataRace across Task/MVar/Chan/Actor, ¬DanglingStackAccess, & exact LP64 40-bit GC pointer masks)"
        return 0
  | ["--eval", fnName, path] =>
    let src ← IO.FS.readFile path
    match Parser.parseProgram src with
    | .error err =>
      IO.eprintln s!"PARSE ERROR ({path}): {err}"
      return 1
    | .ok prog =>
      match checkProgram prog with
      | .error err =>
        IO.eprintln s!"VERIFICATION ERROR ({path}): {err}"
        return 1
      | .ok () =>
        match prog.funs.find? (·.name == fnName) with
        | none =>
          IO.eprintln s!"EVAL ERROR ({path}): unknown function '{fnName}'"
          return 1
        | some fd =>
          if !fd.params.isEmpty then
            IO.eprintln s!"EVAL ERROR ({path}): function '{fnName}' must take 0 parameters"
            return 1
          else
            match runSteps prog.toAdtEnv prog.toFunEnv 1000000 fd.body [] with
            | .error err =>
              IO.eprintln s!"EVAL ERROR ({path}): {err}"
              return 1
            | .ok (val, _) =>
              IO.println (formatEvalValue val)
              return 0
  | _ =>
    IO.eprintln "Usage: geisha-check [--eval <fn> | --verify-vcg [program.gscore]] <program.gscore>"
    return 2
