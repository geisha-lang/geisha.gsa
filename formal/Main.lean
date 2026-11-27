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
      match verifyGscoreProgram prog.funs with
      | .error err =>
        IO.eprintln s!"VCG ERROR ({path}): {err}"
        return 1
      | .ok msg =>
        IO.println s!"{msg}: {path}"
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
