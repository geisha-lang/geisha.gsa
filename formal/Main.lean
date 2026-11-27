import CoreGeisha

open CoreGeisha

def main (args : List String) : IO UInt32 := do
  match args with
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
        IO.println s!"VERIFIED OK: {path} ({prog.adts.length} ADTs, {prog.funs.length} functions, {prog.externs.length} externs, {stackVarCount} stack-promoted cells — guaranteed ¬IsStuck, ¬MatchFailure, ¬HasDataRace across Task/MVar/Chan/Actor, ¬DanglingStackAccess, & exact 40-bit GC pointer masks)"
        return 0
  | _ =>
    IO.eprintln "Usage: geisha-check <program.gscore>"
    return 2
