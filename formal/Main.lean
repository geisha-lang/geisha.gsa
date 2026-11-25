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
        IO.eprintln s!"TYPE ERROR ({path}): {err}"
        return 1
      | .ok () =>
        IO.println s!"VERIFIED OK: {path} ({prog.adts.length} ADTs, {prog.funs.length} functions — guaranteed ¬IsStuck & ¬HasDataRace by CoreGeisha.verified_concurrent_program_safety + verified_program_data_race_freedom)"
        return 0
  | _ =>
    IO.eprintln "Usage: geisha-check <program.gscore>"
    return 2
