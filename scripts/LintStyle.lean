import Mathlib.Tactic.Linter.TextBased

open Lean Lean.Linter Mathlib.Linter.TextBased

/-- Mathlib's text and module-name linters over explicit paths relative to `src`. -/
def main (args : List String) : IO UInt32 := do
  let opts : LinterOptions := { toOptions := {}, linterSets := {} }
  match args with
  | "text" :: root :: paths =>
    for path in paths do
      let (errors, _) ← lintFile opts (System.FilePath.mk root / path) #[]
      for err in errors do
        IO.println <| (Json.mkObj [
          ("path", toJson path),
          ("line", toJson err.lineNumber),
          ("code", toJson err.error.errorCode),
          ("message", toJson err.error.errorMessage)
        ]).compress
    return 0
  | "names" :: paths =>
    let names := paths.toArray.map fun path =>
      (path.dropEnd 5).toString.splitOn "/" |>.foldl Name.str Name.anonymous
    let casing ← modulesNotUpperCamelCase opts names
    let forbidden ← modulesOSForbidden opts names
    return if casing + forbidden == 0 then 0 else 1
  | _ => throw <| IO.userError "usage: LintStyle.lean text ROOT FILE... | names FILE..."
