import Lean

/-!
Resolve exact declaration names to the modules that define them.

This helper is invoked by `validate_lean_decls.py --refresh-providers` after a
successful root build.  Keeping provider discovery here, in Lean's imported
environment, avoids unreliable source-text heuristics for generated names and
namespace nesting.
-/

open Lean

private def nameFromString (value : String) : Name :=
  value.splitOn "." |>.foldl Name.str Name.anonymous

unsafe def main (args : List String) : IO Unit := do
  let env ← importModules #[{ module := `EtingofRepresentationTheory }] {} 0
  if args == ["--all"] then
    for (name, _) in env.constants do
      if let some index := env.getModuleIdxFor? name then
        let module := env.header.moduleNames[index]!.toString
        if module.startsWith "EtingofRepresentationTheory" then
          IO.println s!"{name}\t{module}"
    return
  let namesFile ← match args with
    | [path] => pure path
    | _ => throw <| IO.userError "usage: extract_lean_decl_providers.lean NAMES_FILE"
  for rawName in (← IO.FS.lines namesFile) do
    let nameText := rawName.trimAscii.toString
    if nameText.isEmpty then continue
    let name := nameFromString nameText
    unless env.constants.contains name do
      IO.eprintln s!"unknown declaration (or namespace): {nameText}"
      throw <| IO.userError "declaration resolution failed"
    let module ← match env.getModuleIdxFor? name with
      | some index => pure env.header.moduleNames[index]!.toString
      | none => throw <| IO.userError s!"declaration has no provider module: {nameText}"
    IO.println s!"{nameText}\t{module}"
