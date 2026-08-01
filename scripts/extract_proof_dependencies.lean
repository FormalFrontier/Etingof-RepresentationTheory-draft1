import Lean

/-!
Emit direct proof/body and type dependencies for every declaration in the root
project import.  The tab-separated output is consumed by
`scripts/finalize_proof_dependencies.py`.

`ConstantInfo.value?` hides theorem and opaque bodies by default; passing
`allowOpaque := true` is essential here.  These are the kernel terms stored in
the imported `.olean` environment, not source-identifier proxies.
-/

open Lean

private def moduleOf (env : Environment) (name : Name) : String :=
  match env.getModuleIdxFor? name with
  | some index => env.header.moduleNames[index]!.toString
  | none => "<main>"

private def kindOf : ConstantInfo → String
  | .axiomInfo _ => "axiom"
  | .defnInfo _ => "definition"
  | .thmInfo _ => "theorem"
  | .opaqueInfo _ => "opaque"
  | .quotInfo _ => "quotient"
  | .inductInfo _ => "inductive"
  | .ctorInfo _ => "constructor"
  | .recInfo _ => "recursor"

private def nameFromString (value : String) : Name :=
  value.splitOn "." |>.foldl Name.str Name.anonymous

unsafe def main (args : List String) : IO Unit := do
  let extras : Array Import := args.toArray.map fun value =>
    { module := nameFromString value }
  let env ← importModules (#[{ module := `EtingofRepresentationTheory }] ++ extras) {} 0
  for module in env.header.moduleNames do
    if module.toString.startsWith "EtingofRepresentationTheory" then
      IO.println s!"M\t{module}"
  for (name, info) in env.constants do
    let module := moduleOf env name
    unless module.startsWith "EtingofRepresentationTheory" do continue
    IO.println s!"D\t{name}\t{module}\t{kindOf info}"
    for dependency in info.type.getUsedConstants do
      let depModule := moduleOf env dependency
      if depModule.startsWith "EtingofRepresentationTheory" then
        IO.println s!"T\t{name}\t{dependency}\t{depModule}"
    if let some value := info.value? (allowOpaque := true) then
      for dependency in value.getUsedConstants do
        let depModule := moduleOf env dependency
        if depModule.startsWith "EtingofRepresentationTheory" then
          IO.println s!"P\t{name}\t{dependency}\t{depModule}"
