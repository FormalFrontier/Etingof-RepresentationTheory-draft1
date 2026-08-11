import Mathlib.Lean.CoreM

/-!
Private migration utility.  It exports declaration types from the frozen source
environment; it is not part of either release repository.
-/

open Lean

namespace Release.ExportDeclarationTypes

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

private def runMeta {α} (x : MetaM α) : CoreM α := do
  let stateful := ReaderT.run x ({} : Meta.Context)
  let (result, _) ← StateRefT'.run stateful ({} : Meta.State)
  return result

private def prettyType (type : Expr) : CoreM String := do
  let rendered ← runMeta <| withOptions
    (fun options => options
      |>.setBool `pp.fullNames true
      |>.setBool `pp.universes true
      |>.setBool `pp.explicit false)
    (Meta.ppExpr type)
  return rendered.pretty 120

private def jsonString (value : String) : String :=
  (Json.str value).compress

private def jsonStrings (values : Array String) : String :=
  "[" ++ String.intercalate "," (values.toList.map jsonString) ++ "]"

private def entryLT (a b : Name × ConstantInfo) : Bool :=
  a.1.toString < b.1.toString

private def dependencyLT (a b : Name) : Bool := a.toString < b.toString

private def isGenerated (name : String) : Bool :=
  name.contains "._proof_" || name.contains "._eq_" || name.contains "._unary" ||
    name.contains "._match_" || name.contains "._aux" || name.contains ".match_"

private def needsPrettyType (name : Name) : Bool :=
  let value := name.toString
  !value.startsWith "_private." && !isGenerated value

def exportAll (handle : IO.FS.Handle) : CoreM Unit := do
  let env ← getEnv
  let entries := (env.constants.toList.toArray.filter fun (name, _) =>
    (moduleOf env name).startsWith "EtingofRepresentationTheory").qsort entryLT
  IO.eprintln s!"exporting {entries.size} project declaration types"
  for (name, info) in entries do
    let dependencies := (info.type.getUsedConstants.filter fun dependency =>
      (moduleOf env dependency).startsWith "EtingofRepresentationTheory").qsort dependencyLT
    let prettyJson ← if needsPrettyType name then
      pure <| jsonString (← prettyType info.type)
    else
      pure "null"
    let line := "{" ++
      "\"old_fqn\":" ++ jsonString name.toString ++ "," ++
      "\"provider_module\":" ++ jsonString (moduleOf env name) ++ "," ++
      "\"kind\":" ++ jsonString (kindOf info) ++ "," ++
      "\"pretty_type\":" ++ prettyJson ++ "," ++
      "\"structural_type_hash\":" ++ jsonString (toString (hash info.type)) ++ "," ++
      "\"type_dependencies\":" ++ jsonStrings (dependencies.map Name.toString) ++
      "}"
    handle.putStrLn line

end Release.ExportDeclarationTypes

unsafe def main (args : List String) : IO Unit := do
  let output ← match args with
    | [path] => pure path
    | _ => throw <| IO.userError "usage: export_declaration_types OUTPUT.jsonl"
  Lean.initSearchPath (← Lean.findSysroot)
  IO.FS.withFile output .write fun handle =>
    CoreM.withImportModules #[`EtingofRepresentationTheory]
      (Release.ExportDeclarationTypes.exportAll handle)
