/-
Copyright (c) 2026 mathlib-initiative. All rights reserved.
Released under Apache 2.0 license as described in the file LICENCE.
Authors: Kim Morrison
-/
import Lean

/-!
# Source-reference metadata

This module provides persistent declaration metadata, canonical docstring
citations, and deterministic JSON export.
-/

open Lean Elab Command

namespace RepresentationTheory.Alignment

/-- How a declaration contributes to a cited source item. -/
inductive Role where
  | primary
  | supporting
  deriving BEq, DecidableEq, Repr

namespace Role

def toString : Role → String
  | .primary => "primary"
  | .supporting => "supporting"

end Role

/-- One declaration-to-source association. -/
structure Entry where
  declName : Name
  reference : String
  role : Role
  deriving BEq, Repr

initialize sourceRefExt : SimplePersistentEnvExtension Entry (Array (Array Entry)) ←
  registerSimplePersistentEnvExtension {
    addImportedFn entries := entries
    addEntryFn entries _ := entries
  }

/-- All associations visible in an environment. -/
def getEntries (env : Environment) : Array Entry :=
  let state := PersistentEnvExtension.getState sourceRefExt env
  state.2.flatten.appendList state.1

private def isAsciiLetter (c : Char) : Bool :=
  ('a' <= c && c <= 'z') || ('A' <= c && c <= 'Z')

private def isSafeTailChar (c : Char) : Bool :=
  isAsciiLetter c || c.isDigit || c == '_' || c == '.' || c == '-'

private def isSafeSegment (segment : String) : Bool :=
  match segment.toList with
  | [] => false
  | first :: rest =>
      isAsciiLetter first && rest.all isSafeTailChar && !(segment.contains "..")

private def isChapterSegment (segment : String) : Bool :=
  segment == "Frontmatter" || segment == "Backmatter" ||
    (segment.startsWith "Chapter" &&
      let number := (segment.drop "Chapter".length).toString
      !number.isEmpty && number.toList.all Char.isDigit)

private def isDerivedSegment (segment : String) : Bool :=
  segment.startsWith "Derived" &&
    let number := (segment.drop "Derived".length).toString
    !number.isEmpty && number.toList.all Char.isDigit

/-- Check a canonical source-item identifier. -/
def isValidReference (reference : String) : Bool :=
  match reference.splitOn "/" with
  | [chapter, item] => isChapterSegment chapter && isSafeSegment item
  | [chapter, item, derived] =>
      isChapterSegment chapter && isSafeSegment item && isDerivedSegment derived
  | _ => false

private def jsonString (value : String) : String :=
  (Json.str value).compress

/-- The canonical bibliographic line appended to a declaration docstring. -/
def citationLine (reference : String) (role : Role) : String :=
  "* Etingof et al., Introduction to Representation Theory " ++
    "[book-ref=" ++ reference ++ "; role=" ++ role.toString ++ "]"

private def entryLT (a b : Entry) : Bool :=
  if a.reference != b.reference then a.reference < b.reference
  else if a.role.toString != b.role.toString then a.role.toString < b.role.toString
  else a.declName.toString < b.declName.toString

/-- All associations in deterministic order. -/
def getSortedEntries (env : Environment) : Array Entry :=
  (getEntries env).qsort entryLT

/-- Export all visible associations as deterministic JSON. -/
def exportJson (env : Environment) : String :=
  let objects := (getSortedEntries env).map fun entry =>
    "{\"declaration\":" ++ jsonString entry.declName.toString ++
      ",\"reference\":" ++ jsonString entry.reference ++
      ",\"role\":" ++ jsonString entry.role.toString ++ "}"
  "[" ++ String.intercalate "," objects.toList ++ "]"

private def appendCitation (declName : Name) (reference : String) (role : Role) : CoreM Unit := do
  unless isValidReference reference do
    throwError "malformed source reference '{reference}'"
  let env ← getEnv
  let existing := (getEntries env).filter fun entry =>
    entry.declName == declName && entry.reference == reference
  if existing.any (·.role != role) then
    throwError "conflicting source_ref roles for '{declName}' and '{reference}'"
  if existing.any (·.role == role) then
    return
  let oldDoc := (← findDocString? env declName).getD ""
  let marker := "\n\n* Etingof et al., Introduction to Representation Theory "
  let baseDoc := (oldDoc.splitOn marker).head?.getD oldDoc
  let entry := { declName, reference, role }
  let entries := ((getEntries env).filter (·.declName == declName)).push entry
  let lines := (entries.qsort entryLT).map fun source =>
    citationLine source.reference source.role
  let citations := String.intercalate "\n\n" lines.toList
  addDocStringCore declName <|
    if baseDoc.isEmpty then citations else baseDoc ++ "\n\n" ++ citations
  modifyEnv (sourceRefExt.addEntry · entry)

declare_syntax_cat sourceRefRole
syntax "primary" : sourceRefRole
syntax "supporting" : sourceRefRole
syntax (name := sourceRef) "source_ref" str "(" "role" ":=" sourceRefRole ")" : attr

initialize Lean.registerBuiltinAttribute {
  name := `sourceRef
  descr := "Associate a declaration with a stable source reference."
  add := fun declName stx _kind => do
    match stx with
    | `(attr| source_ref $reference:str (role := primary)) =>
        appendCitation declName reference.getString .primary
    | `(attr| source_ref $reference:str (role := supporting)) =>
        appendCitation declName reference.getString .supporting
    | _ => throwUnsupportedSyntax
  applicationTime := .afterCompilation
}

/-- Define a string constant containing a compile-time association snapshot. -/
elab "#define_source_refs_json" name:ident : command => do
  let value := exportJson (← getEnv)
  elabCommand (← `(def $name : String := $(quote value)))

end RepresentationTheory.Alignment
