import Lean

/-!
# Persistent book-reference metadata

`@[book_ref "Chapter6/Theorem6.5.2" (role := primary)]` associates a Lean
declaration with a stable location in the book.  The metadata is stored in a
persistent environment extension and a canonical bibliographic line with
machine-readable fields is appended to the declaration's docstring.
-/

open Lean Elab Command

namespace BookRef

/-- How a declaration contributes to the cited item in the book. -/
inductive Role where
  | primary
  | supporting
  deriving BEq, DecidableEq, Repr

namespace Role

def toString : Role → String
  | .primary => "primary"
  | .supporting => "supporting"

end Role

/-- One declaration-to-book-reference association. -/
structure Entry where
  declName : Name
  reference : String
  role : Role
  deriving BEq, Repr

/-- Persistent storage. Imported entries remain separated by module; local entries
are stored in the first component of the extension state. -/
initialize bookRefExt : SimplePersistentEnvExtension Entry (Array (Array Entry)) ←
  registerSimplePersistentEnvExtension {
    addImportedFn entries := entries
    addEntryFn entries _ := entries
  }

/-- All entries visible in an environment, before deterministic sorting. -/
def getEntries (env : Environment) : Array Entry :=
  let state := PersistentEnvExtension.getState bookRefExt env
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

/-- Validate a canonical source-item identifier.  The final optional segment is
reserved for derived overlays that do not partition the source transcription. -/
def isValidReference (reference : String) : Bool :=
  match reference.splitOn "/" with
  | [chapter, item] => isChapterSegment chapter && isSafeSegment item
  | [chapter, item, derived] =>
      isChapterSegment chapter && isSafeSegment item && isDerivedSegment derived
  | _ => false

private def jsonString (s : String) : String :=
  (Json.str s).compress

/-- The exact machine-readable line appended to a compiled docstring. -/
def citationLine (reference : String) (role : Role) : String :=
  "* Etingof et al., Introduction to Representation Theory " ++
    "[book-ref=" ++ reference ++ "; role=" ++ role.toString ++ "]"

private def entryLT (a b : Entry) : Bool :=
  if a.reference != b.reference then a.reference < b.reference
  else if a.role.toString != b.role.toString then a.role.toString < b.role.toString
  else a.declName.toString < b.declName.toString

/-- Deterministically sorted entries. -/
def getSortedEntries (env : Environment) : Array Entry :=
  (getEntries env).qsort entryLT

/-- Deterministic JSON export of every visible association. -/
def exportJson (env : Environment) : String :=
  let objects := (getSortedEntries env).map fun entry =>
    "{\"declaration\":" ++ jsonString entry.declName.toString ++
      ",\"reference\":" ++ jsonString entry.reference ++
      ",\"role\":" ++ jsonString entry.role.toString ++ "}"
  "[" ++ String.intercalate "," objects.toList ++ "]"

private def appendCitation (declName : Name) (reference : String) (role : Role) : CoreM Unit := do
  unless isValidReference reference do
    throwError "malformed book reference '{reference}'; expected (Frontmatter|Backmatter|Chapter<digits>)/<safe-item>[/Derived<digits>]"
  let env ← getEnv
  let existing := (getEntries env).filter fun entry =>
    entry.declName == declName && entry.reference == reference
  if existing.any (·.role != role) then
    throwError "conflicting book_ref roles for '{declName}' and '{reference}'"
  if existing.any (·.role == role) then
    return
  let oldDoc := (← findDocString? env declName).getD ""
  let line := citationLine reference role
  addDocStringCore declName <| if oldDoc.isEmpty then line else oldDoc ++ "\n\n" ++ line
  modifyEnv (bookRefExt.addEntry · { declName, reference, role })

declare_syntax_cat bookRefRole
syntax "primary" : bookRefRole
syntax "supporting" : bookRefRole
syntax (name := bookRef) "book_ref" str "(" "role" ":=" bookRefRole ")" : attr

initialize Lean.registerBuiltinAttribute {
  name := `bookRef
  descr := "Associate a declaration with a stable book reference."
  add := fun declName stx _kind => do
    match stx with
    | `(attr| book_ref $reference:str (role := primary)) =>
        appendCitation declName reference.getString .primary
    | `(attr| book_ref $reference:str (role := supporting)) =>
        appendCitation declName reference.getString .supporting
    | _ => throwUnsupportedSyntax
  -- The declaration's own doc comment is installed immediately before this phase,
  -- so this hook can preserve it while appending the citation line.
  applicationTime := .afterCompilation
}

/-- Define a string constant containing a compile-time snapshot of the current export.
The generated constant makes the metadata available to an ordinary executable. -/
elab "#define_book_refs_json" name:ident : command => do
  let value := exportJson (← getEnv)
  elabCommand (← `(def $name : String := $(quote value)))

end BookRef
