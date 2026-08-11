import BookRef.Collected

open Lean
open BookRef

private def expectedJson : String :=
  "[{\"declaration\":\"BookRef.Examples.sampleDefinition\",\"reference\":\"Chapter2/Definition2.1\",\"role\":\"primary\"}," ++
  "{\"declaration\":\"BookRef.Examples.theorem652\",\"reference\":\"Chapter6/Theorem6.5.2\",\"role\":\"primary\"}," ++
  "{\"declaration\":\"BookRef.Examples.theorem652_helper\",\"reference\":\"Chapter6/Theorem6.5.2\",\"role\":\"supporting\"}," ++
  "{\"declaration\":\"BookRef.Duplicate.exactDuplicateIsIdempotent\",\"reference\":\"Chapter9/Theorem9.1\",\"role\":\"primary\"}]"

run_cmd do
  let actual := exportJson (← getEnv)
  unless actual == expectedJson do
    throwError "unexpected JSON export\nexpected: {expectedJson}\nactual:   {actual}"
  let some doc ← findDocString? (← getEnv) `BookRef.Examples.theorem652
    | throwError "compiled docstring was not found"
  let line := citationLine "Chapter6/Theorem6.5.2" .primary
  unless doc.endsWith line do
    throwError "docstring does not end in canonical citation line: {doc}"
  unless doc.startsWith "A theorem with existing prose" do
    throwError "the original docstring prose was not preserved: {doc}"
  unless BookRef.Collected.collectedBookRefsJson == expectedJson do
    throwError "compile-time executable snapshot differs from the environment export"

run_cmd do
  unless isValidReference "Chapter6/Theorem6.5.2" do
    throwError "valid canonical reference was rejected"
  unless isValidReference "Frontmatter/TableOfContents" do
    throwError "frontmatter reference was rejected"
  unless isValidReference "Backmatter/ReferencesHistorical" do
    throwError "backmatter reference was rejected"
  unless isValidReference "Chapter2/Discussion_after_Theorem2.1.1/Derived01" do
    throwError "derived overlay reference was rejected"
  for malformed in #["Chapter/Theorem6.5.2", "Chapter6/Theorem6..5",
      "chapter6/Theorem6.5.2"] do
    if isValidReference malformed then
      throwError "malformed reference was accepted: {malformed}"

run_cmd do
  let env ← getEnv
  let entries := (getEntries env).filter fun entry =>
    entry.declName == `BookRef.Duplicate.exactDuplicateIsIdempotent &&
      entry.reference == "Chapter9/Theorem9.1"
  unless entries.size == 1 do
    throwError "exact duplicate produced {entries.size} environment entries instead of one"
  let some doc ← findDocString? env `BookRef.Duplicate.exactDuplicateIsIdempotent
    | throwError "duplicate-test docstring was not found"
  let line := citationLine "Chapter9/Theorem9.1" .primary
  unless (doc.splitOn line).length == 2 do
    throwError "exact duplicate appended more than one citation line: {doc}"

/-- error: malformed book reference 'not/a/reference'; expected (Frontmatter|Backmatter|Chapter<digits>)/<safe-item>[/Derived<digits>] -/
#guard_msgs in
@[book_ref "not/a/reference" (role := primary)]
theorem malformedAttributeIsRejected : True := by trivial

/-- error: conflicting book_ref roles for 'conflictingRolesAreRejected' and 'Chapter9/Theorem9.2' -/
#guard_msgs in
@[book_ref "Chapter9/Theorem9.2" (role := primary),
  book_ref "Chapter9/Theorem9.2" (role := supporting)]
theorem conflictingRolesAreRejected : True := by trivial

def main : IO Unit :=
  IO.println "book_ref tests passed"
