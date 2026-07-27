# Stage 3.5 — Chapter 2, §2.7

Completed the Mathlib-quality pass for the exact seven-item reading-order interval from
`Discussion_2.7_intro` through `Problem2.7.5`, including the previously easy-to-miss
`Discussion_faithful_example`.

## Scope and result

- Reviewed all 13 Lean provider modules attached to the seven catalog items.
- Changed 12 providers; `Definition2_7_3.lean` was already clean.
- Removed 29 unnecessary direct imports, replacing the one genuinely needed broad import with
  two focused Mathlib imports. A final per-file `#redundant_imports` pass reports no redundant
  import in any of the 13 modules.
- Updated obsolete library/tactic spellings, removed unused simplifier arguments and a no-op
  cast tactic, and made overloaded module/submodule arguments explicit where standalone
  elaboration otherwise timed out or failed.
- Documented narrow `defsWithUnderscore` exceptions caused solely by the stable book-number
  namespaces `Problem2_7_4` and `Problem2_7_5`. The public leaf names themselves follow Mathlib
  naming conventions. The parameter-indexed carrier `Fam q α β` also has a documented
  `unusedArguments` exception because its parameters intentionally select module instances.

## Verification

- Temporary per-file `#lint docBlameThm`: all 16 default declaration linters plus
  `docBlameThm` passed in every provider (17 linters total), covering 200 named and 288
  automatically generated declarations with zero findings.
- Temporary per-file `#redundant_imports`: no transitively redundant imports remain.
- Standalone `lake env lean` elaboration passed for every provider without warnings after the
  temporary diagnostic commands were removed.
- A clean worktree-local `lake build EtingofRepresentationTheory.Chapter2` completed all 8,744
  jobs successfully with no warning in any §2.7 provider; unrelated later-section warnings are
  outside this PR's one-section scope.
- Scoped scan found no `sorry`, `admit`, project `axiom`, or leftover lint/import diagnostic
  commands.
- `progress/items.json` parses successfully and exactly seven §2.7 entries have
  `status = proof_polished` with complete, verified `stage3_5` records.
- The item, internal-dependency, and external-dependency validators all pass; item coverage is
  5,721/5,721 source lines.

The temporary `#lint`, `#redundant_imports`, and `#import_bumps` commands used during review were
removed from the committed sources.
