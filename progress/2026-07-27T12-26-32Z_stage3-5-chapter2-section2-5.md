# Stage 3.5 Mathlib-quality polish — Chapter 2 §2.5

## Scope

This pass reviews exactly `Chapter2/Discussion_2.5_heading`,
`Chapter2/Discussion_2.5_well_defined`, `Chapter2/Problem2.5.1`, and
`Chapter2/Problem2.5.2` after their Stage 3.4 dependency audit. The first two catalog items share
`Discussion_2_5_well_defined.lean`; the two exercises have one Lean file each.

## Source polish

- Trimmed the discussion file to its direct quotient and two-sided-ideal imports. The exercise
  files retain `import Mathlib`: the global end-of-file `#min_imports` command suggested
  semantically unrelated modules that happened to provide transitive dependencies, and its
  documented syntax-and-tactic limitation makes that raw output unsuitable as a source import
  list.
- Removed the redundant `[simp]` attribute from `quotientAlgHom_mul`. The theorem remains the
  named book-facing multiplication formula, while `AlgHom.map_mul` already provides the generic
  simp rule; removing the duplicate also makes the declaration pass `simpNF`.
- Replaced the two non-terminal broad `simp` calls in
  `Problem2_5_2.linearIndependent_one_x_y` with the exact `simp only` sets suggested by `simp?`.
  This eliminates the three flexible-tactic warnings (one for `h1`, and one each for `e0` and
  `e1`) without changing the statement or weakening the proof.
- Reviewed declaration names, docstrings, theorem granularity, and the public quotient,
  cyclicity, coregular-module, and concrete-example APIs. The numbered namespaces retain the
  repository's source-aligned naming convention; no public declaration rename was justified.

All four items advance from `dependency_trimmed` to `proof_polished` with durable `stage3_5`
records.

## Lint and build evidence

Temporary commands were used during review and removed afterward:

- The global end-of-file `#min_imports` output was reviewed as a diagnostic rather than copied
  mechanically. Its useful direct suggestions informed the discussion-file trim; its unrelated
  transitive suggestions for the tactic-heavy exercise files were rejected.
- `#lint only checkUnivs defLemma deprecatedNoSince docBlame dupNamespace impossibleInstance
  nonClassInstance simpComm simpNF simpVarHead structureInType synTaut tacticDocs unusedArguments
  unusedHavesSuffices` passed with zero errors in all three scoped files (11, 1, and 65 checked
  declarations respectively). `defsWithUnderscore` was excluded because it mechanically flags
  every declaration beneath the source-aligned `Problem2_5_1` and `Problem2_5_2` namespaces,
  rather than an underscored declaration stem introduced by this section.
- `lake env lean -D linter.flexible=true` is warning-free for all three scoped files.
- `lake build EtingofRepresentationTheory.Chapter2` passes.
- `python3 scripts/validate_items.py` passes.
- `python3 scripts/validate_dependencies.py` passes.
- `git diff --check` passes.
