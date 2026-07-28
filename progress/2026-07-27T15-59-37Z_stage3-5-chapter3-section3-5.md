# Stage 3.5 — Chapter 3, §3.5

Completed the Mathlib-quality pass for the exact nine-item reading-order interval from
`Chapter3/Introduction_to_3.5` through `Chapter3/Proposition3.5.8`. This work is stacked
exactly on the completed Stage 3.4 dependency audit in draft PR #8077 at commit `d75412a4`.
The scope has ten complete Lean providers and 153 environment-owned declarations. Its immediate
predecessor is `Chapter3/Lemma3.4.2`; its strict successor is `Chapter3/Introduction_to_3.6`.

## Source-quality result

- Removed the unused completeness hypothesis from `Etingof.sum_dim_sq_le_dim`. The proof through
  the density theorem establishes the stronger bound for every finite pairwise-nonisomorphic
  family, which still directly implies the book's complete-family corollary.
- Added nine missing theorem docstrings in Example 3.5.6: three truncated-polynomial residue
  facts, the two-sided ideal instance, two diagonal-character facts, the nontriviality instance,
  and two diagonal-idempotent facts.
- Replaced all five deprecated `push_neg` calls with `push Not`, all ten goal-changing `show`
  tactic invocations with `change`, two flexible matrix simplifications with explicit rewrites,
  and one unnecessary `simpa` with the exact proof term.
- Removed the `simp` attribute from `diagonalHom_diagIdem`: its left side already reduces via the
  more primitive `diagonalHom_apply` and `diagIdem_val` simp lemmas.
- Retained one narrow `unusedArguments` exception on `UpperTriangularSimple`. Its carrier is the
  constant type `k`, while the intentionally retained index selects a different diagonal-action
  module instance and is essential to the representation family.

## Lint, import, warning, and axiom audit

- Temporary per-provider `#lint+ docBlameThm` checks ran all 16 default declaration linters plus
  `docBlameThm`. They found zero errors across 61 lint-visible and 67 automatically generated
  declarations in all ten providers.
- Temporary per-provider `#redundant_imports` checks found no transitively redundant import. All
  18 Stage 3.4 direct-import entries, naming 14 unique modules, remain unchanged.
- After removing the temporary diagnostics, standalone `lake env lean` elaboration of all ten
  provider sources succeeded with completely empty output. The scoped 1,977-job build reports
  only the pre-existing `Theorem3_2_2` warning from outside the exact provider set.
- Removed `Corollary3_5_5.lean`, `Example3_5_6.lean`, and `Theorem3_5_4.lean` from
  `scripts/lint-warning-baseline.txt`; all three are now warning-free.
- An environment-origin `Lean.collectAxioms` audit rechecked every one of the 153 declarations,
  including all private and generated constants. The distribution remains 26 with no axioms,
  eight with `propext`, 39 with `propext` and `Quot.sound`, and 80 with `propext`,
  `Classical.choice`, and `Quot.sound`. There are zero unexpected axioms and no `sorryAx`.
- Scoped scans found no `sorry`, `admit`, project `axiom`, `opaque`, `proof_wanted`,
  `native_decide`, deprecated `push_neg`, leftover diagnostic command, or line over 100
  characters.

## Durable completion and validation

- All nine exact records now have `status = proof_polished` and complete section `3.5` Stage 3.5
  metadata. The eight mathematical records have `mathlib_quality = verified`; the provider-free
  organizational heading correctly uses `not_applicable`.
- Stage 3.2, Stage 3.3, Stage 3.4, internal-dependency, and external-dependency metadata are
  unchanged. The non-§3.5 tracker projection and both dependency files remain unchanged from
  PR #8077; all five scoped internal edges and the no-forward-edge property are preserved.
- `lake build` of the ten providers passed all 1,977 jobs.
- `lake build EtingofRepresentationTheory.Chapter3` passed all 8,692 jobs. Reported warnings are
  pre-existing and outside the ten scoped providers.
- `python3 scripts/validate_items.py` passed with 5,721/5,721 source-line coverage and the
  pre-existing extra-field warnings.
- `python3 scripts/validate_dependencies.py` passed with 583 entries and 578 edges, plus the
  expected conservative-default warning.
- `python3 scripts/validate_external_deps.py` passed with 58 external dependencies.
- `python3 scripts/validate_mathlib_coverage.py` passed with all 58 entries covered.
- Exact scope adjacency, scoped prior-stage invariance, non-scoped tracker invariance, dependency
  invariance, warning-baseline consistency, JSON parsing, source scans, 100-character checks, and
  `git diff --check` all passed.

The temporary lint, redundant-import, and axiom-audit commands were removed from committed source.
