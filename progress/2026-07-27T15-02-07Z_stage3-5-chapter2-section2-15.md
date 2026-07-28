# Stage 3.5 — Chapter 2, §2.15

Completed the Mathlib-quality pass for the exact two-item interval consisting of the §2.15
heading and Problem 2.15.1, stacked on the Stage 3.4 dependency audit in PR #8059. The exercise
is implemented across twelve complete provider modules.

## Declaration and documentation audit

- Temporary per-file `#lint+ docBlameThm` ran all 16 default declaration linters plus
  `docBlameThm`: zero findings across 234 named and 475 automatically generated declarations.
- Added 43 missing theorem and instance docstrings across the highest-weight, Casimir,
  Jordan-block, Clebsch–Gordan, nullity, and semisimple-decomposition APIs.
- Removed the unused `LieModule` argument from `Indecomposable` and three unused family-level
  `LieModule` arguments from the product reindexing API.
- Removed an unused irreducibility argument from the private primitive-vector existence helper.
- Removed the redundant simp attribute from `blockForward_mk`, whose left side was not in simp
  normal form and whose uses are explicit rewrites.
- Kept the established `sl2_e`, `sl2_f`, `sl2_h`, `e_basis`, and `sl2_casimir` API names under
  documented, declaration-local naming exceptions. Renaming them would break the adjacent §2.16
  provider as well as the scoped provider graph.

## Proof and source-quality cleanup

The cold scoped baseline had 68 warnings. The polished providers have zero warnings. The cleanup
replaced deprecated `push_neg`, goal-changing `show`, flexible `simp`, unused simp arguments, an
unused tactic, automatically included but unused section variables, and a multi-goal tactic hazard
with focused, explicit equivalents. Two overlong lines and an empty line inside a command were
also repaired. Every scoped line is at most 100 characters.

Manual review found no remaining unstable suggestion tactic, admission, project axiom, opaque
declaration, `native_decide`, diagnostic command, or linter-disable option. The `RepOf` carrier's
representation index remains under a documented unused-argument exception because it
intentionally distinguishes the module structures placed on the same underlying vector space.

## Imports and axioms

Temporary `#redundant_imports` checks report no transitively redundant import in any provider.
An environment audit identified all 268 exported declarations attributable to the twelve modules;
`#print axioms` was run on every one. The only dependencies reported were `propext`,
`Classical.choice`, and `Quot.sound`; no declaration depends on `sorryAx` or another nonstandard
axiom.

## Durable status and validation

Both exact items now have `status = proof_polished` and complete Stage 3.5 metadata. The heading's
quality status is correctly `not_applicable`; Problem 2.15.1 is `verified`. Earlier stage metadata
and both dependency maps remain unchanged.

- direct elaboration and a scoped build of all twelve providers, with zero output/warnings
- full `lake build EtingofRepresentationTheory.Chapter2`
- `scripts/validate_items.py`
- `scripts/validate_dependencies.py`
- `scripts/validate_external_deps.py`
- `scripts/validate_mathlib_coverage.py`
- exact two-item scope and non-scope tracker invariance checks
- admission, diagnostic, deprecated-tactic, and 100-character scans
- `jq empty` on repository JSON and `git diff --check`

`scripts/verify_blobs.py` retains the repository's known derived-overlay `KeyError: 'id'`; this
pass does not alter blobs or those unrelated records. All temporary diagnostic sources and
commands were removed.
