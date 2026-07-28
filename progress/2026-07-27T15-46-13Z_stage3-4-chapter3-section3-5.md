# Stage 3.4 dependency trimming — Chapter 3 §3.5

**Date:** 2026-07-27
**Scope:** `Chapter3/Introduction_to_3.5` through `Chapter3/Proposition3.5.8`
**Stacked base:** Stage 3.3 PR #8073, commit `0df4dd87146bb729be6946bc42479888be740133`
**Result:** complete — nine items moved to `dependency_trimmed`, with five actual item-level edges and 18 individually required direct imports.

## Exact scope

This pass changes only the nine contiguous `progress/items.json` entries 147–155, their
nine keys in `dependencies/internal.json`, five scoped provider import blocks, and this
audit note. The strict predecessor `Chapter3/Lemma3.4.2`, strict successor
`Chapter3/Introduction_to_3.6`, Stage 3.2 claim coverage, Stage 3.3 proof-integrity
metadata, external dependencies, and all proof bodies remain unchanged.

## Actual internal dependencies

The conservative graph assigned each scoped item one incoming reading-order edge: nine
edges total. Reviewing the surviving project imports and the referenced project
declarations gives the following direct item graph:

| Item | Actual internal dependencies |
|---|---|
| `Chapter3/Introduction_to_3.5` | none |
| `Chapter3/Definition3.5.1` | none |
| `Chapter3/Proposition3.5.2` | none |
| `Chapter3/Proposition3.5.3` | none |
| `Chapter3/Theorem3.5.4` | `Chapter3/Definition3.5.1`; `Chapter3/Theorem3.2.2` |
| `Chapter3/Corollary3.5.5` | `Chapter3/Theorem3.2.2` |
| `Chapter3/Example3.5.6` | none |
| `Chapter3/Definition3.5.7` | none |
| `Chapter3/Proposition3.5.8` | `Chapter2/Definition2.3.8`; `Chapter3/Theorem3.5.4` |

This replaces nine reading-order edges with five declaration-backed edges, a net
reduction of four repository edges (582 to 578). The important nonlocal structure is:

- Theorem 3.5.4 uses `Etingof.Radical` from Definition 3.5.1 and
  `Etingof.density_theorem_part2` from Theorem 3.2.2. Its three providers also import
  one another within the same catalog item; those sibling-provider imports are not
  item-level dependency edges.
- Corollary 3.5.5 proves its bound directly from the density theorem, not from Theorem
  3.5.4.
- Proposition 3.5.8 uses `Etingof.structure_mod_radical` from Theorem 3.5.4 and
  `Etingof.IsIndecomposable` from Chapter 2 Definition 2.3.8. Its implementation does
  not import Definition 3.5.7; it uses Mathlib's `IsSemisimpleRing` directly.

Each `stage3_4.actual_internal_dependencies` array in `progress/items.json` was compared
against the corresponding `dependencies/internal.json` value and matches exactly.

## Direct-import audit and changes

All 53 direct-import entries across the ten Stage 3.3 provider modules were audited.
First, the 32 transitively redundant imports documented by Stage 3.3 were removed.
Every surviving import was then deletion-tested by re-elaborating the complete provider
source with that one import omitted. This exposed three additional unused imports:

- `Theorem3_5_4`: `EtingofRepresentationTheory.Chapter3.Proposition3_5_3`;
- `Corollary3_5_5`: `Mathlib.RingTheory.Jacobson.Ideal`;
- `Example3_5_6`: `Mathlib.RingTheory.LocalRing.MaximalIdeal.Basic`.

The final import counts are:

| Provider | Before | After | Removed |
|---|---:|---:|---:|
| `Definition3_5_1` | 1 | 1 | 0 |
| `Proposition3_5_2` | 1 | 1 | 0 |
| `Proposition3_5_3` | 3 | 3 | 0 |
| `Theorem3_5_4` | 11 | 2 | 9 |
| `Theorem3_5_4_Finiteness` | 6 | 1 | 5 |
| `Theorem3_5_4_CompleteFamily` | 2 | 2 | 0 |
| `Corollary3_5_5` | 8 | 1 | 7 |
| `Example3_5_6` | 11 | 3 | 8 |
| `Definition3_5_7` | 1 | 1 | 0 |
| `Proposition3_5_8` | 9 | 3 | 6 |
| **Total** | **53** | **18** | **35** |

All 18 remaining imports fail the single-import deletion test, so each is required by
its provider in the final import set. Re-elaborating all ten final sources with
`#redundant_imports` reports `No transitively redundant imports found.` for every
provider.

## Validation

- Scoped ten-provider build: passed, 1,977 jobs.
- Full `EtingofRepresentationTheory.Chapter3` build: passed, 8,692 jobs.
- `scripts/validate_items.py`: passed (existing schema warnings only).
- `scripts/validate_dependencies.py`: passed (583 entries, 578 edges; expected
  conservative-default warning only).
- `scripts/validate_external_deps.py`: passed (58 external dependencies).
- `scripts/validate_mathlib_coverage.py`: passed (58/58 entries).
- Import-only source invariant: the five Lean diffs contain exactly 35 removed `import`
  lines and no proof, declaration, documentation, or option changes.
- Item-state invariant: after restoring the nine prior `status` values and deleting only
  their new `stage3_4` objects, `progress/items.json` is JSON-equivalent to the stacked
  Stage 3.3 base.
- Dependency-scope invariant: only the nine scoped keys differ in
  `dependencies/internal.json`; external dependency and Mathlib coverage files are
  unchanged.

The builds reproduce the existing linter and deprecation warnings recorded in Stage 3.3;
none is caused by import trimming.

## Handoff

Chapter 3 §3.5 has completed Stage 3.4 and is now eligible for Stage 3.5, the designated
Mathlib-quality proof-polishing pass.
