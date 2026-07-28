# Stage 3.2 fidelity review — Chapter 2 §2.16

## Scope

Reading order gives exactly six §2.16 catalog items, from
`Chapter2/Discussion_2.16_heading` through `Chapter2/Problem2.16.5`. The preceding item is
`Chapter2/Problem2.15.1`; the next item is `Chapter3/Introduction`. Thus the audit stops before
Chapter 3.

The six items have sixteen direct providers: one each for Problems 2.16.1, 2.16.2, 2.16.4, and
2.16.5, plus the twelve-file `Problem2_16_3*` development. `Chapter2/Sl2Irrep.lean` is imported
separately by the chapter aggregate for Theorem 2.1.1 and is not a §2.16 provider; Problem 2.16.4
contains its own arbitrary-field construction.

## Claim audit

All six blobs and all sixteen providers were audited against the source in reading order. The
durable tracker has 32 claim units:

- 22 `formalized`;
- 2 `covered_elsewhere` by Mathlib's derived-series API;
- 3 `non_formalizable` organizational, heuristic, or proof-strategy units;
- 5 policy-controlled missing classification units.

The five last units preserve two different policy decisions. Three are the explicit unfinished
reprise for Problem 2.16.4 (parameter family, isomorphism criterion, and exhaustiveness), so they
are not a permanent scope exclusion. Two are the intentional project-wide omission of exhaustive
quantum classification in Problem 2.16.5, one for each root-of-unity case. The canonical verdict
bucket is `intentional_omission`, while each claim's reason records which of the two policies
applies. No placeholder, assumption, `Nonempty` shell, or weakened wrapper represents any of
these five units.

The qualifiers are explicit. Problem 2.16.1 fixes the field literally to `ℂ`. Problem 2.16.2 uses
the standing algebraically closed convention and a prime characteristic `p`. In Problem 2.16.3,
the `g₃` dimension theorem assumes `2 ≠ 0`, `g₄` is proved infinite-dimensional over every field,
and the explicit `LoopIdx` basis is the characteristic-zero result. Problem 2.16.4 assumes an
algebraically closed field of prime characteristic `p > 2`. Problem 2.16.5 specializes the
source's allowed algebraically closed characteristic-zero field to `ℂ`; its non-root branch uses
`¬ IsOfFinOrder q`, and its root branch states the source exclusion `q ≠ ±1` as `q² ≠ 1`.

## Repairs

Stage 3.2 made three scoped repairs:

1. The stale header of `Problem2_16_3.lean` no longer says that its now-proved results are
   statement-only or deferred; it points to the companion files containing the explicit basis.
2. `Problem2_16_5.lean` no longer claims that the necessary highest-weight eigenvalue constraint
   determines an irreducible up to isomorphism. Its prose now agrees with the actual theorem and
   the documented classification omission.
3. The quantum presentation now has the surjective augmentation
   `augmentation : Uqsl2 q →ₐ[ℂ] ℂ`, sending `e,f` to zero and `K,L` to one. Consequently
   `Uqsl2 q` has a proved `Nontrivial` instance, closing the presentation's formal nonvacuity gap.

The stale regression wording for Problem 2.16.4 was also corrected: #7531 already restored fresh
elaboration of the existing partial endpoints. The reprise decision itself is unchanged.

## Integrity and nonvacuity

- Problem 2.16.1 uses genuine `IsSimpleOrder (LieSubmodule ℂ L V)` irreducibility; its
  `Nontrivial V` assumption is redundant, not restrictive.
- Problem 2.16.2 constructs both classified families, proves their irreducibility, constructs the
  equivalences inside every `Nonempty`, proves the exact isomorphism criterion, and proves
  exhaustiveness. `Nonempty` only propositionalizes the type of isomorphisms.
- Problem 2.16.3 is the quotient of the free Lie algebra by the two displayed relators. Its
  dimensions have independent matrix lower bounds, and `gFourBasis` is a genuine
  `Module.Basis`, not a spanning-family wrapper.
- Problem 2.16.4 constructs the standard modules and proves their irreducibility. The sharpness
  theorem uses the actual `p`-dimensional module; it does not assume existence.
- Problem 2.16.5 uses genuine `IsSimpleModule` hypotheses, and the new augmentation proves that
  the algebra presentation itself has not collapsed.

## Validation

- `.lake/build` is worktree-local; only `.lake/packages` shares the package cache;
- all 16 scoped providers built together successfully from the fresh local build (8595 jobs);
- `lake build EtingofRepresentationTheory.Chapter2`: success;
- the scoped declaration scan found no `sorry`, `admit`, `axiom`, `opaque`, `native_decide`, or
  `proof_wanted` declaration;
- `#print axioms` on sixteen principal endpoints reported only `propext`, `Classical.choice`, and
  `Quot.sound`, never `sorryAx`;
- `jq empty progress/items.json` and the exact six-item/32-claim aggregation passed;
- `python3 scripts/validate_items.py`: passed with 5721/5721-line coverage and its 593
  pre-existing extra-field warnings;
- `python3 scripts/validate_dependencies.py`: passed with its one pre-existing conservative-default
  warning;
- `python3 scripts/validate_external_deps.py` and
  `python3 scripts/validate_mathlib_coverage.py`: passed;
- normalized non-scope tracker projections match `origin/main` byte-for-byte, dependency metadata
  is unchanged, and `git diff --check` passes.
