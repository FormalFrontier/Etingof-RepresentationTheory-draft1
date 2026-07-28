# Stage 3.5 — Chapter 3, §3.1

Completed the Mathlib-quality pass for the exact ten-item reading-order interval from
`Chapter3/Introduction` through `Chapter3/Discussion_after_Lemma3.1.6`. This work is stacked
exactly on the completed Stage 3.4 dependency audit in draft PR #8062 at commit `7ffa0206`.
The scope has seven complete Lean providers, 60 public declarations, and three private proof
helpers. The immediate predecessor remains `Chapter2/Problem2.16.5`; the strict successor remains
`Chapter3/Introduction_to_3.2`.

## Source-quality result

- Added documentation to all 11 declarations reported by `docBlameThm`: four evaluation and
  equivalence facts in Example 3.1.2, three evaluation simp lemmas in Remark 3.1.3, two matrix
  simp lemmas in Remark 3.1.5, and two post-composition simp lemmas in the alternative proof.
- Replaced both deprecated `push_neg` calls in Proposition 3.1.4 with `push Not`.
- Removed automatically included assumptions that do not belong in theorem signatures. This
  includes unnecessary `DecidableEq`, algebraic-closedness, scalar-tower, finite-dimensionality,
  semisimplicity, and related ambient section assumptions, according to each declaration's actual
  proof and statement requirements.
- Retained 13 `Fintype` hypotheses that are mathematically essential to finite products, finite
  direct sums, or block-matrix arguments even though they do not occur syntactically in the
  proposition returned. Each exception is scoped to one declaration and has an adjacent comment
  explaining the reason.
- Renamed the proof-implicit surjectivity hypothesis of `surjective_map_splits` to `_hf`. The
  stable book-facing signature is retained, while the name now accurately records that the
  complement-of-kernel conclusion follows from source semisimplicity alone.

## Lint, import, style, and axiom audit

- Temporary per-provider `#lint+ docBlameThm` checks ran all 16 default declaration linters plus
  `docBlameThm`. They found zero errors across 60 public and 67 automatically generated
  declarations. The three private Proposition 3.1.4 helpers were also reviewed directly and are
  covered transitively by the public callers.
- Temporary per-provider `#redundant_imports` checks found no transitively redundant import in any
  of the seven headers; Stage 3.4's 12 focused direct imports remain unchanged.
- After removing the temporary diagnostic commands, the isolated seven-provider build succeeded
  in all 1,977 jobs with no output warnings from a scoped provider.
- Removed the five newly clean providers from `scripts/lint-warning-baseline.txt`, preserving the
  CI warning ratchet. Definition 3.1.1 and Example 3.1.2 were not baseline entries.
- `#print axioms` audited all 60 public declarations. None depends on `sorryAx`; the only reported
  dependencies are `propext`, `Classical.choice`, and `Quot.sound`.
- Scoped scans found no `sorry`, `admit`, project `axiom`, `opaque`, `proof_wanted`,
  `native_decide`, deprecated `push_neg`, leftover diagnostic command, or line over 100 characters.

## Durable completion and validation

- All ten exact records now have `status = proof_polished` and complete section `3.1` Stage 3.5
  metadata. The seven proof-bearing records have `mathlib_quality = verified`; the three
  provider-free organizational records correctly use `not_applicable`.
- Stage 3.2, Stage 3.3, Stage 3.4, internal-dependency, and external-dependency metadata are
  unchanged. The non-§3.1 tracker projection and all dependency files are byte-for-byte unchanged
  from PR #8062. The seven scoped internal edges and their no-forward-edge property are preserved.
- `lake build EtingofRepresentationTheory.Chapter3`: passed all 8,693 jobs. Reported warnings are
  pre-existing and outside the seven scoped providers.
- `python3 scripts/validate_items.py`: passed with 5,721/5,721 source-line coverage and the
  pre-existing extra-field warnings.
- `python3 scripts/validate_dependencies.py`: passed with 583 entries and 579 total edges, plus the
  one pre-existing conservative-default warning.
- `python3 scripts/validate_external_deps.py`: passed with 58 external dependencies.
- `python3 scripts/validate_mathlib_coverage.py`: passed with all 58 external dependencies covered.
- Exact scope adjacency, scoped prior-stage invariance, non-scoped tracker invariance, dependency
  invariance, warning-baseline consistency, JSON parsing, source scans, 100-character checks, and
  `git diff --check` all passed.

The temporary lint, redundant-import, and axiom-audit commands were removed from committed source.
