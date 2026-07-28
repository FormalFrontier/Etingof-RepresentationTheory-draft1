# Stage 3.3 proof-integrity review — Chapter 3 §3.1

## Scope and inherited result

This stacked review is based exactly on Stage 3.2 draft PR #8054 at commit `884a7b70`.
Reading order gives ten §3.1 catalog items, from `Chapter3/Introduction` through
`Chapter3/Discussion_after_Lemma3.1.6`, and seven Lean provider files. The immediate predecessor
is `Chapter2/Problem2.16.5`; the strict successor is `Chapter3/Introduction_to_3.2`.

Stage 3.2 supplies 28 exhaustive claim units: 19 `formalized`, 6 `covered_elsewhere`, and 3
`non_formalizable`. The nonformalizable units are the chapter/section convention, an organizational
transition, and a bibliographic attribution. They are preserved honestly as prose without Lean
proof obligations. All 25 mathematical units are covered by the declarations certified here.

## Proof-integrity result

Eight items are `sorry_free`; the chapter/section introduction and the organizational transition
are `not_applicable`. The eight proof-applicable records cite 66 declaration references, comprising
60 unique public declarations across the seven providers. Proposition 3.1.4 additionally uses three
private helper proofs; they were inspected directly and are transitively covered by the audited public
callers.

Every public declaration was resolved by Lean. The 60-declaration `#print axioms` audit reported
only `propext`, `Classical.choice`, and `Quot.sound`; it reported no `sorryAx`, project axiom, or
undeclared dependency. A direct provider scan found no `sorry`, `admit`, `proof_wanted`, `axiom`,
`sorryAx`, `opaque`, or `native_decide` occurrence. No Lean repair was needed: Stage 3.2 had already
left all scoped implementations admission-free.

The final discussion has no dedicated provider. Its four Stage 3.2 claims are certified as
`covered_elsewhere` by the audited declarations from Lemma 3.1.6, the alternative-proof provider,
Remark 3.1.5, and Proposition 3.1.4. The B. Poonen attribution in the alternative-proof discussion
remains bibliographic prose and is not represented as a proved theorem.

## Durable tracker result

- all 10 exact items have complete section `3.1` `stage3_3` objects;
- proof-integrity split: 8 `sorry_free`, 2 `not_applicable`;
- declaration references: 66, comprising 60 unique public declarations;
- internal proof inventory: 3 private helpers, all inspected and transitively audited;
- Stage 3.2 data is unchanged: removing the new `stage3_3` objects reproduces the PR #8054
  scoped records exactly;
- the non-§3.1 tracker projection and dependency metadata are unchanged.

## Validation

- all 7 scoped providers built successfully in isolation (1977 jobs; pre-existing linter warnings
  only);
- `lake build EtingofRepresentationTheory.Chapter3`: success (8693 jobs; pre-existing linter
  warnings only);
- Lean declaration-resolution and 60-declaration `#print axioms` audit: success, with foundational
  axioms only and no `sorryAx` or project axiom;
- exact scoped admission/placeholder scan: clean;
- exact 10-item Stage 3.3 completeness, proof-integrity split, and 60-unique-declaration aggregation:
  passed;
- `jq empty progress/items.json`: passed;
- `python3 scripts/validate_items.py`: passed with 5721/5721-line coverage (593 pre-existing schema
  warnings);
- `python3 scripts/validate_dependencies.py`: passed (one pre-existing conservative-default
  warning);
- `python3 scripts/validate_external_deps.py`: passed;
- `python3 scripts/validate_mathlib_coverage.py`: passed;
- normalized scoped and non-scoped tracker invariance checks and `git diff --check`: passed.
