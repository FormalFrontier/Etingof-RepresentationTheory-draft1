# Stage 3.3 proof verification — Chapter 2 §2.16

## Scope and result

This pass keeps the exact six-item, sixteen-provider §2.16 scope established at Stage 3.2. The
section heading has no proof obligation. The five classification gaps also remain exactly as
recorded there: three unfinished Problem 2.16.4 reprise units (parameter family, isomorphism
criterion, and exhaustiveness) and the two permanent project-wide Problem 2.16.5 exhaustive
classification omissions (non-root and root-of-unity cases). Stage 3.3 does not represent any of
these gaps by a theorem, axiom, wrapper, or strengthened status.

No Lean proof repair was required. The audit did repair one stale tracker reference:
`coe_derivedSeries_one_eq` is correctly namespaced as
`LieAlgebra.coe_derivedSeries_one_eq`, not `LieIdeal.coe_derivedSeries_one_eq`.

## Exhaustive environment audit

A scratch module imported all sixteen direct providers and selected constants by Lean's recorded
module attribution. This inventories generated and private proof constants that a text-only list
of top-level commands would miss. It found 1,589 attributed constants:

- 1,467 are non-private constants (1,369 non-reserved public names and 98 reserved generated
  names), and 122 are private;
- 1,322 are proof constants (1,125 non-reserved public, 98 reserved generated, and 99 private);
- the remaining constants are 238 definitions, 15 constructors, 7 inductives, and 7 recursors;
- there are no scoped `axiom` or `opaque` declarations.

The item/provider totals are: Problem 2.16.1, 1 constant / 1 proof constant; Problem 2.16.2,
211 / 168; the twelve-file Problem 2.16.3 development, 1,108 / 925; Problem 2.16.4, 119 / 109;
and Problem 2.16.5, 150 / 119.

Every attributed constant was passed to `Lean.collectAxioms`, the engine used by
`#print axioms`. The audit fails on a direct project axiom or on any dependency outside
`propext`, `Classical.choice`, and `Quot.sound`; it passed. Separate literal `#print axioms`
commands checked the five externally supplied declarations used by the tracker:
`LieAlgebra.derivedSeries`, `LieAlgebra.coe_derivedSeries_one_eq`,
`LieAlgebra.IsSolvable`, `LieAlgebra.isSolvable_iff`, and `IsOfFinOrder`. They likewise use only
the accepted foundational axioms (or none). Thus no scoped public endpoint or module-attributed
proof constant contains `sorryAx` or a project axiom.

The source-level scan also found no `sorry`, `admit`, `proof_wanted`, `sorryAx`,
`native_decide`, project `axiom`, or `opaque` declaration in any of the sixteen providers.

## Validation

- fresh worktree-local build of all sixteen providers: success (8,595 jobs);
- full `EtingofRepresentationTheory.Chapter2` build: success;
- exhaustive attributed-constant audit and external `#print axioms` checks: success;
- exact six-item Stage 3.3 tracker audit, five-omission invariance check, and JSON parse: success;
- `scripts/validate_items.py`, `scripts/validate_dependencies.py`,
  `scripts/validate_external_deps.py`, and `scripts/validate_mathlib_coverage.py`: success;
- normalized non-scope tracker projection and all non-tracker source providers are unchanged from
  the Stage 3.2 base;
- dependency metadata is unchanged, only `.lake/packages` is shared, and `git diff --check`
  passes.

This PR is limited to Section 2.16 and Stage 3.3.
