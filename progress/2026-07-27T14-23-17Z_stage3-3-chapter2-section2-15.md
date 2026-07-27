# Stage 3.3 proof verification — Chapter 2 §2.15

## Scope and result

This pass is stacked directly on the Stage 3.2 §2.15 commit and preserves its exact two-item
reading-order scope: `Discussion_2.15_heading` and `Problem2.15.1`, stopping before §2.16.
The heading is organizational prose and has no proof obligation. The problem uses all twelve
attached providers:

1. `Sl2Irrep.lean`
2. `Theorem2_1_1.lean`
3. `Problem2_15_1_a_e.lean`
4. `Problem2_15_1_complete_reducibility.lean`
5. `Problem2_15_1_l.lean`
6. `Sl2NullitySequence.lean`
7. `Sl2SemisimpleDecomposition.lean`
8. `Sl2JordanTypeIso.lean`
9. `Problem2_15_1_l_uniqueness.lean`
10. `Problem2_15_1_m.lean`
11. `Problem2_15_1_m_Module.lean`
12. `Problem2_15_1_n.lean`

No proof repair was required. Every formalized claim and its supporting implementation is
proof-complete. The Stage 3.2 fidelity decisions remain unchanged: the source-specific
minimal-counterexample scaffolding in parts (i)–(k) and the analytic `Tr(exp(xH))` route in
part (m) are intentional proof-route omissions. Their intended mathematical endpoints are
proved by stronger complete-reducibility, semisimple-decomposition, algebraic-character, and
explicit-intertwiner results; no placeholder or unproved declaration stands in for an omission.

## Declaration and internal-proof audit

The twelve modules were imported into a dedicated Lean audit command. Module indices were used
to enumerate the complete compiled surface rather than relying on a hand-selected theorem list.
The audit found:

- **268 exported constants**, including named declarations, public instances, and generated
  equation/congruence declarations;
- **710 total module-attributed constants** after including private helpers and other generated
  implementation declarations.

For every exported constant, the audit computed the same transitive axiom set reported by
`#print axioms`. It also computed and checked the axiom set of every internal constant. Every
set was a subset of Lean's accepted foundations `propext`, `Classical.choice`, and `Quot.sound`;
many declarations used fewer or no axioms. There was no `sorryAx` and no project-defined axiom.

A source scan over all twelve files found no token `sorry`, `admit`, `proof_wanted`, or `axiom`.
Fresh direct elaboration of every provider exercised all internal proofs and emitted no
declaration-with-sorry or metavariable diagnostic.

## Validation

- isolated combined build of all twelve providers: 3,221 jobs, success;
- standalone `lake env lean` elaboration of all twelve provider files: success;
- complete exported/internal transitive-axiom audit: 268/710 declarations, success;
- exact two-item Stage 3.3 tracker check and JSON parsing;
- repository item, internal-dependency, external-dependency, and Mathlib-coverage validators;
- scoped lint ratchet and admission/project-axiom scans;
- full Chapter 2 build;
- stacked-diff invariance and `git diff --check`.

The legacy `verify_blobs.py` utility remains incompatible with the ten existing top-level
derived overlay records because those records intentionally use `derived_from` instead of `id`.
It exits with `KeyError: id` before verification; this is unchanged repository-wide validator
debt, not a §2.15 regression.
