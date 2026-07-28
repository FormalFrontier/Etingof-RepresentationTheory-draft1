# Stage 3.3 proof verification — Chapter 2 §2.13

## Scope and result

This pass keeps the exact two-item, ten-claim §2.13 scope established at Stage 3.2.
The section heading has no proof obligation. The only public mathematical endpoint in the chosen
project scope, `Etingof.Problem2_13_1.irrational_arccos_third_div_pi`, is fully proved and depends
only on Lean's accepted foundational axioms `propext`, `Classical.choice`, and `Quot.sound`.

The proof follows the book's arithmetic strategy through an equivalent Chebyshev recurrence:
`b_k = 3^k cos(kθ)` for `θ = arccos(1/3)`, while `3 ∤ b_k`; rationality would force a positive
index at which `b_k` equals a positive power of three. There are no `sorry`, `admit`, project
`axiom`, `proof_wanted`, or `sorryAx` dependencies in this formalized endpoint.

The five Dehn-invariant/scissors-congruence units remain explicit intentional omissions under
`skipped-exercises.md`. Stage 3.3 does not mislabel those omissions as proved declarations.

## Validation

- isolated targeted provider build
- full Chapter 2 build
- scoped source admission scan
- `#print axioms Etingof.Problem2_13_1.irrational_arccos_third_div_pi`
- exact tracker scope/status checks, `jq empty`, and `git diff --check`
