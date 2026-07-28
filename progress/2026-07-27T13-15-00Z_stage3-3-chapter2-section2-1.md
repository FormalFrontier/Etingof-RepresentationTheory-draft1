# Stage 3.3 proof verification — Chapter 2 §2.1

## Scope

This pass covers exactly the seven reading-order items from `Chapter2/Introduction` through
`Chapter2/Discussion_after_Theorem2.1.2`, comprising 41 audited claims. It verifies the statements
and definitions accepted at Stage 3.2 and does not alter the section boundary.

## Completed proof work

- The U(sl(2))/Lie-action preservation bridges, the irreducible classification, complete
  reducibility, and indecomposable corollary are all sorry-free.
- `Theorem_2_1_1_i_polynomial_model` is now proved. The proof constructs the basis equivalence
  `e_i ↦ x^(d-1-i)y^i` between `Fin d → ℂ` and the degree-`d-1` homogeneous submodule, then checks
  the `h`, `e`, and `f` actions against `x∂x-y∂y`, `x∂y`, and `y∂x` on that basis.
- The Dynkin-to-finite-representation-type half of Gabriel's theorem was generalized from
  algebraically closed fields to arbitrary fields. The Chapter 6 positive-root existence and
  uniqueness theorem already has this generality; the previous restriction was unnecessary.

## Remaining Stage 3.3 obligation

`Theorem_2_1_2_general_arbitrary_field` is proved only in the Dynkin-to-finite-type direction.
Its converse remains `proof_wanted`: over a finite field, the existing scalar-parameter families
and orbit-density argument do not establish that loops, parallel/opposite arrows, or a non-Dynkin
underlying graph have infinite representation type. Completing this requires either a
field-independent base-change/descent theorem for representation type or explicit unbounded
families of indecomposable representations. The tracker records this boundary as partial and does
not certify §2.1 Stage 3.3 complete.

## Validation

- direct Lean check of `Theorem2_1_1.lean`
- isolated `lake build EtingofRepresentationTheory.Chapter2.Theorem2_1_2`
- isolated build/check of `Theorem2_1_2_General.lean`
- scoped admission scan and `jq empty progress/items.json`
- `git diff --check`
