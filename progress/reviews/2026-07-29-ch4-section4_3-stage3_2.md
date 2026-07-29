# Stage 3.2 review — Chapter 4, §4.3

## Scope and result

This review covers the six contiguous catalog records from `Chapter4/Introduction_4.3` through
`Chapter4/Example4.3_S4`, including Exercise 4.3.1. Every source blob and the existing detailed
fidelity re-audit were checked against the current providers. All mathematical endpoints are
covered. The `covered_partial` status on the S₄ example is stale: its cited follow-up issue #5429
is closed, all five representations are genuine `FDRep` objects, and the earlier repository-wide
re-audit already adjudicated the alternative realization of the two-dimensional representation as
faithful.

The section heading only says that the following examples concern complex representations of
finite groups; it is organizational prose and has no independent proof obligation.

## Finite abelian groups

`Etingof.Example4_3_FiniteAbelianGroups` proves that every irreducible representation of a finite
abelian group over an algebraically closed field is one-dimensional. `Etingof.CharacterGroup`
models the dual group as multiplicative complex characters, with the pointwise group operations.
Product duality is supplied by `characterGroupProdEquiv` and `characterGroupPiEquiv`.
`nonempty_mulEquiv_characterGroup` proves the noncanonical finite-abelian duality `G ≅ Gˇ`, while
`characterDoubleDualEquiv` and `characterDoubleDualEquiv_apply_apply` give the canonical evaluation
isomorphism `G ≅ (Gˇ)ˇ`, with `φ(g)(χ) = χ(g)`. The cyclic root-of-unity description and the
general product result are provided through Mathlib's finite Pontryagin-duality construction rather
than by fixing a particular decomposition into cyclic factors; this matches the source endpoints
and preserves the stated noncanonicity distinction.

## The symmetric group S₃

The provider constructs the trivial, sign, and standard sum-zero representations as actual
`FDRep ℂ S₃` objects. It proves the three conjugacy classes, dimensions `1,1,2`, simplicity of
all three from their computed trace characters, pairwise non-isomorphism, exhaustiveness, and the
sum-of-squares identity. `Discussion5_11_examples.S3_simple_iso` supplies the exhaustive
classification endpoint. The geometric plane model and displayed matrices are an intentional
choice-of-basis presentation omitted in favor of the canonically equivalent deleted permutation
representation; the irreducible two-dimensional representation itself is fully formalized.

## The quaternion group Q₈ and Exercise 4.3.1

The Q₈ provider proves the five conjugacy classes, center `{ ±1 }`, four one-dimensional
characters, and the genuine two-dimensional Pauli-matrix representation, including the displayed
actions of `i`, `j`, `k`, and `-1`. All five are simple, pairwise non-isomorphic and exhaustive,
with dimensions `1,1,1,1,2` and sum of squares eight.

Exercise 4.3.1 is covered by the detailed final exercise audit. The book's literal combination of
right covariance and right translation has a sign error and is not invariant. The provider makes
the mathematically necessary correction to left covariance, then proves invariance under right
translation, constructs an equivalence with `Fin 2 → ℂ`, proves finrank two, and proves genuine
irreducibility. This is the intended induced representation and the unique two-dimensional Q₈
irreducible, not a weakened substitute.

## The symmetric group S₄

The S₄ provider proves the five conjugacy classes and constructs all five irreducibles:
trivial, sign, the two-dimensional sum-zero representation on the three pair partitions, the
three-dimensional deleted permutation representation, and its sign twist. Their characters are
computed from the actual actions; simplicity, dimensions `1,1,2,3,3`, pairwise non-isomorphism,
exhaustiveness, and the sum-of-squares identity are proved.

The source obtains the two-dimensional object by pullback along `S₄/V₄ ≅ S₃`. The Lean
provider realizes the same action directly on the three pair partitions. Its action homomorphism
is the quotient action used in that construction. A separately packaged kernel/surjectivity/
quotient-isomorphism chain is not required for the example's representation-classification
endpoint, and the existing fidelity review correctly treats this as an equivalent realization,
not a coverage gap. The source's geometric cube/tetrahedron descriptions are likewise represented
by their equivalent permutation and sign-twist models; the distinction of the two three-
dimensional objects is established by different character values on a transposition.

## Verification

- all six records are sorry-free or not applicable as appropriate;
- the detailed 2026-07-21 stale-gap re-audit verifies all four mathematical examples and reports
  only standard axioms on their headline declarations;
- the final exercise audit verifies all three Exercise 4.3.1 endpoints;
- issue #5429, retained by the old S₄ tracker record, is closed as completed;
- the Chapter 4 aggregate and all scoped providers rebuild on the current toolchain.

