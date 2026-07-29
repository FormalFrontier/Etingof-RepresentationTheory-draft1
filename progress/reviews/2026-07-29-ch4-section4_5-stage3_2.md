# Stage 3.2 review — Chapter 4, §4.5

## Scope and result

This review covers the eight contiguous records from `Chapter4/Introduction_4.5` through
`Chapter4/Remark4.5.5`. Every mathematical endpoint is now formalized. Two tracker records are
stale: Remark 4.5.3 was completed by merged PR #7941, closing #5183, and Remark 4.5.5's build
regression #7527 was repaired by merged PR #7626. Both providers rebuild on the current toolchain.

## First orthogonality and its consequence

The introduction's Hermitian pairing is represented by the normalized character sums in
`Etingof.Theorem4_5_1_i` and `Etingof.Theorem4_5_1_ii`. The first theorem identifies the pairing
with the dimension of the genuine equivariant-Hom space for arbitrary finite-dimensional
representations; the second specializes to the Kronecker delta for simple objects. Combined with
Theorem 4.2.1's spanning result, this is exactly the asserted orthonormal basis statement.

The source proof's averaging operator, invariant projection, tensor-dual character calculation,
and invariants/Hom identification are supplied by the Mathlib character-orthogonality machinery
underlying those declarations. `Etingof.Discussion_after_Theorem4_5_1` states the resulting
biconditional irreducibility criterion, not merely one implication.

## Central idempotents and the Frobenius characterization

Problem 4.5.2 is covered by `Etingof.psi`, `psi_acts_self`, `psi_acts_other`,
`psi_idempotent`, and `psi_orthogonal`. The element is the source's explicit character sum in the
actual complex group algebra; its actions are identity/zero on the appropriate simple objects,
and the idempotent and pairwise-orthogonality equations are proved. The final exercise audit
records both source parts independently.

Remark 4.5.3 defines convolution, its unit, the class-function subalgebra, primitive idempotents,
and the renormalized character elements. `character_recovery_exact` supplies the source's definite
normalization, `renormChar_isPrimitiveIdempotent` proves the forward direction,
`sum_renormChar_eq_one` proves completeness, and
`isPrimitiveIdempotent_iff_exists_simple_renormChar` proves the converse classification. Thus the
old note claiming that only the forward direction and an unspecified square-root scalar exist is
obsolete. The historical closing prose is non-formalizable and carries no proof obligation.

## Second orthogonality

The discussion before Theorem 4.5.4 is organizational. `Etingof.Theorem4_5_4` proves the exact
column-orthogonality formula: the sum over a complete irreducible family is the centralizer order
when the two elements are conjugate and zero otherwise. The proof constructs the conjugation
operator on the regular representation and computes its trace, matching the source proof.

Remark 4.5.5 separately packages the unitary character-matrix proof. The matrix is square because
irreducible classes and conjugacy classes have equal cardinality; its entries have the source's
centralizer normalization. `character_matrix_mul_conjTranspose` proves row orthogonality,
`character_matrix_conjTranspose_mul` proves column orthogonality, and `column_orthogonality` reads
off the stated formula. The cited regression is closed and the provider is sorry-free.

## Fidelity and integrity

All representations, Hom spaces, group-algebra elements, convolution products, primitive
idempotents, character matrices, and centralizers are genuine structures. None of the conclusions
is assumed as a hypothesis. Existing axiom audits for the theorem, problem, and both remarks report
only `propext`, `Classical.choice`, and `Quot.sound`; the source tree contains no admission in this
scope. Consequently all eight records have complete claim coverage and verified fidelity (with
the organizational discussion marked not applicable for proof integrity).

