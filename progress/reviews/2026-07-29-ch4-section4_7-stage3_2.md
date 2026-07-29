# Stage 3.2 review — Chapter 4, §4.7

## Scope and result

This review covers `Chapter4/Introduction_4.7` and `Chapter4/Proposition4.7.1`. All source
claims are represented, the provider is sorry-free, and it now rebuilds without warnings.

## Matrix coefficients and orthogonality

The introductory matrix coefficients are the entries of `LinearMap.toMatrix` used throughout
the proposition. `Etingof.Proposition4_7_1_i` proves that coefficients belonging to
nonisomorphic simple representations pair to zero. `Etingof.Proposition4_7_1_ii` computes the
same-representation pairing as the two Kronecker deltas divided by the dimension.

The declarations work over an arbitrary algebraically closed field with invertible group order,
using the bilinear pairing

`|G|⁻¹ ∑ g, f(g) h(g⁻¹)`.

For complex unitary matrix coefficients this is the book's Hermitian pairing after transposing
the second coefficient's indices, because the inverse representation matrix is the conjugate
transpose. Thus the generalized statements specialize to the two displayed source formulas.

## Basis conclusion and integrity

`Etingof.MatrixCoefficients.basis` is an actual `Module.Basis` of the full function space,
assembled from matrix coefficients of a complete irreducible family. Orthogonality gives linear
independence and the Artin–Wedderburn sum-of-squares count supplies the correct cardinality.
`Etingof.Proposition4_7_1_orthogonal_basis` packages orthogonality of this basis, while
`Etingof.Proposition4_7_1_exists_orthogonal_basis` provides the unconditional existential form.

The proof uses genuine representations, bases, matrices, and the full function space; no desired
conclusion is passed in as a hypothesis. Both records therefore have complete Stage 3.2 claim
coverage and verified fidelity.
