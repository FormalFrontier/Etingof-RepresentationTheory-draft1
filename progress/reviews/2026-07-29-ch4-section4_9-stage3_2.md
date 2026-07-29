# Stage 3.2 review — Chapter 4, §4.9

## Scope and result

This review covers `Chapter4/Introduction_4.9` and `Chapter4/Example4.9.1`. The generic
multiplicity formula and every cell of the `S₃`, `S₄`, and `A₅` tensor-product tables are
formalized as statements about genuine finite-dimensional representations. Both providers rebuild
without warnings or admissions.

## Generic multiplicity formula

`Etingof.tensorMultiplicity X Y S` is the dimension of the equivariant-Hom space from the simple
object `S` to `X ⊗ Y`. `Etingof.tensorMultiplicity_eq_inner` proves the character formula

`N = |G|⁻¹ ∑ g, χ_X(g) χ_Y(g) χ_S(g⁻¹)`.

`Etingof.tensorDecomposition` then constructs the actual representation isomorphism to the sum of
irreducibles with these multiplicities for any complete pairwise-nonisomorphic simple family;
`Etingof.exists_tensorDecomposition` supplies such a family unconditionally. The decomposition is
obtained from semisimplicity and isotypic decomposition, rather than treating character equality
alone as definitional equality of representations.

## The three tables

The indexed functions `nS3`, `nS4`, and `nA5` encode every displayed multiplicity, including the
multiplicity-two entries in the final `A₅` products. For each group, the `*_tensor_character`
theorem proves the row-wise character identity, `*_tensor_product_character` connects it to the
actual tensor-product representation, and `*_tensor_iso` gives the resulting `FDRep` isomorphism.
The `*_tensor_iso_biproduct` variants present the targets as categorical direct sums.
`Etingof.Example4_9_1.stdRep_tensor_stdRep_iso` separately spells out the source's
`ℂ² ⊗ ℂ² ≅ ℂ₊ ⊕ ℂ₋ ⊕ ℂ²` example.

No table entry is represented only by a numeric check or an assumed character array. Both records
therefore have complete Stage 3.2 claim coverage, verified fidelity, and verified nonvacuity.
