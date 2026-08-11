import Mathlib.RingTheory.MatrixAlgebra
import Mathlib.LinearAlgebra.Matrix.Reindex

open scoped TensorProduct

/-!
# Exercise 3.10.1: Tensor product of matrix algebras

Show that `Mat_m(k) ⊗ Mat_n(k) ≅ Mat_{mn}(k)`.

This is the tensor product of the two matrix algebras over the base field `k`, and the
claimed isomorphism is one of `k`-algebras. In Mathlib the relevant equivalence is
`Matrix.kroneckerTMulAlgEquiv`, which sends `Mat_m(A) ⊗ Mat_n(B)` to
`Mat_{m × n}(A ⊗ B)`; specialising `A = B = k` and re-indexing `Fin m × Fin n ≃ Fin (m*n)`
(together with `k ⊗ k ≅ k`) gives the statement in the book's form `Mat_{mn}(k)`.

The isomorphism is constructed by `matrix_tensorProduct_matrix`, which
composes `Matrix.kroneckerTMulAlgEquiv` (giving `Mat_{m × n}(k ⊗ k)`), `Algebra.TensorProduct.rid`
(collapsing `k ⊗ k ≅ k` via `AlgEquiv.mapMatrix`), and `Matrix.reindexAlgEquiv` along
`finProdFinEquiv` (re-indexing `Fin m × Fin n ≃ Fin (m*n)`).
-/

/-- Exercise 3.10.1: the tensor product of matrix algebras `Mat_m(k) ⊗ Mat_n(k)` is
isomorphic, as a `k`-algebra, to the matrix algebra `Mat_{mn}(k)`. -/
theorem Etingof.matrix_tensorProduct_matrix (k : Type*) [CommRing k] (m n : ℕ) :
    Nonempty
      ((Matrix (Fin m) (Fin m) k ⊗[k] Matrix (Fin n) (Fin n) k) ≃ₐ[k]
        Matrix (Fin (m * n)) (Fin (m * n)) k) :=
  ⟨(Matrix.kroneckerTMulAlgEquiv (Fin m) (Fin n) k k k k).trans <|
    ((Algebra.TensorProduct.rid k k k).mapMatrix).trans <|
      Matrix.reindexAlgEquiv k _ finProdFinEquiv⟩
