/-
Copyright (c) 2026 mathlib-initiative. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

import Mathlib.RingTheory.MatrixAlgebra
import Mathlib.LinearAlgebra.Matrix.Reindex
import RepresentationTheory.Alignment.Attribute

/-! # Tensor products of matrix algebras -/

open scoped TensorProduct

namespace RepresentationTheory.LinearAlgebra.Matrix.TensorProduct

/-- The tensor product of square matrix algebras of sizes m and n is nonemptily
algebra-equivalent to the square matrix algebra of size m times n. -/
@[source_ref "Chapter3/Exercise3.10.1" (role := primary)]
theorem matrixTensorProduct_algEquiv (k : Type*) [CommRing k] (m n : ℕ) :
    Nonempty
      ((Matrix (Fin m) (Fin m) k ⊗[k] Matrix (Fin n) (Fin n) k) ≃ₐ[k]
        Matrix (Fin (m * n)) (Fin (m * n)) k) :=
  ⟨(Matrix.kroneckerTMulAlgEquiv (Fin m) (Fin n) k k k k).trans <|
    ((Algebra.TensorProduct.rid k k k).mapMatrix).trans <|
      Matrix.reindexAlgEquiv k _ finProdFinEquiv⟩

end RepresentationTheory.LinearAlgebra.Matrix.TensorProduct
