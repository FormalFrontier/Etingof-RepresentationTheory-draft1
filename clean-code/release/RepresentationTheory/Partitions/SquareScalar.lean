/-
Copyright (c) 2026 mathlib-initiative. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: mathlib-initiative
-/

import RepresentationTheory.SymmetricGroup.PartitionGroupAlgebra

/-!
# Square-scalar identity for a partition group-algebra element

Shows that the group-algebra element associated with a natural-number partition has square equal
to a scalar multiple of itself.
-/

namespace RepresentationTheory.Partitions.SquareScalar

/-- For every natural-number partition, the product of the associated object with itself is a
scalar multiple of that object. -/
theorem exists_mul_self_eq_smul
    (n : ℕ) (la : Nat.Partition n) :
    ∃ α : ℂ,
      RepresentationTheory.SymmetricGroup.PartitionAuxiliaryConstructions.auxiliaryPartitionGroupAlgebraElementC n la *
          RepresentationTheory.SymmetricGroup.PartitionAuxiliaryConstructions.auxiliaryPartitionGroupAlgebraElementC n la =
        α • RepresentationTheory.SymmetricGroup.PartitionAuxiliaryConstructions.auxiliaryPartitionGroupAlgebraElementC n la := by
  obtain ⟨ℓ, hℓ⟩ :=
    RepresentationTheory.SymmetricGroup.PartitionGroupAlgebra.exists_sign_fixed_sandwich_eq_smul
      n la
  exact
    ⟨ℓ
        (RepresentationTheory.SymmetricGroup.PartitionAuxiliaryConstructions.auxiliaryPartitionGroupAlgebraElementB n la *
          RepresentationTheory.SymmetricGroup.PartitionAuxiliaryConstructions.auxiliaryPartitionGroupAlgebraElementA n la),
      by
        simp only [
          RepresentationTheory.SymmetricGroup.PartitionAuxiliaryConstructions.auxiliaryPartitionGroupAlgebraElementC]
        rw [mul_assoc
            (RepresentationTheory.SymmetricGroup.PartitionAuxiliaryConstructions.auxiliaryPartitionGroupAlgebraElementA n la)
            (RepresentationTheory.SymmetricGroup.PartitionAuxiliaryConstructions.auxiliaryPartitionGroupAlgebraElementB n la),
          ← mul_assoc
            (RepresentationTheory.SymmetricGroup.PartitionAuxiliaryConstructions.auxiliaryPartitionGroupAlgebraElementB n la)
            (RepresentationTheory.SymmetricGroup.PartitionAuxiliaryConstructions.auxiliaryPartitionGroupAlgebraElementA n la),
          ← mul_assoc
            (RepresentationTheory.SymmetricGroup.PartitionAuxiliaryConstructions.auxiliaryPartitionGroupAlgebraElementA n la)]
        exact hℓ _⟩

end RepresentationTheory.Partitions.SquareScalar
