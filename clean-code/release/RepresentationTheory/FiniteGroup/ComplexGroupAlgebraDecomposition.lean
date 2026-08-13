/-
Copyright (c) 2026 FormalFrontier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENCE.
Authors: FormalFrontier
-/

import RepresentationTheory.Algebra.MonoidAlgebra.Center
import RepresentationTheory.SemisimpleAlgebraCenters

/-!
# Complex Group Algebra Decomposition
-/

open scoped Classical in
noncomputable section

namespace RepresentationTheory.FiniteGroup.ComplexGroupAlgebraDecomposition

/-- The complex monoid algebra of a finite group is algebra-equivalent to a product of nonzero
square complex matrix algebras indexed by the finite cardinality of its conjugacy classes. -/
theorem exists_fin_conjClasses_card_indexed_matrix_block_decomposition
    (G : Type*) [Group G] [Finite G] :
    ∃ d : Fin (Nat.card (ConjClasses G)) → ℕ, (∀ i, d i ≠ 0) ∧
      Nonempty (MonoidAlgebra ℂ G ≃ₐ[ℂ] Π i, Matrix (Fin (d i)) (Fin (d i)) ℂ) := by
  haveI : Fintype G := Fintype.ofFinite _
  have h : Module.finrank ℂ (Subalgebra.center ℂ (MonoidAlgebra ℂ G)) =
      Nat.card (ConjClasses G) :=
    RepresentationTheory.Algebra.MonoidAlgebra.Center.finrank_center_eq_card_conjClasses ℂ G
  rw [← h]
  exact
    RepresentationTheory.SemisimpleAlgebraCenters.exists_algEquiv_pi_matrix_monoidAlgebra
      (k := ℂ) G

/-- For every finite group, there are a nonempty index type whose cardinality equals that of its
conjugacy classes, nonzero block sizes on that type, and a complex-algebra equivalence from its
monoid algebra to the corresponding product of square complex matrix algebras. -/
theorem exists_type_indexed_matrix_block_decomposition_card_eq_conjClasses
    (G : Type*) [Group G] [Finite G] :
    ∃ (ι : Type) (_ : Fintype ι),
      Nat.card ι = Nat.card (ConjClasses G) ∧
      ∃ d : ι → ℕ, (∀ j, d j ≠ 0) ∧
        Nonempty (MonoidAlgebra ℂ G ≃ₐ[ℂ] Π j, Matrix (Fin (d j)) (Fin (d j)) ℂ) := by
  obtain ⟨d, hd, he⟩ :=
    exists_fin_conjClasses_card_indexed_matrix_block_decomposition G
  exact ⟨Fin (Nat.card (ConjClasses G)), inferInstance, by simp, d, hd, he⟩

end RepresentationTheory.FiniteGroup.ComplexGroupAlgebraDecomposition

end
