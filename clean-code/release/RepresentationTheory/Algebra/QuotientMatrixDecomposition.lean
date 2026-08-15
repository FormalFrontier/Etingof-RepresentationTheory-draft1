/-
Copyright (c) 2026 FormalFrontier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENCE.
Authors: FormalFrontier
-/

import RepresentationTheory.Algebra.Semisimplicity.SimpleQuotients
import RepresentationTheory.FieldAlgebraProperties
import RepresentationTheory.CategoryTheory.LinearAlgebra.Auxiliary
import Mathlib.LinearAlgebra.Matrix.ToLin

universe u v w

/-!
# Quotient matrix decompositions

Matrix decompositions of quotients by the simple-module annihilator, together with a criterion
for their matrix blocks to be one-dimensional.
-/

open CategoryTheory CategoryTheory.Limits Module

namespace RepresentationTheory.Algebra.QuotientMatrixDecomposition

section Transport

variable {R : Type*} {S : Type*} [Ring R] [Ring S]

/-- Transfers pairwise commutativity of multiplication backward along a ring equivalence. -/
theorem ringEquiv_forall_mul_comm (e : R ≃+* S) (h : ∀ x y : S, x * y = y * x) (x y : R) :
    x * y = y * x :=
  e.injective (by rw [map_mul, map_mul, h])

/-- A ring equivalence preserves and reflects pairwise commutativity of multiplication. -/
theorem ringEquiv_forall_mul_comm_iff (e : R ≃+* S) :
    (∀ x y : R, x * y = y * x) ↔ ∀ x y : S, x * y = y * x :=
  ⟨fun h => ringEquiv_forall_mul_comm e.symm h, fun h => ringEquiv_forall_mul_comm e h⟩

end Transport

section MatrixForm

variable (k : Type w) (A : Type u)
variable [Field k] [IsAlgClosed k] [Ring A] [Algebra k A] [FiniteDimensional k A]

omit [IsAlgClosed k] in
/-- The quotient by a coatom submodule has vector-space dimension at least one. -/
theorem one_le_finrank_quotient_of_isCoatom (M : Submodule A A) (hM : IsCoatom M) :
    1 ≤ finrank k (A ⧸ M) := by
  haveI : FiniteDimensional k (A ⧸ M) :=
    RepresentationTheory.Algebra.Semisimplicity.SimpleQuotients.finiteDimensional_quotient k A M
  haveI : IsSimpleModule A (A ⧸ M) := isSimpleModule_iff_isCoatom.mpr hM
  haveI : Nontrivial (A ⧸ M) := IsSimpleModule.nontrivial A (A ⧸ M)
  exact finrank_pos

/-- Chooses coatom submodules representing simple modules and decomposes the specified quotient as a family of matrix algebras. -/
theorem exists_coatom_submodules_matrix_decomposition :
    ∃ s : Finset (Submodule A A),
      (∀ M ∈ s, IsCoatom M) ∧
      (∀ M ∈ s, ∀ N ∈ s, M ≠ N → IsEmpty ((A ⧸ M) ≃ₗ[A] (A ⧸ N))) ∧
      (∀ (W : Type u) [AddCommGroup W] [Module A W] [IsSimpleModule A W],
        ∃ M ∈ s, Nonempty (W ≃ₗ[A] (A ⧸ M))) ∧
      (∀ M : {x // x ∈ s}, 1 ≤ finrank k (A ⧸ (M : Submodule A A))) ∧
      Nonempty ((A ⧸
        RepresentationTheory.RingTheory.SimpleModuleAnnihilator.simpleModuleAnnihilator A) ≃ₐ[k]
        ∀ M : {x // x ∈ s},
          Matrix (Fin (finrank k (A ⧸ (M : Submodule A A))))
            (Fin (finrank k (A ⧸ (M : Submodule A A)))) k) := by
  classical
  obtain ⟨s, hcoatom, -, hnoniso, hexh, ⟨e⟩⟩ :=
    RepresentationTheory.Algebra.Semisimplicity.SimpleQuotients.exists_finite_coatomFamily_algEquiv_quotient
      k A
  haveI hfd : ∀ M : {x // x ∈ s}, FiniteDimensional k (A ⧸ (M : Submodule A A)) := fun M =>
    RepresentationTheory.Algebra.Semisimplicity.SimpleQuotients.finiteDimensional_quotient k A _
  -- Choosing a basis of each simple turns its `k`-endomorphism algebra into a matrix algebra.
  let toMat : ∀ M : {x // x ∈ s},
      Module.End k (A ⧸ (M : Submodule A A)) ≃ₐ[k]
        Matrix (Fin (finrank k (A ⧸ (M : Submodule A A))))
          (Fin (finrank k (A ⧸ (M : Submodule A A)))) k := fun M =>
    LinearMap.toMatrixAlgEquiv (Module.finBasis k (A ⧸ (M : Submodule A A)))
  exact ⟨s, hcoatom, hnoniso, hexh,
    fun M => one_le_finrank_quotient_of_isCoatom k A _ (hcoatom M M.2),
    ⟨e.trans (AlgEquiv.piCongrRight toMat)⟩⟩

omit [IsAlgClosed k] [FiniteDimensional k A] in
/-- Characterizes the displayed property of an algebra by commutativity of its specified quotient. -/
theorem property_iff_quotient_mul_comm :
    RepresentationTheory.FieldAlgebraProperties.fieldAlgebraProperty k A ↔
      ∀ x y : A ⧸
        RepresentationTheory.RingTheory.SimpleModuleAnnihilator.simpleModuleAnnihilator A,
        x * y = y * x :=
  (ringEquiv_forall_mul_comm_iff
    (Ideal.quotEquivOfEq (Ideal.jacobson_bot (R := A)))).symm

omit [IsAlgClosed k] [FiniteDimensional k A] in
/-- For a given decomposition into nonempty square matrix blocks, characterizes the displayed property by every block having size one. -/
theorem property_iff_matrix_block_sizes_eq_one {ι : Type*} (d : ι → ℕ) (hd : ∀ i, 1 ≤ d i)
    (e : (A ⧸
      RepresentationTheory.RingTheory.SimpleModuleAnnihilator.simpleModuleAnnihilator A) ≃ₐ[k]
        ∀ i, Matrix (Fin (d i)) (Fin (d i)) k) :
    RepresentationTheory.FieldAlgebraProperties.fieldAlgebraProperty k A ↔ ∀ i, d i = 1 := by
  rw [property_iff_quotient_mul_comm k A, ringEquiv_forall_mul_comm_iff e.toRingEquiv]
  exact
    RepresentationTheory.CategoryTheory.LinearAlgebra.Auxiliary.forall_matrix_mul_comm_iff
      (k := k) d hd

/-- Chooses coatom submodules representing simple modules and gives the displayed matrix decomposition and one-dimensional block criterion. -/
theorem exists_coatom_submodules_matrix_decomposition_iff :
    ∃ s : Finset (Submodule A A),
      (∀ M ∈ s, IsCoatom M) ∧
      (∀ M ∈ s, ∀ N ∈ s, M ≠ N → IsEmpty ((A ⧸ M) ≃ₗ[A] (A ⧸ N))) ∧
      (∀ (W : Type u) [AddCommGroup W] [Module A W] [IsSimpleModule A W],
        ∃ M ∈ s, Nonempty (W ≃ₗ[A] (A ⧸ M))) ∧
      (∀ M : {x // x ∈ s}, 1 ≤ finrank k (A ⧸ (M : Submodule A A))) ∧
      Nonempty ((A ⧸
        RepresentationTheory.RingTheory.SimpleModuleAnnihilator.simpleModuleAnnihilator A) ≃ₐ[k]
        ∀ M : {x // x ∈ s},
          Matrix (Fin (finrank k (A ⧸ (M : Submodule A A))))
            (Fin (finrank k (A ⧸ (M : Submodule A A)))) k) ∧
      (RepresentationTheory.FieldAlgebraProperties.fieldAlgebraProperty k A ↔
        ∀ M : {x // x ∈ s}, finrank k (A ⧸ (M : Submodule A A)) = 1) := by
  obtain ⟨s, hcoatom, hnoniso, hexh, hpos, ⟨e⟩⟩ :=
    exists_coatom_submodules_matrix_decomposition k A
  exact ⟨s, hcoatom, hnoniso, hexh, hpos, ⟨e⟩,
    property_iff_matrix_block_sizes_eq_one k A _ hpos e⟩

end MatrixForm

section CartanAlgebra

/-! ## Opposite endomorphism algebras -/

variable {k : Type w} [Field k] [IsAlgClosed k]
variable {C : Type u} [Category.{v} C]
  [RepresentationTheory.CategoryTheory.SubobjectFiniteDimensional.SubobjectFiniteDimensional C]
  [Linear k C]
  [RepresentationTheory.CategoryTheory.Abelian.FiniteLength.SchurFiniteLengthCategory k C]
  [HasFiniteBiproducts C]
variable {ι : Type v} [Fintype ι]

omit [IsAlgClosed k] [HasFiniteBiproducts C] in
/-- The opposite endomorphism algebra of any displayed object is finite-dimensional over the field. -/
theorem finiteDimensional_op_end (X : C) : FiniteDimensional k (End X)ᵐᵒᵖ := by
  haveI : FiniteDimensional k (End X) :=
    RepresentationTheory.CategoryTheory.Abelian.FiniteLength.SchurFiniteLengthCategory.finiteDimensional_hom
      X X
  exact Module.Finite.equiv (MulOpposite.opLinearEquiv k (M := End X))

/-- Constructs positive matrix block sizes and an algebra equivalence for the displayed quotient of an opposite endomorphism algebra, with the stated criterion for all blocks to have size one. -/
theorem exists_matrix_decomposition_of_op_end_quotient_iff (P : ι → C) (n : ι → ℕ) :
    ∃ (J : Type v) (_ : Fintype J) (d : J → ℕ), (∀ j, 1 ≤ d j) ∧
      Nonempty ((((End
        (RepresentationTheory.CategoryTheory.Preadditive.ProjectiveDecomposition.biproductOfMultiplicities
          P n))ᵐᵒᵖ) ⧸
        RepresentationTheory.RingTheory.SimpleModuleAnnihilator.simpleModuleAnnihilator
          ((End
            (RepresentationTheory.CategoryTheory.Preadditive.ProjectiveDecomposition.biproductOfMultiplicities
              P n))ᵐᵒᵖ))
        ≃ₐ[k] ∀ j, Matrix (Fin (d j)) (Fin (d j)) k) ∧
      (RepresentationTheory.FieldAlgebraProperties.fieldAlgebraProperty k
        ((End
          (RepresentationTheory.CategoryTheory.Preadditive.ProjectiveDecomposition.biproductOfMultiplicities
            P n))ᵐᵒᵖ) ↔ ∀ j, d j = 1) := by
  classical
  haveI : FiniteDimensional k
      (End
        (RepresentationTheory.CategoryTheory.Preadditive.ProjectiveDecomposition.biproductOfMultiplicities
          P n))ᵐᵒᵖ :=
    finiteDimensional_op_end
      (RepresentationTheory.CategoryTheory.Preadditive.ProjectiveDecomposition.biproductOfMultiplicities
        P n)
  obtain ⟨s, -, -, -, hpos, ⟨e⟩, hbasic⟩ :=
    exists_coatom_submodules_matrix_decomposition_iff k
      ((End
        (RepresentationTheory.CategoryTheory.Preadditive.ProjectiveDecomposition.biproductOfMultiplicities
          P n))ᵐᵒᵖ)
  exact ⟨{x // x ∈ s}, inferInstance, _, hpos, ⟨e⟩, hbasic⟩

end CartanAlgebra

end RepresentationTheory.Algebra.QuotientMatrixDecomposition
