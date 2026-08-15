/-
Copyright (c) 2026 mathlib-initiative. All rights reserved.
Released under Apache 2.0 license as described in the file LICENCE.
Authors: Kim Morrison
-/

import RepresentationTheory.Algebra.Module.TensorRestriction
import RepresentationTheory.Algebra.Module.FinitelyGeneratedSubalgebraDescent
import RepresentationTheory.Alignment.Attribute

/-! # Tensor-equivalence descent -/

open scoped TensorProduct

namespace RepresentationTheory.Algebra.Module.TensorEquivDescent

variable {K A V W L : Type*}
  [Field K] [Ring A] [Algebra K A]
  [AddCommGroup V] [Module K V] [Module A V] [IsScalarTower K A V]
  [AddCommGroup W] [Module K W] [Module A W] [IsScalarTower K A W]
  [Field L] [Algebra K L]

/-- An equivalence after tensor extension yields an equivalence before tensor extension under finite-dimensionality hypotheses. -/
@[source_ref "Chapter3/Problem3.8.4" (role := primary),
  source_ref "Chapter3/Problem3.8.4/Derived3" (role := supporting)]
theorem exists_equiv_of_tensorEquiv [FiniteDimensional K V] [FiniteDimensional K W]
    (h : Nonempty ((L ⊗[K] V) ≃ₗ[L ⊗[K] A] (L ⊗[K] W))) :
    Nonempty (V ≃ₗ[A] W) := by
  obtain ⟨e⟩ := h
  obtain ⟨R, hRfg, hR⟩ :=
    RepresentationTheory.Algebra.Module.FinitelyGeneratedSubalgebraDescent.exists_fgSubalgebra_equiv e
  haveI : Algebra.FiniteType K ↥R := (Subalgebra.fg_iff_finiteType R).mp hRfg
  obtain ⟨m, hm⟩ := Ideal.exists_maximal ↥R
  letI : Field (↥R ⧸ m) := Ideal.Quotient.field m
  haveI : Algebra.FiniteType K (↥R ⧸ m) :=
    Algebra.FiniteType.of_surjective (Ideal.Quotient.mkₐ K m)
      (Ideal.Quotient.mkₐ_surjective K m)
  haveI : Module.Finite K (↥R ⧸ m) := finite_of_finite_type_of_isJacobsonRing K (↥R ⧸ m)
  have hκ :=
    RepresentationTheory.LinearAlgebra.TensorProduct.ModuleBaseChange.nonempty_linearEquiv_of_baseChange
      (V := V) (W := W) (Ideal.Quotient.mkₐ K m) hR
  exact RepresentationTheory.Algebra.Module.TensorRestriction.exists_equiv_of_tensorEquiv hκ

end RepresentationTheory.Algebra.Module.TensorEquivDescent
