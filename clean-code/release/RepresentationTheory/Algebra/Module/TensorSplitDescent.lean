/-
Copyright (c) 2026 mathlib-initiative. All rights reserved.
Released under Apache 2.0 license as described in the file LICENCE.
Authors: Kim Morrison
-/

import RepresentationTheory.Algebra.Module.TensorRestriction
import RepresentationTheory.Algebra.Module.FinitelyGeneratedSubalgebraDescent
import RepresentationTheory.Alignment.Attribute

/-! # Tensor-split descent -/

open scoped TensorProduct

namespace RepresentationTheory.Algebra.Module.TensorSplitDescent

variable {K A V W L : Type*}
  [Field K] [Ring A] [Algebra K A]
  [AddCommGroup V] [Module K V] [Module A V] [IsScalarTower K A V]
  [AddCommGroup W] [Module K W] [Module A W] [IsScalarTower K A W]
  [Field L] [Algebra K L]

/-- A retraction after tensor extension yields a retraction before tensor extension under finite-dimensionality hypotheses. -/
@[source_ref "Chapter3/Problem3.8.4" (role := primary)]
theorem exists_retract_of_tensorRetract
    [FiniteDimensional K V] [FiniteDimensional K W]
    (h : ∃ (i : (L ⊗[K] V) →ₗ[L ⊗[K] A] (L ⊗[K] W))
           (p : (L ⊗[K] W) →ₗ[L ⊗[K] A] (L ⊗[K] V)), p.comp i = LinearMap.id) :
    ∃ (i : V →ₗ[A] W) (p : W →ₗ[A] V), p.comp i = LinearMap.id := by
  obtain ⟨i, p, hpi⟩ := h
  obtain ⟨R, hFG, i', p', hpi'⟩ :=
    RepresentationTheory.Algebra.Module.FinitelyGeneratedSubalgebraDescent.exists_fgSubalgebra_retract
      i p hpi
  haveI : Algebra.FiniteType K ↥R := (Subalgebra.fg_iff_finiteType R).mp hFG
  obtain ⟨m, _hm⟩ := Ideal.exists_maximal ↥R
  letI : Field (↥R ⧸ m) := Ideal.Quotient.field m
  haveI : FiniteDimensional K (↥R ⧸ m) := finite_of_finite_type_of_isJacobsonRing K (↥R ⧸ m)
  obtain ⟨i'', p'', hpi''⟩ :=
    RepresentationTheory.LinearAlgebra.TensorProduct.ModuleBaseChange.exists_retraction_of_baseChange
      (Ideal.Quotient.mkₐ K m) ⟨i', p', hpi'⟩
  exact RepresentationTheory.Algebra.Module.TensorRestriction.exists_retract_of_tensorRetract
    ⟨i'', p'', hpi''⟩

end RepresentationTheory.Algebra.Module.TensorSplitDescent
