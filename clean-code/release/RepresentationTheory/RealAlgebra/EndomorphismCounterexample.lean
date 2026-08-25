/-
Copyright (c) 2026 mathlib-initiative. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

import Mathlib.LinearAlgebra.Complex.FiniteDimensional
import RepresentationTheory.Algebra.SimpleModule.Endomorphisms
import RepresentationTheory.Alignment.Attribute

/-! # A real scalar-endomorphism counterexample -/

namespace RepresentationTheory.RealAlgebra.EndomorphismCounterexample

/-- Multiplication by the imaginary unit on the complex numbers is not multiplication by a real scalar. -/
@[source_ref "Chapter2/Remark2.3.11" (role := primary)]
theorem complexImaginaryLinearMap_not_real_scalar :
    ¬ ∃ c : ℝ, ∀ v : ℂ, (Complex.I • (LinearMap.id : ℂ →ₗ[ℂ] ℂ)) v = c • v := by
  rintro ⟨c, hc⟩
  have h1 := hc 1
  simp only [LinearMap.smul_apply, LinearMap.id_coe, id_eq, smul_eq_mul, mul_one,
    Complex.real_smul] at h1
  have := congrArg Complex.im h1
  simp at this

/-- The proposed assertion that every such endomorphism is scalar multiplication is false. -/
@[source_ref "Chapter2/Remark2.3.11" (role := primary)]
theorem not_real_scalar_endomorphism_principle :
    ¬ ∀ {A : Type} [Ring A] [Algebra ℝ A]
      {V : Type} [AddCommGroup V] [Module ℝ V] [Module A V] [IsScalarTower ℝ A V]
      [IsSimpleModule A V] [FiniteDimensional ℝ V]
      (φ : V →ₗ[A] V), ∃ c : ℝ, ∀ v : V, φ v = c • v := by
  intro h
  exact complexImaginaryLinearMap_not_real_scalar
    (h (A := ℂ) (V := ℂ) (φ := Complex.I • (LinearMap.id : ℂ →ₗ[ℂ] ℂ)))

end RepresentationTheory.RealAlgebra.EndomorphismCounterexample
