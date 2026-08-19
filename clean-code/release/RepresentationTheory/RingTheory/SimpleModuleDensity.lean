/-
Copyright (c) 2026 mathlib-initiative. All rights reserved.
Released under Apache 2.0 license as described in the file LICENCE.
Authors: Kim Morrison
-/

import RepresentationTheory.Algebra.Module.SimpleScalarSurjectivity

/-! # Simultaneous interpolation on a simple module -/

namespace RepresentationTheory.RingTheory.SimpleModuleDensity

open Module in

/-- On a simple finite-dimensional module over an algebraically closed field, any prescribed images of a finite linearly independent family are simultaneously realized by one algebra element. -/
theorem exists_smul_eq_on_linearIndependent (k : Type*) (A : Type*) (V : Type*)
    [Field k] [IsAlgClosed k] [Ring A] [Algebra k A]
    [AddCommGroup V] [Module k V] [Module A V] [IsScalarTower k A V]
    [FiniteDimensional k V] [IsSimpleModule A V]
    {n : ℕ} (v : Fin n → V) (hv : LinearIndependent k v) (w : Fin n → V) :
    ∃ a : A, ∀ i, a • v i = w i := by
  let b : Basis (Fin n) k (Submodule.span k (Set.range v)) := Basis.span hv
  let f₀ : (Submodule.span k (Set.range v)) →ₗ[k] V := b.constr k w
  obtain ⟨f, hf⟩ := f₀.exists_extend
  have hfv : ∀ i, f (v i) = w i := by
    intro i
    have h1 : f ((Submodule.span k (Set.range v)).subtype (b i)) = f₀ (b i) :=
      LinearMap.congr_fun hf (b i)
    rw [Basis.constr_basis] at h1
    rwa [show (Submodule.span k (Set.range v)).subtype (b i) = v i from
      Basis.coe_span_apply hv i] at h1
  obtain ⟨a, ha⟩ :=
    RepresentationTheory.Algebra.Module.SimpleScalarSurjectivity.algebra_smul_surjective
      k A V f
  refine ⟨a, fun i => ?_⟩
  have h := LinearMap.congr_fun ha (v i)
  rw [hfv i] at h
  exact h

end RepresentationTheory.RingTheory.SimpleModuleDensity
