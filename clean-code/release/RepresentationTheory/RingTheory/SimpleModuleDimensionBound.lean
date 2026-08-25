/-
Copyright (c) 2026 mathlib-initiative. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

import RepresentationTheory.Algebra.Module.SimpleScalarSurjectivity
import RepresentationTheory.Alignment.Attribute

/-! # Dimension bounds from simple modules -/

namespace RepresentationTheory.RingTheory.SimpleModuleDimensionBound

open Finset Module in

/-- For a finite family of pairwise nonisomorphic finite-dimensional simple modules, the sum of the squares of their ranks is at most the rank of the algebra. -/
@[source_ref "Chapter3/Corollary3.5.5" (role := supporting)]
theorem sum_finrank_sq_le (k : Type*) (A : Type*)
    [Field k] [IsAlgClosed k] [Ring A] [Algebra k A] [FiniteDimensional k A]
    (ι : Type*) [Fintype ι]
    (V : ι → Type*) [∀ i, AddCommGroup (V i)] [∀ i, Module k (V i)]
    [∀ i, Module A (V i)] [∀ i, IsScalarTower k A (V i)]
    [∀ i, FiniteDimensional k (V i)] [∀ i, IsSimpleModule A (V i)]
    (h_noniso : ∀ i j, i ≠ j → IsEmpty (V i ≃ₗ[A] V j)) :
    ∑ i : ι, (finrank k (V i)) ^ 2 ≤ finrank k A := by
  have hsurj :=
    RepresentationTheory.Algebra.Module.SimpleScalarSurjectivity.family_algebra_smul_surjective
      k A ι V h_noniso
  let φ : A →ₗ[k] (∀ i, End k (V i)) :=
    LinearMap.pi (fun i => (Algebra.lsmul k k (V i)).toLinearMap)
  have hφ_surj : Function.Surjective φ := by
    intro f
    obtain ⟨a, ha⟩ := hsurj f
    exact ⟨a, funext fun i => congr_fun ha i⟩
  have h1 : finrank k (∀ i, End k (V i)) ≤ finrank k A := by
    calc finrank k (∀ i, End k (V i))
        = finrank k (LinearMap.range φ) := by
          rw [φ.range_eq_top.mpr hφ_surj, finrank_top]
      _ ≤ finrank k A := LinearMap.finrank_range_le φ
  calc ∑ i : ι, (finrank k (V i)) ^ 2
      = ∑ i : ι, finrank k (End k (V i)) := by
        congr 1; ext i
        rw [sq, ← finrank_linearMap (R := k) (S := k) (M := V i) (N := V i)]
    _ = finrank k (∀ i, End k (V i)) := (finrank_pi_fintype (R := k)).symm
    _ ≤ finrank k A := h1

end RepresentationTheory.RingTheory.SimpleModuleDimensionBound
