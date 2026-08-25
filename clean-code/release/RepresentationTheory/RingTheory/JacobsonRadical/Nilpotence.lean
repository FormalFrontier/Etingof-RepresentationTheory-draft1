/-
Copyright (c) 2026 mathlib-initiative. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

import Mathlib.RingTheory.Artinian.Ring
import Mathlib.RingTheory.Nilpotent.Basic
import Mathlib.LinearAlgebra.FiniteDimensional.Defs
import RepresentationTheory.Alignment.Attribute

/-! # Nilpotence and the Jacobson radical -/

namespace RepresentationTheory.RingTheory.JacobsonRadical.Nilpotence

/-- A nilpotent ideal is contained in the Jacobson radical. -/
@[source_ref "Chapter3/Proposition3.5.3" (role := primary)]
theorem nilpotent_le_jacobson (A : Type*) [Ring A]
    (I : Ideal A) (hI : IsNilpotent I) :
    I ≤ Ideal.jacobson ⊥ := by
  intro x hx
  rw [Ideal.mem_jacobson_iff]
  intro y
  have hyx : y * x ∈ I := I.mul_mem_left y hx
  obtain ⟨n, hn⟩ := hI
  have hnil : IsNilpotent (y * x) := ⟨n, by
    have h := Ideal.pow_mem_pow hyx n
    rw [hn] at h
    exact (Submodule.mem_bot A).mp h⟩
  obtain ⟨u, hu_eq⟩ := hnil.isUnit_one_add
  refine ⟨↑u⁻¹, ?_⟩
  simp only [Submodule.mem_bot]
  have : ↑u⁻¹ * y * x + ↑u⁻¹ - 1 = ↑u⁻¹ * (y * x + 1) - 1 := by
    rw [mul_add, mul_one, mul_assoc]
  rw [this, add_comm (y * x) 1, ← hu_eq, u.inv_mul, sub_self]

/-- The Jacobson radical of a finite-dimensional algebra is nilpotent. -/
@[source_ref "Chapter3/Proposition3.5.3" (role := primary)]
theorem jacobson_isNilpotent_of_finiteDimensional (k : Type*) (A : Type*)
    [Field k] [Ring A] [Algebra k A] [FiniteDimensional k A] :
    IsNilpotent (Ideal.jacobson (⊥ : Ideal A)) := by
  haveI : IsArtinianRing A := isArtinian_of_tower k inferInstance
  exact IsArtinianRing.isNilpotent_jacobson_bot

end RepresentationTheory.RingTheory.JacobsonRadical.Nilpotence
