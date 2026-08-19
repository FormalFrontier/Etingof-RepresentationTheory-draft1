/-
Copyright (c) 2026 mathlib-initiative. All rights reserved.
Released under Apache 2.0 license as described in the file LICENCE.
Authors: Kim Morrison
-/

import Mathlib.RingTheory.Jacobson.Ideal
import RepresentationTheory.Alignment.Attribute

/-! # Two-sidedness of the Jacobson radical -/

namespace RepresentationTheory.RingTheory.JacobsonRadical.TwoSided

/-- Left and right multiplication preserve membership in the Jacobson radical. -/
@[source_ref "Chapter3/Proposition3.5.2" (role := primary)]
theorem mul_mem_jacobson (A : Type*) [Ring A]
    (a r : A) (ha : a ∈ Ideal.jacobson (⊥ : Ideal A)) :
    r * a ∈ Ideal.jacobson (⊥ : Ideal A) ∧ a * r ∈ Ideal.jacobson (⊥ : Ideal A) :=
  ⟨Ideal.mul_mem_left _ r ha, Ideal.mul_mem_right r _ ha⟩

/-- The Jacobson radical of a ring is a two-sided ideal. -/
@[source_ref "Chapter3/Proposition3.5.2" (role := primary),
  source_ref "Chapter3/Proposition3.5.3" (role := supporting)]
theorem jacobson_isTwoSided (A : Type*) [Ring A] :
    (Ideal.jacobson (⊥ : Ideal A)).IsTwoSided :=
  inferInstance

end RepresentationTheory.RingTheory.JacobsonRadical.TwoSided
