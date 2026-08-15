/-
Copyright (c) 2026 mathlib-initiative. All rights reserved.
Released under Apache 2.0 license as described in the file LICENCE.
Authors: mathlib-initiative
-/

import Mathlib
import RepresentationTheory.Alignment.Attribute

namespace RepresentationTheory.NumberTheory.IntegralClosure.Rat

/-- A rational number viewed in the complex numbers is integral over the integers exactly when it is an integer. -/
@[source_ref "Chapter5/Proposition5.2.5" (role := primary), source_ref "Chapter5/Discussion_proof_of_Theorem5.3.1" (role := primary)]
theorem Rat.isIntegral_complex_iff (q : ℚ) :
    IsIntegral ℤ (algebraMap ℚ ℂ q) ↔ ∃ n : ℤ, q = n := by
  rw [isIntegral_algebraMap_iff (algebraMap ℚ ℂ).injective]
  constructor
  · intro hq
    have := IsIntegrallyClosed.isIntegral_iff.mp hq
    obtain ⟨r, hr⟩ := this
    exact ⟨r, by exact_mod_cast hr.symm⟩
  · rintro ⟨n, rfl⟩
    exact isIntegral_algebraMap

end RepresentationTheory.NumberTheory.IntegralClosure.Rat
