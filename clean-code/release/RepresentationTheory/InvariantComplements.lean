/-
Copyright (c) 2026 mathlib-initiative. All rights reserved.
Released under Apache 2.0 license as described in the file LICENCE.
Authors: Kim Morrison
-/

import Mathlib
import RepresentationTheory.Alignment.Attribute

/-! # Invariant complements -/

namespace RepresentationTheory.InvariantComplements

/-- A finite-dimensional complex representation preserving the inner product admits an invariant
complementary submodule to every invariant submodule. -/
@[source_ref "Chapter4/Theorem4.6.3" (role := supporting)]
theorem exists_invariant_isCompl_of_preserves_inner
    (G : Type*) [Group G]
    (V : Type*) [NormedAddCommGroup V] [InnerProductSpace ℂ V] [FiniteDimensional ℂ V]
    (ρ : Representation ℂ G V)
    (hunit : ∀ g : G, ∀ v w : V,
      @inner ℂ V _ (ρ g v) (ρ g w) = @inner ℂ V _ v w) :
    ∀ W : Submodule ℂ V, (∀ g : G, ∀ w ∈ W, ρ g w ∈ W) →
      ∃ W' : Submodule ℂ V, (∀ g : G, ∀ w ∈ W', ρ g w ∈ W') ∧ IsCompl W W' := by
  intro W hW
  refine ⟨Wᗮ, ?_, W.isCompl_orthogonal⟩
  intro g w hw
  rw [Submodule.mem_orthogonal] at hw ⊢
  intro u hu
  have hgu : ρ g⁻¹ u ∈ W := hW g⁻¹ u hu
  have h1 : ρ g (ρ g⁻¹ u) = u := by
    rw [← Module.End.mul_apply, ← map_mul, mul_inv_cancel, map_one, Module.End.one_apply]
  calc @inner ℂ V _ u (ρ g w)
      = @inner ℂ V _ (ρ g (ρ g⁻¹ u)) (ρ g w) := by rw [h1]
    _ = @inner ℂ V _ (ρ g⁻¹ u) w := hunit g _ _
    _ = 0 := hw _ hgu

end RepresentationTheory.InvariantComplements
