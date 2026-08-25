import Mathlib

/-!
# Theorem 4.6.3: Unitary Representations are Completely Reducible

A finite dimensional unitary representation V of any group G is completely reducible.

Proof: If W ⊆ V is a subrepresentation, then W^⊥ (orthogonal complement with respect
to the G-invariant inner product) is also a subrepresentation, since G preserves the
inner product. Therefore V = W ⊕ W^⊥ as representations.

Note: this applies to any group G, not just finite groups. The key hypothesis is the
existence of a G-invariant inner product, not finiteness of G.

## Mathlib correspondence

Mathlib has `Submodule.IsCompl` and orthogonal complement theory in inner product spaces.
This combines representation theory with inner product space structure.
-/

/-- A unitary representation of any group is completely reducible (semisimple):
every `ρ`-invariant subspace `W` has a `ρ`-invariant complement, namely its
orthogonal complement `Wᗮ` under the `G`-invariant inner product.
(Etingof Theorem 4.6.3) -/
theorem Etingof.Theorem4_6_3
    (G : Type*) [Group G]
    (V : Type*) [NormedAddCommGroup V] [InnerProductSpace ℂ V] [FiniteDimensional ℂ V]
    (ρ : Representation ℂ G V)
    (hunit : ∀ g : G, ∀ v w : V,
      @inner ℂ V _ (ρ g v) (ρ g w) = @inner ℂ V _ v w) :
    ∀ W : Submodule ℂ V, (∀ g : G, ∀ w ∈ W, ρ g w ∈ W) →
      ∃ W' : Submodule ℂ V, (∀ g : G, ∀ w ∈ W', ρ g w ∈ W') ∧ IsCompl W W' := by
  intro W hW
  refine ⟨Wᗮ, ?_, W.isCompl_orthogonal⟩
  -- Wᗮ is G-invariant: if w ⊥ W then ρ g w ⊥ W, using ⟪u, ρ g w⟫ = ⟪ρ g⁻¹ u, w⟫
  -- and the fact that ρ g⁻¹ u ∈ W (since W is invariant) so this inner product vanishes.
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
