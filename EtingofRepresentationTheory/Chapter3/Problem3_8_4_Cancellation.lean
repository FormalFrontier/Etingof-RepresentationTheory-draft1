import Mathlib
import EtingofRepresentationTheory.Chapter3.Problem3_8_3

/-!
# Problem 3.8.4 prerequisite: Krull-Schmidt cancellation `Vⁿ ≅ Wⁿ ⟹ V ≅ W`

Problem 3.8.4 reduces the scalar-extension isomorphism problem to the following purely
module-theoretic cancellation statement over an arbitrary field: if two finite dimensional
`A`-modules `V`, `W` have isomorphic `n`-fold powers `Vⁿ ≅ Wⁿ` (with `n > 0`), then already
`V ≅ W`.

The proof runs through the Krull-Schmidt theorem, valid over any field by Problem 3.8.3
(`Etingof.Problem3_8_3.krull_schmidt_existence` / `krull_schmidt_uniqueness`). Decompose `V`
and `W` into indecomposables; the power `Vⁿ` then decomposes into `n` copies of each summand,
and Krull-Schmidt uniqueness identifies the multiset of indecomposable summands of `Vⁿ` with
that of `Wⁿ`. Since every multiplicity is scaled by the same `n`, the per-iso-class
multiplicities of `V` and `W` agree, which forces `V ≅ W`.

This file supplies the reusable helper `Etingof.IsIndecomposable.of_linearEquiv`
(indecomposability is an isomorphism invariant) and the main theorem `iso_pow_cancel`.
-/

namespace Etingof.Problem3_8_4

/-- Indecomposability is invariant under `A`-linear isomorphism: if `V` is indecomposable
and `V ≃ₗ[A] W`, then `W` is indecomposable. -/
theorem _root_.Etingof.IsIndecomposable.of_linearEquiv {A V W : Type*} [Ring A]
    [AddCommGroup V] [Module A V] [AddCommGroup W] [Module A W]
    (e : V ≃ₗ[A] W) (hV : Etingof.IsIndecomposable A V) :
    Etingof.IsIndecomposable A W := by
  obtain ⟨hne, hsplit⟩ := hV
  refine ⟨?_, fun W₁ W₂ hC => ?_⟩
  · obtain ⟨a, b, hab⟩ := hne
    exact ⟨e a, e b, fun h => hab (e.injective h)⟩
  -- `g` is the order isomorphism `Submodule A W ≃o Submodule A V` given by `comap e`.
  set g := (Submodule.orderIsoMapComap (e : V ≃ₗ[A] W)).symm with hg
  have hC' : IsCompl (g W₁) (g W₂) := g.isCompl_iff.mp hC
  have hbot : ∀ {U : Submodule A W}, g U = ⊥ → U = ⊥ := by
    intro U hU
    have : g U = g ⊥ := by rw [hU, OrderIso.map_bot]
    exact g.injective this
  rcases hsplit _ _ hC' with h1 | h2
  · exact Or.inl (hbot h1)
  · exact Or.inr (hbot h2)

/-- Transport an internal decomposition into indecomposables across an `A`-linear
isomorphism `e : V ≃ₗ[A] V'`: the images `(D i).map e` form an indecomposable
decomposition of `V'`. Each of the four defining properties (indecomposability, nonzero,
spanning, independence) is preserved. -/
theorem indecDecomp_map {A V V' : Type*} [Ring A]
    [AddCommGroup V] [Module A V] [AddCommGroup V'] [Module A V']
    (e : V ≃ₗ[A] V') {p : ℕ} (D : Fin p → Submodule A V)
    (hindec : ∀ i, Etingof.IsIndecomposable A (D i))
    (hne : ∀ i, D i ≠ ⊥) (hsup : iSup D = ⊤) (hind : iSupIndep D) :
    (∀ i, Etingof.IsIndecomposable A ((D i).map (e : V →ₗ[A] V'))) ∧
      (∀ i, (D i).map (e : V →ₗ[A] V') ≠ ⊥) ∧
      iSup (fun i => (D i).map (e : V →ₗ[A] V')) = ⊤ ∧
      iSupIndep (fun i => (D i).map (e : V →ₗ[A] V')) := by
  refine ⟨fun i => (hindec i).of_linearEquiv
      (Submodule.equivMapOfInjective (e : V →ₗ[A] V') e.injective (D i)), fun i => ?_, ?_, ?_⟩
  · rw [Ne, Submodule.map_eq_bot_iff]
    exact hne i
  · rw [← Submodule.map_iSup, hsup, Submodule.map_top, LinearEquiv.range]
  · exact LinearMap.iSupIndep_map (e : V →ₗ[A] V') e.injective hind

/-- **Krull-Schmidt cancellation.** For finite dimensional representations `V`, `W` of an
algebra `A` over an arbitrary field `k`, if the `n`-fold powers are isomorphic
(`Vⁿ ≅ Wⁿ`) for some `n > 0`, then `V` and `W` are isomorphic.

Proof (Problem 3.8.4 route): decompose `V` and `W` into indecomposables via Krull-Schmidt
existence over the arbitrary field `k` (Problem 3.8.3); then `Vⁿ` and `Wⁿ` decompose into
`n` copies of each summand, and Krull-Schmidt uniqueness matches the two multisets of
indecomposable summands, scaling every multiplicity by `n`. Cancelling the common factor
`n > 0` shows the per-iso-class multiplicities of `V` and `W` agree, giving `V ≅ W`. -/
theorem iso_pow_cancel (k A V W : Type*) [Field k] [Ring A] [Algebra k A]
    [AddCommGroup V] [Module k V] [Module A V] [IsScalarTower k A V]
    [AddCommGroup W] [Module k W] [Module A W] [IsScalarTower k A W]
    [FiniteDimensional k V] [FiniteDimensional k W]
    {n : ℕ} (hn : 0 < n)
    (h : Nonempty ((Fin n → V) ≃ₗ[A] (Fin n → W))) :
    Nonempty (V ≃ₗ[A] W) := by
  sorry

end Etingof.Problem3_8_4
