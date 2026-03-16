import Mathlib

/-!
# Theorem 5.1.5: Frobenius-Schur Theorem (Involution Count)

The number of involutions (elements g with g² = 1) in a finite group G equals:
  Σ_V dim(V) · FS(V)
where the sum is over all irreducible representations V, and FS(V) is the
Frobenius-Schur indicator.

The proof uses the decomposition of the symmetric and exterior squares:
  χ_V(g²) = χ_{S²V}(g) - χ_{Λ²V}(g)

## Mathlib correspondence

Uses symmetric and exterior powers, character theory, and the Frobenius-Schur indicator.
-/

/-- The number of involutions in G equals Σ_V dim(V) · FS(V), where the sum ranges over
irreducible representations. (Etingof Theorem 5.1.5) -/
theorem Etingof.Theorem5_1_5
    (G : Type*) [Group G] [Fintype G] [DecidableEq G] :
    -- |{g ∈ G | g² = 1}| = Σ_V dim(V) · FS(V)
    -- over all irreducible representations V
    Finset.card (Finset.univ.filter (fun g : G => g * g = 1)) =
    sorry := by
  sorry
