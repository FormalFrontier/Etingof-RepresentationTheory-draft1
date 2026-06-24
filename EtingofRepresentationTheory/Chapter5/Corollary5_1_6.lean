import Mathlib
import EtingofRepresentationTheory.Chapter5.Theorem5_1_5

/-!
# Corollary 5.1.6: Real Representations and Involutions

If all irreducible representations of G are defined over the reals (i.e., all
Frobenius-Schur indicators equal 1), then the number of involutions in G
equals Σ dim(Vᵢ), where the sum runs over all irreducible representations.

## Mathlib correspondence

Follows from Theorem 5.1.5 by setting all FS indicators to 1.
-/

open FDRep CategoryTheory

universe u

variable {k G : Type u} [Field k] [Group G] [Fintype G]

/-- If all irreducible representations of G are real (Frobenius-Schur indicator
= 1), then the number of involutions (elements with `g² = 1`) equals the sum of
their dimensions. This specializes Theorem 5.1.5, whose right-hand side
`∑ᵢ dim(Vᵢ) · FS(Vᵢ)` collapses to `∑ᵢ dim(Vᵢ)` when every `FS(Vᵢ) = 1`.
(Etingof Corollary 5.1.6) -/
theorem Etingof.Corollary5_1_6
    [DecidableEq G] [IsAlgClosed k] [NeZero (Nat.card G : k)]
    [Invertible (Fintype.card G : k)]
    (D : IrrepDecomp k G)
    (V : Fin D.n → FDRep k G)
    (hV : ∀ i, Simple (V i))
    (hinj : ∀ i j, Nonempty ((V i) ≅ (V j)) → i = j)
    -- Hypothesis: all irreducible representations are of real type (FS indicator = 1)
    (h_all_real : ∀ i, (V i).frobeniusSchurIndicator = 1) :
    (Finset.univ.filter (fun g : G => g * g = 1)).card =
    ∑ i : Fin D.n, (Module.finrank k (V i) : k) := by
  rw [Etingof.Theorem5_1_5 D V hV hinj]
  refine Finset.sum_congr rfl (fun i _ => ?_)
  rw [h_all_real i, mul_one]
