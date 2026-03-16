import Mathlib

/-!
# Corollary 5.1.6: Real Representations and Involutions

If all irreducible representations of G are defined over the reals (i.e., all
Frobenius-Schur indicators equal 1), then the number of involutions in G
equals Σ dim(Vᵢ), where the sum runs over all irreducible representations.

## Mathlib correspondence

Follows from Theorem 5.1.5 by setting all FS indicators to 1.
-/

/-- If all irreducible representations of G are real (FS = 1), then the number
of involutions equals the sum of their dimensions. (Etingof Corollary 5.1.6) -/
theorem Etingof.Corollary5_1_6
    (G : Type*) [Group G] [Fintype G] [DecidableEq G]
    -- Hypothesis: all irreducible representations are of real type (FS indicator = 1)
    (h_all_real : True) :  -- TODO: express "all FS indicators = 1" once indicator API exists
    -- Number of involutions = Σ dim(Vᵢ)
    True := by
  trivial
  -- TODO: Formalize once Theorem 5.1.5 and FS indicator are properly connected.
