import Mathlib
import EtingofRepresentationTheory.Infrastructure.IrreducibleEnumeration

/-!
# Regular Representation Character Identity

For a finite group G over ℂ (or any algebraically closed field of good characteristic),
the character of the regular representation satisfies:

* `χ_reg(1) = |G|`
* `χ_reg(g) = 0` for `g ≠ 1`

These are computed as traces of the left-multiplication action on `G →₀ k`.

## References

- Etingof, *Introduction to Representation Theory*, Section 4.4
-/

open Representation CategoryTheory

universe u

variable {k G : Type u} [Field k] [Group G]

/-! ### Character of the regular representation -/

/-- The character of the regular representation at the identity is `|G|`. -/
theorem regularCharacter_one [Fintype G] :
    LinearMap.trace k (G →₀ k) ((Representation.ofMulAction k G G) 1) =
      (Fintype.card G : k) := by
  rw [map_one, LinearMap.trace_one]
  simp

/-- The character of the regular representation at `g ≠ 1` is `0`. -/
theorem regularCharacter_ne_one [Finite G] (g : G) (hg : g ≠ 1) :
    LinearMap.trace k (G →₀ k) ((Representation.ofMulAction k G G) g) = 0 := by
  classical
  cases nonempty_fintype G
  have key : ∀ h : G, ofMulAction k G G g (Finsupp.single h 1) h = 0 := by
    intro h
    rw [ofMulAction_apply, Finsupp.single_apply, if_neg]
    intro heq
    rw [smul_eq_mul] at heq
    -- heq : h = g⁻¹ * h, need g = 1
    exact hg (inv_eq_one.mp (mul_right_cancel (show g⁻¹ * h = 1 * h by rw [one_mul, ← heq])))
  rw [LinearMap.trace_eq_matrix_trace k (Finsupp.basisSingleOne (ι := G) (R := k))]
  simp only [Matrix.trace, Matrix.diag_apply, LinearMap.toMatrix_apply]
  apply Finset.sum_eq_zero
  intro h _
  convert key h using 1

open scoped Classical in
/-- Combined form: `χ_reg(g)` equals `|G|` if `g = 1` and `0` otherwise. -/
theorem regularCharacter_eq [Fintype G] (g : G) :
    LinearMap.trace k (G →₀ k) ((Representation.ofMulAction k G G) g) =
      if g = 1 then (Fintype.card G : k) else 0 := by
  split
  · subst_vars; exact regularCharacter_one
  · exact regularCharacter_ne_one g ‹_›

/-! ### Sum-of-dimensions character identity

For `g ≠ 1`, the decomposition of the regular representation into irreducibles gives:
`∑_i dim(V_i) · χ_{V_i}(g) = 0`

This requires the full FDRep connection from `IrrepDecomp.n_eq_card_simples`,
which is not yet available (see issue #643). -/

/-- For `g ≠ 1`, the sum `∑_i dim(V_i) · χ_{V_i}(g) = 0` over all irreducible
representations. This follows from the decomposition of the regular representation
into irreducibles combined with `regularCharacter_ne_one`.

**Blocked on**: `IrrepDecomp.n_eq_card_simples` (issue #643). -/
theorem sum_dim_character_eq_zero [Fintype G] [IsAlgClosed k] [NeZero (Nat.card G : k)]
    (D : IrrepDecomp k G) (V : Fin D.n → FDRep k G)
    (hV : ∀ i, Simple (V i))
    (hinj : ∀ i j, Nonempty ((V i) ≅ (V j)) → i = j)
    (hsurj : ∀ (W : FDRep k G), Simple W → ∃ i, Nonempty (W ≅ V i))
    (g : G) (hg : g ≠ 1) :
    ∑ i, (D.d i : k) * (V i).character g = 0 := by
  sorry
