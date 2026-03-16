import Mathlib
import EtingofRepresentationTheory.Infrastructure.IrreducibleEnumeration
import EtingofRepresentationTheory.Infrastructure.RegularCharacter

/-!
# Theorem 5.1.5: Frobenius-Schur Theorem (Involution Count)

The number of involutions (elements g with g² = 1) in a finite group G equals:
  Σ_V dim(V) · FS(V)
where the sum is over all irreducible representations V, and FS(V) is the
Frobenius-Schur indicator.

## Mathlib correspondence

Uses character theory and the Frobenius-Schur indicator.
-/

open FDRep CategoryTheory

universe u

variable {k G : Type u} [Field k] [Group G] [Fintype G]

/-- Frobenius-Schur indicator of an FDRep object, computed as
(1/|G|) Σ_{g∈G} χ_V(g²). -/
noncomputable def FDRep.frobeniusSchurIndicator
    [Invertible (Fintype.card G : k)]
    (V : FDRep k G) : k :=
  ⅟(Fintype.card G : k) • ∑ g : G, V.character (g * g)

/-- The sum `∑_i d_i · χ_{V_i}(h)` over all irreducible representations equals the
regular character: `|G|` if `h = 1` and `0` otherwise. -/
private lemma sum_dim_char_eq_regularChar
    [DecidableEq G] [IsAlgClosed k] [NeZero (Nat.card G : k)]
    (D : IrrepDecomp k G)
    (V : Fin D.n → FDRep k G)
    (hV : ∀ i, Simple (V i))
    (hinj : ∀ i j, Nonempty ((V i) ≅ (V j)) → i = j)
    (hsurj : ∀ (W : FDRep k G), Simple W → ∃ i, Nonempty (W ≅ V i))
    (h : G) :
    ∑ i, (D.d i : k) * (V i).character h =
      if h = 1 then (Fintype.card G : k) else 0 := by
  split
  case isTrue heq =>
    subst heq
    simp only [FDRep.char_one]
    have hd := D.d_eq_finrank V hV hinj hsurj
    have : ∀ i, (Module.finrank k (V i) : k) = (D.d i : k) := by
      intro i; rw [← hd i]
    simp_rw [this]
    rw [← D.sum_sq_eq_card]; push_cast; congr 1; ext i; ring
  case isFalse hne =>
    exact sum_dim_character_eq_zero D V hV hinj hsurj h hne

/-- The number of involutions in G equals Σ_i dim(V_i) · FS(V_i), where the sum ranges over
irreducible representations indexed by a Wedderburn-Artin decomposition.
(Etingof Theorem 5.1.5) -/
theorem Etingof.Theorem5_1_5
    [DecidableEq G] [IsAlgClosed k] [NeZero (Nat.card G : k)]
    [Invertible (Fintype.card G : k)]
    (D : IrrepDecomp k G)
    (V : Fin D.n → FDRep k G)
    (hV : ∀ i, Simple (V i))
    (hinj : ∀ i j, Nonempty ((V i) ≅ (V j)) → i = j)
    (hsurj : ∀ (W : FDRep k G), Simple W → ∃ i, Nonempty (W ≅ V i)) :
    (Finset.univ.filter (fun g : G => g * g = 1)).card =
    ∑ i : Fin D.n, D.d i * (V i).frobeniusSchurIndicator := by
  simp only [FDRep.frobeniusSchurIndicator]
  -- Factor out ⅟|G| and rearrange sums
  simp_rw [mul_smul_comm]
  rw [← Finset.smul_sum]
  simp_rw [Finset.mul_sum]
  rw [Finset.sum_comm]
  -- Apply the regular character identity
  simp_rw [sum_dim_char_eq_regularChar D V hV hinj hsurj]
  -- Simplify: ⅟|G| • ∑_g (if g²=1 then |G| else 0) = #{involutions}
  rw [← Finset.sum_filter, Finset.sum_const]
  simp only [nsmul_eq_mul, smul_eq_mul]
  -- Goal: ↑card = ⅟↑|G| * ↑card * ↑|G|
  rw [invOf_eq_inv]
  have hne : (Fintype.card G : k) ≠ 0 := Invertible.ne_zero _
  field_simp [hne]
