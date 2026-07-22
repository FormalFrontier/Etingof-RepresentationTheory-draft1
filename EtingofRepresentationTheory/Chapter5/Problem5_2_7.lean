import Mathlib
import EtingofRepresentationTheory.Chapter5.Remark5_2_8
import EtingofRepresentationTheory.Chapter4.Discussion_4_4

/-!
# Problem 5.2.7(b): an irreducible representation of dimension `> 1` vanishes somewhere

> **Problem 5.2.7(b).** Show that if `V` is an irreducible complex representation of a
> finite group `G` of dimension `> 1`, then there exists `g ∈ G` such that `χ_V(g) = 0`.
>
> Hint: Assume the contrary. Use orthonormality of characters to show that the
> arithmetic mean of the numbers `|χ_V(g)|²` for `g ≠ 1` is `< 1`. Deduce that their
> product `β` satisfies `0 < β < 1`. Show that all conjugates of `β` satisfy the same
> inequalities and derive a contradiction.

This file supplies the two pieces the book's argument still needs on top of the
Galois-conjugate rationality core already formalized in
`EtingofRepresentationTheory.Chapter5.Remark5_2_8`:

1. `beta_lt_one` — the `0 < β < 1` bound. This is the *only* step where irreducibility
   and `dim V > 1` enter. Writing `β = ∏_{g ≠ 1} |χ_V(g)|²`, the first orthogonality
   relation (`FDRep.char_orthonormal`) gives `∑_g |χ_V(g)|² = |G|`, hence
   `∑_{g ≠ 1} |χ_V(g)|² = |G| - (dim V)²`. Since `dim V > 1` this sum is `< |G| - 1`, the
   number of factors, so the arithmetic mean of the `|χ_V(g)|²` is `< 1`; AM-GM
   (`Real.geom_mean_le_arith_mean`) then forces the product `β < 1`, while positivity of
   each factor (under the contradiction hypothesis `χ_V(g) ≠ 0`) gives `0 < β`.

2. `exists_character_eq_zero` — the honest top-level conclusion `∃ g, χ_V(g) = 0`.
   Assuming the contrary, `β = ∏_{g ≠ 1} χ_V(g)·χ_V(g⁻¹)` is a rational
   (`Etingof.Remark5_2_8.character_prod_rat`) algebraic integer, and step 1 gives
   `0 < β < 1`; `Etingof.Remark5_2_8.beta_rat_not_mem_Ioo` derives `False`.

Part (a) of Problem 5.2.7 (existence of the finite Galois extension `K`) is a separate,
larger gap tracked elsewhere and is not addressed here.
-/

namespace Etingof.Problem5_2_7

open Finset CategoryTheory

variable {G : Type} [Group G] [Fintype G] [DecidableEq G]

/-- Each character factor is the squared modulus: `χ_V(g)·χ_V(g⁻¹) = |χ_V(g)|²`, using
`χ_V(g⁻¹) = conj χ_V(g)` (`Etingof.char_inv_eq_conj`) and `z·conj z = |z|²`. -/
private theorem char_mul_inv_eq_normSq (V : FDRep ℂ G) (g : G) :
    V.character g * V.character g⁻¹ = ((Complex.normSq (V.character g) : ℝ) : ℂ) := by
  rw [Etingof.char_inv_eq_conj V g, Complex.mul_conj]

/-- **Orthonormality sum.** For an irreducible complex representation `V` of a finite
group `G`, `∑_{g} χ_V(g)·χ_V(g⁻¹) = |G|`. This is the first orthogonality relation
`FDRep.char_orthonormal V V` (the `V ≅ V` case), cleared of its `⅟|G|` normalization. -/
theorem sum_char_mul_inv_eq_card (V : FDRep ℂ G) [Simple V]
    [Invertible (Fintype.card G : ℂ)] :
    ∑ g : G, V.character g * V.character g⁻¹ = (Fintype.card G : ℂ) := by
  have horth := FDRep.char_orthonormal V V
  rw [if_pos ⟨Iso.refl V⟩, smul_eq_mul] at horth
  -- `⅟|G| * S = 1`, so multiplying by `|G|` gives `S = |G|`.
  have h2 : (Fintype.card G : ℂ) * (⅟(Fintype.card G : ℂ) *
      ∑ g : G, V.character g * V.character g⁻¹) = (Fintype.card G : ℂ) * 1 := by rw [horth]
  rwa [← mul_assoc, mul_invOf_self, one_mul, mul_one] at h2

/-- **The `0 < β < 1` bound (Problem 5.2.7(b), main argument).** Let `V` be an
irreducible complex representation of a finite group `G` with `dim V > 1`, and suppose
`χ_V(g) ≠ 0` for every `g` (the hint's contradiction hypothesis). Then the product
`β = ∏_{g ≠ 1} |χ_V(g)|²` satisfies `0 < β < 1`.

Here `β` is the real product of squared moduli; it maps to
`∏_{g ≠ 1} χ_V(g)·χ_V(g⁻¹)` under `ℝ → ℂ` via `char_mul_inv_eq_normSq`. -/
theorem beta_lt_one (V : FDRep ℂ G) [Simple V] (h : 1 < Module.finrank ℂ V)
    (hne : ∀ g : G, V.character g ≠ 0) :
    0 < ∏ g ∈ univ.filter (· ≠ 1), Complex.normSq (V.character g) ∧
      ∏ g ∈ univ.filter (· ≠ 1), Complex.normSq (V.character g) < 1 := by
  haveI : Nonempty G := ⟨1⟩
  haveI : Invertible (Fintype.card G : ℂ) :=
    invertibleOfNonzero (by exact_mod_cast Fintype.card_ne_zero (α := G))
  set s : Finset G := univ.filter (· ≠ 1) with hs_def
  have hs_erase : s = univ.erase 1 := Finset.filter_ne' univ 1
  -- `dim V ≥ 2`, as a real number.
  have hfrn : 2 ≤ Module.finrank ℂ V := h
  have hfr : (2 : ℝ) ≤ (Module.finrank ℂ V : ℝ) := by exact_mod_cast hfrn
  -- `∑_{g} |χ_V(g)|² = |G|`, as a real identity.
  have hsumreal : ∑ g : G, Complex.normSq (V.character g) = (Fintype.card G : ℝ) := by
    have hC : (↑(∑ g : G, Complex.normSq (V.character g)) : ℂ) = (Fintype.card G : ℂ) := by
      rw [Complex.ofReal_sum]
      rw [Finset.sum_congr rfl (fun g _ => (char_mul_inv_eq_normSq V g).symm)]
      exact sum_char_mul_inv_eq_card V
    exact_mod_cast hC
  -- `|χ_V(1)|² = (dim V)²`.
  have h1 : Complex.normSq (V.character (1 : G)) = (Module.finrank ℂ V : ℝ) ^ 2 := by
    rw [FDRep.char_one, Complex.normSq_natCast]; ring
  -- `∑_{g ≠ 1} |χ_V(g)|² = |G| - (dim V)²`.
  have hSs : ∑ g ∈ s, Complex.normSq (V.character g)
      = (Fintype.card G : ℝ) - (Module.finrank ℂ V : ℝ) ^ 2 := by
    have hsplit := Finset.add_sum_erase univ
      (fun g => Complex.normSq (V.character g)) (Finset.mem_univ (1 : G))
    rw [hs_erase]
    have hrw : ∑ g ∈ univ.erase 1, Complex.normSq (V.character g)
        = (∑ g : G, Complex.normSq (V.character g)) - Complex.normSq (V.character 1) :=
      eq_sub_of_add_eq (by rw [add_comm]; exact hsplit)
    rw [hrw, hsumreal, h1]
  -- `|G| ≥ 4` (since `∑ |χ|² = |G| ≥ |χ_V(1)|² = (dim V)² ≥ 4`).
  have hcardge : (4 : ℝ) ≤ (Fintype.card G : ℝ) := by
    rw [← hsumreal]
    calc (4 : ℝ) ≤ (Module.finrank ℂ V : ℝ) ^ 2 := by nlinarith [hfr]
      _ = Complex.normSq (V.character 1) := h1.symm
      _ ≤ ∑ g : G, Complex.normSq (V.character g) :=
          Finset.single_le_sum (fun g _ => Complex.normSq_nonneg _) (Finset.mem_univ 1)
  -- `s.card = |G| - 1 > 0`.
  have hcard_real : (s.card : ℝ) = (Fintype.card G : ℝ) - 1 := by
    rw [hs_erase, Finset.card_erase_of_mem (Finset.mem_univ 1), Finset.card_univ,
      Nat.cast_sub Fintype.card_pos, Nat.cast_one]
  have hcardpos : 0 < s.card := by
    have : (0 : ℝ) < (s.card : ℝ) := by rw [hcard_real]; linarith
    exact_mod_cast this
  -- Each factor is positive, hence so is the product.
  have hβpos : 0 < ∏ g ∈ s, Complex.normSq (V.character g) :=
    Finset.prod_pos (fun g _ => Complex.normSq_pos.mpr (hne g))
  refine ⟨hβpos, ?_⟩
  -- The sum over `s` is strictly below the number of terms.
  have hlt : ∑ g ∈ s, Complex.normSq (V.character g) < (s.card : ℝ) := by
    rw [hSs, hcard_real]; nlinarith [hfr]
  -- AM-GM with all weights `1`.
  have hgm := Real.geom_mean_le_arith_mean s (fun _ => (1 : ℝ))
    (fun g => Complex.normSq (V.character g)) (fun i _ => zero_le_one)
    (by rw [Finset.sum_const, nsmul_eq_mul, mul_one]; exact_mod_cast hcardpos)
    (fun i _ => Complex.normSq_nonneg _)
  simp only [Real.rpow_one, Finset.sum_const, nsmul_eq_mul, mul_one, one_mul] at hgm
  -- `β ^ (1/card) ≤ (∑)/card < 1`, hence `β < 1`.
  have hrhs : (∑ g ∈ s, Complex.normSq (V.character g)) / (s.card : ℝ) < 1 := by
    rw [div_lt_one (by exact_mod_cast hcardpos)]; exact hlt
  have hβt : (∏ g ∈ s, Complex.normSq (V.character g)) ^ ((s.card : ℝ)⁻¹) < 1 :=
    lt_of_le_of_lt hgm hrhs
  by_contra hge
  push_neg at hge
  have : 1 ≤ (∏ g ∈ s, Complex.normSq (V.character g)) ^ ((s.card : ℝ)⁻¹) :=
    Real.one_le_rpow hge (by positivity)
  linarith

/-- **Problem 5.2.7(b).** If `V` is an irreducible complex representation of a finite
group `G` with `dim V > 1`, then `χ_V(g) = 0` for some `g ∈ G`.

Assume not: `χ_V(g) ≠ 0` for all `g`. Then `β = ∏_{g ≠ 1} χ_V(g)·χ_V(g⁻¹)` is rational
(`Etingof.Remark5_2_8.character_prod_rat`) with value `q : ℚ`, and its real form
`∏_{g ≠ 1} |χ_V(g)|²` satisfies `0 < β < 1` (`beta_lt_one`), so `0 < q < 1`. As `β` is
also an algebraic integer, `Etingof.Remark5_2_8.beta_rat_not_mem_Ioo` yields `False`. -/
theorem exists_character_eq_zero (V : FDRep ℂ G) [Simple V]
    (h : 1 < Module.finrank ℂ V) : ∃ g : G, V.character g = 0 := by
  by_contra hcon
  push_neg at hcon
  obtain ⟨hβpos, hβlt⟩ := beta_lt_one V h hcon
  set s : Finset G := univ.filter (· ≠ 1) with hs_def
  obtain ⟨q, hq⟩ := Etingof.Remark5_2_8.character_prod_rat V
  rw [← hs_def] at hq
  -- `algebraMap ℚ ℂ q = ↑q` as a real, matched against the real product `β`.
  have hqcast : algebraMap ℚ ℂ q = ((q : ℝ) : ℂ) := by
    rw [Complex.ofReal_ratCast]; simp
  have hβeq : (q : ℝ) = ∏ g ∈ s, Complex.normSq (V.character g) := by
    have hC : ((q : ℝ) : ℂ) = ∏ g ∈ s, ((Complex.normSq (V.character g) : ℝ) : ℂ) := by
      rw [← hqcast, hq]
      exact Finset.prod_congr rfl (fun g _ => char_mul_inv_eq_normSq V g)
    rw [← Complex.ofReal_prod] at hC
    exact_mod_cast hC
  have hq0 : 0 < q := by
    have : (0 : ℝ) < (q : ℝ) := by rw [hβeq]; exact hβpos
    exact_mod_cast this
  have hq1 : q < 1 := by
    have : (q : ℝ) < 1 := by rw [hβeq]; exact hβlt
    exact_mod_cast this
  exact Etingof.Remark5_2_8.beta_rat_not_mem_Ioo V (hs_def ▸ hq) hq0 hq1

end Etingof.Problem5_2_7
