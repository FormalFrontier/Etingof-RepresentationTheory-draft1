import Mathlib
import EtingofRepresentationTheory.Chapter4.Discussion_4_4
import EtingofRepresentationTheory.Chapter5.Lemma5_7_2
import EtingofRepresentationTheory.Infrastructure.FDRepIsotypic
import EtingofRepresentationTheory.Infrastructure.IrreducibleEnumeration

/-!
# Realizing a norm-one virtual character as an actual irreducible representation

`Etingof.Lemma5_7_2` says that if a virtual character, written as an integer combination
`Σ nᵢ χ_{Wᵢ}` over a family of pairwise non-isomorphic simples, has self inner product `1`
and positive dimension, then exactly one coefficient is `1` and the rest vanish.  In that
shape the conclusion is about the coefficients, and using it requires the caller to supply
the expansion in a complete family of irreducibles.

This file removes both obligations.  The input becomes the shape a virtual character
actually arrives in — a *difference of two honest representations* `A - B` — and the output
becomes an actual object: a simple `W : FDRep ℂ G` whose character is `χ_A - χ_B`.

## Main results

* `Etingof.exists_simple_character_eq_sub` : if `⟨χ_A - χ_B, χ_A - χ_B⟩ = 1` and
  `dim B < dim A`, there is a simple `W` with `χ_W = χ_A - χ_B`.
* `Etingof.simpleOfVirtualChar` : the representation itself, together with
  `Etingof.simpleOfVirtualChar_simple`, `Etingof.simpleOfVirtualChar_character` and
  `Etingof.finrank_simpleOfVirtualChar` (`dim W = dim A - dim B`).

## Method

The complete family that `Lemma5_7_2` needs is not the caller's problem: every finite group
has one, by `exists_simples_sum_finrank_sq_eq_card` (the column representations of the
Wedderburn-Artin decomposition).  Expanding `χ_A` and `χ_B` over it with
`Etingof.FDRep.exists_character_eq_sum` gives natural-number multiplicities `aᵢ`, `bᵢ`, so
`χ_A - χ_B = Σ (aᵢ - bᵢ) χ_{Tᵢ}` is an integer combination and `Lemma5_7_2` applies.  The
surviving index names the representation.

The inner product is stated in the `starRingEnd` form used by the Chapter 5 computations
(`Etingof.Lemma5_25_3_innerProduct`); `Etingof.char_inv_eq_conj` converts it to the
`χ(g⁻¹)` form that `Lemma5_7_2` expects.
-/

open CategoryTheory Module

namespace Etingof

variable {G : Type} [Group G] [Fintype G]

/-- **A norm-one virtual character of positive dimension is the character of a simple
representation.**  Here the virtual character is presented as a difference `χ_A - χ_B` of the
characters of two honest representations, which is how virtual characters arise in practice
(Etingof Lemma 5.7.2, object form). -/
theorem exists_simple_character_eq_sub (A B : FDRep ℂ G)
    (hnorm : (Fintype.card G : ℂ)⁻¹ •
      ∑ g : G, (A.character g - B.character g) *
        (starRingEnd ℂ) (A.character g - B.character g) = 1)
    (hpos : finrank ℂ B < finrank ℂ A) :
    ∃ W : FDRep ℂ G, Simple W ∧
      ∀ g : G, W.character g = A.character g - B.character g := by
  classical
  haveI : Invertible (Fintype.card G : ℂ) :=
    invertibleOfNonzero (Nat.cast_ne_zero.mpr Fintype.card_ne_zero)
  haveI : NeZero (Nat.card G : ℂ) :=
    ⟨Nat.cast_ne_zero.mpr (Nat.card_pos (α := G)).ne'⟩
  -- A complete family of pairwise non-isomorphic irreducibles exists for any finite group.
  obtain ⟨N, T, hT, hinj, hcomplete, -⟩ := exists_simples_sum_finrank_sq_eq_card ℂ G
  haveI : ∀ i, Simple (T i) := hT
  -- Expand both characters over it, and subtract.
  obtain ⟨a, ha⟩ := Etingof.FDRep.exists_character_eq_sum T hcomplete A
  obtain ⟨b, hb⟩ := Etingof.FDRep.exists_character_eq_sum T hcomplete B
  obtain ⟨m, hm⟩ : ∃ m : Fin N → ℤ, ∀ g : G,
      ∑ i, (m i : ℂ) * (T i).character g = A.character g - B.character g := by
    refine ⟨fun i => (a i : ℤ) - (b i : ℤ), fun g => ?_⟩
    rw [ha g, hb g, ← Finset.sum_sub_distrib]
    exact Finset.sum_congr rfl fun i _ => by push_cast; ring
  -- The hypotheses of `Lemma5_7_2`, transported along `hm`.
  have hnorm' : ⅟(Fintype.card G : ℂ) •
      ∑ g : G, (∑ i, (m i : ℂ) * (T i).character g) *
               (∑ j, (m j : ℂ) * (T j).character g⁻¹) = 1 := by
    rw [invOf_eq_inv]
    rw [← hnorm]
    refine congrArg _ (Finset.sum_congr rfl fun g _ => ?_)
    rw [hm g, hm g⁻¹, map_sub, ← Etingof.char_inv_eq_conj, ← Etingof.char_inv_eq_conj]
  have hdim : ∑ i, m i * (finrank ℂ (T i) : ℤ)
      = (finrank ℂ A : ℤ) - (finrank ℂ B : ℤ) := by
    have hC : ((∑ i, m i * (finrank ℂ (T i) : ℤ) : ℤ) : ℂ)
        = (((finrank ℂ A : ℤ) - (finrank ℂ B : ℤ) : ℤ) : ℂ) := by
      have h1 := hm 1
      simp only [FDRep.char_one] at h1
      push_cast
      exact h1
    exact_mod_cast hC
  have hpos' : 0 < ∑ i, m i * (finrank ℂ (T i) : ℤ) := by
    rw [hdim]; omega
  -- Exactly one coefficient survives, and it is `1`.
  obtain ⟨i₀, hi₀, hrest⟩ := Etingof.Lemma5_7_2 T hinj m hnorm' hpos'
  refine ⟨T i₀, hT i₀, fun g => ?_⟩
  rw [← hm g, Finset.sum_eq_single i₀ (fun i _ hi => by rw [hrest i hi]; simp)
    (fun h => absurd (Finset.mem_univ i₀) h), hi₀]
  simp

section Choice

variable (A B : FDRep ℂ G)
  (hnorm : (Fintype.card G : ℂ)⁻¹ •
    ∑ g : G, (A.character g - B.character g) *
      (starRingEnd ℂ) (A.character g - B.character g) = 1)
  (hpos : finrank ℂ B < finrank ℂ A)

/-- The simple representation whose character is the virtual character `χ_A - χ_B`, when the
latter has self inner product `1` and positive dimension.  This is a genuine object, not a
placeholder: it is one of the column representations of the Wedderburn-Artin decomposition
of `ℂ[G]`, selected by `exists_simple_character_eq_sub`. -/
noncomputable def simpleOfVirtualChar : FDRep ℂ G :=
  (exists_simple_character_eq_sub A B hnorm hpos).choose

instance simpleOfVirtualChar_simple : Simple (simpleOfVirtualChar A B hnorm hpos) :=
  (exists_simple_character_eq_sub A B hnorm hpos).choose_spec.1

@[simp]
lemma simpleOfVirtualChar_character (g : G) :
    (simpleOfVirtualChar A B hnorm hpos).character g = A.character g - B.character g :=
  (exists_simple_character_eq_sub A B hnorm hpos).choose_spec.2 g

/-- The dimension of the representation realizing `χ_A - χ_B` is `dim A - dim B`. -/
lemma finrank_simpleOfVirtualChar :
    finrank ℂ (simpleOfVirtualChar A B hnorm hpos) = finrank ℂ A - finrank ℂ B := by
  have h := simpleOfVirtualChar_character A B hnorm hpos 1
  simp only [FDRep.char_one] at h
  have : ((finrank ℂ (simpleOfVirtualChar A B hnorm hpos) : ℤ) : ℂ)
      = ((finrank ℂ A : ℤ) - (finrank ℂ B : ℤ) : ℤ) := by push_cast; exact h
  have hZ : (finrank ℂ (simpleOfVirtualChar A B hnorm hpos) : ℤ)
      = (finrank ℂ A : ℤ) - (finrank ℂ B : ℤ) := by exact_mod_cast this
  omega

end Choice

end Etingof
