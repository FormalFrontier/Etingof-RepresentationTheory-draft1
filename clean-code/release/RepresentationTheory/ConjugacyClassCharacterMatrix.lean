/-
Copyright (c) 2026 mathlib-initiative. All rights reserved.
Released under Apache 2.0 license as described in the file LICENCE.
Authors: mathlib-initiative
-/

import Mathlib
import RepresentationTheory.FDRep.Character
import RepresentationTheory.Representation.Character.InversionAndInvariantForms
import RepresentationTheory.Alignment.Attribute

open CategoryTheory MulAction
open scoped Classical ComplexConjugate Matrix

namespace RepresentationTheory.ConjugacyClassCharacterMatrix

variable {G : Type} [Group G] [Fintype G]

/-- An auxiliary natural-number-valued function on a group. -/
noncomputable def auxiliaryGroupElementNat (g : G) : ℕ :=
  Nat.card (Subgroup.centralizer ({g} : Set G))

/-- The auxiliary natural number assigned to an element of a finite group is positive. -/
lemma auxiliaryGroupElementNat_pos (g : G) : 0 < auxiliaryGroupElementNat g := by
  rw [auxiliaryGroupElementNat]
  exact Nat.card_pos

/-- The conjugacy class of a chosen representative of a quotient class is that class. -/
lemma mk_out_conjugacyClass (c : ConjClasses G) : ConjClasses.mk (Quotient.out c) = c := by
  rw [← ConjClasses.quotient_mk_eq_mk]
  exact Quotient.out_eq c

/-- Complex conjugation of a finite-group character value equals the character value at the
inverse element. -/
lemma star_character_eq_character_inv (W : FDRep ℂ G) (g : G) :
    star (W.character g) = W.character g⁻¹ := by
  rw [← starRingEnd_apply]
  exact
    (RepresentationTheory.Representation.Character.InversionAndInvariantForms.character_inv_eq_conj
      W.ρ g).symm

/-- An auxiliary complex-valued function on the conjugacy classes of a group. -/
noncomputable def auxiliaryConjugacyClassComplex (c : ConjClasses G) : ℂ :=
  (Real.sqrt (auxiliaryGroupElementNat (Quotient.out c) : ℝ) : ℂ)

/-- The square root of the cast auxiliary natural number assigned to a conjugacy-class
representative is positive. -/
lemma natCast_auxiliaryGroupElementNat_sqrt_pos (c : ConjClasses G) :
    0 < Real.sqrt (auxiliaryGroupElementNat (Quotient.out c) : ℝ) :=
  Real.sqrt_pos.mpr (by exact_mod_cast auxiliaryGroupElementNat_pos (Quotient.out c))

/-- The auxiliary complex number attached to a conjugacy class of a finite group is nonzero. -/
lemma auxiliaryConjugacyClassComplex_ne_zero (c : ConjClasses G) :
    auxiliaryConjugacyClassComplex c ≠ 0 := by
  rw [auxiliaryConjugacyClassComplex, Ne, Complex.ofReal_eq_zero]
  exact (natCast_auxiliaryGroupElementNat_sqrt_pos c).ne'

/-- The auxiliary complex number attached to a conjugacy class is fixed by complex
conjugation. -/
lemma star_auxiliaryConjugacyClassComplex (c : ConjClasses G) :
    star (auxiliaryConjugacyClassComplex c) = auxiliaryConjugacyClassComplex c := by
  rw [auxiliaryConjugacyClassComplex, ← starRingEnd_apply, Complex.conj_ofReal]

/-- The square of the auxiliary complex number attached to a conjugacy class is the cast of the
auxiliary natural number assigned to a representative. -/
lemma auxiliaryConjugacyClassComplex_sq (c : ConjClasses G) :
    auxiliaryConjugacyClassComplex c * auxiliaryConjugacyClassComplex c =
      (auxiliaryGroupElementNat (Quotient.out c) : ℂ) := by
  rw [auxiliaryConjugacyClassComplex, ← Complex.ofReal_mul,
    Real.mul_self_sqrt (by positivity), Complex.ofReal_natCast]

/-- Associates a complex matrix indexed by conjugacy classes to a conjugacy-class-indexed family
of representations. -/
noncomputable def auxiliaryConjugacyClassMatrix (V : ConjClasses G → FDRep ℂ G) :
    Matrix (ConjClasses G) (ConjClasses G) ℂ :=
  fun i j => (V i).character (Quotient.out j) / auxiliaryConjugacyClassComplex j

/-- Rewrites the product of an entry of the auxiliary matrix with the conjugate of another entry
as a quotient involving character values and an auxiliary natural number. -/
lemma auxiliaryConjugacyClassMatrix_entry_mul_star_entry
    (V : ConjClasses G → FDRep ℂ G) (i j c : ConjClasses G) :
    auxiliaryConjugacyClassMatrix V i c * star (auxiliaryConjugacyClassMatrix V j c) =
      (V i).character (Quotient.out c) * (V j).character (Quotient.out c)⁻¹ /
        (auxiliaryGroupElementNat (Quotient.out c) : ℂ) := by
  simp only [auxiliaryConjugacyClassMatrix]
  rw [star_div₀, star_character_eq_character_inv, star_auxiliaryConjugacyClassComplex,
    div_mul_div_comm, auxiliaryConjugacyClassComplex_sq]

/-- Expresses a conjugated auxiliary-matrix entry times another entry as a quotient of character
values by two auxiliary complex numbers attached to conjugacy classes. -/
lemma star_auxiliaryConjugacyClassMatrix_entry_mul_entry
    (V : ConjClasses G → FDRep ℂ G) (i c c' : ConjClasses G) :
    star (auxiliaryConjugacyClassMatrix V i c) * auxiliaryConjugacyClassMatrix V i c' =
      (V i).character (Quotient.out c)⁻¹ * (V i).character (Quotient.out c') /
        (auxiliaryConjugacyClassComplex c * auxiliaryConjugacyClassComplex c') := by
  simp only [auxiliaryConjugacyClassMatrix]
  rw [star_div₀, star_character_eq_character_inv, star_auxiliaryConjugacyClassComplex,
    div_mul_div_comm]

/-- The number of elements in a conjugacy class multiplied by the auxiliary natural number
assigned to a representative equals the group cardinality. -/
lemma conjugacyClassCard_mul_auxiliaryGroupElementNat (c : ConjClasses G) :
    (Finset.univ.filter (fun a : G => ConjClasses.mk a = c)).card *
        auxiliaryGroupElementNat (Quotient.out c) = Fintype.card G := by
  classical
  have hcarrier :
      (Finset.univ.filter (fun a : G => ConjClasses.mk a = c)) = (c.carrier).toFinset := by
    ext a
    simp [ConjClasses.mem_carrier_iff_mk_eq]
  have horb : MulAction.orbit (ConjAct G) (Quotient.out c) = c.carrier := by
    rw [ConjAct.orbit_eq_carrier_conjClasses, mk_out_conjugacyClass]
  have hstab : auxiliaryGroupElementNat (Quotient.out c) =
      Fintype.card (MulAction.stabilizer (ConjAct G) (Quotient.out c)) := by
    rw [auxiliaryGroupElementNat, Subgroup.nat_card_centralizer_nat_card_stabilizer,
      Nat.card_eq_fintype_card]
  rw [hcarrier, Set.toFinset_card,
    Fintype.card_congr (Equiv.setCongr horb.symm), hstab,
    MulAction.card_orbit_mul_card_stabilizer_eq_card_group (ConjAct G) (Quotient.out c),
    ConjAct.card]

/-- For a conjugation-invariant complex function, the sum over conjugacy classes divided by the
auxiliary natural numbers of representatives equals the group sum scaled by the inverse of the
group cardinality. -/
lemma sum_conjClasses_div_auxiliaryGroupElementNat
    (F : G → ℂ) (hF : ∀ a b : G, F (b * a * b⁻¹) = F a)
    [Invertible (Fintype.card G : ℂ)] :
    ∑ c : ConjClasses G,
        F (Quotient.out c) / (auxiliaryGroupElementNat (Quotient.out c) : ℂ) =
      ⅟(Fintype.card G : ℂ) • ∑ g : G, F g := by
  classical
  have key : ∀ c : ConjClasses G,
      ∑ a ∈ Finset.univ.filter (fun a : G => ConjClasses.mk a = c), F a =
        (Fintype.card G : ℂ) /
          (auxiliaryGroupElementNat (Quotient.out c) : ℂ) * F (Quotient.out c) := by
    intro c
    have hconst : ∀ a ∈ Finset.univ.filter (fun a : G => ConjClasses.mk a = c),
        F a = F (Quotient.out c) := by
      intro a ha
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at ha
      have hconj : ConjClasses.mk a = ConjClasses.mk (Quotient.out c) := by
        rw [ha, mk_out_conjugacyClass]
      obtain ⟨u, hu⟩ := isConj_iff.mp (ConjClasses.mk_eq_mk_iff_isConj.mp hconj)
      rw [← hu, hF]
    rw [Finset.sum_congr rfl hconst, Finset.sum_const, nsmul_eq_mul]
    congr 1
    rw [eq_div_iff (by
      exact_mod_cast (auxiliaryGroupElementNat_pos (Quotient.out c)).ne')]
    exact_mod_cast conjugacyClassCard_mul_auxiliaryGroupElementNat c
  have step : ∑ g : G, F g =
      ∑ c : ConjClasses G,
        (Fintype.card G : ℂ) /
          (auxiliaryGroupElementNat (Quotient.out c) : ℂ) * F (Quotient.out c) := by
    rw [← Finset.sum_fiberwise Finset.univ ConjClasses.mk F]
    exact Finset.sum_congr rfl (fun c _ => key c)
  rw [step, Finset.smul_sum]
  apply Finset.sum_congr rfl
  intro c _
  rw [smul_eq_mul,
    show (Fintype.card G : ℂ) /
        (auxiliaryGroupElementNat (Quotient.out c) : ℂ) * F (Quotient.out c) =
      (Fintype.card G : ℂ) *
        (F (Quotient.out c) / (auxiliaryGroupElementNat (Quotient.out c) : ℂ)) from by ring,
    ← mul_assoc, invOf_mul_self, one_mul]

variable (V : ConjClasses G → FDRep ℂ G)

/-- The conjugate transpose of the auxiliary conjugacy-class matrix is a right inverse when the
indexed simple representations are pairwise nonisomorphic. -/
@[source_ref "Chapter4/Remark4.5.5" (role := supporting)]
theorem auxiliaryConjugacyClassMatrix_mul_conjTranspose_eq_one
    [∀ i, Simple (V i)] (hdist : ∀ i j, Nonempty (V i ≅ V j) → i = j)
    [Invertible (Fintype.card G : ℂ)] :
    auxiliaryConjugacyClassMatrix V * (auxiliaryConjugacyClassMatrix V)ᴴ = 1 := by
  classical
  ext i j
  rw [Matrix.mul_apply]
  have hrow : (∑ c, auxiliaryConjugacyClassMatrix V i c *
      (auxiliaryConjugacyClassMatrix V)ᴴ c j) =
      ∑ c : ConjClasses G,
        (fun g => (V i).character g * (V j).character g⁻¹) (Quotient.out c) /
          (auxiliaryGroupElementNat (Quotient.out c) : ℂ) := by
    apply Finset.sum_congr rfl
    intro c _
    rw [Matrix.conjTranspose_apply]
    exact auxiliaryConjugacyClassMatrix_entry_mul_star_entry V i j c
  rw [hrow, sum_conjClasses_div_auxiliaryGroupElementNat
    (fun g => (V i).character g * (V j).character g⁻¹) ?hF]
  · rw [RepresentationTheory.FDRep.Character.normalizedCharacterSum_eq_ite_iso_of_simple,
      Matrix.one_apply]
    by_cases h : i = j
    · subst h
      rw [if_pos ⟨Iso.refl _⟩, if_pos rfl]
    · rw [if_neg (fun hn => h (hdist i j hn)), if_neg h]
  case hF =>
    intro a b
    show (V i).character (b * a * b⁻¹) * (V j).character (b * a * b⁻¹)⁻¹ =
      (V i).character a * (V j).character a⁻¹
    rw [show (b * a * b⁻¹)⁻¹ = b * a⁻¹ * b⁻¹ from by group]
    rw [FDRep.char_conj, FDRep.char_conj]

/-- The conjugate transpose of the auxiliary conjugacy-class matrix is a left inverse when the
indexed simple representations are pairwise nonisomorphic. -/
@[source_ref "Chapter4/Remark4.5.5" (role := supporting)]
theorem conjTranspose_auxiliaryConjugacyClassMatrix_mul_eq_one
    [∀ i, Simple (V i)] (hdist : ∀ i j, Nonempty (V i ≅ V j) → i = j)
    [Invertible (Fintype.card G : ℂ)] :
    (auxiliaryConjugacyClassMatrix V)ᴴ * auxiliaryConjugacyClassMatrix V = 1 :=
  (Matrix.mul_eq_one_comm_of_equiv (Equiv.refl (ConjClasses G))).mp
    (auxiliaryConjugacyClassMatrix_mul_conjTranspose_eq_one V hdist)

/-- Sums products of character values over the indexed simple representations, giving the
auxiliary natural number attached to a representative when the conjugacy classes are equal and
zero otherwise. -/
@[source_ref "Chapter4/Remark4.5.5" (role := supporting)]
theorem sum_character_inv_mul_character
    [∀ i, Simple (V i)] (hdist : ∀ i j, Nonempty (V i ≅ V j) → i = j)
    [Invertible (Fintype.card G : ℂ)] (c c' : ConjClasses G) :
    ∑ i : ConjClasses G,
        (V i).character (Quotient.out c)⁻¹ * (V i).character (Quotient.out c') =
      if c = c' then (auxiliaryGroupElementNat (Quotient.out c) : ℂ) else 0 := by
  classical
  have hU := conjTranspose_auxiliaryConjugacyClassMatrix_mul_eq_one V hdist
  have h2 := congrFun (congrFun hU c) c'
  rw [Matrix.mul_apply] at h2
  simp only [Matrix.conjTranspose_apply] at h2
  rw [Finset.sum_congr rfl
    (fun i _ => star_auxiliaryConjugacyClassMatrix_entry_mul_entry V i c c')] at h2
  rw [← Finset.sum_div, Matrix.one_apply] at h2
  rw [div_eq_iff (mul_ne_zero (auxiliaryConjugacyClassComplex_ne_zero c)
    (auxiliaryConjugacyClassComplex_ne_zero c'))] at h2
  rw [h2]
  by_cases hcc : c = c'
  · subst hcc
    rw [if_pos rfl, if_pos rfl, one_mul, auxiliaryConjugacyClassComplex_sq]
  · rw [if_neg hcc, if_neg hcc, zero_mul]

end RepresentationTheory.ConjugacyClassCharacterMatrix
