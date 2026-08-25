/-
Copyright (c) 2026 mathlib-initiative. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: mathlib-initiative
-/

import Mathlib
import RepresentationTheory.FiniteFieldMatrixCharacterValues
import RepresentationTheory.GaloisFieldAuxiliary
import RepresentationTheory.Alignment.Attribute

namespace RepresentationTheory.FiniteField.CharacterSums

variable (p : ℕ) [hp : Fact (Nat.Prime p)] (n : ℕ)

private abbrev GL2 := Matrix.GeneralLinearGroup (Fin 2) (GaloisField p n)


 

/-- The sum of a nontrivial complex-valued character of a finite commutative group vanishes. -/
lemma sum_character_eq_zero_of_ne_one
    {G : Type*} [CommGroup G] [Fintype G]
    (χ : G →* ℂˣ) (hχ : χ ≠ 1) :
    ∑ g : G, (χ g : ℂ) = 0 := by
   
   
  have ⟨g₀, hg₀⟩ : ∃ g₀, χ g₀ ≠ 1 := by
    by_contra h; push Not at h; exact absurd (MonoidHom.ext h) hχ
   
  have hne : (χ g₀ : ℂ) ≠ 1 := by
    intro h; apply hg₀; exact Units.val_injective h
  have key : (χ g₀ : ℂ) * ∑ g, (χ g : ℂ) = ∑ g, (χ g : ℂ) := by
    rw [Finset.mul_sum]
    apply Finset.sum_nbij (fun g => g₀ * g)
    · intro g _; exact Finset.mem_univ _
    · intro g₁ _ g₂ _ h; exact mul_left_cancel h
    · intro g _; exact ⟨g₀⁻¹ * g, Finset.mem_univ _, by group⟩
    · intro g _; simp only [map_mul, Units.val_mul]
   
  have h1 : ((χ g₀ : ℂ) - 1) * ∑ g, (χ g : ℂ) = 0 := by
    rw [sub_mul, one_mul, sub_eq_zero]; exact key
  rcases mul_eq_zero.mp h1 with h | h
  · exact absurd (sub_eq_zero.mp h) hne
  · exact h

open Classical in
 



private lemma complementarySeriesChar_elliptic_eq
    [Fintype (GaloisField p n)] [DecidableEq (GaloisField p n)]
    [Fintype (GL2 p n)]
    (nu : (RepresentationTheory.FiniteFieldMatrixCharacterValues.distinguishedMatrixSubgroup p n) →* ℂˣ)
    (g : GL2 p n) (hg : RepresentationTheory.FiniteFieldUnitClassDecomposition.Auxiliary.classPredicateAlpha (p := p) (n := n) g) :
    RepresentationTheory.FiniteFieldMatrixCharacterValues.subgroupCharacterMatrixFunction p n nu g =
    -((Fintype.card ↥(RepresentationTheory.FiniteFieldMatrixCharacterValues.distinguishedMatrixSubgroup p n) : ℂ)⁻¹ *
        ∑ x : GL2 p n,
          if h : x⁻¹ * g * x ∈ RepresentationTheory.FiniteFieldMatrixCharacterValues.distinguishedMatrixSubgroup p n
          then (nu ⟨x⁻¹ * g * x, h⟩).val
          else 0) := by
  unfold RepresentationTheory.FiniteFieldMatrixCharacterValues.subgroupCharacterMatrixFunction
  set alpha := nu.comp (RepresentationTheory.FiniteFieldMatrixCharacterValues.scalarUnitsToDistinguishedSubgroup p n)
  have hW : RepresentationTheory.FiniteFieldMatrixCharacterValues.distinguishedMatrixUnitFunction p n g = -1 := RepresentationTheory.FiniteFieldMatrixCharacterValues.distinguishedMatrixUnitFunction_auxiliaryProperty p n g hg
  have hV : RepresentationTheory.FiniteFieldMatrixCharacterValues.multiplicativeCharacterMatrixFunction p n alpha g = 0 := RepresentationTheory.FiniteFieldMatrixCharacterValues.multiplicativeCharacterMatrixFunction_eq_zero_of_auxiliaryProperty p n alpha g hg
  rw [hW, hV]
  ring

 

/-- The commutative group structure on the subtype defined by the auxiliary membership condition. -/
noncomputable instance auxiliarySubtypeCommGroup :
    CommGroup ↥(RepresentationTheory.FiniteFieldMatrixCharacterValues.distinguishedMatrixSubgroup p n) :=
  { (inferInstance : Group ↥(RepresentationTheory.FiniteFieldMatrixCharacterValues.distinguishedMatrixSubgroup p n)) with
    mul_comm := by
      intro ⟨a, ha⟩ ⟨b, hb⟩
      ext
      obtain ⟨a', rfl⟩ := ha
      obtain ⟨b', rfl⟩ := hb
      simp only [Subgroup.coe_mul, ← map_mul, mul_comm a' b'] }

 
/-- Transforms a complex-valued multiplicative character on the auxiliary subtype into another such character. -/
noncomputable def characterTransform
    [Fintype (GaloisField p n)]
    (nu : ↥(RepresentationTheory.FiniteFieldMatrixCharacterValues.distinguishedMatrixSubgroup p n) →* ℂˣ) :
    ↥(RepresentationTheory.FiniteFieldMatrixCharacterValues.distinguishedMatrixSubgroup p n) →* ℂˣ :=
  (powMonoidHom (Fintype.card (GaloisField p n) - 1)).comp nu

 
private lemma qm1_char_nontrivial
    [Fintype (GaloisField p n)]
    (nu : ↥(RepresentationTheory.FiniteFieldMatrixCharacterValues.distinguishedMatrixSubgroup p n) →* ℂˣ)
    (hnu_ne : ∃ k : ↥(RepresentationTheory.FiniteFieldMatrixCharacterValues.distinguishedMatrixSubgroup p n),
      (nu k) ^ Fintype.card (GaloisField p n) ≠ nu k) :
    characterTransform p n nu ≠ 1 := by
  obtain ⟨k, hk⟩ := hnu_ne
  intro h
  apply hk
  have := congr_fun (congr_arg DFunLike.coe h) k
  simp only [characterTransform, MonoidHom.coe_comp, Function.comp_apply, powMonoidHom_apply,
    MonoidHom.one_apply] at this
   
  have hq_pos : 0 < Fintype.card (GaloisField p n) := Fintype.card_pos
  rw [show Fintype.card (GaloisField p n) = Fintype.card (GaloisField p n) - 1 + 1
    from by omega, pow_succ, this, one_mul]

 
/-- The transformed character is one on values of the specified auxiliary map. -/
lemma characterTransform_apply_auxiliaryMap_eq_one
    [Fintype (GaloisField p n)] [DecidableEq (GaloisField p n)]
    (nu : ↥(RepresentationTheory.FiniteFieldMatrixCharacterValues.distinguishedMatrixSubgroup p n) →* ℂˣ)
    (hn : n ≠ 0)
    (a : (GaloisField p n)ˣ) :
    characterTransform p n nu (RepresentationTheory.FiniteFieldMatrixCharacterValues.scalarUnitsToDistinguishedSubgroup p n a) = 1 := by
  simp only [characterTransform, MonoidHom.coe_comp, Function.comp_apply, powMonoidHom_apply]
   
   
   
   
  have : (RepresentationTheory.FiniteFieldMatrixCharacterValues.scalarUnitsToDistinguishedSubgroup p n a) ^ (Fintype.card (GaloisField p n) - 1) = 1 := by
    have hord : orderOf a ∣ Fintype.card (GaloisField p n) - 1 := by
      rw [← Fintype.card_units]
      exact orderOf_dvd_card
    have := map_pow (RepresentationTheory.FiniteFieldMatrixCharacterValues.scalarUnitsToDistinguishedSubgroup p n) a (Fintype.card (GaloisField p n) - 1)
    rw [← this]
    have ha_pow : a ^ (Fintype.card (GaloisField p n) - 1) = 1 :=
      orderOf_dvd_iff_pow_eq_one.mp hord
    rw [ha_pow, map_one]
  rw [← map_pow, this, map_one]

 



/-- Derives one auxiliary property from membership in the auxiliary set and the failure of another auxiliary property. -/
lemma auxiliaryProperty_of_mem_of_not_otherProperty
    (hp2 : p ≠ 2) (hn : n ≠ 0)
    (k : GL2 p n) (hk : k ∈ RepresentationTheory.FiniteFieldMatrixCharacterValues.distinguishedMatrixSubgroup p n)
    (hne : ¬RepresentationTheory.FiniteFieldUnitClassDecomposition.Auxiliary.classPredicateAlpha (p := p) (n := n) k) :
    RepresentationTheory.FiniteFieldUnitClassDecomposition.Auxiliary.classPredicateGamma (p := p) (n := n) k := by
   
  have hK := RepresentationTheory.FiniteFieldMatrixCharacterValues.matrixInvariant_eq_zero_or_not_isSquare_of_mem_distinguishedSubgroup p n hp2 k hk
   
  have hIsSquare : IsSquare (RepresentationTheory.FiniteFieldUnitClassDecomposition.Auxiliary.entryDiscriminant k) := by
    simp only [RepresentationTheory.FiniteFieldUnitClassDecomposition.Auxiliary.classPredicateAlpha, not_not] at hne; exact hne
   
  have hdisc_zero : RepresentationTheory.FiniteFieldUnitClassDecomposition.Auxiliary.entryDiscriminant k = 0 := by
    rcases hK with h | h
    · exact h
    · exact absurd hIsSquare h
   
  rcases RepresentationTheory.FiniteFieldUnitClassDecomposition.classPredicates_exhaustive k with hs | hp | hss | he
  · exact hs
  ·  
    have h_para := RepresentationTheory.FiniteFieldMatrixCharacterValues.conjugate_not_mem_distinguishedSubgroup p n k hp 1
    simp only [inv_one, one_mul, mul_one] at h_para
    exact absurd hk h_para
  ·  
    exact absurd hdisc_zero hss.1
  ·  
    exact absurd he hne

 
 
 
 
open Classical in
private lemma nonscalar_char_sum
    [Fintype (GL2 p n)] [Fintype (GaloisField p n)]
    [DecidableEq (GaloisField p n)]
    (hp2 : p ≠ 2)
    (nu : (RepresentationTheory.FiniteFieldMatrixCharacterValues.distinguishedMatrixSubgroup p n) →* ℂˣ) (hn : n ≠ 0)
    (hnu_ne : ∃ k : ↥(RepresentationTheory.FiniteFieldMatrixCharacterValues.distinguishedMatrixSubgroup p n),
      (nu k) ^ Fintype.card (GaloisField p n) ≠ nu k) :
    ∑ k : ↥(RepresentationTheory.FiniteFieldMatrixCharacterValues.distinguishedMatrixSubgroup p n),
      (if RepresentationTheory.FiniteFieldUnitClassDecomposition.Auxiliary.classPredicateAlpha (p := p) (n := n) (k : GL2 p n)
       then (1 : ℂ) + starRingEnd ℂ ((characterTransform p n nu k : ℂˣ) : ℂ)
       else 0) =
    ((Fintype.card (GaloisField p n) : ℂ) - 1) ^ 2 := by
   
   
   
   
   
  set ψ : ↥(RepresentationTheory.FiniteFieldMatrixCharacterValues.distinguishedMatrixSubgroup p n) → ℂ :=
    fun k => starRingEnd ℂ ((characterTransform p n nu k : ℂˣ) : ℂ) with hψ_def
   
  have h_conj_sum_zero : ∑ k : ↥(RepresentationTheory.FiniteFieldMatrixCharacterValues.distinguishedMatrixSubgroup p n), ψ k = 0 := by
    rw [hψ_def]
    rw [show (∑ k, starRingEnd ℂ ((characterTransform p n nu k : ℂˣ) : ℂ)) =
      starRingEnd ℂ (∑ k, ((characterTransform p n nu k : ℂˣ) : ℂ)) from
        (map_sum (starRingEnd ℂ) _ _).symm]
    rw [sum_character_eq_zero_of_ne_one (characterTransform p n nu)
      (qm1_char_nontrivial p n nu hnu_ne), map_zero]
  have h_full_sum : ∑ k : ↥(RepresentationTheory.FiniteFieldMatrixCharacterValues.distinguishedMatrixSubgroup p n), ((1 : ℂ) + ψ k) =
      (Fintype.card ↥(RepresentationTheory.FiniteFieldMatrixCharacterValues.distinguishedMatrixSubgroup p n) : ℂ) := by
    rw [Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ, nsmul_eq_mul, mul_one,
      h_conj_sum_zero, add_zero]
   
  have hdecomp : ∑ k : ↥(RepresentationTheory.FiniteFieldMatrixCharacterValues.distinguishedMatrixSubgroup p n),
      (if RepresentationTheory.FiniteFieldUnitClassDecomposition.Auxiliary.classPredicateAlpha (p := p) (n := n) (k : GL2 p n)
       then (1 : ℂ) + ψ k else 0) =
      ∑ k : ↥(RepresentationTheory.FiniteFieldMatrixCharacterValues.distinguishedMatrixSubgroup p n), ((1 : ℂ) + ψ k) -
      ∑ k : ↥(RepresentationTheory.FiniteFieldMatrixCharacterValues.distinguishedMatrixSubgroup p n),
        (if ¬RepresentationTheory.FiniteFieldUnitClassDecomposition.Auxiliary.classPredicateAlpha (p := p) (n := n) (k : GL2 p n)
         then (1 : ℂ) + ψ k else 0) := by
    rw [← Finset.sum_sub_distrib]
    congr 1; ext k; split_ifs with h <;> simp
   
  have h_scalar_psi_one : ∀ k : ↥(RepresentationTheory.FiniteFieldMatrixCharacterValues.distinguishedMatrixSubgroup p n),
      ¬RepresentationTheory.FiniteFieldUnitClassDecomposition.Auxiliary.classPredicateAlpha (p := p) (n := n) (k : GL2 p n) → ψ k = 1 := by
    intro k hne
    have hscalar := auxiliaryProperty_of_mem_of_not_otherProperty p n hp2 hn
      (k : GL2 p n) k.2 hne
     
    have hk00_ne : (k : GL2 p n).val 0 0 ≠ 0 := by
      obtain ⟨h01, h10, h00_eq⟩ := hscalar
       
      intro h0
      have h01' : (k : GL2 p n).val 0 1 = 0 := h01
      have h10' : (k : GL2 p n).val 1 0 = 0 := h10
      have h00_eq' : (k : GL2 p n).val 0 0 = (k : GL2 p n).val 1 1 := h00_eq
      have h11 : (k : GL2 p n).val 1 1 = 0 := by rw [← h00_eq']; exact h0
      have hdet_zero : Matrix.det (k : GL2 p n).val = 0 := by
        rw [Matrix.det_fin_two]; simp [h01', h10', h0, h11]
      have hdet_unit := (k : GL2 p n).isUnit
      rw [Matrix.isUnit_iff_isUnit_det] at hdet_unit
      exact not_isUnit_zero (hdet_zero ▸ hdet_unit)
    set a := Units.mk0 ((k : GL2 p n).val 0 0) hk00_ne
     
    have hk_eq : k = RepresentationTheory.FiniteFieldMatrixCharacterValues.scalarUnitsToDistinguishedSubgroup p n a := by
      apply Subtype.ext
      letI := RepresentationTheory.FiniteFieldMatrixCharacterValues.quadraticFiniteFieldAlgebra p n
      unfold RepresentationTheory.FiniteFieldMatrixCharacterValues.scalarUnitsToDistinguishedSubgroup
      simp only [dif_neg hn, MonoidHom.comp_apply, MonoidHom.codRestrict_apply]
      exact RepresentationTheory.FiniteFieldMatrixCharacterValues.eq_quadraticFieldUnitsToMatrixUnits_topLeft p n hn (k : GL2 p n) hscalar hk00_ne
     
     
    change ψ k = 1
    have hqm1 : (characterTransform p n nu (RepresentationTheory.FiniteFieldMatrixCharacterValues.scalarUnitsToDistinguishedSubgroup p n a) : ℂˣ) =
      (1 : ℂˣ) := characterTransform_apply_auxiliaryMap_eq_one p n nu hn a
    simp only [hψ_def, hk_eq, hqm1, Units.val_one, map_one]
   
  have h_scalar_sum : ∑ k : ↥(RepresentationTheory.FiniteFieldMatrixCharacterValues.distinguishedMatrixSubgroup p n),
      (if ¬RepresentationTheory.FiniteFieldUnitClassDecomposition.Auxiliary.classPredicateAlpha (p := p) (n := n) (k : GL2 p n) then (1 : ℂ) + ψ k else 0) =
      2 * (Fintype.card (GaloisField p n) - 1 : ℂ) := by
     
    have hval : ∀ k : ↥(RepresentationTheory.FiniteFieldMatrixCharacterValues.distinguishedMatrixSubgroup p n),
        ¬RepresentationTheory.FiniteFieldUnitClassDecomposition.Auxiliary.classPredicateAlpha (p := p) (n := n) (k : GL2 p n) →
        (1 : ℂ) + ψ k = 2 := by
      intro k hne; rw [h_scalar_psi_one k hne]; norm_num
     
     
     
     
    have h_ite_eq : ∀ k' : ↥(RepresentationTheory.FiniteFieldMatrixCharacterValues.distinguishedMatrixSubgroup p n),
        (if ¬RepresentationTheory.FiniteFieldUnitClassDecomposition.Auxiliary.classPredicateAlpha (p := p) (n := n) (k' : GL2 p n) then (1 : ℂ) + ψ k' else 0) =
        if ¬RepresentationTheory.FiniteFieldUnitClassDecomposition.Auxiliary.classPredicateAlpha (p := p) (n := n) (k' : GL2 p n) then (2 : ℂ) else 0 := by
      intro k'; split_ifs with h
      · rfl
      · exact hval k' h
    simp_rw [h_ite_eq]
     
    rw [Finset.sum_ite, Finset.sum_const_zero, add_zero, Finset.sum_const, nsmul_eq_mul]
     
    letI := RepresentationTheory.FiniteFieldMatrixCharacterValues.quadraticFiniteFieldAlgebra p n
    set b := Module.finBasisOfFinrankEq (R := GaloisField p n)
      (M := GaloisField p (2 * n)) (RepresentationTheory.FiniteFieldMatrixCharacterValues.quadraticFiniteField_finrank p n hn)
     
    have h_entry : ∀ (a : (GaloisField p n)ˣ) (i j : Fin 2),
        ((RepresentationTheory.FiniteFieldMatrixCharacterValues.scalarUnitsToDistinguishedSubgroup p n a :
          ↥(RepresentationTheory.FiniteFieldMatrixCharacterValues.distinguishedMatrixSubgroup p n)) : GL2 p n).val i j =
        if i = j then (a : GaloisField p n) else 0 := by
      intro a i j
      unfold RepresentationTheory.FiniteFieldMatrixCharacterValues.scalarUnitsToDistinguishedSubgroup RepresentationTheory.FiniteFieldMatrixCharacterValues.quadraticFieldUnitsToMatrixUnits
      simp only [dif_neg hn, MonoidHom.comp_apply, MonoidHom.codRestrict_apply]
      change (Algebra.leftMulMatrix b
        ((algebraMap (GaloisField p n) (GaloisField p (2 * n))) (a : GaloisField p n))) i j = _
      rw [Algebra.leftMulMatrix_eq_repr_mul, Algebra.algebraMap_eq_smul_one,
          smul_mul_assoc, one_mul, map_smul, Finsupp.smul_apply, smul_eq_mul,
          b.repr_self, Finsupp.single_apply, mul_ite, mul_one, mul_zero]
      simp only [eq_comm]
     
    have h_ste_not_ell : ∀ a : (GaloisField p n)ˣ,
        ¬RepresentationTheory.FiniteFieldUnitClassDecomposition.Auxiliary.classPredicateAlpha (p := p) (n := n)
          ((RepresentationTheory.FiniteFieldMatrixCharacterValues.scalarUnitsToDistinguishedSubgroup p n a :
            ↥(RepresentationTheory.FiniteFieldMatrixCharacterValues.distinguishedMatrixSubgroup p n)) : GL2 p n) :=
      fun a => RepresentationTheory.FiniteFieldUnitClassDecomposition.not_classPredicateAlpha_of_classPredicateGamma _
        ((RepresentationTheory.FiniteFieldUnitClassDecomposition.classPredicateGamma_iff_matrixEntries _).mpr ⟨by simp [h_entry], by simp [h_entry], by simp [h_entry]⟩)
     
    have h_ste_inj : Function.Injective (RepresentationTheory.FiniteFieldMatrixCharacterValues.scalarUnitsToDistinguishedSubgroup p n) := by
      intro a₁ a₂ h
      have h₀ := h_entry a₁ 0 0; simp only [ite_true] at h₀
      have h₁ := h_entry a₂ 0 0; simp only [ite_true] at h₁
      have : (a₁ : GaloisField p n) = (a₂ : GaloisField p n) := by
        have := congr_arg (fun k : ↥(RepresentationTheory.FiniteFieldMatrixCharacterValues.distinguishedMatrixSubgroup p n) =>
          (k : GL2 p n).val 0 0) h
        simp only [h₀, h₁] at this; exact this
      exact Units.ext this
     
    have h_card : (Finset.univ.filter (fun k : ↥(RepresentationTheory.FiniteFieldMatrixCharacterValues.distinguishedMatrixSubgroup p n) =>
        ¬RepresentationTheory.FiniteFieldUnitClassDecomposition.Auxiliary.classPredicateAlpha (p := p) (n := n) (k : GL2 p n))).card =
        Fintype.card (GaloisField p n) - 1 := by
      rw [← Fintype.card_units, ← Finset.card_univ (α := (GaloisField p n)ˣ)]
      symm
      apply Finset.card_nbij (RepresentationTheory.FiniteFieldMatrixCharacterValues.scalarUnitsToDistinguishedSubgroup p n)
      · intro a _; exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, h_ste_not_ell a⟩
      · intro a₁ _ a₂ _ h; exact h_ste_inj h
      · intro k hk
        rw [Finset.mem_coe, Finset.mem_filter] at hk
        have hscalar := auxiliaryProperty_of_mem_of_not_otherProperty p n hp2 hn
          (k : GL2 p n) k.2 hk.2
        have hk00_ne : (k : GL2 p n).val 0 0 ≠ 0 := by
          obtain ⟨h01, h10, _⟩ := (RepresentationTheory.FiniteFieldUnitClassDecomposition.classPredicateGamma_iff_matrixEntries _).mp hscalar
          intro h0
          have : Matrix.det (k : GL2 p n).val = 0 := by
            rw [Matrix.det_fin_two]; simp [h01, h10, h0]
          exact (Matrix.isUnits_det_units (k : GL2 p n)).ne_zero this
        refine ⟨Units.mk0 _ hk00_ne, Finset.mem_coe.mpr (Finset.mem_univ _), ?_⟩
        apply Subtype.ext
        unfold RepresentationTheory.FiniteFieldMatrixCharacterValues.scalarUnitsToDistinguishedSubgroup
        simp only [dif_neg hn, MonoidHom.comp_apply, MonoidHom.codRestrict_apply]
        exact (RepresentationTheory.FiniteFieldMatrixCharacterValues.eq_quadraticFieldUnitsToMatrixUnits_topLeft p n hn _ hscalar hk00_ne).symm
    rw [h_card]; push_cast [Nat.cast_sub Fintype.card_pos]; ring
   
  rw [hdecomp, h_full_sum, h_scalar_sum]
   
  haveI : Fintype (GaloisField p (2 * n)) := Fintype.ofFinite _
  set q := Fintype.card (GaloisField p n) with hq_def
  have hq_pos : 1 < q := by
    rw [hq_def, ← Nat.card_eq_fintype_card, GaloisField.card p n hn]
    exact Nat.one_lt_pow hn hp.out.one_lt
  have hinj : Function.Injective (RepresentationTheory.FiniteFieldMatrixCharacterValues.quadraticFieldUnitsToMatrixUnits p n) := by
    intro a b hab
    unfold RepresentationTheory.FiniteFieldMatrixCharacterValues.quadraticFieldUnitsToMatrixUnits at hab
    simp only [dif_neg hn] at hab
    exact Units.ext (RingHom.injective
      (Algebra.leftMulMatrix (Module.finBasisOfFinrankEq (GaloisField p n)
      (GaloisField p (2 * n)) (RepresentationTheory.FiniteFieldMatrixCharacterValues.quadraticFiniteField_finrank p n hn))).toRingHom
      (congr_arg (fun g => g.val) hab))
  have hKc_units : Fintype.card ↥(RepresentationTheory.FiniteFieldMatrixCharacterValues.distinguishedMatrixSubgroup p n) =
      Fintype.card (GaloisField p (2 * n))ˣ := by
    rw [← Nat.card_eq_fintype_card, ← Nat.card_eq_fintype_card]
    change Nat.card ↥(RepresentationTheory.FiniteFieldMatrixCharacterValues.quadraticFieldUnitsToMatrixUnits p n).range = _
    exact Nat.card_congr ((RepresentationTheory.FiniteFieldMatrixCharacterValues.quadraticFieldUnitsToMatrixUnits p n).ofInjective hinj).symm.toEquiv
  have hq_pn : q = p ^ n := by
    rw [hq_def, ← Nat.card_eq_fintype_card, GaloisField.card p n hn]
  have hKc_nat : Fintype.card ↥(RepresentationTheory.FiniteFieldMatrixCharacterValues.distinguishedMatrixSubgroup p n) = q ^ 2 - 1 := by
    rw [hKc_units, Fintype.card_units,
      ← Nat.card_eq_fintype_card,
      GaloisField.card p (2 * n) (Nat.mul_ne_zero two_ne_zero hn)]
    congr 1
    rw [hq_pn, show 2 * n = n * 2 from by ring, pow_mul]
  have h1 : 1 ≤ q ^ 2 := by nlinarith
  have hKc_C : (Fintype.card ↥(RepresentationTheory.FiniteFieldMatrixCharacterValues.distinguishedMatrixSubgroup p n) : ℂ) =
      (q : ℂ) ^ 2 - 1 := by
    rw [hKc_nat]; push_cast [Nat.cast_sub h1]; ring
  rw [hKc_C]; ring

 
 
 
open Classical in
/-- An auxiliary result with an unavailable displayed type. -/
lemma auxiliaryTheorem
    [Fintype (GL2 p n)] [Fintype (GaloisField p n)]
    [DecidableEq (GaloisField p n)]
    (hp2 : p ≠ 2)
    (nu : (RepresentationTheory.FiniteFieldMatrixCharacterValues.distinguishedMatrixSubgroup p n) →* ℂˣ) (hn : n ≠ 0)
    (k : ↥(RepresentationTheory.FiniteFieldMatrixCharacterValues.distinguishedMatrixSubgroup p n))
    (hk_ell : RepresentationTheory.FiniteFieldUnitClassDecomposition.Auxiliary.classPredicateAlpha (p := p) (n := n) (k : GL2 p n)) :
    ∑ z : GL2 p n,
      (if h : z⁻¹ * (k : GL2 p n) * z ∈ RepresentationTheory.FiniteFieldMatrixCharacterValues.distinguishedMatrixSubgroup p n
       then (nu k : ℂ) * starRingEnd ℂ ((nu ⟨z⁻¹ * (k : GL2 p n) * z, h⟩).val)
       else 0) =
    (Fintype.card ↥(RepresentationTheory.FiniteFieldMatrixCharacterValues.distinguishedMatrixSubgroup p n) : ℂ) *
    ((1 : ℂ) + starRingEnd ℂ ((characterTransform p n nu k : ℂˣ) : ℂ)) := by
  haveI : Fintype (GaloisField p (2 * n)) := Fintype.ofFinite _
   
  have hk_ns : ¬RepresentationTheory.FiniteFieldUnitClassDecomposition.Auxiliary.classPredicateGamma (p := p) (n := n) (k : GL2 p n) :=
    fun hs => RepresentationTheory.FiniteFieldUnitClassDecomposition.not_classPredicateAlpha_of_classPredicateGamma (k : GL2 p n) hs hk_ell
   
  obtain ⟨β, hβ⟩ := k.2
   
  set N := Finset.univ.filter (fun z : GL2 p n => RepresentationTheory.GaloisFieldAuxiliary.auxiliaryPredicate p n z)
  set K_set := Finset.univ.filter (fun z : GL2 p n =>
    z ∈ RepresentationTheory.FiniteFieldMatrixCharacterValues.distinguishedMatrixSubgroup p n) with hK_set_def
  set σK_set := Finset.univ.filter (fun z : GL2 p n =>
    ∃ α : (GaloisField p (2 * n))ˣ,
      z = RepresentationTheory.GaloisFieldAuxiliary.auxiliaryElement p n * RepresentationTheory.FiniteFieldMatrixCharacterValues.quadraticFieldUnitsToMatrixUnits p n α) with hσK_set_def
   
  set F : GL2 p n → ℂ := fun z =>
    if h : z⁻¹ * (k : GL2 p n) * z ∈ RepresentationTheory.FiniteFieldMatrixCharacterValues.distinguishedMatrixSubgroup p n
    then (nu k : ℂ) * starRingEnd ℂ ((nu ⟨z⁻¹ * (k : GL2 p n) * z, h⟩).val)
    else 0 with hF_def
   
  have h_vanish : ∀ z : GL2 p n, ¬RepresentationTheory.GaloisFieldAuxiliary.auxiliaryPredicate p n z → F z = 0 := by
    intro z hz; simp only [F]
    rw [dif_neg]; intro h
    exact hz (RepresentationTheory.GaloisFieldAuxiliary.auxiliaryPredicate_of_mem_of_notAuxiliaryCondition_of_conjugate_mem p n hn hp2
      (k : GL2 p n) k.2 hk_ns z h)
   
  have h_restrict : ∑ z, F z = ∑ z ∈ N, F z := by
    symm; apply Finset.sum_subset_zero_on_sdiff (Finset.filter_subset _ _)
    · intro z hz
      simp only [Finset.mem_sdiff, Finset.mem_univ, true_and,
          Finset.mem_filter] at hz
      exact h_vanish z hz
    · intro z _; rfl
   
  have hN_eq : N = K_set ∪ σK_set := by
    ext z
    simp only [N, K_set, σK_set, Finset.mem_union, Finset.mem_filter,
      Finset.mem_univ, true_and]
    constructor
    · exact RepresentationTheory.GaloisFieldAuxiliary.mem_auxiliarySet_or_exists_auxiliaryElement_mul_of_auxiliaryPredicate p n hn hp2 z
    · rintro (hk | ⟨α, hα⟩)
      · exact RepresentationTheory.GaloisFieldAuxiliary.auxiliaryPredicate_of_mem p n z hk
      · subst hα
        exact RepresentationTheory.GaloisFieldAuxiliary.auxiliaryPredicate_auxiliaryElement_mul_of_mem p n hn _ ⟨α, rfl⟩
   
  have hKσK_disj : Disjoint K_set σK_set := by
    rw [Finset.disjoint_filter]
    intro z _ hz_K ⟨α, hα⟩
    have : RepresentationTheory.GaloisFieldAuxiliary.auxiliaryElement p n ∈ RepresentationTheory.FiniteFieldMatrixCharacterValues.distinguishedMatrixSubgroup p n := by
      obtain ⟨γ, hγ⟩ := hz_K
      rw [hα] at hγ
      have : RepresentationTheory.GaloisFieldAuxiliary.auxiliaryElement p n =
          RepresentationTheory.FiniteFieldMatrixCharacterValues.quadraticFieldUnitsToMatrixUnits p n γ * (RepresentationTheory.FiniteFieldMatrixCharacterValues.quadraticFieldUnitsToMatrixUnits p n α)⁻¹ := by
        rw [hγ]; group
      rw [this]; exact ⟨γ * α⁻¹, by rw [map_mul, map_inv]⟩
    exact RepresentationTheory.GaloisFieldAuxiliary.auxiliaryElement_not_mem_auxiliarySet p n hn this
   
  rw [h_restrict, hN_eq, Finset.sum_union hKσK_disj]
   
   
  have hK_eval : ∑ z ∈ K_set, F z =
      (Fintype.card ↥(RepresentationTheory.FiniteFieldMatrixCharacterValues.distinguishedMatrixSubgroup p n) : ℂ) := by
     
    have hK_conj : ∀ z : GL2 p n, z ∈ RepresentationTheory.FiniteFieldMatrixCharacterValues.distinguishedMatrixSubgroup p n →
        z⁻¹ * (k : GL2 p n) * z = (k : GL2 p n) := by
      intro z hz
      obtain ⟨α, rfl⟩ := hz
      obtain ⟨γ, hγ⟩ := k.2
      change (RepresentationTheory.FiniteFieldMatrixCharacterValues.quadraticFieldUnitsToMatrixUnits p n α)⁻¹ * (k : GL2 p n) *
        RepresentationTheory.FiniteFieldMatrixCharacterValues.quadraticFieldUnitsToMatrixUnits p n α = (k : GL2 p n)
      rw [show (k : GL2 p n) = RepresentationTheory.FiniteFieldMatrixCharacterValues.quadraticFieldUnitsToMatrixUnits p n γ from hγ.symm]
      simp only [← map_inv, ← map_mul, inv_mul_cancel_comm]
    have hK_mem : ∀ z : GL2 p n, z ∈ RepresentationTheory.FiniteFieldMatrixCharacterValues.distinguishedMatrixSubgroup p n →
        z⁻¹ * (k : GL2 p n) * z ∈ RepresentationTheory.FiniteFieldMatrixCharacterValues.distinguishedMatrixSubgroup p n := by
      intro z hz; rw [hK_conj z hz]; exact k.2
     
    have hterm : ∀ z ∈ K_set, F z = 1 := by
      intro z hz
      simp only [K_set, Finset.mem_filter, Finset.mem_univ, true_and] at hz
      simp only [F, dif_pos (hK_mem z hz)]
      have : (⟨z⁻¹ * (k : GL2 p n) * z, hK_mem z hz⟩ :
          ↥(RepresentationTheory.FiniteFieldMatrixCharacterValues.distinguishedMatrixSubgroup p n)) = k := by
        exact Subtype.ext (hK_conj z hz)
      rw [this]
      exact RepresentationTheory.FiniteFieldMatrixCharacterValues.characterValue_mul_star_eq_one nu k
    rw [Finset.sum_congr rfl hterm, Finset.sum_const, nsmul_eq_mul, mul_one]
     
    simp only [K_set, ← Fintype.card_subtype]
   
   
  have hσK_eval : ∑ z ∈ σK_set, F z =
      (Fintype.card ↥(RepresentationTheory.FiniteFieldMatrixCharacterValues.distinguishedMatrixSubgroup p n) : ℂ) *
      starRingEnd ℂ ((characterTransform p n nu k : ℂˣ) : ℂ) := by
     
     
     
     
    obtain ⟨γ, hγ⟩ := k.2   
     
    set kq_units : (GaloisField p (2 * n))ˣ :=
      ⟨(γ : GaloisField p (2 * n)) ^ Fintype.card (GaloisField p n),
       (γ⁻¹ : GaloisField p (2 * n)) ^ Fintype.card (GaloisField p n),
       by rw [← mul_pow]; simp ,
       by rw [← mul_pow]; simp ⟩
    have hkq_mem : RepresentationTheory.FiniteFieldMatrixCharacterValues.quadraticFieldUnitsToMatrixUnits p n kq_units ∈
        RepresentationTheory.FiniteFieldMatrixCharacterValues.distinguishedMatrixSubgroup p n := ⟨kq_units, rfl⟩
     
    have hfrob_conj : (RepresentationTheory.GaloisFieldAuxiliary.auxiliaryElement p n)⁻¹ *
        (k : GL2 p n) * RepresentationTheory.GaloisFieldAuxiliary.auxiliaryElement p n =
        RepresentationTheory.FiniteFieldMatrixCharacterValues.quadraticFieldUnitsToMatrixUnits p n kq_units := by
      rw [show (k : GL2 p n) = RepresentationTheory.FiniteFieldMatrixCharacterValues.quadraticFieldUnitsToMatrixUnits p n γ from hγ.symm]
      exact RepresentationTheory.GaloisFieldAuxiliary.conjugate_auxiliaryFunctionValue_eq_auxiliaryFunctionValue_cardPowerUnit p n hn γ
     
    have hσK_conj : ∀ α : (GaloisField p (2 * n))ˣ,
        (RepresentationTheory.GaloisFieldAuxiliary.auxiliaryElement p n * RepresentationTheory.FiniteFieldMatrixCharacterValues.quadraticFieldUnitsToMatrixUnits p n α)⁻¹ *
        (k : GL2 p n) *
        (RepresentationTheory.GaloisFieldAuxiliary.auxiliaryElement p n * RepresentationTheory.FiniteFieldMatrixCharacterValues.quadraticFieldUnitsToMatrixUnits p n α) =
        RepresentationTheory.FiniteFieldMatrixCharacterValues.quadraticFieldUnitsToMatrixUnits p n kq_units := by
      intro α
       
      have h1 : (RepresentationTheory.GaloisFieldAuxiliary.auxiliaryElement p n * RepresentationTheory.FiniteFieldMatrixCharacterValues.quadraticFieldUnitsToMatrixUnits p n α)⁻¹ *
          (k : GL2 p n) *
          (RepresentationTheory.GaloisFieldAuxiliary.auxiliaryElement p n * RepresentationTheory.FiniteFieldMatrixCharacterValues.quadraticFieldUnitsToMatrixUnits p n α) =
          (RepresentationTheory.FiniteFieldMatrixCharacterValues.quadraticFieldUnitsToMatrixUnits p n α)⁻¹ *
          ((RepresentationTheory.GaloisFieldAuxiliary.auxiliaryElement p n)⁻¹ * (k : GL2 p n) *
            RepresentationTheory.GaloisFieldAuxiliary.auxiliaryElement p n) *
          RepresentationTheory.FiniteFieldMatrixCharacterValues.quadraticFieldUnitsToMatrixUnits p n α := by group
      rw [h1, hfrob_conj, ← map_inv, ← map_mul, ← map_mul, inv_mul_cancel_comm]
     
    have hσK_mem : ∀ α : (GaloisField p (2 * n))ˣ,
        (RepresentationTheory.GaloisFieldAuxiliary.auxiliaryElement p n * RepresentationTheory.FiniteFieldMatrixCharacterValues.quadraticFieldUnitsToMatrixUnits p n α)⁻¹ *
        (k : GL2 p n) *
        (RepresentationTheory.GaloisFieldAuxiliary.auxiliaryElement p n * RepresentationTheory.FiniteFieldMatrixCharacterValues.quadraticFieldUnitsToMatrixUnits p n α) ∈
        RepresentationTheory.FiniteFieldMatrixCharacterValues.distinguishedMatrixSubgroup p n := by
      intro α; rw [hσK_conj α]; exact hkq_mem
     
     
     
     
    have hnu_kq : nu ⟨RepresentationTheory.FiniteFieldMatrixCharacterValues.quadraticFieldUnitsToMatrixUnits p n kq_units, hkq_mem⟩ =
        (nu k) ^ Fintype.card (GaloisField p n) := by
      have : ⟨RepresentationTheory.FiniteFieldMatrixCharacterValues.quadraticFieldUnitsToMatrixUnits p n kq_units, hkq_mem⟩ =
          k ^ Fintype.card (GaloisField p n) := by
        apply Subtype.ext
        change RepresentationTheory.FiniteFieldMatrixCharacterValues.quadraticFieldUnitsToMatrixUnits p n kq_units =
          (k : GL2 p n) ^ Fintype.card (GaloisField p n)
        rw [show (k : GL2 p n) = RepresentationTheory.FiniteFieldMatrixCharacterValues.quadraticFieldUnitsToMatrixUnits p n γ from hγ.symm,
          ← map_pow]
        congr 1; exact Units.ext rfl
      rw [this, map_pow]
     
    have hchar_val : (nu k : ℂ) * starRingEnd ℂ ((nu k : ℂ) ^ Fintype.card (GaloisField p n)) =
        starRingEnd ℂ ((nu k : ℂ) ^ (Fintype.card (GaloisField p n) - 1)) := by
      set v := (nu k : ℂ)
      set c := starRingEnd ℂ v
      have hvc : v * c = 1 := RepresentationTheory.FiniteFieldMatrixCharacterValues.characterValue_mul_star_eq_one nu k
      rw [map_pow, map_pow]
       
      have hq_pos : 0 < Fintype.card (GaloisField p n) := Fintype.card_pos
      rw [show Fintype.card (GaloisField p n) = Fintype.card (GaloisField p n) - 1 + 1 from
        by omega, pow_succ]
      calc v * (c ^ (Fintype.card (GaloisField p n) - 1) * c)
          = c ^ (Fintype.card (GaloisField p n) - 1) * (v * c) := by ring
        _ = c ^ (Fintype.card (GaloisField p n) - 1) * 1 := by rw [hvc]
        _ = c ^ (Fintype.card (GaloisField p n) - 1) := mul_one _
     
    have hterm : ∀ z ∈ σK_set, F z =
        starRingEnd ℂ ((characterTransform p n nu k : ℂˣ) : ℂ) := by
      intro z hz
      simp only [σK_set, Finset.mem_filter, Finset.mem_univ, true_and] at hz
      obtain ⟨α, rfl⟩ := hz
      simp only [F, dif_pos (hσK_mem α)]
       
      have hconj_eq : (⟨_ , hσK_mem α⟩ : ↥(RepresentationTheory.FiniteFieldMatrixCharacterValues.distinguishedMatrixSubgroup p n)) =
          ⟨RepresentationTheory.FiniteFieldMatrixCharacterValues.quadraticFieldUnitsToMatrixUnits p n kq_units, hkq_mem⟩ :=
        Subtype.ext (hσK_conj α)
      rw [hconj_eq, hnu_kq, Units.val_pow_eq_pow_val, hchar_val]
      congr 1  
    rw [Finset.sum_congr rfl hterm, Finset.sum_const, nsmul_eq_mul]
     
    congr 1
     
    rw [show σK_set = K_set.map ⟨(RepresentationTheory.GaloisFieldAuxiliary.auxiliaryElement p n * ·),
        mul_right_injective _⟩ from by
      ext z; simp only [σK_set, K_set, Finset.mem_filter, Finset.mem_univ, true_and,
        Finset.mem_map, Function.Embedding.coeFn_mk]
      constructor
      · rintro ⟨α, rfl⟩
        exact ⟨RepresentationTheory.FiniteFieldMatrixCharacterValues.quadraticFieldUnitsToMatrixUnits p n α, ⟨α, rfl⟩, rfl⟩
      · rintro ⟨w, ⟨α, rfl⟩, rfl⟩
        exact ⟨α, rfl⟩]
    rw [Finset.card_map]
    simp only [K_set, ← Fintype.card_subtype]
   
  rw [hK_eval, hσK_eval]; ring

 
 
 
 
 
 
 
 
open Classical in
private lemma elliptic_sum_algebraic_core
    [Fintype (GL2 p n)] [Fintype (GaloisField p n)]
    [DecidableEq (GaloisField p n)]
    (hp2 : p ≠ 2)
    (nu : (RepresentationTheory.FiniteFieldMatrixCharacterValues.distinguishedMatrixSubgroup p n) →* ℂˣ) (hn : n ≠ 0)
    (hnu_ne : ∃ k : ↥(RepresentationTheory.FiniteFieldMatrixCharacterValues.distinguishedMatrixSubgroup p n),
      (nu k) ^ Fintype.card (GaloisField p n) ≠ nu k) :
    ∑ g ∈ Finset.univ.filter (fun g : GL2 p n => RepresentationTheory.FiniteFieldUnitClassDecomposition.Auxiliary.classPredicateAlpha (p := p) (n := n) g),
      (∑ x : GL2 p n,
        if h : x⁻¹ * g * x ∈ RepresentationTheory.FiniteFieldMatrixCharacterValues.distinguishedMatrixSubgroup p n
        then (nu ⟨x⁻¹ * g * x, h⟩).val else 0) *
      starRingEnd ℂ (∑ x : GL2 p n,
        if h : x⁻¹ * g * x ∈ RepresentationTheory.FiniteFieldMatrixCharacterValues.distinguishedMatrixSubgroup p n
        then (nu ⟨x⁻¹ * g * x, h⟩).val else 0) =
    (Fintype.card (GL2 p n) : ℂ) *
    (Fintype.card ↥(RepresentationTheory.FiniteFieldMatrixCharacterValues.distinguishedMatrixSubgroup p n) : ℂ) *
    ∑ k : ↥(RepresentationTheory.FiniteFieldMatrixCharacterValues.distinguishedMatrixSubgroup p n),
      (if RepresentationTheory.FiniteFieldUnitClassDecomposition.Auxiliary.classPredicateAlpha (p := p) (n := n) (k : GL2 p n)
       then (1 : ℂ) + starRingEnd ℂ ((characterTransform p n nu k : ℂˣ) : ℂ)
       else 0) := by
   
   
   
   
  have hreindex :
    ∑ g ∈ Finset.univ.filter (fun g : GL2 p n => RepresentationTheory.FiniteFieldUnitClassDecomposition.Auxiliary.classPredicateAlpha (p := p) (n := n) g),
      (∑ x : GL2 p n,
        if h : x⁻¹ * g * x ∈ RepresentationTheory.FiniteFieldMatrixCharacterValues.distinguishedMatrixSubgroup p n
        then (nu ⟨x⁻¹ * g * x, h⟩).val else 0) *
      starRingEnd ℂ (∑ x : GL2 p n,
        if h : x⁻¹ * g * x ∈ RepresentationTheory.FiniteFieldMatrixCharacterValues.distinguishedMatrixSubgroup p n
        then (nu ⟨x⁻¹ * g * x, h⟩).val else 0) =
    (Fintype.card (GL2 p n) : ℂ) *
    ∑ k : ↥(RepresentationTheory.FiniteFieldMatrixCharacterValues.distinguishedMatrixSubgroup p n),
      (if RepresentationTheory.FiniteFieldUnitClassDecomposition.Auxiliary.classPredicateAlpha (p := p) (n := n) (k : GL2 p n)
       then ∑ z : GL2 p n,
         (if h : z⁻¹ * (k : GL2 p n) * z ∈ RepresentationTheory.FiniteFieldMatrixCharacterValues.distinguishedMatrixSubgroup p n
          then (nu k : ℂ) * starRingEnd ℂ ((nu ⟨z⁻¹ * (k : GL2 p n) * z, h⟩).val)
          else 0)
       else 0) := by
     
     
     
     
    have hcc : ∀ (a b : GL2 p n), a⁻¹ * (a * b * a⁻¹) * a = b := by intros; group
    have hcc2 : ∀ (a b c : GL2 p n),
        (a * b)⁻¹ * (a * c * a⁻¹) * (a * b) = b⁻¹ * c * b := by intros; group
     
    have hdisc' : ∀ (a b : GL2 p n), RepresentationTheory.FiniteFieldUnitClassDecomposition.Auxiliary.entryDiscriminant (a * b * a⁻¹) = RepresentationTheory.FiniteFieldUnitClassDecomposition.Auxiliary.entryDiscriminant b := by
      intro a b
      conv_lhs => rw [show a * b * a⁻¹ = a⁻¹⁻¹ * b * a⁻¹ from by simp]
      exact RepresentationTheory.FiniteFieldMatrixCharacterValues.matrixInvariant_conj p n b a⁻¹
    have hIsEll : ∀ (a b : GL2 p n),
        RepresentationTheory.FiniteFieldUnitClassDecomposition.Auxiliary.classPredicateAlpha (p := p) (n := n) (a * b * a⁻¹) ↔
        RepresentationTheory.FiniteFieldUnitClassDecomposition.Auxiliary.classPredicateAlpha (p := p) (n := n) b := by
      intro a b; simp only [RepresentationTheory.FiniteFieldUnitClassDecomposition.Auxiliary.classPredicateAlpha, hdisc']
     
     
     
    have hS_conj : ∀ (g a : GL2 p n),
        (∑ x : GL2 p n,
          if h : x⁻¹ * (a⁻¹ * g * a) * x ∈ RepresentationTheory.FiniteFieldMatrixCharacterValues.distinguishedMatrixSubgroup p n
          then (nu ⟨x⁻¹ * (a⁻¹ * g * a) * x, h⟩).val else 0) =
        (∑ x : GL2 p n,
          if h : x⁻¹ * g * x ∈ RepresentationTheory.FiniteFieldMatrixCharacterValues.distinguishedMatrixSubgroup p n
          then (nu ⟨x⁻¹ * g * x, h⟩).val else 0) := by
      intro g a
      refine Fintype.sum_equiv (Equiv.mulLeft a) _ _ ?_
      intro x; simp only [Equiv.coe_mulLeft]
      have key : x⁻¹ * (a⁻¹ * g * a) * x = (a * x)⁻¹ * g * (a * x) := by group
      simp_rw [key]
     
     
    simp_rw [map_sum (starRingEnd ℂ), apply_dite (starRingEnd ℂ), map_zero,
             Fintype.sum_mul_sum]
    rw [Finset.sum_comm]
     
     
     
    have hreindex_inner : ∀ (x : GL2 p n),
        (∑ g ∈ Finset.univ.filter (fun g : GL2 p n =>
            RepresentationTheory.FiniteFieldUnitClassDecomposition.Auxiliary.classPredicateAlpha (p := p) (n := n) g),
          ∑ y : GL2 p n,
            (if hx : x⁻¹ * g * x ∈ RepresentationTheory.FiniteFieldMatrixCharacterValues.distinguishedMatrixSubgroup p n
             then (nu ⟨x⁻¹ * g * x, hx⟩).val else 0) *
            (if hy : y⁻¹ * g * y ∈ RepresentationTheory.FiniteFieldMatrixCharacterValues.distinguishedMatrixSubgroup p n
             then starRingEnd ℂ ((nu ⟨y⁻¹ * g * y, hy⟩).val) else 0)) =
        (∑ k ∈ Finset.univ.filter (fun k : GL2 p n =>
            RepresentationTheory.FiniteFieldUnitClassDecomposition.Auxiliary.classPredicateAlpha (p := p) (n := n) k),
          ∑ z : GL2 p n,
            (if hk : k ∈ RepresentationTheory.FiniteFieldMatrixCharacterValues.distinguishedMatrixSubgroup p n
             then (nu ⟨k, hk⟩).val else 0) *
            (if hz : z⁻¹ * k * z ∈ RepresentationTheory.FiniteFieldMatrixCharacterValues.distinguishedMatrixSubgroup p n
             then starRingEnd ℂ ((nu ⟨z⁻¹ * k * z, hz⟩).val) else 0)) := by
      intro x
       
       
      refine Finset.sum_equiv ((MulAut.conj x⁻¹).toEquiv) (fun g => ?_) (fun g _ => ?_)
      ·  
        simp only [Finset.mem_filter, Finset.mem_univ, true_and,
                    MulEquiv.toEquiv_eq_coe, MulEquiv.coe_toEquiv, MulAut.conj_apply, inv_inv]
        exact (hIsEll x⁻¹ g).symm
      ·  
         
        simp only [MulEquiv.toEquiv_eq_coe, MulEquiv.coe_toEquiv, MulAut.conj_apply, inv_inv]
         
         
         
        refine Fintype.sum_equiv (Equiv.mulLeft x⁻¹) _ _ ?_
        intro y; simp only [Equiv.coe_mulLeft]
        have h_grp : (x⁻¹ * y)⁻¹ * (x⁻¹ * g * x) * (x⁻¹ * y) = y⁻¹ * g * y := by group
        simp_rw [h_grp]
    simp_rw [hreindex_inner]
     
    rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
     
     
    congr 1
     
     
     
     
     
    rw [Finset.sum_filter]
     
    symm
    apply (Finset.sum_congr_set
      (RepresentationTheory.FiniteFieldMatrixCharacterValues.distinguishedMatrixSubgroup p n).carrier
      (fun (k : GL2 p n) =>
        if RepresentationTheory.FiniteFieldUnitClassDecomposition.Auxiliary.classPredicateAlpha (p := p) (n := n) k then
          ∑ z : GL2 p n,
            (if hk : k ∈ RepresentationTheory.FiniteFieldMatrixCharacterValues.distinguishedMatrixSubgroup p n then (nu ⟨k, hk⟩ : ℂˣ).val else 0) *
            (if hz : z⁻¹ * k * z ∈ RepresentationTheory.FiniteFieldMatrixCharacterValues.distinguishedMatrixSubgroup p n
             then starRingEnd ℂ ((nu ⟨z⁻¹ * k * z, hz⟩ : ℂˣ).val) else 0)
        else (0 : ℂ))
      (fun (k : ↥(RepresentationTheory.FiniteFieldMatrixCharacterValues.distinguishedMatrixSubgroup p n)) =>
        if RepresentationTheory.FiniteFieldUnitClassDecomposition.Auxiliary.classPredicateAlpha (p := p) (n := n) (k : GL2 p n) then
          ∑ z : GL2 p n,
            if h : z⁻¹ * (k : GL2 p n) * z ∈ RepresentationTheory.FiniteFieldMatrixCharacterValues.distinguishedMatrixSubgroup p n
            then (nu k : ℂˣ).val * starRingEnd ℂ ((nu ⟨z⁻¹ * (k : GL2 p n) * z, h⟩ : ℂˣ).val)
            else (0 : ℂ)
        else (0 : ℂ))
      ?_ ?_).symm
    ·  
      intro k hk
      have hk' : k ∈ RepresentationTheory.FiniteFieldMatrixCharacterValues.distinguishedMatrixSubgroup p n := hk
      simp only []
      split_ifs with hell
      ·  
         
        congr 1; ext z
        split_ifs with hz
        · rfl
        · exact mul_zero _
      · rfl
    ·  
      intro k hk
      have hk' : k ∉ RepresentationTheory.FiniteFieldMatrixCharacterValues.distinguishedMatrixSubgroup p n := hk
       
       
      split_ifs with hell
      · apply Finset.sum_eq_zero; intro z _
        simp only [zero_mul]
      · rfl
   
   
   
   
   
  have hnorm_eval : ∀ (k : ↥(RepresentationTheory.FiniteFieldMatrixCharacterValues.distinguishedMatrixSubgroup p n)),
    RepresentationTheory.FiniteFieldUnitClassDecomposition.Auxiliary.classPredicateAlpha (p := p) (n := n) (k : GL2 p n) →
    ∑ z : GL2 p n,
      (if h : z⁻¹ * (k : GL2 p n) * z ∈ RepresentationTheory.FiniteFieldMatrixCharacterValues.distinguishedMatrixSubgroup p n
       then (nu k : ℂ) * starRingEnd ℂ ((nu ⟨z⁻¹ * (k : GL2 p n) * z, h⟩).val)
       else 0) =
    (Fintype.card ↥(RepresentationTheory.FiniteFieldMatrixCharacterValues.distinguishedMatrixSubgroup p n) : ℂ) *
    ((1 : ℂ) + starRingEnd ℂ ((characterTransform p n nu k : ℂˣ) : ℂ)) :=
    fun k hk => auxiliaryTheorem p n hp2 nu hn k hk
   
  rw [hreindex]
   
  have hinner : ∀ k : ↥(RepresentationTheory.FiniteFieldMatrixCharacterValues.distinguishedMatrixSubgroup p n),
    (if RepresentationTheory.FiniteFieldUnitClassDecomposition.Auxiliary.classPredicateAlpha (p := p) (n := n) (k : GL2 p n)
     then ∑ z : GL2 p n,
       (if h : z⁻¹ * (k : GL2 p n) * z ∈ RepresentationTheory.FiniteFieldMatrixCharacterValues.distinguishedMatrixSubgroup p n
        then (nu k : ℂ) * starRingEnd ℂ ((nu ⟨z⁻¹ * (k : GL2 p n) * z, h⟩).val)
        else 0)
     else 0) =
    (Fintype.card ↥(RepresentationTheory.FiniteFieldMatrixCharacterValues.distinguishedMatrixSubgroup p n) : ℂ) *
    (if RepresentationTheory.FiniteFieldUnitClassDecomposition.Auxiliary.classPredicateAlpha (p := p) (n := n) (k : GL2 p n)
     then (1 : ℂ) + starRingEnd ℂ ((characterTransform p n nu k : ℂˣ) : ℂ)
     else 0) := by
    intro k; split_ifs with hk
    · exact hnorm_eval k hk
    · simp
  simp_rw [hinner, ← Finset.mul_sum]
  ring

open Classical in
 















private lemma induced_normSq_sum_elliptic
    [Fintype (GL2 p n)] [Fintype (GaloisField p n)]
    [DecidableEq (GaloisField p n)]
    (hp2 : p ≠ 2)
    (nu : (RepresentationTheory.FiniteFieldMatrixCharacterValues.distinguishedMatrixSubgroup p n) →* ℂˣ) (hn : n ≠ 0)
    (hnu_ne : ∃ k : ↥(RepresentationTheory.FiniteFieldMatrixCharacterValues.distinguishedMatrixSubgroup p n),
      (nu k) ^ Fintype.card (GaloisField p n) ≠ nu k) :
    ∑ g ∈ Finset.univ.filter (fun g : GL2 p n => RepresentationTheory.FiniteFieldUnitClassDecomposition.Auxiliary.classPredicateAlpha (p := p) (n := n) g),
      ((Fintype.card ↥(RepresentationTheory.FiniteFieldMatrixCharacterValues.distinguishedMatrixSubgroup p n) : ℂ)⁻¹ *
        ∑ x : GL2 p n,
          if h : x⁻¹ * g * x ∈ RepresentationTheory.FiniteFieldMatrixCharacterValues.distinguishedMatrixSubgroup p n
          then (nu ⟨x⁻¹ * g * x, h⟩).val
          else 0) *
      starRingEnd ℂ ((Fintype.card ↥(RepresentationTheory.FiniteFieldMatrixCharacterValues.distinguishedMatrixSubgroup p n) : ℂ)⁻¹ *
        ∑ x : GL2 p n,
          if h : x⁻¹ * g * x ∈ RepresentationTheory.FiniteFieldMatrixCharacterValues.distinguishedMatrixSubgroup p n
          then (nu ⟨x⁻¹ * g * x, h⟩).val
          else 0) =
    (Fintype.card (GaloisField p n) : ℂ) *
    ((Fintype.card (GaloisField p n) : ℂ) - 1) ^ 3 := by
   
   
  have h_factor : ∀ (S : ℂ),
      ((Fintype.card ↥(RepresentationTheory.FiniteFieldMatrixCharacterValues.distinguishedMatrixSubgroup p n) : ℂ)⁻¹ * S) *
      starRingEnd ℂ ((Fintype.card ↥(RepresentationTheory.FiniteFieldMatrixCharacterValues.distinguishedMatrixSubgroup p n) : ℂ)⁻¹ * S) =
      (Fintype.card ↥(RepresentationTheory.FiniteFieldMatrixCharacterValues.distinguishedMatrixSubgroup p n) : ℂ)⁻¹ ^ 2 *
      (S * starRingEnd ℂ S) := by
    intro S; simp only [map_mul, map_inv₀, Complex.conj_natCast]; ring
  simp_rw [h_factor, ← Finset.mul_sum]
   
   
   
   
   
   
   
   
   
   
   
   
   
  have hraw : ∑ g ∈ Finset.univ.filter (fun g : GL2 p n => RepresentationTheory.FiniteFieldUnitClassDecomposition.Auxiliary.classPredicateAlpha (p := p) (n := n) g),
      (∑ x : GL2 p n,
        if h : x⁻¹ * g * x ∈ RepresentationTheory.FiniteFieldMatrixCharacterValues.distinguishedMatrixSubgroup p n
        then (nu ⟨x⁻¹ * g * x, h⟩).val else 0) *
      starRingEnd ℂ (∑ x : GL2 p n,
        if h : x⁻¹ * g * x ∈ RepresentationTheory.FiniteFieldMatrixCharacterValues.distinguishedMatrixSubgroup p n
        then (nu ⟨x⁻¹ * g * x, h⟩).val else 0) =
    (Fintype.card (GL2 p n) : ℂ) *
    (Fintype.card ↥(RepresentationTheory.FiniteFieldMatrixCharacterValues.distinguishedMatrixSubgroup p n) : ℂ) *
    ((Fintype.card (GaloisField p n) : ℂ) - 1) ^ 2 := by
     
     
     
     
     
     
     
     
     
     
     
     
     
     
     
     
     
     
     
     
     
     
     
    rw [elliptic_sum_algebraic_core p n hp2 nu hn hnu_ne,
        nonscalar_char_sum p n hp2 nu hn hnu_ne]
  rw [hraw]
   
   
   
  set q := Fintype.card (GaloisField p n) with hq_def
  have hq_pos : 1 < q := by
    rw [hq_def, ← Nat.card_eq_fintype_card, GaloisField.card p n hn]
    exact Nat.one_lt_pow hn hp.out.one_lt
  have hinj : Function.Injective (RepresentationTheory.FiniteFieldMatrixCharacterValues.quadraticFieldUnitsToMatrixUnits p n) := by
    intro a b hab
    unfold RepresentationTheory.FiniteFieldMatrixCharacterValues.quadraticFieldUnitsToMatrixUnits at hab
    simp only [dif_neg hn] at hab
    exact Units.ext (RingHom.injective
      (Algebra.leftMulMatrix (Module.finBasisOfFinrankEq (GaloisField p n)
      (GaloisField p (2 * n)) (RepresentationTheory.FiniteFieldMatrixCharacterValues.quadraticFiniteField_finrank p n hn))).toRingHom
      (congr_arg (fun g => g.val) hab))
  haveI : Fintype (GaloisField p (2 * n)) := Fintype.ofFinite _
   
  have hKc_units : Fintype.card ↥(RepresentationTheory.FiniteFieldMatrixCharacterValues.distinguishedMatrixSubgroup p n) =
      Fintype.card (GaloisField p (2 * n))ˣ := by
    rw [← Nat.card_eq_fintype_card, ← Nat.card_eq_fintype_card]
    change Nat.card ↥(RepresentationTheory.FiniteFieldMatrixCharacterValues.quadraticFieldUnitsToMatrixUnits p n).range = _
    exact Nat.card_congr ((RepresentationTheory.FiniteFieldMatrixCharacterValues.quadraticFieldUnitsToMatrixUnits p n).ofInjective hinj).symm.toEquiv
   
  have hq_pn : q = p ^ n := by
    rw [hq_def, ← Nat.card_eq_fintype_card, GaloisField.card p n hn]
  have hKc_nat : Fintype.card ↥(RepresentationTheory.FiniteFieldMatrixCharacterValues.distinguishedMatrixSubgroup p n) = q ^ 2 - 1 := by
    rw [hKc_units, Fintype.card_units,
      ← Nat.card_eq_fintype_card,
      GaloisField.card p (2 * n) (Nat.mul_ne_zero two_ne_zero hn)]
    congr 1
    rw [hq_pn, show 2 * n = n * 2 from by ring, pow_mul]
   
  have hGc_nat : Fintype.card (GL2 p n) = (q ^ 2 - 1) * (q ^ 2 - q) := by
    have := @Matrix.card_GL_field (GaloisField p n) _ _ 2
    simp only [Fin.prod_univ_two, Fin.val_zero, Fin.val_one, pow_zero, pow_one,
               ← Nat.card_eq_fintype_card] at this
    rw [← Nat.card_eq_fintype_card, this, Nat.card_eq_fintype_card]
   
  have h1 : 1 ≤ q ^ 2 := by nlinarith
  have h2 : q ≤ q ^ 2 := by nlinarith
  have hKc_C : (Fintype.card ↥(RepresentationTheory.FiniteFieldMatrixCharacterValues.distinguishedMatrixSubgroup p n) : ℂ) =
      (q : ℂ) ^ 2 - 1 := by
    rw [hKc_nat]; push_cast [Nat.cast_sub h1]; ring
  have hGc_C : (Fintype.card (GL2 p n) : ℂ) =
      ((q : ℂ) ^ 2 - 1) * ((q : ℂ) ^ 2 - (q : ℂ)) := by
    rw [hGc_nat, Nat.cast_mul]; push_cast [Nat.cast_sub h1, Nat.cast_sub h2]; ring
  have hKc_ne : (Fintype.card ↥(RepresentationTheory.FiniteFieldMatrixCharacterValues.distinguishedMatrixSubgroup p n) : ℂ) ≠ 0 := by
    exact_mod_cast Fintype.card_pos (α := ↥(RepresentationTheory.FiniteFieldMatrixCharacterValues.distinguishedMatrixSubgroup p n)).ne'
  rw [hGc_C, hKc_C]
  have hq2_ne : (q : ℂ) ^ 2 - 1 ≠ 0 := by rw [← hKc_C]; exact hKc_ne
  field_simp

open Classical in
 





private lemma elliptic_contribution
    [Fintype (GL2 p n)] [Fintype (GaloisField p n)]
    [DecidableEq (GaloisField p n)]
    (hp2 : p ≠ 2)
    (nu : (RepresentationTheory.FiniteFieldMatrixCharacterValues.distinguishedMatrixSubgroup p n) →* ℂˣ) (hn : n ≠ 0)
    (hnu_ne : ∃ k : ↥(RepresentationTheory.FiniteFieldMatrixCharacterValues.distinguishedMatrixSubgroup p n),
      (nu k) ^ Fintype.card (GaloisField p n) ≠ nu k) :
    ∑ g ∈ Finset.univ.filter (fun g : GL2 p n => RepresentationTheory.FiniteFieldUnitClassDecomposition.Auxiliary.classPredicateAlpha (p := p) (n := n) g),
      RepresentationTheory.FiniteFieldMatrixCharacterValues.subgroupCharacterMatrixFunction p n nu g *
      starRingEnd ℂ (RepresentationTheory.FiniteFieldMatrixCharacterValues.subgroupCharacterMatrixFunction p n nu g) =
    (Fintype.card (GaloisField p n) : ℂ) *
    ((Fintype.card (GaloisField p n) : ℂ) - 1) ^ 3 := by
   
  have hconv : ∀ g ∈ Finset.univ.filter
      (fun g : GL2 p n => RepresentationTheory.FiniteFieldUnitClassDecomposition.Auxiliary.classPredicateAlpha (p := p) (n := n) g),
      RepresentationTheory.FiniteFieldMatrixCharacterValues.subgroupCharacterMatrixFunction p n nu g *
      starRingEnd ℂ (RepresentationTheory.FiniteFieldMatrixCharacterValues.subgroupCharacterMatrixFunction p n nu g) =
      ((Fintype.card ↥(RepresentationTheory.FiniteFieldMatrixCharacterValues.distinguishedMatrixSubgroup p n) : ℂ)⁻¹ *
        ∑ x : GL2 p n,
          if h : x⁻¹ * g * x ∈ RepresentationTheory.FiniteFieldMatrixCharacterValues.distinguishedMatrixSubgroup p n
          then (nu ⟨x⁻¹ * g * x, h⟩).val else 0) *
      starRingEnd ℂ ((Fintype.card ↥(RepresentationTheory.FiniteFieldMatrixCharacterValues.distinguishedMatrixSubgroup p n) : ℂ)⁻¹ *
        ∑ x : GL2 p n,
          if h : x⁻¹ * g * x ∈ RepresentationTheory.FiniteFieldMatrixCharacterValues.distinguishedMatrixSubgroup p n
          then (nu ⟨x⁻¹ * g * x, h⟩).val else 0) := by
    intro g hg
    rw [Finset.mem_filter] at hg
    rw [complementarySeriesChar_elliptic_eq p n nu g hg.2]
    simp only [map_neg, neg_mul, mul_neg, neg_neg]
  rw [Finset.sum_congr rfl hconv]
   
  exact induced_normSq_sum_elliptic p n hp2 nu hn hnu_ne

 


private lemma innerProduct_arith_identity (q : ℂ) :
    (q - 1) ^ 3 + (q - 1) * (q ^ 2 - 1) + q * (q - 1) ^ 3 =
    (q ^ 2 - 1) * (q ^ 2 - q) := by
  ring

 










private lemma innerProduct_sum_eq_card
    [Fintype (GaloisField p n)] [DecidableEq (GaloisField p n)]
    [Fintype (GL2 p n)]
    (hp2 : p ≠ 2)
    (nu : (RepresentationTheory.FiniteFieldMatrixCharacterValues.distinguishedMatrixSubgroup p n) →* ℂˣ) (hn : 0 < n)
    (hnu_ne : ∃ k : ↥(RepresentationTheory.FiniteFieldMatrixCharacterValues.distinguishedMatrixSubgroup p n),
      (nu k) ^ Fintype.card (GaloisField p n) ≠ nu k) :
    (∑ x : GL2 p n,
      RepresentationTheory.FiniteFieldMatrixCharacterValues.subgroupCharacterMatrixFunction p n nu x *
      starRingEnd ℂ (RepresentationTheory.FiniteFieldMatrixCharacterValues.subgroupCharacterMatrixFunction p n nu x) : ℂ) =
    (Fintype.card (GL2 p n) : ℂ) := by
  have hn_ne : n ≠ 0 := by omega
  set q := Fintype.card (GaloisField p n) with hq_def
  have hq1 : 1 < q := by
    rw [hq_def, ← Nat.card_eq_fintype_card, GaloisField.card p n hn_ne]
    exact Nat.one_lt_pow hn_ne hp.out.one_lt
   
  have hG : Fintype.card (GL2 p n) = (q ^ 2 - 1) * (q ^ 2 - q) := by
    have := @Matrix.card_GL_field (GaloisField p n) _ _ 2
    simp only [Fin.prod_univ_two, Fin.val_zero, Fin.val_one, pow_zero, pow_one,
               ← Nat.card_eq_fintype_card] at this
    rw [← Nat.card_eq_fintype_card, this, Nat.card_eq_fintype_card]
   
  set χ := RepresentationTheory.FiniteFieldMatrixCharacterValues.subgroupCharacterMatrixFunction p n nu
  set f : GL2 p n → ℂ := fun g => χ g * starRingEnd ℂ (χ g)
   
  have hsplit := RepresentationTheory.FiniteFieldUnitClassDecomposition.sum_eq_sum_classPredicateFilters (p := p) (n := n) f
  rw [hsplit]
   
   
  have h_scalar : ∑ g ∈ Finset.univ.filter (fun g => RepresentationTheory.FiniteFieldUnitClassDecomposition.Auxiliary.classPredicateGamma g), f g =
      ((q : ℂ) - 1) ^ 3 := by
    have hval : ∀ g ∈ Finset.univ.filter (fun g => RepresentationTheory.FiniteFieldUnitClassDecomposition.Auxiliary.classPredicateGamma (p := p) (n := n) g),
        f g = ((q : ℂ) - 1) ^ 2 := fun g hg => by
      rw [Finset.mem_filter] at hg
      exact RepresentationTheory.FiniteFieldMatrixCharacterValues.subgroupCharacterMatrixFunction_mul_star_eq_card_sub_one_sq p n nu hn_ne g hg.2
    rw [Finset.sum_congr rfl hval, Finset.sum_const, RepresentationTheory.FiniteFieldUnitClassDecomposition.card_classPredicateGamma hn_ne, nsmul_eq_mul]
    have h1 : 1 ≤ q := by omega
    rw [show Fintype.card (GaloisField p n) = q from hq_def.symm]
    push_cast [Nat.cast_sub h1]; ring
   
  have h_parabolic : ∑ g ∈ Finset.univ.filter (fun g => RepresentationTheory.FiniteFieldUnitClassDecomposition.Auxiliary.classPredicateBeta g), f g =
      ((q : ℂ) - 1) * ((q : ℂ) ^ 2 - 1) := by
    have hval : ∀ g ∈ Finset.univ.filter (fun g => RepresentationTheory.FiniteFieldUnitClassDecomposition.Auxiliary.classPredicateBeta (p := p) (n := n) g),
        f g = 1 := fun g hg => by
      rw [Finset.mem_filter] at hg
      exact RepresentationTheory.FiniteFieldMatrixCharacterValues.subgroupCharacterMatrixFunction_mul_star_eq_one p n hp2 nu g hg.2
    rw [Finset.sum_congr rfl hval, Finset.sum_const, RepresentationTheory.FiniteFieldUnitClassDecomposition.card_classPredicateBeta hp2 hn_ne, nsmul_eq_mul,
      mul_one]
    have h1 : 1 ≤ q := by omega
    have h2 : 1 ≤ q ^ 2 := by nlinarith
    rw [show Fintype.card (GaloisField p n) = q from hq_def.symm]
    push_cast [Nat.cast_sub h1, Nat.cast_sub h2]; ring
   
  have h_split : ∑ g ∈ Finset.univ.filter (fun g => RepresentationTheory.FiniteFieldUnitClassDecomposition.Auxiliary.classPredicateDelta g), f g = 0 := by
    apply Finset.sum_eq_zero; intro g hg
    rw [Finset.mem_filter] at hg
    have h0 : χ g = 0 := RepresentationTheory.FiniteFieldMatrixCharacterValues.subgroupCharacterMatrixFunction_eq_zero_of_auxiliaryProperty p n hp2 nu g hg.2
    change χ g * starRingEnd ℂ (χ g) = 0
    rw [h0, map_zero, mul_zero]
   
  have h_elliptic : ∑ g ∈ Finset.univ.filter (fun g => RepresentationTheory.FiniteFieldUnitClassDecomposition.Auxiliary.classPredicateAlpha g), f g =
      (q : ℂ) * ((q : ℂ) - 1) ^ 3 :=
    elliptic_contribution p n hp2 nu hn_ne hnu_ne
   
  rw [h_scalar, h_parabolic, h_split, h_elliptic, hG]
  have h1 : 1 ≤ q := by omega
  have h2 : 1 ≤ q ^ 2 := by nlinarith
  have h3 : q ≤ q ^ 2 := by nlinarith
  push_cast [Nat.cast_sub h1, Nat.cast_sub h2, Nat.cast_sub h3]; ring

 


/-- Shows that the normalized sum of each auxiliary value multiplied by its complex conjugate is one under the stated nontriviality condition. -/
@[source_ref "Chapter5/Lemma5.25.3" (role := primary)]
theorem normalized_sum_auxiliaryValue_mul_star_eq_one
    [Fintype (GaloisField p n)] [DecidableEq (GaloisField p n)]
    [Fintype (GL2 p n)]
    (hp2 : p ≠ 2)
    (nu : (RepresentationTheory.FiniteFieldMatrixCharacterValues.distinguishedMatrixSubgroup p n) →* ℂˣ) (hn : 0 < n)
    (hnu_ne : ∃ k : ↥(RepresentationTheory.FiniteFieldMatrixCharacterValues.distinguishedMatrixSubgroup p n),
      (nu k) ^ Fintype.card (GaloisField p n) ≠ nu k) :
    (Fintype.card (GL2 p n) : ℂ)⁻¹ •
      ∑ x : GL2 p n,
        RepresentationTheory.FiniteFieldMatrixCharacterValues.subgroupCharacterMatrixFunction p n nu x *
        starRingEnd ℂ (RepresentationTheory.FiniteFieldMatrixCharacterValues.subgroupCharacterMatrixFunction p n nu x) = 1 := by
  rw [innerProduct_sum_eq_card p n hp2 nu hn hnu_ne]
  simp only [smul_eq_mul]
  have hcard : (Fintype.card (GL2 p n) : ℂ) ≠ 0 := by
    exact_mod_cast Fintype.card_pos.ne'
  exact inv_mul_cancel₀ hcard

 


private lemma charW₁_one
    [Fintype (GaloisField p n)] [DecidableEq (GaloisField p n)] :
    RepresentationTheory.FiniteFieldMatrixCharacterValues.distinguishedMatrixUnitFunction p n 1 =
      (Fintype.card (GaloisField p n) : ℂ) := by
  unfold RepresentationTheory.FiniteFieldMatrixCharacterValues.distinguishedMatrixUnitFunction
  simp only [Matrix.GeneralLinearGroup.coe_one, Matrix.one_apply]
  norm_num

private lemma dimension_arith_identity
    (q : ℂ) (hq : q ≠ 0) (hq1 : q - 1 ≠ 0) (hqp1 : q + 1 ≠ 0) :
    q * (q⁻¹ * ((q - 1) ^ 2)⁻¹ * ((q ^ 2 - 1) * (q ^ 2 - q))) -
    q⁻¹ * ((q - 1) ^ 2)⁻¹ * ((q ^ 2 - 1) * (q ^ 2 - q)) -
    (q ^ 2 - 1)⁻¹ * ((q ^ 2 - 1) * (q ^ 2 - q)) = q - 1 := by
  have hq2m1 : q ^ 2 - 1 ≠ 0 := by
    have : q ^ 2 - 1 = (q - 1) * (q + 1) := by ring
    rw [this]; exact mul_ne_zero hq1 hqp1
  have hqm1sq : (q - 1) ^ 2 ≠ 0 := pow_ne_zero 2 hq1
  field_simp [hq, hq1, hqp1, hq2m1, hqm1sq]
  ring

/-- Evaluates the auxiliary complex-valued quantity at one as p raised to n minus one and proves that this difference is positive. -/
@[source_ref "Chapter5/Lemma5.25.3" (role := primary)]
theorem auxiliaryValue_one_eq_pow_sub_one_and_pos
    [Fintype (GaloisField p n)] [DecidableEq (GaloisField p n)]
    [Fintype (GL2 p n)]
    (nu : (RepresentationTheory.FiniteFieldMatrixCharacterValues.distinguishedMatrixSubgroup p n) →* ℂˣ) (hn : 0 < n) :
    RepresentationTheory.FiniteFieldMatrixCharacterValues.subgroupCharacterMatrixFunction p n nu 1 = (p ^ n : ℂ) - 1 ∧
    (0 : ℝ) < (p ^ n : ℝ) - 1 := by
  constructor
  ·  
     
    have h1x : ∀ x : GL2 p n, x⁻¹ * 1 * x = 1 := by intro x; simp
     
    change RepresentationTheory.FiniteFieldMatrixCharacterValues.subgroupCharacterMatrixFunction p n nu 1 = (p ^ n : ℂ) - 1
    unfold RepresentationTheory.FiniteFieldMatrixCharacterValues.subgroupCharacterMatrixFunction RepresentationTheory.FiniteFieldMatrixCharacterValues.distinguishedMatrixUnitFunction RepresentationTheory.FiniteFieldMatrixCharacterValues.multiplicativeCharacterMatrixFunction
    simp only [Matrix.GeneralLinearGroup.coe_one, Matrix.one_apply, h1x]
     
    have hnu_sub : ∀ h, nu (⟨1, h⟩ : ↥(RepresentationTheory.FiniteFieldMatrixCharacterValues.distinguishedMatrixSubgroup p n)) = 1 :=
      fun h => (congrArg nu (Subtype.ext rfl)).trans (map_one nu)
    simp only [hnu_sub, Units.val_one]
     
    norm_num
     
     
     
     
     
     
     
     
     
     
     
     
    simp only [← Nat.card_eq_fintype_card]
    have hn_ne : n ≠ 0 := by omega
    have hq_val : Nat.card (GaloisField p n) = p ^ n := GaloisField.card p n hn_ne
    have hq1 : 1 < Nat.card (GaloisField p n) := by
      rw [hq_val]; exact Nat.one_lt_pow hn_ne hp.out.one_lt
     
    have hG : Nat.card (GL2 p n) =
        (Nat.card (GaloisField p n) ^ 2 - 1) *
        (Nat.card (GaloisField p n) ^ 2 - Nat.card (GaloisField p n)) := by
      haveI : Fintype (GaloisField p n) := Fintype.ofFinite _
      have := @Matrix.card_GL_field (GaloisField p n) _ _ 2
      simp only [Fin.prod_univ_two, Fin.val_zero, Fin.val_one, pow_zero, pow_one,
                  ← Nat.card_eq_fintype_card] at this
      exact this
     
    have hK : Nat.card ↥(RepresentationTheory.FiniteFieldMatrixCharacterValues.distinguishedMatrixSubgroup p n) =
        Nat.card (GaloisField p n) ^ 2 - 1 := by
       
      change Nat.card ↥(RepresentationTheory.FiniteFieldMatrixCharacterValues.quadraticFieldUnitsToMatrixUnits p n).range = _
       
      have hinj : Function.Injective (RepresentationTheory.FiniteFieldMatrixCharacterValues.quadraticFieldUnitsToMatrixUnits p n) := by
        intro a b hab
        unfold RepresentationTheory.FiniteFieldMatrixCharacterValues.quadraticFieldUnitsToMatrixUnits at hab
        simp only [dif_neg hn_ne] at hab
        have hval := congr_arg (fun g => g.val) hab
        have := RingHom.injective
          (Algebra.leftMulMatrix (Module.finBasisOfFinrankEq (GaloisField p n)
          (GaloisField p (2 * n)) (RepresentationTheory.FiniteFieldMatrixCharacterValues.quadraticFiniteField_finrank p n hn_ne))).toRingHom
        exact Units.ext (this hval)
       
      have : (RepresentationTheory.FiniteFieldMatrixCharacterValues.quadraticFieldUnitsToMatrixUnits p n).range.carrier = Set.range (RepresentationTheory.FiniteFieldMatrixCharacterValues.quadraticFieldUnitsToMatrixUnits p n) :=
        MonoidHom.coe_range _
      rw [show Nat.card ↥(RepresentationTheory.FiniteFieldMatrixCharacterValues.quadraticFieldUnitsToMatrixUnits p n).range =
        Nat.card ↥(Set.range (RepresentationTheory.FiniteFieldMatrixCharacterValues.quadraticFieldUnitsToMatrixUnits p n)) from by
        congr 1]
      rw [Nat.card_range_of_injective hinj]
       
      rw [Nat.card_units]
      rw [GaloisField.card p (2 * n) (Nat.mul_ne_zero two_ne_zero hn_ne)]
      rw [hq_val]; ring_nf
     
    rw [hq_val] at hG hK ⊢
     
    rw [hG, hK]
     
     
    have h1 : 1 ≤ p ^ n := by omega
    have h2 : 1 ≤ (p ^ n) ^ 2 := by nlinarith
    have h3 : p ^ n ≤ (p ^ n) ^ 2 := by nlinarith
    simp only [Nat.cast_sub h1, Nat.cast_mul, Nat.cast_sub h2, Nat.cast_sub h3, Nat.cast_pow,
               Nat.cast_one]
     
     
    have hpn_ne : (↑p : ℂ) ^ n ≠ 0 := by
      exact_mod_cast show (p ^ n : ℕ) ≠ 0 by omega
    have hpn1_ne : (↑p : ℂ) ^ n - 1 ≠ 0 := by
      intro h
      have : (p ^ n : ℕ) = 1 := by exact_mod_cast sub_eq_zero.mp h
      omega
    have hpnp1_ne : (↑p : ℂ) ^ n + 1 ≠ 0 := by
      have : (↑(p ^ n + 1) : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
      push_cast [Nat.cast_pow] at this; exact this
     
    exact dimension_arith_identity _ hpn_ne hpn1_ne hpnp1_ne
  ·  
    have hp_pos := hp.out.pos
    have h1 : 1 < p ^ n := by
      calc p ^ n ≥ p ^ 1 := Nat.pow_le_pow_right hp_pos hn
        _ = p := pow_one p
        _ ≥ 2 := hp.out.two_le
    have h2 : (1 : ℝ) < (p ^ n : ℝ) := by exact_mod_cast h1
    linarith

end RepresentationTheory.FiniteField.CharacterSums
