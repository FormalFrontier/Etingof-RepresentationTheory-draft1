/-
Copyright (c) 2026 mathlib-initiative. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: mathlib-initiative
-/

import RepresentationTheory.Representation.SubtypeCharacter
import RepresentationTheory.ZModInvolution
import RepresentationTheory.FiniteGroups.CharacterRigidity
import Mathlib.RingTheory.RootsOfUnity.EnoughRootsOfUnity
import RepresentationTheory.Alignment.Attribute

/-! # Characters over finite Galois fields -/

noncomputable section

open CategoryTheory

variable (p : ℕ) [hp : Fact (Nat.Prime p)] (n : ℕ)

private abbrev GL2 := Matrix.GeneralLinearGroup (Fin 2) (GaloisField p n)
private abbrev K := ↥(RepresentationTheory.FiniteFieldMatrixCharacterValues.distinguishedMatrixSubgroup p n)

namespace RepresentationTheory.GaloisFieldCharacters

variable [Fintype (GaloisField p n)] [DecidableEq (GaloisField p n)]
  [Fintype (GL2 p n)]

omit [Fintype (GaloisField p n)] [DecidableEq (GaloisField p n)] [Fintype (GL2 p n)] in

/-- Cyclicity of the auxiliary subgroup for nonzero extension degree -/
theorem GaloisField.isCyclic_auxiliarySubgroup (hn : n ≠ 0) : IsCyclic (K p n) := by
  let e := (RepresentationTheory.FiniteFieldMatrixCharacterValues.quadraticFieldUnitsToMatrixUnits p n).ofInjective (by
    intro a b hab
    unfold RepresentationTheory.FiniteFieldMatrixCharacterValues.quadraticFieldUnitsToMatrixUnits at hab
    simp only [dif_neg hn] at hab
    exact Units.ext (RingHom.injective
      (Algebra.leftMulMatrix (Module.finBasisOfFinrankEq (GaloisField p n)
        (GaloisField p (2 * n)) (RepresentationTheory.FiniteFieldMatrixCharacterValues.quadraticFiniteField_finrank p n hn))).toRingHom
        (congr_arg (fun g => g.val) hab)))
  exact isCyclic_of_surjective e e.surjective

/-- Multiplicative equivalence between complex unit-valued characters and modular exponents -/
@[source_ref "Chapter5/Discussion_5.25.4" (role := supporting)]
def GaloisField.characterExponentEquiv (hn : n ≠ 0) :
    (K p n →* ℂˣ) ≃* Multiplicative (ZMod ((Fintype.card (GaloisField p n)) ^ 2 - 1)) := by
  letI : IsCyclic (K p n) := GaloisField.isCyclic_auxiliarySubgroup p n hn
  letI : NeZero (Nat.card (K p n)) := ⟨Nat.card_pos.ne'⟩
  let dual : (K p n →* ℂˣ) ≃* K p n :=
    (IsCyclic.monoidHom_equiv_self (K p n) ℂ).some
  let param : K p n ≃* Multiplicative
      (ZMod ((Fintype.card (GaloisField p n)) ^ 2 - 1)) :=
    mulEquivOfCyclicCardEq (by
      rw [Nat.card_congr Multiplicative.toAdd, Nat.card_zmod,
        RepresentationTheory.FiniteField.RepresentationConstruction.subtype_card_eq_field_card_sq_sub_one p n hn])
  exact dual.trans param

/-- Finite-field-cardinality power transform on complex unit-valued characters -/
def GaloisField.characterCardPow
    (nu : K p n →* ℂˣ) : K p n →* ℂˣ :=
  (powMonoidHom (Fintype.card (GaloisField p n))).comp nu

omit [DecidableEq (GaloisField p n)] [Fintype (GL2 p n)] in
/-- Evaluation of the finite-field-cardinality power transform -/
@[simp]
theorem GaloisField.characterCardPow_apply (nu : K p n →* ℂˣ) (k : K p n) :
    GaloisField.characterCardPow p n nu k =
      (nu k) ^ Fintype.card (GaloisField p n) := rfl

omit [DecidableEq (GaloisField p n)] [Fintype (GL2 p n)] in

/-- Cardinality-power transform transported to modular exponents -/
theorem GaloisField.characterExponentEquiv_characterCardPow (hn : n ≠ 0) (nu : K p n →* ℂˣ) :
    GaloisField.characterExponentEquiv p n hn (GaloisField.characterCardPow p n nu) =
      Multiplicative.ofAdd
        (RepresentationTheory.ZModInvolution.zmodTransform (Fintype.card (GaloisField p n))
          (Multiplicative.toAdd (GaloisField.characterExponentEquiv p n hn nu))) := by
  change GaloisField.characterExponentEquiv p n hn
      (nu ^ Fintype.card (GaloisField p n)) = _
  calc
    _ = (GaloisField.characterExponentEquiv p n hn nu) ^
        Fintype.card (GaloisField p n) :=
      map_pow (GaloisField.characterExponentEquiv p n hn).toMonoidHom nu _
    _ = _ := by
      apply Multiplicative.toAdd.injective
      simp [RepresentationTheory.ZModInvolution.zmodTransform, nsmul_eq_mul]

/-- Complex unit-valued character associated to a modular exponent -/
def GaloisField.characterOfExponent (hn : n ≠ 0)
    (x : ZMod ((Fintype.card (GaloisField p n)) ^ 2 - 1)) : K p n →* ℂˣ :=
  (GaloisField.characterExponentEquiv p n hn).symm (Multiplicative.ofAdd x)

omit [DecidableEq (GaloisField p n)] [Fintype (GL2 p n)] in
/-- Modular exponent of its associated character -/
@[simp]
theorem GaloisField.characterExponentEquiv_characterOfExponent (hn : n ≠ 0)
    (x : ZMod ((Fintype.card (GaloisField p n)) ^ 2 - 1)) :
    GaloisField.characterExponentEquiv p n hn (GaloisField.characterOfExponent p n hn x) =
      Multiplicative.ofAdd x :=
  (GaloisField.characterExponentEquiv p n hn).apply_symm_apply _

omit [DecidableEq (GaloisField p n)] [Fintype (GL2 p n)] in

/-- Nonfixed character criterion in terms of its modular exponent -/
theorem GaloisField.characterCardPow_ne_iff_exponent_ne (hn : n ≠ 0)
    (x : ZMod ((Fintype.card (GaloisField p n)) ^ 2 - 1)) :
    GaloisField.characterCardPow p n (GaloisField.characterOfExponent p n hn x) ≠
        GaloisField.characterOfExponent p n hn x ↔
      RepresentationTheory.ZModInvolution.zmodTransform (Fintype.card (GaloisField p n)) x ≠ x := by
  rw [ne_eq, ← (GaloisField.characterExponentEquiv p n hn).injective.eq_iff,
    GaloisField.characterExponentEquiv_characterCardPow, GaloisField.characterExponentEquiv_characterOfExponent]
  rfl

omit [Fintype (GaloisField p n)] [DecidableEq (GaloisField p n)] [Fintype (GL2 p n)] in

/-- Normalizer membership of an auxiliary element for nonzero extension degree -/
theorem GaloisField.auxiliaryElement_mem_normalizer (hn : n ≠ 0) :
    RepresentationTheory.GaloisFieldAuxiliary.auxiliaryElement p n ∈ Subgroup.normalizer (RepresentationTheory.FiniteFieldMatrixCharacterValues.distinguishedMatrixSubgroup p n) := by
  apply Subgroup.mem_normalizer_fintype
  intro k hk
  rw [← RepresentationTheory.GaloisFieldAuxiliary.auxiliaryElement_inv_eq p n hn]
  exact RepresentationTheory.GaloisFieldAuxiliary.auxiliaryPredicate_auxiliaryElement p n hn k hk

omit [DecidableEq (GaloisField p n)] [Fintype (GL2 p n)] in

/-- Auxiliary character construction as the cardinality-power transform -/
theorem GaloisField.auxiliaryCharacter_eq_characterCardPow (hn : n ≠ 0) (nu : K p n →* ℂˣ) :
    RepresentationTheory.FDRep.SubgroupCharacterFunctions.subgroupCharacterOfNormalizer (RepresentationTheory.FiniteFieldMatrixCharacterValues.distinguishedMatrixSubgroup p n) nu
      (RepresentationTheory.GaloisFieldAuxiliary.auxiliaryElement p n) (GaloisField.auxiliaryElement_mem_normalizer p n hn) =
        GaloisField.characterCardPow p n nu := by
  apply MonoidHom.ext
  intro k
  obtain ⟨a, ha⟩ := k.2
  have hk : k = ⟨RepresentationTheory.FiniteFieldMatrixCharacterValues.quadraticFieldUnitsToMatrixUnits p n a, ⟨a, rfl⟩⟩ := Subtype.ext ha.symm
  subst k
  let k0 : K p n := ⟨RepresentationTheory.FiniteFieldMatrixCharacterValues.quadraticFieldUnitsToMatrixUnits p n a, ⟨a, rfl⟩⟩
  let kc : K p n :=
    ⟨RepresentationTheory.GaloisFieldAuxiliary.auxiliaryElement p n * (k0 : GL2 p n) * (RepresentationTheory.GaloisFieldAuxiliary.auxiliaryElement p n)⁻¹,
      (Subgroup.mem_normalizer_iff.mp (GaloisField.auxiliaryElement_mem_normalizer p n hn) k0).mp k0.2⟩
  change nu kc = (nu k0) ^ Fintype.card (GaloisField p n)
  have hconj :
      kc =
        ⟨RepresentationTheory.FiniteFieldMatrixCharacterValues.quadraticFieldUnitsToMatrixUnits p n (a ^ Fintype.card (GaloisField p n)), ⟨_, rfl⟩⟩ := by
    apply Subtype.ext
    change RepresentationTheory.GaloisFieldAuxiliary.auxiliaryElement p n * RepresentationTheory.FiniteFieldMatrixCharacterValues.quadraticFieldUnitsToMatrixUnits p n a * (RepresentationTheory.GaloisFieldAuxiliary.auxiliaryElement p n)⁻¹ = _
    rw [RepresentationTheory.GaloisFieldAuxiliary.auxiliaryElement_inv_eq p n hn]
    have hc := RepresentationTheory.GaloisFieldAuxiliary.conjugate_auxiliaryFunctionValue_eq_auxiliaryFunctionValue_cardPowerUnit p n hn a
    rw [RepresentationTheory.GaloisFieldAuxiliary.auxiliaryElement_inv_eq p n hn] at hc
    exact hc.trans (congrArg (RepresentationTheory.FiniteFieldMatrixCharacterValues.quadraticFieldUnitsToMatrixUnits p n) (Units.ext rfl))
  rw [hconj]
  rw [← map_pow]
  apply congrArg nu
  apply Subtype.ext
  exact map_pow (RepresentationTheory.FiniteFieldMatrixCharacterValues.quadraticFieldUnitsToMatrixUnits p n) a _

/-- Isomorphism of finite-dimensional representations under the cardinality-power character transform -/
def GaloisField.fdRepIso_characterCardPow (hn : n ≠ 0) (nu : K p n →* ℂˣ) :
    RepresentationTheory.FiniteField.RepresentationConstruction.representationOfCharacter p n nu ≅
      RepresentationTheory.FiniteField.RepresentationConstruction.representationOfCharacter p n (GaloisField.characterCardPow p n nu) :=
  show RepresentationTheory.FDRep.SubgroupCharacterFunctions.representationFromSubgroupCharacter (RepresentationTheory.FiniteFieldMatrixCharacterValues.distinguishedMatrixSubgroup p n) nu ≅
      RepresentationTheory.FDRep.SubgroupCharacterFunctions.representationFromSubgroupCharacter (RepresentationTheory.FiniteFieldMatrixCharacterValues.distinguishedMatrixSubgroup p n)
        (GaloisField.characterCardPow p n nu) from
    RepresentationTheory.FDRep.SubgroupCharacterFunctions.representationIsoOfNormalizer (RepresentationTheory.FiniteFieldMatrixCharacterValues.distinguishedMatrixSubgroup p n) nu
      (RepresentationTheory.GaloisFieldAuxiliary.auxiliaryElement p n) (GaloisField.auxiliaryElement_mem_normalizer p n hn) ≪≫
        eqToIso (by rw [GaloisField.auxiliaryCharacter_eq_characterCardPow p n hn nu])

omit [DecidableEq (GaloisField p n)] [Fintype (GL2 p n)] in

/-- Invariance of character restriction under the cardinality-power transform -/
theorem GaloisField.characterCardPow_comp_auxiliaryHom (hn : n ≠ 0) (nu : K p n →* ℂˣ) :
    (GaloisField.characterCardPow p n nu).comp (RepresentationTheory.FiniteFieldMatrixCharacterValues.scalarUnitsToDistinguishedSubgroup p n) =
      nu.comp (RepresentationTheory.FiniteFieldMatrixCharacterValues.scalarUnitsToDistinguishedSubgroup p n) := by
  classical
  apply MonoidHom.ext
  intro a
  change (nu (RepresentationTheory.FiniteFieldMatrixCharacterValues.scalarUnitsToDistinguishedSubgroup p n a)) ^ Fintype.card (GaloisField p n) =
    nu (RepresentationTheory.FiniteFieldMatrixCharacterValues.scalarUnitsToDistinguishedSubgroup p n a)
  have h := RepresentationTheory.FiniteField.CharacterSums.characterTransform_apply_auxiliaryMap_eq_one p n nu hn a
  change (nu (RepresentationTheory.FiniteFieldMatrixCharacterValues.scalarUnitsToDistinguishedSubgroup p n a)) ^ (Fintype.card (GaloisField p n) - 1) = 1 at h
  have hqpos : 0 < Fintype.card (GaloisField p n) := Fintype.card_pos
  rw [show Fintype.card (GaloisField p n) =
    Fintype.card (GaloisField p n) - 1 + 1 by omega, pow_succ, h, one_mul]

/-- Invariance of an auxiliary value under the cardinality-power character transform -/
theorem GaloisField.auxiliaryValue_characterCardPow (hn : n ≠ 0) (nu : K p n →* ℂˣ) :
    RepresentationTheory.FiniteFieldMatrixCharacterValues.subgroupCharacterMatrixFunction p n nu =
      RepresentationTheory.FiniteFieldMatrixCharacterValues.subgroupCharacterMatrixFunction p n (GaloisField.characterCardPow p n nu) := by
  funext g
  rw [RepresentationTheory.FiniteField.RepresentationConstruction.representation_character_formula, RepresentationTheory.FiniteField.RepresentationConstruction.representation_character_formula,
    GaloisField.characterCardPow_comp_auxiliaryHom p n hn nu]
  rw [FDRep.char_iso (GaloisField.fdRepIso_characterCardPow p n hn nu)]

/-- Isomorphism between auxiliary objects indexed by a character and its cardinality-power transform -/
@[source_ref "Chapter5/Discussion_5.25.4" (role := supporting)]
def GaloisField.auxiliaryIso_characterCardPow
    (hp2 : p ≠ 2) (hn : 0 < n) (nu : K p n →* ℂˣ)
    (hnu : ∃ k : K p n, (nu k) ^ Fintype.card (GaloisField p n) ≠ nu k)
    (hnuF : ∃ k : K p n,
      (GaloisField.characterCardPow p n nu k) ^ Fintype.card (GaloisField p n) ≠
        GaloisField.characterCardPow p n nu k) :
    RepresentationTheory.Representation.SubtypeCharacter.subtypeCharacterRepresentationOfPowerNonfixed p n nu hp2 hn hnu ≅
      RepresentationTheory.Representation.SubtypeCharacter.subtypeCharacterRepresentationOfPowerNonfixed p n (GaloisField.characterCardPow p n nu) hp2 hn hnuF :=
  (RepresentationTheory.FiniteGroups.CharacterRigidity.nonempty_iso_of_character_eq _ _ (by
    funext g
    rw [RepresentationTheory.Representation.SubtypeCharacter.subtypeCharacterRepresentationOfPowerNonfixed_character_eq_auxiliary, RepresentationTheory.Representation.SubtypeCharacter.subtypeCharacterRepresentationOfPowerNonfixed_character_eq_auxiliary,
      GaloisField.auxiliaryValue_characterCardPow p n hn.ne' nu])).some

omit [DecidableEq (GaloisField p n)] in

/-- Character value as a unit value plus its finite-field-cardinality power -/
theorem GaloisField.fdRep_character_apply_eq_unit_add_card_pow
    (hp2 : p ≠ 2) (hn : n ≠ 0) (nu : K p n →* ℂˣ)
    (k : K p n) (hk : RepresentationTheory.FiniteFieldUnitClassDecomposition.Auxiliary.classPredicateAlpha (p := p) (n := n) (k : GL2 p n)) :
    (RepresentationTheory.FiniteField.RepresentationConstruction.representationOfCharacter p n nu).character (k : GL2 p n) =
      (nu k : ℂ) + (nu k : ℂ) ^ Fintype.card (GaloisField p n) := by
  classical
  let S : ℂ := ∑ z : GL2 p n,
    if h : z⁻¹ * (k : GL2 p n) * z ∈ RepresentationTheory.FiniteFieldMatrixCharacterValues.distinguishedMatrixSubgroup p n
    then (nu ⟨z⁻¹ * (k : GL2 p n) * z, h⟩ : ℂ) else 0
  have hweighted : (nu k : ℂ) * starRingEnd ℂ S =
      (Fintype.card (K p n) : ℂ) *
        (1 + starRingEnd ℂ ((RepresentationTheory.FiniteField.CharacterSums.characterTransform p n nu k : ℂˣ) : ℂ)) := by
    calc
      (nu k : ℂ) * starRingEnd ℂ S =
          ∑ z : GL2 p n,
            if h : z⁻¹ * (k : GL2 p n) * z ∈ RepresentationTheory.FiniteFieldMatrixCharacterValues.distinguishedMatrixSubgroup p n
            then (nu k : ℂ) *
              starRingEnd ℂ (nu ⟨z⁻¹ * (k : GL2 p n) * z, h⟩ : ℂ)
            else 0 := by
        dsimp only [S]
        rw [map_sum, Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro z _
        split_ifs <;> simp
      _ = _ := RepresentationTheory.FiniteField.CharacterSums.auxiliaryTheorem p n hp2 nu hn k hk
  have hconj := congrArg (starRingEnd ℂ) hweighted
  have hconj' : starRingEnd ℂ (nu k : ℂ) * S =
      (Fintype.card (K p n) : ℂ) *
        (1 + (nu k : ℂ) ^ (Fintype.card (GaloisField p n) - 1)) := by
    simpa [RepresentationTheory.FiniteField.CharacterSums.characterTransform] using hconj
  have hnorm : (nu k : ℂ) * starRingEnd ℂ (nu k : ℂ) = 1 :=
    RepresentationTheory.FiniteFieldMatrixCharacterValues.characterValue_mul_star_eq_one nu k
  have hqpos : 0 < Fintype.card (GaloisField p n) := Fintype.card_pos
  have hpow : (nu k : ℂ) *
      (nu k : ℂ) ^ (Fintype.card (GaloisField p n) - 1) =
        (nu k : ℂ) ^ Fintype.card (GaloisField p n) := by
    have hqeq : Fintype.card (GaloisField p n) - 1 + 1 =
        Fintype.card (GaloisField p n) := by omega
    calc
      _ = (nu k : ℂ) ^ (Fintype.card (GaloisField p n) - 1) * (nu k : ℂ) :=
        mul_comm _ _
      _ = (nu k : ℂ) ^ (Fintype.card (GaloisField p n) - 1 + 1) :=
        (pow_succ _ _).symm
      _ = _ := by rw [hqeq]
  have hS : S = (Fintype.card (K p n) : ℂ) *
      ((nu k : ℂ) + (nu k : ℂ) ^ Fintype.card (GaloisField p n)) := by
    calc
      S = (nu k : ℂ) * (starRingEnd ℂ (nu k : ℂ) * S) := by
        rw [← mul_assoc, hnorm, one_mul]
      _ = (nu k : ℂ) * ((Fintype.card (K p n) : ℂ) *
          (1 + (nu k : ℂ) ^ (Fintype.card (GaloisField p n) - 1))) := by rw [hconj']
      _ = (Fintype.card (K p n) : ℂ) *
          ((nu k : ℂ) + (nu k : ℂ) ^ Fintype.card (GaloisField p n)) := by
        rw [← hpow]
        ring
  rw [RepresentationTheory.FiniteField.RepresentationConstruction.auxiliary_theorem]
  change (Fintype.card (K p n) : ℂ)⁻¹ * S = _
  have hKne : (Fintype.card (K p n) : ℂ) ≠ 0 := by
    exact_mod_cast Fintype.card_ne_zero (α := K p n)
  rw [hS, ← mul_assoc, inv_mul_cancel₀ hKne, one_mul]

/-- Auxiliary value as the negative sum of a unit value and its cardinality power -/
theorem GaloisField.auxiliaryValue_apply_eq_neg_unit_add_card_pow
    (hp2 : p ≠ 2) (hn : n ≠ 0) (nu : K p n →* ℂˣ)
    (k : K p n) (hk : RepresentationTheory.FiniteFieldUnitClassDecomposition.Auxiliary.classPredicateAlpha (p := p) (n := n) (k : GL2 p n)) :
    RepresentationTheory.FiniteFieldMatrixCharacterValues.subgroupCharacterMatrixFunction p n nu (k : GL2 p n) =
      -((nu k : ℂ) + (nu k : ℂ) ^ Fintype.card (GaloisField p n)) := by
  rw [RepresentationTheory.FiniteField.RepresentationConstruction.representation_character_formula, RepresentationTheory.FiniteFieldMatrixCharacterValues.distinguishedMatrixUnitFunction_auxiliaryProperty p n (k : GL2 p n) hk,
    RepresentationTheory.FiniteFieldMatrixCharacterValues.multiplicativeCharacterMatrixFunction_eq_zero_of_auxiliaryProperty p n _ (k : GL2 p n) hk,
    GaloisField.fdRep_character_apply_eq_unit_add_card_pow p n hp2 hn nu k hk]
  ring

omit [DecidableEq (GaloisField p n)] [Fintype (GL2 p n)] in

private theorem two_le_fieldCard (hn : n ≠ 0) :
    2 ≤ Fintype.card (GaloisField p n) := by
  rw [← Nat.card_eq_fintype_card, GaloisField.card p n hn]
  exact Nat.one_lt_pow hn hp.out.one_lt

omit [DecidableEq (GaloisField p n)] [Fintype (GL2 p n)] in

private theorem orderOf_le_q_sub_one_of_isScalar
    (hn : n ≠ 0) (k : K p n)
    (hk : RepresentationTheory.FiniteFieldUnitClassDecomposition.Auxiliary.classPredicateGamma (p := p) (n := n) (k : GL2 p n)) :
    orderOf k ≤ Fintype.card (GaloisField p n) - 1 := by
  classical
  let a : (GaloisField p n)ˣ := Units.mk0 ((k : GL2 p n).val 0 0)
    (RepresentationTheory.FiniteFieldMatrixCharacterValues.topLeft_ne_zero_of_auxiliaryProperty p n (k : GL2 p n) hk)
  have hka : k = RepresentationTheory.FiniteFieldMatrixCharacterValues.scalarUnitsToDistinguishedSubgroup p n a := by
    apply Subtype.ext
    letI := RepresentationTheory.FiniteFieldMatrixCharacterValues.quadraticFiniteFieldAlgebra p n
    unfold RepresentationTheory.FiniteFieldMatrixCharacterValues.scalarUnitsToDistinguishedSubgroup
    simp only [dif_neg hn, MonoidHom.comp_apply, MonoidHom.codRestrict_apply]
    exact RepresentationTheory.FiniteFieldMatrixCharacterValues.eq_quadraticFieldUnitsToMatrixUnits_topLeft p n hn (k : GL2 p n) hk
      (RepresentationTheory.FiniteFieldMatrixCharacterValues.topLeft_ne_zero_of_auxiliaryProperty p n (k : GL2 p n) hk)
  rw [hka]
  calc
    orderOf (RepresentationTheory.FiniteFieldMatrixCharacterValues.scalarUnitsToDistinguishedSubgroup p n a) ≤ orderOf a :=
      Nat.le_of_dvd (orderOf_pos _) (orderOf_map_dvd (RepresentationTheory.FiniteFieldMatrixCharacterValues.scalarUnitsToDistinguishedSubgroup p n) a)
    _ ≤ Fintype.card ((GaloisField p n)ˣ) := by
      rw [← Nat.card_eq_fintype_card]
      exact orderOf_le_card
    _ = Fintype.card (GaloisField p n) - 1 := Fintype.card_units _

omit [Fintype (GaloisField p n)] [DecidableEq (GaloisField p n)] [Fintype (GL2 p n)] in

private theorem generator_isElliptic
    (hp2 : p ≠ 2) (hn : n ≠ 0) (g : K p n)
    (hg : ∀ x, x ∈ Subgroup.zpowers g) :
    RepresentationTheory.FiniteFieldUnitClassDecomposition.Auxiliary.classPredicateAlpha (p := p) (n := n) (g : GL2 p n) := by
  classical
  letI : Fintype (GaloisField p n) := Fintype.ofFinite _
  letI : Fintype (GL2 p n) := Fintype.ofFinite _
  by_contra hge
  have hscalar := RepresentationTheory.FiniteField.CharacterSums.auxiliaryProperty_of_mem_of_not_otherProperty
    p n hp2 hn (g : GL2 p n) g.2 hge
  have hle := orderOf_le_q_sub_one_of_isScalar p n hn g hscalar
  have hord : orderOf g = Nat.card (K p n) :=
    orderOf_eq_card_of_forall_mem_zpowers hg
  rw [RepresentationTheory.FiniteField.RepresentationConstruction.subtype_card_eq_field_card_sq_sub_one p n hn] at hord
  have hq := two_le_fieldCard p n hn
  have hqsq : Fintype.card (GaloisField p n) <
      Fintype.card (GaloisField p n) ^ 2 := by nlinarith
  have hgt := Nat.sub_lt_sub_right (by omega : 1 ≤ Fintype.card (GaloisField p n)) hqsq
  rw [← hord] at hgt
  exact (not_lt_of_ge hle) hgt

omit [Fintype (GaloisField p n)] [DecidableEq (GaloisField p n)] [Fintype (GL2 p n)] in

private theorem generator_sq_isElliptic
    (hp2 : p ≠ 2) (hn : n ≠ 0) (g : K p n)
    (hg : ∀ x, x ∈ Subgroup.zpowers g) :
    RepresentationTheory.FiniteFieldUnitClassDecomposition.Auxiliary.classPredicateAlpha (p := p) (n := n) ((g ^ 2 : K p n) : GL2 p n) := by
  classical
  letI : Fintype (GaloisField p n) := Fintype.ofFinite _
  letI : Fintype (GL2 p n) := Fintype.ofFinite _
  by_contra hge
  have hscalar := RepresentationTheory.FiniteField.CharacterSums.auxiliaryProperty_of_mem_of_not_otherProperty
    p n hp2 hn ((g ^ 2 : K p n) : GL2 p n) (g ^ 2).2 hge
  have hle := orderOf_le_q_sub_one_of_isScalar p n hn (g ^ 2) hscalar
  have hord : orderOf g = Nat.card (K p n) :=
    orderOf_eq_card_of_forall_mem_zpowers hg
  rw [RepresentationTheory.FiniteField.RepresentationConstruction.subtype_card_eq_field_card_sq_sub_one p n hn] at hord
  set q := Fintype.card (GaloisField p n) with hqdef
  have hq : 3 ≤ q := by
    rw [hqdef, ← Nat.card_eq_fintype_card, GaloisField.card p n hn]
    have hp3 : 3 ≤ p := (hp.out.two_le.lt_or_eq.resolve_right hp2.symm).succ_le
    exact hp3.trans (Nat.le_pow (Nat.pos_of_ne_zero hn))
  have hqodd : Odd q := by
    rw [hqdef, ← Nat.card_eq_fintype_card, GaloisField.card p n hn]
    exact (hp.out.odd_of_ne_two hp2).pow
  obtain ⟨m, hm⟩ := hqodd
  have htwo : 2 ∣ q ^ 2 - 1 := by
    refine ⟨2 * m ^ 2 + 2 * m, ?_⟩
    have halg : (2 * m + 1) ^ 2 = 2 * (2 * m ^ 2 + 2 * m) + 1 := by ring
    rw [hm]
    omega
  have hord2 : orderOf (g ^ 2) = orderOf g / 2 :=
    orderOf_pow_of_dvd (x := g) two_ne_zero (hord.symm ▸ htwo)
  have hhalf : 2 * ((q ^ 2 - 1) / 2) = q ^ 2 - 1 :=
    Nat.mul_div_cancel' htwo
  rw [hord2, hord] at hle
  have hqsub : q - 1 + 1 = q := by omega
  have hqsqsub : q ^ 2 - 1 + 1 = q ^ 2 :=
    Nat.sub_add_cancel (Nat.one_le_iff_ne_zero.mpr (pow_ne_zero 2 (by omega)))
  have hgt : 2 * (q - 1) < q ^ 2 - 1 := by nlinarith
  have hle2 := Nat.mul_le_mul_left 2 hle
  rw [hhalf] at hle2
  exact (not_lt_of_ge hle2) hgt

omit [DecidableEq (GaloisField p n)] in

/-- Character equality up to cardinality-power transform from an auxiliary isomorphism -/
theorem GaloisField.eq_or_eq_characterCardPow_of_auxiliaryIso
    (hp2 : p ≠ 2) (hn : 0 < n)
    (nu mu : K p n →* ℂˣ)
    (hnu : ∃ k : K p n,
      (nu k) ^ Fintype.card (GaloisField p n) ≠ nu k)
    (hmu : ∃ k : K p n,
      (mu k) ^ Fintype.card (GaloisField p n) ≠ mu k)
    (e : RepresentationTheory.Representation.SubtypeCharacter.subtypeCharacterRepresentationOfPowerNonfixed p n nu hp2 hn hnu ≅
      RepresentationTheory.Representation.SubtypeCharacter.subtypeCharacterRepresentationOfPowerNonfixed p n mu hp2 hn hmu) :
    mu = nu ∨ mu = GaloisField.characterCardPow p n nu := by
  classical
  letI : IsCyclic (K p n) := GaloisField.isCyclic_auxiliarySubgroup p n hn.ne'
  obtain ⟨g, hg⟩ := IsCyclic.exists_generator (α := K p n)
  have hgEll := generator_isElliptic p n hp2 hn.ne' g hg
  have hg2Ell := generator_sq_isElliptic p n hp2 hn.ne' g hg
  have hsum :
      (nu g : ℂ) + (nu g : ℂ) ^ Fintype.card (GaloisField p n) =
        (mu g : ℂ) + (mu g : ℂ) ^ Fintype.card (GaloisField p n) := by
    have h := congrFun (FDRep.char_iso e) (g : GL2 p n)
    rw [RepresentationTheory.Representation.SubtypeCharacter.subtypeCharacterRepresentationOfPowerNonfixed_character_eq_auxiliary, RepresentationTheory.Representation.SubtypeCharacter.subtypeCharacterRepresentationOfPowerNonfixed_character_eq_auxiliary,
      GaloisField.auxiliaryValue_apply_eq_neg_unit_add_card_pow p n hp2 hn.ne' nu g hgEll,
      GaloisField.auxiliaryValue_apply_eq_neg_unit_add_card_pow p n hp2 hn.ne' mu g hgEll] at h
    exact neg_injective h
  have hsum2 :
      (nu (g ^ 2) : ℂ) +
          (nu (g ^ 2) : ℂ) ^ Fintype.card (GaloisField p n) =
        (mu (g ^ 2) : ℂ) +
          (mu (g ^ 2) : ℂ) ^ Fintype.card (GaloisField p n) := by
    have h := congrFun (FDRep.char_iso e) ((g ^ 2 : K p n) : GL2 p n)
    rw [RepresentationTheory.Representation.SubtypeCharacter.subtypeCharacterRepresentationOfPowerNonfixed_character_eq_auxiliary, RepresentationTheory.Representation.SubtypeCharacter.subtypeCharacterRepresentationOfPowerNonfixed_character_eq_auxiliary,
      GaloisField.auxiliaryValue_apply_eq_neg_unit_add_card_pow p n hp2 hn.ne' nu (g ^ 2) hg2Ell,
      GaloisField.auxiliaryValue_apply_eq_neg_unit_add_card_pow p n hp2 hn.ne' mu (g ^ 2) hg2Ell] at h
    exact neg_injective h
  have hsquare :
      (nu g : ℂ) ^ 2 +
          ((nu g : ℂ) ^ Fintype.card (GaloisField p n)) ^ 2 =
        (mu g : ℂ) ^ 2 +
          ((mu g : ℂ) ^ Fintype.card (GaloisField p n)) ^ 2 := by
    have hraw :
        (nu g : ℂ) ^ 2 + ((nu g : ℂ) ^ 2) ^ Fintype.card (GaloisField p n) =
          (mu g : ℂ) ^ 2 + ((mu g : ℂ) ^ 2) ^ Fintype.card (GaloisField p n) := by
      simpa only [map_pow, Units.val_pow_eq_pow_val] using hsum2
    have hpow_comm (x : ℂ) :
        (x ^ 2) ^ Fintype.card (GaloisField p n) =
          (x ^ Fintype.card (GaloisField p n)) ^ 2 := by
      rw [← pow_mul, ← pow_mul, Nat.mul_comm]
    rw [← hpow_comm, ← hpow_comm]
    exact hraw
  have hsumsq := congrArg (fun z : ℂ => z ^ 2) hsum
  have htwoprod :
      (2 : ℂ) * ((nu g : ℂ) *
          (nu g : ℂ) ^ Fintype.card (GaloisField p n)) =
        (2 : ℂ) * ((mu g : ℂ) *
          (mu g : ℂ) ^ Fintype.card (GaloisField p n)) := by
    calc
      _ = ((nu g : ℂ) +
            (nu g : ℂ) ^ Fintype.card (GaloisField p n)) ^ 2 -
          ((nu g : ℂ) ^ 2 +
            ((nu g : ℂ) ^ Fintype.card (GaloisField p n)) ^ 2) := by ring
      _ = ((mu g : ℂ) +
            (mu g : ℂ) ^ Fintype.card (GaloisField p n)) ^ 2 -
          ((mu g : ℂ) ^ 2 +
            ((mu g : ℂ) ^ Fintype.card (GaloisField p n)) ^ 2) := by
              rw [hsumsq, hsquare]
      _ = _ := by ring
  have hprod :
      (nu g : ℂ) * (nu g : ℂ) ^ Fintype.card (GaloisField p n) =
        (mu g : ℂ) * (mu g : ℂ) ^ Fintype.card (GaloisField p n) := by
    exact mul_left_cancel₀ (by norm_num : (2 : ℂ) ≠ 0) htwoprod
  have hroot :
      ((mu g : ℂ) - (nu g : ℂ)) *
        ((mu g : ℂ) - (nu g : ℂ) ^ Fintype.card (GaloisField p n)) = 0 := by
    calc
      _ = (mu g : ℂ) ^ 2 - (mu g : ℂ) *
            ((nu g : ℂ) + (nu g : ℂ) ^ Fintype.card (GaloisField p n)) +
          (nu g : ℂ) * (nu g : ℂ) ^ Fintype.card (GaloisField p n) := by ring
      _ = (mu g : ℂ) ^ 2 - (mu g : ℂ) *
            ((mu g : ℂ) + (mu g : ℂ) ^ Fintype.card (GaloisField p n)) +
          (mu g : ℂ) * (mu g : ℂ) ^ Fintype.card (GaloisField p n) := by
              rw [hsum, hprod]
      _ = 0 := by ring
  have hom_eq_of_generator (a b : K p n →* ℂˣ) (hab : a g = b g) : a = b := by
    apply MonoidHom.ext
    intro k
    obtain ⟨z, rfl⟩ := hg k
    simp only [map_zpow, hab]
  rcases mul_eq_zero.mp hroot with hsame | hfrob
  · left
    apply hom_eq_of_generator
    exact Units.ext (sub_eq_zero.mp hsame)
  · right
    apply hom_eq_of_generator
    apply Units.ext
    exact sub_eq_zero.mp hfrob

omit [DecidableEq (GaloisField p n)] in

/-- Isomorphism criterion for auxiliary objects indexed by nonfixed characters -/
@[source_ref "Chapter5/Discussion_5.25.4" (role := supporting)]
theorem GaloisField.auxiliaryIso_iff_eq_or_eq_characterCardPow
    (hp2 : p ≠ 2) (hn : 0 < n)
    (nu mu : K p n →* ℂˣ)
    (hnu : ∃ k : K p n,
      (nu k) ^ Fintype.card (GaloisField p n) ≠ nu k)
    (hmu : ∃ k : K p n,
      (mu k) ^ Fintype.card (GaloisField p n) ≠ mu k) :
    Nonempty (RepresentationTheory.Representation.SubtypeCharacter.subtypeCharacterRepresentationOfPowerNonfixed p n nu hp2 hn hnu ≅
      RepresentationTheory.Representation.SubtypeCharacter.subtypeCharacterRepresentationOfPowerNonfixed p n mu hp2 hn hmu) ↔
      mu = nu ∨ mu = GaloisField.characterCardPow p n nu := by
  classical
  constructor
  · rintro ⟨e⟩
    exact GaloisField.eq_or_eq_characterCardPow_of_auxiliaryIso p n hp2 hn nu mu hnu hmu e
  · rintro (rfl | rfl)
    · exact ⟨Iso.refl _⟩
    · exact ⟨GaloisField.auxiliaryIso_characterCardPow p n hp2 hn nu hnu hmu⟩

/-! ### The packaged complementary-series family -/

section Family

variable [NeZero n]

omit [DecidableEq (GaloisField p n)] [Fintype (GL2 p n)] in
private instance complementarySeries_modulus_neZero :
    NeZero (Fintype.card (GaloisField p n) ^ 2 - 1) := by
  classical
  have hq := two_le_fieldCard p n (NeZero.ne n)
  constructor
  exact (Nat.sub_pos_of_lt (Nat.one_lt_pow two_ne_zero hq)).ne'

/-- Auxiliary index type over a finite Galois field -/
abbrev GaloisField.AuxiliaryIndex :=
  {x : ZMod (Fintype.card (GaloisField p n) ^ 2 - 1) //
    x ∈ RepresentationTheory.ZModInvolution.auxiliaryZModFinsetB (Fintype.card (GaloisField p n))}

/-- Complex unit-valued character associated to an auxiliary index -/
def GaloisField.characterOfAuxiliaryIndex (i : GaloisField.AuxiliaryIndex p n) : K p n →* ℂˣ :=
  GaloisField.characterOfExponent p n (NeZero.ne n) i.1

omit [DecidableEq (GaloisField p n)] [Fintype (GL2 p n)] in

/-- Existence of a nonfixed value of an auxiliary-index character under cardinality powering -/
theorem GaloisField.exists_characterOfAuxiliaryIndex_cardPow_ne (i : GaloisField.AuxiliaryIndex p n) :
    ∃ k : K p n,
      (GaloisField.characterOfAuxiliaryIndex p n i k) ^ Fintype.card (GaloisField p n) ≠
        GaloisField.characterOfAuxiliaryIndex p n i k := by
  have hiMoved : RepresentationTheory.ZModInvolution.zmodTransform
      (Fintype.card (GaloisField p n)) i.1 ≠ i.1 := by
    exact (RepresentationTheory.ZModInvolution.mem_auxiliaryZModFinsetA_iff _ i.1).mp
      (Finset.mem_filter.mp i.2).1
  have hchar : GaloisField.characterCardPow p n (GaloisField.characterOfAuxiliaryIndex p n i) ≠
      GaloisField.characterOfAuxiliaryIndex p n i :=
    (GaloisField.characterCardPow_ne_iff_exponent_ne p n (NeZero.ne n) i.1).mpr hiMoved
  by_contra h
  apply hchar
  apply MonoidHom.ext
  intro k
  exact not_ne_iff.mp (not_exists.mp h k)

/-- Finite-dimensional complex representation associated to an auxiliary index -/
@[source_ref "Chapter5/Discussion_5.25.4" (role := supporting)]
def GaloisField.fdRepOfAuxiliaryIndex (hp2 : p ≠ 2) (i : GaloisField.AuxiliaryIndex p n) :
    FDRep ℂ (GL2 p n) :=
  RepresentationTheory.Representation.SubtypeCharacter.subtypeCharacterRepresentationOfPowerNonfixed p n (GaloisField.characterOfAuxiliaryIndex p n i) hp2
    (Nat.pos_of_ne_zero (NeZero.ne n)) (GaloisField.exists_characterOfAuxiliaryIndex_cardPow_ne p n i)

omit [DecidableEq (GaloisField p n)] in

/-- Simplicity of the representation associated to an auxiliary index -/
@[source_ref "Chapter5/Discussion_5.25.4" (role := supporting)]
theorem GaloisField.simple_fdRepOfAuxiliaryIndex (hp2 : p ≠ 2) (i : GaloisField.AuxiliaryIndex p n) :
    Simple (GaloisField.fdRepOfAuxiliaryIndex p n hp2 i) := by
  classical
  unfold GaloisField.fdRepOfAuxiliaryIndex
  infer_instance

omit [DecidableEq (GaloisField p n)] in

/-- Finite rank of the representation associated to an auxiliary index -/
theorem GaloisField.finrank_fdRepOfAuxiliaryIndex (hp2 : p ≠ 2) (i : GaloisField.AuxiliaryIndex p n) :
    Module.finrank ℂ (GaloisField.fdRepOfAuxiliaryIndex p n hp2 i).V = p ^ n - 1 := by
  classical
  exact RepresentationTheory.Representation.SubtypeCharacter.subtypeCharacterRepresentationOfPowerNonfixed_finrank_eq_pow_sub_one p n (GaloisField.characterOfAuxiliaryIndex p n i) hp2
    (Nat.pos_of_ne_zero (NeZero.ne n)) (GaloisField.exists_characterOfAuxiliaryIndex_cardPow_ne p n i)

omit [DecidableEq (GaloisField p n)] in

/-- Equality of auxiliary indices determined by isomorphic associated representations -/
@[source_ref "Chapter5/Discussion_5.25.4" (role := supporting)]
theorem GaloisField.eq_of_fdRepOfAuxiliaryIndex_iso (hp2 : p ≠ 2) :
    ∀ i j : GaloisField.AuxiliaryIndex p n,
      Nonempty (GaloisField.fdRepOfAuxiliaryIndex p n hp2 i ≅ GaloisField.fdRepOfAuxiliaryIndex p n hp2 j) → i = j := by
  classical
  intro i j hij
  have horbit := (GaloisField.auxiliaryIso_iff_eq_or_eq_characterCardPow p n hp2
    (Nat.pos_of_ne_zero (NeZero.ne n))
    (GaloisField.characterOfAuxiliaryIndex p n i) (GaloisField.characterOfAuxiliaryIndex p n j)
    (GaloisField.exists_characterOfAuxiliaryIndex_cardPow_ne p n i) (GaloisField.exists_characterOfAuxiliaryIndex_cardPow_ne p n j)).mp hij
  rcases horbit with hsame | hfrob
  · apply Subtype.ext
    have h := congrArg (GaloisField.characterExponentEquiv p n (NeZero.ne n)) hsame
    rw [GaloisField.characterOfAuxiliaryIndex, GaloisField.characterExponentEquiv_characterOfExponent,
      GaloisField.characterOfAuxiliaryIndex, GaloisField.characterExponentEquiv_characterOfExponent] at h
    exact Multiplicative.ofAdd.injective h.symm
  · have hparam : j.1 = RepresentationTheory.ZModInvolution.zmodTransform
        (Fintype.card (GaloisField p n)) i.1 := by
      have h := congrArg (GaloisField.characterExponentEquiv p n (NeZero.ne n)) hfrob
      rw [GaloisField.characterOfAuxiliaryIndex, GaloisField.characterExponentEquiv_characterOfExponent,
        GaloisField.characterExponentEquiv_characterCardPow, GaloisField.characterOfAuxiliaryIndex,
        GaloisField.characterExponentEquiv_characterOfExponent] at h
      change Multiplicative.ofAdd j.1 = Multiplicative.ofAdd
        (RepresentationTheory.ZModInvolution.zmodTransform (Fintype.card (GaloisField p n)) i.1) at h
      exact Multiplicative.ofAdd.injective h
    have hiLt : i.1.val <
        (RepresentationTheory.ZModInvolution.zmodTransform (Fintype.card (GaloisField p n)) i.1).val :=
      (Finset.mem_filter.mp i.2).2
    have hjLt : j.1.val <
        (RepresentationTheory.ZModInvolution.zmodTransform (Fintype.card (GaloisField p n)) j.1).val :=
      (Finset.mem_filter.mp j.2).2
    rw [hparam, RepresentationTheory.ZModInvolution.zmodTransform_involutive _
      (two_le_fieldCard p n (NeZero.ne n))] at hjLt
    omega

omit [DecidableEq (GaloisField p n)] [Fintype (GL2 p n)] in

/-- Cardinality of the auxiliary index type -/
@[source_ref "Chapter5/Discussion_5.25.4" (role := supporting)]
theorem GaloisField.natCard_auxiliaryIndex :
    Nat.card (GaloisField.AuxiliaryIndex p n) =
      Fintype.card (GaloisField p n) * (Fintype.card (GaloisField p n) - 1) / 2 := by
  rw [Nat.card_eq_fintype_card, Fintype.card_coe,
    RepresentationTheory.ZModInvolution.card_auxiliaryZModFinsetB _
      (two_le_fieldCard p n (NeZero.ne n))]

omit [DecidableEq (GaloisField p n)] [Fintype (GL2 p n)] in

/-- Family of pairwise nonisomorphic simple objects with prescribed index cardinality -/
@[source_ref "Chapter5/Discussion_5.25.4" (role := supporting)]
theorem GaloisField.exists_pairwise_nonisomorphic_simple_family (hp2 : p ≠ 2) :
    ∃ (ι : Type) (F : ι → FDRep ℂ (GL2 p n)),
      (∀ i, Simple (F i)) ∧
      (∀ i j, Nonempty (F i ≅ F j) → i = j) ∧
      Nat.card ι = Fintype.card (GaloisField p n) *
        (Fintype.card (GaloisField p n) - 1) / 2 := by
  classical
  letI : Fintype (GL2 p n) := Fintype.ofFinite _
  exact ⟨GaloisField.AuxiliaryIndex p n, GaloisField.fdRepOfAuxiliaryIndex p n hp2,
    GaloisField.simple_fdRepOfAuxiliaryIndex p n hp2, GaloisField.eq_of_fdRepOfAuxiliaryIndex_iso p n hp2,
    GaloisField.natCard_auxiliaryIndex p n⟩

end Family

end RepresentationTheory.GaloisFieldCharacters

end
