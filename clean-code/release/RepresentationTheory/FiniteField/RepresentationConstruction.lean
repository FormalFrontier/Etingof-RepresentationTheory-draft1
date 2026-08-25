/-
Copyright (c) 2026 mathlib-initiative. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: mathlib-initiative
-/

import RepresentationTheory.FiniteFieldMatrixCharacterValues
import RepresentationTheory.FDRep.SubgroupCharacterFunctions

noncomputable section

variable (p : ℕ) [hp : Fact (Nat.Prime p)] (n : ℕ)

private abbrev GL2'' := Matrix.GeneralLinearGroup (Fin 2) (GaloisField p n)

open scoped Classical in
/-- Constructs a finite-dimensional complex representation from a unit-valued character on the displayed subtype. -/
def RepresentationTheory.FiniteField.RepresentationConstruction.representationOfCharacter
    [Fintype (GaloisField p n)] [Fintype (GL2'' p n)]
    (nu : ↥(RepresentationTheory.FiniteFieldMatrixCharacterValues.distinguishedMatrixSubgroup
      p n) →* ℂˣ) :
    FDRep ℂ (GL2'' p n) :=
  RepresentationTheory.FDRep.SubgroupCharacterFunctions.representationFromSubgroupCharacter
    (RepresentationTheory.FiniteFieldMatrixCharacterValues.distinguishedMatrixSubgroup p n) nu

open scoped Classical in
/-- An auxiliary theorem. -/
theorem RepresentationTheory.FiniteField.RepresentationConstruction.auxiliary_theorem
    [Fintype (GaloisField p n)] [Fintype (GL2'' p n)]
    (nu : ↥(RepresentationTheory.FiniteFieldMatrixCharacterValues.distinguishedMatrixSubgroup
      p n) →* ℂˣ) (g : GL2'' p n) :
    (RepresentationTheory.FiniteField.RepresentationConstruction.representationOfCharacter
      p n nu).character g =
      (Fintype.card ↥(RepresentationTheory.FiniteFieldMatrixCharacterValues.distinguishedMatrixSubgroup
        p n) : ℂ)⁻¹ *
        ∑ x : GL2'' p n,
          if h : x⁻¹ * g * x ∈
              RepresentationTheory.FiniteFieldMatrixCharacterValues.distinguishedMatrixSubgroup p n
          then (nu ⟨x⁻¹ * g * x, h⟩).val else 0 :=
  RepresentationTheory.FDRep.SubgroupCharacterFunctions.auxiliary_representationFromSubgroupCharacter
    (RepresentationTheory.FiniteFieldMatrixCharacterValues.distinguishedMatrixSubgroup p n) nu g

open scoped Classical in
/-- The representation constructed from a character has dimension equal to the displayed quotient of finite cardinalities. -/
theorem RepresentationTheory.FiniteField.RepresentationConstruction.representationOfCharacter_finrank
    [Fintype (GaloisField p n)] [Fintype (GL2'' p n)]
    (nu : ↥(RepresentationTheory.FiniteFieldMatrixCharacterValues.distinguishedMatrixSubgroup
      p n) →* ℂˣ) :
    Module.finrank ℂ
      (RepresentationTheory.FiniteField.RepresentationConstruction.representationOfCharacter
        p n nu) =
      Fintype.card (GL2'' p n) /
        Fintype.card ↥(RepresentationTheory.FiniteFieldMatrixCharacterValues.distinguishedMatrixSubgroup
          p n) :=
  RepresentationTheory.FDRep.SubgroupCharacterFunctions.finrank_representationFromSubgroupCharacter
    (RepresentationTheory.FiniteFieldMatrixCharacterValues.distinguishedMatrixSubgroup p n) nu

/-- The displayed subtype has cardinality one less than the square of the finite field cardinality. -/
theorem RepresentationTheory.FiniteField.RepresentationConstruction.subtype_card_eq_field_card_sq_sub_one
    [Fintype (GaloisField p n)] (hn : n ≠ 0) :
    Nat.card ↥(RepresentationTheory.FiniteFieldMatrixCharacterValues.distinguishedMatrixSubgroup
      p n) = Fintype.card (GaloisField p n) ^ 2 - 1 := by
  classical
  haveI : Fintype (GaloisField p (2 * n)) := Fintype.ofFinite _
  have hinj : Function.Injective
      (RepresentationTheory.FiniteFieldMatrixCharacterValues.quadraticFieldUnitsToMatrixUnits
        p n) := by
    intro a b hab
    unfold RepresentationTheory.FiniteFieldMatrixCharacterValues.quadraticFieldUnitsToMatrixUnits at hab
    simp only [dif_neg hn] at hab
    exact Units.ext (RingHom.injective
      (Algebra.leftMulMatrix (Module.finBasisOfFinrankEq (GaloisField p n)
      (GaloisField p (2 * n))
        (RepresentationTheory.FiniteFieldMatrixCharacterValues.quadraticFiniteField_finrank
          p n hn))).toRingHom
      (congr_arg (fun g => g.val) hab))
  have hcard :
      Nat.card ↥(RepresentationTheory.FiniteFieldMatrixCharacterValues.distinguishedMatrixSubgroup
        p n) = Nat.card (GaloisField p (2 * n))ˣ := by
    change Nat.card
      ↥(RepresentationTheory.FiniteFieldMatrixCharacterValues.quadraticFieldUnitsToMatrixUnits
        p n).range = _
    exact Nat.card_congr
      ((RepresentationTheory.FiniteFieldMatrixCharacterValues.quadraticFieldUnitsToMatrixUnits
        p n).ofInjective hinj).symm.toEquiv
  rw [hcard, Nat.card_eq_fintype_card, Fintype.card_units, ← Nat.card_eq_fintype_card,
    GaloisField.card p (2 * n) (Nat.mul_ne_zero two_ne_zero hn),
    ← Nat.card_eq_fintype_card, GaloisField.card p n hn, ← pow_mul, Nat.mul_comm n 2]

open scoped Classical in
/-- For nonzero extension degree, the constructed representation has dimension equal to the field cardinality times its predecessor. -/
theorem RepresentationTheory.FiniteField.RepresentationConstruction.representationOfCharacter_finrank_eq_field_card_mul_pred
    [Fintype (GaloisField p n)] [Fintype (GL2'' p n)]
    (hn : n ≠ 0)
    (nu : ↥(RepresentationTheory.FiniteFieldMatrixCharacterValues.distinguishedMatrixSubgroup
      p n) →* ℂˣ) :
    Module.finrank ℂ
      (RepresentationTheory.FiniteField.RepresentationConstruction.representationOfCharacter
        p n nu) =
      Fintype.card (GaloisField p n) * (Fintype.card (GaloisField p n) - 1) := by
  set q := Fintype.card (GaloisField p n) with hq
  have hq2 : 2 ≤ q := by
    rw [hq, ← Nat.card_eq_fintype_card, GaloisField.card p n hn]
    calc 2 ≤ p := hp.out.two_le
      _ = p ^ 1 := (pow_one p).symm
      _ ≤ p ^ n := Nat.pow_le_pow_right hp.out.pos (Nat.one_le_iff_ne_zero.mpr hn)
  have hG : Fintype.card (GL2'' p n) = (q ^ 2 - 1) * (q ^ 2 - q) := by
    have h := Matrix.card_GL_field (𝔽 := GaloisField p n) 2
    rw [Nat.card_eq_fintype_card] at h
    rw [h]
    simp [Fin.prod_univ_two, hq]
  have hpos : 0 < q ^ 2 - 1 := Nat.sub_pos_of_lt (Nat.one_lt_pow two_ne_zero hq2)
  rw [RepresentationTheory.FiniteField.RepresentationConstruction.representationOfCharacter_finrank,
    hG, ← Nat.card_eq_fintype_card,
    RepresentationTheory.FiniteField.RepresentationConstruction.subtype_card_eq_field_card_sq_sub_one
      p n hn,
    Nat.mul_div_cancel_left _ hpos, Nat.mul_sub, pow_two, Nat.mul_one]

open Classical in
/-- Relates the displayed character expression to auxiliary values associated with a unit-valued character. -/
theorem RepresentationTheory.FiniteField.RepresentationConstruction.representation_character_formula
    [Fintype (GaloisField p n)] [DecidableEq (GaloisField p n)]
    [Fintype (GL2'' p n)]
    (nu : ↥(RepresentationTheory.FiniteFieldMatrixCharacterValues.distinguishedMatrixSubgroup
      p n) →* ℂˣ) (g : GL2'' p n) :
    RepresentationTheory.FiniteFieldMatrixCharacterValues.subgroupCharacterMatrixFunction
      p n nu g =
      RepresentationTheory.FiniteFieldMatrixCharacterValues.distinguishedMatrixUnitFunction
          p n g *
          RepresentationTheory.FiniteFieldMatrixCharacterValues.multiplicativeCharacterMatrixFunction
            p n
            (nu.comp
              (RepresentationTheory.FiniteFieldMatrixCharacterValues.scalarUnitsToDistinguishedSubgroup
                p n)) g
        - RepresentationTheory.FiniteFieldMatrixCharacterValues.multiplicativeCharacterMatrixFunction
            p n
            (nu.comp
              (RepresentationTheory.FiniteFieldMatrixCharacterValues.scalarUnitsToDistinguishedSubgroup
                p n)) g
        - (RepresentationTheory.FiniteField.RepresentationConstruction.representationOfCharacter
            p n nu).character g := by
  rw [RepresentationTheory.FiniteField.RepresentationConstruction.auxiliary_theorem]
  rfl
