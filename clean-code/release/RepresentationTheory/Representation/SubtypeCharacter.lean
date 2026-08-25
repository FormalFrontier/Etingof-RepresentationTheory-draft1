/-
Copyright (c) 2026 mathlib-initiative. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: mathlib-initiative
-/

import Mathlib
import RepresentationTheory.Group.CharacterOperations
import RepresentationTheory.FiniteField.RepresentationConstruction
import RepresentationTheory.FiniteFieldMatrixCharacterFormulas
import RepresentationTheory.FiniteField.CharacterSums
import RepresentationTheory.FDRep.Biproduct
import RepresentationTheory.FDRep.CharacterDifference
import RepresentationTheory.Alignment.Attribute

noncomputable section

open CategoryTheory MonoidalCategory

variable (p : ℕ) [hp : Fact (Nat.Prime p)] (n : ℕ)

private abbrev AuxiliaryGroup := Matrix.GeneralLinearGroup (Fin 2) (GaloisField p n)

namespace RepresentationTheory.Representation.SubtypeCharacter

variable [Fintype (GaloisField p n)] [DecidableEq (GaloisField p n)]
  [Fintype (AuxiliaryGroup p n)]

/-- Constructs a finite-dimensional complex representation from a unit-valued multiplicative map on the displayed subtype. -/
def subtypeCharacterRepresentation
    (nu : ↥(RepresentationTheory.FiniteFieldMatrixCharacterValues.distinguishedMatrixSubgroup
      p n) →* ℂˣ) : FDRep ℂ (AuxiliaryGroup p n) :=
  RepresentationTheory.AuxiliaryFiniteFieldRepresentations.auxiliaryRepresentation p n 1 ⊗
    RepresentationTheory.AuxiliaryFiniteFieldRepresentations.auxiliaryPairedRepresentation p n
      (nu.comp
        (RepresentationTheory.FiniteFieldMatrixCharacterValues.scalarUnitsToDistinguishedSubgroup
          p n)) 1

/-- Constructs a finite-dimensional complex representation from a unit-valued multiplicative map on the displayed subtype, using the supplied finite instances. -/
def fintypeSubtypeCharacterRepresentation
    (nu : ↥(RepresentationTheory.FiniteFieldMatrixCharacterValues.distinguishedMatrixSubgroup
      p n) →* ℂˣ) : FDRep ℂ (AuxiliaryGroup p n) :=
  RepresentationTheory.AuxiliaryFiniteFieldRepresentations.auxiliaryPairedRepresentation p n
      (nu.comp
        (RepresentationTheory.FiniteFieldMatrixCharacterValues.scalarUnitsToDistinguishedSubgroup
          p n)) 1 ⊞
    RepresentationTheory.FiniteField.RepresentationConstruction.representationOfCharacter p n nu

/-- At each group element, the difference of the characters of two displayed subtype-character representations is an auxiliary function. -/
theorem subtypeCharacterRepresentations_character_sub_eq_auxiliary
    (nu : ↥(RepresentationTheory.FiniteFieldMatrixCharacterValues.distinguishedMatrixSubgroup
      p n) →* ℂˣ) (g : AuxiliaryGroup p n) :
    (subtypeCharacterRepresentation p n nu).character g -
        (fintypeSubtypeCharacterRepresentation p n nu).character g =
      RepresentationTheory.FiniteFieldMatrixCharacterValues.subgroupCharacterMatrixFunction
        p n nu g := by
  rw [subtypeCharacterRepresentation, fintypeSubtypeCharacterRepresentation,
    RepresentationTheory.Group.CharacterOperations.character_tensor,
    RepresentationTheory.FDRep.Biproduct.character_biprod,
    RepresentationTheory.FiniteFieldMatrixCharacterFormulas.character_auxFamily_one,
    RepresentationTheory.FiniteFieldMatrixCharacterFormulas.character_auxTwoParameter_rightOne,
    RepresentationTheory.FiniteField.RepresentationConstruction.representation_character_formula]
  ring

omit [DecidableEq (GaloisField p n)] in
private theorem subtypeCharacter_innerProduct
    (hp2 : p ≠ 2) (hn : 0 < n)
    (nu : ↥(RepresentationTheory.FiniteFieldMatrixCharacterValues.distinguishedMatrixSubgroup
      p n) →* ℂˣ)
    (hnu_ne : ∃ k : ↥(RepresentationTheory.FiniteFieldMatrixCharacterValues.distinguishedMatrixSubgroup
      p n),
      (nu k) ^ Fintype.card (GaloisField p n) ≠ nu k) :
    (Fintype.card (AuxiliaryGroup p n) : ℂ)⁻¹ •
      ∑ g : AuxiliaryGroup p n,
        ((subtypeCharacterRepresentation p n nu).character g -
            (fintypeSubtypeCharacterRepresentation p n nu).character g) *
          starRingEnd ℂ
            ((subtypeCharacterRepresentation p n nu).character g -
              (fintypeSubtypeCharacterRepresentation p n nu).character g) = 1 := by
  classical
  simpa only [subtypeCharacterRepresentations_character_sub_eq_auxiliary] using
    RepresentationTheory.FiniteField.CharacterSums.normalized_sum_auxiliaryValue_mul_star_eq_one
      p n hp2 nu hn hnu_ne

omit [DecidableEq (GaloisField p n)] in
private theorem subtypeCharacter_dimension_pos
    (hn : 0 < n)
    (nu : ↥(RepresentationTheory.FiniteFieldMatrixCharacterValues.distinguishedMatrixSubgroup
      p n) →* ℂˣ) :
    Module.finrank ℂ (fintypeSubtypeCharacterRepresentation p n nu) <
      Module.finrank ℂ (subtypeCharacterRepresentation p n nu) := by
  classical
  have hchar := subtypeCharacterRepresentations_character_sub_eq_auxiliary p n nu
    (1 : AuxiliaryGroup p n)
  rw [FDRep.char_one, FDRep.char_one,
    (RepresentationTheory.FiniteField.CharacterSums.auxiliaryValue_one_eq_pow_sub_one_and_pos
      p n nu hn).1] at hchar
  have hcharZ :
      (Module.finrank ℂ (subtypeCharacterRepresentation p n nu) : ℤ) -
          (Module.finrank ℂ (fintypeSubtypeCharacterRepresentation p n nu) : ℤ) =
        (p ^ n : ℤ) - 1 := by
    exact_mod_cast hchar
  have hpow : (1 : ℤ) < p ^ n := by
    have hreal :=
      (RepresentationTheory.FiniteField.CharacterSums.auxiliaryValue_one_eq_pow_sub_one_and_pos
        p n nu hn).2
    exact_mod_cast (sub_pos.mp hreal)
  omega

/-- Under the stated odd-prime, positive-degree, and power-nonfixed hypotheses, constructs a finite-dimensional complex representation. -/
@[source_ref "Chapter5/Discussion_5.25.4" (role := supporting)]
def subtypeCharacterRepresentationOfPowerNonfixed
    (nu : ↥(RepresentationTheory.FiniteFieldMatrixCharacterValues.distinguishedMatrixSubgroup
      p n) →* ℂˣ)
    (hp2 : p ≠ 2) (hn : 0 < n)
    (hnu_ne : ∃ k : ↥(RepresentationTheory.FiniteFieldMatrixCharacterValues.distinguishedMatrixSubgroup
      p n),
      (nu k) ^ Fintype.card (GaloisField p n) ≠ nu k) : FDRep ℂ (AuxiliaryGroup p n) :=
  RepresentationTheory.FDRep.CharacterDifference.characterDifferenceRepresentation
    (subtypeCharacterRepresentation p n nu) (fintypeSubtypeCharacterRepresentation p n nu)
    (subtypeCharacter_innerProduct p n hp2 hn nu hnu_ne)
    (subtypeCharacter_dimension_pos p n hn nu)

/-- The representation constructed under the power-nonfixed hypotheses is simple. -/
@[source_ref "Chapter5/Discussion_5.25.4" (role := primary)]
instance subtypeCharacterRepresentationOfPowerNonfixed_isSimple
    (nu : ↥(RepresentationTheory.FiniteFieldMatrixCharacterValues.distinguishedMatrixSubgroup
      p n) →* ℂˣ)
    (hp2 : p ≠ 2) (hn : 0 < n)
    (hnu_ne : ∃ k : ↥(RepresentationTheory.FiniteFieldMatrixCharacterValues.distinguishedMatrixSubgroup
      p n),
      (nu k) ^ Fintype.card (GaloisField p n) ≠ nu k) :
    CategoryTheory.Simple (subtypeCharacterRepresentationOfPowerNonfixed p n nu hp2 hn hnu_ne) := by
  unfold subtypeCharacterRepresentationOfPowerNonfixed
  infer_instance

/-- The character of the power-nonfixed representation equals the displayed auxiliary function. -/
@[source_ref "Chapter5/Discussion_5.25.4" (role := primary), simp]
theorem subtypeCharacterRepresentationOfPowerNonfixed_character_eq_auxiliary
    (nu : ↥(RepresentationTheory.FiniteFieldMatrixCharacterValues.distinguishedMatrixSubgroup
      p n) →* ℂˣ)
    (hp2 : p ≠ 2) (hn : 0 < n)
    (hnu_ne : ∃ k : ↥(RepresentationTheory.FiniteFieldMatrixCharacterValues.distinguishedMatrixSubgroup
      p n),
      (nu k) ^ Fintype.card (GaloisField p n) ≠ nu k)
    (g : AuxiliaryGroup p n) :
    (subtypeCharacterRepresentationOfPowerNonfixed p n nu hp2 hn hnu_ne).character g =
      RepresentationTheory.FiniteFieldMatrixCharacterValues.subgroupCharacterMatrixFunction
        p n nu g := by
  rw [subtypeCharacterRepresentationOfPowerNonfixed,
    RepresentationTheory.FDRep.CharacterDifference.character_characterDifferenceRepresentation,
    subtypeCharacterRepresentations_character_sub_eq_auxiliary]

omit [DecidableEq (GaloisField p n)] in
/-- The underlying complex module of the power-nonfixed representation has dimension p raised to n minus one. -/
@[source_ref "Chapter5/Discussion_5.25.4" (role := primary)]
theorem subtypeCharacterRepresentationOfPowerNonfixed_finrank_eq_pow_sub_one
    (nu : ↥(RepresentationTheory.FiniteFieldMatrixCharacterValues.distinguishedMatrixSubgroup
      p n) →* ℂˣ)
    (hp2 : p ≠ 2) (hn : 0 < n)
    (hnu_ne : ∃ k : ↥(RepresentationTheory.FiniteFieldMatrixCharacterValues.distinguishedMatrixSubgroup
      p n),
      (nu k) ^ Fintype.card (GaloisField p n) ≠ nu k) :
    Module.finrank ℂ (subtypeCharacterRepresentationOfPowerNonfixed p n nu hp2 hn hnu_ne) =
      p ^ n - 1 := by
  classical
  have hchar := subtypeCharacterRepresentationOfPowerNonfixed_character_eq_auxiliary p n nu hp2
    hn hnu_ne (1 : AuxiliaryGroup p n)
  rw [FDRep.char_one,
    (RepresentationTheory.FiniteField.CharacterSums.auxiliaryValue_one_eq_pow_sub_one_and_pos
      p n nu hn).1] at hchar
  have hpow : 1 ≤ p ^ n := Nat.one_le_iff_ne_zero.mpr (pow_ne_zero n hp.out.ne_zero)
  exact_mod_cast hchar

end RepresentationTheory.Representation.SubtypeCharacter

end
