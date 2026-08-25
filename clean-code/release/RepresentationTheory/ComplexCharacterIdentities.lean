/-
Copyright (c) 2026 mathlib-initiative. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: mathlib-initiative
-/

import Mathlib
import RepresentationTheory.ThreeCoordinateGroupRepresentations
import RepresentationTheory.FiniteGroups.CharacterRigidity
import RepresentationTheory.Representation.FiniteProducts
import RepresentationTheory.Alignment.Attribute

noncomputable section

open RepresentationTheory.ThreeCoordinateGroupRepresentations
  RepresentationTheory.ThreeCoordinateGroupRepresentations.ThreeCoordinateGroup

namespace RepresentationTheory.ComplexCharacterIdentities

variable {p : ℕ}

/-- An auxiliary predicate on a complex parameter and a complex representation on functions from `ZMod p`. -/
def AuxiliaryProperty (z : ℂ)
    (ρ : Representation ℂ
      (RepresentationTheory.ThreeCoordinateGroupRepresentations.ThreeCoordinateGroup p)
      (ZMod p → ℂ)) : Prop :=
  (∀ (f : ZMod p → ℂ) (t : ZMod p),
      (ρ
        (RepresentationTheory.ThreeCoordinateGroupRepresentations.ThreeCoordinateGroup.firstGenerator p)
        f) t = f (t - 1)) ∧
  (∀ (f : ZMod p → ℂ) (t : ZMod p),
      (ρ
        (RepresentationTheory.ThreeCoordinateGroupRepresentations.ThreeCoordinateGroup.secondGenerator p)
        f) t = z ^ t.val * f t)

/-- A representation satisfying the auxiliary property is equal to the specified canonical representation associated to the given root of unity. -/
theorem eq_canonicalRepresentation_of_auxiliaryProperty [Fact p.Prime] (z : ℂ)
    (hz : z ^ p = 1)
    (ρ : Representation ℂ
      (RepresentationTheory.ThreeCoordinateGroupRepresentations.ThreeCoordinateGroup p)
      (ZMod p → ℂ))
    (hρ : AuxiliaryProperty z ρ) :
    ρ = RepresentationTheory.ThreeCoordinateGroupRepresentations.shiftScaleRepresentation z hz := by
  haveI : NeZero p := ⟨(Fact.out : p.Prime).ne_zero⟩
  obtain ⟨w, _hw, huniq⟩ :=
    RepresentationTheory.ThreeCoordinateGroupRepresentations.existsUnique_shift_scale_representation
      z hz
  rw [huniq ρ hρ,
    huniq
      (RepresentationTheory.ThreeCoordinateGroupRepresentations.shiftScaleRepresentation z hz)
      ⟨fun f t =>
        RepresentationTheory.ThreeCoordinateGroupRepresentations.shiftScaleRepresentation_firstGenerator_apply
          z hz f t,
        fun f t =>
          RepresentationTheory.ThreeCoordinateGroupRepresentations.shiftScaleRepresentation_secondGenerator_apply
            z hz f t⟩]

/-- The sum of the powers indexed by `ZMod p` of a nontrivial complex `p`-th root of unity is zero. -/
theorem sum_powers_eq_zero [Fact p.Prime] {z : ℂ} (hz : z ^ p = 1) (hz1 : z ≠ 1) :
    ∑ u : ZMod p, z ^ u.val = 0 := by
  haveI : NeZero p := ⟨(Fact.out : p.Prime).ne_zero⟩
  haveI : Fact (1 < p) := ⟨(Fact.out : p.Prime).one_lt⟩
  have step : ∀ u : ZMod p, z * z ^ u.val = z ^ (u + 1).val := by
    intro u
    rw [← pow_succ', ZMod.val_add, ZMod.val_one,
      RepresentationTheory.ThreeCoordinateGroupRepresentations.root_pow_mod hz]
  have key : z * (∑ u : ZMod p, z ^ u.val) = ∑ u : ZMod p, z ^ u.val :=
    calc z * (∑ u : ZMod p, z ^ u.val)
        = ∑ u : ZMod p, z * z ^ u.val := by rw [Finset.mul_sum]
      _ = ∑ u : ZMod p, z ^ (u + 1).val := Finset.sum_congr rfl (fun u _ => step u)
      _ = ∑ v : ZMod p, z ^ v.val :=
            Fintype.sum_equiv (Equiv.addRight (1 : ZMod p)) _ _ (fun _ => rfl)
  have h0 : (z - 1) * (∑ u : ZMod p, z ^ u.val) = 0 := by
    rw [sub_mul, one_mul, key, sub_self]
  rcases mul_eq_zero.mp h0 with h | h
  · exact absurd (sub_eq_zero.mp h) hz1
  · exact h

/-- For a complex `p`-th root of unity, raising it to the natural representative of `-c` equals raising its inverse to the representative of `c`. -/
theorem pow_neg_val_eq_inv_pow_val [NeZero p] {z : ℂ} (hz : z ^ p = 1) (c : ZMod p) :
    z ^ ((-c).val) = (z⁻¹) ^ c.val := by
  have hmod : ((-c).val + c.val) % p = 0 := by
    have h := ZMod.val_add (-c) c
    rw [neg_add_cancel, ZMod.val_zero] at h
    exact h.symm
  have hmul : z ^ ((-c).val) * z ^ c.val = 1 := by
    rw [← pow_add,
      ← RepresentationTheory.ThreeCoordinateGroupRepresentations.root_pow_mod hz
        ((-c).val + c.val),
      hmod, pow_zero]
  rw [inv_pow, eq_comm]
  exact inv_eq_of_mul_eq_one_left hmul

/-- The trace of the specified auxiliary endomorphism is `p * z⁻¹ ^ g.c.val` when the first two coordinates of `g` vanish, and zero otherwise. -/
theorem trace_auxiliaryMap_eq_ite [Fact p.Prime] (z : ℂ) (hz : z ^ p = 1) (hz1 : z ≠ 1)
    (g : RepresentationTheory.ThreeCoordinateGroupRepresentations.ThreeCoordinateGroup p) :
    LinearMap.trace ℂ (ZMod p → ℂ)
        (RepresentationTheory.ThreeCoordinateGroupRepresentations.shiftScaleAction z g) =
      if g.firstCoordinate = 0 ∧ g.secondCoordinate = 0
        then (p : ℂ) * (z⁻¹) ^ g.thirdCoordinate.val
        else 0 := by
  haveI : NeZero p := ⟨(Fact.out : p.Prime).ne_zero⟩
  classical
  rw [LinearMap.trace_eq_matrix_trace ℂ (Pi.basisFun ℂ (ZMod p))]
  simp only [Matrix.trace, Matrix.diag_apply, LinearMap.toMatrix_apply,
    Pi.basisFun_repr, Pi.basisFun_apply,
    RepresentationTheory.ThreeCoordinateGroupRepresentations.shiftScaleAction_apply,
    Pi.single_apply, sub_eq_self]
  rw [← Finset.sum_mul]
  by_cases ha : g.firstCoordinate = 0
  · rw [if_pos ha, mul_one]
    by_cases hb : g.secondCoordinate = 0
    · rw [if_pos ⟨ha, hb⟩, hb]
      simp only [zero_mul, zero_sub]
      rw [Finset.sum_const, Finset.card_univ, ZMod.card, nsmul_eq_mul,
        pow_neg_val_eq_inv_pow_val hz g.thirdCoordinate]
    · rw [if_neg (fun h => hb h.2),
        Fintype.sum_equiv
          ((Equiv.mulLeft₀ g.secondCoordinate hb).trans (Equiv.subRight g.thirdCoordinate))
          (fun i => z ^ (g.secondCoordinate * i - g.thirdCoordinate).val)
          (fun u => z ^ u.val) (fun _ => rfl)]
      exact sum_powers_eq_zero hz hz1
  · rw [if_neg ha, mul_zero, if_neg (fun h => ha h.1)]

/-- The trace of a representation satisfying the auxiliary property is `p * z⁻¹ ^ c.val` when the first two coordinates vanish, and zero otherwise. -/
@[source_ref "Chapter4/Problem4.12.9" (role := supporting)]
theorem trace_eq_ite_of_auxiliaryProperty [Fact p.Prime] (z : ℂ) (hz : z ^ p = 1)
    (hz1 : z ≠ 1)
    (ρ : Representation ℂ
      (RepresentationTheory.ThreeCoordinateGroupRepresentations.ThreeCoordinateGroup p)
      (ZMod p → ℂ))
    (hρ : AuxiliaryProperty z ρ) (a b c : ZMod p) :
    LinearMap.trace ℂ (ZMod p → ℂ) (ρ ⟨a, b, c⟩) =
      if a = 0 ∧ b = 0 then (p : ℂ) * (z⁻¹) ^ c.val else 0 := by
  rw [eq_canonicalRepresentation_of_auxiliaryProperty z hz ρ hρ,
    RepresentationTheory.ThreeCoordinateGroupRepresentations.shiftScaleRepresentation_apply]
  exact trace_auxiliaryMap_eq_ite z hz hz1 ⟨a, b, c⟩

/-- The product of the traces associated to two nontrivial roots is `p` times the trace associated to their product. -/
theorem trace_mul_trace_eq_card_mul_trace_product [Fact p.Prime]
    (z w : ℂ) (hz : z ^ p = 1) (hw : w ^ p = 1)
    (hz1 : z ≠ 1) (hw1 : w ≠ 1) (hzw : z * w ≠ 1)
    (ρz ρw ρzw : Representation ℂ
      (RepresentationTheory.ThreeCoordinateGroupRepresentations.ThreeCoordinateGroup p)
      (ZMod p → ℂ))
    (hρz : AuxiliaryProperty z ρz) (hρw : AuxiliaryProperty w ρw)
    (hρzw : AuxiliaryProperty (z * w) ρzw)
    (g : RepresentationTheory.ThreeCoordinateGroupRepresentations.ThreeCoordinateGroup p) :
    LinearMap.trace ℂ (ZMod p → ℂ) (ρz g) *
        LinearMap.trace ℂ (ZMod p → ℂ) (ρw g) =
      (p : ℂ) * LinearMap.trace ℂ (ZMod p → ℂ) (ρzw g) := by
  obtain ⟨a, b, c⟩ := g
  rw [trace_eq_ite_of_auxiliaryProperty z hz hz1 ρz hρz a b c,
      trace_eq_ite_of_auxiliaryProperty w hw hw1 ρw hρw a b c,
      trace_eq_ite_of_auxiliaryProperty (z * w)
        (by rw [mul_pow, hz, hw, mul_one]) hzw ρzw hρzw a b c]
  by_cases h : a = 0 ∧ b = 0
  · simp only [if_pos h]
    rw [mul_inv, mul_pow]; ring
  · simp only [if_neg h, mul_zero]

/-- For representations attached by the auxiliary property to inverse roots, the product of their traces is `p ^ 2` when the first two coordinates vanish, and zero otherwise. -/
theorem trace_mul_trace_eq_ite_of_inverseRoots [Fact p.Prime]
    (z w : ℂ) (hz : z ^ p = 1) (hz1 : z ≠ 1) (hw1 : w ≠ 1) (hzw : z * w = 1)
    (ρz ρw : Representation ℂ
      (RepresentationTheory.ThreeCoordinateGroupRepresentations.ThreeCoordinateGroup p)
      (ZMod p → ℂ))
    (hρz : AuxiliaryProperty z ρz) (hρw : AuxiliaryProperty w ρw)
    (a b c : ZMod p) :
    LinearMap.trace ℂ (ZMod p → ℂ) (ρz ⟨a, b, c⟩) *
        LinearMap.trace ℂ (ZMod p → ℂ) (ρw ⟨a, b, c⟩) =
      if a = 0 ∧ b = 0 then (p : ℂ) ^ 2 else 0 := by
  have hw : w ^ p = 1 := by
    have hzwp : (z * w) ^ p = 1 := by rw [hzw, one_pow]
    rw [mul_pow, hz, one_mul] at hzwp; exact hzwp
  rw [trace_eq_ite_of_auxiliaryProperty z hz hz1 ρz hρz a b c,
      trace_eq_ite_of_auxiliaryProperty w hw hw1 ρw hρw a b c]
  by_cases h : a = 0 ∧ b = 0
  · simp only [if_pos h]
    have hone : (z⁻¹) ^ c.val * (w⁻¹) ^ c.val = 1 := by
      rw [← mul_pow, ← mul_inv, hzw, inv_one, one_pow]
    rw [show ((p : ℂ) * (z⁻¹) ^ c.val) * ((p : ℂ) * (w⁻¹) ^ c.val) =
          (p : ℂ) ^ 2 * ((z⁻¹) ^ c.val * (w⁻¹) ^ c.val) from by ring,
      hone, mul_one]
  · simp only [if_neg h, mul_zero]

/-- The trace of the one-dimensional representation associated to a multiplicative character equals the value of that character. -/
theorem trace_oneDimensionalRepresentation_eq
    (χ : RepresentationTheory.ThreeCoordinateGroupRepresentations.ThreeCoordinateGroup p →* ℂˣ)
    (g : RepresentationTheory.ThreeCoordinateGroupRepresentations.ThreeCoordinateGroup p) :
    LinearMap.trace ℂ ℂ
      (RepresentationTheory.PermutationDegreeThree.representationOfUnitCharacter χ g) =
        (χ g : ℂ) := by
  have hg : RepresentationTheory.PermutationDegreeThree.representationOfUnitCharacter χ g =
      (χ g : ℂ) • LinearMap.id := rfl
  rw [hg, map_smul, LinearMap.trace_id]
  simp

/-- The product of the traces of two one-dimensional character representations equals the trace of the representation attached to the product character. -/
theorem trace_oneDimensional_mul_eq
    (χ χ' : RepresentationTheory.ThreeCoordinateGroupRepresentations.ThreeCoordinateGroup p →* ℂˣ)
    (g : RepresentationTheory.ThreeCoordinateGroupRepresentations.ThreeCoordinateGroup p) :
    LinearMap.trace ℂ ℂ
        (RepresentationTheory.PermutationDegreeThree.representationOfUnitCharacter χ g) *
      LinearMap.trace ℂ ℂ
        (RepresentationTheory.PermutationDegreeThree.representationOfUnitCharacter χ' g) =
      LinearMap.trace ℂ ℂ
        (RepresentationTheory.PermutationDegreeThree.representationOfUnitCharacter (χ * χ') g) := by
  rw [trace_oneDimensionalRepresentation_eq, trace_oneDimensionalRepresentation_eq,
    trace_oneDimensionalRepresentation_eq, MonoidHom.mul_apply, Units.val_mul]

/-- Multiplying the trace of a representation satisfying the auxiliary property by the trace of a one-dimensional character representation leaves it unchanged. -/
theorem mul_trace_eq_trace_of_auxiliaryProperty [Fact p.Prime]
    (χ : RepresentationTheory.ThreeCoordinateGroupRepresentations.ThreeCoordinateGroup p →* ℂˣ)
    (z : ℂ) (hz : z ^ p = 1) (hz1 : z ≠ 1)
    (ρ : Representation ℂ
      (RepresentationTheory.ThreeCoordinateGroupRepresentations.ThreeCoordinateGroup p)
      (ZMod p → ℂ))
    (hρ : AuxiliaryProperty z ρ) (a b c : ZMod p) :
    LinearMap.trace ℂ ℂ
        (RepresentationTheory.PermutationDegreeThree.representationOfUnitCharacter χ ⟨a, b, c⟩) *
      LinearMap.trace ℂ (ZMod p → ℂ) (ρ ⟨a, b, c⟩) =
        LinearMap.trace ℂ (ZMod p → ℂ) (ρ ⟨a, b, c⟩) := by
  rw [trace_oneDimensionalRepresentation_eq,
    trace_eq_ite_of_auxiliaryProperty z hz hz1 ρ hρ a b c]
  by_cases h : a = 0 ∧ b = 0
  · simp only [if_pos h]
    have hcentral : χ ⟨a, b, c⟩ = 1 := by
      have hmem :
          (⟨a, b, c⟩ :
            RepresentationTheory.ThreeCoordinateGroupRepresentations.ThreeCoordinateGroup p) ∈
            (RepresentationTheory.ThreeCoordinateGroupRepresentations.coordinateQuotientHom p).ker := by
        rw [MonoidHom.mem_ker]
        change Multiplicative.ofAdd (a, b) = 1
        rw [h.1, h.2]; rfl
      exact MonoidHom.mem_ker.mp
        (RepresentationTheory.ThreeCoordinateGroupRepresentations.ker_coordinateQuotient_le_ker
          χ hmem)
    rw [hcentral, Units.val_one, one_mul]
  · simp only [if_neg h, mul_zero]

section Isomorphisms

open CategoryTheory CategoryTheory.MonoidalCategory
open scoped CategoryTheory.MonoidalCategory

variable [Fact p.Prime]

/-- The multiplicative characters from the finite group under consideration to the units of the complex numbers form a finite type. -/
instance finite_multiplicativeCharacter :
    Finite
      (RepresentationTheory.ThreeCoordinateGroupRepresentations.ThreeCoordinateGroup p →* ℂˣ) :=
  Nat.finite_of_card_ne_zero
    (by
      rw [RepresentationTheory.ThreeCoordinateGroupRepresentations.character_card_eq_square];
      exact pow_ne_zero 2 (Fact.out : p.Prime).ne_zero)

/-- A fintype structure on the multiplicative characters to the units of the complex numbers. -/
noncomputable instance multiplicativeCharacterFintype :
    Fintype
      (RepresentationTheory.ThreeCoordinateGroupRepresentations.ThreeCoordinateGroup p →* ℂˣ) :=
  Fintype.ofFinite _

/-- The character of a finite-dimensional representation is its pointwise linear trace. -/
theorem character_eq_trace
    (ρ : Representation ℂ
      (RepresentationTheory.ThreeCoordinateGroupRepresentations.ThreeCoordinateGroup p)
      (ZMod p → ℂ))
    (g : RepresentationTheory.ThreeCoordinateGroupRepresentations.ThreeCoordinateGroup p) :
    (FDRep.of ρ).character g = LinearMap.trace ℂ (ZMod p → ℂ) (ρ g) := rfl

/-- The sum of all multiplicative-character values is `p ^ 2` when the first two coordinates vanish, and zero otherwise. -/
theorem sum_multiplicativeCharacters_eq_ite (a b c : ZMod p) :
    ∑ χ : RepresentationTheory.ThreeCoordinateGroupRepresentations.ThreeCoordinateGroup p →* ℂˣ,
        (χ ⟨a, b, c⟩ : ℂ) =
      if a = 0 ∧ b = 0 then (p : ℂ) ^ 2 else 0 := by
  haveI : NeZero p := ⟨(Fact.out : p.Prime).ne_zero⟩
  haveI : Finite (Multiplicative (ZMod p × ZMod p) →* ℂˣ) :=
    Finite.of_equiv _
      (RepresentationTheory.ThreeCoordinateGroupRepresentations.characterPrecompositionEquiv p).symm
  haveI : Fintype (Multiplicative (ZMod p × ZMod p) →* ℂˣ) := Fintype.ofFinite _
  have hre :
      ∑ χ : RepresentationTheory.ThreeCoordinateGroupRepresentations.ThreeCoordinateGroup p →* ℂˣ,
          (χ ⟨a, b, c⟩ : ℂ) =
        ∑ ψ : Multiplicative (ZMod p × ZMod p) →* ℂˣ,
          ((ψ (Multiplicative.ofAdd (a, b)) : ℂ)) :=
    (Fintype.sum_equiv
      (RepresentationTheory.ThreeCoordinateGroupRepresentations.characterPrecompositionEquiv p)
      _ _ fun _ => rfl).symm
  rw [hre, RepresentationTheory.Representation.FiniteProducts.sum_additiveCharacters]
  have hiff : ((a, b) : ZMod p × ZMod p) = 0 ↔ (a = 0 ∧ b = 0) := by
    simp [Prod.ext_iff]
  have hcard : (Fintype.card (ZMod p × ZMod p) : ℂ) = (p : ℂ) ^ 2 := by
    rw [Fintype.card_prod, ZMod.card]
    push_cast
    ring
  by_cases h : a = 0 ∧ b = 0
  · rw [if_pos (hiff.mpr h), if_pos h, hcard]
  · rw [if_neg fun hab => h (hiff.mp hab), if_neg h]

/-- The tensor product of representations satisfying the auxiliary property for two roots is nonemptily isomorphic to the specified auxiliary object for the product root. -/
@[source_ref "Chapter4/Problem4.12.9" (role := supporting)]
theorem tensor_iso_auxiliaryObject
    (z w : ℂ) (hz : z ^ p = 1) (hw : w ^ p = 1)
    (hz1 : z ≠ 1) (hw1 : w ≠ 1) (hzw : z * w ≠ 1)
    (ρz ρw ρzw : Representation ℂ
      (RepresentationTheory.ThreeCoordinateGroupRepresentations.ThreeCoordinateGroup p)
      (ZMod p → ℂ))
    (hρz : AuxiliaryProperty z ρz) (hρw : AuxiliaryProperty w ρw)
    (hρzw : AuxiliaryProperty (z * w) ρzw) :
    Nonempty ((FDRep.of ρz ⊗ FDRep.of ρw :
        FDRep ℂ
          (RepresentationTheory.ThreeCoordinateGroupRepresentations.ThreeCoordinateGroup p)) ≅
      RepresentationTheory.Representation.FiniteProducts.finiteProduct
        fun _ : Fin p => FDRep.of ρzw) := by
  refine RepresentationTheory.FiniteGroups.CharacterRigidity.nonempty_iso_of_character_eq
    _ _ (funext fun g => ?_)
  rw [FDRep.char_tensor, Pi.mul_apply,
    RepresentationTheory.Representation.FiniteProducts.character_finiteProduct,
    Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul,
    character_eq_trace, character_eq_trace, character_eq_trace]
  exact trace_mul_trace_eq_card_mul_trace_product
    z w hz hw hz1 hw1 hzw ρz ρw ρzw hρz hρw hρzw g

/-- The tensor product of representations associated to inverse nontrivial roots is nonemptily isomorphic to the specified auxiliary object formed from all multiplicative-character representations. -/
@[source_ref "Chapter4/Problem4.12.9" (role := supporting)]
theorem tensor_iso_multiplicativeCharacterAuxiliaryObject
    (z w : ℂ) (hz : z ^ p = 1) (hz1 : z ≠ 1) (hw1 : w ≠ 1) (hzw : z * w = 1)
    (ρz ρw : Representation ℂ
      (RepresentationTheory.ThreeCoordinateGroupRepresentations.ThreeCoordinateGroup p)
      (ZMod p → ℂ))
    (hρz : AuxiliaryProperty z ρz) (hρw : AuxiliaryProperty w ρw) :
    Nonempty ((FDRep.of ρz ⊗ FDRep.of ρw :
        FDRep ℂ
          (RepresentationTheory.ThreeCoordinateGroupRepresentations.ThreeCoordinateGroup p)) ≅
      RepresentationTheory.Representation.FiniteProducts.finiteProduct
        fun χ :
            RepresentationTheory.ThreeCoordinateGroupRepresentations.ThreeCoordinateGroup p →* ℂˣ =>
          FDRep.of
            (RepresentationTheory.PermutationDegreeThree.representationOfUnitCharacter χ)) := by
  refine RepresentationTheory.FiniteGroups.CharacterRigidity.nonempty_iso_of_character_eq
    _ _ (funext fun g => ?_)
  obtain ⟨a, b, c⟩ := g
  rw [FDRep.char_tensor, Pi.mul_apply,
    RepresentationTheory.Representation.FiniteProducts.character_finiteProduct,
    character_eq_trace, character_eq_trace]
  simp only
    [RepresentationTheory.PermutationDegreeThree.character_representationOfUnitCharacter]
  rw [sum_multiplicativeCharacters_eq_ite a b c]
  exact trace_mul_trace_eq_ite_of_inverseRoots z w hz hz1 hw1 hzw ρz ρw hρz hρw a b c

/-- The tensor product of representations satisfying the auxiliary property for two roots is nonemptily isomorphic to the displayed biproduct of the product-root representation. -/
@[source_ref "Chapter4/Problem4.12.9" (role := supporting)]
theorem tensor_iso_biproduct
    (z w : ℂ) (hz : z ^ p = 1) (hw : w ^ p = 1)
    (hz1 : z ≠ 1) (hw1 : w ≠ 1) (hzw : z * w ≠ 1)
    (ρz ρw ρzw : Representation ℂ
      (RepresentationTheory.ThreeCoordinateGroupRepresentations.ThreeCoordinateGroup p)
      (ZMod p → ℂ))
    (hρz : AuxiliaryProperty z ρz) (hρw : AuxiliaryProperty w ρw)
    (hρzw : AuxiliaryProperty (z * w) ρzw) :
    Nonempty ((FDRep.of ρz ⊗ FDRep.of ρw :
        FDRep ℂ
          (RepresentationTheory.ThreeCoordinateGroupRepresentations.ThreeCoordinateGroup p)) ≅
      ⨁ fun _ : Fin p => FDRep.of ρzw) :=
  (tensor_iso_auxiliaryObject z w hz hw hz1 hw1 hzw ρz ρw ρzw hρz hρw hρzw).map fun e =>
    e ≪≫ RepresentationTheory.Representation.FiniteProducts.finiteProductIsoBiproduct _

/-- The tensor product of representations associated to inverse nontrivial roots is nonemptily isomorphic to the biproduct of all one-dimensional multiplicative-character representations. -/
@[source_ref "Chapter4/Problem4.12.9" (role := supporting)]
theorem tensor_iso_multiplicativeCharacterBiproduct
    (z w : ℂ) (hz : z ^ p = 1) (hz1 : z ≠ 1) (hw1 : w ≠ 1) (hzw : z * w = 1)
    (ρz ρw : Representation ℂ
      (RepresentationTheory.ThreeCoordinateGroupRepresentations.ThreeCoordinateGroup p)
      (ZMod p → ℂ))
    (hρz : AuxiliaryProperty z ρz) (hρw : AuxiliaryProperty w ρw) :
    Nonempty ((FDRep.of ρz ⊗ FDRep.of ρw :
        FDRep ℂ
          (RepresentationTheory.ThreeCoordinateGroupRepresentations.ThreeCoordinateGroup p)) ≅
      ⨁ fun χ :
          RepresentationTheory.ThreeCoordinateGroupRepresentations.ThreeCoordinateGroup p →* ℂˣ =>
        FDRep.of
          (RepresentationTheory.PermutationDegreeThree.representationOfUnitCharacter χ)) := by
  classical
  exact
    (tensor_iso_multiplicativeCharacterAuxiliaryObject z w hz hz1 hw1 hzw
      ρz ρw hρz hρw).map fun e =>
        e ≪≫ RepresentationTheory.Representation.FiniteProducts.finiteProductIsoBiproduct _

omit [Fact p.Prime] in
/-- The tensor product of the one-dimensional representations attached to two multiplicative characters is isomorphic to the representation attached to their product. -/
@[source_ref "Chapter4/Problem4.12.9" (role := supporting)]
def tensorMultiplicativeCharacterIso
    (χ χ' :
      RepresentationTheory.ThreeCoordinateGroupRepresentations.ThreeCoordinateGroup p →* ℂˣ) :
    (FDRep.of (RepresentationTheory.PermutationDegreeThree.representationOfUnitCharacter χ) ⊗
        FDRep.of
          (RepresentationTheory.PermutationDegreeThree.representationOfUnitCharacter χ') :
      FDRep ℂ
        (RepresentationTheory.ThreeCoordinateGroupRepresentations.ThreeCoordinateGroup p)) ≅
      FDRep.of
        (RepresentationTheory.PermutationDegreeThree.representationOfUnitCharacter (χ * χ')) :=
  Action.mkIso (TensorProduct.lid ℂ ℂ).toFGModuleCatIso fun g => by
    apply FGModuleCat.hom_ext
    refine TensorProduct.ext' fun a b => ?_
    change (TensorProduct.lid ℂ ℂ)
        (TensorProduct.map
          ((RepresentationTheory.PermutationDegreeThree.representationOfUnitCharacter χ) g)
          ((RepresentationTheory.PermutationDegreeThree.representationOfUnitCharacter χ') g)
          (a ⊗ₜ[ℂ] b)) =
      (RepresentationTheory.PermutationDegreeThree.representationOfUnitCharacter (χ * χ')) g
        ((TensorProduct.lid ℂ ℂ) (a ⊗ₜ[ℂ] b))
    simp only [TensorProduct.map_tmul, TensorProduct.lid_tmul,
      RepresentationTheory.PermutationDegreeThree.representationOfUnitCharacter,
      MonoidHom.coe_mk, OneHom.coe_mk, LinearMap.smul_apply, LinearMap.id_coe, id_eq,
      MonoidHom.mul_apply, Units.val_mul, smul_eq_mul]
    ring

omit [Fact p.Prime] in
/-- The tensor product of two one-dimensional multiplicative-character representations is nonemptily isomorphic to the representation of the product character. -/
@[source_ref "Chapter4/Problem4.12.9" (role := supporting)]
theorem tensor_multiplicativeCharacter_iso_mul
    (χ χ' :
      RepresentationTheory.ThreeCoordinateGroupRepresentations.ThreeCoordinateGroup p →* ℂˣ) :
    Nonempty
      ((FDRep.of
          (RepresentationTheory.PermutationDegreeThree.representationOfUnitCharacter χ) ⊗
          FDRep.of
            (RepresentationTheory.PermutationDegreeThree.representationOfUnitCharacter χ') :
        FDRep ℂ
          (RepresentationTheory.ThreeCoordinateGroupRepresentations.ThreeCoordinateGroup p)) ≅
        FDRep.of
          (RepresentationTheory.PermutationDegreeThree.representationOfUnitCharacter (χ * χ'))) :=
  ⟨tensorMultiplicativeCharacterIso χ χ'⟩

/-- Tensoring a representation satisfying the auxiliary property with a one-dimensional multiplicative-character representation yields an isomorphic representation. -/
@[source_ref "Chapter4/Problem4.12.9" (role := supporting)]
theorem tensor_multiplicativeCharacter_iso_self
    (χ : RepresentationTheory.ThreeCoordinateGroupRepresentations.ThreeCoordinateGroup p →* ℂˣ)
    (z : ℂ) (hz : z ^ p = 1) (hz1 : z ≠ 1)
    (ρ : Representation ℂ
      (RepresentationTheory.ThreeCoordinateGroupRepresentations.ThreeCoordinateGroup p)
      (ZMod p → ℂ))
    (hρ : AuxiliaryProperty z ρ) :
    Nonempty
      ((FDRep.of
          (RepresentationTheory.PermutationDegreeThree.representationOfUnitCharacter χ) ⊗
          FDRep.of ρ :
        FDRep ℂ
          (RepresentationTheory.ThreeCoordinateGroupRepresentations.ThreeCoordinateGroup p)) ≅
        FDRep.of ρ) := by
  refine RepresentationTheory.FiniteGroups.CharacterRigidity.nonempty_iso_of_character_eq
    _ _ (funext fun g => ?_)
  obtain ⟨a, b, c⟩ := g
  rw [FDRep.char_tensor, Pi.mul_apply, character_eq_trace,
    RepresentationTheory.PermutationDegreeThree.character_representationOfUnitCharacter,
    ← trace_oneDimensionalRepresentation_eq χ
      (⟨a, b, c⟩ :
        RepresentationTheory.ThreeCoordinateGroupRepresentations.ThreeCoordinateGroup p)]
  exact mul_trace_eq_trace_of_auxiliaryProperty χ z hz hz1 ρ hρ a b c

end Isomorphisms

end RepresentationTheory.ComplexCharacterIdentities
