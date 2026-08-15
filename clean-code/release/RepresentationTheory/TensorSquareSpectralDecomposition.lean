/-
Copyright (c) 2026 mathlib-initiative. All rights reserved.
Released under Apache 2.0 license as described in the file LICENCE.
Authors: mathlib-initiative
-/

import RepresentationTheory.AlternatingTensorSquare
import RepresentationTheory.Alignment.Attribute

/-!
# Tensor-square spectral decomposition

A spectral decomposition of an alternating tensor square and an indexed family of simple complex
representations.
-/

namespace RepresentationTheory.TensorSquareSpectralDecomposition

open RepresentationTheory.AlternatingTensorSquare
open RepresentationTheory.Group.PermutationSubgroupData
open RepresentationTheory.PermutationActionRepresentations
open RepresentationTheory.QuaternionGroupTwo
open RepresentationTheory.QuaternionGroupTwo.AuxiliaryType

open Equiv CategoryTheory
open scoped TensorProduct

noncomputable section

set_option linter.unusedSectionVars false
set_option linter.unusedFintypeInType false
set_option linter.unusedDecidableInType false

set_option synthInstance.maxHeartbeats 400000 in
/-- The additive commutative group structure on the carrier of the distinguished subrepresentation.
-/
local instance distinguishedSubrepresentationAddCommGroup : AddCommGroup
  ↑auxiliaryTensorSquareSubrepresentation.toSubmodule := inferInstance

/-- An auxiliary element of the distinguished group subtype. -/
def auxiliaryGroupElement : permutationSubgroupFin5 := conjugacyClassRepresentative 3

/-- The tensor-square endomorphism restricted to the distinguished subrepresentation. -/
def restrictedTensorSquareEndomorphism : Module.End ℂ
  ↥auxiliaryTensorSquareSubrepresentation.toSubmodule :=
  ∑ g : permutationSubgroupFin5, auxiliaryTensorSquareSubrepresentation.toRepresentation (g *
    auxiliaryGroupElement * g⁻¹)

/-- The restricted endomorphism commutes with the action on the distinguished subrepresentation. -/
lemma restrictedTensorSquareEndomorphism_commutes (h : permutationSubgroupFin5) : Commute
  (auxiliaryTensorSquareSubrepresentation.toRepresentation h) restrictedTensorSquareEndomorphism :=
  by
  change auxiliaryTensorSquareSubrepresentation.toRepresentation h *
    restrictedTensorSquareEndomorphism = restrictedTensorSquareEndomorphism *
    auxiliaryTensorSquareSubrepresentation.toRepresentation h
  rw [restrictedTensorSquareEndomorphism, Finset.mul_sum, Finset.sum_mul,
    ← Equiv.sum_comp (Equiv.mulLeft h⁻¹)
      (fun g => auxiliaryTensorSquareSubrepresentation.toRepresentation h *
        auxiliaryTensorSquareSubrepresentation.toRepresentation
          (g * auxiliaryGroupElement * g⁻¹))]
  refine Finset.sum_congr rfl fun g _ => ?_
  simp only [Equiv.coe_mulLeft]
  rw [← map_mul, ← map_mul]
  congr 1
  group

/-- The restricted tensor-square endomorphism has trace sixty. -/
lemma trace_restrictedTensorSquareEndomorphism : LinearMap.trace ℂ
  (↥auxiliaryTensorSquareSubrepresentation.toSubmodule) restrictedTensorSquareEndomorphism = 60 :=
  by
  have hchar : ∀ x : permutationSubgroupFin5,
      LinearMap.trace ℂ (↥auxiliaryTensorSquareSubrepresentation.toSubmodule)
        (auxiliaryTensorSquareSubrepresentation.toRepresentation x)
        = alternatingSquareRepresentation.character x := fun x => rfl
  have hterm : ∀ g : permutationSubgroupFin5,
      LinearMap.trace ℂ (↥auxiliaryTensorSquareSubrepresentation.toSubmodule)
        (auxiliaryTensorSquareSubrepresentation.toRepresentation
          (g * auxiliaryGroupElement * g⁻¹))
        = 1 := by
    intro g
    rw [hchar, FDRep.char_conj, auxiliaryGroupElement]
    simpa using auxiliaryUnavailableStatement 3
  rw [restrictedTensorSquareEndomorphism, map_sum, Finset.sum_congr rfl (fun g _ => hterm g),
    Finset.sum_const,
    Finset.card_univ, nsmul_eq_mul, mul_one]
  have hcard : (Fintype.card permutationSubgroupFin5 : ℂ) = 60 := by
    rw [← Nat.card_eq_fintype_card, card_permutationSubgroupFin5]; norm_num
  rw [hcard]

/-- A complex-linear endomorphism of the tensor square of the distinguished coordinate submodule. -/
def tensorSquareEndomorphism : Module.End ℂ (auxiliaryCoordinateSubmodule ⊗[ℂ]
  auxiliaryCoordinateSubmodule) :=
  ∑ g : permutationSubgroupFin5, (coordinateRepresentation.tprod coordinateRepresentation) (g *
    auxiliaryGroupElement * g⁻¹)

/-- The tensor-square endomorphism commutes with every operator of the tensor-product
representation. -/
lemma tensorSquareEndomorphism_commutes (h : permutationSubgroupFin5) : Commute
  ((coordinateRepresentation.tprod coordinateRepresentation) h) tensorSquareEndomorphism := by
  change (coordinateRepresentation.tprod coordinateRepresentation) h * tensorSquareEndomorphism =
    tensorSquareEndomorphism * (coordinateRepresentation.tprod coordinateRepresentation) h
  rw [tensorSquareEndomorphism, Finset.mul_sum, Finset.sum_mul,
    ← Equiv.sum_comp (Equiv.mulLeft h⁻¹)
      (fun g => (coordinateRepresentation.tprod coordinateRepresentation) h *
        (coordinateRepresentation.tprod coordinateRepresentation) (g * auxiliaryGroupElement *
        g⁻¹))]
  refine Finset.sum_congr rfl fun g _ => ?_
  simp only [Equiv.coe_mulLeft]
  rw [← map_mul, ← map_mul]
  congr 1
  group

/-- The tensor-square endomorphism commutes with the displayed auxiliary endomorphism. -/
lemma tensorSquareEndomorphism_commutes_with_auxiliaryEndomorphism : Commute equivariantIdempotent
  tensorSquareEndomorphism := by
  change equivariantIdempotent * tensorSquareEndomorphism = tensorSquareEndomorphism *
    equivariantIdempotent
  rw [tensorSquareEndomorphism, Finset.mul_sum, Finset.sum_mul]
  exact Finset.sum_congr rfl fun g _ => equivariantIdempotent_commutes (g * auxiliaryGroupElement *
    g⁻¹)

/-- The tensor-square endomorphism preserves the distinguished tensor-square subrepresentation. -/
lemma tensorSquareEndomorphism_preserves_subrepresentation : ∀ v ∈
  auxiliaryTensorSquareSubrepresentation.toSubmodule, tensorSquareEndomorphism v ∈
  auxiliaryTensorSquareSubrepresentation.toSubmodule := by
  intro v hv
  rw [tensorSquareEndomorphism, LinearMap.sum_apply]
  exact Submodule.sum_mem _ fun g _ => auxiliaryTensorSquareSubrepresentation.apply_mem_toSubmodule
    (g * auxiliaryGroupElement * g⁻¹) hv

/-- The underlying value of the restricted endomorphism agrees with the ambient tensor-square
endomorphism. -/
lemma coe_restrictedTensorSquareEndomorphism_apply (v :
  ↥auxiliaryTensorSquareSubrepresentation.toSubmodule) :
    ((restrictedTensorSquareEndomorphism v :
        ↥auxiliaryTensorSquareSubrepresentation.toSubmodule) :
      auxiliaryCoordinateSubmodule ⊗[ℂ] auxiliaryCoordinateSubmodule) =
        tensorSquareEndomorphism
          (v : auxiliaryCoordinateSubmodule ⊗[ℂ] auxiliaryCoordinateSubmodule) := by
  simp only [restrictedTensorSquareEndomorphism, tensorSquareEndomorphism, LinearMap.sum_apply,
    Submodule.coe_sum]
  rfl

/-- Membership in a restricted eigenspace is equivalent to ambient eigenspace membership of the
underlying vector. -/
lemma mem_restricted_eigenspace_iff (μ : ℂ) (v :
  ↥auxiliaryTensorSquareSubrepresentation.toSubmodule) :
    v ∈ Module.End.eigenspace restrictedTensorSquareEndomorphism μ
      ↔ (v : auxiliaryCoordinateSubmodule ⊗[ℂ] auxiliaryCoordinateSubmodule) ∈
        Module.End.eigenspace tensorSquareEndomorphism μ := by
  rw [Module.End.mem_eigenspace_iff, Module.End.mem_eigenspace_iff, Subtype.ext_iff,
    coe_restrictedTensorSquareEndomorphism_apply,
    Submodule.coe_smul]

/-- The second auxiliary complex spectral value. -/
noncomputable def secondSpectralValue : ℂ := 10 + 10 * (Real.sqrt 5 : ℂ)

/-- The first auxiliary complex spectral value. -/
noncomputable def firstSpectralValue : ℂ := 10 - 10 * (Real.sqrt 5 : ℂ)

/-- A subrepresentation of the tensor-product representation associated with the second spectral
summand. -/
def secondSpectralSubrepresentation : Subrepresentation (coordinateRepresentation.tprod
  coordinateRepresentation) where
  toSubmodule := auxiliaryTensorSquareSubrepresentation.toSubmodule ⊓ Module.End.eigenspace
    tensorSquareEndomorphism secondSpectralValue
  apply_mem_toSubmodule h v hv := by
    rw [Submodule.mem_inf] at hv ⊢
    exact ⟨auxiliaryTensorSquareSubrepresentation.apply_mem_toSubmodule h hv.1,
      Module.End.mapsTo_genEigenspace_of_comm (tensorSquareEndomorphism_commutes h).symm
        secondSpectralValue 1 hv.2⟩

/-- A subrepresentation of the tensor-product representation associated with the first spectral
summand. -/
def firstSpectralSubrepresentation : Subrepresentation (coordinateRepresentation.tprod
  coordinateRepresentation) where
  toSubmodule := auxiliaryTensorSquareSubrepresentation.toSubmodule ⊓ Module.End.eigenspace
    tensorSquareEndomorphism firstSpectralValue
  apply_mem_toSubmodule h v hv := by
    rw [Submodule.mem_inf] at hv ⊢
    exact ⟨auxiliaryTensorSquareSubrepresentation.apply_mem_toSubmodule h hv.1,
      Module.End.mapsTo_genEigenspace_of_comm (tensorSquareEndomorphism_commutes h).symm
        firstSpectralValue 1 hv.2⟩

/-- An auxiliary finite-dimensional complex representation. -/
def auxiliaryRepresentationTwo : FDRep ℂ permutationSubgroupFin5 := FDRep.of
  secondSpectralSubrepresentation.toRepresentation

/-- An auxiliary finite-dimensional complex representation. -/
def auxiliaryRepresentationOne : FDRep ℂ permutationSubgroupFin5 := FDRep.of
  firstSpectralSubrepresentation.toRepresentation

/-- The second spectral subrepresentation is the image of the second eigenspace under the ambient
subtype map. -/
lemma secondSpectralSubrepresentation_toSubmodule :
    secondSpectralSubrepresentation.toSubmodule
      = (Module.End.eigenspace restrictedTensorSquareEndomorphism secondSpectralValue).map
        auxiliaryTensorSquareSubrepresentation.toSubmodule.subtype := by
  ext x
  rw [show secondSpectralSubrepresentation.toSubmodule
      = auxiliaryTensorSquareSubrepresentation.toSubmodule ⊓ Module.End.eigenspace
        tensorSquareEndomorphism secondSpectralValue from rfl,
    Submodule.mem_inf, Submodule.mem_map]
  constructor
  · rintro ⟨hx, hxe⟩
    exact
      ⟨⟨x, hx⟩,
        (mem_restricted_eigenspace_iff secondSpectralValue ⟨x, hx⟩).mpr hxe, rfl⟩
  · rintro ⟨⟨y, hy⟩, hye, rfl⟩
    exact ⟨hy, (mem_restricted_eigenspace_iff secondSpectralValue ⟨y, hy⟩).mp hye⟩

/-- The first spectral subrepresentation is the image of the first eigenspace under the ambient
subtype map. -/
lemma firstSpectralSubrepresentation_toSubmodule :
    firstSpectralSubrepresentation.toSubmodule
      = (Module.End.eigenspace restrictedTensorSquareEndomorphism firstSpectralValue).map
        auxiliaryTensorSquareSubrepresentation.toSubmodule.subtype := by
  ext x
  rw [show firstSpectralSubrepresentation.toSubmodule
      = auxiliaryTensorSquareSubrepresentation.toSubmodule ⊓ Module.End.eigenspace
        tensorSquareEndomorphism firstSpectralValue from rfl,
    Submodule.mem_inf, Submodule.mem_map]
  constructor
  · rintro ⟨hx, hxe⟩
    exact
      ⟨⟨x, hx⟩, (mem_restricted_eigenspace_iff firstSpectralValue ⟨x, hx⟩).mpr hxe, rfl⟩
  · rintro ⟨⟨y, hy⟩, hye, rfl⟩
    exact ⟨hy, (mem_restricted_eigenspace_iff firstSpectralValue ⟨y, hy⟩).mp hye⟩

/-- The second spectral subrepresentation has the same dimension as the second eigenspace. -/
lemma finrank_secondSpectralSubrepresentation_eq :
    Module.finrank ℂ secondSpectralSubrepresentation.toSubmodule
      = Module.finrank ℂ (Module.End.eigenspace restrictedTensorSquareEndomorphism
        secondSpectralValue) := by
  rw [secondSpectralSubrepresentation_toSubmodule, Submodule.finrank_map_subtype_eq]

/-- The first spectral subrepresentation has the same dimension as the first eigenspace. -/
lemma finrank_firstSpectralSubrepresentation_eq :
    Module.finrank ℂ firstSpectralSubrepresentation.toSubmodule
      = Module.finrank ℂ (Module.End.eigenspace restrictedTensorSquareEndomorphism
        firstSpectralValue) := by
  rw [firstSpectralSubrepresentation_toSubmodule, Submodule.finrank_map_subtype_eq]

/-- The trace of the restricted endomorphism composed with an action operator is the displayed
finite character sum. -/
lemma trace_restrictedTensorSquareEndomorphism_mul_action (g : permutationSubgroupFin5) :
    LinearMap.trace ℂ (↥auxiliaryTensorSquareSubrepresentation.toSubmodule)
      (restrictedTensorSquareEndomorphism * auxiliaryTensorSquareSubrepresentation.toRepresentation
      g)
      = ∑ h : permutationSubgroupFin5, alternatingSquareRepresentation.character (h *
        auxiliaryGroupElement * h⁻¹ * g) := by
  have hchar : ∀ x : permutationSubgroupFin5, LinearMap.trace ℂ
    (↥auxiliaryTensorSquareSubrepresentation.toSubmodule)
    (auxiliaryTensorSquareSubrepresentation.toRepresentation x)
      = alternatingSquareRepresentation.character x := fun _ => rfl
  rw [restrictedTensorSquareEndomorphism, Finset.sum_mul, map_sum]
  refine Finset.sum_congr rfl fun h _ => ?_
  rw [← map_mul, hchar]

set_option maxRecDepth 8000 in
set_option maxHeartbeats 4000000 in

/-- An auxiliary statement whose formal type was unavailable. -/
lemma auxiliaryUnavailableStatementTwo (j : Fin 5) :
    LinearMap.trace ℂ (↥auxiliaryTensorSquareSubrepresentation.toSubmodule)
      (restrictedTensorSquareEndomorphism * auxiliaryTensorSquareSubrepresentation.toRepresentation
      (conjugacyClassRepresentative j))
      = (![60, 0, -20, 60, -40] j : ℂ) := by
  rw [trace_restrictedTensorSquareEndomorphism_mul_action]
  have hchar : ∀ y : permutationSubgroupFin5, alternatingSquareRepresentation.character y
      = (2⁻¹ : ℂ) *
        ((((fixedPointCount (G := permutationSubgroupFin5) (α := Fin 5) y : ℤ) - 1) ^ 2 -
          ((fixedPointCount (G := permutationSubgroupFin5) (α := Fin 5) (y * y) : ℤ) - 1) :
          ℤ) : ℂ) := by
    intro y
    rw [character_alternatingSquareRepresentation,
      RepresentationTheory.IndexedPermutationFinsetAction.character_auxiliaryRepresentationOne,
      RepresentationTheory.IndexedPermutationFinsetAction.character_auxiliaryRepresentationOne]
    push_cast; ring
  have key : ∀ i : Fin 5,
      (∑ h : permutationSubgroupFin5,
        (((fixedPointCount (G := permutationSubgroupFin5) (α := Fin 5)
          (h * auxiliaryGroupElement * h⁻¹ * conjugacyClassRepresentative i) : ℤ) - 1) ^ 2
        - ((fixedPointCount (G := permutationSubgroupFin5) (α := Fin 5) ((h * auxiliaryGroupElement
          * h⁻¹ * conjugacyClassRepresentative i)
            * (h * auxiliaryGroupElement * h⁻¹ * conjugacyClassRepresentative i)) : ℤ) - 1)))
      = ![120, 0, -40, 120, -80] i := by decide
  rw [Finset.sum_congr rfl (fun h _ => hchar _), ← Finset.mul_sum, ← Int.cast_sum, key j]
  fin_cases j <;> norm_num

/-- The square of the restricted endomorphism has trace three thousand six hundred. -/
lemma trace_restrictedTensorSquareEndomorphism_sq : LinearMap.trace ℂ
  (↥auxiliaryTensorSquareSubrepresentation.toSubmodule) (restrictedTensorSquareEndomorphism *
  restrictedTensorSquareEndomorphism) = 3600 := by
  have hconj : ∀ g : permutationSubgroupFin5,
      LinearMap.trace ℂ (↥auxiliaryTensorSquareSubrepresentation.toSubmodule)
        (restrictedTensorSquareEndomorphism *
        auxiliaryTensorSquareSubrepresentation.toRepresentation
          (g * auxiliaryGroupElement * g⁻¹))
        = LinearMap.trace ℂ (↥auxiliaryTensorSquareSubrepresentation.toSubmodule)
          (restrictedTensorSquareEndomorphism *
          auxiliaryTensorSquareSubrepresentation.toRepresentation auxiliaryGroupElement) := by
    intro g
    have hc : auxiliaryTensorSquareSubrepresentation.toRepresentation g *
      restrictedTensorSquareEndomorphism = restrictedTensorSquareEndomorphism *
      auxiliaryTensorSquareSubrepresentation.toRepresentation g :=
      (restrictedTensorSquareEndomorphism_commutes g).eq
    have hrw : restrictedTensorSquareEndomorphism *
      auxiliaryTensorSquareSubrepresentation.toRepresentation (g * auxiliaryGroupElement * g⁻¹)
        = auxiliaryTensorSquareSubrepresentation.toRepresentation g *
          (restrictedTensorSquareEndomorphism *
          auxiliaryTensorSquareSubrepresentation.toRepresentation auxiliaryGroupElement)
            * auxiliaryTensorSquareSubrepresentation.toRepresentation g⁻¹ := by
      rw [map_mul, map_mul]
      simp only [← mul_assoc]
      rw [hc]
    rw [hrw, LinearMap.trace_mul_comm, ← mul_assoc, ← map_mul, inv_mul_cancel, map_one, one_mul]
  have hz2 : restrictedTensorSquareEndomorphism * restrictedTensorSquareEndomorphism = ∑ g :
    permutationSubgroupFin5, restrictedTensorSquareEndomorphism *
    auxiliaryTensorSquareSubrepresentation.toRepresentation
      (g * auxiliaryGroupElement * g⁻¹) := by
    rw [← Finset.mul_sum]; rfl
  rw [hz2, map_sum, Finset.sum_congr rfl (fun g _ => hconj g), Finset.sum_const, Finset.card_univ,
    nsmul_eq_mul]
  have hr5 : LinearMap.trace ℂ (↥auxiliaryTensorSquareSubrepresentation.toSubmodule)
    (restrictedTensorSquareEndomorphism * auxiliaryTensorSquareSubrepresentation.toRepresentation
    auxiliaryGroupElement) = 60 := by
    have h := auxiliaryUnavailableStatementTwo 3
    rw [show conjugacyClassRepresentative 3 = auxiliaryGroupElement from rfl] at h
    rw [h]
    norm_num [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
      Matrix.cons_val_three, Matrix.cons_val_four, Matrix.head_cons, Matrix.tail_cons]
  have hcard : (Fintype.card permutationSubgroupFin5 : ℂ) = 60 := by
    rw [← Nat.card_eq_fintype_card, card_permutationSubgroupFin5]; norm_num
  rw [hr5, hcard]; norm_num

set_option maxRecDepth 8000 in
set_option maxHeartbeats 4000000 in

/-- The trace of the cube of the restricted endomorphism is ninety-six thousand. -/
lemma trace_restrictedTensorSquareEndomorphism_cube :
    LinearMap.trace ℂ (↥auxiliaryTensorSquareSubrepresentation.toSubmodule)
      (restrictedTensorSquareEndomorphism * restrictedTensorSquareEndomorphism *
      restrictedTensorSquareEndomorphism) = 96000 := by

  have hconj : ∀ g : permutationSubgroupFin5,
      LinearMap.trace ℂ (↥auxiliaryTensorSquareSubrepresentation.toSubmodule)
          (restrictedTensorSquareEndomorphism * restrictedTensorSquareEndomorphism *
            auxiliaryTensorSquareSubrepresentation.toRepresentation (g * auxiliaryGroupElement *
            g⁻¹))
        = LinearMap.trace ℂ (↥auxiliaryTensorSquareSubrepresentation.toSubmodule)
          (restrictedTensorSquareEndomorphism * restrictedTensorSquareEndomorphism *
            auxiliaryTensorSquareSubrepresentation.toRepresentation auxiliaryGroupElement) := by
    intro g
    have hcomm : Commute (auxiliaryTensorSquareSubrepresentation.toRepresentation g)
      (restrictedTensorSquareEndomorphism * restrictedTensorSquareEndomorphism) :=
      (restrictedTensorSquareEndomorphism_commutes g).mul_right
        (restrictedTensorSquareEndomorphism_commutes g)
    have hrw : restrictedTensorSquareEndomorphism * restrictedTensorSquareEndomorphism *
      auxiliaryTensorSquareSubrepresentation.toRepresentation (g * auxiliaryGroupElement * g⁻¹)
        = auxiliaryTensorSquareSubrepresentation.toRepresentation g *
          (restrictedTensorSquareEndomorphism * restrictedTensorSquareEndomorphism *
          auxiliaryTensorSquareSubrepresentation.toRepresentation auxiliaryGroupElement)
            * auxiliaryTensorSquareSubrepresentation.toRepresentation g⁻¹ := by
      rw [map_mul, map_mul, ← mul_assoc, ← mul_assoc, ← hcomm.eq,
        mul_assoc (auxiliaryTensorSquareSubrepresentation.toRepresentation g)]
    rw [hrw, LinearMap.trace_mul_comm, ← mul_assoc, ← map_mul, inv_mul_cancel, map_one, one_mul]
  have hz3 : restrictedTensorSquareEndomorphism * restrictedTensorSquareEndomorphism *
    restrictedTensorSquareEndomorphism
      = ∑ g : permutationSubgroupFin5, restrictedTensorSquareEndomorphism *
        restrictedTensorSquareEndomorphism * auxiliaryTensorSquareSubrepresentation.toRepresentation
        (g * auxiliaryGroupElement * g⁻¹) := by
    rw [← Finset.mul_sum]; rfl
  rw [hz3, map_sum, Finset.sum_congr rfl (fun g _ => hconj g), Finset.sum_const,
    Finset.card_univ, nsmul_eq_mul]

  have htr_conj : ∀ (c x : permutationSubgroupFin5),
      LinearMap.trace ℂ (↥auxiliaryTensorSquareSubrepresentation.toSubmodule)
        (restrictedTensorSquareEndomorphism *
        auxiliaryTensorSquareSubrepresentation.toRepresentation (c * x * c⁻¹))
        = LinearMap.trace ℂ (↥auxiliaryTensorSquareSubrepresentation.toSubmodule)
          (restrictedTensorSquareEndomorphism *
          auxiliaryTensorSquareSubrepresentation.toRepresentation x) := by
    intro c x
    have hc : auxiliaryTensorSquareSubrepresentation.toRepresentation c *
      restrictedTensorSquareEndomorphism = restrictedTensorSquareEndomorphism *
      auxiliaryTensorSquareSubrepresentation.toRepresentation c :=
      (restrictedTensorSquareEndomorphism_commutes c).eq
    have hrw : restrictedTensorSquareEndomorphism *
      auxiliaryTensorSquareSubrepresentation.toRepresentation (c * x * c⁻¹)
        = auxiliaryTensorSquareSubrepresentation.toRepresentation c *
          (restrictedTensorSquareEndomorphism *
          auxiliaryTensorSquareSubrepresentation.toRepresentation x)
            * auxiliaryTensorSquareSubrepresentation.toRepresentation c⁻¹ := by
      rw [map_mul, map_mul]
      simp only [← mul_assoc]
      rw [hc]
    rw [hrw, LinearMap.trace_mul_comm, ← mul_assoc, ← map_mul, inv_mul_cancel, map_one, one_mul]

  have hvec : ∀ j : Fin 5,
      (![60, 0, -20, 60, -40] j : ℂ) =
        (((![60, 0, -20, 60, -40] : Fin 5 → ℤ) j : ℤ) : ℂ) := by
    intro j; fin_cases j <;> norm_num

  have htable : ∀ y : permutationSubgroupFin5,
      LinearMap.trace ℂ (↥auxiliaryTensorSquareSubrepresentation.toSubmodule)
        (restrictedTensorSquareEndomorphism *
        auxiliaryTensorSquareSubrepresentation.toRepresentation y)
        = (((![60, 0, -20, 60, -40] : Fin 5 → ℤ) (conjugacyClassIndex y) : ℤ) : ℂ) := by
    intro y
    obtain ⟨c, hc⟩ := exists_conj_classRepresentative y

    have key : LinearMap.trace ℂ (↥auxiliaryTensorSquareSubrepresentation.toSubmodule)
      (restrictedTensorSquareEndomorphism * auxiliaryTensorSquareSubrepresentation.toRepresentation
      y)
        = LinearMap.trace ℂ (↥auxiliaryTensorSquareSubrepresentation.toSubmodule)
            (restrictedTensorSquareEndomorphism *
              auxiliaryTensorSquareSubrepresentation.toRepresentation (conjugacyClassRepresentative
              (conjugacyClassIndex y))) := by
      conv_lhs => rw [← hc]
      exact htr_conj c _
    rw [key, auxiliaryUnavailableStatementTwo, hvec]

  have hexpand : restrictedTensorSquareEndomorphism * restrictedTensorSquareEndomorphism *
    auxiliaryTensorSquareSubrepresentation.toRepresentation auxiliaryGroupElement
      = ∑ h : permutationSubgroupFin5, restrictedTensorSquareEndomorphism *
        auxiliaryTensorSquareSubrepresentation.toRepresentation
          (h * auxiliaryGroupElement * h⁻¹ * auxiliaryGroupElement) := by
    rw [show
      (restrictedTensorSquareEndomorphism * restrictedTensorSquareEndomorphism :
        Module.End ℂ ↥auxiliaryTensorSquareSubrepresentation.toSubmodule)
          = ∑ h : permutationSubgroupFin5, restrictedTensorSquareEndomorphism *
            auxiliaryTensorSquareSubrepresentation.toRepresentation (h * auxiliaryGroupElement *
            h⁻¹) by
        rw [← Finset.mul_sum]; rfl, Finset.sum_mul]
    refine Finset.sum_congr rfl fun h _ => ?_
    rw [mul_assoc, ← map_mul]
  have hr5 : LinearMap.trace ℂ (↥auxiliaryTensorSquareSubrepresentation.toSubmodule)
      (restrictedTensorSquareEndomorphism * restrictedTensorSquareEndomorphism *
        auxiliaryTensorSquareSubrepresentation.toRepresentation auxiliaryGroupElement) = 1600 := by
    have key :
        (∑ h : permutationSubgroupFin5,
          (![60, 0, -20, 60, -40] : Fin 5 → ℤ)
            (conjugacyClassIndex (h * auxiliaryGroupElement * h⁻¹ * auxiliaryGroupElement)))
          = 1600 := by decide
    rw [hexpand, map_sum,
      Finset.sum_congr rfl (fun h _ => htable (h * auxiliaryGroupElement * h⁻¹ *
        auxiliaryGroupElement)),
      ← Int.cast_sum, key]
    norm_num
  have hcard : (Fintype.card permutationSubgroupFin5 : ℂ) = 60 := by
    rw [← Nat.card_eq_fintype_card, card_permutationSubgroupFin5]; norm_num
  rw [hr5, hcard]; norm_num

/-- The displayed tensor-square subrepresentation has complex dimension six. -/
lemma finrank_auxiliaryTensorSubrepresentation : Module.finrank ℂ
  (↥auxiliaryTensorSquareSubrepresentation.toSubmodule) = 6 := by
  have h : (Module.finrank ℂ alternatingSquareRepresentation : ℂ) = 6 := by
    rw [← FDRep.char_one alternatingSquareRepresentation, show (1 : permutationSubgroupFin5) =
      conjugacyClassRepresentative 0 from rfl, auxiliaryUnavailableStatement]
    norm_num
  exact_mod_cast h

/-- The restricted tensor-square endomorphism is not a scalar multiple of the identity. -/
lemma restrictedTensorSquareEndomorphism_ne_smul_one (c : ℂ) :
    restrictedTensorSquareEndomorphism ≠ c • 1 := by
  intro hc
  have htr1 : LinearMap.trace ℂ (↥auxiliaryTensorSquareSubrepresentation.toSubmodule)
      (1 : Module.End ℂ ↥auxiliaryTensorSquareSubrepresentation.toSubmodule) = 6 := by
    rw [Module.End.one_eq_id, LinearMap.trace_id, finrank_auxiliaryTensorSubrepresentation];
      norm_num
  have h1 : c * 6 = 60 := by
    have h := trace_restrictedTensorSquareEndomorphism
    rwa [hc, map_smul, htr1, smul_eq_mul] at h
  have h2 : c * c * 6 = 3600 := by
    have h := trace_restrictedTensorSquareEndomorphism_sq
    rwa [hc, smul_mul_smul_comm, one_mul, map_smul, htr1, smul_eq_mul] at h
  have hc10 : c = 10 := by linear_combination h1 / 6
  rw [hc10] at h2; norm_num at h2

set_option maxRecDepth 4000 in
set_option maxHeartbeats 1600000 in

/-- The square of the restricted endomorphism satisfies a quadratic linear relation with it and the
identity. -/
lemma exists_quadratic_relation_restrictedTensorSquareEndomorphism : ∃ a b : ℂ,
  restrictedTensorSquareEndomorphism * restrictedTensorSquareEndomorphism = a •
  restrictedTensorSquareEndomorphism + b • 1 := by

  let zHom : alternatingSquareRepresentation ⟶ alternatingSquareRepresentation :=
    { hom := FGModuleCat.ofHom restrictedTensorSquareEndomorphism
      comm := fun g => by
        ext v
        exact congr_fun (congr_arg DFunLike.coe (restrictedTensorSquareEndomorphism_commutes
          g).symm) v }

  let Φ :
      (alternatingSquareRepresentation ⟶ alternatingSquareRepresentation) →ₗ[ℂ]
        Module.End ℂ (↥auxiliaryTensorSquareSubrepresentation.toSubmodule) :=
    { toFun := fun f => f.hom.hom.hom
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl }
  have hid : Φ (𝟙 alternatingSquareRepresentation) = 1 := rfl
  have hz : Φ zHom = restrictedTensorSquareEndomorphism := rfl
  have hzz : Φ (zHom ≫ zHom) = restrictedTensorSquareEndomorphism *
    restrictedTensorSquareEndomorphism := rfl

  have hone :
      (1 : Module.End ℂ (↥auxiliaryTensorSquareSubrepresentation.toSubmodule)) ≠ 0 := by
    intro h
    have htr : LinearMap.trace ℂ (↥auxiliaryTensorSquareSubrepresentation.toSubmodule)
        (1 : Module.End ℂ (↥auxiliaryTensorSquareSubrepresentation.toSubmodule)) = 6 := by
      rw [Module.End.one_eq_id, LinearMap.trace_id, finrank_auxiliaryTensorSubrepresentation];
        norm_num
    rw [h, map_zero] at htr; norm_num at htr

  have hdep : ¬ LinearIndependent ℂ
      (![𝟙 alternatingSquareRepresentation, zHom, zHom ≫ zHom] : Fin 3 →
        (alternatingSquareRepresentation ⟶ alternatingSquareRepresentation)) := by
    intro hli
    have h := hli.fintype_card_le_finrank
    rw [finrank_end_alternatingSquareRepresentation, Fintype.card_fin] at h; omega
  rw [Fintype.not_linearIndependent_iff] at hdep
  obtain ⟨c, hsum, i₀, hne⟩ := hdep

  have himg :
      c 0 • (1 : Module.End ℂ (↥auxiliaryTensorSquareSubrepresentation.toSubmodule)) +
        c 1 • restrictedTensorSquareEndomorphism
      + c 2 • (restrictedTensorSquareEndomorphism * restrictedTensorSquareEndomorphism) = 0 := by
    have hkey := congr_arg Φ hsum
    rw [map_zero, map_sum, Fin.sum_univ_three] at hkey
    simpa only [map_smul, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
      Matrix.cons_val_two, Matrix.tail_cons, hid, hz, hzz] using hkey

  have hc2 : c 2 ≠ 0 := by
    intro h2
    rw [h2, zero_smul, add_zero] at himg
    by_cases h1 : c 1 = 0
    · rw [h1, zero_smul, add_zero] at himg
      have hc0 : c 0 = 0 := (smul_eq_zero.mp himg).resolve_right hone
      apply hne
      have hi : (i₀ : ℕ) = 0 ∨ (i₀ : ℕ) = 1 ∨ (i₀ : ℕ) = 2 := by omega
      rcases hi with hi | hi | hi
      · have hi' : i₀ = 0 := Fin.ext_iff.mpr hi
        simpa [hi'] using hc0
      · have hi' : i₀ = 1 := Fin.ext_iff.mpr hi
        simpa [hi'] using h1
      · have hi' : i₀ = 2 := Fin.ext_iff.mpr hi
        simpa [hi'] using h2
    · refine restrictedTensorSquareEndomorphism_ne_smul_one (-((c 1)⁻¹ * c 0)) ?_

      have hscaled := congrArg (fun x => (c 1)⁻¹ • x) himg
      simp only [smul_add, smul_zero, smul_smul, inv_mul_cancel₀ h1, one_smul] at hscaled
      apply eq_of_sub_eq_zero
      rw [← hscaled]; module

  refine ⟨-((c 2)⁻¹ * c 1), -((c 2)⁻¹ * c 0), ?_⟩
  have hscaled := congrArg (fun x => (c 2)⁻¹ • x) himg
  simp only [smul_add, smul_zero, smul_smul, inv_mul_cancel₀ hc2, one_smul] at hscaled
  apply eq_of_sub_eq_zero
  rw [← hscaled]; module

/-- The sum of the two spectral values is twenty. -/
lemma secondSpectralValue_add_firstSpectralValue : secondSpectralValue + firstSpectralValue = 20 :=
  by
  simp only [secondSpectralValue, firstSpectralValue]; ring

/-- The square of the complex number obtained from the real square root of five is five. -/
lemma sq_complex_sqrt_five : (Real.sqrt 5 : ℂ) ^ 2 = 5 := by
  rw [← Complex.ofReal_pow, Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 5)]; norm_num

/-- An auxiliary statement whose formal type was unavailable. -/
lemma auxiliaryUnavailableStatementOne : secondSpectralValue * firstSpectralValue = -400 := by
  simp only [secondSpectralValue, firstSpectralValue]; ring_nf; rw [sq_complex_sqrt_five]; norm_num

/-- The difference of the spectral values is twenty times the complex square root of five. -/
lemma secondSpectralValue_sub_firstSpectralValue : secondSpectralValue - firstSpectralValue = 20 *
  (Real.sqrt 5 : ℂ) := by
  simp only [secondSpectralValue, firstSpectralValue]; ring

/-- Twenty times the complex square root of five is nonzero. -/
lemma twenty_mul_complex_sqrt_five_ne_zero : (20 * (Real.sqrt 5 : ℂ)) ≠ 0 :=
  mul_ne_zero (by norm_num) (by
    rw [Ne, Complex.ofReal_eq_zero]
    exact ne_of_gt (Real.sqrt_pos.mpr (by norm_num)))

/-- The square of the restricted endomorphism equals twenty times the endomorphism plus four hundred
times the identity. -/
lemma restrictedTensorSquareEndomorphism_sq : restrictedTensorSquareEndomorphism *
  restrictedTensorSquareEndomorphism =
    (20 : ℂ) • restrictedTensorSquareEndomorphism + (400 : ℂ) • 1 := by
  obtain ⟨a, b, hab⟩ := exists_quadratic_relation_restrictedTensorSquareEndomorphism
  have htr1 :
      LinearMap.trace ℂ (↥auxiliaryTensorSquareSubrepresentation.toSubmodule) 1 = 6 := by
    rw [Module.End.one_eq_id, LinearMap.trace_id, finrank_auxiliaryTensorSubrepresentation];
      norm_num

  have e1 : (3600 : ℂ) = a * 60 + b * 6 := by
    have h := congr_arg
      (LinearMap.trace ℂ (↥auxiliaryTensorSquareSubrepresentation.toSubmodule)) hab
    rwa [trace_restrictedTensorSquareEndomorphism_sq, map_add, map_smul, map_smul,
      trace_restrictedTensorSquareEndomorphism, htr1, smul_eq_mul,
      smul_eq_mul] at h

  have hcube : restrictedTensorSquareEndomorphism * restrictedTensorSquareEndomorphism *
    restrictedTensorSquareEndomorphism = a • (restrictedTensorSquareEndomorphism *
    restrictedTensorSquareEndomorphism) + b • restrictedTensorSquareEndomorphism := by
    conv_lhs => rw [hab]
    rw [add_mul, smul_mul_assoc, smul_mul_assoc, one_mul]
  have e2 : (96000 : ℂ) = a * 3600 + b * 60 := by
    have h := congr_arg
      (LinearMap.trace ℂ (↥auxiliaryTensorSquareSubrepresentation.toSubmodule)) hcube
    rwa [trace_restrictedTensorSquareEndomorphism_cube, map_add, map_smul, map_smul,
      trace_restrictedTensorSquareEndomorphism_sq, trace_restrictedTensorSquareEndomorphism,
      smul_eq_mul,
      smul_eq_mul] at h
  have ha : a = 20 := by linear_combination (1 / 300 : ℂ) * e1 + (-1 / 3000 : ℂ) * e2
  have hb : b = 400 := by linear_combination (-1 / 5 : ℂ) * e1 + (1 / 300 : ℂ) * e2
  rw [ha, hb] at hab
  exact hab

/-- A complex-linear projection associated with the spectral decomposition of the restricted
endomorphism. -/
noncomputable def spectralProjection : Module.End ℂ
  ↥auxiliaryTensorSquareSubrepresentation.toSubmodule :=
  (20 * (Real.sqrt 5 : ℂ))⁻¹ •
    (restrictedTensorSquareEndomorphism - firstSpectralValue • 1)

set_option maxHeartbeats 800000 in

/-- The spectral projection projects onto the eigenspace for the second spectral value. -/
lemma isProj_spectralProjection : LinearMap.IsProj (Module.End.eigenspace
  restrictedTensorSquareEndomorphism secondSpectralValue) spectralProjection := by

  have hkey : restrictedTensorSquareEndomorphism * restrictedTensorSquareEndomorphism =
    (secondSpectralValue + firstSpectralValue) • restrictedTensorSquareEndomorphism -
    (secondSpectralValue * firstSpectralValue) • 1 := by
    rw [restrictedTensorSquareEndomorphism_sq, secondSpectralValue_add_firstSpectralValue,
      auxiliaryUnavailableStatementOne]; module
  have hzP : restrictedTensorSquareEndomorphism * (restrictedTensorSquareEndomorphism -
    firstSpectralValue • 1) = secondSpectralValue • (restrictedTensorSquareEndomorphism -
    firstSpectralValue • 1) := by
    rw [mul_sub restrictedTensorSquareEndomorphism restrictedTensorSquareEndomorphism
      (firstSpectralValue • 1), mul_smul_comm, mul_one, hkey,
      smul_sub secondSpectralValue restrictedTensorSquareEndomorphism (firstSpectralValue • 1),
        smul_smul]
    module
  refine ⟨fun x => ?_, fun x hx => ?_⟩
  ·
    rw [Module.End.mem_eigenspace_iff]
    have hop : restrictedTensorSquareEndomorphism * spectralProjection = secondSpectralValue •
      spectralProjection := by
      rw [spectralProjection, mul_smul_comm, hzP, smul_comm]
    have h := congr_arg
      (fun f : Module.End ℂ (↥auxiliaryTensorSquareSubrepresentation.toSubmodule) => f x) hop
    simpa [Module.End.mul_apply] using h
  ·
    rw [Module.End.mem_eigenspace_iff] at hx
    rw [spectralProjection, LinearMap.smul_apply, LinearMap.sub_apply, LinearMap.smul_apply,
      Module.End.one_apply, hx, ← sub_smul, smul_smul, secondSpectralValue_sub_firstSpectralValue,
      inv_mul_cancel₀ twenty_mul_complex_sqrt_five_ne_zero, one_smul]

/-- The kernel of the spectral projection is the eigenspace for the first spectral value. -/
lemma ker_spectralProjection : LinearMap.ker spectralProjection = Module.End.eigenspace
  restrictedTensorSquareEndomorphism firstSpectralValue := by
  ext x
  rw [LinearMap.mem_ker, Module.End.mem_eigenspace_iff, spectralProjection, LinearMap.smul_apply,
    smul_eq_zero]
  constructor
  · rintro (h | h)
    · exact absurd h (inv_ne_zero twenty_mul_complex_sqrt_five_ne_zero)
    · rwa [LinearMap.sub_apply, LinearMap.smul_apply, Module.End.one_apply, sub_eq_zero] at h
  · intro h
    refine Or.inr ?_
    rw [LinearMap.sub_apply, LinearMap.smul_apply, Module.End.one_apply, sub_eq_zero]
    exact h

/-- The spectral projection has trace three. -/
lemma trace_spectralProjection : LinearMap.trace ℂ
  (↥auxiliaryTensorSquareSubrepresentation.toSubmodule) spectralProjection = 3 := by
  have htr1 :
      LinearMap.trace ℂ (↥auxiliaryTensorSquareSubrepresentation.toSubmodule) 1 = 6 := by
    rw [Module.End.one_eq_id, LinearMap.trace_id, finrank_auxiliaryTensorSubrepresentation];
      norm_num
  rw [spectralProjection,
    LinearMap.map_smul
      (LinearMap.trace ℂ (↥auxiliaryTensorSquareSubrepresentation.toSubmodule))
      (20 * (Real.sqrt 5 : ℂ))⁻¹
      (restrictedTensorSquareEndomorphism - firstSpectralValue • 1),
    LinearMap.map_sub (LinearMap.trace ℂ (↥auxiliaryTensorSquareSubrepresentation.toSubmodule))
      restrictedTensorSquareEndomorphism (firstSpectralValue • 1),
    LinearMap.map_smul (LinearMap.trace ℂ (↥auxiliaryTensorSquareSubrepresentation.toSubmodule))
      firstSpectralValue 1,
    trace_restrictedTensorSquareEndomorphism, htr1, smul_eq_mul, smul_eq_mul, firstSpectralValue,
    show
      (60 : ℂ) - (10 - 10 * (Real.sqrt 5 : ℂ)) * 6 =
        (20 * (Real.sqrt 5 : ℂ)) * 3 from by ring,
    ← mul_assoc, inv_mul_cancel₀ twenty_mul_complex_sqrt_five_ne_zero, one_mul]

set_option synthInstance.maxHeartbeats 400000 in

/-- The eigenspace for the second spectral value has complex dimension three. -/
lemma finrank_eigenspace_secondSpectralValue :
    Module.finrank ℂ
      (Module.End.eigenspace restrictedTensorSquareEndomorphism secondSpectralValue) = 3 := by
  haveI : FiniteDimensional ℂ (↥auxiliaryTensorSquareSubrepresentation.toSubmodule) :=
    FiniteDimensional.of_finrank_pos (by rw [finrank_auxiliaryTensorSubrepresentation]; norm_num)
  haveI : Module.Free ℂ (↥(Module.End.eigenspace restrictedTensorSquareEndomorphism
    secondSpectralValue)) :=
    Module.Free.of_divisionRing ℂ (↥(Module.End.eigenspace restrictedTensorSquareEndomorphism
      secondSpectralValue))
  haveI : Module.Free ℂ (↥(LinearMap.ker spectralProjection)) :=
    Module.Free.of_divisionRing ℂ (↥(LinearMap.ker spectralProjection))
  have h := isProj_spectralProjection.trace
  rw [trace_spectralProjection] at h
  exact_mod_cast h.symm

/-- The eigenspaces for the two displayed spectral values are complementary. -/
lemma spectralEigenspaces_isCompl :
    IsCompl (Module.End.eigenspace restrictedTensorSquareEndomorphism secondSpectralValue)
      (Module.End.eigenspace restrictedTensorSquareEndomorphism firstSpectralValue) := by
  have h := isProj_spectralProjection.isCompl
  rwa [ker_spectralProjection] at h

/-- The eigenspace for the first spectral value has complex dimension three. -/
lemma finrank_eigenspace_firstSpectralValue :
    Module.finrank ℂ
      (Module.End.eigenspace restrictedTensorSquareEndomorphism firstSpectralValue) = 3 := by
  haveI : FiniteDimensional ℂ (↥auxiliaryTensorSquareSubrepresentation.toSubmodule) :=
    FiniteDimensional.of_finrank_pos (by rw [finrank_auxiliaryTensorSubrepresentation]; norm_num)
  have hsum := Submodule.finrank_add_eq_of_isCompl spectralEigenspaces_isCompl
  rw [finrank_eigenspace_secondSpectralValue, finrank_auxiliaryTensorSubrepresentation] at hsum
  omega

/-- The second spectral subrepresentation has complex dimension three. -/
lemma finrank_secondSpectralSubrepresentation : Module.finrank ℂ
  secondSpectralSubrepresentation.toSubmodule = 3 := by
  rw [finrank_secondSpectralSubrepresentation_eq, finrank_eigenspace_secondSpectralValue]

/-- The first spectral subrepresentation has complex dimension three. -/
lemma finrank_firstSpectralSubrepresentation : Module.finrank ℂ
  firstSpectralSubrepresentation.toSubmodule = 3 := by
  rw [finrank_firstSpectralSubrepresentation_eq, finrank_eigenspace_firstSpectralValue]

/-- The displayed complex-valued map preserves addition. -/
lemma complexValueMap_add (a b : RepresentationTheory.QuaternionGroupTwo.AuxiliaryType) :
    auxiliaryTypeToComplex (a + b) = auxiliaryTypeToComplex a + auxiliaryTypeToComplex b := by
  simp only [auxiliaryTypeToComplex,
    RepresentationTheory.QuaternionGroupTwo.AuxiliaryType.add_re,
    RepresentationTheory.QuaternionGroupTwo.AuxiliaryType.add_im]; push_cast; ring

/-- The character of the displayed representation is the sum of two displayed table entries at each
index. -/
lemma character_auxiliaryRepresentation_eq_tableRowSum (j : Fin 5) :
    alternatingSquareRepresentation.character (conjugacyClassRepresentative j) =
      auxiliaryTypeToComplex (indexedTable 1 j) + auxiliaryTypeToComplex (indexedTable 2 j) := by
  rw [auxiliaryUnavailableStatement, ← complexValueMap_add, auxiliaryTypeToComplex]
  fin_cases j <;>
    simp only [indexedTable, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
      Matrix.head_cons, Matrix.tail_cons] <;>
    norm_num [RepresentationTheory.QuaternionGroupTwo.AuxiliaryType.add_re,
      RepresentationTheory.QuaternionGroupTwo.AuxiliaryType.add_im,
      RepresentationTheory.QuaternionGroupTwo.AuxiliaryType.mk_re,
      RepresentationTheory.QuaternionGroupTwo.AuxiliaryType.mk_im,
      RepresentationTheory.QuaternionGroupTwo.AuxiliaryType.ofNat_re,
      RepresentationTheory.QuaternionGroupTwo.AuxiliaryType.ofNat_im,
      RepresentationTheory.QuaternionGroupTwo.AuxiliaryType.neg_re,
      RepresentationTheory.QuaternionGroupTwo.AuxiliaryType.neg_im,
      RepresentationTheory.QuaternionGroupTwo.AuxiliaryType.one_re,
      RepresentationTheory.QuaternionGroupTwo.AuxiliaryType.one_im,
      RepresentationTheory.QuaternionGroupTwo.AuxiliaryType.zero_re,
      RepresentationTheory.QuaternionGroupTwo.AuxiliaryType.zero_im]

set_option synthInstance.maxHeartbeats 400000 in
set_option maxHeartbeats 800000 in

private lemma character_eq_restrict_trace
    (S : Subrepresentation (coordinateRepresentation.tprod coordinateRepresentation))
    (E : Submodule ℂ (↥auxiliaryTensorSquareSubrepresentation.toSubmodule))
    (hSE : S.toSubmodule = E.map auxiliaryTensorSquareSubrepresentation.toSubmodule.subtype)
    (g : permutationSubgroupFin5)
    (hmaps : Set.MapsTo (auxiliaryTensorSquareSubrepresentation.toRepresentation g) E E) :
    (FDRep.of S.toRepresentation).character g
      = LinearMap.trace ℂ ↥E
        ((auxiliaryTensorSquareSubrepresentation.toRepresentation g).restrict hmaps) := by

  letI : AddCommGroup (↥E) := E.addCommGroup

  have hmapsInto : ∀ x : ↥E,
      auxiliaryTensorSquareSubrepresentation.toSubmodule.subtype (E.subtype x) ∈
        S.toSubmodule := by
    intro x; rw [hSE]; exact Submodule.mem_map_of_mem x.2
  set g0 : ↥E →ₗ[ℂ] ↥S.toSubmodule :=
    (auxiliaryTensorSquareSubrepresentation.toSubmodule.subtype ∘ₗ E.subtype).codRestrict
      S.toSubmodule hmapsInto with hg0
  have hg0_inj : Function.Injective g0 := by
    intro a b hab
    have h :
        (E.subtype a : ↥auxiliaryTensorSquareSubrepresentation.toSubmodule) = E.subtype b := by
      apply auxiliaryTensorSquareSubrepresentation.toSubmodule.injective_subtype
      simpa [hg0, LinearMap.codRestrict_apply, LinearMap.comp_apply] using Subtype.ext_iff.mp hab
    exact E.injective_subtype h
  have hg0_surj : Function.Surjective g0 := by
    intro z
    obtain ⟨w, hw, hwz⟩ := Submodule.mem_map.mp
      (show (z : auxiliaryCoordinateSubmodule ⊗[ℂ] auxiliaryCoordinateSubmodule) ∈ E.map
        auxiliaryTensorSquareSubrepresentation.toSubmodule.subtype by rw [← hSE]; exact z.2)
    exact ⟨⟨w, hw⟩, Subtype.ext hwz⟩
  set e : ↥E ≃ₗ[ℂ] ↥S.toSubmodule :=
    LinearEquiv.ofBijective g0 ⟨hg0_inj, hg0_surj⟩ with he
  have hecoe : ∀ w : ↥E, ((e w : ↥S.toSubmodule) : auxiliaryCoordinateSubmodule ⊗[ℂ]
    auxiliaryCoordinateSubmodule)
      = ((w : ↥auxiliaryTensorSquareSubrepresentation.toSubmodule) : auxiliaryCoordinateSubmodule
        ⊗[ℂ] auxiliaryCoordinateSubmodule) := by
    intro w
    simp only [he, LinearEquiv.ofBijective_apply, hg0, LinearMap.codRestrict_apply,
      LinearMap.comp_apply, Submodule.coe_subtype]

  have hconj : S.toRepresentation g
      = e.conj ((auxiliaryTensorSquareSubrepresentation.toRepresentation g).restrict hmaps) := by
    refine LinearMap.ext fun y => Subtype.ext ?_
    rw [LinearEquiv.conj_apply_apply]
    have hLHS : ((S.toRepresentation g y : ↥S.toSubmodule) : auxiliaryCoordinateSubmodule ⊗[ℂ]
      auxiliaryCoordinateSubmodule)
        = (coordinateRepresentation.tprod coordinateRepresentation) g (y :
          auxiliaryCoordinateSubmodule ⊗[ℂ] auxiliaryCoordinateSubmodule) := rfl
    have hRHS : ((e ((auxiliaryTensorSquareSubrepresentation.toRepresentation g).restrict hmaps
      (e.symm y)) : ↥S.toSubmodule)
          : auxiliaryCoordinateSubmodule ⊗[ℂ] auxiliaryCoordinateSubmodule)
        = (coordinateRepresentation.tprod coordinateRepresentation) g (y :
          auxiliaryCoordinateSubmodule ⊗[ℂ] auxiliaryCoordinateSubmodule) := by
      rw [hecoe]
      have hcoe : (((auxiliaryTensorSquareSubrepresentation.toRepresentation g).restrict hmaps
        (e.symm y) : ↥E)
            : ↥auxiliaryTensorSquareSubrepresentation.toSubmodule)
          = auxiliaryTensorSquareSubrepresentation.toRepresentation g ((e.symm y : ↥E) :
            ↥auxiliaryTensorSquareSubrepresentation.toSubmodule) :=
        LinearMap.coe_restrict_apply hmaps (e.symm y)
      rw [hcoe]
      have hcoe2 : ((auxiliaryTensorSquareSubrepresentation.toRepresentation g ((e.symm y : ↥E) :
        ↥auxiliaryTensorSquareSubrepresentation.toSubmodule)
            : ↥auxiliaryTensorSquareSubrepresentation.toSubmodule) : auxiliaryCoordinateSubmodule
              ⊗[ℂ] auxiliaryCoordinateSubmodule)
          = (coordinateRepresentation.tprod coordinateRepresentation) g (((e.symm y : ↥E) :
            ↥auxiliaryTensorSquareSubrepresentation.toSubmodule) :
              auxiliaryCoordinateSubmodule ⊗[ℂ] auxiliaryCoordinateSubmodule) := rfl
      rw [hcoe2]
      congr 1
      have hsy := hecoe (e.symm y)
      rw [LinearEquiv.apply_symm_apply] at hsy
      exact hsy.symm
    rw [hLHS, hRHS]

  change LinearMap.trace ℂ ↥S.toSubmodule (S.toRepresentation g)
      = LinearMap.trace ℂ ↥E
        ((auxiliaryTensorSquareSubrepresentation.toRepresentation g).restrict hmaps)
  rw [hconj]
  exact LinearMap.trace_conj' _ e

private lemma mapsTo_eigenspace_muPlus (g : permutationSubgroupFin5) :
    Set.MapsTo (auxiliaryTensorSquareSubrepresentation.toRepresentation g)
      (Module.End.eigenspace restrictedTensorSquareEndomorphism secondSpectralValue : Set _)
        (Module.End.eigenspace restrictedTensorSquareEndomorphism secondSpectralValue : Set _) :=
  Module.End.mapsTo_genEigenspace_of_comm (restrictedTensorSquareEndomorphism_commutes g).symm
    secondSpectralValue 1

private lemma mapsTo_eigenspace_muMinus (g : permutationSubgroupFin5) :
    Set.MapsTo (auxiliaryTensorSquareSubrepresentation.toRepresentation g)
      (Module.End.eigenspace restrictedTensorSquareEndomorphism firstSpectralValue : Set _)
        (Module.End.eigenspace restrictedTensorSquareEndomorphism firstSpectralValue : Set _) :=
  Module.End.mapsTo_genEigenspace_of_comm (restrictedTensorSquareEndomorphism_commutes g).symm
    firstSpectralValue 1

private lemma repC3plus_character_eq_trace (g : permutationSubgroupFin5) :
    auxiliaryRepresentationTwo.character g
      = LinearMap.trace ℂ ↥(Module.End.eigenspace restrictedTensorSquareEndomorphism
        secondSpectralValue)
          ((auxiliaryTensorSquareSubrepresentation.toRepresentation g).restrict
            (mapsTo_eigenspace_muPlus g)) :=
  character_eq_restrict_trace secondSpectralSubrepresentation _
    secondSpectralSubrepresentation_toSubmodule g
    (mapsTo_eigenspace_muPlus g)

private lemma repC3minus_character_eq_trace (g : permutationSubgroupFin5) :
    auxiliaryRepresentationOne.character g
      = LinearMap.trace ℂ ↥(Module.End.eigenspace restrictedTensorSquareEndomorphism
        firstSpectralValue)
          ((auxiliaryTensorSquareSubrepresentation.toRepresentation g).restrict
            (mapsTo_eigenspace_muMinus g)) :=
  character_eq_restrict_trace firstSpectralSubrepresentation _
    firstSpectralSubrepresentation_toSubmodule g
    (mapsTo_eigenspace_muMinus g)

set_option synthInstance.maxHeartbeats 400000 in
set_option maxRecDepth 4000 in
set_option maxHeartbeats 800000 in

private lemma repC3_character_system (g : permutationSubgroupFin5) :
    auxiliaryRepresentationTwo.character g + auxiliaryRepresentationOne.character g =
      alternatingSquareRepresentation.character g
      ∧ secondSpectralValue * auxiliaryRepresentationTwo.character g + firstSpectralValue *
        auxiliaryRepresentationOne.character g
          = LinearMap.trace ℂ ↥auxiliaryTensorSquareSubrepresentation.toSubmodule
            (restrictedTensorSquareEndomorphism *
            auxiliaryTensorSquareSubrepresentation.toRepresentation g) := by
  classical
  haveI : FiniteDimensional ℂ (↥auxiliaryTensorSquareSubrepresentation.toSubmodule) :=
    FiniteDimensional.of_finrank_pos (by rw [finrank_auxiliaryTensorSubrepresentation]; norm_num)
  set N : Fin 2 → Submodule ℂ (↥auxiliaryTensorSquareSubrepresentation.toSubmodule)
    := ![Module.End.eigenspace restrictedTensorSquareEndomorphism secondSpectralValue,
      Module.End.eigenspace restrictedTensorSquareEndomorphism firstSpectralValue] with hN
  have huniv : (Set.univ : Set (Fin 2)) = {0, 1} := by
    ext i; simp only [Set.mem_univ, Set.mem_insert_iff, Set.mem_singleton_iff, true_iff]; omega
  have hInternal : DirectSum.IsInternal N :=
    (DirectSum.isInternal_submodule_iff_isCompl N zero_ne_one huniv).mpr spectralEigenspaces_isCompl
  haveI : ∀ i, Module.Finite ℂ ↥(N i) := fun i => inferInstance
  haveI : ∀ i, Module.Free ℂ ↥(N i) := fun i => Module.Free.of_divisionRing ℂ (↥(N i))

  have hf : ∀ i, Set.MapsTo (auxiliaryTensorSquareSubrepresentation.toRepresentation g) (↑(N i))
    (↑(N i)) :=
    Fin.forall_fin_two.mpr ⟨mapsTo_eigenspace_muPlus g, mapsTo_eigenspace_muMinus g⟩

  have hMmaps : ∀ i, Set.MapsTo (restrictedTensorSquareEndomorphism *
    auxiliaryTensorSquareSubrepresentation.toRepresentation g) (↑(N i)) (↑(N i)) :=
    Fin.forall_fin_two.mpr
      ⟨fun x hx => Module.End.mapsTo_genEigenspace_of_comm (Commute.refl
        restrictedTensorSquareEndomorphism) secondSpectralValue 1
          (mapsTo_eigenspace_muPlus g hx),
       fun x hx => Module.End.mapsTo_genEigenspace_of_comm (Commute.refl
         restrictedTensorSquareEndomorphism) firstSpectralValue 1
          (mapsTo_eigenspace_muMinus g hx)⟩

  have hM0 : (restrictedTensorSquareEndomorphism *
    auxiliaryTensorSquareSubrepresentation.toRepresentation g).restrict (hMmaps 0)
      = secondSpectralValue • (auxiliaryTensorSquareSubrepresentation.toRepresentation g).restrict
        (hf 0) := by
    refine LinearMap.ext fun x => Subtype.ext ?_
    have hmem : auxiliaryTensorSquareSubrepresentation.toRepresentation g (x :
      ↥auxiliaryTensorSquareSubrepresentation.toSubmodule)
        ∈ Module.End.eigenspace restrictedTensorSquareEndomorphism secondSpectralValue := hf 0 x.2
    change restrictedTensorSquareEndomorphism
      (auxiliaryTensorSquareSubrepresentation.toRepresentation g (x :
      ↥auxiliaryTensorSquareSubrepresentation.toSubmodule))
        = secondSpectralValue • auxiliaryTensorSquareSubrepresentation.toRepresentation g (x :
          ↥auxiliaryTensorSquareSubrepresentation.toSubmodule)
    exact Module.End.mem_eigenspace_iff.mp hmem
  have hM1 : (restrictedTensorSquareEndomorphism *
    auxiliaryTensorSquareSubrepresentation.toRepresentation g).restrict (hMmaps 1)
      = firstSpectralValue • (auxiliaryTensorSquareSubrepresentation.toRepresentation g).restrict
        (hf 1) := by
    refine LinearMap.ext fun x => Subtype.ext ?_
    have hmem : auxiliaryTensorSquareSubrepresentation.toRepresentation g (x :
      ↥auxiliaryTensorSquareSubrepresentation.toSubmodule)
        ∈ Module.End.eigenspace restrictedTensorSquareEndomorphism firstSpectralValue := hf 1 x.2
    change restrictedTensorSquareEndomorphism
      (auxiliaryTensorSquareSubrepresentation.toRepresentation g (x :
      ↥auxiliaryTensorSquareSubrepresentation.toSubmodule))
        = firstSpectralValue • auxiliaryTensorSquareSubrepresentation.toRepresentation g (x :
          ↥auxiliaryTensorSquareSubrepresentation.toSubmodule)
    exact Module.End.mem_eigenspace_iff.mp hmem
  refine ⟨?_, ?_⟩
  · have key := LinearMap.trace_eq_sum_trace_restrict hInternal hf
    rw [Fin.sum_univ_two] at key
    rw [repC3plus_character_eq_trace, repC3minus_character_eq_trace]
    exact key.symm
  · have keyM := LinearMap.trace_eq_sum_trace_restrict hInternal hMmaps
    rw [Fin.sum_univ_two, hM0, hM1, map_smul, map_smul, smul_eq_mul, smul_eq_mul] at keyM
    rw [repC3plus_character_eq_trace, repC3minus_character_eq_trace]
    exact keyM.symm

/-- The second auxiliary representation has the displayed character-table row. -/
lemma character_auxiliaryRepresentationTwo (j : Fin 5) :
    auxiliaryRepresentationTwo.character (conjugacyClassRepresentative j) = auxiliaryTypeToComplex
      (indexedTable 1 j) := by
  obtain ⟨e1, e2⟩ := repC3_character_system (conjugacyClassRepresentative j)
  rw [auxiliaryUnavailableStatement] at e1
  rw [auxiliaryUnavailableStatementTwo] at e2
  have hne : secondSpectralValue - firstSpectralValue ≠ 0 := by
    rw [secondSpectralValue_sub_firstSpectralValue]
    exact twenty_mul_complex_sqrt_five_ne_zero
  refine mul_left_cancel₀ hne ?_
  rw [show (secondSpectralValue - firstSpectralValue) * auxiliaryRepresentationTwo.character
    (conjugacyClassRepresentative j)
      = (![60, 0, -20, 60, -40] j : ℂ) - firstSpectralValue * (![6, 0, -2, 1, 1] j : ℂ) from by
    linear_combination e2 - firstSpectralValue * e1]
  have hs := sq_complex_sqrt_five
  fin_cases j <;>
    norm_num [auxiliaryTypeToComplex, secondSpectralValue, firstSpectralValue, indexedTable,
      Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.cons_val_two, Matrix.cons_val_three, Matrix.cons_val_four, Matrix.head_cons,
      Matrix.tail_cons, RepresentationTheory.QuaternionGroupTwo.AuxiliaryType.mk_re,
      RepresentationTheory.QuaternionGroupTwo.AuxiliaryType.mk_im,
      RepresentationTheory.QuaternionGroupTwo.AuxiliaryType.ofNat_re,
      RepresentationTheory.QuaternionGroupTwo.AuxiliaryType.ofNat_im,
      RepresentationTheory.QuaternionGroupTwo.AuxiliaryType.neg_re,
      RepresentationTheory.QuaternionGroupTwo.AuxiliaryType.neg_im,
      RepresentationTheory.QuaternionGroupTwo.AuxiliaryType.one_re,
      RepresentationTheory.QuaternionGroupTwo.AuxiliaryType.one_im,
      RepresentationTheory.QuaternionGroupTwo.AuxiliaryType.zero_re,
      RepresentationTheory.QuaternionGroupTwo.AuxiliaryType.zero_im]

  · ring
  · ring
  · linear_combination (-10 : ℂ) * hs
  · linear_combination (10 : ℂ) * hs

/-- The first auxiliary representation has the displayed character-table row. -/
lemma character_auxiliaryRepresentationOne (j : Fin 5) :
    auxiliaryRepresentationOne.character (conjugacyClassRepresentative j) = auxiliaryTypeToComplex
      (indexedTable 2 j) := by
  obtain ⟨e1, e2⟩ := repC3_character_system (conjugacyClassRepresentative j)
  rw [auxiliaryUnavailableStatement] at e1
  rw [auxiliaryUnavailableStatementTwo] at e2
  have hne : secondSpectralValue - firstSpectralValue ≠ 0 := by
    rw [secondSpectralValue_sub_firstSpectralValue]
    exact twenty_mul_complex_sqrt_five_ne_zero
  refine mul_left_cancel₀ hne ?_
  rw [show (secondSpectralValue - firstSpectralValue) * auxiliaryRepresentationOne.character
    (conjugacyClassRepresentative j)
      = secondSpectralValue * (![6, 0, -2, 1, 1] j : ℂ) - (![60, 0, -20, 60, -40] j : ℂ) from by
    linear_combination secondSpectralValue * e1 - e2]
  have hs := sq_complex_sqrt_five
  fin_cases j <;>
    norm_num [auxiliaryTypeToComplex, secondSpectralValue, firstSpectralValue, indexedTable,
      Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.cons_val_two, Matrix.cons_val_three, Matrix.cons_val_four, Matrix.head_cons,
      Matrix.tail_cons, RepresentationTheory.QuaternionGroupTwo.AuxiliaryType.mk_re,
      RepresentationTheory.QuaternionGroupTwo.AuxiliaryType.mk_im,
      RepresentationTheory.QuaternionGroupTwo.AuxiliaryType.ofNat_re,
      RepresentationTheory.QuaternionGroupTwo.AuxiliaryType.ofNat_im,
      RepresentationTheory.QuaternionGroupTwo.AuxiliaryType.neg_re,
      RepresentationTheory.QuaternionGroupTwo.AuxiliaryType.neg_im,
      RepresentationTheory.QuaternionGroupTwo.AuxiliaryType.one_re,
      RepresentationTheory.QuaternionGroupTwo.AuxiliaryType.one_im,
      RepresentationTheory.QuaternionGroupTwo.AuxiliaryType.zero_re,
      RepresentationTheory.QuaternionGroupTwo.AuxiliaryType.zero_im]
  · ring
  · ring
  · linear_combination (10 : ℂ) * hs
  · linear_combination (-10 : ℂ) * hs

set_option maxHeartbeats 1000000 in

/-- The second auxiliary representation is simple. -/
lemma simple_auxiliaryRepresentationTwo : Simple auxiliaryRepresentationTwo := by
  rw [FDRep.simple_iff_char_is_norm_one, card_permutationSubgroupFin5]
  have hterm : ∀ g : permutationSubgroupFin5, auxiliaryRepresentationTwo.character g *
    auxiliaryRepresentationTwo.character g⁻¹
      = auxiliaryRepresentationTwo.character (conjugacyClassRepresentative (conjugacyClassIndex g))
        ^ 2 := by
    have hclass : ∀ a b : permutationSubgroupFin5, (∃ c, c * a * c⁻¹ = b) →
        auxiliaryRepresentationTwo.character b = auxiliaryRepresentationTwo.character a := by
      rintro a b ⟨c, rfl⟩; rw [FDRep.char_conj]
    intro g
    obtain ⟨c, hc⟩ := exists_conj_classRepresentative g
    obtain ⟨d, hd⟩ := classRepresentative_isConj_inv (conjugacyClassIndex g)
    have h1 : auxiliaryRepresentationTwo.character g = auxiliaryRepresentationTwo.character
      (conjugacyClassRepresentative (conjugacyClassIndex g)) :=
      hclass _ _ ⟨c, hc⟩
    have hAinv : auxiliaryRepresentationTwo.character (conjugacyClassRepresentative
      (conjugacyClassIndex g))⁻¹
        = auxiliaryRepresentationTwo.character (conjugacyClassRepresentative (conjugacyClassIndex
          g)) :=
      hclass _ _ ⟨d, hd⟩
    have hginv : auxiliaryRepresentationTwo.character g⁻¹
        = auxiliaryRepresentationTwo.character (conjugacyClassRepresentative (conjugacyClassIndex
          g))⁻¹ := by
      refine hclass _ _ ⟨c, ?_⟩
      conv_rhs => rw [← hc]
      group
    rw [h1, hginv, hAinv]; ring
  rw [Finset.sum_congr rfl (fun g _ => hterm g)]
  rw [show (∑ g : permutationSubgroupFin5, auxiliaryRepresentationTwo.character
    (conjugacyClassRepresentative (conjugacyClassIndex g)) ^ 2)
        = ∑ j : Fin 5, ∑ _g ∈ Finset.univ.filter (fun g => conjugacyClassIndex g = j),
            auxiliaryRepresentationTwo.character (conjugacyClassRepresentative j) ^ 2
      from (Finset.sum_fiberwise' Finset.univ conjugacyClassIndex
        (fun j => auxiliaryRepresentationTwo.character (conjugacyClassRepresentative j) ^ 2)).symm]
  simp only [Finset.sum_const, card_fiber_conjugacyClassIndex, nsmul_eq_mul]
  rw [Fin.sum_univ_five, character_auxiliaryRepresentationTwo 0,
    character_auxiliaryRepresentationTwo 1, character_auxiliaryRepresentationTwo 2,
    character_auxiliaryRepresentationTwo 3, character_auxiliaryRepresentationTwo 4]
  have hs := sq_complex_sqrt_five
  norm_num [auxiliaryTypeToComplex, indexedTable, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.cons_val_two,
    Matrix.cons_val_three, Matrix.cons_val_four, Matrix.head_cons, Matrix.tail_cons,
    RepresentationTheory.QuaternionGroupTwo.AuxiliaryType.mk_re,
    RepresentationTheory.QuaternionGroupTwo.AuxiliaryType.mk_im,
    RepresentationTheory.QuaternionGroupTwo.AuxiliaryType.ofNat_re,
    RepresentationTheory.QuaternionGroupTwo.AuxiliaryType.ofNat_im,
    RepresentationTheory.QuaternionGroupTwo.AuxiliaryType.neg_re,
    RepresentationTheory.QuaternionGroupTwo.AuxiliaryType.neg_im,
    RepresentationTheory.QuaternionGroupTwo.AuxiliaryType.one_re,
    RepresentationTheory.QuaternionGroupTwo.AuxiliaryType.one_im,
    RepresentationTheory.QuaternionGroupTwo.AuxiliaryType.zero_re,
    RepresentationTheory.QuaternionGroupTwo.AuxiliaryType.zero_im]
  linear_combination (6 : ℂ) * hs

set_option maxHeartbeats 1000000 in

/-- The first auxiliary representation is simple. -/
lemma simple_auxiliaryRepresentationOne : Simple auxiliaryRepresentationOne := by
  rw [FDRep.simple_iff_char_is_norm_one, card_permutationSubgroupFin5]
  have hterm : ∀ g : permutationSubgroupFin5, auxiliaryRepresentationOne.character g *
    auxiliaryRepresentationOne.character g⁻¹
      = auxiliaryRepresentationOne.character (conjugacyClassRepresentative (conjugacyClassIndex g))
        ^ 2 := by
    have hclass : ∀ a b : permutationSubgroupFin5, (∃ c, c * a * c⁻¹ = b) →
        auxiliaryRepresentationOne.character b = auxiliaryRepresentationOne.character a := by
      rintro a b ⟨c, rfl⟩; rw [FDRep.char_conj]
    intro g
    obtain ⟨c, hc⟩ := exists_conj_classRepresentative g
    obtain ⟨d, hd⟩ := classRepresentative_isConj_inv (conjugacyClassIndex g)
    have h1 : auxiliaryRepresentationOne.character g = auxiliaryRepresentationOne.character
      (conjugacyClassRepresentative (conjugacyClassIndex g)) :=
      hclass _ _ ⟨c, hc⟩
    have hAinv : auxiliaryRepresentationOne.character (conjugacyClassRepresentative
      (conjugacyClassIndex g))⁻¹
        = auxiliaryRepresentationOne.character (conjugacyClassRepresentative (conjugacyClassIndex
          g)) :=
      hclass _ _ ⟨d, hd⟩
    have hginv : auxiliaryRepresentationOne.character g⁻¹
        = auxiliaryRepresentationOne.character (conjugacyClassRepresentative (conjugacyClassIndex
          g))⁻¹ := by
      refine hclass _ _ ⟨c, ?_⟩
      conv_rhs => rw [← hc]
      group
    rw [h1, hginv, hAinv]; ring
  rw [Finset.sum_congr rfl (fun g _ => hterm g)]
  rw [show (∑ g : permutationSubgroupFin5, auxiliaryRepresentationOne.character
    (conjugacyClassRepresentative (conjugacyClassIndex g)) ^ 2)
        = ∑ j : Fin 5, ∑ _g ∈ Finset.univ.filter (fun g => conjugacyClassIndex g = j),
            auxiliaryRepresentationOne.character (conjugacyClassRepresentative j) ^ 2
      from (Finset.sum_fiberwise' Finset.univ conjugacyClassIndex
        (fun j => auxiliaryRepresentationOne.character (conjugacyClassRepresentative j) ^ 2)).symm]
  simp only [Finset.sum_const, card_fiber_conjugacyClassIndex, nsmul_eq_mul]
  rw [Fin.sum_univ_five, character_auxiliaryRepresentationOne 0,
    character_auxiliaryRepresentationOne 1, character_auxiliaryRepresentationOne 2,
    character_auxiliaryRepresentationOne 3, character_auxiliaryRepresentationOne 4]
  have hs := sq_complex_sqrt_five
  norm_num [auxiliaryTypeToComplex, indexedTable, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.cons_val_two,
    Matrix.cons_val_three, Matrix.cons_val_four, Matrix.head_cons, Matrix.tail_cons,
    RepresentationTheory.QuaternionGroupTwo.AuxiliaryType.mk_re,
    RepresentationTheory.QuaternionGroupTwo.AuxiliaryType.mk_im,
    RepresentationTheory.QuaternionGroupTwo.AuxiliaryType.ofNat_re,
    RepresentationTheory.QuaternionGroupTwo.AuxiliaryType.ofNat_im,
    RepresentationTheory.QuaternionGroupTwo.AuxiliaryType.neg_re,
    RepresentationTheory.QuaternionGroupTwo.AuxiliaryType.neg_im,
    RepresentationTheory.QuaternionGroupTwo.AuxiliaryType.one_re,
    RepresentationTheory.QuaternionGroupTwo.AuxiliaryType.one_im,
    RepresentationTheory.QuaternionGroupTwo.AuxiliaryType.zero_re,
    RepresentationTheory.QuaternionGroupTwo.AuxiliaryType.zero_im]
  linear_combination (6 : ℂ) * hs

/-- A family of five finite-dimensional complex representations. -/
def indexedSimpleRepresentations : Fin 5 → FDRep ℂ permutationSubgroupFin5 :=
  ![RepresentationTheory.IndexedPermutationFinsetAction.trivialRepresentation,
  auxiliaryRepresentationTwo, auxiliaryRepresentationOne,
  RepresentationTheory.IndexedPermutationFinsetAction.auxiliaryRepresentationOne,
  RepresentationTheory.IndexedPermutationFinsetAction.auxiliaryRepresentationTwo]

/-- The index map selecting the character-table row of each indexed representation. -/
def representationCharacterRowIndex : Fin 5 → Fin 5 := id

/-- Every representation in the indexed family is simple. -/
@[source_ref "Chapter4/Example4.8.1" (role := primary)]
lemma simple_indexedSimpleRepresentations (i : Fin 5) : Simple (indexedSimpleRepresentations i) :=
  by
  fin_cases i
  · exact RepresentationTheory.IndexedPermutationFinsetAction.simple_trivialRepresentation
  · exact simple_auxiliaryRepresentationTwo
  · exact simple_auxiliaryRepresentationOne
  · exact RepresentationTheory.IndexedPermutationFinsetAction.simple_auxiliaryRepresentationOne
  · exact RepresentationTheory.IndexedPermutationFinsetAction.simple_auxiliaryRepresentationTwo

/-- The character of each indexed representation at each indexed group element is the corresponding
complex table entry. -/
@[source_ref "Chapter4/Example4.8.1" (role := primary)]
lemma character_indexedSimpleRepresentations (i j : Fin 5) :
    (indexedSimpleRepresentations i).character (conjugacyClassRepresentative j) =
      auxiliaryTypeToComplex (indexedTable (representationCharacterRowIndex i) j) := by
  simp only [representationCharacterRowIndex, id_eq]
  fin_cases i
  · exact (character_auxiliaryRepresentation_row_zero j).trans
      (complexTable_selectedRows_eq_intCast 0 j).symm
  · exact character_auxiliaryRepresentationTwo j
  · exact character_auxiliaryRepresentationOne j
  · exact (character_auxiliaryRepresentation_row_one j).trans (complexTable_selectedRows_eq_intCast
    1 j).symm
  · exact (character_auxiliaryRepresentation_row_two j).trans (complexTable_selectedRows_eq_intCast
    2 j).symm

/-- The five indexed representations have dimensions one, three, three, four, and five. -/
lemma finrank_indexedSimpleRepresentations (i : Fin 5) :
    Module.finrank ℂ (indexedSimpleRepresentations i) = ![1, 3, 3, 4, 5] i := by
  have him : ∀ j : Fin 5, (indexedTable j 0).im = 0 := by decide
  have hre : ∀ j : Fin 5, (indexedTable j 0).re = ((![1, 3, 3, 4, 5] j : ℕ) : ℚ) := by decide
  have key : (Module.finrank ℂ (indexedSimpleRepresentations i) : ℂ) = auxiliaryTypeToComplex
    (indexedTable i 0) := by
    rw [← FDRep.char_one]
    have h1 : (indexedSimpleRepresentations i).character (1 : permutationSubgroupFin5) =
      (indexedSimpleRepresentations i).character (conjugacyClassRepresentative 0) := rfl
    rw [h1, character_indexedSimpleRepresentations]
    simp only [representationCharacterRowIndex, id_eq]
  have goalC :
      (Module.finrank ℂ (indexedSimpleRepresentations i) : ℂ) =
        ((![1, 3, 3, 4, 5] i : ℕ) : ℂ) := by
    rw [key, auxiliaryTypeToComplex, him i, hre i]
    push_cast
    ring
  exact_mod_cast goalC

/-- Representations with distinct indices are not isomorphic. -/
@[source_ref "Chapter4/Example4.8.1" (role := primary)]
lemma indexedSimpleRepresentations_pairwise_nonisomorphic (i j : Fin 5) (hij : i ≠ j) :
    ¬ Nonempty (indexedSimpleRepresentations i ≅ indexedSimpleRepresentations j) := by
  rintro ⟨e⟩
  apply hij
  have hchar : (indexedSimpleRepresentations i).character = (indexedSimpleRepresentations
    j).character := FDRep.char_iso e
  have hc : ∀ c : Fin 5, auxiliaryTypeToComplex (indexedTable i c) = auxiliaryTypeToComplex
    (indexedTable j c) := by
    intro c
    have h := congrFun hchar (conjugacyClassRepresentative c)
    rw [character_indexedSimpleRepresentations, character_indexedSimpleRepresentations] at h
    simpa only [representationCharacterRowIndex, id_eq] using h

  have inj0 : ∀ a b : Fin 5, auxiliaryTypeToComplex (indexedTable a 0) = auxiliaryTypeToComplex
    (indexedTable b 0) → indexedTable a 0 = indexedTable b 0 := by
    intro a b h
    have ha : (indexedTable a 0).im = 0 := by fin_cases a <;> decide
    have hb : (indexedTable b 0).im = 0 := by fin_cases b <;> decide
    rw [auxiliaryTypeToComplex, auxiliaryTypeToComplex, ha, hb] at h
    simp only [Rat.cast_zero, zero_mul, add_zero] at h
    exact RepresentationTheory.QuaternionGroupTwo.AuxiliaryType.ext (by exact_mod_cast h)
      (ha.trans hb.symm)
  have hdim : indexedTable i 0 = indexedTable j 0 := inj0 i j (hc 0)

  have golden : ¬ (auxiliaryTypeToComplex (indexedTable 1 3) = auxiliaryTypeToComplex (indexedTable
    2 3)) := by
    simp only [auxiliaryTypeToComplex, indexedTable, Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.cons_val_two,
      Matrix.cons_val_three, Matrix.head_cons, Matrix.tail_cons,
      RepresentationTheory.QuaternionGroupTwo.AuxiliaryType.mk_re,
      RepresentationTheory.QuaternionGroupTwo.AuxiliaryType.mk_im]
    intro h
    have hz : (Real.sqrt 5 : ℂ) = 0 := by linear_combination h
    have hsq := sq_complex_sqrt_five
    rw [hz] at hsq
    norm_num at hsq
  fin_cases i <;> fin_cases j <;>
    first
      | rfl
      | (revert hdim; decide)
      | exact absurd (hc 3) golden
      | exact absurd (hc 3).symm golden

end

end RepresentationTheory.TensorSquareSpectralDecomposition
