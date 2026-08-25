/-
Copyright (c) 2026 mathlib-initiative. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: mathlib-initiative
-/

import RepresentationTheory.Algebra.PartitionPermutation

noncomputable section

namespace RepresentationTheory.PartitionTensor.Complexification

open scoped TensorProduct
open MonoidAlgebra
open RepresentationTheory.Algebra.PartitionPermutation
open RepresentationTheory.GeneralLinearGroup.WeightCharacter
open RepresentationTheory.MonoidAlgebra.PartitionSubmoduleSandwich

variable (n : ℕ) (la : Nat.Partition n)

private abbrev coefficientBaseChangeRingHom :
    MonoidAlgebra ℚ (Equiv.Perm (Fin n)) →+* MonoidAlgebra ℂ (Equiv.Perm (Fin n)) :=
  MonoidAlgebra.mapRingHom (Equiv.Perm (Fin n)) (algebraMap ℚ ℂ)

private lemma coefficientBaseChangeRingHom_of (σ : Equiv.Perm (Fin n)) :
    coefficientBaseChangeRingHom n (MonoidAlgebra.of ℚ _ σ) =
      MonoidAlgebra.of ℂ _ σ := by
  change MonoidAlgebra.mapRingHom _ _ (MonoidAlgebra.single σ 1) =
    MonoidAlgebra.single σ 1
  rw [MonoidAlgebra.mapRingHom_single, map_one]

private lemma coefficientBaseChangeRingHom_partitionSymmetrizer :
    coefficientBaseChangeRingHom n (partitionSymmetrizer ℚ n la) =
      partitionSymmetrizer ℂ n la := by
  rw [partitionSymmetrizer_eq_map_int ℚ n la, partitionSymmetrizer_eq_map_int ℂ n la]
  ext g
  simp only [coefficientBaseChangeRingHom, MonoidAlgebra.coeff_mapRingHom]
  norm_cast

private def coefficientBaseChangeLinearMap :
    MonoidAlgebra ℚ (Equiv.Perm (Fin n)) →ₗ[ℚ] MonoidAlgebra ℂ (Equiv.Perm (Fin n)) :=
  (coefficientBaseChangeRingHom n).toAddMonoidHom.toRatLinearMap

private lemma coefficientBaseChangeLinearMap_apply
    (x : MonoidAlgebra ℚ (Equiv.Perm (Fin n))) :
    coefficientBaseChangeLinearMap n x = coefficientBaseChangeRingHom n x := rfl

private def partitionSubtypeToComplexGroupAlgebra :
    ↥(partitionSubmodule ℚ n la) →ₗ[ℚ] MonoidAlgebra ℂ (Equiv.Perm (Fin n)) :=
  (coefficientBaseChangeLinearMap n).comp
    ((partitionSubmodule ℚ n la).subtype.restrictScalars ℚ)

private lemma partitionSubtypeToComplexGroupAlgebra_apply
    (v : ↥(partitionSubmodule ℚ n la)) :
    partitionSubtypeToComplexGroupAlgebra n la v =
      coefficientBaseChangeRingHom n
        (v : MonoidAlgebra ℚ (Equiv.Perm (Fin n))) := rfl

private def partitionSubtypeComplexificationMap :
    ℂ ⊗[ℚ] ↥(partitionSubmodule ℚ n la) →ₗ[ℂ]
      MonoidAlgebra ℂ (Equiv.Perm (Fin n)) :=
  (partitionSubtypeToComplexGroupAlgebra n la).liftBaseChange ℂ

private lemma partitionSubtypeComplexificationMap_tmul
    (z : ℂ) (v : ↥(partitionSubmodule ℚ n la)) :
    partitionSubtypeComplexificationMap n la (z ⊗ₜ[ℚ] v) =
      z • coefficientBaseChangeRingHom n
        (v : MonoidAlgebra ℚ (Equiv.Perm (Fin n))) := by
  rw [partitionSubtypeComplexificationMap, LinearMap.liftBaseChange_tmul,
    partitionSubtypeToComplexGroupAlgebra_apply]

private lemma partitionSubtypeComplexificationMap_injective :
    Function.Injective (partitionSubtypeComplexificationMap n la) := by
  classical
  have hincl_inj : Function.Injective
      ((partitionSubmodule ℚ n la).subtype.restrictScalars ℚ) := by
    intro a b hab
    exact Subtype.ext hab
  have hlT : Function.Injective
      (LinearMap.lTensor ℂ ((partitionSubmodule ℚ n la).subtype.restrictScalars ℚ)) :=
    Module.Flat.lTensor_preserves_injective_linearMap _ hincl_inj
  let coeffQ := (MonoidAlgebra.coeffLinearEquiv ℚ :
    MonoidAlgebra ℚ (Equiv.Perm (Fin n)) ≃ₗ[ℚ]
      Equiv.Perm (Fin n) →₀ ℚ)
  let coeffC := (MonoidAlgebra.coeffLinearEquiv ℂ :
    MonoidAlgebra ℂ (Equiv.Perm (Fin n)) ≃ₗ[ℂ]
      Equiv.Perm (Fin n) →₀ ℂ)
  let F₀ := TensorProduct.finsuppScalarRight ℚ ℂ ℂ (Equiv.Perm (Fin n))
  let F : ℂ ⊗[ℚ] MonoidAlgebra ℚ (Equiv.Perm (Fin n)) →
      MonoidAlgebra ℂ (Equiv.Perm (Fin n)) := fun t =>
    coeffC.symm (F₀ (LinearMap.lTensor ℂ coeffQ.toLinearMap t))
  have hF_inj : Function.Injective F :=
    coeffC.symm.injective.comp (F₀.injective.comp
      (Module.Flat.lTensor_preserves_injective_linearMap _ coeffQ.injective))
  have hcomp : ∀ t, partitionSubtypeComplexificationMap n la t =
      F (LinearMap.lTensor ℂ
        ((partitionSubmodule ℚ n la).subtype.restrictScalars ℚ) t) := by
    intro t
    induction t using TensorProduct.induction_on with
    | zero => simp [F]
    | tmul z v =>
      rw [partitionSubtypeComplexificationMap_tmul, LinearMap.lTensor_tmul]
      ext g
      simp only [F, coeffQ, coeffC, F₀,
        MonoidAlgebra.coeffLinearEquiv_symm_apply]
      rw [LinearMap.lTensor_tmul]
      rw [TensorProduct.finsuppScalarRight_apply_tmul_apply,
        MonoidAlgebra.coeff_smul_apply, coefficientBaseChangeRingHom,
        MonoidAlgebra.coeff_mapRingHom]
      simp only [LinearMap.coe_restrictScalars, Submodule.coe_subtype]
      simp [Algebra.smul_def, mul_comm]
    | add x y hx hy => simp [F, hx, hy]
  have hcompose : Function.Injective
      (fun t => F (LinearMap.lTensor ℂ
        ((partitionSubmodule ℚ n la).subtype.restrictScalars ℚ) t)) :=
    hF_inj.comp hlT
  rw [show (partitionSubtypeComplexificationMap n la : _ → _) =
    fun t => F (LinearMap.lTensor ℂ
      ((partitionSubmodule ℚ n la).subtype.restrictScalars ℚ) t) from funext hcomp]
  exact hcompose

private lemma partitionSubtypeComplexificationMap_range :
    LinearMap.range (partitionSubtypeComplexificationMap n la) =
      (partitionSubmodule ℂ n la).restrictScalars ℂ := by
  classical
  rw [partitionSubtypeComplexificationMap, LinearMap.range_liftBaseChange]
  apply le_antisymm
  · rw [Submodule.span_le]
    rintro _ ⟨v, rfl⟩
    rw [SetLike.mem_coe, Submodule.restrictScalars_mem]
    obtain ⟨a, ha⟩ := Submodule.mem_span_singleton.mp v.2
    rw [partitionSubtypeToComplexGroupAlgebra_apply, ← ha, smul_eq_mul, map_mul,
      coefficientBaseChangeRingHom_partitionSymmetrizer]
    exact Submodule.mem_span_singleton.mpr
      ⟨coefficientBaseChangeRingHom n a, rfl⟩
  · set T := Submodule.span ℂ
      (↑(LinearMap.range (partitionSubtypeToComplexGroupAlgebra n la)) :
        Set (MonoidAlgebra ℂ (Equiv.Perm (Fin n)))) with hT
    have hmul : ∀ b : MonoidAlgebra ℂ (Equiv.Perm (Fin n)),
        b * partitionSymmetrizer ℂ n la ∈ T := by
      intro b
      induction b using MonoidAlgebra.induction_on with
      | hadd x y hx hy => rw [add_mul]; exact T.add_mem hx hy
      | hsmul r x hx => rw [smul_mul_assoc]; exact T.smul_mem r hx
      | hM σ =>
        have hmem : MonoidAlgebra.of ℚ _ σ * partitionSymmetrizer ℚ n la ∈
            partitionSubmodule ℚ n la :=
          Submodule.smul_mem _ (MonoidAlgebra.of ℚ _ σ) (Submodule.subset_span rfl)
        have hval : MonoidAlgebra.of ℂ _ σ * partitionSymmetrizer ℂ n la =
            partitionSubtypeToComplexGroupAlgebra n la
              ⟨MonoidAlgebra.of ℚ _ σ * partitionSymmetrizer ℚ n la, hmem⟩ := by
          rw [partitionSubtypeToComplexGroupAlgebra_apply, map_mul,
            coefficientBaseChangeRingHom_of,
            coefficientBaseChangeRingHom_partitionSymmetrizer]
        rw [hval]
        exact Submodule.subset_span (LinearMap.mem_range_self _ _)
    intro x hx
    rw [Submodule.restrictScalars_mem] at hx
    obtain ⟨b, rfl⟩ := Submodule.mem_span_singleton.mp hx
    rw [smul_eq_mul]
    exact hmul b

/-- A complex-linear equivalence from the rational partition-indexed subtype tensored with
the complex numbers to the corresponding complex partition-indexed subtype. -/
def partitionSubtypeComplexificationLinearEquiv :
    ℂ ⊗[ℚ] ↥(partitionSubmodule ℚ n la) ≃ₗ[ℂ] ↥(partitionSubmodule ℂ n la) :=
  (LinearEquiv.ofInjective (partitionSubtypeComplexificationMap n la)
    (partitionSubtypeComplexificationMap_injective n la)).trans
    (LinearEquiv.ofEq _ _ (partitionSubtypeComplexificationMap_range n la))

@[simp]
private lemma partitionSubtypeComplexificationLinearEquiv_coe
    (t : ℂ ⊗[ℚ] ↥(partitionSubmodule ℚ n la)) :
    ((partitionSubtypeComplexificationLinearEquiv n la t :
      ↥(partitionSubmodule ℂ n la)) : MonoidAlgebra ℂ (Equiv.Perm (Fin n))) =
        partitionSubtypeComplexificationMap n la t := rfl

/-- Composing the displayed equivalence with the complex base change of the map over the
rationals equals composing the map over the complex numbers with the equivalence. -/
theorem partitionSubtypeComplexificationLinearEquiv_comp_baseChange_eq_comp
    (σ : Equiv.Perm (Fin n)) :
    (partitionSubtypeComplexificationLinearEquiv n la).toLinearMap ∘ₗ
        LinearMap.baseChange ℂ (partitionSubtypeLinearEndomorphismOfPerm ℚ n la σ)
      = (partitionSubtypeLinearEndomorphismOfPerm ℂ n la σ) ∘ₗ
        (partitionSubtypeComplexificationLinearEquiv n la).toLinearMap := by
  apply LinearMap.ext
  intro t
  induction t using TensorProduct.induction_on with
  | zero => simp only [map_zero]
  | tmul z v =>
    apply Subtype.ext
    simp only [LinearMap.comp_apply, LinearMap.baseChange_tmul, LinearEquiv.coe_coe,
      partitionSubtypeComplexificationLinearEquiv_coe,
      partitionSubtypeComplexificationMap_tmul]
    change z • coefficientBaseChangeRingHom n
        (MonoidAlgebra.of ℚ _ σ * (v : MonoidAlgebra ℚ (Equiv.Perm (Fin n)))) =
      MonoidAlgebra.of ℂ _ σ *
        (z • coefficientBaseChangeRingHom n
          (v : MonoidAlgebra ℚ (Equiv.Perm (Fin n))))
    rw [map_mul, coefficientBaseChangeRingHom_of, mul_smul_comm]
  | add x y hx hy =>
    simp only [map_add]
    rw [hx, hy]

end RepresentationTheory.PartitionTensor.Complexification

end
