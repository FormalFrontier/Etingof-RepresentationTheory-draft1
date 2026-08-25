/-
Copyright (c) 2026 mathlib-initiative. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: mathlib-initiative
-/

import RepresentationTheory.MonoidAlgebra.PartitionSubmoduleSandwich
import RepresentationTheory.GeneralLinearGroup.WeightCharacter
import RepresentationTheory.SimpleModule.SubtypeRepresentation
import RepresentationTheory.Alignment.Attribute

open scoped TensorProduct

namespace RepresentationTheory.PartitionModels

noncomputable section

open RepresentationTheory.GeneralLinearGroup.WeightCharacter
open RepresentationTheory.MonoidAlgebra.PartitionSubmoduleSandwich
open RepresentationTheory.SimpleModule.SubtypeRepresentation
open RepresentationTheory.SymmetricGroup.PartitionAuxiliaryConstructions

variable (n : ℕ) (la : Nat.Partition n)

private abbrev coeffMapRatComplex (n : ℕ) :
    MonoidAlgebra ℚ (Equiv.Perm (Fin n)) →+* MonoidAlgebra ℂ (Equiv.Perm (Fin n)) :=
  MonoidAlgebra.mapRingHom (Equiv.Perm (Fin n)) (algebraMap ℚ ℂ)

private theorem coeffMapRatComplex_partitionSymmetrizer
    (n : ℕ) (la : Nat.Partition n) :
    coeffMapRatComplex n (partitionSymmetrizer ℚ n la) =
      auxiliaryPartitionGroupAlgebraElementC n la := by
  rw [partitionSymmetrizer_eq_map_int, complexPartitionSymmetrizer_eq_map_int]
  ext x
  simp only [coeffMapRatComplex, MonoidAlgebra.coeff_mapRingHom, eq_intCast]
  norm_cast

private def groupAlgebraScalarExtensionMap (n : ℕ) :
    (ℂ ⊗[ℚ] MonoidAlgebra ℚ (Equiv.Perm (Fin n))) →ₗ[ℂ]
      MonoidAlgebra ℂ (Equiv.Perm (Fin n)) :=
  (MonoidAlgebra.coeffLinearEquiv ℂ).symm.toLinearMap ∘ₗ
    (TensorProduct.finsuppScalarRight ℚ ℂ ℂ (Equiv.Perm (Fin n))).toLinearMap ∘ₗ
      LinearMap.baseChange ℂ (MonoidAlgebra.coeffLinearEquiv ℚ).toLinearMap

private def partitionScalarExtensionMap (n : ℕ) (la : Nat.Partition n) :
    (ℂ ⊗[ℚ] ↑(partitionSubmodule ℚ n la)) →ₗ[ℂ]
      MonoidAlgebra ℂ (Equiv.Perm (Fin n)) :=
  groupAlgebraScalarExtensionMap n ∘ₗ
    LinearMap.baseChange ℂ ((partitionSubmodule ℚ n la).subtype.restrictScalars ℚ)

private theorem partitionScalarExtensionMap_tmul
    (z : ℂ) (w : partitionSubmodule ℚ n la) :
    partitionScalarExtensionMap n la (z ⊗ₜ[ℚ] w) =
      z • coeffMapRatComplex n
        (w : MonoidAlgebra ℚ (Equiv.Perm (Fin n))) := by
  ext g
  simp only [partitionScalarExtensionMap, groupAlgebraScalarExtensionMap,
    LinearMap.comp_apply, LinearMap.baseChange_tmul,
    MonoidAlgebra.coeff_smul_apply, coeffMapRatComplex,
    MonoidAlgebra.coeff_mapRingHom, LinearMap.coe_restrictScalars,
    Submodule.coe_subtype]
  simp [Algebra.smul_def, mul_comm]

private theorem partitionScalarExtensionMap_injective :
    Function.Injective (partitionScalarExtensionMap n la) := by
  have h : Function.Injective
      ((partitionSubmodule ℚ n la).subtype.restrictScalars ℚ) :=
    Subtype.coe_injective
  have hbc : Function.Injective
      ⇑(LinearMap.baseChange ℂ
        ((partitionSubmodule ℚ n la).subtype.restrictScalars ℚ)) := by
    rw [LinearMap.baseChange_eq_ltensor]
    exact Module.Flat.lTensor_preserves_injective_linearMap _ h
  have hcoeff : Function.Injective
      (LinearMap.baseChange ℂ
        (MonoidAlgebra.coeffLinearEquiv ℚ :
          MonoidAlgebra ℚ (Equiv.Perm (Fin n)) ≃ₗ[ℚ]
            Equiv.Perm (Fin n) →₀ ℚ).toLinearMap) := by
    rw [LinearMap.baseChange_eq_ltensor]
    exact Module.Flat.lTensor_preserves_injective_linearMap _
      (MonoidAlgebra.coeffLinearEquiv ℚ).injective
  exact (MonoidAlgebra.coeffLinearEquiv ℂ).symm.injective.comp
    ((TensorProduct.finsuppScalarRight ℚ ℂ ℂ (Equiv.Perm (Fin n))).injective.comp
      (hcoeff.comp hbc))

private theorem coeffMapRatComplex_mem_partitionSubmodule
    (y : MonoidAlgebra ℚ (Equiv.Perm (Fin n)))
    (hy : y ∈ partitionSubmodule ℚ n la) :
    coeffMapRatComplex n y ∈ PartitionAuxiliary.partitionSubmodule n la := by
  induction hy using Submodule.span_induction with
  | mem y hy =>
    rw [Set.mem_singleton_iff] at hy
    subst hy
    rw [coeffMapRatComplex_partitionSymmetrizer]
    exact Submodule.subset_span rfl
  | zero => simp
  | add a b _ _ ha hb =>
    rw [map_add]
    exact (PartitionAuxiliary.partitionSubmodule n la).add_mem ha hb
  | smul a b _ hb =>
    rw [smul_eq_mul, map_mul]
    exact (PartitionAuxiliary.partitionSubmodule n la).smul_mem
      (coeffMapRatComplex n a) hb

private theorem partitionScalarExtensionMap_mem
    (x : ℂ ⊗[ℚ] partitionSubmodule ℚ n la) :
    partitionScalarExtensionMap n la x ∈
      PartitionAuxiliary.partitionSubmodule n la := by
  induction x using TensorProduct.induction_on with
  | zero => simp
  | tmul z w =>
    rw [partitionScalarExtensionMap_tmul]
    exact (PartitionAuxiliary.partitionSubmodule n la).smul_of_tower_mem z
      (coeffMapRatComplex_mem_partitionSubmodule n la _ w.2)
  | add a b ha hb =>
    rw [map_add]
    exact (PartitionAuxiliary.partitionSubmodule n la).add_mem ha hb

private theorem coeffMapRatComplex_of (g : Equiv.Perm (Fin n)) :
    coeffMapRatComplex n (MonoidAlgebra.of ℚ (Equiv.Perm (Fin n)) g) =
      MonoidAlgebra.of ℂ (Equiv.Perm (Fin n)) g := by
  change MonoidAlgebra.mapRingHom _ _ (MonoidAlgebra.single g 1) =
    MonoidAlgebra.single g 1
  rw [MonoidAlgebra.mapRingHom_single, map_one]

private theorem partitionScalarExtensionMap_smul_of
    (g : Equiv.Perm (Fin n)) (z : ℂ) (w : partitionSubmodule ℚ n la) :
    MonoidAlgebra.of ℂ _ g • partitionScalarExtensionMap n la (z ⊗ₜ[ℚ] w) =
      partitionScalarExtensionMap n la
        (z ⊗ₜ[ℚ] (MonoidAlgebra.of ℚ _ g • w)) := by
  rw [partitionScalarExtensionMap_tmul, partitionScalarExtensionMap_tmul,
    Submodule.coe_smul]
  conv_rhs =>
    rw [show (MonoidAlgebra.of ℚ (Equiv.Perm (Fin n)) g •
          (w : MonoidAlgebra ℚ _)) =
        MonoidAlgebra.of ℚ _ g * (w : MonoidAlgebra ℚ _) from rfl,
      map_mul, coeffMapRatComplex_of]
  rw [smul_comm (MonoidAlgebra.of ℂ (Equiv.Perm (Fin n)) g) z, smul_eq_mul]

private def leftPermutationLinearMap (g : Equiv.Perm (Fin n)) :
    partitionSubmodule ℚ n la →ₗ[ℚ] partitionSubmodule ℚ n la :=
  DistribSMul.toLinearMap ℚ (partitionSubmodule ℚ n la)
    (MonoidAlgebra.of ℚ _ g)

private theorem partitionScalarExtensionMap_smul_of_all
    (g : Equiv.Perm (Fin n)) (x : ℂ ⊗[ℚ] partitionSubmodule ℚ n la) :
    MonoidAlgebra.of ℂ _ g • partitionScalarExtensionMap n la x =
      partitionScalarExtensionMap n la
        (LinearMap.baseChange ℂ (leftPermutationLinearMap n la g) x) := by
  induction x using TensorProduct.induction_on with
  | zero => simp
  | tmul z w =>
    rw [LinearMap.baseChange_tmul, partitionScalarExtensionMap_smul_of]
    rfl
  | add a b ha hb =>
    rw [map_add, map_add, smul_add, ha, hb, map_add]

private theorem partitionScalarExtensionMap_range_smul_mem
    (a : MonoidAlgebra ℂ (Equiv.Perm (Fin n)))
    (y : MonoidAlgebra ℂ (Equiv.Perm (Fin n)))
    (hy : y ∈ LinearMap.range (partitionScalarExtensionMap n la)) :
    a • y ∈ LinearMap.range (partitionScalarExtensionMap n la) := by
  obtain ⟨x, rfl⟩ := hy
  induction a using MonoidAlgebra.induction_on with
  | hM g =>
    rw [partitionScalarExtensionMap_smul_of_all]
    exact LinearMap.mem_range_self _ _
  | hadd a b ha hb =>
    rw [add_smul]
    exact (LinearMap.range _).add_mem ha hb
  | hsmul r a ha =>
    rw [smul_assoc]
    exact (LinearMap.range _).smul_mem r ha

private theorem complexPartitionSubmodule_le_range :
    (PartitionAuxiliary.partitionSubmodule n la).restrictScalars ℂ ≤
      LinearMap.range (partitionScalarExtensionMap n la) := by
  intro v hv
  induction hv using Submodule.span_induction with
  | mem v hv =>
    rw [Set.mem_singleton_iff] at hv
    subst hv
    refine ⟨1 ⊗ₜ[ℚ]
      ⟨partitionSymmetrizer ℚ n la, Submodule.subset_span rfl⟩, ?_⟩
    rw [partitionScalarExtensionMap_tmul, one_smul,
      coeffMapRatComplex_partitionSymmetrizer]
  | zero => exact (LinearMap.range _).zero_mem
  | add a b _ _ ha hb => exact (LinearMap.range _).add_mem ha hb
  | smul a b _ hb =>
    exact partitionScalarExtensionMap_range_smul_mem n la a b hb

private def partitionComplexificationEquiv :
    (ℂ ⊗[ℚ] partitionSubmodule ℚ n la) ≃ₗ[ℂ]
      PartitionAuxiliary.partitionSubmodule n la :=
  LinearEquiv.ofBijective
    ((partitionScalarExtensionMap n la).codRestrict
      ((PartitionAuxiliary.partitionSubmodule n la).restrictScalars ℂ)
      (partitionScalarExtensionMap_mem n la))
    ⟨fun a b h => partitionScalarExtensionMap_injective n la (Subtype.ext_iff.mp h),
      fun v => by
        obtain ⟨x, hx⟩ := complexPartitionSubmodule_le_range n la v.2
        exact ⟨x, Subtype.ext hx⟩⟩

private theorem partitionComplexificationEquiv_apply
    (x : ℂ ⊗[ℚ] partitionSubmodule ℚ n la) :
    (partitionComplexificationEquiv n la x :
      MonoidAlgebra ℂ (Equiv.Perm (Fin n))) =
        partitionScalarExtensionMap n la x := rfl

/-- For each partition, there exists a map from the complex scalar extension of the associated
rational module that intertwines the permutation action. -/
@[source_ref"Chapter5/Corollary5.12.4"(role:=supporting)]
theorem exists_perm_equivariant_complexification (n : ℕ) (la : Nat.Partition n) :
    ∃ e : (ℂ ⊗[ℚ] partitionSubmodule ℚ n la) ≃ₗ[ℂ]
        PartitionAuxiliary.partitionSubmodule n la,
      ∀ (g : Equiv.Perm (Fin n)) (z : ℂ) (w : partitionSubmodule ℚ n la),
        (e (z ⊗ₜ[ℚ] (MonoidAlgebra.of ℚ _ g • w)) :
            MonoidAlgebra ℂ (Equiv.Perm (Fin n))) =
          MonoidAlgebra.of ℂ _ g •
            (e (z ⊗ₜ[ℚ] w) : MonoidAlgebra ℂ (Equiv.Perm (Fin n))) := by
  refine ⟨partitionComplexificationEquiv n la, fun g z w => ?_⟩
  rw [partitionComplexificationEquiv_apply,
    partitionComplexificationEquiv_apply,
    ← partitionScalarExtensionMap_smul_of]

/-- Every simple module over the displayed algebra admits a partition-indexed model whose
rational permutation module is simple and whose complex scalar extension intertwines the
permutation action. -/
@[source_ref"Chapter5/Corollary5.12.4"(role:=supporting)]
theorem exists_partition_model_with_equivariant_complexification
    (n : ℕ) (M : Type)
    [AddCommGroup M] [Module (PartitionAuxiliary.natIndexedType n) M]
    [IsSimpleModule (PartitionAuxiliary.natIndexedType n) M] :
    ∃ la : Nat.Partition n,
      Nonempty (M ≃ₗ[PartitionAuxiliary.natIndexedType n]
        PartitionAuxiliary.partitionSubmodule n la) ∧
      IsSimpleModule (MonoidAlgebra ℚ (Equiv.Perm (Fin n)))
        (partitionSubmodule ℚ n la) ∧
      ∃ e : (ℂ ⊗[ℚ] partitionSubmodule ℚ n la) ≃ₗ[ℂ]
          PartitionAuxiliary.partitionSubmodule n la,
        ∀ (g : Equiv.Perm (Fin n)) (z : ℂ) (w : partitionSubmodule ℚ n la),
          (e (z ⊗ₜ[ℚ] (MonoidAlgebra.of ℚ _ g • w)) :
              MonoidAlgebra ℂ (Equiv.Perm (Fin n))) =
            MonoidAlgebra.of ℂ _ g •
              (e (z ⊗ₜ[ℚ] w) : MonoidAlgebra ℂ (Equiv.Perm (Fin n))) := by
  obtain ⟨la, hM⟩ := exists_linearEquiv_to_subtype n M
  exact ⟨la, hM, isSimpleModule_partitionSubmodule_rat n la,
    exists_perm_equivariant_complexification n la⟩

end

end RepresentationTheory.PartitionModels
