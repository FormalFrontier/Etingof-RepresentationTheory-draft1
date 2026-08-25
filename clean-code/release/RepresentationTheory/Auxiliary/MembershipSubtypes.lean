/-
Copyright (c) 2026 mathlib-initiative. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: mathlib-initiative
-/

import RepresentationTheory.Permutation.PartitionIndexedAuxiliary
import RepresentationTheory.PartitionFinrank














namespace RepresentationTheory.Auxiliary.MembershipSubtypes

noncomputable section

variable {n : ℕ} {la : Nat.Partition n}





/-- Maps the displayed source type into the subtype defined by membership in the displayed set. -/
noncomputable def to_membershipSubtype (T : RepresentationTheory.SymmetricGroup.PartitionAuxiliaryConstructions.AuxiliaryPartitionSource n la) :
    RepresentationTheory.PartitionAuxiliary.partitionSubmodule n la :=
  ⟨(Nat.card (↥(RepresentationTheory.SymmetricGroup.PartitionAuxiliaryConstructions.auxiliaryPartitionPermutationSubgroupB n la)) : ℂ)⁻¹ •
      MonoidAlgebra.of ℂ _ (RepresentationTheory.Combinatorics.PartitionPermutation.associatedPermutation n la T)⁻¹ * RepresentationTheory.SymmetricGroup.PartitionAuxiliaryConstructions.auxiliaryPartitionGroupAlgebraElementC n la, by
    rw [RepresentationTheory.PartitionAuxiliary.partitionSubmodule, Submodule.mem_span_singleton]
    exact ⟨(Nat.card (↥(RepresentationTheory.SymmetricGroup.PartitionAuxiliaryConstructions.auxiliaryPartitionPermutationSubgroupB n la)) : ℂ)⁻¹ •
      MonoidAlgebra.of ℂ _ (RepresentationTheory.Combinatorics.PartitionPermutation.associatedPermutation n la T)⁻¹, rfl⟩⟩



/-- Applying the displayed map to the underlying value of the subtype-valued function gives the displayed function. -/
theorem auxiliaryMap_apply_subtypeVal (T : RepresentationTheory.SymmetricGroup.PartitionAuxiliaryConstructions.AuxiliaryPartitionSource n la) :
    RepresentationTheory.Permutation.PartitionIndexedAuxiliary.auxiliaryLinearMap (n := n) (la := la) (to_membershipSubtype T : RepresentationTheory.PartitionAuxiliary.natIndexedType n) =
      RepresentationTheory.Permutation.PartitionIndexedAuxiliary.objectToAuxiliaryType2 T := by
  simp only [to_membershipSubtype, map_smul, smul_mul_assoc,
    RepresentationTheory.Permutation.PartitionIndexedAuxiliary.auxiliaryLinearMap_monomial_mul_specifiedElement]
  rw [smul_smul, inv_mul_cancel₀, one_smul, inv_inv]
  · exact RepresentationTheory.Permutation.PartitionIndexedAuxiliary.permutationToAuxiliaryType2_objectPermutation T
  · exact Nat.cast_ne_zero.mpr (Nat.card_pos (α := ↥(RepresentationTheory.SymmetricGroup.PartitionAuxiliaryConstructions.auxiliaryPartitionPermutationSubgroupB n la))).ne'


/-- The displayed subtype-valued function is linearly independent over Complex. -/
theorem linearIndependent_to_membershipSubtype :
    LinearIndependent ℂ (to_membershipSubtype :
      RepresentationTheory.SymmetricGroup.PartitionAuxiliaryConstructions.AuxiliaryPartitionSource n la → RepresentationTheory.PartitionAuxiliary.partitionSubmodule n la) := by
  let ψ : RepresentationTheory.PartitionAuxiliary.partitionSubmodule n la →ₗ[ℂ] RepresentationTheory.Permutation.PartitionIndexedAuxiliary.partitionIndexedAuxiliaryType2 n la :=
    (RepresentationTheory.Permutation.PartitionIndexedAuxiliary.auxiliaryLinearMap (n := n) (la := la)).comp
      ((RepresentationTheory.PartitionAuxiliary.partitionSubmodule n la).restrictScalars ℂ).subtype
  have hψ : ψ ∘ (to_membershipSubtype :
      RepresentationTheory.SymmetricGroup.PartitionAuxiliaryConstructions.AuxiliaryPartitionSource n la → RepresentationTheory.PartitionAuxiliary.partitionSubmodule n la) =
      (RepresentationTheory.Permutation.PartitionIndexedAuxiliary.objectToAuxiliaryType2 : RepresentationTheory.SymmetricGroup.PartitionAuxiliaryConstructions.AuxiliaryPartitionSource n la → RepresentationTheory.Permutation.PartitionIndexedAuxiliary.partitionIndexedAuxiliaryType2 n la) := by
    funext T
    change RepresentationTheory.Permutation.PartitionIndexedAuxiliary.auxiliaryLinearMap (to_membershipSubtype T : RepresentationTheory.PartitionAuxiliary.natIndexedType n) = RepresentationTheory.Permutation.PartitionIndexedAuxiliary.objectToAuxiliaryType2 T
    exact auxiliaryMap_apply_subtypeVal T
  apply LinearIndependent.of_comp ψ
  rw [hψ]
  exact RepresentationTheory.Permutation.PartitionIndexedAuxiliary.linearIndependent_objectToAuxiliaryType2


/-- The Complex span of the range of the displayed function is the top submodule. -/
theorem auxiliaryFunction_span_eq_top :
    Submodule.span ℂ (Set.range (to_membershipSubtype :
      RepresentationTheory.SymmetricGroup.PartitionAuxiliaryConstructions.AuxiliaryPartitionSource n la → RepresentationTheory.PartitionAuxiliary.partitionSubmodule n la)) = ⊤ := by
  apply linearIndependent_to_membershipSubtype.span_eq_top_of_card_eq_finrank'
  simpa only [Nat.card_eq_fintype_card] using
    (RepresentationTheory.PartitionFinrank.finrank_eq_card_auxiliaryType n la).symm


/-- A Complex basis of the displayed membership subtype, indexed by the displayed type. -/
noncomputable def membershipSubtypeBasis :
    Module.Basis (RepresentationTheory.SymmetricGroup.PartitionAuxiliaryConstructions.AuxiliaryPartitionSource n la) ℂ (RepresentationTheory.PartitionAuxiliary.partitionSubmodule n la) :=
  Module.Basis.mk linearIndependent_to_membershipSubtype auxiliaryFunction_span_eq_top.ge

/-- The membership-subtype basis evaluated at an index equals the displayed subtype-valued function. -/
@[simp] theorem membershipSubtypeBasis_apply (T : RepresentationTheory.SymmetricGroup.PartitionAuxiliaryConstructions.AuxiliaryPartitionSource n la) :
    membershipSubtypeBasis T = to_membershipSubtype T := by
  rw [membershipSubtypeBasis, Module.Basis.mk_apply]


/-- A Complex-linear map from the displayed membership subtype to the displayed codomain. -/
noncomputable def membershipSubtypeLinearMap :
    RepresentationTheory.PartitionAuxiliary.partitionSubmodule n la →ₗ[ℂ] RepresentationTheory.Permutation.PartitionIndexedAuxiliary.partitionIndexedAuxiliaryType2 n la :=
  (RepresentationTheory.Permutation.PartitionIndexedAuxiliary.auxiliaryLinearMap (n := n) (la := la)).comp
    ((RepresentationTheory.PartitionAuxiliary.partitionSubmodule n la).restrictScalars ℂ).subtype

/-- Applying the membership-subtype linear map to the displayed subtype-valued function gives the displayed function. -/
@[simp] theorem membershipSubtypeLinearMap_apply
    (T : RepresentationTheory.SymmetricGroup.PartitionAuxiliaryConstructions.AuxiliaryPartitionSource n la) :
    membershipSubtypeLinearMap (to_membershipSubtype T) = RepresentationTheory.Permutation.PartitionIndexedAuxiliary.objectToAuxiliaryType2 T :=
  auxiliaryMap_apply_subtypeVal T





/-- The range of the displayed linear map equals the Complex span of the range of the displayed function. -/
theorem membershipSubtypeLinearMap_range_eq_auxiliaryFunction_span :
    LinearMap.range (membershipSubtypeLinearMap (n := n) (la := la)) =
      Submodule.span ℂ (Set.range (RepresentationTheory.Permutation.PartitionIndexedAuxiliary.objectToAuxiliaryType2 :
        RepresentationTheory.SymmetricGroup.PartitionAuxiliaryConstructions.AuxiliaryPartitionSource n la → RepresentationTheory.Permutation.PartitionIndexedAuxiliary.partitionIndexedAuxiliaryType2 n la)) := by
  apply le_antisymm
  · rintro _ ⟨v, rfl⟩
    let b := membershipSubtypeBasis (n := n) (la := la)
    have hrepr := b.sum_repr v
    rw [← hrepr, map_sum]
    apply Submodule.sum_mem
    intro T hT
    rw [map_smul]
    apply Submodule.smul_mem
    apply Submodule.subset_span
    refine ⟨T, ?_⟩
    simp only [b, membershipSubtypeBasis_apply,
      membershipSubtypeLinearMap_apply]
  · apply Submodule.span_le.mpr
    rintro _ ⟨T, rfl⟩
    exact ⟨to_membershipSubtype T, membershipSubtypeLinearMap_apply T⟩



/-- The permutation-indexed value belongs to the range of the displayed linear map. -/
theorem perm_mem_membershipSubtypeLinearMap_range
    (σ : Equiv.Perm (Fin n)) :
    RepresentationTheory.Permutation.PartitionIndexedAuxiliary.permutationToAuxiliaryType2 (n := n) (la := la) σ ∈
      LinearMap.range (membershipSubtypeLinearMap (n := n) (la := la)) := by
  let c : ℂ := Nat.card ↥(RepresentationTheory.SymmetricGroup.PartitionAuxiliaryConstructions.auxiliaryPartitionPermutationSubgroupB n la)
  have hc : c ≠ 0 :=
    Nat.cast_ne_zero.mpr (Nat.card_pos (α := ↥(RepresentationTheory.SymmetricGroup.PartitionAuxiliaryConstructions.auxiliaryPartitionPermutationSubgroupB n la))).ne'
  let v : RepresentationTheory.PartitionAuxiliary.partitionSubmodule n la :=
    ⟨c⁻¹ • MonoidAlgebra.of ℂ _ σ⁻¹ * RepresentationTheory.SymmetricGroup.PartitionAuxiliaryConstructions.auxiliaryPartitionGroupAlgebraElementC n la, by
      rw [RepresentationTheory.PartitionAuxiliary.partitionSubmodule, Submodule.mem_span_singleton]
      exact ⟨c⁻¹ • MonoidAlgebra.of ℂ _ σ⁻¹, rfl⟩⟩
  refine ⟨v, ?_⟩
  change RepresentationTheory.Permutation.PartitionIndexedAuxiliary.auxiliaryLinearMap
      (c⁻¹ • MonoidAlgebra.of ℂ _ σ⁻¹ * RepresentationTheory.SymmetricGroup.PartitionAuxiliaryConstructions.auxiliaryPartitionGroupAlgebraElementC n la) =
    RepresentationTheory.Permutation.PartitionIndexedAuxiliary.permutationToAuxiliaryType2 σ
  simp only [map_smul, smul_mul_assoc,
    RepresentationTheory.Permutation.PartitionIndexedAuxiliary.auxiliaryLinearMap_monomial_mul_specifiedElement]
  rw [smul_smul, inv_mul_cancel₀ hc, one_smul, inv_inv]



/-- The permutation-indexed value belongs to the Complex span of the range of the displayed function. -/
theorem perm_mem_auxiliaryFunction_span
    (σ : Equiv.Perm (Fin n)) :
    RepresentationTheory.Permutation.PartitionIndexedAuxiliary.permutationToAuxiliaryType2 (n := n) (la := la) σ ∈
      Submodule.span ℂ (Set.range (RepresentationTheory.Permutation.PartitionIndexedAuxiliary.objectToAuxiliaryType2 :
        RepresentationTheory.SymmetricGroup.PartitionAuxiliaryConstructions.AuxiliaryPartitionSource n la → RepresentationTheory.Permutation.PartitionIndexedAuxiliary.partitionIndexedAuxiliaryType2 n la)) := by
  rw [← membershipSubtypeLinearMap_range_eq_auxiliaryFunction_span]
  exact perm_mem_membershipSubtypeLinearMap_range σ

end

end RepresentationTheory.Auxiliary.MembershipSubtypes
