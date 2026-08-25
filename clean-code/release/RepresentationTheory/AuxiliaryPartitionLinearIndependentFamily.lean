/-
Copyright (c) 2026 mathlib-initiative. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: mathlib-initiative
-/

import RepresentationTheory.AuxiliaryPartitionOrder
import RepresentationTheory.Alignment.Attribute















namespace RepresentationTheory.AuxiliaryPartitionLinearIndependentFamily

noncomputable section

private theorem positionEntry_eq_content {n : ℕ} {nu mu : Nat.Partition n}
    (T : RepresentationTheory.AuxiliaryPartitionCardinality.auxiliaryFamily n nu mu) (x : Fin n) :
    T.auxiliaryPositionEntry x = RepresentationTheory.SymmetricGroup.PartitionAuxiliaryConstructions.flatIndexRow (RepresentationTheory.SymmetricGroup.PartitionAuxiliaryConstructions.auxiliaryPartitionNatList mu)
      ((RepresentationTheory.Combinatorics.PartitionPermutation.associatedPermutation n nu T.toAuxiliaryObject)⁻¹ x).val := by
  let c := RepresentationTheory.Combinatorics.PartitionPermutation.finEquivPartitionIndex n nu x
  change T.1 c.1.1 c.1.2 = _
  rw [← T.entry_eq_auxiliary_nat_value c]
  congr 2




private theorem polytabloidTab_standardization_rightMul_coeff_zero_or_one {n : ℕ}
    {nu mu : Nat.Partition n} (T : RepresentationTheory.AuxiliaryPartitionCardinality.auxiliaryFamily n nu mu)
    (p : ↑(RepresentationTheory.SymmetricGroup.PartitionAuxiliaryConstructions.auxiliaryPartitionPermutationSubgroupB n mu)) :
    RepresentationTheory.Permutation.PartitionIndexedAuxiliary.objectToAuxiliaryType2 T.toAuxiliaryObject
        (RepresentationTheory.Permutation.PartitionIndexedAuxiliary.permutationAuxiliaryTypeMap (la := nu) p.val
          (RepresentationTheory.Permutation.PartitionIndexedAuxiliary.objectToAuxiliaryType n nu T.toAuxiliaryObject)) = 0 ∨
      RepresentationTheory.Permutation.PartitionIndexedAuxiliary.objectToAuxiliaryType2 T.toAuxiliaryObject
        (RepresentationTheory.Permutation.PartitionIndexedAuxiliary.permutationAuxiliaryTypeMap (la := nu) p.val
          (RepresentationTheory.Permutation.PartitionIndexedAuxiliary.objectToAuxiliaryType n nu T.toAuxiliaryObject)) = 1 := by
  classical
  let σ := RepresentationTheory.Combinatorics.PartitionPermutation.associatedPermutation n nu T.toAuxiliaryObject
  let target := RepresentationTheory.Permutation.PartitionIndexedAuxiliary.permutationAuxiliaryTypeMap (la := nu) p.val
    (RepresentationTheory.Permutation.PartitionIndexedAuxiliary.objectToAuxiliaryType n nu T.toAuxiliaryObject)
  by_cases hex : ∃ q : ↑(RepresentationTheory.SymmetricGroup.PartitionAuxiliaryConstructions.auxiliaryPartitionPermutationSubgroupA n nu),
      RepresentationTheory.Permutation.PartitionIndexedAuxiliary.permutationToAuxiliaryType n nu (q.val⁻¹ * σ) = target
  · obtain ⟨q, hq⟩ := hex
    have htarget : target = RepresentationTheory.Permutation.PartitionIndexedAuxiliary.objectToAuxiliaryType n nu T.toAuxiliaryObject := by
      have htab : RepresentationTheory.Permutation.PartitionIndexedAuxiliary.permutationToAuxiliaryType n nu (q.val⁻¹ * σ) =
          RepresentationTheory.Permutation.PartitionIndexedAuxiliary.permutationToAuxiliaryType n nu (σ * p.val) := by
        simpa only [target, RepresentationTheory.Permutation.PartitionIndexedAuxiliary.objectToAuxiliaryType, RepresentationTheory.Permutation.PartitionIndexedAuxiliary.permutationAuxiliaryTypeMap_apply_permutation] using hq
      have hr : q.val⁻¹ * σ * (σ * p.val)⁻¹ ∈ RepresentationTheory.SymmetricGroup.PartitionAuxiliaryConstructions.auxiliaryPartitionPermutationSubgroupB n nu :=
        (RepresentationTheory.Permutation.PartitionIndexedAuxiliary.permutationToAuxiliaryType_eq_iff_mul_inv_mem _ _).mp htab
      let r := q.val⁻¹ * σ * (σ * p.val)⁻¹
      have hpres : ∀ x, T.auxiliaryPositionEntry (q.val (r x)) = T.auxiliaryPositionEntry x := by
        intro x
        rw [positionEntry_eq_content T, positionEntry_eq_content T]
        have hpInv := (RepresentationTheory.SymmetricGroup.PartitionAuxiliaryConstructions.auxiliaryPartitionPermutationSubgroupB n mu).inv_mem p.prop
        have hpContent := hpInv (σ⁻¹ x)
        have hperm : σ⁻¹ * q.val * r = p.val⁻¹ * σ⁻¹ := by
          simp only [r]
          group
        have happ := congrArg (fun g : Equiv.Perm (Fin n) ↦ g x) hperm
        simp only [Equiv.Perm.coe_mul, Function.comp_apply] at happ
        rw [happ]
        exact hpContent
      have hqOne : q.val = 1 :=
        T.auxiliary_left_perm_eq_one
          q.val r q.prop hr hpres
      rw [hqOne] at hq
      simpa only [σ, RepresentationTheory.Permutation.PartitionIndexedAuxiliary.objectToAuxiliaryType, inv_one, one_mul] using hq.symm
    right
    change RepresentationTheory.Permutation.PartitionIndexedAuxiliary.objectToAuxiliaryType2 T.toAuxiliaryObject target = 1
    rw [htarget, RepresentationTheory.Permutation.PartitionIndexedAuxiliary.objectToAuxiliaryType2_apply_objectValue]
  · left
    change RepresentationTheory.Permutation.PartitionIndexedAuxiliary.objectToAuxiliaryType2 T.toAuxiliaryObject target = 0
    simp only [RepresentationTheory.Permutation.PartitionIndexedAuxiliary.objectToAuxiliaryType2]
    rw [Finsupp.finsetSum_apply]
    apply Finset.sum_eq_zero
    intro q hqmem
    rw [Finsupp.smul_apply, smul_eq_mul, Finsupp.single_apply]
    have hne : RepresentationTheory.Permutation.PartitionIndexedAuxiliary.permutationToAuxiliaryType n nu (q.val⁻¹ * σ) ≠ target := by
      intro heq
      exact hex ⟨q, heq⟩
    rw [if_neg hne, mul_zero]




/-- The indicated auxiliary evaluation is nonzero on the corresponding member of the displayed family. -/
theorem auxiliary_evaluation_ne_zero {n : ℕ}
    (mu nu : Nat.Partition n) (T : RepresentationTheory.AuxiliaryPartitionCardinality.auxiliaryFamily n nu mu) :
    RepresentationTheory.AuxiliaryPartitionLinearIndependence.auxiliaryCoordinate mu nu T
      (RepresentationTheory.AuxiliaryPartitionIndexMaps.auxiliaryFamilyMap n mu nu T) ≠ 0 := by
  classical
  letI := Fintype.ofFinite (↑(RepresentationTheory.SymmetricGroup.PartitionAuxiliaryConstructions.auxiliaryPartitionPermutationSubgroupB n mu))
  rw [RepresentationTheory.AuxiliaryPartitionLinearIndependence.auxiliaryCoordinate_apply]
  change RepresentationTheory.Auxiliary.MembershipSubtypes.membershipSubtypeLinearMap
      ((RepresentationTheory.AuxiliaryPartitionSubmodules.auxiliaryAmbientToSubmodule n mu nu
        (RepresentationTheory.Auxiliary.MembershipSubtypes.to_membershipSubtype T.toAuxiliaryObject)).1)
          (RepresentationTheory.Permutation.PartitionIndexedAuxiliary.objectToAuxiliaryType n nu T.toAuxiliaryObject) ≠ 0
  rw [RepresentationTheory.AuxiliaryPartitionPermutationAverages.auxiliary_apply_eq_inv_card_mul_sum]
  let coeff : ↑(RepresentationTheory.SymmetricGroup.PartitionAuxiliaryConstructions.auxiliaryPartitionPermutationSubgroupB n mu) → ℂ := fun p ↦
    RepresentationTheory.Permutation.PartitionIndexedAuxiliary.objectToAuxiliaryType2 T.toAuxiliaryObject
      (RepresentationTheory.Permutation.PartitionIndexedAuxiliary.permutationAuxiliaryTypeMap (la := nu) p.val
        (RepresentationTheory.Permutation.PartitionIndexedAuxiliary.objectToAuxiliaryType n nu T.toAuxiliaryObject))
  let stabilizer : Finset (↑(RepresentationTheory.SymmetricGroup.PartitionAuxiliaryConstructions.auxiliaryPartitionPermutationSubgroupB n mu)) :=
    Finset.univ.filter fun p ↦ coeff p = 1
  have hcoeff : ∀ p, coeff p = if coeff p = 1 then 1 else 0 := by
    intro p
    rcases polytabloidTab_standardization_rightMul_coeff_zero_or_one T p with hp | hp
    · change coeff p = 0 at hp
      rw [hp]
      norm_num
    · change coeff p = 1 at hp
      rw [hp]
      norm_num
  have hone : coeff ⟨1, (RepresentationTheory.SymmetricGroup.PartitionAuxiliaryConstructions.auxiliaryPartitionPermutationSubgroupB n mu).one_mem⟩ = 1 := by
    have honeAction : RepresentationTheory.Permutation.PartitionIndexedAuxiliary.permutationAuxiliaryTypeMap (la := nu) (1 : Equiv.Perm (Fin n))
        (RepresentationTheory.Permutation.PartitionIndexedAuxiliary.objectToAuxiliaryType n nu T.toAuxiliaryObject) =
          RepresentationTheory.Permutation.PartitionIndexedAuxiliary.objectToAuxiliaryType n nu T.toAuxiliaryObject := by
      change RepresentationTheory.Permutation.PartitionIndexedAuxiliary.permutationToAuxiliaryType n nu (RepresentationTheory.Combinatorics.PartitionPermutation.associatedPermutation n nu T.toAuxiliaryObject * 1) = _
      rw [mul_one]
      rfl
    simp only [coeff]
    rw [honeAction, RepresentationTheory.Permutation.PartitionIndexedAuxiliary.objectToAuxiliaryType2_apply_objectValue]
  have hstabilizer : stabilizer.Nonempty := by
    refine ⟨⟨1, (RepresentationTheory.SymmetricGroup.PartitionAuxiliaryConstructions.auxiliaryPartitionPermutationSubgroupB n mu).one_mem⟩, ?_⟩
    simp only [stabilizer, Finset.mem_filter, Finset.mem_univ, true_and]
    exact hone
  have hsum : (∑ p : ↑(RepresentationTheory.SymmetricGroup.PartitionAuxiliaryConstructions.auxiliaryPartitionPermutationSubgroupB n mu), coeff p) =
      (stabilizer.card : ℂ) := by
    calc
      (∑ p : ↑(RepresentationTheory.SymmetricGroup.PartitionAuxiliaryConstructions.auxiliaryPartitionPermutationSubgroupB n mu), coeff p) =
          ∑ p : ↑(RepresentationTheory.SymmetricGroup.PartitionAuxiliaryConstructions.auxiliaryPartitionPermutationSubgroupB n mu), if coeff p = 1 then 1 else 0 := by
            apply Finset.sum_congr rfl
            intro p hp
            exact hcoeff p
      _ = (stabilizer.card : ℂ) := by simp [stabilizer]
  rw [show (∑ p : ↑(RepresentationTheory.SymmetricGroup.PartitionAuxiliaryConstructions.auxiliaryPartitionPermutationSubgroupB n mu), RepresentationTheory.Permutation.PartitionIndexedAuxiliary.objectToAuxiliaryType2 T.toAuxiliaryObject
      (RepresentationTheory.Permutation.PartitionIndexedAuxiliary.permutationAuxiliaryTypeMap (la := nu) p.val
        (RepresentationTheory.Permutation.PartitionIndexedAuxiliary.objectToAuxiliaryType n nu T.toAuxiliaryObject))) =
          (stabilizer.card : ℂ) from hsum]
  apply mul_ne_zero
  · exact inv_ne_zero (Nat.cast_ne_zero.mpr
      (Nat.card_pos (α := ↑(RepresentationTheory.SymmetricGroup.PartitionAuxiliaryConstructions.auxiliaryPartitionPermutationSubgroupB n mu))).ne')
  · exact Nat.cast_ne_zero.mpr (Finset.card_ne_zero.mpr hstabilizer)


/-- The displayed auxiliary family indexed by partition-dependent objects is linearly independent over the complex numbers. -/
theorem auxiliary_linearIndependent {n : ℕ}
    (mu nu : Nat.Partition n) :
    LinearIndependent ℂ (RepresentationTheory.AuxiliaryPartitionIndexMaps.auxiliaryFamilyMap n mu nu) :=
  RepresentationTheory.AuxiliaryPartitionOrder.auxiliary_linearIndependent_of_diagonal_evaluation_ne_zero mu nu
    (auxiliary_evaluation_ne_zero mu nu)


/-- An auxiliary object associated with a pair of partitions. -/
noncomputable def auxiliaryObject {n : ℕ}
    (mu nu : Nat.Partition n) : RepresentationTheory.AuxiliaryPartitionSubmodules.auxiliaryStructure n mu nu :=
  RepresentationTheory.AuxiliaryPartitionLinearIndependence.auxiliaryConstructionOfLinearIndependent mu nu
    (auxiliary_linearIndependent mu nu)



/-- The two displayed auxiliary natural-number quantities associated with the pair of partitions are equal. -/
@[source_ref "Chapter5/Proposition5.14.1" (role := primary),
  source_ref "Chapter5/Definition5.14.2" (role := supporting),
  source_ref "Chapter5/Remark5.15.5" (role := supporting)]
theorem auxiliary_nat_values_eq (n : ℕ)
    (mu nu : Nat.Partition n) :
    RepresentationTheory.AuxiliaryPartitionDecomposition.auxiliaryNatValue n mu nu = RepresentationTheory.YoungDiagram.PartitionConstructions.auxiliaryPartitionPairNat n nu mu :=
  RepresentationTheory.AuxiliaryPartitionSubmodules.auxiliary_nat_value_eq_of_structure n mu nu
    (auxiliaryObject mu nu)

end

end RepresentationTheory.AuxiliaryPartitionLinearIndependentFamily
