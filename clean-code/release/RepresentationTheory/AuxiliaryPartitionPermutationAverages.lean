/-
Copyright (c) 2026 mathlib-initiative. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: mathlib-initiative
-/

import RepresentationTheory.AuxiliaryPartitionIndexMaps










namespace RepresentationTheory.AuxiliaryPartitionPermutationAverages

noncomputable section


/-- Applying the auxiliary map for a permutation and then the map for its inverse recovers the original input. -/
@[simp] theorem auxiliaryPermutationMap_inv_apply {n : ℕ} {nu : Nat.Partition n}
    (p : Equiv.Perm (Fin n)) (t : RepresentationTheory.Permutation.PartitionIndexedAuxiliary.partitionIndexedAuxiliaryType n nu) :
    RepresentationTheory.Permutation.PartitionIndexedAuxiliary.permutationAuxiliaryTypeMap (la := nu) p⁻¹ (RepresentationTheory.Permutation.PartitionIndexedAuxiliary.permutationAuxiliaryTypeMap (la := nu) p t) = t := by
  induction t using Quotient.inductionOn with
  | _ σ =>
      change RepresentationTheory.Permutation.PartitionIndexedAuxiliary.permutationToAuxiliaryType n nu ((σ * p) * p⁻¹) = RepresentationTheory.Permutation.PartitionIndexedAuxiliary.permutationToAuxiliaryType n nu σ
      congr 1
      group


/-- The auxiliary map associated with a finite permutation is injective. -/
theorem auxiliaryPermutationMap_injective {n : ℕ} {nu : Nat.Partition n}
    (p : Equiv.Perm (Fin n)) :
    Function.Injective (RepresentationTheory.Permutation.PartitionIndexedAuxiliary.permutationAuxiliaryTypeMap (la := nu) p) := by
  intro t u h
  have := congrArg (RepresentationTheory.Permutation.PartitionIndexedAuxiliary.permutationAuxiliaryTypeMap (la := nu) p⁻¹) h
  simpa using this



/-- The displayed auxiliary function equals an inverse-cardinality scalar multiple of a finite sum of permuted functions. -/
theorem auxiliary_eq_inv_card_smul_sum {n : ℕ}
    {mu nu : Nat.Partition n} (T : RepresentationTheory.AuxiliaryPartitionCardinality.auxiliaryFamily n nu mu) :
    letI := Fintype.ofFinite (↥(RepresentationTheory.SymmetricGroup.PartitionAuxiliaryConstructions.auxiliaryPartitionPermutationSubgroupB n mu))
    RepresentationTheory.Auxiliary.MembershipSubtypes.membershipSubtypeLinearMap
          ((RepresentationTheory.AuxiliaryPartitionSubmodules.auxiliaryAmbientToSubmodule n mu nu
            (RepresentationTheory.Auxiliary.MembershipSubtypes.to_membershipSubtype T.toAuxiliaryObject)).1) =
        (Nat.card (↥(RepresentationTheory.SymmetricGroup.PartitionAuxiliaryConstructions.auxiliaryPartitionPermutationSubgroupB n mu)) : ℂ)⁻¹ •
          ∑ p : ↥(RepresentationTheory.SymmetricGroup.PartitionAuxiliaryConstructions.auxiliaryPartitionPermutationSubgroupB n mu),
            Finsupp.mapDomain (RepresentationTheory.Permutation.PartitionIndexedAuxiliary.permutationAuxiliaryTypeMap (la := nu) p.val⁻¹)
              (RepresentationTheory.Permutation.PartitionIndexedAuxiliary.objectToAuxiliaryType2 T.toAuxiliaryObject) := by
  classical
  unfold RepresentationTheory.Auxiliary.MembershipSubtypes.membershipSubtypeLinearMap RepresentationTheory.AuxiliaryPartitionSubmodules.auxiliaryAmbientToSubmodule RepresentationTheory.AuxiliaryPartitionSubmodules.auxiliaryEndomorphism
  change RepresentationTheory.Permutation.PartitionIndexedAuxiliary.auxiliaryLinearMap
      ((Nat.card (↥(RepresentationTheory.SymmetricGroup.PartitionAuxiliaryConstructions.auxiliaryPartitionPermutationSubgroupB n mu)) : ℂ)⁻¹ •
        (RepresentationTheory.SymmetricGroup.PartitionAuxiliaryConstructions.auxiliaryPartitionGroupAlgebraElementB n mu *
          (RepresentationTheory.Auxiliary.MembershipSubtypes.to_membershipSubtype T.toAuxiliaryObject : RepresentationTheory.PartitionAuxiliary.natIndexedType n))) = _
  rw [map_smul]
  congr 1
  simp only [RepresentationTheory.SymmetricGroup.PartitionAuxiliaryConstructions.auxiliaryPartitionGroupAlgebraElementB, Finset.sum_mul, map_sum, RepresentationTheory.Permutation.PartitionIndexedAuxiliary.auxiliaryLinearMap_monomial_mul,
    RepresentationTheory.Auxiliary.MembershipSubtypes.auxiliaryMap_apply_subtypeVal]
  apply Finset.sum_congr
  · ext
    simp
  · intro p hp
    rfl




/-- Pointwise evaluation of the displayed auxiliary function equals an inverse-cardinality multiple of a finite sum. -/
theorem auxiliary_apply_eq_inv_card_mul_sum {n : ℕ}
    {mu nu : Nat.Partition n} (T : RepresentationTheory.AuxiliaryPartitionCardinality.auxiliaryFamily n nu mu) (t : RepresentationTheory.Permutation.PartitionIndexedAuxiliary.partitionIndexedAuxiliaryType n nu) :
    letI := Fintype.ofFinite (↥(RepresentationTheory.SymmetricGroup.PartitionAuxiliaryConstructions.auxiliaryPartitionPermutationSubgroupB n mu))
    RepresentationTheory.Auxiliary.MembershipSubtypes.membershipSubtypeLinearMap
          ((RepresentationTheory.AuxiliaryPartitionSubmodules.auxiliaryAmbientToSubmodule n mu nu
            (RepresentationTheory.Auxiliary.MembershipSubtypes.to_membershipSubtype T.toAuxiliaryObject)).1) t =
        (Nat.card (↥(RepresentationTheory.SymmetricGroup.PartitionAuxiliaryConstructions.auxiliaryPartitionPermutationSubgroupB n mu)) : ℂ)⁻¹ *
          ∑ p : ↥(RepresentationTheory.SymmetricGroup.PartitionAuxiliaryConstructions.auxiliaryPartitionPermutationSubgroupB n mu),
            RepresentationTheory.Permutation.PartitionIndexedAuxiliary.objectToAuxiliaryType2 T.toAuxiliaryObject
              (RepresentationTheory.Permutation.PartitionIndexedAuxiliary.permutationAuxiliaryTypeMap (la := nu) p.val t) := by
  classical
  rw [auxiliary_eq_inv_card_smul_sum T]
  simp only [Finsupp.smul_apply, smul_eq_mul, Finsupp.finsetSum_apply]
  congr 1
  apply Finset.sum_congr
  · ext
    simp
  · intro p hp
    let a := RepresentationTheory.Permutation.PartitionIndexedAuxiliary.permutationAuxiliaryTypeMap (la := nu) p.val t
    have ha : RepresentationTheory.Permutation.PartitionIndexedAuxiliary.permutationAuxiliaryTypeMap (la := nu) p.val⁻¹ a = t :=
      auxiliaryPermutationMap_inv_apply p.val t
    calc
      Finsupp.mapDomain (RepresentationTheory.Permutation.PartitionIndexedAuxiliary.permutationAuxiliaryTypeMap (la := nu) p.val⁻¹)
          (RepresentationTheory.Permutation.PartitionIndexedAuxiliary.objectToAuxiliaryType2 T.toAuxiliaryObject) t =
          Finsupp.mapDomain (RepresentationTheory.Permutation.PartitionIndexedAuxiliary.permutationAuxiliaryTypeMap (la := nu) p.val⁻¹)
            (RepresentationTheory.Permutation.PartitionIndexedAuxiliary.objectToAuxiliaryType2 T.toAuxiliaryObject)
              (RepresentationTheory.Permutation.PartitionIndexedAuxiliary.permutationAuxiliaryTypeMap (la := nu) p.val⁻¹ a) := by rw [ha]
      _ = RepresentationTheory.Permutation.PartitionIndexedAuxiliary.objectToAuxiliaryType2 T.toAuxiliaryObject a :=
        Finsupp.mapDomain_apply
          (auxiliaryPermutationMap_injective (nu := nu) p.val⁻¹)
          (RepresentationTheory.Permutation.PartitionIndexedAuxiliary.objectToAuxiliaryType2 T.toAuxiliaryObject) a




/-- A nonzero auxiliary evaluation yields a subgroup element satisfying the displayed relation between the two standardized permutations. -/
theorem auxiliary_exists_of_ne_zero {n : ℕ}
    {mu nu : Nat.Partition n} (T U : RepresentationTheory.AuxiliaryPartitionCardinality.auxiliaryFamily n nu mu)
    (hne : RepresentationTheory.Auxiliary.MembershipSubtypes.membershipSubtypeLinearMap
      ((RepresentationTheory.AuxiliaryPartitionSubmodules.auxiliaryAmbientToSubmodule n mu nu
        (RepresentationTheory.Auxiliary.MembershipSubtypes.to_membershipSubtype T.toAuxiliaryObject)).1)
          (RepresentationTheory.Permutation.PartitionIndexedAuxiliary.objectToAuxiliaryType n nu U.toAuxiliaryObject) ≠ 0) :
    ∃ p : ↥(RepresentationTheory.SymmetricGroup.PartitionAuxiliaryConstructions.auxiliaryPartitionPermutationSubgroupB n mu),
      RepresentationTheory.Permutation.PartitionIndexedAuxiliary.permutationRel nu (RepresentationTheory.Combinatorics.PartitionPermutation.associatedPermutation n nu T.toAuxiliaryObject)
        (RepresentationTheory.Combinatorics.PartitionPermutation.associatedPermutation n nu U.toAuxiliaryObject * p.val) := by
  classical
  letI := Fintype.ofFinite (↥(RepresentationTheory.SymmetricGroup.PartitionAuxiliaryConstructions.auxiliaryPartitionPermutationSubgroupB n mu))
  rw [auxiliary_apply_eq_inv_card_mul_sum]
    at hne
  have hsum :
      (∑ p : ↥(RepresentationTheory.SymmetricGroup.PartitionAuxiliaryConstructions.auxiliaryPartitionPermutationSubgroupB n mu),
        RepresentationTheory.Permutation.PartitionIndexedAuxiliary.objectToAuxiliaryType2 T.toAuxiliaryObject
          (RepresentationTheory.Permutation.PartitionIndexedAuxiliary.permutationAuxiliaryTypeMap (la := nu) p.val
            (RepresentationTheory.Permutation.PartitionIndexedAuxiliary.objectToAuxiliaryType n nu U.toAuxiliaryObject))) ≠ 0 := by
    intro hzero
    rw [hzero, mul_zero] at hne
    exact hne rfl
  obtain ⟨p, hp⟩ := Finset.exists_ne_zero_of_sum_ne_zero hsum
  refine ⟨p, RepresentationTheory.Permutation.PartitionIndexedAuxiliary.permutationRel_of_objectToAuxiliaryType2_apply_ne_zero T.toAuxiliaryObject
    (RepresentationTheory.Combinatorics.PartitionPermutation.associatedPermutation n nu U.toAuxiliaryObject * p.val) ?_⟩
  simpa only [RepresentationTheory.Permutation.PartitionIndexedAuxiliary.objectToAuxiliaryType, RepresentationTheory.Permutation.PartitionIndexedAuxiliary.permutationAuxiliaryTypeMap_apply_permutation] using hp.2





/-- An auxiliary natural-number function determined by two partitions, a finite permutation, and two natural-number arguments. -/
noncomputable def auxiliaryPermutationNatFunction {n : ℕ} (mu nu : Nat.Partition n)
    (σ : Equiv.Perm (Fin n)) (a i : ℕ) : ℕ :=
  ((Finset.univ : Finset (Fin n)).filter fun e =>
    RepresentationTheory.SymmetricGroup.PartitionAuxiliaryConstructions.flatIndexRow (RepresentationTheory.SymmetricGroup.PartitionAuxiliaryConstructions.auxiliaryPartitionNatList mu) e.val < a ∧
      RepresentationTheory.SymmetricGroup.PartitionAuxiliaryConstructions.flatIndexRow (RepresentationTheory.SymmetricGroup.PartitionAuxiliaryConstructions.auxiliaryPartitionNatList nu) (σ e).val < i).card



/-- An auxiliary natural-number function of an indexing object and two natural-number arguments. -/
noncomputable def _root_.RepresentationTheory.AuxiliaryPartitionCardinality.auxiliaryFamily.auxiliaryNatFunction {n : ℕ}
    {nu mu : Nat.Partition n} (T : RepresentationTheory.AuxiliaryPartitionCardinality.auxiliaryFamily n nu mu) (a i : ℕ) : ℕ :=
  ((Finset.univ : Finset (RepresentationTheory.Combinatorics.PartitionPermutation.PartitionIndex n nu)).filter fun c =>
    T.1 c.1.1 c.1.2 < a ∧ c.1.1 < i).card



/-- The auxiliary natural-number function is unchanged by right multiplication with an element of the displayed subgroup. -/
theorem auxiliaryPermutationNatFunction_mul_eq {n : ℕ} (mu nu : Nat.Partition n)
    (σ : Equiv.Perm (Fin n)) (p : Equiv.Perm (Fin n))
    (hp : p ∈ RepresentationTheory.SymmetricGroup.PartitionAuxiliaryConstructions.auxiliaryPartitionPermutationSubgroupB n mu) (a i : ℕ) :
    auxiliaryPermutationNatFunction mu nu (σ * p) a i =
      auxiliaryPermutationNatFunction mu nu σ a i := by
  classical
  let source := (Finset.univ : Finset (Fin n)).filter fun e =>
    RepresentationTheory.SymmetricGroup.PartitionAuxiliaryConstructions.flatIndexRow (RepresentationTheory.SymmetricGroup.PartitionAuxiliaryConstructions.auxiliaryPartitionNatList mu) e.val < a ∧
      RepresentationTheory.SymmetricGroup.PartitionAuxiliaryConstructions.flatIndexRow (RepresentationTheory.SymmetricGroup.PartitionAuxiliaryConstructions.auxiliaryPartitionNatList nu) ((σ * p) e).val < i
  let target := (Finset.univ : Finset (Fin n)).filter fun e =>
    RepresentationTheory.SymmetricGroup.PartitionAuxiliaryConstructions.flatIndexRow (RepresentationTheory.SymmetricGroup.PartitionAuxiliaryConstructions.auxiliaryPartitionNatList mu) e.val < a ∧
      RepresentationTheory.SymmetricGroup.PartitionAuxiliaryConstructions.flatIndexRow (RepresentationTheory.SymmetricGroup.PartitionAuxiliaryConstructions.auxiliaryPartitionNatList nu) (σ e).val < i
  change source.card = target.card
  apply Finset.card_bij (fun e _ => p e)
  · intro e he
    rw [Finset.mem_filter] at he ⊢
    refine ⟨Finset.mem_univ _, ?_, ?_⟩
    · rw [hp e]
      exact he.2.1
    · simpa only [Equiv.Perm.coe_mul, Function.comp_apply] using he.2.2
  · intro e₁ h₁ e₂ h₂ heq
    exact p.injective heq
  · intro e he
    refine ⟨p⁻¹ e, ?_, p.apply_symm_apply e⟩
    rw [Finset.mem_filter] at he ⊢
    refine ⟨Finset.mem_univ _, ?_, ?_⟩
    · have hpInv := (RepresentationTheory.SymmetricGroup.PartitionAuxiliaryConstructions.auxiliaryPartitionPermutationSubgroupB n mu).inv_mem hp
      rw [hpInv e]
      exact he.2.1
    · simp only [Equiv.Perm.coe_mul, Function.comp_apply]
      have hpe : p (p⁻¹ e) = e := p.apply_symm_apply e
      rw [hpe]
      exact he.2.2



/-- At the displayed standardizing permutation, the auxiliary natural-number function agrees with the indexing object's displayed natural-number function. -/
theorem auxiliaryPermutationNatFunction_standardization {n : ℕ}
    {nu mu : Nat.Partition n} (T : RepresentationTheory.AuxiliaryPartitionCardinality.auxiliaryFamily n nu mu) (a i : ℕ) :
    auxiliaryPermutationNatFunction mu nu (RepresentationTheory.Combinatorics.PartitionPermutation.associatedPermutation n nu T.toAuxiliaryObject) a i =
      T.auxiliaryNatFunction a i := by
  classical
  let e : RepresentationTheory.Combinatorics.PartitionPermutation.PartitionIndex n nu ≃ Fin n :=
    Equiv.ofBijective T.toAuxiliaryObject.1 T.toAuxiliaryObject.2.1
  let source := (Finset.univ : Finset (Fin n)).filter fun x =>
    RepresentationTheory.SymmetricGroup.PartitionAuxiliaryConstructions.flatIndexRow (RepresentationTheory.SymmetricGroup.PartitionAuxiliaryConstructions.auxiliaryPartitionNatList mu) x.val < a ∧
      RepresentationTheory.SymmetricGroup.PartitionAuxiliaryConstructions.flatIndexRow (RepresentationTheory.SymmetricGroup.PartitionAuxiliaryConstructions.auxiliaryPartitionNatList nu) (RepresentationTheory.Combinatorics.PartitionPermutation.associatedPermutation n nu T.toAuxiliaryObject x).val < i
  let target := (Finset.univ : Finset (RepresentationTheory.Combinatorics.PartitionPermutation.PartitionIndex n nu)).filter fun c =>
    T.1 c.1.1 c.1.2 < a ∧ c.1.1 < i
  change source.card = target.card
  apply Finset.card_bij (fun x _ => e.symm x)
  · intro x hx
    rw [Finset.mem_filter] at hx ⊢
    let c := e.symm x
    have hentry : e c = x := e.apply_symm_apply x
    have hentry' : T.toAuxiliaryObject.1 c = x := by
      change e c = x
      exact hentry
    refine ⟨Finset.mem_univ _, ?_, ?_⟩
    · rw [← RepresentationTheory.AuxiliaryPartitionCardinality.auxiliaryFamily.entry_eq_auxiliary_nat_value T c, hentry']
      exact hx.2.1
    · rw [← RepresentationTheory.AuxiliaryPartitionIndexMaps.auxiliary_nat_value_equiv_symm_eq_fst c, ← RepresentationTheory.AuxiliaryPartitionIndexMaps.auxiliary_map_apply_eq_equiv_symm
        T.toAuxiliaryObject c, hentry']
      exact hx.2.2
  · intro x₁ hx₁ x₂ hx₂ heq
    exact e.symm.injective heq
  · intro c hc
    refine ⟨e c, ?_, e.symm_apply_apply c⟩
    rw [Finset.mem_filter] at hc ⊢
    refine ⟨Finset.mem_univ _, ?_, ?_⟩
    · change RepresentationTheory.SymmetricGroup.PartitionAuxiliaryConstructions.flatIndexRow (RepresentationTheory.SymmetricGroup.PartitionAuxiliaryConstructions.auxiliaryPartitionNatList mu) (T.toAuxiliaryObject.1 c).val < a
      rw [RepresentationTheory.AuxiliaryPartitionCardinality.auxiliaryFamily.entry_eq_auxiliary_nat_value T c]
      exact hc.2.1
    · change RepresentationTheory.SymmetricGroup.PartitionAuxiliaryConstructions.flatIndexRow (RepresentationTheory.SymmetricGroup.PartitionAuxiliaryConstructions.auxiliaryPartitionNatList nu)
        (RepresentationTheory.Combinatorics.PartitionPermutation.associatedPermutation n nu T.toAuxiliaryObject (T.toAuxiliaryObject.1 c)).val < i
      rw [RepresentationTheory.AuxiliaryPartitionIndexMaps.auxiliary_map_apply_eq_equiv_symm T.toAuxiliaryObject c,
        RepresentationTheory.AuxiliaryPartitionIndexMaps.auxiliary_nat_value_equiv_symm_eq_fst c]
      exact hc.2.2

end

end RepresentationTheory.AuxiliaryPartitionPermutationAverages
