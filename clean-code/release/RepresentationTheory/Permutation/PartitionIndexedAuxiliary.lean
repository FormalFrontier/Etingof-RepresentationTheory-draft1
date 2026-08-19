/-
Copyright (c) 2026 mathlib-initiative. All rights reserved.
Released under Apache 2.0 license as described in the file LICENCE.
Authors: mathlib-initiative
-/

import Mathlib
import RepresentationTheory.SymmetricGroup.PartitionAuxiliaryConstructions
import RepresentationTheory.Combinatorics.PartitionPermutation
import RepresentationTheory.PartitionAuxiliary








































namespace RepresentationTheory.Permutation.PartitionIndexedAuxiliary

noncomputable section

variable {n : ℕ} {la : Nat.Partition n}







/-- A setoid on permutations of `Fin n`, indexed by a partition. -/
def permutationSetoid (n : ℕ) (la : Nat.Partition n) :
    Setoid (Equiv.Perm (Fin n)) where
  r σ₁ σ₂ := σ₁ * σ₂⁻¹ ∈ RepresentationTheory.SymmetricGroup.PartitionAuxiliaryConstructions.auxiliaryPartitionPermutationSubgroupB n la
  iseqv := {
    refl := fun σ => by
      show σ * σ⁻¹ ∈ RepresentationTheory.SymmetricGroup.PartitionAuxiliaryConstructions.auxiliaryPartitionPermutationSubgroupB n la
      rw [mul_inv_cancel]
      exact (RepresentationTheory.SymmetricGroup.PartitionAuxiliaryConstructions.auxiliaryPartitionPermutationSubgroupB n la).one_mem
    symm := fun {σ₁ σ₂} h => by
      show σ₂ * σ₁⁻¹ ∈ RepresentationTheory.SymmetricGroup.PartitionAuxiliaryConstructions.auxiliaryPartitionPermutationSubgroupB n la
      have : σ₂ * σ₁⁻¹ = (σ₁ * σ₂⁻¹)⁻¹ := by
        rw [mul_inv_rev, inv_inv]
      rw [this]
      exact (RepresentationTheory.SymmetricGroup.PartitionAuxiliaryConstructions.auxiliaryPartitionPermutationSubgroupB n la).inv_mem h
    trans := fun {σ₁ σ₂ σ₃} h₁₂ h₂₃ => by
      show σ₁ * σ₃⁻¹ ∈ RepresentationTheory.SymmetricGroup.PartitionAuxiliaryConstructions.auxiliaryPartitionPermutationSubgroupB n la
      have key : σ₁ * σ₃⁻¹ = (σ₁ * σ₂⁻¹) * (σ₂ * σ₃⁻¹) := by
        group
      rw [key]
      exact (RepresentationTheory.SymmetricGroup.PartitionAuxiliaryConstructions.auxiliaryPartitionPermutationSubgroupB n la).mul_mem h₁₂ h₂₃
  }



/-- An auxiliary type parameterized by a natural number and a partition of it. -/
def partitionIndexedAuxiliaryType (n : ℕ) (la : Nat.Partition n) :=
  Quotient (permutationSetoid n la)

/-- Supplies a finite-type instance for the partition-indexed auxiliary type. -/
noncomputable instance partitionIndexedAuxiliaryTypeFintype : Fintype (partitionIndexedAuxiliaryType n la) := by
  haveI : DecidableRel (permutationSetoid n la).r := Classical.decRel _
  unfold partitionIndexedAuxiliaryType
  exact Quotient.fintype (permutationSetoid n la)


/-- Maps a permutation to the partition-indexed auxiliary type. -/
def permutationToAuxiliaryType (n : ℕ) (la : Nat.Partition n) (σ : Equiv.Perm (Fin n)) :
    partitionIndexedAuxiliaryType n la :=
  Quotient.mk (permutationSetoid n la) σ


/-- The displayed values for two permutations are equal exactly when the product of the first with the inverse of the second belongs to the indicated collection. -/
theorem permutationToAuxiliaryType_eq_iff_mul_inv_mem (σ₁ σ₂ : Equiv.Perm (Fin n)) :
    permutationToAuxiliaryType n la σ₁ = permutationToAuxiliaryType n la σ₂ ↔ σ₁ * σ₂⁻¹ ∈ RepresentationTheory.SymmetricGroup.PartitionAuxiliaryConstructions.auxiliaryPartitionPermutationSubgroupB n la :=
  Quotient.eq (r := permutationSetoid n la)



/-- The displayed values for two permutations are equal exactly when the indicated coordinate values agree at every finite index. -/
theorem permutationToAuxiliaryType_eq_iff_coordinate_eq (σ₁ σ₂ : Equiv.Perm (Fin n)) :
    permutationToAuxiliaryType n la σ₁ = permutationToAuxiliaryType n la σ₂ ↔
      ∀ k : Fin n, RepresentationTheory.SymmetricGroup.PartitionAuxiliaryConstructions.flatIndexRow (RepresentationTheory.SymmetricGroup.PartitionAuxiliaryConstructions.auxiliaryPartitionNatList la) (σ₁ k).val =
                    RepresentationTheory.SymmetricGroup.PartitionAuxiliaryConstructions.flatIndexRow (RepresentationTheory.SymmetricGroup.PartitionAuxiliaryConstructions.auxiliaryPartitionNatList la) (σ₂ k).val := by
  rw [permutationToAuxiliaryType_eq_iff_mul_inv_mem]
  constructor
  · intro h k
    have hmem := h (σ₂ k)
    simp only [Equiv.Perm.coe_mul, Function.comp_apply,
               Equiv.Perm.coe_inv, Equiv.symm_apply_apply] at hmem
    exact hmem
  · intro h k
    show RepresentationTheory.SymmetricGroup.PartitionAuxiliaryConstructions.flatIndexRow (RepresentationTheory.SymmetricGroup.PartitionAuxiliaryConstructions.auxiliaryPartitionNatList la) ((σ₁ * σ₂⁻¹) k).val = RepresentationTheory.SymmetricGroup.PartitionAuxiliaryConstructions.flatIndexRow (RepresentationTheory.SymmetricGroup.PartitionAuxiliaryConstructions.auxiliaryPartitionNatList la) k.val
    simp only [Equiv.Perm.coe_mul, Function.comp_apply]
    rw [h (σ₂⁻¹ k)]
    congr 1
    exact congrArg Fin.val (Equiv.apply_symm_apply σ₂ k)




/-- Assigns a natural number to an auxiliary object and a finite index. -/
def auxiliaryObjectIndex (n : ℕ) (la : Nat.Partition n) (T : RepresentationTheory.SymmetricGroup.PartitionAuxiliaryConstructions.AuxiliaryPartitionSource n la)
    (k : Fin n) : ℕ :=
  RepresentationTheory.SymmetricGroup.PartitionAuxiliaryConstructions.flatIndexRow (RepresentationTheory.SymmetricGroup.PartitionAuxiliaryConstructions.auxiliaryPartitionNatList la) (RepresentationTheory.Combinatorics.PartitionPermutation.associatedPermutation n la T k).val


/-- Maps an element of an auxiliary type to the partition-indexed auxiliary type. -/
def objectToAuxiliaryType (n : ℕ) (la : Nat.Partition n) (T : RepresentationTheory.SymmetricGroup.PartitionAuxiliaryConstructions.AuxiliaryPartitionSource n la) :
    partitionIndexedAuxiliaryType n la :=
  permutationToAuxiliaryType n la (RepresentationTheory.Combinatorics.PartitionPermutation.associatedPermutation n la T)




private theorem syt_entry_lt_of_col_lt (T : RepresentationTheory.SymmetricGroup.PartitionAuxiliaryConstructions.AuxiliaryPartitionSource n la) (k₁ k₂ : Fin n)
    (hrow : RepresentationTheory.SymmetricGroup.PartitionAuxiliaryConstructions.flatIndexRow (RepresentationTheory.SymmetricGroup.PartitionAuxiliaryConstructions.auxiliaryPartitionNatList la) (RepresentationTheory.Combinatorics.PartitionPermutation.associatedPermutation n la T k₁).val =
            RepresentationTheory.SymmetricGroup.PartitionAuxiliaryConstructions.flatIndexRow (RepresentationTheory.SymmetricGroup.PartitionAuxiliaryConstructions.auxiliaryPartitionNatList la) (RepresentationTheory.Combinatorics.PartitionPermutation.associatedPermutation n la T k₂).val)
    (hcol : RepresentationTheory.SymmetricGroup.PartitionAuxiliaryConstructions.flatIndexColumn (RepresentationTheory.SymmetricGroup.PartitionAuxiliaryConstructions.auxiliaryPartitionNatList la) (RepresentationTheory.Combinatorics.PartitionPermutation.associatedPermutation n la T k₁).val <
            RepresentationTheory.SymmetricGroup.PartitionAuxiliaryConstructions.flatIndexColumn (RepresentationTheory.SymmetricGroup.PartitionAuxiliaryConstructions.auxiliaryPartitionNatList la) (RepresentationTheory.Combinatorics.PartitionPermutation.associatedPermutation n la T k₂).val) :
    k₁ < k₂ := by
  set e := Equiv.ofBijective T.val T.prop.1

  have hcell : ∀ k : Fin n, e.symm k = (RepresentationTheory.Combinatorics.PartitionPermutation.finEquivPartitionIndex n la) (RepresentationTheory.Combinatorics.PartitionPermutation.associatedPermutation n la T k) := by
    intro k
    simp only [e, RepresentationTheory.Combinatorics.PartitionPermutation.associatedPermutation, Equiv.trans_apply, Equiv.apply_symm_apply]

  have hrow' : (e.symm k₁).val.1 = (e.symm k₂).val.1 := by
    rw [hcell k₁, hcell k₂]; exact hrow

  have hcol' : (e.symm k₁).val.2 < (e.symm k₂).val.2 := by
    rw [hcell k₁, hcell k₂]; exact hcol

  have h := T.prop.2.1 (e.symm k₁) (e.symm k₂) hrow' hcol'

  rwa [show T.val (e.symm k₁) = k₁ from e.apply_symm_apply k₁,
       show T.val (e.symm k₂) = k₂ from e.apply_symm_apply k₂] at h









/-- The displayed map from the auxiliary object type is injective. -/
theorem objectToAuxiliaryType_injective (n : ℕ) (la : Nat.Partition n) :
    Function.Injective (objectToAuxiliaryType n la) := by
  intro T₁ T₂ h
  rw [objectToAuxiliaryType, objectToAuxiliaryType, permutationToAuxiliaryType_eq_iff_coordinate_eq] at h
  apply RepresentationTheory.Combinatorics.PartitionPermutation.associatedPermutation_injective n la

  suffices ∀ (m : ℕ) (k : Fin n), k.val = m → RepresentationTheory.Combinatorics.PartitionPermutation.associatedPermutation n la T₁ k = RepresentationTheory.Combinatorics.PartitionPermutation.associatedPermutation n la T₂ k by
    exact Equiv.ext (fun k => this k.val k rfl)
  intro m
  induction m using Nat.strongRecOn with
  | ind m ih =>
    intro k hkm
    have hsum : (RepresentationTheory.SymmetricGroup.PartitionAuxiliaryConstructions.auxiliaryPartitionNatList la).sum = n := RepresentationTheory.Partition.YoungDiagram.sum_sortedParts n la

    suffices hcol : RepresentationTheory.SymmetricGroup.PartitionAuxiliaryConstructions.flatIndexColumn (RepresentationTheory.SymmetricGroup.PartitionAuxiliaryConstructions.auxiliaryPartitionNatList la) (RepresentationTheory.Combinatorics.PartitionPermutation.associatedPermutation n la T₁ k).val =
                    RepresentationTheory.SymmetricGroup.PartitionAuxiliaryConstructions.flatIndexColumn (RepresentationTheory.SymmetricGroup.PartitionAuxiliaryConstructions.auxiliaryPartitionNatList la) (RepresentationTheory.Combinatorics.PartitionPermutation.associatedPermutation n la T₂ k).val by
      exact Fin.ext (RepresentationTheory.SymmetricGroup.PartitionAuxiliaryConstructions.eq_of_flatIndexRow_eq_and_column_eq (RepresentationTheory.SymmetricGroup.PartitionAuxiliaryConstructions.auxiliaryPartitionNatList la)
        (RepresentationTheory.Combinatorics.PartitionPermutation.associatedPermutation n la T₁ k).val (RepresentationTheory.Combinatorics.PartitionPermutation.associatedPermutation n la T₂ k).val
        (by omega) (by omega) (h k) hcol)

    by_contra hcol_ne
    rcases lt_or_gt_of_ne hcol_ne with hlt | hlt
    ·

      set k' := (RepresentationTheory.Combinatorics.PartitionPermutation.associatedPermutation n la T₂).symm (RepresentationTheory.Combinatorics.PartitionPermutation.associatedPermutation n la T₁ k)
      have hk'_eq : RepresentationTheory.Combinatorics.PartitionPermutation.associatedPermutation n la T₂ k' = RepresentationTheory.Combinatorics.PartitionPermutation.associatedPermutation n la T₁ k :=
        (RepresentationTheory.Combinatorics.PartitionPermutation.associatedPermutation n la T₂).apply_symm_apply (RepresentationTheory.Combinatorics.PartitionPermutation.associatedPermutation n la T₁ k)

      have hk'_lt : k' < k :=
        syt_entry_lt_of_col_lt T₂ k' k
          (by simp only [hk'_eq]; exact h k)
          (by simp only [hk'_eq]; exact hlt)

      have hih := ih k'.val (by omega) k' rfl

      exact absurd ((RepresentationTheory.Combinatorics.PartitionPermutation.associatedPermutation n la T₁).injective (by rw [hih, hk'_eq])) (ne_of_lt hk'_lt)
    ·
      set k' := (RepresentationTheory.Combinatorics.PartitionPermutation.associatedPermutation n la T₁).symm (RepresentationTheory.Combinatorics.PartitionPermutation.associatedPermutation n la T₂ k)
      have hk'_eq : RepresentationTheory.Combinatorics.PartitionPermutation.associatedPermutation n la T₁ k' = RepresentationTheory.Combinatorics.PartitionPermutation.associatedPermutation n la T₂ k :=
        (RepresentationTheory.Combinatorics.PartitionPermutation.associatedPermutation n la T₁).apply_symm_apply (RepresentationTheory.Combinatorics.PartitionPermutation.associatedPermutation n la T₂ k)
      have hk'_lt : k' < k :=
        syt_entry_lt_of_col_lt T₁ k' k
          (by simp only [hk'_eq]; exact (h k).symm)
          (by simp only [hk'_eq]; exact hlt)
      have hih := ih k'.val (by omega) k' rfl
      exact absurd ((RepresentationTheory.Combinatorics.PartitionPermutation.associatedPermutation n la T₂).injective (by rw [← hih, hk'_eq])) (ne_of_lt hk'_lt)






/-- A permutation belonging to each of two indicated collections is the identity. -/
theorem eq_one_of_mem_two_auxiliarySets (n : ℕ) (la : Nat.Partition n)
    (σ : Equiv.Perm (Fin n)) (hrow : σ ∈ RepresentationTheory.SymmetricGroup.PartitionAuxiliaryConstructions.auxiliaryPartitionPermutationSubgroupB n la)
    (hcol : σ ∈ RepresentationTheory.SymmetricGroup.PartitionAuxiliaryConstructions.auxiliaryPartitionPermutationSubgroupA n la) : σ = 1 := by
  ext k
  simp only [Equiv.Perm.one_apply]
  have hr : RepresentationTheory.SymmetricGroup.PartitionAuxiliaryConstructions.flatIndexRow (RepresentationTheory.SymmetricGroup.PartitionAuxiliaryConstructions.auxiliaryPartitionNatList la) (σ k).val = RepresentationTheory.SymmetricGroup.PartitionAuxiliaryConstructions.flatIndexRow (RepresentationTheory.SymmetricGroup.PartitionAuxiliaryConstructions.auxiliaryPartitionNatList la) k.val := hrow k
  have hc : RepresentationTheory.SymmetricGroup.PartitionAuxiliaryConstructions.flatIndexColumn (RepresentationTheory.SymmetricGroup.PartitionAuxiliaryConstructions.auxiliaryPartitionNatList la) (σ k).val = RepresentationTheory.SymmetricGroup.PartitionAuxiliaryConstructions.flatIndexColumn (RepresentationTheory.SymmetricGroup.PartitionAuxiliaryConstructions.auxiliaryPartitionNatList la) k.val := hcol k
  have hsum : (RepresentationTheory.SymmetricGroup.PartitionAuxiliaryConstructions.auxiliaryPartitionNatList la).sum = n := by
    have h := Multiset.sort_eq la.parts (· ≥ ·)
    have : ((RepresentationTheory.SymmetricGroup.PartitionAuxiliaryConstructions.auxiliaryPartitionNatList la) : Multiset ℕ).sum = la.parts.sum := congrArg Multiset.sum h
    rw [Multiset.sum_coe] at this; rw [this, la.parts_sum]
  have hk : k.val < (RepresentationTheory.SymmetricGroup.PartitionAuxiliaryConstructions.auxiliaryPartitionNatList la).sum := by omega
  have hsk : (σ k).val < (RepresentationTheory.SymmetricGroup.PartitionAuxiliaryConstructions.auxiliaryPartitionNatList la).sum := by omega
  exact RepresentationTheory.SymmetricGroup.PartitionAuxiliaryConstructions.eq_of_flatIndexRow_eq_and_column_eq (RepresentationTheory.SymmetricGroup.PartitionAuxiliaryConstructions.auxiliaryPartitionNatList la) (σ k).val k.val hsk hk hr hc













/-- Associates a subgroup of permutations of `Fin n` with each member of an auxiliary type. -/
def associatedSubgroup (n : ℕ) (la : Nat.Partition n)
    (T : RepresentationTheory.SymmetricGroup.PartitionAuxiliaryConstructions.AuxiliaryPartitionSource n la) : Subgroup (Equiv.Perm (Fin n)) :=
  (RepresentationTheory.SymmetricGroup.PartitionAuxiliaryConstructions.auxiliaryPartitionPermutationSubgroupA n la).map (MulAut.conj (RepresentationTheory.Combinatorics.PartitionPermutation.associatedPermutation n la T)⁻¹).toMonoidHom

/-- Membership in the subgroup associated with an auxiliary object is characterized by a conjugate of a member of the displayed collection. -/
theorem mem_associatedSubgroup_iff_exists_conjugate (T : RepresentationTheory.SymmetricGroup.PartitionAuxiliaryConstructions.AuxiliaryPartitionSource n la)
    (π : Equiv.Perm (Fin n)) :
    π ∈ associatedSubgroup n la T ↔
      ∃ q ∈ RepresentationTheory.SymmetricGroup.PartitionAuxiliaryConstructions.auxiliaryPartitionPermutationSubgroupA n la,
        π = (RepresentationTheory.Combinatorics.PartitionPermutation.associatedPermutation n la T)⁻¹ * q * RepresentationTheory.Combinatorics.PartitionPermutation.associatedPermutation n la T := by
  simp only [associatedSubgroup, Subgroup.mem_map, MulAut.conj_apply,
             MulEquiv.coe_toMonoidHom, inv_inv]
  constructor
  · rintro ⟨q, hq, rfl⟩; exact ⟨q, hq, rfl⟩
  · rintro ⟨q, hq, rfl⟩; exact ⟨q, hq, rfl⟩



/-- Conjugating a member of the associated subgroup by the displayed permutation expression gives a member of the indicated collection. -/
theorem mem_auxiliarySet_of_mem_associatedSubgroup (T : RepresentationTheory.SymmetricGroup.PartitionAuxiliaryConstructions.AuxiliaryPartitionSource n la)
    (π : Equiv.Perm (Fin n)) (hπ : π ∈ associatedSubgroup n la T) :
    RepresentationTheory.Combinatorics.PartitionPermutation.associatedPermutation n la T * π * (RepresentationTheory.Combinatorics.PartitionPermutation.associatedPermutation n la T)⁻¹ ∈ RepresentationTheory.SymmetricGroup.PartitionAuxiliaryConstructions.auxiliaryPartitionPermutationSubgroupA n la := by
  rw [mem_associatedSubgroup_iff_exists_conjugate] at hπ
  obtain ⟨q, hq, rfl⟩ := hπ
  group
  exact hq





/-- The displayed value of the permutation expression associated with an auxiliary object equals that object's displayed auxiliary value. -/
theorem permutationToAuxiliaryType_objectPermutation (T : RepresentationTheory.SymmetricGroup.PartitionAuxiliaryConstructions.AuxiliaryPartitionSource n la) :
    permutationToAuxiliaryType n la (1⁻¹ * RepresentationTheory.Combinatorics.PartitionPermutation.associatedPermutation n la T) = objectToAuxiliaryType n la T := by
  simp [objectToAuxiliaryType]





/-- For an auxiliary object and a nonidentity permutation in the indicated collection, the displayed two values of the partition-indexed auxiliary type are unequal. -/
theorem permutationToAuxiliaryType_inv_mul_ne_objectValue (T : RepresentationTheory.SymmetricGroup.PartitionAuxiliaryConstructions.AuxiliaryPartitionSource n la)
    (q : Equiv.Perm (Fin n)) (hq : q ∈ RepresentationTheory.SymmetricGroup.PartitionAuxiliaryConstructions.auxiliaryPartitionPermutationSubgroupA n la) (hne : q ≠ 1) :
    permutationToAuxiliaryType n la (q⁻¹ * RepresentationTheory.Combinatorics.PartitionPermutation.associatedPermutation n la T) ≠ objectToAuxiliaryType n la T := by
  rw [Ne, objectToAuxiliaryType, permutationToAuxiliaryType_eq_iff_mul_inv_mem]
  intro hmem

  simp only [mul_assoc, mul_inv_cancel, mul_one] at hmem
  have : q⁻¹ = 1 := eq_one_of_mem_two_auxiliarySets n la q⁻¹ hmem
    ((RepresentationTheory.SymmetricGroup.PartitionAuxiliaryConstructions.auxiliaryPartitionPermutationSubgroupA n la).inv_mem hq)
  exact hne (inv_eq_one.mp this)







/-- A natural-valued function of a permutation, a finite index, and an additional natural-number argument, indexed by a partition. -/
def permutationToIndexedNatFunction (la : Nat.Partition n) (σ : Equiv.Perm (Fin n))
    (k : Fin n) (i : ℕ) : ℕ :=
  (Finset.univ.filter fun e : Fin n =>
    e ≤ k ∧ RepresentationTheory.SymmetricGroup.PartitionAuxiliaryConstructions.flatIndexRow (RepresentationTheory.SymmetricGroup.PartitionAuxiliaryConstructions.auxiliaryPartitionNatList la) (σ e).val < i).card



/-- Permutations with equal displayed values in the partition-indexed auxiliary type have equal values of the indicated natural-valued function. -/
theorem permutationToIndexedNatFunction_eq_of_auxiliaryValue_eq (σ₁ σ₂ : Equiv.Perm (Fin n))
    (h : permutationToAuxiliaryType n la σ₁ = permutationToAuxiliaryType n la σ₂) (k : Fin n) (i : ℕ) :
    permutationToIndexedNatFunction la σ₁ k i = permutationToIndexedNatFunction la σ₂ k i := by
  rw [permutationToAuxiliaryType_eq_iff_coordinate_eq] at h
  simp only [permutationToIndexedNatFunction]
  congr 1
  ext e
  simp only [Finset.mem_filter, Finset.mem_univ, true_and]
  constructor <;> intro ⟨hle, hrow⟩
  · exact ⟨hle, (h e) ▸ hrow⟩
  · exact ⟨hle, (h e) ▸ hrow⟩




/-- A binary relation on permutations of `Fin n`, indexed by a partition. -/
def permutationRel (la : Nat.Partition n) (σ₁ σ₂ : Equiv.Perm (Fin n)) : Prop :=
  ∀ k : Fin n, ∀ i : ℕ,
    permutationToIndexedNatFunction la σ₂ k i ≤ permutationToIndexedNatFunction la σ₁ k i


/-- A second binary relation on permutations of `Fin n`, indexed by a partition. -/
def permutationRelAux (la : Nat.Partition n) (σ₁ σ₂ : Equiv.Perm (Fin n)) : Prop :=
  permutationRel la σ₁ σ₂ ∧ permutationToAuxiliaryType n la σ₁ ≠ permutationToAuxiliaryType n la σ₂


/-- The permutation relation holds from every permutation to itself. -/
theorem permutationRel_refl (σ : Equiv.Perm (Fin n)) :
    permutationRel la σ σ :=
  fun _ _ => le_refl _


/-- The permutation relation is transitive on permutations. -/
theorem permutationRel_trans {σ₁ σ₂ σ₃ : Equiv.Perm (Fin n)}
    (h₁₂ : permutationRel la σ₁ σ₂) (h₂₃ : permutationRel la σ₂ σ₃) :
    permutationRel la σ₁ σ₃ :=
  fun k i => le_trans (h₂₃ k i) (h₁₂ k i)



/-- The permutation relation is preserved when either argument is replaced by a permutation with the same displayed auxiliary value. -/
theorem permutationRel_congr {σ₁ σ₁' σ₂ σ₂' : Equiv.Perm (Fin n)}
    (h₁ : permutationToAuxiliaryType n la σ₁ = permutationToAuxiliaryType n la σ₁')
    (h₂ : permutationToAuxiliaryType n la σ₂ = permutationToAuxiliaryType n la σ₂')
    (hdom : permutationRel la σ₁ σ₂) :
    permutationRel la σ₁' σ₂' := by
  intro k i
  rw [← permutationToIndexedNatFunction_eq_of_auxiliaryValue_eq σ₂ σ₂' h₂,
      ← permutationToIndexedNatFunction_eq_of_auxiliaryValue_eq σ₁ σ₁' h₁]
  exact hdom k i




/-- In a two-step chain of the displayed relation, equality of the first and final auxiliary values implies equality of the middle and final values. -/
theorem middle_auxiliaryValue_eq_of_rel_chain {σ₁ σ₂ σ₃ : Equiv.Perm (Fin n)}
    (h₁₂ : permutationRel la σ₁ σ₂) (h₂₃ : permutationRel la σ₂ σ₃)
    (heq : permutationToAuxiliaryType n la σ₁ = permutationToAuxiliaryType n la σ₃) :
    permutationToAuxiliaryType n la σ₂ = permutationToAuxiliaryType n la σ₃ := by

  have hcount : ∀ k : Fin n, ∀ i : ℕ,
      permutationToIndexedNatFunction la σ₂ k i = permutationToIndexedNatFunction la σ₃ k i := by
    intro k i
    have h1 := h₁₂ k i
    have h2 := h₂₃ k i
    have h3 := permutationToIndexedNatFunction_eq_of_auxiliaryValue_eq σ₁ σ₃ heq k i
    omega

  rw [permutationToAuxiliaryType_eq_iff_coordinate_eq]
  intro k
  by_contra hne

  have hlt : RepresentationTheory.SymmetricGroup.PartitionAuxiliaryConstructions.flatIndexRow (RepresentationTheory.SymmetricGroup.PartitionAuxiliaryConstructions.auxiliaryPartitionNatList la) (σ₂ k).val <
      RepresentationTheory.SymmetricGroup.PartitionAuxiliaryConstructions.flatIndexRow (RepresentationTheory.SymmetricGroup.PartitionAuxiliaryConstructions.auxiliaryPartitionNatList la) (σ₃ k).val := by
    rcases Nat.lt_or_ge (RepresentationTheory.SymmetricGroup.PartitionAuxiliaryConstructions.flatIndexRow (RepresentationTheory.SymmetricGroup.PartitionAuxiliaryConstructions.auxiliaryPartitionNatList la) (σ₂ k).val)
        (RepresentationTheory.SymmetricGroup.PartitionAuxiliaryConstructions.flatIndexRow (RepresentationTheory.SymmetricGroup.PartitionAuxiliaryConstructions.auxiliaryPartitionNatList la) (σ₃ k).val) with h | h
    · exact h
    · rcases Nat.eq_or_lt_of_le h with heq' | hlt'
      · exact absurd heq'.symm hne
      ·



        exfalso


        set r' := RepresentationTheory.SymmetricGroup.PartitionAuxiliaryConstructions.flatIndexRow (RepresentationTheory.SymmetricGroup.PartitionAuxiliaryConstructions.auxiliaryPartitionNatList la) (σ₂ k).val
        rcases k with ⟨_ | m', hk'⟩
        ·
          have : permutationToIndexedNatFunction la σ₃ ⟨0, hk'⟩ r' = 1 := by
            simp only [permutationToIndexedNatFunction]
            rw [show (Finset.univ.filter fun e : Fin n =>
                e ≤ ⟨0, hk'⟩ ∧ RepresentationTheory.SymmetricGroup.PartitionAuxiliaryConstructions.flatIndexRow (RepresentationTheory.SymmetricGroup.PartitionAuxiliaryConstructions.auxiliaryPartitionNatList la) (σ₃ e).val < r') =
              {⟨0, hk'⟩} from by
              ext ⟨e, he⟩
              simp only [Finset.mem_filter, Finset.mem_univ, true_and,
                Finset.mem_singleton, Fin.mk_le_mk, Fin.ext_iff]
              constructor
              · intro ⟨hle, _⟩; omega
              · intro heq'; subst heq'; exact ⟨le_refl _, hlt'⟩]
            exact Finset.card_singleton _
          have : permutationToIndexedNatFunction la σ₂ ⟨0, hk'⟩ r' = 0 := by
            simp only [permutationToIndexedNatFunction]
            apply Finset.card_eq_zero.mpr
            rw [Finset.filter_eq_empty_iff]
            intro ⟨e, he⟩ _
            simp only [not_and, Fin.mk_le_mk]
            intro hle hrow
            have : e = 0 := by omega
            subst this; exact Nat.lt_irrefl _ hrow
          linarith [hcount ⟨0, hk'⟩ r']
        ·
          have hm' : m' < n := by omega
          have h2d : permutationToIndexedNatFunction la σ₃ ⟨m' + 1, hk'⟩ r' =
              permutationToIndexedNatFunction la σ₃ ⟨m', hm'⟩ r' + 1 := by
            simp only [permutationToIndexedNatFunction]
            rw [show (Finset.univ.filter fun e : Fin n =>
                e ≤ ⟨m' + 1, hk'⟩ ∧ RepresentationTheory.SymmetricGroup.PartitionAuxiliaryConstructions.flatIndexRow (RepresentationTheory.SymmetricGroup.PartitionAuxiliaryConstructions.auxiliaryPartitionNatList la) (σ₃ e).val < r') =
              (Finset.univ.filter fun e : Fin n =>
                e ≤ ⟨m', hm'⟩ ∧ RepresentationTheory.SymmetricGroup.PartitionAuxiliaryConstructions.flatIndexRow (RepresentationTheory.SymmetricGroup.PartitionAuxiliaryConstructions.auxiliaryPartitionNatList la) (σ₃ e).val < r') ∪
              {⟨m' + 1, hk'⟩} from by
              ext ⟨e, he⟩
              simp only [Finset.mem_filter, Finset.mem_univ, true_and,
                Finset.mem_union, Finset.mem_singleton, Fin.mk_le_mk, Fin.ext_iff]
              constructor
              · intro ⟨hle, hrow⟩
                by_cases heq' : e = m' + 1
                · right; exact heq'
                · left; exact ⟨by omega, hrow⟩
              · intro hh
                rcases hh with ⟨hle, hrow⟩ | heq'
                · exact ⟨by omega, hrow⟩
                · subst heq'; exact ⟨le_refl _, hlt'⟩]
            rw [Finset.card_union_of_disjoint (by
              rw [Finset.disjoint_left]
              intro ⟨e, he⟩ hmem hsing
              simp only [Finset.mem_filter, Finset.mem_univ, true_and,
                Fin.mk_le_mk] at hmem
              simp only [Finset.mem_singleton, Fin.ext_iff] at hsing
              omega)]
            simp
          have h3d : permutationToIndexedNatFunction la σ₂ ⟨m' + 1, hk'⟩ r' =
              permutationToIndexedNatFunction la σ₂ ⟨m', hm'⟩ r' := by
            simp only [permutationToIndexedNatFunction]
            congr 1; ext ⟨e, he⟩
            simp only [Finset.mem_filter, Finset.mem_univ, true_and, Fin.mk_le_mk]
            constructor
            · intro ⟨hle, hrow⟩
              constructor
              · by_contra hgt; push Not at hgt
                have : e = m' + 1 := by omega
                subst this; exact Nat.lt_irrefl _ hrow
              · exact hrow
            · intro ⟨hle, hrow⟩; exact ⟨by omega, hrow⟩
          linarith [hcount ⟨m' + 1, hk'⟩ r', hcount ⟨m', hm'⟩ r']

  set r := RepresentationTheory.SymmetricGroup.PartitionAuxiliaryConstructions.flatIndexRow (RepresentationTheory.SymmetricGroup.PartitionAuxiliaryConstructions.auxiliaryPartitionNatList la) (σ₃ k).val
  rcases k with ⟨_ | m, hk⟩
  ·
    have h2 : permutationToIndexedNatFunction la σ₂ ⟨0, hk⟩ r = 1 := by
      simp only [permutationToIndexedNatFunction]
      rw [show (Finset.univ.filter fun e : Fin n =>
          e ≤ ⟨0, hk⟩ ∧ RepresentationTheory.SymmetricGroup.PartitionAuxiliaryConstructions.flatIndexRow (RepresentationTheory.SymmetricGroup.PartitionAuxiliaryConstructions.auxiliaryPartitionNatList la) (σ₂ e).val < r) =
        {⟨0, hk⟩} from by
        ext ⟨e, he⟩
        simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_singleton,
          Fin.mk_le_mk, Fin.ext_iff]
        constructor
        · intro ⟨hle, _⟩; omega
        · intro heq; subst heq; exact ⟨le_refl _, hlt⟩]
      exact Finset.card_singleton _
    have h3 : permutationToIndexedNatFunction la σ₃ ⟨0, hk⟩ r = 0 := by
      simp only [permutationToIndexedNatFunction]
      apply Finset.card_eq_zero.mpr
      rw [Finset.filter_eq_empty_iff]
      intro ⟨e, he⟩ _
      simp only [not_and, Fin.mk_le_mk]
      intro hle hrow
      have : e = 0 := by omega
      subst this; exact Nat.lt_irrefl _ hrow
    linarith [hcount ⟨0, hk⟩ r]
  ·
    have hm : m < n := by omega

    have h2_diff : permutationToIndexedNatFunction la σ₂ ⟨m + 1, hk⟩ r =
        permutationToIndexedNatFunction la σ₂ ⟨m, hm⟩ r + 1 := by
      simp only [permutationToIndexedNatFunction]
      rw [show (Finset.univ.filter fun e : Fin n =>
          e ≤ ⟨m + 1, hk⟩ ∧ RepresentationTheory.SymmetricGroup.PartitionAuxiliaryConstructions.flatIndexRow (RepresentationTheory.SymmetricGroup.PartitionAuxiliaryConstructions.auxiliaryPartitionNatList la) (σ₂ e).val < r) =
        (Finset.univ.filter fun e : Fin n =>
          e ≤ ⟨m, hm⟩ ∧ RepresentationTheory.SymmetricGroup.PartitionAuxiliaryConstructions.flatIndexRow (RepresentationTheory.SymmetricGroup.PartitionAuxiliaryConstructions.auxiliaryPartitionNatList la) (σ₂ e).val < r) ∪ {⟨m + 1, hk⟩} from by
        ext ⟨e, he⟩
        simp only [Finset.mem_filter, Finset.mem_univ, true_and,
          Finset.mem_union, Finset.mem_singleton, Fin.mk_le_mk, Fin.ext_iff]
        constructor
        · intro ⟨hle, hrow⟩
          by_cases heq : e = m + 1
          · right; exact heq
          · left; exact ⟨by omega, hrow⟩
        · intro h
          rcases h with ⟨hle, hrow⟩ | heq
          · exact ⟨by omega, hrow⟩
          · subst heq; exact ⟨le_refl _, hlt⟩]
      rw [Finset.card_union_of_disjoint (by
        rw [Finset.disjoint_left]
        intro ⟨e, he⟩ hmem hsing
        simp only [Finset.mem_filter, Finset.mem_univ, true_and, Fin.mk_le_mk] at hmem
        simp only [Finset.mem_singleton, Fin.ext_iff] at hsing
        omega)]
      simp

    have h3_diff : permutationToIndexedNatFunction la σ₃ ⟨m + 1, hk⟩ r =
        permutationToIndexedNatFunction la σ₃ ⟨m, hm⟩ r := by
      simp only [permutationToIndexedNatFunction]
      congr 1; ext ⟨e, he⟩
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, Fin.mk_le_mk]
      constructor
      · intro ⟨hle, hrow⟩
        constructor
        · by_contra hgt; push Not at hgt
          have : e = m + 1 := by omega
          subst this; exact Nat.lt_irrefl _ hrow
        · exact hrow
      · intro ⟨hle, hrow⟩; exact ⟨by omega, hrow⟩
    linarith [hcount ⟨m + 1, hk⟩ r, hcount ⟨m, hm⟩ r]






/-- Maps each permutation to a natural-valued function on `Fin n`, indexed by a partition. -/
def permutationToNatFunction (la : Nat.Partition n) (σ : Equiv.Perm (Fin n)) :
    Fin n → ℕ :=
  fun k => RepresentationTheory.SymmetricGroup.PartitionAuxiliaryConstructions.flatIndexRow (RepresentationTheory.SymmetricGroup.PartitionAuxiliaryConstructions.auxiliaryPartitionNatList la) (σ k).val


/-- Permutations with equal displayed auxiliary values have equal indicated natural-valued functions. -/
theorem permutationToNatFunction_eq_of_auxiliaryValue_eq (σ₁ σ₂ : Equiv.Perm (Fin n))
    (h : permutationToAuxiliaryType n la σ₁ = permutationToAuxiliaryType n la σ₂) :
    permutationToNatFunction la σ₁ = permutationToNatFunction la σ₂ := by
  rw [permutationToAuxiliaryType_eq_iff_coordinate_eq] at h
  ext k; exact h k


/-- Permutations with equal indicated natural-valued functions have equal displayed auxiliary values. -/
theorem permutationToAuxiliaryType_eq_of_natFunction_eq (σ₁ σ₂ : Equiv.Perm (Fin n))
    (h : permutationToNatFunction la σ₁ = permutationToNatFunction la σ₂) :
    permutationToAuxiliaryType n la σ₁ = permutationToAuxiliaryType n la σ₂ := by
  rw [permutationToAuxiliaryType_eq_iff_coordinate_eq]
  intro k; exact congr_fun h k






private theorem syt_entry_lt_of_row_lt (T : RepresentationTheory.SymmetricGroup.PartitionAuxiliaryConstructions.AuxiliaryPartitionSource n la) (k₁ k₂ : Fin n)
    (hcol : RepresentationTheory.SymmetricGroup.PartitionAuxiliaryConstructions.flatIndexColumn (RepresentationTheory.SymmetricGroup.PartitionAuxiliaryConstructions.auxiliaryPartitionNatList la) (RepresentationTheory.Combinatorics.PartitionPermutation.associatedPermutation n la T k₁).val =
            RepresentationTheory.SymmetricGroup.PartitionAuxiliaryConstructions.flatIndexColumn (RepresentationTheory.SymmetricGroup.PartitionAuxiliaryConstructions.auxiliaryPartitionNatList la) (RepresentationTheory.Combinatorics.PartitionPermutation.associatedPermutation n la T k₂).val)
    (hrow : RepresentationTheory.SymmetricGroup.PartitionAuxiliaryConstructions.flatIndexRow (RepresentationTheory.SymmetricGroup.PartitionAuxiliaryConstructions.auxiliaryPartitionNatList la) (RepresentationTheory.Combinatorics.PartitionPermutation.associatedPermutation n la T k₁).val <
            RepresentationTheory.SymmetricGroup.PartitionAuxiliaryConstructions.flatIndexRow (RepresentationTheory.SymmetricGroup.PartitionAuxiliaryConstructions.auxiliaryPartitionNatList la) (RepresentationTheory.Combinatorics.PartitionPermutation.associatedPermutation n la T k₂).val) :
    k₁ < k₂ := by
  set e := Equiv.ofBijective T.val T.prop.1
  have hcell : ∀ k : Fin n, e.symm k = (RepresentationTheory.Combinatorics.PartitionPermutation.finEquivPartitionIndex n la) (RepresentationTheory.Combinatorics.PartitionPermutation.associatedPermutation n la T k) := by
    intro k
    simp only [e, RepresentationTheory.Combinatorics.PartitionPermutation.associatedPermutation, Equiv.trans_apply, Equiv.apply_symm_apply]

  have hcol' : (e.symm k₁).val.2 = (e.symm k₂).val.2 := by
    rw [hcell k₁, hcell k₂]; exact hcol

  have hrow' : (e.symm k₁).val.1 < (e.symm k₂).val.1 := by
    rw [hcell k₁, hcell k₂]; exact hrow

  have h := T.prop.2.2 (e.symm k₁) (e.symm k₂) hcol' hrow'
  rwa [show T.val (e.symm k₁) = k₁ from e.apply_symm_apply k₁,
       show T.val (e.symm k₂) = k₂ from e.apply_symm_apply k₂] at h






private theorem syt_col_entry_le_of_row_le (T : RepresentationTheory.SymmetricGroup.PartitionAuxiliaryConstructions.AuxiliaryPartitionSource n la)
    (e₁ e₂ : Fin n)
    (hcol : RepresentationTheory.SymmetricGroup.PartitionAuxiliaryConstructions.flatIndexColumn (RepresentationTheory.SymmetricGroup.PartitionAuxiliaryConstructions.auxiliaryPartitionNatList la) (RepresentationTheory.Combinatorics.PartitionPermutation.associatedPermutation n la T e₁).val =
            RepresentationTheory.SymmetricGroup.PartitionAuxiliaryConstructions.flatIndexColumn (RepresentationTheory.SymmetricGroup.PartitionAuxiliaryConstructions.auxiliaryPartitionNatList la) (RepresentationTheory.Combinatorics.PartitionPermutation.associatedPermutation n la T e₂).val)
    (hrow : RepresentationTheory.SymmetricGroup.PartitionAuxiliaryConstructions.flatIndexRow (RepresentationTheory.SymmetricGroup.PartitionAuxiliaryConstructions.auxiliaryPartitionNatList la) (RepresentationTheory.Combinatorics.PartitionPermutation.associatedPermutation n la T e₁).val ≤
            RepresentationTheory.SymmetricGroup.PartitionAuxiliaryConstructions.flatIndexRow (RepresentationTheory.SymmetricGroup.PartitionAuxiliaryConstructions.auxiliaryPartitionNatList la) (RepresentationTheory.Combinatorics.PartitionPermutation.associatedPermutation n la T e₂).val) :
    e₁ ≤ e₂ := by
  rcases eq_or_lt_of_le hrow with hr | hr
  ·
    have hsum : (RepresentationTheory.SymmetricGroup.PartitionAuxiliaryConstructions.auxiliaryPartitionNatList la).sum = n := RepresentationTheory.Partition.YoungDiagram.sum_sortedParts n la
    have h₁ : (RepresentationTheory.Combinatorics.PartitionPermutation.associatedPermutation n la T e₁).val < (RepresentationTheory.SymmetricGroup.PartitionAuxiliaryConstructions.auxiliaryPartitionNatList la).sum := by omega
    have h₂ : (RepresentationTheory.Combinatorics.PartitionPermutation.associatedPermutation n la T e₂).val < (RepresentationTheory.SymmetricGroup.PartitionAuxiliaryConstructions.auxiliaryPartitionNatList la).sum := by omega
    have := RepresentationTheory.SymmetricGroup.PartitionAuxiliaryConstructions.eq_of_flatIndexRow_eq_and_column_eq (RepresentationTheory.SymmetricGroup.PartitionAuxiliaryConstructions.auxiliaryPartitionNatList la)
      (RepresentationTheory.Combinatorics.PartitionPermutation.associatedPermutation n la T e₁).val (RepresentationTheory.Combinatorics.PartitionPermutation.associatedPermutation n la T e₂).val h₁ h₂ hr hcol
    have := (RepresentationTheory.Combinatorics.PartitionPermutation.associatedPermutation n la T).injective (Fin.ext this)
    omega
  · exact le_of_lt (syt_entry_lt_of_row_lt T e₁ e₂ hcol hr)



private theorem card_filter_le_min {α : Type*}
    (A B : Finset α) (hB : B ⊆ A) (P : α → Prop) [DecidablePred P] :
    (B.filter P).card ≤ min B.card (A.filter P).card :=
  le_min (Finset.card_filter_le B P)
    (Finset.card_le_card (Finset.filter_subset_filter P hB))




private theorem syt_row_le_of_entry_le (T : RepresentationTheory.SymmetricGroup.PartitionAuxiliaryConstructions.AuxiliaryPartitionSource n la)
    (e₁ e₂ : Fin n)
    (hcol : RepresentationTheory.SymmetricGroup.PartitionAuxiliaryConstructions.flatIndexColumn (RepresentationTheory.SymmetricGroup.PartitionAuxiliaryConstructions.auxiliaryPartitionNatList la) (RepresentationTheory.Combinatorics.PartitionPermutation.associatedPermutation n la T e₁).val =
            RepresentationTheory.SymmetricGroup.PartitionAuxiliaryConstructions.flatIndexColumn (RepresentationTheory.SymmetricGroup.PartitionAuxiliaryConstructions.auxiliaryPartitionNatList la) (RepresentationTheory.Combinatorics.PartitionPermutation.associatedPermutation n la T e₂).val)
    (hle : e₁ ≤ e₂) :
    RepresentationTheory.SymmetricGroup.PartitionAuxiliaryConstructions.flatIndexRow (RepresentationTheory.SymmetricGroup.PartitionAuxiliaryConstructions.auxiliaryPartitionNatList la) (RepresentationTheory.Combinatorics.PartitionPermutation.associatedPermutation n la T e₁).val ≤
    RepresentationTheory.SymmetricGroup.PartitionAuxiliaryConstructions.flatIndexRow (RepresentationTheory.SymmetricGroup.PartitionAuxiliaryConstructions.auxiliaryPartitionNatList la) (RepresentationTheory.Combinatorics.PartitionPermutation.associatedPermutation n la T e₂).val := by
  by_contra h
  push Not at h
  have := syt_entry_lt_of_row_lt T e₂ e₁ hcol.symm h
  omega




private theorem swap_column_dominance (σ : Equiv.Perm (Fin n))
    (p₁ p₂ : Fin n) (hcol : RepresentationTheory.SymmetricGroup.PartitionAuxiliaryConstructions.flatIndexColumn (RepresentationTheory.SymmetricGroup.PartitionAuxiliaryConstructions.auxiliaryPartitionNatList la) p₁.val = RepresentationTheory.SymmetricGroup.PartitionAuxiliaryConstructions.flatIndexColumn (RepresentationTheory.SymmetricGroup.PartitionAuxiliaryConstructions.auxiliaryPartitionNatList la) p₂.val)
    (hrow_lt : RepresentationTheory.SymmetricGroup.PartitionAuxiliaryConstructions.flatIndexRow (RepresentationTheory.SymmetricGroup.PartitionAuxiliaryConstructions.auxiliaryPartitionNatList la) p₁.val < RepresentationTheory.SymmetricGroup.PartitionAuxiliaryConstructions.flatIndexRow (RepresentationTheory.SymmetricGroup.PartitionAuxiliaryConstructions.auxiliaryPartitionNatList la) p₂.val)
    (hentry : σ.symm p₁ < σ.symm p₂) :
    permutationRel la σ (Equiv.swap p₁ p₂ * σ) := by
  intro k i
  simp only [permutationToIndexedNatFunction, Equiv.Perm.coe_mul, Function.comp_apply]






  set e₁ := σ.symm p₁
  set e₂ := σ.symm p₂











  by_cases hi₁ : RepresentationTheory.SymmetricGroup.PartitionAuxiliaryConstructions.flatIndexRow (RepresentationTheory.SymmetricGroup.PartitionAuxiliaryConstructions.auxiliaryPartitionNatList la) p₁.val < i
  · by_cases hi₂ : RepresentationTheory.SymmetricGroup.PartitionAuxiliaryConstructions.flatIndexRow (RepresentationTheory.SymmetricGroup.PartitionAuxiliaryConstructions.auxiliaryPartitionNatList la) p₂.val < i
    ·
      apply Finset.card_le_card
      intro e
      simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      intro ⟨hle, hrow⟩
      refine ⟨hle, ?_⟩
      by_cases he₁ : σ e = p₁
      · rw [he₁]; exact hi₁
      · by_cases he₂ : σ e = p₂
        · rw [he₂]; exact hi₂
        · rw [Equiv.swap_apply_of_ne_of_ne he₁ he₂] at hrow; exact hrow
    ·
      push Not at hi₂
















      suffices h : ∀ e : Fin n, e ≠ e₁ → e ≠ e₂ →
          (RepresentationTheory.SymmetricGroup.PartitionAuxiliaryConstructions.flatIndexRow (RepresentationTheory.SymmetricGroup.PartitionAuxiliaryConstructions.auxiliaryPartitionNatList la) (Equiv.swap p₁ p₂ (σ e)).val < i ↔
           RepresentationTheory.SymmetricGroup.PartitionAuxiliaryConstructions.flatIndexRow (RepresentationTheory.SymmetricGroup.PartitionAuxiliaryConstructions.auxiliaryPartitionNatList la) (σ e).val < i) by

        rw [← Finset.card_image_of_injective _ (Equiv.swap e₁ e₂).injective]
        apply Finset.card_le_card
        intro e he
        simp only [Finset.mem_image, Finset.mem_filter, Finset.mem_univ, true_and] at he ⊢
        obtain ⟨e', ⟨hle', hrow'⟩, rfl⟩ := he

        by_cases hee₁ : e' = e₁
        ·
          exfalso; subst hee₁
          have : σ e₁ = p₁ := σ.apply_symm_apply p₁
          rw [this, Equiv.swap_apply_left] at hrow'; omega
        · by_cases hee₂ : e' = e₂
          ·
            subst hee₂
            rw [Equiv.swap_apply_right]
            have hσe₁ : σ e₁ = p₁ := σ.apply_symm_apply p₁
            rw [hσe₁]
            exact ⟨le_of_lt (lt_of_lt_of_le hentry hle'), hi₁⟩
          ·
            rw [Equiv.swap_apply_of_ne_of_ne hee₁ hee₂]
            exact ⟨hle', (h e' hee₁ hee₂).mp hrow'⟩

      intro e hne₁ hne₂
      have : σ e ≠ p₁ := fun h => hne₁ (σ.injective (h ▸ (σ.apply_symm_apply p₁).symm))
      have : σ e ≠ p₂ := fun h => hne₂ (σ.injective (h ▸ (σ.apply_symm_apply p₂).symm))
      rw [Equiv.swap_apply_of_ne_of_ne ‹σ e ≠ p₁› ‹σ e ≠ p₂›]
  ·
    push Not at hi₁
    apply Finset.card_le_card
    intro e
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    intro ⟨hle, hrow⟩
    refine ⟨hle, ?_⟩
    by_cases he₁ : σ e = p₁
    · exfalso; rw [he₁, Equiv.swap_apply_left] at hrow; omega
    · by_cases he₂ : σ e = p₂
      · exfalso; rw [he₂, Equiv.swap_apply_right] at hrow; omega
      · rw [Equiv.swap_apply_of_ne_of_ne he₁ he₂] at hrow; exact hrow

/-- A permutation in the displayed collection relates the indicated permutation expression to its inverse left translate. -/
theorem permutationRel_inv_mul_of_mem (T : RepresentationTheory.SymmetricGroup.PartitionAuxiliaryConstructions.AuxiliaryPartitionSource n la)
    (q : Equiv.Perm (Fin n)) (hq : q ∈ RepresentationTheory.SymmetricGroup.PartitionAuxiliaryConstructions.auxiliaryPartitionPermutationSubgroupA n la) :
    permutationRel la (RepresentationTheory.Combinatorics.PartitionPermutation.associatedPermutation n la T) (q⁻¹ * RepresentationTheory.Combinatorics.PartitionPermutation.associatedPermutation n la T) := by
  set σ := RepresentationTheory.Combinatorics.PartitionPermutation.associatedPermutation n la T with hσ_def
  have hq_inv : ∀ p : Fin n, RepresentationTheory.SymmetricGroup.PartitionAuxiliaryConstructions.flatIndexColumn (RepresentationTheory.SymmetricGroup.PartitionAuxiliaryConstructions.auxiliaryPartitionNatList la) (q⁻¹ p).val =
      RepresentationTheory.SymmetricGroup.PartitionAuxiliaryConstructions.flatIndexColumn (RepresentationTheory.SymmetricGroup.PartitionAuxiliaryConstructions.auxiliaryPartitionNatList la) p.val := (RepresentationTheory.SymmetricGroup.PartitionAuxiliaryConstructions.auxiliaryPartitionPermutationSubgroupA n la).inv_mem hq
  have hq_fwd : ∀ p : Fin n, RepresentationTheory.SymmetricGroup.PartitionAuxiliaryConstructions.flatIndexColumn (RepresentationTheory.SymmetricGroup.PartitionAuxiliaryConstructions.auxiliaryPartitionNatList la) (q p).val =
      RepresentationTheory.SymmetricGroup.PartitionAuxiliaryConstructions.flatIndexColumn (RepresentationTheory.SymmetricGroup.PartitionAuxiliaryConstructions.auxiliaryPartitionNatList la) p.val := hq
  intro k i
  simp only [permutationToIndexedNatFunction, Equiv.Perm.coe_mul, Function.comp_apply]
  set A := Finset.univ.filter (fun e : Fin n =>
    e ≤ k ∧ RepresentationTheory.SymmetricGroup.PartitionAuxiliaryConstructions.flatIndexRow (RepresentationTheory.SymmetricGroup.PartitionAuxiliaryConstructions.auxiliaryPartitionNatList la) (σ e).val < i)
  set B := Finset.univ.filter (fun e : Fin n =>
    e ≤ k ∧ RepresentationTheory.SymmetricGroup.PartitionAuxiliaryConstructions.flatIndexRow (RepresentationTheory.SymmetricGroup.PartitionAuxiliaryConstructions.auxiliaryPartitionNatList la) (q⁻¹ (σ e)).val < i)
  set ecol : Fin n → ℕ := fun e => RepresentationTheory.SymmetricGroup.PartitionAuxiliaryConstructions.flatIndexColumn (RepresentationTheory.SymmetricGroup.PartitionAuxiliaryConstructions.auxiliaryPartitionNatList la) (σ e).val

  suffices hcol : ∀ c, (B.filter (fun e => ecol e = c)).card ≤
      (A.filter (fun e => ecol e = c)).card by
    have hmaps : ∀ (S : Finset (Fin n)), (S : Set (Fin n)).MapsTo ecol
        (↑(Finset.univ.image ecol)) :=
      fun _ e _ => Finset.mem_coe.mpr (Finset.mem_image.mpr ⟨e, Finset.mem_univ e, rfl⟩)
    rw [Finset.card_eq_sum_card_fiberwise (hmaps B),
        Finset.card_eq_sum_card_fiberwise (hmaps A)]
    exact Finset.sum_le_sum (fun c _ => hcol c)
  intro c

  by_cases hall : ∀ e : Fin n, ecol e = c → e ≤ k →
      RepresentationTheory.SymmetricGroup.PartitionAuxiliaryConstructions.flatIndexRow (RepresentationTheory.SymmetricGroup.PartitionAuxiliaryConstructions.auxiliaryPartitionNatList la) (σ e).val < i
  ·

    have hAeq : A.filter (fun e => ecol e = c) =
        Finset.univ.filter (fun e : Fin n => e ≤ k ∧ ecol e = c) := by
      ext e; simp only [Finset.mem_filter, Finset.mem_univ, true_and, A]
      exact ⟨fun ⟨⟨h1, _⟩, h2⟩ => ⟨h1, h2⟩,
             fun ⟨h1, h2⟩ => ⟨⟨h1, hall e h2 h1⟩, h2⟩⟩
    rw [hAeq]
    apply Finset.card_le_card
    intro e; simp only [Finset.mem_filter, Finset.mem_univ, true_and, B]
    exact fun ⟨⟨h1, _⟩, h2⟩ => ⟨h1, h2⟩
  ·

    push Not at hall
    obtain ⟨e₀, hecol₀, hle₀, hrow₀⟩ := hall
    have hrow_imp : ∀ e : Fin n, ecol e = c →
        RepresentationTheory.SymmetricGroup.PartitionAuxiliaryConstructions.flatIndexRow (RepresentationTheory.SymmetricGroup.PartitionAuxiliaryConstructions.auxiliaryPartitionNatList la) (σ e).val < i → e ≤ k := by
      intro e hec hri
      by_contra hgt; push Not at hgt
      have he₀_le : e₀ ≤ e := by omega
      have hcol_eq : RepresentationTheory.SymmetricGroup.PartitionAuxiliaryConstructions.flatIndexColumn (RepresentationTheory.SymmetricGroup.PartitionAuxiliaryConstructions.auxiliaryPartitionNatList la) (RepresentationTheory.Combinatorics.PartitionPermutation.associatedPermutation n la T e₀).val =
          RepresentationTheory.SymmetricGroup.PartitionAuxiliaryConstructions.flatIndexColumn (RepresentationTheory.SymmetricGroup.PartitionAuxiliaryConstructions.auxiliaryPartitionNatList la) (RepresentationTheory.Combinatorics.PartitionPermutation.associatedPermutation n la T e).val := by
        change ecol e₀ = ecol e; rw [hecol₀, hec]
      have hrow_le := syt_row_le_of_entry_le T e₀ e hcol_eq he₀_le
      simp only [← hσ_def] at hrow_le; omega

    have hAeq : A.filter (fun e => ecol e = c) =
        Finset.univ.filter (fun e : Fin n =>
          RepresentationTheory.SymmetricGroup.PartitionAuxiliaryConstructions.flatIndexRow (RepresentationTheory.SymmetricGroup.PartitionAuxiliaryConstructions.auxiliaryPartitionNatList la) (σ e).val < i ∧ ecol e = c) := by
      ext e; simp only [Finset.mem_filter, Finset.mem_univ, true_and, A]
      exact ⟨fun ⟨⟨_, h2⟩, h3⟩ => ⟨h2, h3⟩,
             fun ⟨h1, h2⟩ => ⟨⟨hrow_imp e h2 h1, h1⟩, h2⟩⟩
    rw [hAeq]

    calc (B.filter (fun e => ecol e = c)).card
        ≤ (Finset.univ.filter (fun e : Fin n =>
            RepresentationTheory.SymmetricGroup.PartitionAuxiliaryConstructions.flatIndexRow (RepresentationTheory.SymmetricGroup.PartitionAuxiliaryConstructions.auxiliaryPartitionNatList la) (q⁻¹ (σ e)).val < i ∧ ecol e = c)).card := by
          apply Finset.card_le_card
          intro e; simp only [Finset.mem_filter, Finset.mem_univ, true_and, B]
          exact fun ⟨⟨_, h2⟩, h3⟩ => ⟨h2, h3⟩
      _ = (Finset.univ.filter (fun e : Fin n =>
            RepresentationTheory.SymmetricGroup.PartitionAuxiliaryConstructions.flatIndexRow (RepresentationTheory.SymmetricGroup.PartitionAuxiliaryConstructions.auxiliaryPartitionNatList la) (σ e).val < i ∧ ecol e = c)).card := by


          apply Finset.card_nbij'
            (fun e => σ.symm ((q : Equiv.Perm (Fin n))⁻¹ (σ e)))
            (fun e => σ.symm (q (σ e)))
          ·
            intro e he
            simp only [Finset.mem_coe, Finset.mem_filter, Finset.mem_univ,
              true_and] at he ⊢
            refine ⟨?_, ?_⟩
            ·
              simp only [Equiv.apply_symm_apply]; exact he.1
            ·
              show ecol (σ.symm ((q : Equiv.Perm (Fin n))⁻¹ (σ e))) = c
              simp only [ecol, Equiv.apply_symm_apply, hq_inv]; exact he.2
          ·
            intro e he
            simp only [Finset.mem_coe, Finset.mem_filter, Finset.mem_univ,
              true_and] at he ⊢
            refine ⟨?_, ?_⟩
            ·
              rw [Equiv.apply_symm_apply]
              change RepresentationTheory.SymmetricGroup.PartitionAuxiliaryConstructions.flatIndexRow (RepresentationTheory.SymmetricGroup.PartitionAuxiliaryConstructions.auxiliaryPartitionNatList la) (q.symm (q (σ e))).val < i
              rw [Equiv.symm_apply_apply]; exact he.1
            ·
              show ecol (σ.symm (q (σ e))) = c
              simp only [ecol, Equiv.apply_symm_apply, hq_fwd]; exact he.2
          ·
            intro e _
            dsimp only

            simp only [Equiv.apply_symm_apply, Equiv.Perm.coe_inv, Equiv.apply_symm_apply,
                Equiv.symm_apply_apply]
          ·
            intro e _
            dsimp only

            simp only [Equiv.apply_symm_apply, Equiv.Perm.coe_inv, Equiv.symm_apply_apply]




/-- A nonidentity member of the displayed collection satisfies the second indicated permutation relation with the corresponding inverse left translate. -/
theorem permutationRelAux_inv_mul_of_mem_ne_one (T : RepresentationTheory.SymmetricGroup.PartitionAuxiliaryConstructions.AuxiliaryPartitionSource n la)
    (q : Equiv.Perm (Fin n)) (hq : q ∈ RepresentationTheory.SymmetricGroup.PartitionAuxiliaryConstructions.auxiliaryPartitionPermutationSubgroupA n la) (hne : q ≠ 1) :
    permutationRelAux la (RepresentationTheory.Combinatorics.PartitionPermutation.associatedPermutation n la T) (q⁻¹ * RepresentationTheory.Combinatorics.PartitionPermutation.associatedPermutation n la T) :=
  ⟨permutationRel_inv_mul_of_mem T q hq,
   (permutationToAuxiliaryType_inv_mul_ne_objectValue T q hq hne).symm⟩















/-- From a nonzero value on a member of a finite set, one can choose a nonzero member such that every related nonzero member has the same displayed auxiliary value. -/
lemma exists_nonzero_mem_with_related_value_eq
    (S : Finset (RepresentationTheory.SymmetricGroup.PartitionAuxiliaryConstructions.AuxiliaryPartitionSource n la))
    (f : RepresentationTheory.SymmetricGroup.PartitionAuxiliaryConstructions.AuxiliaryPartitionSource n la → ℂ) (T₀ : RepresentationTheory.SymmetricGroup.PartitionAuxiliaryConstructions.AuxiliaryPartitionSource n la)
    (hT₀ : T₀ ∈ S) (hfT₀ : f T₀ ≠ 0) :
    ∃ T₁ ∈ S, f T₁ ≠ 0 ∧
      ∀ T' ∈ S, f T' ≠ 0 →
        permutationRel la (RepresentationTheory.Combinatorics.PartitionPermutation.associatedPermutation n la T') (RepresentationTheory.Combinatorics.PartitionPermutation.associatedPermutation n la T₁) →
        objectToAuxiliaryType n la T' = objectToAuxiliaryType n la T₁ := by


  classical


  suffices hmain : ∀ (m : ℕ) (T : RepresentationTheory.SymmetricGroup.PartitionAuxiliaryConstructions.AuxiliaryPartitionSource n la),
      T ∈ S → f T ≠ 0 →
      (S.filter fun T' => f T' ≠ 0 ∧
        permutationRelAux la (RepresentationTheory.Combinatorics.PartitionPermutation.associatedPermutation n la T') (RepresentationTheory.Combinatorics.PartitionPermutation.associatedPermutation n la T)).card = m →
      ∃ T₁ ∈ S, f T₁ ≠ 0 ∧ ∀ T' ∈ S, f T' ≠ 0 →
        permutationRel la (RepresentationTheory.Combinatorics.PartitionPermutation.associatedPermutation n la T') (RepresentationTheory.Combinatorics.PartitionPermutation.associatedPermutation n la T₁) →
        objectToAuxiliaryType n la T' = objectToAuxiliaryType n la T₁ by
    exact hmain _ T₀ hT₀ hfT₀ rfl
  intro m
  induction m using Nat.strongRecOn with
  | ind m ih =>
  intro T hTS hfT hcard

  by_cases hmax : ∀ T' ∈ S, f T' ≠ 0 →
      permutationRel la (RepresentationTheory.Combinatorics.PartitionPermutation.associatedPermutation n la T') (RepresentationTheory.Combinatorics.PartitionPermutation.associatedPermutation n la T) →
      objectToAuxiliaryType n la T' = objectToAuxiliaryType n la T
  · exact ⟨T, hTS, hfT, hmax⟩
  ·
    push Not at hmax
    obtain ⟨T', hT'S, hfT', hdom, hne_tab⟩ := hmax

    have hstrict : permutationRelAux la (RepresentationTheory.Combinatorics.PartitionPermutation.associatedPermutation n la T') (RepresentationTheory.Combinatorics.PartitionPermutation.associatedPermutation n la T) :=
      ⟨hdom, fun h => hne_tab (permutationToAuxiliaryType_eq_of_natFunction_eq _ _
        (permutationToNatFunction_eq_of_auxiliaryValue_eq _ _ h))⟩
    apply ih (S.filter fun T'' => f T'' ≠ 0 ∧
        permutationRelAux la (RepresentationTheory.Combinatorics.PartitionPermutation.associatedPermutation n la T'') (RepresentationTheory.Combinatorics.PartitionPermutation.associatedPermutation n la T')).card
    ·
      rw [← hcard]
      apply Finset.card_lt_card
      rw [Finset.ssubset_iff_of_subset]
      ·
        refine ⟨T', ?_, ?_⟩
        · simp only [Finset.mem_filter]
          exact ⟨hT'S, hfT', hstrict⟩
        · simp only [Finset.mem_filter]
          simp only [not_and]
          intro _ _ hsd
          exact hsd.2 rfl
      ·
        intro T'' hT''
        simp only [Finset.mem_filter] at hT'' ⊢
        refine ⟨hT''.1, hT''.2.1, ?_⟩
        exact ⟨permutationRel_trans hT''.2.2.1 hstrict.1,
          fun heq =>




            hstrict.2 (middle_auxiliaryValue_eq_of_rel_chain
              hT''.2.2.1 hstrict.1 heq)⟩
    · exact hT'S
    · exact hfT'
    · rfl





/-- If the displayed relation holds in both directions between two permutations, their displayed auxiliary values are equal. -/
theorem permutationToAuxiliaryType_eq_of_rel_and_reverse {σ₁ σ₂ : Equiv.Perm (Fin n)}
    (h₁₂ : permutationRel la σ₁ σ₂) (h₂₁ : permutationRel la σ₂ σ₁) :
    permutationToAuxiliaryType n la σ₂ = permutationToAuxiliaryType n la σ₁ :=
  middle_auxiliaryValue_eq_of_rel_chain h₁₂ h₂₁ rfl


/-- Applying the displayed permutation map to a quotient representative recovers the original element. -/
theorem permutationToAuxiliaryType_quotientOut (t : partitionIndexedAuxiliaryType n la) :
    permutationToAuxiliaryType n la (Quotient.out t) = t :=
  Quotient.out_eq t














/-- A nonempty finite set contains a member to which no distinct member of the set is related by the displayed relation. -/
lemma exists_mem_unique_of_related
    (S : Finset (partitionIndexedAuxiliaryType n la)) (t₀ : partitionIndexedAuxiliaryType n la) (ht₀ : t₀ ∈ S) :
    ∃ t₁ ∈ S, ∀ t' ∈ S,
      permutationRel la (Quotient.out t') (Quotient.out t₁) → t' = t₁ := by
  classical

  have hAntisymm : ∀ a b : partitionIndexedAuxiliaryType n la,
      permutationRel la (Quotient.out a) (Quotient.out b) →
      permutationRel la (Quotient.out b) (Quotient.out a) → a = b := by
    intro a b hab hba
    have := permutationToAuxiliaryType_eq_of_rel_and_reverse (la := la) hab hba
    rw [permutationToAuxiliaryType_quotientOut, permutationToAuxiliaryType_quotientOut] at this
    exact this.symm

  suffices hmain : ∀ (m : ℕ) (t : partitionIndexedAuxiliaryType n la), t ∈ S →
      (S.filter fun t' =>
        permutationRel la (Quotient.out t') (Quotient.out t) ∧ t' ≠ t).card = m →
      ∃ t₁ ∈ S, ∀ t' ∈ S,
        permutationRel la (Quotient.out t') (Quotient.out t₁) → t' = t₁ by
    exact hmain _ t₀ ht₀ rfl
  intro m
  induction m using Nat.strongRecOn with
  | ind m ih =>
  intro t htS hcard
  by_cases hmax : ∀ t' ∈ S,
      permutationRel la (Quotient.out t') (Quotient.out t) → t' = t
  · exact ⟨t, htS, hmax⟩
  ·
    push Not at hmax
    obtain ⟨t', ht'S, hdom, hne⟩ := hmax
    apply ih (S.filter fun t'' =>
        permutationRel la (Quotient.out t'') (Quotient.out t') ∧ t'' ≠ t').card
    ·
      rw [← hcard]
      apply Finset.card_lt_card
      rw [Finset.ssubset_iff_of_subset]
      ·
        refine ⟨t', ?_, ?_⟩
        · simp only [Finset.mem_filter]
          exact ⟨ht'S, hdom, hne⟩
        · intro hmem
          rw [Finset.mem_filter] at hmem
          exact hmem.2.2 rfl
      ·
        intro t'' ht''
        simp only [Finset.mem_filter] at ht'' ⊢
        refine ⟨ht''.1, permutationRel_trans ht''.2.1 hdom, ?_⟩
        intro heq

        apply hne
        have hother : permutationRel la (Quotient.out t) (Quotient.out t') :=
          heq ▸ ht''.2.1
        exact hAntisymm t' t hdom hother
    · exact ht'S
    · rfl








/-- A second auxiliary type parameterized by a natural number and a partition of it. -/
abbrev partitionIndexedAuxiliaryType2 (n : ℕ) (la : Nat.Partition n) :=
  Finsupp (partitionIndexedAuxiliaryType n la) ℂ







/-- Maps an element of an auxiliary type to the second partition-indexed auxiliary type. -/
noncomputable def objectToAuxiliaryType2 (T : RepresentationTheory.SymmetricGroup.PartitionAuxiliaryConstructions.AuxiliaryPartitionSource n la) :
    partitionIndexedAuxiliaryType2 n la :=
  haveI : DecidablePred (· ∈ RepresentationTheory.SymmetricGroup.PartitionAuxiliaryConstructions.auxiliaryPartitionPermutationSubgroupA n la) := Classical.decPred _
  ∑ q : ↥(RepresentationTheory.SymmetricGroup.PartitionAuxiliaryConstructions.auxiliaryPartitionPermutationSubgroupA n la),
    ((↑(Equiv.Perm.sign q.val) : ℤ) : ℂ) •
      Finsupp.single (permutationToAuxiliaryType n la (q.val⁻¹ * RepresentationTheory.Combinatorics.PartitionPermutation.associatedPermutation n la T)) 1



private theorem toTabloid_inv_mul_injective (T : RepresentationTheory.SymmetricGroup.PartitionAuxiliaryConstructions.AuxiliaryPartitionSource n la)
    (q₁ q₂ : ↥(RepresentationTheory.SymmetricGroup.PartitionAuxiliaryConstructions.auxiliaryPartitionPermutationSubgroupA n la))
    (h : permutationToAuxiliaryType n la (q₁.val⁻¹ * RepresentationTheory.Combinatorics.PartitionPermutation.associatedPermutation n la T) =
         permutationToAuxiliaryType n la (q₂.val⁻¹ * RepresentationTheory.Combinatorics.PartitionPermutation.associatedPermutation n la T)) :
    q₁ = q₂ := by
  rw [permutationToAuxiliaryType_eq_iff_mul_inv_mem] at h

  have h' : q₁.val⁻¹ * q₂.val ∈ RepresentationTheory.SymmetricGroup.PartitionAuxiliaryConstructions.auxiliaryPartitionPermutationSubgroupB n la := by
    convert h using 1; group
  have := eq_one_of_mem_two_auxiliarySets n la (q₁.val⁻¹ * q₂.val) h'
    ((RepresentationTheory.SymmetricGroup.PartitionAuxiliaryConstructions.auxiliaryPartitionPermutationSubgroupA n la).mul_mem
      ((RepresentationTheory.SymmetricGroup.PartitionAuxiliaryConstructions.auxiliaryPartitionPermutationSubgroupA n la).inv_mem q₁.prop) q₂.prop)
  exact Subtype.ext (eq_of_inv_mul_eq_one this)





/-- The map associated with an auxiliary object takes value one at its displayed associated value. -/
theorem objectToAuxiliaryType2_apply_objectValue (T : RepresentationTheory.SymmetricGroup.PartitionAuxiliaryConstructions.AuxiliaryPartitionSource n la) :
    objectToAuxiliaryType2 T (objectToAuxiliaryType n la T) = 1 := by
  classical
  simp only [objectToAuxiliaryType2, objectToAuxiliaryType]
  rw [Finsupp.finsetSum_apply]
  rw [Finset.sum_eq_single (⟨1, (RepresentationTheory.SymmetricGroup.PartitionAuxiliaryConstructions.auxiliaryPartitionPermutationSubgroupA n la).one_mem⟩ :
      ↥(RepresentationTheory.SymmetricGroup.PartitionAuxiliaryConstructions.auxiliaryPartitionPermutationSubgroupA n la))]
  ·
    simp [Equiv.Perm.sign_one]
  ·
    intro q _ hq
    rw [Finsupp.smul_apply, smul_eq_mul, Finsupp.single_apply]
    have hne : (q : Equiv.Perm (Fin n)) ≠ 1 := fun h => hq (Subtype.ext h)
    have := permutationToAuxiliaryType_inv_mul_ne_objectValue T q.val q.prop hne
    simp only [objectToAuxiliaryType] at this
    rw [if_neg this, mul_zero]
  · intro h; exact absurd (Finset.mem_univ _) h







/-- A nonzero value of the map associated with an auxiliary object at a displayed permutation image implies the indicated relation. -/
theorem permutationRel_of_objectToAuxiliaryType2_apply_ne_zero (T : RepresentationTheory.SymmetricGroup.PartitionAuxiliaryConstructions.AuxiliaryPartitionSource n la)
    (σ : Equiv.Perm (Fin n))
    (hne : objectToAuxiliaryType2 T (permutationToAuxiliaryType n la σ) ≠ 0) :
    permutationRel la (RepresentationTheory.Combinatorics.PartitionPermutation.associatedPermutation n la T) σ := by
  classical
  simp only [objectToAuxiliaryType2] at hne
  rw [Finsupp.finsetSum_apply] at hne

  obtain ⟨q, _, hq_term⟩ := Finset.exists_ne_zero_of_sum_ne_zero hne
  rw [Finsupp.smul_apply, smul_eq_mul, Finsupp.single_apply] at hq_term
  split_ifs at hq_term with heq
  ·

    have hdom := permutationRel_inv_mul_of_mem T q.val q.prop

    exact permutationRel_congr rfl heq hdom
  · simp at hq_term



/-- A nonzero value of the map associated with one auxiliary object at another object's displayed value implies the indicated relation between their displayed permutations. -/
theorem permutationRel_of_objectToAuxiliaryType2_apply_objectValue_ne_zero (T₁ T₂ : RepresentationTheory.SymmetricGroup.PartitionAuxiliaryConstructions.AuxiliaryPartitionSource n la)
    (hne : objectToAuxiliaryType2 T₁ (objectToAuxiliaryType n la T₂) ≠ 0) :
    permutationRel la (RepresentationTheory.Combinatorics.PartitionPermutation.associatedPermutation n la T₁) (RepresentationTheory.Combinatorics.PartitionPermutation.associatedPermutation n la T₂) :=
  permutationRel_of_objectToAuxiliaryType2_apply_ne_zero T₁ (RepresentationTheory.Combinatorics.PartitionPermutation.associatedPermutation n la T₂) hne





private lemma polytabloidTab_coeff_zero_of_maximal
    (S : Finset (RepresentationTheory.SymmetricGroup.PartitionAuxiliaryConstructions.AuxiliaryPartitionSource n la))
    (f : RepresentationTheory.SymmetricGroup.PartitionAuxiliaryConstructions.AuxiliaryPartitionSource n la → ℂ)
    (hf : ∑ t ∈ S, f t • objectToAuxiliaryType2 t = 0)
    (T₀ : RepresentationTheory.SymmetricGroup.PartitionAuxiliaryConstructions.AuxiliaryPartitionSource n la) (hT₀ : T₀ ∈ S)
    (hmax : ∀ T' ∈ S, f T' ≠ 0 →
      permutationRel la (RepresentationTheory.Combinatorics.PartitionPermutation.associatedPermutation n la T') (RepresentationTheory.Combinatorics.PartitionPermutation.associatedPermutation n la T₀) →
      objectToAuxiliaryType n la T' = objectToAuxiliaryType n la T₀) :
    f T₀ = 0 := by
  classical

  have heval : (∑ t ∈ S, f t • objectToAuxiliaryType2 t) (objectToAuxiliaryType n la T₀) = 0 := by
    rw [hf]; rfl
  rw [Finsupp.finsetSum_apply] at heval
  simp only [Finsupp.smul_apply, smul_eq_mul] at heval

  rw [← Finset.add_sum_erase S _ hT₀] at heval

  rw [objectToAuxiliaryType2_apply_objectValue, mul_one] at heval

  suffices hrest : ∀ T' ∈ S.erase T₀,
      f T' * objectToAuxiliaryType2 T' (objectToAuxiliaryType n la T₀) = 0 by
    rw [Finset.sum_eq_zero hrest, add_zero] at heval; exact heval
  intro T' hT'
  have hT'S : T' ∈ S := Finset.mem_of_mem_erase hT'
  have hne_T : T' ≠ T₀ := Finset.ne_of_mem_erase hT'
  by_cases hfT' : f T' = 0
  · rw [hfT', zero_mul]
  by_cases hcoeff : objectToAuxiliaryType2 T' (objectToAuxiliaryType n la T₀) = 0
  · rw [hcoeff, mul_zero]
  ·
    have hdom := permutationRel_of_objectToAuxiliaryType2_apply_objectValue_ne_zero T' T₀ hcoeff

    have htab_eq := hmax T' hT'S hfT' hdom

    exact absurd (objectToAuxiliaryType_injective n la htab_eq) hne_T








/-- The displayed family indexed by the auxiliary type is linearly independent over the complex numbers. -/
theorem linearIndependent_objectToAuxiliaryType2 :
    LinearIndependent ℂ (fun T : RepresentationTheory.SymmetricGroup.PartitionAuxiliaryConstructions.AuxiliaryPartitionSource n la => objectToAuxiliaryType2 T) := by
  rw [linearIndependent_iff']
  intro S f hf T hT
  by_contra hfT
  obtain ⟨T₀, hT₀, hfT₀, hmax⟩ := exists_nonzero_mem_with_related_value_eq S f T hT hfT
  exact hfT₀ (polytabloidTab_coeff_zero_of_maximal S f hf T₀ hT₀ hmax)

















/-- Maps a permutation of `Fin n` to the second partition-indexed auxiliary type. -/
noncomputable def permutationToAuxiliaryType2 (σ : Equiv.Perm (Fin n)) :
    partitionIndexedAuxiliaryType2 n la :=
  haveI : DecidablePred (· ∈ RepresentationTheory.SymmetricGroup.PartitionAuxiliaryConstructions.auxiliaryPartitionPermutationSubgroupA n la) := Classical.decPred _
  ∑ q : ↥(RepresentationTheory.SymmetricGroup.PartitionAuxiliaryConstructions.auxiliaryPartitionPermutationSubgroupA n la),
    ((↑(Equiv.Perm.sign q.val) : ℤ) : ℂ) •
      Finsupp.single (permutationToAuxiliaryType n la (q.val⁻¹ * σ)) 1


/-- The value attached to the displayed permutation associated with an auxiliary object equals the value assigned directly to that object. -/
theorem permutationToAuxiliaryType2_objectPermutation (T : RepresentationTheory.SymmetricGroup.PartitionAuxiliaryConstructions.AuxiliaryPartitionSource n la) :
    permutationToAuxiliaryType2 (RepresentationTheory.Combinatorics.PartitionPermutation.associatedPermutation n la T) = objectToAuxiliaryType2 T := rfl


/-- Left multiplication by a permutation in the displayed collection scales the associated value by its sign. -/
theorem permutationToAuxiliaryType2_mul_eq_sign_smul (q₀ : Equiv.Perm (Fin n))
    (hq₀ : q₀ ∈ RepresentationTheory.SymmetricGroup.PartitionAuxiliaryConstructions.auxiliaryPartitionPermutationSubgroupA n la) (σ : Equiv.Perm (Fin n)) :
    permutationToAuxiliaryType2 (n := n) (la := la) (q₀ * σ) =
      ((↑(Equiv.Perm.sign q₀) : ℤ) : ℂ) •
        permutationToAuxiliaryType2 (n := n) (la := la) σ := by
  classical
  simp only [permutationToAuxiliaryType2, Finset.smul_sum, smul_smul]

  set φ : ↥(RepresentationTheory.SymmetricGroup.PartitionAuxiliaryConstructions.auxiliaryPartitionPermutationSubgroupA n la) ≃ ↥(RepresentationTheory.SymmetricGroup.PartitionAuxiliaryConstructions.auxiliaryPartitionPermutationSubgroupA n la) :=
    ⟨fun q => ⟨q₀⁻¹ * q, (RepresentationTheory.SymmetricGroup.PartitionAuxiliaryConstructions.auxiliaryPartitionPermutationSubgroupA n la).mul_mem
        ((RepresentationTheory.SymmetricGroup.PartitionAuxiliaryConstructions.auxiliaryPartitionPermutationSubgroupA n la).inv_mem hq₀) q.prop⟩,
     fun q => ⟨q₀ * q, (RepresentationTheory.SymmetricGroup.PartitionAuxiliaryConstructions.auxiliaryPartitionPermutationSubgroupA n la).mul_mem hq₀ q.prop⟩,
     fun ⟨q, _⟩ => Subtype.ext (by group),
     fun ⟨q, _⟩ => Subtype.ext (by group)⟩
  refine Fintype.sum_equiv φ _ _ (fun ⟨q, hq⟩ => ?_)

  have hφ_val : (φ ⟨q, hq⟩ : ↥(RepresentationTheory.SymmetricGroup.PartitionAuxiliaryConstructions.auxiliaryPartitionPermutationSubgroupA n la)).val = q₀⁻¹ * q := rfl
  simp only [hφ_val]
  congr 1

  simp only [← Units.val_mul, ← Int.cast_mul]
  congr 1; congr 1
  rw [← map_mul, mul_inv_cancel_left]

















/-- An auxiliary theorem whose formal statement is unavailable in the packet. -/
theorem opaqueAuxiliaryTheorem (σ : Equiv.Perm (Fin n))
    (G : Finset (Fin n))
    (t : Equiv.Perm (Fin n))
    (ht_row : t ∈ RepresentationTheory.SymmetricGroup.PartitionAuxiliaryConstructions.auxiliaryPartitionPermutationSubgroupB n la)
    (ht_supp : ∀ x, x ∉ G → t x = x)
    (ht_sign : Equiv.Perm.sign t = -1) :
    ∑ w : { w : Equiv.Perm (Fin n) // ∀ x, x ∉ G → w x = x },
      ((↑(↑(Equiv.Perm.sign w.val) : ℤ) : ℂ) •
        Finsupp.single (permutationToAuxiliaryType n la (w.val * σ)) (1 : ℂ)) = 0 := by


  set S := { w : Equiv.Perm (Fin n) // ∀ x, x ∉ G → w x = x }
  have ht_inv_supp : ∀ x, x ∉ G → t⁻¹ x = x := fun x hx => by
    calc t⁻¹ x = t⁻¹ (t x) := by rw [ht_supp x hx]
      _ = x := Equiv.symm_apply_apply t x
  have hmul_mem : ∀ (w : Equiv.Perm (Fin n)),
      (∀ x, x ∉ G → w x = x) → (∀ x, x ∉ G → (t * w) x = x) :=
    fun w hw x hx => by change t (w x) = x; rw [hw x hx, ht_supp x hx]
  have hinv_mem : ∀ (w : Equiv.Perm (Fin n)),
      (∀ x, x ∉ G → w x = x) → (∀ x, x ∉ G → (t⁻¹ * w) x = x) :=
    fun w hw x hx => by change t⁻¹ (w x) = x; rw [hw x hx, ht_inv_supp x hx]

  set φ : S ≃ S :=
    ⟨fun ⟨w, hw⟩ => ⟨t * w, hmul_mem w hw⟩,
     fun ⟨w, hw⟩ => ⟨t⁻¹ * w, hinv_mem w hw⟩,
     fun ⟨w, _⟩ => Subtype.ext (show t⁻¹ * (t * w) = w by group),
     fun ⟨w, _⟩ => Subtype.ext (show t * (t⁻¹ * w) = w by group)⟩

  have key : ∀ (w : S),
      ((↑(↑(Equiv.Perm.sign (φ w).val) : ℤ) : ℂ) •
        Finsupp.single (permutationToAuxiliaryType n la ((φ w).val * σ)) (1 : ℂ)) =
      -((↑(↑(Equiv.Perm.sign w.val) : ℤ) : ℂ) •
        Finsupp.single (permutationToAuxiliaryType n la (w.val * σ)) (1 : ℂ)) := by
    intro ⟨w, hw⟩

    change ((↑(↑(Equiv.Perm.sign (t * w)) : ℤ) : ℂ) •
      Finsupp.single (permutationToAuxiliaryType n la (t * w * σ)) (1 : ℂ)) =
      -((↑(↑(Equiv.Perm.sign w) : ℤ) : ℂ) •
        Finsupp.single (permutationToAuxiliaryType n la (w * σ)) (1 : ℂ))

    have hsign : (↑(↑(Equiv.Perm.sign (t * w)) : ℤ) : ℂ) =
        -(↑(↑(Equiv.Perm.sign w) : ℤ) : ℂ) := by
      rw [map_mul, ht_sign, Units.val_mul, Int.cast_mul]
      simp [Int.cast_neg, Int.cast_one]

    have htabloid : permutationToAuxiliaryType n la (t * w * σ) = permutationToAuxiliaryType n la (w * σ) := by
      rw [permutationToAuxiliaryType_eq_iff_mul_inv_mem]
      convert ht_row using 1; group
    rw [hsign, htabloid, neg_smul]

  have h_neg : ∑ w : S, ((↑(↑(Equiv.Perm.sign w.val) : ℤ) : ℂ) •
      Finsupp.single (permutationToAuxiliaryType n la (w.val * σ)) (1 : ℂ)) =
    -(∑ w : S, ((↑(↑(Equiv.Perm.sign w.val) : ℤ) : ℂ) •
      Finsupp.single (permutationToAuxiliaryType n la (w.val * σ)) (1 : ℂ))) := by
    conv_lhs => rw [← Equiv.sum_comp φ]
    simp_rw [key]
    rw [Finset.sum_neg_distrib (f := fun (w : S) =>
      ((↑(↑(Equiv.Perm.sign w.val) : ℤ) : ℂ) •
        Finsupp.single (permutationToAuxiliaryType n la (w.val * σ)) (1 : ℂ)))]

  have h_add : ∑ w : S, ((↑(↑(Equiv.Perm.sign w.val) : ℤ) : ℂ) •
      Finsupp.single (permutationToAuxiliaryType n la (w.val * σ)) (1 : ℂ)) +
    ∑ w : S, ((↑(↑(Equiv.Perm.sign w.val) : ℤ) : ℂ) •
      Finsupp.single (permutationToAuxiliaryType n la (w.val * σ)) (1 : ℂ)) =
    (0 : partitionIndexedAuxiliaryType2 n la) := by
    nth_rw 1 [h_neg]; exact neg_add_cancel _
  rwa [show ∀ (x : partitionIndexedAuxiliaryType2 n la), x + x = (2 : ℂ) • x from
    fun x => (two_smul ℂ x).symm, smul_eq_zero,
    or_iff_right (by norm_num : (2 : ℂ) ≠ 0)] at h_add















/-- A complex-linear map from the displayed auxiliary source to the second partition-indexed auxiliary type. -/
noncomputable def auxiliaryLinearMap :
    RepresentationTheory.PartitionAuxiliary.natIndexedType n →ₗ[ℂ] partitionIndexedAuxiliaryType2 n la :=
  (Finsupp.lmapDomain ℂ ℂ (fun σ => permutationToAuxiliaryType n la σ⁻¹)).comp
    (MonoidAlgebra.coeffLinearEquiv ℂ).toLinearMap


/-- The displayed linear map maps a permutation monomial to the single-support value at the image of its inverse. -/
theorem auxiliaryLinearMap_monomial (σ : Equiv.Perm (Fin n)) :
    auxiliaryLinearMap (MonoidAlgebra.of ℂ _ σ) =
      (Finsupp.single (permutationToAuxiliaryType n la σ⁻¹) (1 : ℂ) :
        partitionIndexedAuxiliaryType2 n la) := by
  simp only [auxiliaryLinearMap, MonoidAlgebra.of_apply]
  exact Finsupp.mapDomain_single



private theorem toTabloid_inv_right_congr (σ₁ σ₂ τ : Equiv.Perm (Fin n))
    (h : permutationToAuxiliaryType n la σ₁⁻¹ = permutationToAuxiliaryType n la σ₂⁻¹) :
    permutationToAuxiliaryType n la (σ₁⁻¹ * τ⁻¹) = permutationToAuxiliaryType n la (σ₂⁻¹ * τ⁻¹) := by
  rw [permutationToAuxiliaryType_eq_iff_mul_inv_mem] at h ⊢
  convert h using 1; group




private theorem tabloidProjection_factor (τ σ₁ σ₂ : Equiv.Perm (Fin n))
    (h : permutationToAuxiliaryType n la σ₁⁻¹ = permutationToAuxiliaryType n la σ₂⁻¹) :
    permutationToAuxiliaryType n la (τ * σ₁)⁻¹ = permutationToAuxiliaryType n la (τ * σ₂)⁻¹ := by
  simp only [mul_inv_rev]
  exact toTabloid_inv_right_congr σ₁ σ₂ τ h




/-- Maps a permutation and an element of the partition-indexed auxiliary type to another element of that type. -/
noncomputable def permutationAuxiliaryTypeMap (τ : Equiv.Perm (Fin n)) :
    partitionIndexedAuxiliaryType n la → partitionIndexedAuxiliaryType n la :=
  Quotient.map (· * τ) (fun σ₁ σ₂ (h : σ₁ * σ₂⁻¹ ∈ RepresentationTheory.SymmetricGroup.PartitionAuxiliaryConstructions.auxiliaryPartitionPermutationSubgroupB n la) => by
    change (σ₁ * τ) * (σ₂ * τ)⁻¹ ∈ RepresentationTheory.SymmetricGroup.PartitionAuxiliaryConstructions.auxiliaryPartitionPermutationSubgroupB n la
    convert h using 1; group)

/-- Applying the displayed map to the auxiliary value of a permutation gives the auxiliary value of the displayed product. -/
@[simp]
theorem permutationAuxiliaryTypeMap_apply_permutation (τ σ : Equiv.Perm (Fin n)) :
    permutationAuxiliaryTypeMap (la := la) τ (permutationToAuxiliaryType n la σ) = permutationToAuxiliaryType n la (σ * τ) :=
  rfl




/-- Under the displayed linear map, multiplication by a permutation monomial corresponds to reindexing by the specified inverse map. -/
theorem auxiliaryLinearMap_monomial_mul (τ : Equiv.Perm (Fin n))
    (v : RepresentationTheory.PartitionAuxiliary.natIndexedType n) :
    auxiliaryLinearMap (n := n) (la := la) (MonoidAlgebra.of ℂ _ τ * v) =
      Finsupp.mapDomain (permutationAuxiliaryTypeMap (la := la) τ⁻¹)
        (auxiliaryLinearMap (n := n) (la := la) v) := by

  refine v.induction_linear (by simp [map_zero, Finsupp.mapDomain_zero])
    (fun f g hf hg => by simp only [mul_add, map_add, Finsupp.mapDomain_add, hf, hg]) ?_
  intro σ c

  simp only [auxiliaryLinearMap, MonoidAlgebra.of_apply, MonoidAlgebra.single_mul_single, one_mul]

  change Finsupp.mapDomain _ (Finsupp.single (τ * σ) c) =
    Finsupp.mapDomain _ (Finsupp.mapDomain _ (Finsupp.single σ c))
  simp only [Finsupp.mapDomain_single, permutationAuxiliaryTypeMap_apply_permutation, mul_inv_rev]



/-- If an element has zero image under the displayed linear map, then so does its product with every displayed permutation monomial. -/
theorem auxiliaryLinearMap_monomial_mul_eq_zero
    (v : RepresentationTheory.PartitionAuxiliary.natIndexedType n) (hv : auxiliaryLinearMap (n := n) (la := la) v = 0)
    (τ : Equiv.Perm (Fin n)) :
    auxiliaryLinearMap (n := n) (la := la) (MonoidAlgebra.of ℂ _ τ * v) = 0 := by
  rw [auxiliaryLinearMap_monomial_mul, hv, Finsupp.mapDomain_zero]


private theorem toTabloid_inv_of_rowSubgroup (g : ↥(RepresentationTheory.SymmetricGroup.PartitionAuxiliaryConstructions.auxiliaryPartitionPermutationSubgroupB n la)) :
    permutationToAuxiliaryType n la g.val⁻¹ = permutationToAuxiliaryType n la 1 := by
  rw [permutationToAuxiliaryType_eq_iff_mul_inv_mem]
  simp only [inv_one, mul_one]
  exact (RepresentationTheory.SymmetricGroup.PartitionAuxiliaryConstructions.auxiliaryPartitionPermutationSubgroupB n la).inv_mem g.prop



/-- The displayed linear map sends the indicated source element to a cardinality scalar times the single-support value at the image of the identity permutation. -/
theorem auxiliaryLinearMap_apply_specifiedElement :
    auxiliaryLinearMap (n := n) (la := la) (RepresentationTheory.SymmetricGroup.PartitionAuxiliaryConstructions.auxiliaryPartitionGroupAlgebraElementB n la) =
      (Nat.card (↥(RepresentationTheory.SymmetricGroup.PartitionAuxiliaryConstructions.auxiliaryPartitionPermutationSubgroupB n la)) : ℂ) •
        (Finsupp.single (permutationToAuxiliaryType n la 1) (1 : ℂ) :
          partitionIndexedAuxiliaryType2 n la) := by
  classical
  simp only [RepresentationTheory.SymmetricGroup.PartitionAuxiliaryConstructions.auxiliaryPartitionGroupAlgebraElementB, map_sum, auxiliaryLinearMap_monomial,
    toTabloid_inv_of_rowSubgroup]
  rw [Finset.sum_const, Finset.card_univ, ← Nat.card_eq_fintype_card,
    ← Nat.cast_smul_eq_nsmul ℂ]



/-- The indicated source element has nonzero image under the displayed linear map. -/
theorem auxiliaryLinearMap_specifiedElement_ne_zero :
    auxiliaryLinearMap (n := n) (la := la) (RepresentationTheory.SymmetricGroup.PartitionAuxiliaryConstructions.auxiliaryPartitionGroupAlgebraElementC n la) ≠ 0 := by
  classical

  rw [RepresentationTheory.SymmetricGroup.PartitionAuxiliaryConstructions.auxiliaryPartitionGroupAlgebraElementC]

  simp only [RepresentationTheory.SymmetricGroup.PartitionAuxiliaryConstructions.auxiliaryPartitionGroupAlgebraElementA, Finset.sum_mul, map_sum, smul_mul_assoc, map_smul,
    auxiliaryLinearMap_monomial_mul, auxiliaryLinearMap_apply_specifiedElement,
    Finsupp.mapDomain_smul, Finsupp.mapDomain_single, permutationAuxiliaryTypeMap_apply_permutation, one_mul]


  intro h

  have h_eval : ∀ (f : partitionIndexedAuxiliaryType2 n la), f = 0 → f (permutationToAuxiliaryType n la 1) = 0 :=
    fun f hf => by rw [hf]; rfl
  have h0 := h_eval _ h

  simp only [Finsupp.finsetSum_apply, Finsupp.smul_apply, smul_eq_mul,
    Finsupp.single_apply] at h0


  have h_filter : ∀ (q : ↥(RepresentationTheory.SymmetricGroup.PartitionAuxiliaryConstructions.auxiliaryPartitionPermutationSubgroupA n la)),
      permutationToAuxiliaryType n la q.val⁻¹ = permutationToAuxiliaryType n la 1 → q.val = 1 := by
    intro ⟨q, hq⟩ h1
    rw [permutationToAuxiliaryType_eq_iff_mul_inv_mem, inv_one, mul_one] at h1
    have := eq_one_of_mem_two_auxiliarySets n la q⁻¹ h1
      ((RepresentationTheory.SymmetricGroup.PartitionAuxiliaryConstructions.auxiliaryPartitionPermutationSubgroupA n la).inv_mem hq)
    rwa [inv_eq_one] at this

  simp only [show ∀ (q : ↥(RepresentationTheory.SymmetricGroup.PartitionAuxiliaryConstructions.auxiliaryPartitionPermutationSubgroupA n la)),
      (if permutationToAuxiliaryType n la q.val⁻¹ = permutationToAuxiliaryType n la 1 then (1 : ℂ) else 0) =
      (if q.val = 1 then 1 else 0) from fun q => by
        split_ifs with h1 h2 h2
        · rfl
        · exact absurd (h_filter q h1) h2
        · exact absurd (by simp [h2]) h1
        · rfl] at h0

  simp only [mul_ite, mul_one, mul_zero] at h0


  have h_coe : ∀ x : ↥(RepresentationTheory.SymmetricGroup.PartitionAuxiliaryConstructions.auxiliaryPartitionPermutationSubgroupA n la),
      ((↑x : Equiv.Perm (Fin n)) = 1) =
        (x = ⟨1, (RepresentationTheory.SymmetricGroup.PartitionAuxiliaryConstructions.auxiliaryPartitionPermutationSubgroupA n la).one_mem⟩) :=
    fun x => by simp only [Subtype.ext_iff]
  simp only [h_coe] at h0
  rw [Finset.sum_ite_eq'] at h0
  simp only [Finset.mem_univ, ↓reduceIte, Equiv.Perm.sign_one, Int.cast_one,
    Units.val_one, one_mul] at h0
  exact Nat.cast_ne_zero.mpr (Nat.card_pos (α := ↥(RepresentationTheory.SymmetricGroup.PartitionAuxiliaryConstructions.auxiliaryPartitionPermutationSubgroupB n la))).ne' h0





/-- If an element has zero image under the displayed linear map, then every displayed left multiple also has zero image. -/
theorem auxiliaryLinearMap_mul_eq_zero
    (v : RepresentationTheory.PartitionAuxiliary.natIndexedType n) (hv : auxiliaryLinearMap (n := n) (la := la) v = 0)
    (a : RepresentationTheory.PartitionAuxiliary.natIndexedType n) :
    auxiliaryLinearMap (n := n) (la := la) (a * v) = 0 := by
  induction a using MonoidAlgebra.induction_on with
  | hM τ => exact auxiliaryLinearMap_monomial_mul_eq_zero v hv τ
  | hadd a b ha hb => rw [add_mul, map_add, ha, hb, add_zero]
  | hsmul r a ha => rw [smul_mul_assoc, map_smul, ha, smul_zero]








/-- Within the indicated set of source elements, an element with zero image under the displayed linear map is zero. -/
theorem eq_zero_of_mem_of_auxiliaryLinearMap_eq_zero
    (v : RepresentationTheory.PartitionAuxiliary.natIndexedType n) (hv : v ∈ RepresentationTheory.PartitionAuxiliary.partitionSubmodule n la)
    (h : auxiliaryLinearMap (n := n) (la := la) v = 0) :
    v = 0 := by
  classical
  haveI := RepresentationTheory.PartitionAuxiliary.partitionSubmodule_isSimpleModule n la

  let K : Submodule (RepresentationTheory.PartitionAuxiliary.natIndexedType n) (RepresentationTheory.PartitionAuxiliary.partitionSubmodule n la) :=
    { carrier := {w | auxiliaryLinearMap (n := n) (la := la) w.val = 0}
      zero_mem' := by simp
      add_mem' := fun ha hb => by
        simp only [Set.mem_setOf_eq, Submodule.coe_add] at *
        rw [map_add, ha, hb, add_zero]
      smul_mem' := fun r w hw => by
        simp only [Set.mem_setOf_eq, SetLike.val_smul] at *
        exact auxiliaryLinearMap_mul_eq_zero w.val hw r }

  have hK_ne_top : K ≠ ⊤ := by
    intro hK_top
    apply auxiliaryLinearMap_specifiedElement_ne_zero (n := n) (la := la)
    have hc_mem : RepresentationTheory.SymmetricGroup.PartitionAuxiliaryConstructions.auxiliaryPartitionGroupAlgebraElementC n la ∈ RepresentationTheory.PartitionAuxiliary.partitionSubmodule n la :=
      Submodule.subset_span rfl
    have : (⟨RepresentationTheory.SymmetricGroup.PartitionAuxiliaryConstructions.auxiliaryPartitionGroupAlgebraElementC n la, hc_mem⟩ : RepresentationTheory.PartitionAuxiliary.partitionSubmodule n la) ∈ K := by
      rw [hK_top]; exact Submodule.mem_top
    exact this

  have hK_bot : K = ⊥ := by
    rcases (IsSimpleOrder.eq_bot_or_eq_top K) with h | h
    · exact h
    · exact absurd h hK_ne_top

  have hv_in_K : (⟨v, hv⟩ : RepresentationTheory.PartitionAuxiliary.partitionSubmodule n la) ∈ K := h
  rw [hK_bot] at hv_in_K
  exact congr_arg Subtype.val ((Submodule.mem_bot _).mp hv_in_K)









private theorem tabloidProjection_youngSymmetrizer_eq :
    auxiliaryLinearMap (n := n) (la := la) (RepresentationTheory.SymmetricGroup.PartitionAuxiliaryConstructions.auxiliaryPartitionGroupAlgebraElementC n la) =
      (Nat.card (↥(RepresentationTheory.SymmetricGroup.PartitionAuxiliaryConstructions.auxiliaryPartitionPermutationSubgroupB n la)) : ℂ) •
        permutationToAuxiliaryType2 (n := n) (la := la) 1 := by
  classical
  simp only [RepresentationTheory.SymmetricGroup.PartitionAuxiliaryConstructions.auxiliaryPartitionGroupAlgebraElementC, RepresentationTheory.SymmetricGroup.PartitionAuxiliaryConstructions.auxiliaryPartitionGroupAlgebraElementA, Finset.sum_mul, map_sum,
    smul_mul_assoc, map_smul, auxiliaryLinearMap_monomial_mul, auxiliaryLinearMap_apply_specifiedElement,
    Finsupp.mapDomain_smul, Finsupp.mapDomain_single, permutationAuxiliaryTypeMap_apply_permutation, one_mul]


  simp_rw [smul_comm (Equiv.Perm.sign _ : ℂ)]
  rw [← Finset.smul_sum]
  simp [permutationToAuxiliaryType2, mul_one]

/-- The displayed linear map sends the product of a permutation monomial and a specified source element to a cardinality scalar times the auxiliary value of the inverse permutation. -/
theorem auxiliaryLinearMap_monomial_mul_specifiedElement (σ : Equiv.Perm (Fin n)) :
    auxiliaryLinearMap (n := n) (la := la)
      (MonoidAlgebra.of ℂ _ σ * RepresentationTheory.SymmetricGroup.PartitionAuxiliaryConstructions.auxiliaryPartitionGroupAlgebraElementC n la) =
      (Nat.card (↥(RepresentationTheory.SymmetricGroup.PartitionAuxiliaryConstructions.auxiliaryPartitionPermutationSubgroupB n la)) : ℂ) •
        permutationToAuxiliaryType2 (n := n) (la := la) σ⁻¹ := by
  classical

  rw [auxiliaryLinearMap_monomial_mul, tabloidProjection_youngSymmetrizer_eq,
    Finsupp.mapDomain_smul]
  congr 1

  simp only [permutationToAuxiliaryType2]
  rw [Finsupp.mapDomain_finsetSum]
  congr 1; ext ⟨q, hq⟩
  rw [Finsupp.mapDomain_smul, Finsupp.mapDomain_single, permutationAuxiliaryTypeMap_apply_permutation, mul_one]




/-- Each displayed value of the object map belongs to the image of the indicated scalar-restricted submodule under the displayed linear map. -/
theorem objectToAuxiliaryType2_mem_mappedSubmodule
    (T : RepresentationTheory.SymmetricGroup.PartitionAuxiliaryConstructions.AuxiliaryPartitionSource n la) :
    objectToAuxiliaryType2 (n := n) (la := la) T ∈
      Submodule.map (auxiliaryLinearMap (n := n) (la := la))
        ((RepresentationTheory.PartitionAuxiliary.partitionSubmodule n la).restrictScalars ℂ) := by
  rw [Submodule.mem_map]
  refine ⟨(Nat.card (↥(RepresentationTheory.SymmetricGroup.PartitionAuxiliaryConstructions.auxiliaryPartitionPermutationSubgroupB n la)) : ℂ)⁻¹ •
    MonoidAlgebra.of ℂ _ (RepresentationTheory.Combinatorics.PartitionPermutation.associatedPermutation n la T)⁻¹ * RepresentationTheory.SymmetricGroup.PartitionAuxiliaryConstructions.auxiliaryPartitionGroupAlgebraElementC n la, ?_, ?_⟩
  ·
    rw [Submodule.restrictScalars_mem, RepresentationTheory.PartitionAuxiliary.partitionSubmodule, Submodule.mem_span_singleton]
    exact ⟨_, rfl⟩
  ·
    simp only [map_smul, smul_mul_assoc, auxiliaryLinearMap_monomial_mul_specifiedElement]
    rw [smul_smul, inv_mul_cancel₀, one_smul]
    ·
      rw [inv_inv]
      exact (permutationToAuxiliaryType2_objectPermutation T).symm
    ·
      exact Nat.cast_ne_zero.mpr (Nat.card_pos (α := ↥(RepresentationTheory.SymmetricGroup.PartitionAuxiliaryConstructions.auxiliaryPartitionPermutationSubgroupB n la))).ne'




/-- The cardinality of the displayed finite auxiliary type is bounded by the complex finrank of the indicated subtype. -/
theorem card_auxiliaryType_le_finrank :
    Fintype.card (RepresentationTheory.SymmetricGroup.PartitionAuxiliaryConstructions.AuxiliaryPartitionSource n la) ≤
      Module.finrank ℂ (RepresentationTheory.PartitionAuxiliary.partitionSubmodule n la) := by

  have hli := linearIndependent_objectToAuxiliaryType2 (n := n) (la := la)

  have hmem : ∀ T, objectToAuxiliaryType2 (n := n) (la := la) T ∈
      Submodule.map (auxiliaryLinearMap (n := n) (la := la))
        ((RepresentationTheory.PartitionAuxiliary.partitionSubmodule n la).restrictScalars ℂ) :=
    objectToAuxiliaryType2_mem_mappedSubmodule

  set S := Submodule.map (auxiliaryLinearMap (n := n) (la := la))
    ((RepresentationTheory.PartitionAuxiliary.partitionSubmodule n la).restrictScalars ℂ)
  have hli_sub : LinearIndependent ℂ (fun T => (⟨objectToAuxiliaryType2 T, hmem T⟩ : S)) := by
    apply LinearIndependent.of_comp S.subtype


    simpa only [Function.comp_def, Submodule.coe_subtype] using hli

  have h1 := hli_sub.fintype_card_le_finrank

  have h2 := Submodule.finrank_map_le (auxiliaryLinearMap (n := n) (la := la))
    ((RepresentationTheory.PartitionAuxiliary.partitionSubmodule n la).restrictScalars ℂ)

  exact h1.trans h2

end

end RepresentationTheory.Permutation.PartitionIndexedAuxiliary

/-- An auxiliary statement whose displayed formal type is unavailable. -/
alias _root_.RepresentationTheory.Permutation.PartitionIndexedAuxiliary.Auxiliary.statement019782 := _root_.RepresentationTheory.Permutation.PartitionIndexedAuxiliary.opaqueAuxiliaryTheorem
