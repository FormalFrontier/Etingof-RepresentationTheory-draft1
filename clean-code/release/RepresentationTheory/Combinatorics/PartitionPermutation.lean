/-
Copyright (c) 2026 mathlib-initiative. All rights reserved.
Released under Apache 2.0 license as described in the file LICENCE.
Authors: mathlib-initiative
-/

import Mathlib
import RepresentationTheory.Partition.YoungDiagram
import RepresentationTheory.SimpleModule.SubtypeRepresentation
import RepresentationTheory.PartitionLinearEquivBoundsAndMonoidAlgebra
import RepresentationTheory.PartitionAuxiliary




































namespace RepresentationTheory.Combinatorics.PartitionPermutation

/-- The coefficient-function coercion for a monoid algebra. -/
local instance monoidAlgebraCoeFun {R M : Type*} [Semiring R] :
    CoeFun (MonoidAlgebra R M) (fun _ => M → R) :=
  ⟨fun a => a.coeff⟩

noncomputable section






/-- The type of indices associated with a partition of a natural number. -/
abbrev PartitionIndex (n : ℕ) (la : Nat.Partition n) :=
  { c : ℕ × ℕ // c.1 < la.auxiliaryPartitionNatList.length ∧ c.2 < la.auxiliaryPartitionNatList.getD c.1 0 }




private theorem sortedParts_sum (n : ℕ) (la : Nat.Partition n) :
    la.auxiliaryPartitionNatList.sum = n := by
  have h := Multiset.sort_eq la.parts (· ≥ ·)
  have : (la.auxiliaryPartitionNatList : Multiset ℕ).sum = la.parts.sum := congrArg Multiset.sum h
  rw [Multiset.sum_coe] at this; rw [this, la.parts_sum]


/-- The selected part index of an entry below a list sum is less than the list length. -/
theorem selectedPartIndex_lt_length (parts : List ℕ) (k : ℕ) (hk : k < parts.sum) :
    RepresentationTheory.SymmetricGroup.PartitionAuxiliaryConstructions.flatIndexRow parts k < parts.length := by
  induction parts generalizing k with
  | nil => simp [List.sum_nil] at hk
  | cons p ps ih =>
    simp only [RepresentationTheory.SymmetricGroup.PartitionAuxiliaryConstructions.flatIndexRow, List.length_cons]
    split_ifs with h
    · omega
    · have : k - p < ps.sum := by simp [List.sum_cons] at hk; omega
      have := ih _ this
      omega


/-- The two list-derived coordinates of a finite partition index lie within their respective bounds. -/
theorem partitionCoordinates_lt (n : ℕ) (la : Nat.Partition n) (k : Fin n) :
    RepresentationTheory.SymmetricGroup.PartitionAuxiliaryConstructions.flatIndexRow la.auxiliaryPartitionNatList k.val < la.auxiliaryPartitionNatList.length ∧
    RepresentationTheory.SymmetricGroup.PartitionAuxiliaryConstructions.flatIndexColumn la.auxiliaryPartitionNatList k.val < la.auxiliaryPartitionNatList.getD (RepresentationTheory.SymmetricGroup.PartitionAuxiliaryConstructions.flatIndexRow la.auxiliaryPartitionNatList k.val) 0 := by
  have hsum : la.auxiliaryPartitionNatList.sum = n := sortedParts_sum n la
  have hk : k.val < la.auxiliaryPartitionNatList.sum := by omega
  exact ⟨selectedPartIndex_lt_length la.auxiliaryPartitionNatList k.val hk,
         RepresentationTheory.SymmetricGroup.PartitionAuxiliaryConstructions.flatIndexColumn_lt_rowLength la.auxiliaryPartitionNatList k.val hk⟩





/-- The partition index associated with a finite index. -/
def partitionIndexOfFin (n : ℕ) (la : Nat.Partition n) : Fin n → PartitionIndex n la :=
  fun k => ⟨(RepresentationTheory.SymmetricGroup.PartitionAuxiliaryConstructions.flatIndexRow la.auxiliaryPartitionNatList k.val, RepresentationTheory.SymmetricGroup.PartitionAuxiliaryConstructions.flatIndexColumn la.auxiliaryPartitionNatList k.val),
            partitionCoordinates_lt n la k⟩


/-- The map from finite indices to partition indices is injective. -/
theorem partitionIndexOfFin_injective (n : ℕ) (la : Nat.Partition n) :
    Function.Injective (partitionIndexOfFin n la) := by
  intro ⟨k₁, hk₁⟩ ⟨k₂, hk₂⟩ h
  simp only [partitionIndexOfFin, Subtype.mk.injEq, Prod.mk.injEq] at h
  have hsum : la.auxiliaryPartitionNatList.sum = n := sortedParts_sum n la
  apply Fin.ext
  exact RepresentationTheory.SymmetricGroup.PartitionAuxiliaryConstructions.eq_of_flatIndexRow_eq_and_column_eq la.auxiliaryPartitionNatList k₁ k₂
    (by omega) (by omega) h.1 h.2


/-- The map from finite indices to partition indices is surjective. -/
theorem partitionIndexOfFin_surjective (n : ℕ) (la : Nat.Partition n) :
    Function.Surjective (partitionIndexOfFin n la) := by
  intro ⟨⟨r, c⟩, hr, hc⟩
  have hsum : la.auxiliaryPartitionNatList.sum = n := sortedParts_sum n la
  obtain ⟨k, hk, hrow, hcol⟩ := RepresentationTheory.SymmetricGroup.PartitionAuxiliaryConstructions.exists_flatIndex_of_column_lt_rowLength la.auxiliaryPartitionNatList r c hc
  exact ⟨⟨k, by omega⟩, Subtype.ext (Prod.ext hrow hcol)⟩


/-- The equivalence between finite indices and the index type of a partition. -/
def finEquivPartitionIndex (n : ℕ) (la : Nat.Partition n) : Fin n ≃ PartitionIndex n la :=
  Equiv.ofBijective (partitionIndexOfFin n la)
    ⟨partitionIndexOfFin_injective n la, partitionIndexOfFin_surjective n la⟩











/-- The permutation associated with partition-dependent input data. -/
def associatedPermutation (n : ℕ) (la : Nat.Partition n) (T : RepresentationTheory.SymmetricGroup.PartitionAuxiliaryConstructions.AuxiliaryPartitionSource n la) :
    Equiv.Perm (Fin n) :=
  (Equiv.ofBijective T.val T.prop.1).symm.trans (finEquivPartitionIndex n la).symm


/-- The map assigning an associated permutation is injective. -/
theorem associatedPermutation_injective (n : ℕ) (la : Nat.Partition n) :
    Function.Injective (associatedPermutation n la) := by
  intro T₁ T₂ h
  have key : T₁.val = T₂.val := by
    funext c


    have h_at := Equiv.ext_iff.mp h (T₁.val c)
    simp only [associatedPermutation, Equiv.trans_apply] at h_at

    have he₁ : (Equiv.ofBijective T₁.val T₁.prop.1).symm (T₁.val c) = c :=
      (Equiv.ofBijective T₁.val T₁.prop.1).symm_apply_apply c
    rw [he₁] at h_at
    have h2 : c = (Equiv.ofBijective T₂.val T₂.prop.1).symm (T₁.val c) :=
      (finEquivPartitionIndex n la).symm.injective h_at
    set e₂ := Equiv.ofBijective T₂.val T₂.prop.1
    calc T₁.val c
        = e₂ (e₂.symm (T₁.val c)) :=
          (e₂.apply_symm_apply (T₁.val c)).symm
      _ = e₂ c := by rw [← h2]
      _ = T₂.val c := rfl
  exact Subtype.ext key









/-- An element of a target family associated with partition-dependent input data. -/
noncomputable def associatedElement (n : ℕ) (la : Nat.Partition n)
    (T : RepresentationTheory.SymmetricGroup.PartitionAuxiliaryConstructions.AuxiliaryPartitionSource n la) : RepresentationTheory.PartitionAuxiliary.natIndexedType n :=
  haveI : DecidablePred (· ∈ RepresentationTheory.SymmetricGroup.PartitionAuxiliaryConstructions.auxiliaryPartitionPermutationSubgroupA n la) := Classical.decPred _
  ∑ q : ↥(RepresentationTheory.SymmetricGroup.PartitionAuxiliaryConstructions.auxiliaryPartitionPermutationSubgroupA n la),
    ((↑(Equiv.Perm.sign q.val) : ℤ) : ℂ) •
      MonoidAlgebra.of ℂ _ ((associatedPermutation n la T)⁻¹ * q.val * associatedPermutation n la T)


/-- The associated element equals the distinguished target element when its associated permutation is the identity. -/
theorem associatedElement_eq_of_associatedPermutation_eq_one (n : ℕ) (la : Nat.Partition n)
    (T : RepresentationTheory.SymmetricGroup.PartitionAuxiliaryConstructions.AuxiliaryPartitionSource n la) (h : associatedPermutation n la T = 1) :
    associatedElement n la T = RepresentationTheory.SymmetricGroup.PartitionAuxiliaryConstructions.auxiliaryPartitionGroupAlgebraElementA n la := by
  simp only [associatedElement, RepresentationTheory.SymmetricGroup.PartitionAuxiliaryConstructions.auxiliaryPartitionGroupAlgebraElementA, h, inv_one, one_mul, mul_one,
    MonoidAlgebra.of_apply]











/-- An alternative target-family element associated with partition-dependent input data. -/
def associatedElementAlt (n : ℕ) (la : Nat.Partition n) (T : RepresentationTheory.SymmetricGroup.PartitionAuxiliaryConstructions.AuxiliaryPartitionSource n la) :
    RepresentationTheory.PartitionAuxiliary.natIndexedType n :=
  MonoidAlgebra.of ℂ _ (associatedPermutation n la T) * RepresentationTheory.SymmetricGroup.PartitionAuxiliaryConstructions.auxiliaryPartitionGroupAlgebraElementC n la





/-- The alternative associated element belongs to the distinguished subset. -/
theorem associatedElementAlt_mem (n : ℕ) (la : Nat.Partition n)
    (T : RepresentationTheory.SymmetricGroup.PartitionAuxiliaryConstructions.AuxiliaryPartitionSource n la) :
    associatedElementAlt n la T ∈ RepresentationTheory.PartitionAuxiliary.partitionSubmodule n la :=
  Submodule.smul_mem _ (MonoidAlgebra.of ℂ _ (associatedPermutation n la T))
    (Submodule.subset_span rfl)



/-- The alternative associated element equals the specified product when its associated permutation is the identity. -/
theorem associatedElementAlt_eq_mul_of_associatedPermutation_eq_one (n : ℕ) (la : Nat.Partition n)
    (T₀ : RepresentationTheory.SymmetricGroup.PartitionAuxiliaryConstructions.AuxiliaryPartitionSource n la)
    (hT₀ : associatedPermutation n la T₀ = 1) :
    associatedElementAlt n la T₀ = RepresentationTheory.SymmetricGroup.PartitionAuxiliaryConstructions.auxiliaryPartitionGroupAlgebraElementA n la * RepresentationTheory.SymmetricGroup.PartitionAuxiliaryConstructions.auxiliaryPartitionGroupAlgebraElementB n la := by
  simp [associatedElementAlt, RepresentationTheory.SymmetricGroup.PartitionAuxiliaryConstructions.auxiliaryPartitionGroupAlgebraElementC, hT₀, MonoidAlgebra.of_apply,
    show (MonoidAlgebra.single (1 : Equiv.Perm (Fin n)) (1 : ℂ)) = 1 from rfl]




/-- A member of a distinguished subset associated with partition-dependent input data. -/
def associatedMember (n : ℕ) (la : Nat.Partition n) (T : RepresentationTheory.SymmetricGroup.PartitionAuxiliaryConstructions.AuxiliaryPartitionSource n la) :
    RepresentationTheory.PartitionAuxiliary.partitionSubmodule n la :=
  ⟨associatedElementAlt n la T, associatedElementAlt_mem n la T⟩




/-- An alternative member of a distinguished subset associated with partition-dependent input data. -/
def associatedMemberAlt (n : ℕ) (la : Nat.Partition n) :
    RepresentationTheory.SymmetricGroup.PartitionAuxiliaryConstructions.AuxiliaryPartitionSource n la → RepresentationTheory.PartitionAuxiliary.partitionSubmodule n la :=
  associatedMember n la





private theorem row_col_inter_trivial' (n : ℕ) (la : Nat.Partition n)
    (σ : Equiv.Perm (Fin n)) (hrow : σ ∈ RepresentationTheory.SymmetricGroup.PartitionAuxiliaryConstructions.auxiliaryPartitionPermutationSubgroupB n la) (hcol : σ ∈ RepresentationTheory.SymmetricGroup.PartitionAuxiliaryConstructions.auxiliaryPartitionPermutationSubgroupA n la) :
    σ = 1 := by
  ext k
  simp only [Equiv.Perm.one_apply]
  have hsum : la.auxiliaryPartitionNatList.sum = n := sortedParts_sum n la
  have hk : k.val < la.auxiliaryPartitionNatList.sum := by rw [hsum]; exact k.isLt
  have hσk : (σ k).val < la.auxiliaryPartitionNatList.sum := by rw [hsum]; exact (σ k).isLt
  exact RepresentationTheory.SymmetricGroup.PartitionAuxiliaryConstructions.eq_of_flatIndexRow_eq_and_column_eq la.auxiliaryPartitionNatList
    (σ k).val k.val hσk hk (hrow k) (hcol k)


private lemma columnAntisymmetrizer_apply_not_mem' (n : ℕ) (la : Nat.Partition n)
    (σ : Equiv.Perm (Fin n)) (hσ : σ ∉ RepresentationTheory.SymmetricGroup.PartitionAuxiliaryConstructions.auxiliaryPartitionPermutationSubgroupA n la) :
    (RepresentationTheory.SymmetricGroup.PartitionAuxiliaryConstructions.auxiliaryPartitionGroupAlgebraElementA n la : RepresentationTheory.PartitionAuxiliary.natIndexedType n) σ = 0 := by
  classical
  simp only [RepresentationTheory.SymmetricGroup.PartitionAuxiliaryConstructions.auxiliaryPartitionGroupAlgebraElementA, MonoidAlgebra.of_apply]
  change (∑ q : ↥(RepresentationTheory.SymmetricGroup.PartitionAuxiliaryConstructions.auxiliaryPartitionPermutationSubgroupA n la),
    ((↑(↑(Equiv.Perm.sign (q : Equiv.Perm (Fin n))) : ℤ) : ℂ) •
      MonoidAlgebra.single (q : Equiv.Perm (Fin n)) (1 : ℂ))).coeff σ = 0
  rw [MonoidAlgebra.coeff_sum]
  change (Finsupp.applyAddHom σ) (∑ q : ↥(RepresentationTheory.SymmetricGroup.PartitionAuxiliaryConstructions.auxiliaryPartitionPermutationSubgroupA n la),
    (((↑(↑(Equiv.Perm.sign (q : Equiv.Perm (Fin n))) : ℤ) : ℂ) •
      MonoidAlgebra.single (q : Equiv.Perm (Fin n)) (1 : ℂ))).coeff) = 0
  rw [map_sum]
  exact Fintype.sum_eq_zero _ (fun q => by
  change ((↑(↑(Equiv.Perm.sign (q : Equiv.Perm (Fin n))) : ℤ) : ℂ) •
    (Finsupp.single (q : Equiv.Perm (Fin n)) (1 : ℂ))) σ = 0
  rw [Finsupp.smul_apply, smul_eq_mul, Finsupp.single_apply]
  split_ifs with h
  · exact absurd (h ▸ q.prop) hσ
  · ring)


private lemma rowSymmetrizer_apply_not_mem' (n : ℕ) (la : Nat.Partition n)
    (σ : Equiv.Perm (Fin n)) (hσ : σ ∉ RepresentationTheory.SymmetricGroup.PartitionAuxiliaryConstructions.auxiliaryPartitionPermutationSubgroupB n la) :
    (RepresentationTheory.SymmetricGroup.PartitionAuxiliaryConstructions.auxiliaryPartitionGroupAlgebraElementB n la : RepresentationTheory.PartitionAuxiliary.natIndexedType n) σ = 0 := by
  classical
  simp only [RepresentationTheory.SymmetricGroup.PartitionAuxiliaryConstructions.auxiliaryPartitionGroupAlgebraElementB, MonoidAlgebra.of_apply]
  change (∑ p : ↥(RepresentationTheory.SymmetricGroup.PartitionAuxiliaryConstructions.auxiliaryPartitionPermutationSubgroupB n la),
    MonoidAlgebra.single (p : Equiv.Perm (Fin n)) (1 : ℂ)).coeff σ = 0
  rw [MonoidAlgebra.coeff_sum]
  change (Finsupp.applyAddHom σ) (∑ p : ↥(RepresentationTheory.SymmetricGroup.PartitionAuxiliaryConstructions.auxiliaryPartitionPermutationSubgroupB n la),
    (MonoidAlgebra.single (p : Equiv.Perm (Fin n)) (1 : ℂ)).coeff) = 0
  rw [map_sum]
  exact Fintype.sum_eq_zero _ (fun p => by
    simp only [Finsupp.applyAddHom_apply]
    rw [MonoidAlgebra.coeff_single, Finsupp.single_apply]
    split_ifs with h
    · exact absurd (h ▸ p.prop) hσ
    · rfl)














/-- Every permutation with nonzero coefficient factors as a product of elements from the two specified subsets. -/
theorem exists_mem_mul_mem_eq_of_coeff_ne_zero (n : ℕ) (la : Nat.Partition n)
    (g : Equiv.Perm (Fin n))
    (hg : (RepresentationTheory.SymmetricGroup.PartitionAuxiliaryConstructions.auxiliaryPartitionGroupAlgebraElementC n la : RepresentationTheory.PartitionAuxiliary.natIndexedType n) g ≠ 0) :
    ∃ q ∈ RepresentationTheory.SymmetricGroup.PartitionAuxiliaryConstructions.auxiliaryPartitionPermutationSubgroupA n la, ∃ p ∈ RepresentationTheory.SymmetricGroup.PartitionAuxiliaryConstructions.auxiliaryPartitionPermutationSubgroupB n la,
      g = q * p := by
  classical
  change (RepresentationTheory.SymmetricGroup.PartitionAuxiliaryConstructions.auxiliaryPartitionGroupAlgebraElementA n la * RepresentationTheory.SymmetricGroup.PartitionAuxiliaryConstructions.auxiliaryPartitionGroupAlgebraElementB n la) g ≠ 0 at hg
  have hmem : g ∈ (RepresentationTheory.SymmetricGroup.PartitionAuxiliaryConstructions.auxiliaryPartitionGroupAlgebraElementA n la * RepresentationTheory.SymmetricGroup.PartitionAuxiliaryConstructions.auxiliaryPartitionGroupAlgebraElementB n la).coeff.support :=
    Finsupp.mem_support_iff.mpr hg
  have hmem' := MonoidAlgebra.support_coeff_mul_subset
    (RepresentationTheory.SymmetricGroup.PartitionAuxiliaryConstructions.auxiliaryPartitionGroupAlgebraElementA n la) (RepresentationTheory.SymmetricGroup.PartitionAuxiliaryConstructions.auxiliaryPartitionGroupAlgebraElementB n la) hmem
  obtain ⟨q', hq'_mem, p', hp'_mem, hg_eq⟩ := Finset.mem_mul.mp hmem'
  have hq'_col : q' ∈ RepresentationTheory.SymmetricGroup.PartitionAuxiliaryConstructions.auxiliaryPartitionPermutationSubgroupA n la := by
    by_contra h_not
    exact (Finsupp.mem_support_iff.mp hq'_mem)
      (columnAntisymmetrizer_apply_not_mem' n la q' h_not)
  have hp'_row : p' ∈ RepresentationTheory.SymmetricGroup.PartitionAuxiliaryConstructions.auxiliaryPartitionPermutationSubgroupB n la := by
    by_contra h_not
    exact (Finsupp.mem_support_iff.mp hp'_mem)
      (rowSymmetrizer_apply_not_mem' n la p' h_not)
  exact ⟨q', hq'_col, p', hp'_row, hg_eq.symm⟩


/-- The coefficient at a product of elements from the specified subsets equals the sign of the first factor. -/
theorem coeff_mul_eq_sign_of_mem (n : ℕ) (la : Nat.Partition n)
    (q : Equiv.Perm (Fin n)) (hq : q ∈ RepresentationTheory.SymmetricGroup.PartitionAuxiliaryConstructions.auxiliaryPartitionPermutationSubgroupA n la)
    (p : Equiv.Perm (Fin n)) (hp : p ∈ RepresentationTheory.SymmetricGroup.PartitionAuxiliaryConstructions.auxiliaryPartitionPermutationSubgroupB n la) :
    (RepresentationTheory.SymmetricGroup.PartitionAuxiliaryConstructions.auxiliaryPartitionGroupAlgebraElementC n la : RepresentationTheory.PartitionAuxiliary.natIndexedType n) (q * p) =
      (↑(↑(Equiv.Perm.sign q) : ℤ) : ℂ) := by
  classical


  change (RepresentationTheory.SymmetricGroup.PartitionAuxiliaryConstructions.auxiliaryPartitionGroupAlgebraElementA n la * RepresentationTheory.SymmetricGroup.PartitionAuxiliaryConstructions.auxiliaryPartitionGroupAlgebraElementB n la) (q * p) = _




  have heval : (RepresentationTheory.SymmetricGroup.PartitionAuxiliaryConstructions.auxiliaryPartitionGroupAlgebraElementA n la * RepresentationTheory.SymmetricGroup.PartitionAuxiliaryConstructions.auxiliaryPartitionGroupAlgebraElementB n la) (q * p) =
      ∑ q' : ↥(RepresentationTheory.SymmetricGroup.PartitionAuxiliaryConstructions.auxiliaryPartitionPermutationSubgroupA n la),
        ((↑(↑(Equiv.Perm.sign q'.val) : ℤ) : ℂ) *
          (RepresentationTheory.SymmetricGroup.PartitionAuxiliaryConstructions.auxiliaryPartitionGroupAlgebraElementB n la : RepresentationTheory.PartitionAuxiliary.natIndexedType n) (q'.val⁻¹ * (q * p))) := by
    unfold RepresentationTheory.SymmetricGroup.PartitionAuxiliaryConstructions.auxiliaryPartitionGroupAlgebraElementA
    simp only [MonoidAlgebra.of_apply, Finset.sum_mul]
    change (∑ q' : ↥(RepresentationTheory.SymmetricGroup.PartitionAuxiliaryConstructions.auxiliaryPartitionPermutationSubgroupA n la),
      (((↑(↑(Equiv.Perm.sign (q' : Equiv.Perm (Fin n))) : ℤ) : ℂ) •
        MonoidAlgebra.single (q' : Equiv.Perm (Fin n)) (1 : ℂ)) *
          RepresentationTheory.SymmetricGroup.PartitionAuxiliaryConstructions.auxiliaryPartitionGroupAlgebraElementB n la)).coeff (q * p) =
        ∑ q' : ↥(RepresentationTheory.SymmetricGroup.PartitionAuxiliaryConstructions.auxiliaryPartitionPermutationSubgroupA n la),
          ((↑(↑(Equiv.Perm.sign q'.val) : ℤ) : ℂ) *
            (RepresentationTheory.SymmetricGroup.PartitionAuxiliaryConstructions.auxiliaryPartitionGroupAlgebraElementB n la : RepresentationTheory.PartitionAuxiliary.natIndexedType n) (q'.val⁻¹ * (q * p)))
    rw [MonoidAlgebra.coeff_sum]
    change (Finsupp.applyAddHom (q * p))
        (∑ q' : ↥(RepresentationTheory.SymmetricGroup.PartitionAuxiliaryConstructions.auxiliaryPartitionPermutationSubgroupA n la),
          ((((↑(↑(Equiv.Perm.sign (q' : Equiv.Perm (Fin n))) : ℤ) : ℂ) •
            MonoidAlgebra.single (q' : Equiv.Perm (Fin n)) (1 : ℂ)) *
              RepresentationTheory.SymmetricGroup.PartitionAuxiliaryConstructions.auxiliaryPartitionGroupAlgebraElementB n la)).coeff) = _
    rw [map_sum]
    apply Finset.sum_congr rfl
    intro q' _
    rw [Algebra.smul_mul_assoc]
    simp [MonoidAlgebra.single_mul_apply]
  rw [heval]

  rw [Finset.sum_eq_single (⟨q, hq⟩ : ↥(RepresentationTheory.SymmetricGroup.PartitionAuxiliaryConstructions.auxiliaryPartitionPermutationSubgroupA n la))]
  ·
    simp only [inv_mul_cancel_left]
    rw [show (RepresentationTheory.SymmetricGroup.PartitionAuxiliaryConstructions.auxiliaryPartitionGroupAlgebraElementB n la : RepresentationTheory.PartitionAuxiliary.natIndexedType n) p = 1 from by
      simp only [RepresentationTheory.SymmetricGroup.PartitionAuxiliaryConstructions.auxiliaryPartitionGroupAlgebraElementB, MonoidAlgebra.of_apply]
      change (∑ p' : ↥(RepresentationTheory.SymmetricGroup.PartitionAuxiliaryConstructions.auxiliaryPartitionPermutationSubgroupB n la),
        MonoidAlgebra.single (p' : Equiv.Perm (Fin n)) (1 : ℂ)).coeff p = 1
      rw [MonoidAlgebra.coeff_sum]
      change (Finsupp.applyAddHom p) (∑ p' : ↥(RepresentationTheory.SymmetricGroup.PartitionAuxiliaryConstructions.auxiliaryPartitionPermutationSubgroupB n la),
        (MonoidAlgebra.single (p' : Equiv.Perm (Fin n)) (1 : ℂ)).coeff) = 1
      rw [map_sum]
      rw [Finset.sum_eq_single (⟨p, hp⟩ : ↥(RepresentationTheory.SymmetricGroup.PartitionAuxiliaryConstructions.auxiliaryPartitionPermutationSubgroupB n la))]
      · simp
      · intro ⟨p', _⟩ _ hne
        simp only [Finsupp.applyAddHom_apply]
        rw [MonoidAlgebra.coeff_single, Finsupp.single_apply,
          if_neg (fun h => hne (Subtype.ext h))]
      · intro h; exact absurd (Finset.mem_univ _) h]
    ring
  ·
    intro ⟨q', hq'⟩ _ hne
    suffices h : (RepresentationTheory.SymmetricGroup.PartitionAuxiliaryConstructions.auxiliaryPartitionGroupAlgebraElementB n la : RepresentationTheory.PartitionAuxiliary.natIndexedType n) (q'⁻¹ * (q * p)) = 0 by
      rw [h, mul_zero]
    simp only [RepresentationTheory.SymmetricGroup.PartitionAuxiliaryConstructions.auxiliaryPartitionGroupAlgebraElementB, MonoidAlgebra.of_apply]
    change (∑ p' : ↥(RepresentationTheory.SymmetricGroup.PartitionAuxiliaryConstructions.auxiliaryPartitionPermutationSubgroupB n la),
      MonoidAlgebra.single (p' : Equiv.Perm (Fin n)) (1 : ℂ)).coeff
        (q'⁻¹ * (q * p)) = 0
    rw [MonoidAlgebra.coeff_sum]
    change (Finsupp.applyAddHom (q'⁻¹ * (q * p)))
      (∑ p' : ↥(RepresentationTheory.SymmetricGroup.PartitionAuxiliaryConstructions.auxiliaryPartitionPermutationSubgroupB n la),
        (MonoidAlgebra.single (p' : Equiv.Perm (Fin n)) (1 : ℂ)).coeff) = 0
    rw [map_sum]
    apply Fintype.sum_eq_zero
    intro ⟨p', hp'⟩
    simp only [Finsupp.applyAddHom_apply]
    rw [MonoidAlgebra.coeff_single, Finsupp.single_apply]
    rw [if_neg]
    intro heq

    have : q'⁻¹ * q = p' * p⁻¹ := by
      have h : p' = q'⁻¹ * (q * p) := heq
      calc q'⁻¹ * q = q'⁻¹ * (q * p) * p⁻¹ := by group
        _ = p' * p⁻¹ := by rw [← h]
    have hqp_row : q'⁻¹ * q ∈ RepresentationTheory.SymmetricGroup.PartitionAuxiliaryConstructions.auxiliaryPartitionPermutationSubgroupB n la := by
      rw [this]; exact (RepresentationTheory.SymmetricGroup.PartitionAuxiliaryConstructions.auxiliaryPartitionPermutationSubgroupB n la).mul_mem hp' ((RepresentationTheory.SymmetricGroup.PartitionAuxiliaryConstructions.auxiliaryPartitionPermutationSubgroupB n la).inv_mem hp)
    have hqp_col : q'⁻¹ * q ∈ RepresentationTheory.SymmetricGroup.PartitionAuxiliaryConstructions.auxiliaryPartitionPermutationSubgroupA n la :=
      (RepresentationTheory.SymmetricGroup.PartitionAuxiliaryConstructions.auxiliaryPartitionPermutationSubgroupA n la).mul_mem ((RepresentationTheory.SymmetricGroup.PartitionAuxiliaryConstructions.auxiliaryPartitionPermutationSubgroupA n la).inv_mem hq') hq
    exact hne (Subtype.ext (inv_mul_eq_one.mp
      (row_col_inter_trivial' n la _ hqp_row hqp_col)))
  · intro h; exact absurd (Finset.mem_univ _) h


private lemma youngSymmetrizer_one_coeff (n : ℕ) (la : Nat.Partition n) :
    (RepresentationTheory.SymmetricGroup.PartitionAuxiliaryConstructions.auxiliaryPartitionGroupAlgebraElementC n la : RepresentationTheory.PartitionAuxiliary.natIndexedType n) 1 = 1 := by
  have h := coeff_mul_eq_sign_of_mem n la 1 (RepresentationTheory.SymmetricGroup.PartitionAuxiliaryConstructions.auxiliaryPartitionPermutationSubgroupA n la).one_mem
    1 (RepresentationTheory.SymmetricGroup.PartitionAuxiliaryConstructions.auxiliaryPartitionPermutationSubgroupB n la).one_mem
  simpa [Equiv.Perm.sign_one] using h









private lemma youngSymmetrizer_rowPerm_coeff (n : ℕ) (la : Nat.Partition n)
    (p : Equiv.Perm (Fin n)) (hp : p ∈ RepresentationTheory.SymmetricGroup.PartitionAuxiliaryConstructions.auxiliaryPartitionPermutationSubgroupB n la) :
    (RepresentationTheory.SymmetricGroup.PartitionAuxiliaryConstructions.auxiliaryPartitionGroupAlgebraElementC n la : RepresentationTheory.PartitionAuxiliary.natIndexedType n) p = 1 := by
  have h := coeff_mul_eq_sign_of_mem n la 1 (RepresentationTheory.SymmetricGroup.PartitionAuxiliaryConstructions.auxiliaryPartitionPermutationSubgroupA n la).one_mem p hp
  simpa [Equiv.Perm.sign_one] using h




















/-- A permutation with nonzero coefficient in the alternative associated element admits the specified three-factor decomposition. -/
theorem exists_factorization_of_associatedElementAlt_coeff_ne_zero (n : ℕ) (la : Nat.Partition n)
    (T₂ : RepresentationTheory.SymmetricGroup.PartitionAuxiliaryConstructions.AuxiliaryPartitionSource n la) (σ : Equiv.Perm (Fin n))
    (hne : (associatedElementAlt n la T₂ : RepresentationTheory.PartitionAuxiliary.natIndexedType n) σ ≠ 0) :
    ∃ q ∈ RepresentationTheory.SymmetricGroup.PartitionAuxiliaryConstructions.auxiliaryPartitionPermutationSubgroupA n la, ∃ p ∈ RepresentationTheory.SymmetricGroup.PartitionAuxiliaryConstructions.auxiliaryPartitionPermutationSubgroupB n la,
      σ = associatedPermutation n la T₂ * q * p := by
  classical
  set τ := associatedPermutation n la T₂

  have hne' : (RepresentationTheory.SymmetricGroup.PartitionAuxiliaryConstructions.auxiliaryPartitionGroupAlgebraElementC n la : RepresentationTheory.PartitionAuxiliary.natIndexedType n) (τ⁻¹ * σ) ≠ 0 := by
    simp only [associatedElementAlt, MonoidAlgebra.of_apply] at hne
    rwa [MonoidAlgebra.single_mul_apply, one_mul] at hne

  obtain ⟨q, hq, p, hp, h_eq⟩ := exists_mem_mul_mem_eq_of_coeff_ne_zero n la (τ⁻¹ * σ) hne'
  refine ⟨q, hq, p, hp, ?_⟩
  have : σ = τ * (τ⁻¹ * σ) := by group
  rw [this, h_eq, mul_assoc]













private theorem orderEmbOfFin_lt_of_injective_lt [LinearOrder α]
    {A B : Finset α} {m : ℕ} (hA : A.card = m) (hB : B.card = m)
    (f : Fin m → α) (hfA : ∀ i, f i ∈ A) (hf_inj : Function.Injective f)
    (hlt : ∀ i, f i < B.orderEmbOfFin hB i) (c : Fin m) :
    A.orderEmbOfFin hA c < B.orderEmbOfFin hB c := by
  by_contra hge
  push Not at hge

  set β := B.orderEmbOfFin hB c

  have above_c : ∀ j : Fin m, β ≤ f j → c < j := by
    intro j hfj
    have h1 : β < B.orderEmbOfFin hB j := lt_of_le_of_lt hfj (hlt j)
    exact (B.orderEmbOfFin hB).lt_iff_lt.mp h1

  have hi_sub : Finset.univ.filter (fun j : Fin m => β ≤ f j) ⊆ Finset.Ioi c := by
    intro j hj
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hj
    exact Finset.mem_Ioi.mpr (above_c j hj)

  have lo_inj : (Finset.univ.filter (fun j : Fin m => f j < β)).card ≤
      (A.filter (· < β)).card := by
    apply Finset.card_le_card_of_injOn f
    · intro j hj
      simp only [Finset.mem_coe, Finset.mem_filter, Finset.mem_univ, true_and] at hj
      exact Finset.mem_filter.mpr ⟨hfA j, hj⟩
    · exact Set.InjOn.mono (Set.subset_univ _) (Function.Injective.injOn hf_inj)


  have filter_le_c : (A.filter (· < β)).card ≤ c.val := by
    have sub : A.filter (· < β) ⊆ A.filter (· < A.orderEmbOfFin hA c) := by
      apply Finset.monotone_filter_right A
      intro a _ ha; exact lt_of_lt_of_le ha hge
    have hsub : A.filter (· < A.orderEmbOfFin hA c) ⊆
        (Finset.Iio c).image (A.orderEmbOfFin hA) := by
      intro a ha
      rw [Finset.mem_filter] at ha
      have ⟨ha_mem, ha_lt⟩ := ha
      have ha_range : a ∈ Set.range (A.orderEmbOfFin hA) := by
        rw [Finset.range_orderEmbOfFin]; exact ha_mem
      obtain ⟨j, rfl⟩ := ha_range
      exact Finset.mem_image.mpr ⟨j, Finset.mem_Iio.mpr
        ((A.orderEmbOfFin hA).lt_iff_lt.mp ha_lt), rfl⟩
    calc (A.filter (· < β)).card
        ≤ (A.filter (· < A.orderEmbOfFin hA c)).card := Finset.card_le_card sub
      _ ≤ ((Finset.Iio c).image (A.orderEmbOfFin hA)).card := Finset.card_le_card hsub
      _ ≤ (Finset.Iio c).card := Finset.card_image_le
      _ = c.val := @Fin.card_Iio m c

  have sum_eq : (Finset.univ.filter (fun j : Fin m => f j < β)).card +
      (Finset.univ.filter (fun j : Fin m => ¬ f j < β)).card = m := by
    have := @Finset.card_filter_add_card_filter_not _ (Finset.univ : Finset (Fin m))
      (fun j : Fin m => f j < β) _ _
    rwa [Finset.card_univ, Fintype.card_fin] at this
  have hi_card : (Finset.univ.filter (fun j : Fin m => ¬ f j < β)).card ≤ m - 1 - c.val := by
    calc (Finset.univ.filter (fun j : Fin m => ¬ f j < β)).card
        ≤ (Finset.Ioi c).card := by
          apply Finset.card_le_card
          intro j hj
          simp only [Finset.mem_filter, Finset.mem_univ, true_and, not_lt] at hj
          exact Finset.mem_Ioi.mpr (above_c j hj)
      _ = m - 1 - c.val := @Fin.card_Ioi m c
  omega





private theorem youngSymmetrizer_mul_of_row' (n : ℕ) (la : Nat.Partition n)
    (p : Equiv.Perm (Fin n)) (hp : p ∈ RepresentationTheory.SymmetricGroup.PartitionAuxiliaryConstructions.auxiliaryPartitionPermutationSubgroupB n la) :
    RepresentationTheory.SymmetricGroup.PartitionAuxiliaryConstructions.auxiliaryPartitionGroupAlgebraElementC n la * MonoidAlgebra.of ℂ _ p = RepresentationTheory.SymmetricGroup.PartitionAuxiliaryConstructions.auxiliaryPartitionGroupAlgebraElementC n la := by
  unfold RepresentationTheory.SymmetricGroup.PartitionAuxiliaryConstructions.auxiliaryPartitionGroupAlgebraElementC
  rw [mul_assoc, RepresentationTheory.SymmetricGroup.PartitionGroupAlgebra.mul_perm_eq_self_of_mem p hp]


/-- A natural-number statistic of a permutation relative to a partition. -/
def partitionPermutationStatistic (n : ℕ) (la : Nat.Partition n)
    (σ : Equiv.Perm (Fin n)) : ℕ :=
  (Finset.univ.filter fun pp : Fin n × Fin n =>
    RepresentationTheory.SymmetricGroup.PartitionAuxiliaryConstructions.flatIndexColumn la.auxiliaryPartitionNatList pp.1.val = RepresentationTheory.SymmetricGroup.PartitionAuxiliaryConstructions.flatIndexColumn la.auxiliaryPartitionNatList pp.2.val ∧
    RepresentationTheory.SymmetricGroup.PartitionAuxiliaryConstructions.flatIndexRow la.auxiliaryPartitionNatList pp.1.val < RepresentationTheory.SymmetricGroup.PartitionAuxiliaryConstructions.flatIndexRow la.auxiliaryPartitionNatList pp.2.val ∧
    σ.symm pp.2 < σ.symm pp.1).card


/-- An auxiliary partition-dependent condition on a permutation. -/
def PermutationCondition (n : ℕ) (la : Nat.Partition n)
    (σ : Equiv.Perm (Fin n)) : Prop :=
  ∀ p₁ p₂ : Fin n,
    RepresentationTheory.SymmetricGroup.PartitionAuxiliaryConstructions.flatIndexColumn la.auxiliaryPartitionNatList p₁.val = RepresentationTheory.SymmetricGroup.PartitionAuxiliaryConstructions.flatIndexColumn la.auxiliaryPartitionNatList p₂.val →
    RepresentationTheory.SymmetricGroup.PartitionAuxiliaryConstructions.flatIndexRow la.auxiliaryPartitionNatList p₁.val < RepresentationTheory.SymmetricGroup.PartitionAuxiliaryConstructions.flatIndexRow la.auxiliaryPartitionNatList p₂.val →
    σ.symm p₁ < σ.symm p₂















/-- A permutation satisfying the auxiliary condition factors through a specified subset element and an associated permutation. -/
theorem exists_factorization_of_permutationCondition (n : ℕ) (la : Nat.Partition n)
    (σ : Equiv.Perm (Fin n)) (hcs : PermutationCondition n la σ) :
    ∃ T : RepresentationTheory.SymmetricGroup.PartitionAuxiliaryConstructions.AuxiliaryPartitionSource n la,
      ∃ p ∈ RepresentationTheory.SymmetricGroup.PartitionAuxiliaryConstructions.auxiliaryPartitionPermutationSubgroupB n la, σ = p * associatedPermutation n la T := by
  classical
  set parts := la.auxiliaryPartitionNatList with parts_def
  have hps : parts.sum = n := sortedParts_sum n la

  let rowPositions (r : ℕ) : Finset (Fin n) :=
    Finset.univ.filter (fun pos => RepresentationTheory.SymmetricGroup.PartitionAuxiliaryConstructions.flatIndexRow parts pos.val = r)

  let rowEntries (r : ℕ) : Finset (Fin n) := (rowPositions r).image σ.symm

  have σ_inj_on_row (r : ℕ) : Set.InjOn σ.symm ↑(rowPositions r) :=
    Set.InjOn.mono (Set.subset_univ _) (Equiv.injective σ.symm).injOn

  have rowEnt_card : ∀ r : ℕ, r < parts.length →
      (rowEntries r).card = parts.getD r 0 := by
    intro r hr; rw [Finset.card_image_of_injOn (σ_inj_on_row r)]
    set S := rowPositions r
    set w := parts.getD r 0

    have h_inj : Set.InjOn (fun pos : Fin n => RepresentationTheory.SymmetricGroup.PartitionAuxiliaryConstructions.flatIndexColumn parts pos.val) ↑S := by
      intro ⟨a, _⟩ ha ⟨b, _⟩ hb heq
      simp only [S, rowPositions, Finset.mem_coe, Finset.mem_filter,
        Finset.mem_univ, true_and] at ha hb
      exact Fin.ext (RepresentationTheory.SymmetricGroup.PartitionAuxiliaryConstructions.eq_of_flatIndexRow_eq_and_column_eq parts a b
        (by omega) (by omega) (ha.trans hb.symm) heq)
    have h_range : ∀ pos ∈ S, RepresentationTheory.SymmetricGroup.PartitionAuxiliaryConstructions.flatIndexColumn parts pos.val ∈ Finset.range w := by
      intro pos hpos
      simp only [S, rowPositions, Finset.mem_filter, Finset.mem_univ, true_and] at hpos
      have := RepresentationTheory.SymmetricGroup.PartitionAuxiliaryConstructions.flatIndexColumn_lt_rowLength parts pos.val (by omega)
      rw [hpos] at this; exact Finset.mem_range.mpr this

    have h_surj : Finset.range w ⊆ (S.image (fun pos : Fin n => RepresentationTheory.SymmetricGroup.PartitionAuxiliaryConstructions.flatIndexColumn parts pos.val)) := by
      intro c hc
      rw [Finset.mem_range] at hc
      obtain ⟨k, hk, hrow, hcol⟩ := RepresentationTheory.SymmetricGroup.PartitionAuxiliaryConstructions.exists_flatIndex_of_column_lt_rowLength parts r c hc
      exact Finset.mem_image.mpr ⟨⟨k, by omega⟩,
        Finset.mem_filter.mpr ⟨Finset.mem_univ _, hrow⟩, hcol⟩

    calc S.card = (S.image (fun pos : Fin n => RepresentationTheory.SymmetricGroup.PartitionAuxiliaryConstructions.flatIndexColumn parts pos.val)).card :=
          (Finset.card_image_of_injOn h_inj).symm
      _ = (Finset.range w).card := by
          apply le_antisymm
          · exact Finset.card_le_card (Finset.image_subset_iff.mpr (fun pos hp => h_range pos hp))
          · exact Finset.card_le_card h_surj
      _ = w := Finset.card_range w

  let T_fun : PartitionIndex n la → Fin n := fun cell =>
    (rowEntries cell.val.1).orderEmbOfFin (rowEnt_card cell.val.1 cell.prop.1)
      ⟨cell.val.2, by have := cell.prop.2; omega⟩

  have T_inj : Function.Injective T_fun := by
    intro ⟨⟨r₁, c₁⟩, hr₁, hc₁⟩ ⟨⟨r₂, c₂⟩, hr₂, hc₂⟩ h
    simp only [T_fun] at h
    by_cases hr : r₁ = r₂
    · subst hr
      have hinj := ((rowEntries r₁).orderEmbOfFin (rowEnt_card r₁ hr₁)).injective
      have := Fin.mk.inj (hinj h)
      exact Subtype.ext (Prod.ext rfl this)
    · exfalso

      have h1 := Finset.orderEmbOfFin_mem (rowEntries r₁) (rowEnt_card r₁ hr₁) ⟨c₁, by omega⟩
      have h2 := Finset.orderEmbOfFin_mem (rowEntries r₂) (rowEnt_card r₂ hr₂) ⟨c₂, by omega⟩


      have h1' : (rowEntries r₂).orderEmbOfFin (rowEnt_card r₂ hr₂)
          ⟨c₂, by omega⟩ ∈ rowEntries r₁ := h ▸ h1

      obtain ⟨pos₁, hpos₁, hv₁⟩ := Finset.mem_image.mp h1'
      obtain ⟨pos₂, hpos₂, hv₂⟩ := Finset.mem_image.mp h2

      have := σ.symm.injective (hv₁.trans hv₂.symm)
      rw [this] at hpos₁
      exact hr ((Finset.mem_filter.mp hpos₁).2.symm.trans (Finset.mem_filter.mp hpos₂).2)

  have T_surj : Function.Surjective T_fun := by
    have h_card : Fintype.card (PartitionIndex n la) = Fintype.card (Fin n) :=
      Fintype.card_of_bijective (finEquivPartitionIndex n la).bijective |>.symm
    exact ((Fintype.bijective_iff_injective_and_card T_fun).mpr ⟨T_inj, h_card⟩).2

  have T_row_inc : ∀ c₁ c₂ : PartitionIndex n la,
      c₁.val.1 = c₂.val.1 → c₁.val.2 < c₂.val.2 → T_fun c₁ < T_fun c₂ := by
    intro ⟨⟨r₁, col₁⟩, hr₁, hc₁⟩ ⟨⟨r₂, col₂⟩, hr₂, hc₂⟩ hrow hcol
    simp only at hrow hcol; subst hrow
    exact ((rowEntries r₁).orderEmbOfFin (rowEnt_card r₁ hr₁)).strictMono (by omega)





  have parts_descending : ∀ r₁ r₂ : ℕ, r₁ < r₂ → r₂ < parts.length →
      parts.getD r₂ 0 ≤ parts.getD r₁ 0 := by
    intro r₁ r₂ hr₁₂ hr₂
    have hsorted : parts.Pairwise (· ≥ ·) := la.parts.pairwise_sort (· ≥ ·)
    have hi : r₁ < parts.length := by omega
    rw [List.getD_eq_getElem (hn := hr₂), List.getD_eq_getElem (hn := hi)]
    exact List.pairwise_iff_get.mp hsorted ⟨r₁, hi⟩ ⟨r₂, hr₂⟩ hr₁₂
  have T_col_inc : ∀ c₁ c₂ : PartitionIndex n la,
      c₁.val.2 = c₂.val.2 → c₁.val.1 < c₂.val.1 → T_fun c₁ < T_fun c₂ := by
    intro ⟨⟨r₁, col₁⟩, hr₁, hc₁⟩ ⟨⟨r₂, col₂⟩, hr₂, hc₂⟩ hcol_eq hrow
    simp only at hcol_eq hrow; subst hcol_eq



    set w₂ := parts.getD r₂ 0
    have hw₂ : (rowEntries r₂).card = w₂ := rowEnt_card r₂ hr₂

    have b_mem : ∀ i : Fin w₂,
        (rowEntries r₂).orderEmbOfFin hw₂ i ∈ rowEntries r₂ :=
      fun i => Finset.orderEmbOfFin_mem _ hw₂ i
    have b_source : ∀ i : Fin w₂, ∃ qi : Fin n,
        qi ∈ rowPositions r₂ ∧ σ.symm qi = (rowEntries r₂).orderEmbOfFin hw₂ i :=
      fun i => Finset.mem_image.mp (b_mem i)
    let qi : Fin w₂ → Fin n := fun i => (b_source i).choose
    have qi_mem : ∀ i, (qi i) ∈ rowPositions r₂ := fun i => (b_source i).choose_spec.1
    have qi_val : ∀ i, σ.symm (qi i) = (rowEntries r₂).orderEmbOfFin hw₂ i :=
      fun i => (b_source i).choose_spec.2

    have qi_col_lt : ∀ i, RepresentationTheory.SymmetricGroup.PartitionAuxiliaryConstructions.flatIndexColumn parts (qi i).val < parts.getD r₁ 0 := by
      intro i
      have hq_row := (Finset.mem_filter.mp (qi_mem i)).2
      have := RepresentationTheory.SymmetricGroup.PartitionAuxiliaryConstructions.flatIndexColumn_lt_rowLength parts (qi i).val (by rw [hps]; exact (qi i).isLt)
      rw [hq_row] at this
      exact Nat.lt_of_lt_of_le this (parts_descending r₁ r₂ hrow hr₂)

    have pi_exists : ∀ i : Fin w₂, ∃ pi : Fin n,
        RepresentationTheory.SymmetricGroup.PartitionAuxiliaryConstructions.flatIndexRow parts pi.val = r₁ ∧
        RepresentationTheory.SymmetricGroup.PartitionAuxiliaryConstructions.flatIndexColumn parts pi.val = RepresentationTheory.SymmetricGroup.PartitionAuxiliaryConstructions.flatIndexColumn parts (qi i).val := by
      intro i
      obtain ⟨k, hk, hrow_k, hcol_k⟩ := RepresentationTheory.SymmetricGroup.PartitionAuxiliaryConstructions.exists_flatIndex_of_column_lt_rowLength parts r₁
        (RepresentationTheory.SymmetricGroup.PartitionAuxiliaryConstructions.flatIndexColumn parts (qi i).val) (qi_col_lt i)
      exact ⟨⟨k, by rw [← hps]; exact hk⟩, hrow_k, hcol_k⟩
    let pi : Fin w₂ → Fin n := fun i => (pi_exists i).choose
    have pi_row : ∀ i, RepresentationTheory.SymmetricGroup.PartitionAuxiliaryConstructions.flatIndexRow parts (pi i).val = r₁ := fun i => (pi_exists i).choose_spec.1
    have pi_col : ∀ i, RepresentationTheory.SymmetricGroup.PartitionAuxiliaryConstructions.flatIndexColumn parts (pi i).val = RepresentationTheory.SymmetricGroup.PartitionAuxiliaryConstructions.flatIndexColumn parts (qi i).val :=
      fun i => (pi_exists i).choose_spec.2

    let f : Fin w₂ → Fin n := fun i => σ.symm (pi i)
    have hfA : ∀ i, f i ∈ rowEntries r₁ :=
      fun i => Finset.mem_image.mpr ⟨pi i,
        Finset.mem_filter.mpr ⟨Finset.mem_univ _, pi_row i⟩, rfl⟩
    have hf_lt : ∀ i, f i < (rowEntries r₂).orderEmbOfFin hw₂ i := by
      intro i; rw [← qi_val i]
      have hqi_row : RepresentationTheory.SymmetricGroup.PartitionAuxiliaryConstructions.flatIndexRow parts (qi i).val = r₂ := (Finset.mem_filter.mp (qi_mem i)).2
      exact hcs (pi i) (qi i)
        (pi_col i)
        (by rw [pi_row, hqi_row]; exact hrow)

    have hf_inj : Function.Injective f := by
      intro i₁ i₂ heq
      have hp_eq : pi i₁ = pi i₂ := σ.symm.injective heq
      have hcol_eq : RepresentationTheory.SymmetricGroup.PartitionAuxiliaryConstructions.flatIndexColumn parts (qi i₁).val = RepresentationTheory.SymmetricGroup.PartitionAuxiliaryConstructions.flatIndexColumn parts (qi i₂).val := by
        rw [← pi_col i₁, ← pi_col i₂]
        exact congrArg (RepresentationTheory.SymmetricGroup.PartitionAuxiliaryConstructions.flatIndexColumn parts ·.val) hp_eq
      have hq_eq : qi i₁ = qi i₂ :=
        Fin.ext (RepresentationTheory.SymmetricGroup.PartitionAuxiliaryConstructions.eq_of_flatIndexRow_eq_and_column_eq parts _ _
          (by rw [hps]; exact (qi i₁).isLt) (by rw [hps]; exact (qi i₂).isLt)
          ((Finset.mem_filter.mp (qi_mem i₁)).2.trans
            (Finset.mem_filter.mp (qi_mem i₂)).2.symm) hcol_eq)
      have := congrArg σ.symm hq_eq
      rw [qi_val, qi_val] at this
      exact ((rowEntries r₂).orderEmbOfFin hw₂).injective this



    set β := (rowEntries r₂).orderEmbOfFin hw₂ ⟨col₁, by omega⟩ with β_def


    have f_lt_β : ∀ i : Fin w₂, i.val ≤ col₁ → f i < β := by
      intro i hi
      calc f i < (rowEntries r₂).orderEmbOfFin hw₂ i := hf_lt i
        _ ≤ β := ((rowEntries r₂).orderEmbOfFin hw₂).monotone (by omega)

    have count_below : col₁ + 1 ≤ ((rowEntries r₁).filter (· < β)).card := by
      let S : Finset (Fin w₂) := Finset.univ.filter (fun i => i.val ≤ col₁)
      have hS_card : S.card = col₁ + 1 := by
        rw [show S = Finset.Iic (⟨col₁, by omega⟩ : Fin w₂) from by
          ext i; simp [S, Finset.mem_Iic, Fin.le_def]]
        exact Fin.card_Iic ⟨col₁, by omega⟩
      rw [← hS_card]
      apply Finset.card_le_card_of_injOn f
      · intro i hi
        simp only [Finset.mem_coe, Finset.mem_filter, Finset.mem_univ, true_and, S] at hi
        exact Finset.mem_filter.mpr ⟨hfA i, f_lt_β i hi⟩
      · exact Set.InjOn.mono (Set.subset_univ _) hf_inj.injOn




    by_contra hge; push Not at hge

    have hge' : β ≤ (rowEntries r₁).orderEmbOfFin (rowEnt_card r₁ hr₁) ⟨col₁, by omega⟩ := hge


    have filter_le : ((rowEntries r₁).filter (· < β)).card ≤ col₁ := by
      have sub : (rowEntries r₁).filter (· < β) ⊆
          (rowEntries r₁).filter (· < (rowEntries r₁).orderEmbOfFin (rowEnt_card r₁ hr₁)
            ⟨col₁, by omega⟩) :=
        Finset.monotone_filter_right _ (fun a _ ha => lt_of_lt_of_le ha hge')
      have sub2 : (rowEntries r₁).filter
          (· < (rowEntries r₁).orderEmbOfFin (rowEnt_card r₁ hr₁) ⟨col₁, by omega⟩) ⊆
          (Finset.Iio (⟨col₁, by omega⟩ : Fin (parts.getD r₁ 0))).image
            ((rowEntries r₁).orderEmbOfFin (rowEnt_card r₁ hr₁)) := by
        intro a ha
        rw [Finset.mem_filter] at ha
        have ⟨ha_mem, ha_lt⟩ := ha
        have ha_range : a ∈ Set.range ((rowEntries r₁).orderEmbOfFin (rowEnt_card r₁ hr₁)) := by
          rw [Finset.range_orderEmbOfFin]; exact ha_mem
        obtain ⟨j, rfl⟩ := ha_range
        exact Finset.mem_image.mpr ⟨j, Finset.mem_Iio.mpr
          (((rowEntries r₁).orderEmbOfFin (rowEnt_card r₁ hr₁)).lt_iff_lt.mp ha_lt), rfl⟩
      calc ((rowEntries r₁).filter (· < β)).card
          ≤ ((rowEntries r₁).filter
              (· < (rowEntries r₁).orderEmbOfFin (rowEnt_card r₁ hr₁)
                ⟨col₁, by omega⟩)).card := Finset.card_le_card sub
        _ ≤ ((Finset.Iio (⟨col₁, by omega⟩ : Fin (parts.getD r₁ 0))).image
              ((rowEntries r₁).orderEmbOfFin (rowEnt_card r₁ hr₁))).card :=
            Finset.card_le_card sub2
        _ ≤ (Finset.Iio (⟨col₁, by omega⟩ : Fin (parts.getD r₁ 0))).card :=
            Finset.card_image_le
        _ = col₁ := @Fin.card_Iio (parts.getD r₁ 0) ⟨col₁, by omega⟩
    omega
  let T : RepresentationTheory.SymmetricGroup.PartitionAuxiliaryConstructions.AuxiliaryPartitionSource n la :=
    ⟨T_fun, ⟨T_inj, T_surj⟩, T_row_inc, T_col_inc⟩

  have T_mem_rowEntries : ∀ (cell : PartitionIndex n la),
      T_fun cell ∈ rowEntries cell.val.1 := by
    intro ⟨⟨r, c⟩, hr, hc⟩
    exact Finset.orderEmbOfFin_mem (rowEntries r) (rowEnt_card r hr) ⟨c, by omega⟩







  let p := σ * (associatedPermutation n la T)⁻¹
  have hp_row : p ∈ RepresentationTheory.SymmetricGroup.PartitionAuxiliaryConstructions.auxiliaryPartitionPermutationSubgroupB n la := by
    intro k
    simp only [p, Equiv.Perm.coe_mul, Function.comp_apply]






    set entry := (associatedPermutation n la T)⁻¹ k with entry_def

    have h_entry : entry = T_fun ((finEquivPartitionIndex n la) k) := by
      simp only [entry_def, associatedPermutation, Equiv.Perm.inv_def, Equiv.symm_trans_apply,
                 Equiv.symm_symm, Equiv.ofBijective_apply]
      rfl

    have h_cell_row : ((finEquivPartitionIndex n la) k).val.1 = RepresentationTheory.SymmetricGroup.PartitionAuxiliaryConstructions.flatIndexRow parts k.val := by
      simp [finEquivPartitionIndex, partitionIndexOfFin, Equiv.ofBijective_apply]
      rfl

    have h_mem : entry ∈ rowEntries (RepresentationTheory.SymmetricGroup.PartitionAuxiliaryConstructions.flatIndexRow parts k.val) := by
      rw [h_entry, ← h_cell_row]
      exact T_mem_rowEntries ((finEquivPartitionIndex n la) k)

    obtain ⟨pos, hpos, hv⟩ := Finset.mem_image.mp h_mem

    have h_σ : σ entry = pos := by rw [← hv]; exact σ.apply_symm_apply pos
    rw [h_σ]
    exact (Finset.mem_filter.mp hpos).2
  exact ⟨T, p, hp_row, by simp only [p]; group⟩





/-- Failure of the auxiliary condition yields two indices with equal first derived values, increasing second derived values, and reversed inverse images. -/
theorem exists_indices_of_not_permutationCondition (n : ℕ) (la : Nat.Partition n)
    (σ : Equiv.Perm (Fin n)) (h : ¬ PermutationCondition n la σ) :
    ∃ p₁ p₂ : Fin n,
      RepresentationTheory.SymmetricGroup.PartitionAuxiliaryConstructions.flatIndexColumn la.auxiliaryPartitionNatList p₁.val = RepresentationTheory.SymmetricGroup.PartitionAuxiliaryConstructions.flatIndexColumn la.auxiliaryPartitionNatList p₂.val ∧
      RepresentationTheory.SymmetricGroup.PartitionAuxiliaryConstructions.flatIndexRow la.auxiliaryPartitionNatList p₁.val < RepresentationTheory.SymmetricGroup.PartitionAuxiliaryConstructions.flatIndexRow la.auxiliaryPartitionNatList p₂.val ∧
      σ.symm p₂ < σ.symm p₁ := by
  simp only [PermutationCondition, not_forall] at h
  obtain ⟨p₁, p₂, hcol, hrow, hinv⟩ := h
  simp only [not_lt] at hinv
  have hne : p₁ ≠ p₂ := by intro heq; rw [heq] at hrow; exact Nat.lt_irrefl _ hrow
  have hne' : σ.symm p₁ ≠ σ.symm p₂ := σ.symm.injective.ne hne
  exact ⟨p₁, p₂, hcol, hrow, lt_of_le_of_ne hinv hne'.symm⟩




























private def garnirSet (n : ℕ) (la : Nat.Partition n)
    (p₁ p₂ : Fin n) : Finset (Fin n) :=
  let parts := la.auxiliaryPartitionNatList
  let r₁ := RepresentationTheory.SymmetricGroup.PartitionAuxiliaryConstructions.flatIndexRow parts p₁.val
  let r₂ := RepresentationTheory.SymmetricGroup.PartitionAuxiliaryConstructions.flatIndexRow parts p₂.val
  let j := RepresentationTheory.SymmetricGroup.PartitionAuxiliaryConstructions.flatIndexColumn parts p₁.val
  Finset.univ.filter fun pos =>
    (RepresentationTheory.SymmetricGroup.PartitionAuxiliaryConstructions.flatIndexRow parts pos.val = r₁ ∧ j ≤ RepresentationTheory.SymmetricGroup.PartitionAuxiliaryConstructions.flatIndexColumn parts pos.val) ∨
    (RepresentationTheory.SymmetricGroup.PartitionAuxiliaryConstructions.flatIndexRow parts pos.val = r₂ ∧ RepresentationTheory.SymmetricGroup.PartitionAuxiliaryConstructions.flatIndexColumn parts pos.val ≤ j)



private noncomputable def garnirElement (n : ℕ) (la : Nat.Partition n)
    (p₁ p₂ : Fin n) : RepresentationTheory.PartitionAuxiliary.natIndexedType n :=
  ∑ w : { w : Equiv.Perm (Fin n) // ∀ x, x ∉ garnirSet n la p₁ p₂ → w x = x },
    (↑(↑(Equiv.Perm.sign w.val) : ℤ) : ℂ) • MonoidAlgebra.of ℂ _ w.val








private theorem garnirSet_has_row_pair (n : ℕ) (la : Nat.Partition n)
    (p₁ p₂ : Fin n)
    (hcol : RepresentationTheory.SymmetricGroup.PartitionAuxiliaryConstructions.flatIndexColumn la.auxiliaryPartitionNatList p₁.val = RepresentationTheory.SymmetricGroup.PartitionAuxiliaryConstructions.flatIndexColumn la.auxiliaryPartitionNatList p₂.val)
    (_hrow : RepresentationTheory.SymmetricGroup.PartitionAuxiliaryConstructions.flatIndexRow la.auxiliaryPartitionNatList p₁.val < RepresentationTheory.SymmetricGroup.PartitionAuxiliaryConstructions.flatIndexRow la.auxiliaryPartitionNatList p₂.val)
    (hwidth : 1 < la.auxiliaryPartitionNatList.getD (RepresentationTheory.SymmetricGroup.PartitionAuxiliaryConstructions.flatIndexRow la.auxiliaryPartitionNatList p₁.val) 0) :
    ∃ a b : Fin n, a ≠ b ∧ a ∈ garnirSet n la p₁ p₂ ∧ b ∈ garnirSet n la p₁ p₂ ∧
      RepresentationTheory.SymmetricGroup.PartitionAuxiliaryConstructions.flatIndexRow la.auxiliaryPartitionNatList a.val = RepresentationTheory.SymmetricGroup.PartitionAuxiliaryConstructions.flatIndexRow la.auxiliaryPartitionNatList b.val := by
  set parts := la.auxiliaryPartitionNatList with hparts_def
  set r₁ := RepresentationTheory.SymmetricGroup.PartitionAuxiliaryConstructions.flatIndexRow parts p₁.val with hr₁_def
  set r₂ := RepresentationTheory.SymmetricGroup.PartitionAuxiliaryConstructions.flatIndexRow parts p₂.val with hr₂_def
  set j := RepresentationTheory.SymmetricGroup.PartitionAuxiliaryConstructions.flatIndexColumn parts p₁.val with hj_def

  have hn_pos : 0 < n := Fin.pos p₁
  have hp₁_valid : p₁.val < parts.sum := by
    rw [hparts_def, sortedParts_sum]; exact p₁.isLt
  have hp₂_valid : p₂.val < parts.sum := by
    rw [hparts_def, sortedParts_sum]; exact p₂.isLt
  have hj_lt_r₁ : j < parts.getD r₁ 0 := RepresentationTheory.SymmetricGroup.PartitionAuxiliaryConstructions.flatIndexColumn_lt_rowLength parts p₁.val hp₁_valid
  have hj_lt_r₂ : j < parts.getD r₂ 0 := by
    have := RepresentationTheory.SymmetricGroup.PartitionAuxiliaryConstructions.flatIndexColumn_lt_rowLength parts p₂.val hp₂_valid
    rwa [← hcol] at this

  by_cases hj_pos : 0 < j
  ·

    have h0_lt : 0 < parts.getD r₂ 0 := by omega
    obtain ⟨k₀, hk₀_sum, hk₀_row, hk₀_col⟩ := RepresentationTheory.SymmetricGroup.PartitionAuxiliaryConstructions.exists_flatIndex_of_column_lt_rowLength parts r₂ 0 h0_lt

    have h1_lt : 1 < parts.getD r₂ 0 := by omega
    obtain ⟨k₁, hk₁_sum, hk₁_row, hk₁_col⟩ := RepresentationTheory.SymmetricGroup.PartitionAuxiliaryConstructions.exists_flatIndex_of_column_lt_rowLength parts r₂ 1 h1_lt

    have hne : k₀ ≠ k₁ := by
      intro heq; rw [heq] at hk₀_col; rw [hk₀_col] at hk₁_col; omega

    rw [hparts_def, sortedParts_sum n la] at hk₀_sum hk₁_sum
    refine ⟨⟨k₀, hk₀_sum⟩, ⟨k₁, hk₁_sum⟩, fun h => hne (congrArg Fin.val h), ?_, ?_, ?_⟩
    · simp only [garnirSet, Finset.mem_filter, Finset.mem_univ, true_and, ← hparts_def]
      right; exact ⟨hk₀_row, by rw [hk₀_col]; omega⟩
    · simp only [garnirSet, Finset.mem_filter, Finset.mem_univ, true_and, ← hparts_def]
      right; exact ⟨hk₁_row, by rw [hk₁_col]; omega⟩
    · rw [show (⟨k₀, hk₀_sum⟩ : Fin n).val = k₀ from rfl,
          show (⟨k₁, hk₁_sum⟩ : Fin n).val = k₁ from rfl, hk₀_row, hk₁_row]
  ·
    push Not at hj_pos
    have hj_eq : j = 0 := Nat.le_zero.mp hj_pos

    have h0_lt : 0 < parts.getD r₁ 0 := by omega
    obtain ⟨k₀, hk₀_sum, hk₀_row, hk₀_col⟩ := RepresentationTheory.SymmetricGroup.PartitionAuxiliaryConstructions.exists_flatIndex_of_column_lt_rowLength parts r₁ 0 h0_lt

    obtain ⟨k₁, hk₁_sum, hk₁_row, hk₁_col⟩ := RepresentationTheory.SymmetricGroup.PartitionAuxiliaryConstructions.exists_flatIndex_of_column_lt_rowLength parts r₁ 1 hwidth

    have hne : k₀ ≠ k₁ := by
      intro heq; rw [heq] at hk₀_col; rw [hk₀_col] at hk₁_col; omega
    rw [hparts_def, sortedParts_sum n la] at hk₀_sum hk₁_sum
    refine ⟨⟨k₀, hk₀_sum⟩, ⟨k₁, hk₁_sum⟩, fun h => hne (congrArg Fin.val h), ?_, ?_, ?_⟩
    · simp only [garnirSet, Finset.mem_filter, Finset.mem_univ, true_and, ← hparts_def]
      left; exact ⟨hk₀_row, by rw [← hj_def, hk₀_col, hj_eq]⟩
    · simp only [garnirSet, Finset.mem_filter, Finset.mem_univ, true_and, ← hparts_def]
      left; exact ⟨hk₁_row, by rw [← hj_def, hj_eq]; omega⟩
    · rw [show (⟨k₀, hk₀_sum⟩ : Fin n).val = k₀ from rfl,
          show (⟨k₁, hk₁_sum⟩ : Fin n).val = k₁ from rfl, hk₀_row, hk₁_row]



private theorem left_transposition_negates_garnir (n : ℕ) (la : Nat.Partition n)
    (p₁ p₂ : Fin n) (t : Equiv.Perm (Fin n))
    (ht_supp : ∀ x, x ∉ garnirSet n la p₁ p₂ → t x = x)
    (ht_sign : Equiv.Perm.sign t = -1) :
    MonoidAlgebra.of ℂ _ t * garnirElement n la p₁ p₂ =
      -garnirElement n la p₁ p₂ := by
  simp only [garnirElement]
  rw [Finset.mul_sum, ← Finset.sum_neg_distrib]
  simp_rw [Algebra.mul_smul_comm, ← map_mul (MonoidAlgebra.of ℂ (Equiv.Perm (Fin n)))]


  set S := garnirSet n la p₁ p₂ with hS_def
  have ht_inv_supp : ∀ x, x ∉ S → t⁻¹ x = x := fun x hx => by
    calc t⁻¹ x = t⁻¹ (t x) := by rw [ht_supp x hx]
      _ = x := Equiv.symm_apply_apply t x
  set P := fun w : Equiv.Perm (Fin n) => ∀ x, x ∉ S → w x = x
  have hmul_mem : ∀ (w : Equiv.Perm (Fin n)), P w → P (t * w) := fun w hw x hx => by
    change t (w x) = x; rw [hw x hx, ht_supp x hx]
  have hinv_mem : ∀ (w : Equiv.Perm (Fin n)), P w → P (t⁻¹ * w) := fun w hw x hx => by
    change t⁻¹ (w x) = x; rw [hw x hx, ht_inv_supp x hx]

  refine Fintype.sum_equiv
    ⟨fun ⟨w, hw⟩ => ⟨t * w, hmul_mem w hw⟩,
     fun ⟨w, hw⟩ => ⟨t⁻¹ * w, hinv_mem w hw⟩,
     fun ⟨w, _⟩ => Subtype.ext (show t⁻¹ * (t * w) = w by group),
     fun ⟨w, _⟩ => Subtype.ext (show t * (t⁻¹ * w) = w by group)⟩
    _ _ (fun ⟨w, hw⟩ => ?_)





  change (↑(↑(Equiv.Perm.sign w) : ℤ) : ℂ) •
      MonoidAlgebra.of ℂ _ (t * w) =
    -((↑(↑(Equiv.Perm.sign (t * w)) : ℤ) : ℂ) •
      MonoidAlgebra.of ℂ _ (t * w))
  have hsm : (↑(↑(Equiv.Perm.sign (t * w)) : ℤ) : ℂ) =
      -(↑(↑(Equiv.Perm.sign w) : ℤ) : ℂ) := by
    have h1 : Equiv.Perm.sign (t * w) = Equiv.Perm.sign t * Equiv.Perm.sign w := map_mul _ _ _
    rw [h1, ht_sign]
    simp only [Units.val_mul, Int.cast_mul]
    have : (↑(-1 : ℤˣ) : ℤ) = -1 := rfl
    rw [this, Int.cast_neg, Int.cast_one, neg_one_mul]
  rw [hsm, neg_smul, neg_neg]

private theorem garnir_row_annihilates (n : ℕ) (la : Nat.Partition n)
    (p₁ p₂ : Fin n)
    (hcol : RepresentationTheory.SymmetricGroup.PartitionAuxiliaryConstructions.flatIndexColumn la.auxiliaryPartitionNatList p₁.val = RepresentationTheory.SymmetricGroup.PartitionAuxiliaryConstructions.flatIndexColumn la.auxiliaryPartitionNatList p₂.val)
    (hrow : RepresentationTheory.SymmetricGroup.PartitionAuxiliaryConstructions.flatIndexRow la.auxiliaryPartitionNatList p₁.val < RepresentationTheory.SymmetricGroup.PartitionAuxiliaryConstructions.flatIndexRow la.auxiliaryPartitionNatList p₂.val)
    (hwidth : 1 < la.auxiliaryPartitionNatList.getD (RepresentationTheory.SymmetricGroup.PartitionAuxiliaryConstructions.flatIndexRow la.auxiliaryPartitionNatList p₁.val) 0) :
    RepresentationTheory.SymmetricGroup.PartitionAuxiliaryConstructions.auxiliaryPartitionGroupAlgebraElementB n la * garnirElement n la p₁ p₂ = 0 := by

  obtain ⟨a, b, hab, ha_mem, hb_mem, hrow_eq⟩ :=
    garnirSet_has_row_pair n la p₁ p₂ hcol hrow hwidth
  set t := Equiv.swap a b

  have ht_sign : Equiv.Perm.sign t = -1 := Equiv.Perm.sign_swap hab

  have ht_supp : ∀ x, x ∉ garnirSet n la p₁ p₂ → t x = x := by
    intro x hx
    simp only [t, Equiv.swap_apply_def]
    split_ifs with h1 h2
    · exact absurd (h1 ▸ ha_mem) hx
    · exact absurd (h2 ▸ hb_mem) hx
    · rfl

  have ht_row : t ∈ RepresentationTheory.SymmetricGroup.PartitionAuxiliaryConstructions.auxiliaryPartitionPermutationSubgroupB n la := by
    intro k; simp only [t, Equiv.swap_apply_def]
    split_ifs with h1 h2
    · exact h1 ▸ hrow_eq.symm
    · exact h2 ▸ hrow_eq
    · rfl

  have h_neg : MonoidAlgebra.of ℂ _ t * garnirElement n la p₁ p₂ =
      -garnirElement n la p₁ p₂ :=
    left_transposition_negates_garnir n la p₁ p₂ t ht_supp ht_sign
  have h_absorb : RepresentationTheory.SymmetricGroup.PartitionAuxiliaryConstructions.auxiliaryPartitionGroupAlgebraElementB n la * MonoidAlgebra.of ℂ _ t =
      RepresentationTheory.SymmetricGroup.PartitionAuxiliaryConstructions.auxiliaryPartitionGroupAlgebraElementB n la := RepresentationTheory.SymmetricGroup.PartitionGroupAlgebra.mul_perm_eq_self_of_mem t ht_row

  have key : RepresentationTheory.SymmetricGroup.PartitionAuxiliaryConstructions.auxiliaryPartitionGroupAlgebraElementB n la * garnirElement n la p₁ p₂ =
      -(RepresentationTheory.SymmetricGroup.PartitionAuxiliaryConstructions.auxiliaryPartitionGroupAlgebraElementB n la * garnirElement n la p₁ p₂) := by
    have h_tt : t * t = 1 := Equiv.swap_mul_self a b

    have h_inv : MonoidAlgebra.of ℂ (Equiv.Perm (Fin n)) t *
        MonoidAlgebra.of ℂ (Equiv.Perm (Fin n)) t = 1 := by
      rw [← map_mul, Equiv.swap_mul_self a b, map_one]
    have h_inv : MonoidAlgebra.of ℂ (Equiv.Perm (Fin n)) t *
        (MonoidAlgebra.of ℂ (Equiv.Perm (Fin n)) t * garnirElement n la p₁ p₂) =
        garnirElement n la p₁ p₂ := by
      rw [← mul_assoc, h_inv, one_mul]
    calc RepresentationTheory.SymmetricGroup.PartitionAuxiliaryConstructions.auxiliaryPartitionGroupAlgebraElementB n la * garnirElement n la p₁ p₂
        = RepresentationTheory.SymmetricGroup.PartitionAuxiliaryConstructions.auxiliaryPartitionGroupAlgebraElementB n la * (MonoidAlgebra.of ℂ _ t *
            (MonoidAlgebra.of ℂ _ t * garnirElement n la p₁ p₂)) := by
          rw [h_inv]
      _ = (RepresentationTheory.SymmetricGroup.PartitionAuxiliaryConstructions.auxiliaryPartitionGroupAlgebraElementB n la * MonoidAlgebra.of ℂ _ t) *
            (MonoidAlgebra.of ℂ _ t * garnirElement n la p₁ p₂) := by
          rw [mul_assoc]
      _ = RepresentationTheory.SymmetricGroup.PartitionAuxiliaryConstructions.auxiliaryPartitionGroupAlgebraElementB n la *
            (MonoidAlgebra.of ℂ _ t * garnirElement n la p₁ p₂) := by
          rw [h_absorb]
      _ = RepresentationTheory.SymmetricGroup.PartitionAuxiliaryConstructions.auxiliaryPartitionGroupAlgebraElementB n la * (-garnirElement n la p₁ p₂) := by rw [h_neg]
      _ = -(RepresentationTheory.SymmetricGroup.PartitionAuxiliaryConstructions.auxiliaryPartitionGroupAlgebraElementB n la * garnirElement n la p₁ p₂) := mul_neg _ _

  have h2 : RepresentationTheory.SymmetricGroup.PartitionAuxiliaryConstructions.auxiliaryPartitionGroupAlgebraElementB n la * garnirElement n la p₁ p₂ +
      RepresentationTheory.SymmetricGroup.PartitionAuxiliaryConstructions.auxiliaryPartitionGroupAlgebraElementB n la * garnirElement n la p₁ p₂ = 0 := by
    nth_rw 1 [key]; exact neg_add_cancel _
  have h3 : (2 : ℂ) • (RepresentationTheory.SymmetricGroup.PartitionAuxiliaryConstructions.auxiliaryPartitionGroupAlgebraElementB n la * garnirElement n la p₁ p₂) = 0 := by
    rw [two_smul]; exact h2
  exact (smul_eq_zero.mp h3).resolve_left (by norm_num : (2 : ℂ) ≠ 0)


private theorem swap_mem_ColumnSubgroup' (n : ℕ) (la : Nat.Partition n)
    (p₁ p₂ : Fin n)
    (hcol : RepresentationTheory.SymmetricGroup.PartitionAuxiliaryConstructions.flatIndexColumn la.auxiliaryPartitionNatList p₁.val = RepresentationTheory.SymmetricGroup.PartitionAuxiliaryConstructions.flatIndexColumn la.auxiliaryPartitionNatList p₂.val) :
    Equiv.swap p₁ p₂ ∈ RepresentationTheory.SymmetricGroup.PartitionAuxiliaryConstructions.auxiliaryPartitionPermutationSubgroupA n la := by
  intro k
  simp only [Equiv.swap_apply_def]
  split_ifs with h1 h2
  · subst h1; exact hcol.symm
  · subst h2; exact hcol
  · rfl



private theorem of_col_mul_YoungSymmetrizer (n : ℕ) (la : Nat.Partition n)
    (q : Equiv.Perm (Fin n)) (hq : q ∈ RepresentationTheory.SymmetricGroup.PartitionAuxiliaryConstructions.auxiliaryPartitionPermutationSubgroupA n la) :
    MonoidAlgebra.of ℂ _ q * RepresentationTheory.SymmetricGroup.PartitionAuxiliaryConstructions.auxiliaryPartitionGroupAlgebraElementC n la =
      ((↑(↑(Equiv.Perm.sign q) : ℤ) : ℂ)) • RepresentationTheory.SymmetricGroup.PartitionAuxiliaryConstructions.auxiliaryPartitionGroupAlgebraElementC n la := by
  change MonoidAlgebra.of ℂ _ q * (RepresentationTheory.SymmetricGroup.PartitionAuxiliaryConstructions.auxiliaryPartitionGroupAlgebraElementA n la * RepresentationTheory.SymmetricGroup.PartitionAuxiliaryConstructions.auxiliaryPartitionGroupAlgebraElementB n la) =
    _ • (RepresentationTheory.SymmetricGroup.PartitionAuxiliaryConstructions.auxiliaryPartitionGroupAlgebraElementA n la * RepresentationTheory.SymmetricGroup.PartitionAuxiliaryConstructions.auxiliaryPartitionGroupAlgebraElementB n la)
  rw [← mul_assoc, RepresentationTheory.SymmetricGroup.PartitionGroupAlgebra.perm_mul_eq_sign_smul_of_mem q hq, Algebra.smul_mul_assoc]




private theorem garnir_swap_identity (n : ℕ) (la : Nat.Partition n)
    (σ : Equiv.Perm (Fin n)) (p₁ p₂ : Fin n)
    (hcol : RepresentationTheory.SymmetricGroup.PartitionAuxiliaryConstructions.flatIndexColumn la.auxiliaryPartitionNatList p₁.val = RepresentationTheory.SymmetricGroup.PartitionAuxiliaryConstructions.flatIndexColumn la.auxiliaryPartitionNatList p₂.val)
    (hne : p₁ ≠ p₂) :
    MonoidAlgebra.of ℂ _ σ * RepresentationTheory.SymmetricGroup.PartitionAuxiliaryConstructions.auxiliaryPartitionGroupAlgebraElementC n la =
      (-1 : ℂ) • (MonoidAlgebra.of ℂ _ (σ * Equiv.swap p₁ p₂) *
        RepresentationTheory.SymmetricGroup.PartitionAuxiliaryConstructions.auxiliaryPartitionGroupAlgebraElementC n la) := by
  have hswap_col := swap_mem_ColumnSubgroup' n la p₁ p₂ hcol
  have h1 : MonoidAlgebra.of ℂ _ (Equiv.swap p₁ p₂) * RepresentationTheory.SymmetricGroup.PartitionAuxiliaryConstructions.auxiliaryPartitionGroupAlgebraElementC n la =
      (-1 : ℂ) • RepresentationTheory.SymmetricGroup.PartitionAuxiliaryConstructions.auxiliaryPartitionGroupAlgebraElementC n la := by
    rw [of_col_mul_YoungSymmetrizer n la _ hswap_col, Equiv.Perm.sign_swap hne]
    simp [Int.cast_neg, Int.cast_one]
  have key : MonoidAlgebra.of ℂ (Equiv.Perm (Fin n)) σ *
      (MonoidAlgebra.of ℂ _ (Equiv.swap p₁ p₂) * RepresentationTheory.SymmetricGroup.PartitionAuxiliaryConstructions.auxiliaryPartitionGroupAlgebraElementC n la) =
      MonoidAlgebra.of ℂ _ (σ * Equiv.swap p₁ p₂) * RepresentationTheory.SymmetricGroup.PartitionAuxiliaryConstructions.auxiliaryPartitionGroupAlgebraElementC n la := by
    rw [← mul_assoc, ← map_mul]
  rw [h1, Algebra.mul_smul_comm] at key


  rw [← key, smul_smul]; norm_num


private theorem columnInvCount'_pos_of_inv (n : ℕ) (la : Nat.Partition n)
    (σ : Equiv.Perm (Fin n))
    (p₁ p₂ : Fin n)
    (hcol : RepresentationTheory.SymmetricGroup.PartitionAuxiliaryConstructions.flatIndexColumn la.auxiliaryPartitionNatList p₁.val = RepresentationTheory.SymmetricGroup.PartitionAuxiliaryConstructions.flatIndexColumn la.auxiliaryPartitionNatList p₂.val)
    (hrow : RepresentationTheory.SymmetricGroup.PartitionAuxiliaryConstructions.flatIndexRow la.auxiliaryPartitionNatList p₁.val < RepresentationTheory.SymmetricGroup.PartitionAuxiliaryConstructions.flatIndexRow la.auxiliaryPartitionNatList p₂.val)
    (hinv : σ.symm p₂ < σ.symm p₁) :
    0 < partitionPermutationStatistic n la σ := by
  unfold partitionPermutationStatistic
  apply Finset.card_pos.mpr
  exact ⟨(p₁, p₂), Finset.mem_filter.mpr ⟨Finset.mem_univ _, hcol, hrow, hinv⟩⟩



private theorem single_column_garnir (n : ℕ) (la : Nat.Partition n)
    (σ : Equiv.Perm (Fin n))
    (h_single : ∀ i, i < la.auxiliaryPartitionNatList.length → la.auxiliaryPartitionNatList.getD i 0 = 1) :
    MonoidAlgebra.of ℂ _ σ * RepresentationTheory.SymmetricGroup.PartitionAuxiliaryConstructions.auxiliaryPartitionGroupAlgebraElementC n la =
      ((↑(↑(Equiv.Perm.sign σ) : ℤ) : ℂ)) •
        (MonoidAlgebra.of ℂ _ (1 : Equiv.Perm (Fin n)) * RepresentationTheory.SymmetricGroup.PartitionAuxiliaryConstructions.auxiliaryPartitionGroupAlgebraElementC n la) := by

  have hσ_col : σ ∈ RepresentationTheory.SymmetricGroup.PartitionAuxiliaryConstructions.auxiliaryPartitionPermutationSubgroupA n la := by
    intro k
    have hk := k.isLt
    have hsum : la.auxiliaryPartitionNatList.sum = n := sortedParts_sum n la
    have hksum : k.val < la.auxiliaryPartitionNatList.sum := by omega

    have hk_col : RepresentationTheory.SymmetricGroup.PartitionAuxiliaryConstructions.flatIndexColumn la.auxiliaryPartitionNatList k.val = 0 := by
      have hrow := selectedPartIndex_lt_length la.auxiliaryPartitionNatList k.val hksum
      have hw := h_single _ hrow
      have hcol := RepresentationTheory.SymmetricGroup.PartitionAuxiliaryConstructions.flatIndexColumn_lt_rowLength la.auxiliaryPartitionNatList k.val hksum
      rw [hw] at hcol; omega
    have hσk_col : RepresentationTheory.SymmetricGroup.PartitionAuxiliaryConstructions.flatIndexColumn la.auxiliaryPartitionNatList (σ k).val = 0 := by
      have hσk := (σ k).isLt
      have hσksum : (σ k).val < la.auxiliaryPartitionNatList.sum := by omega
      have hrow := selectedPartIndex_lt_length la.auxiliaryPartitionNatList (σ k).val hσksum
      have hw := h_single _ hrow
      have hcol := RepresentationTheory.SymmetricGroup.PartitionAuxiliaryConstructions.flatIndexColumn_lt_rowLength la.auxiliaryPartitionNatList (σ k).val hσksum
      rw [hw] at hcol; omega
    rw [hk_col, hσk_col]

  have h_row_trivial : ∀ (p : Equiv.Perm (Fin n)), p ∈ RepresentationTheory.SymmetricGroup.PartitionAuxiliaryConstructions.auxiliaryPartitionPermutationSubgroupB n la → p = 1 := by
    intro p hp; ext k : 1; simp only [Equiv.Perm.one_apply]
    have hk_lt : k.val < la.auxiliaryPartitionNatList.sum := by rw [sortedParts_sum]; exact k.isLt
    have hpk_lt : (p k).val < la.auxiliaryPartitionNatList.sum := by rw [sortedParts_sum]; exact (p k).isLt
    have hcol_k : RepresentationTheory.SymmetricGroup.PartitionAuxiliaryConstructions.flatIndexColumn la.auxiliaryPartitionNatList k.val = 0 := by
      have hcol := RepresentationTheory.SymmetricGroup.PartitionAuxiliaryConstructions.flatIndexColumn_lt_rowLength la.auxiliaryPartitionNatList k.val hk_lt
      rw [h_single _ (selectedPartIndex_lt_length la.auxiliaryPartitionNatList k.val hk_lt)] at hcol; omega
    have hcol_pk : RepresentationTheory.SymmetricGroup.PartitionAuxiliaryConstructions.flatIndexColumn la.auxiliaryPartitionNatList (p k).val = 0 := by
      have hcol := RepresentationTheory.SymmetricGroup.PartitionAuxiliaryConstructions.flatIndexColumn_lt_rowLength la.auxiliaryPartitionNatList (p k).val hpk_lt
      rw [h_single _ (selectedPartIndex_lt_length la.auxiliaryPartitionNatList (p k).val hpk_lt)] at hcol; omega
    exact Fin.ext (RepresentationTheory.SymmetricGroup.PartitionAuxiliaryConstructions.eq_of_flatIndexRow_eq_and_column_eq la.auxiliaryPartitionNatList (p k).val k.val
      hpk_lt hk_lt (hp k) (by rw [hcol_pk, hcol_k]))


  have h_unique : Unique (↥(RepresentationTheory.SymmetricGroup.PartitionAuxiliaryConstructions.auxiliaryPartitionPermutationSubgroupB n la)) :=
    ⟨⟨⟨1, (RepresentationTheory.SymmetricGroup.PartitionAuxiliaryConstructions.auxiliaryPartitionPermutationSubgroupB n la).one_mem⟩⟩, fun g => Subtype.ext (h_row_trivial g.val g.prop)⟩
  have h_rowSym_eq : RepresentationTheory.SymmetricGroup.PartitionAuxiliaryConstructions.auxiliaryPartitionGroupAlgebraElementB n la = MonoidAlgebra.of ℂ _ (1 : Equiv.Perm (Fin n)) := by
    have hval : ∀ g : ↥(RepresentationTheory.SymmetricGroup.PartitionAuxiliaryConstructions.auxiliaryPartitionPermutationSubgroupB n la), (g : Equiv.Perm (Fin n)) = 1 :=
      fun g => h_row_trivial g.val g.prop
    simp only [RepresentationTheory.SymmetricGroup.PartitionAuxiliaryConstructions.auxiliaryPartitionGroupAlgebraElementB, hval, Finset.sum_const, Finset.card_univ]
    haveI := h_unique
    simp [Fintype.card_unique]
  have h_of_one : MonoidAlgebra.of ℂ (Equiv.Perm (Fin n)) (1 : Equiv.Perm (Fin n)) = 1 :=
    map_one _
  rw [RepresentationTheory.SymmetricGroup.PartitionAuxiliaryConstructions.auxiliaryPartitionGroupAlgebraElementC]
  simp only [h_rowSym_eq, h_of_one, mul_one, one_mul]
  exact RepresentationTheory.SymmetricGroup.PartitionGroupAlgebra.perm_mul_eq_sign_smul_of_mem σ hσ_col


private theorem rowOfPos_mono (parts : List ℕ) (a b : ℕ)
    (hb : b < parts.sum)
    (hab : a ≤ b) : RepresentationTheory.SymmetricGroup.PartitionAuxiliaryConstructions.flatIndexRow parts a ≤ RepresentationTheory.SymmetricGroup.PartitionAuxiliaryConstructions.flatIndexRow parts b := by
  induction parts generalizing a b with
  | nil => simp [List.sum_nil] at hb
  | cons p ps ih =>
    simp only [RepresentationTheory.SymmetricGroup.PartitionAuxiliaryConstructions.flatIndexRow]
    split_ifs with ha hb
    · omega
    · omega
    · exfalso; simp [List.sum_cons] at hb; omega
    · have hb' : b - p < ps.sum := by simp [List.sum_cons] at hb; omega
      have hab' : a - p ≤ b - p := Nat.sub_le_sub_right hab p
      have := ih (a - p) (b - p) hb' hab'
      omega



private theorem rowOfPos_eq_length (parts : List ℕ) (a : ℕ) (ha : parts.sum ≤ a) :
    RepresentationTheory.SymmetricGroup.PartitionAuxiliaryConstructions.flatIndexRow parts a = parts.length := by
  induction parts generalizing a with
  | nil => simp [RepresentationTheory.SymmetricGroup.PartitionAuxiliaryConstructions.flatIndexRow]
  | cons p ps ih =>
    simp only [RepresentationTheory.SymmetricGroup.PartitionAuxiliaryConstructions.flatIndexRow, List.length_cons]
    have : ¬(a < p) := by simp [List.sum_cons] at ha; omega
    rw [if_neg this]
    have : ps.sum ≤ a - p := by simp [List.sum_cons] at ha; omega
    rw [ih _ this]; omega

private theorem lt_of_lt_rowOfPos (parts : List ℕ) (a b : ℕ)
    (hb : b < parts.sum)
    (hrow : RepresentationTheory.SymmetricGroup.PartitionAuxiliaryConstructions.flatIndexRow parts a < RepresentationTheory.SymmetricGroup.PartitionAuxiliaryConstructions.flatIndexRow parts b) : a < b := by
  by_contra h
  push Not at h

  by_cases ha : a < parts.sum
  · have := rowOfPos_mono parts b a ha h
    omega
  · push Not at ha
    have := rowOfPos_eq_length parts a ha
    have := selectedPartIndex_lt_length parts b hb
    omega


private theorem columnInvCount'_one (n : ℕ) (la : Nat.Partition n) :
    partitionPermutationStatistic n la 1 = 0 := by
  unfold partitionPermutationStatistic
  apply Finset.card_eq_zero.mpr
  apply Finset.filter_eq_empty_iff.mpr
  intro ⟨a, b⟩ _
  simp only [not_and]
  intro _ hrow
  have hsum : la.auxiliaryPartitionNatList.sum = n := sortedParts_sum n la
  have hb : b.val < la.auxiliaryPartitionNatList.sum := by omega
  exact Nat.not_lt.mpr (Nat.le_of_lt (lt_of_lt_rowOfPos la.auxiliaryPartitionNatList a.val b.val hb hrow))








end

end RepresentationTheory.Combinatorics.PartitionPermutation
