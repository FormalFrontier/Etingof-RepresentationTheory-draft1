/-
Copyright (c) 2026 FormalFrontier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENCE.
Authors: FormalFrontier
-/
import RepresentationTheory.SymmetricGroup.PartitionDominance
import RepresentationTheory.MonoidAlgebra.PartitionSubmoduleSandwich

set_option linter.style.openClassical false
set_option linter.style.longLine false

namespace RepresentationTheory.PartitionMonoidAlgebra

noncomputable section
open scoped Classical

private abbrev G' (n : ℕ) := Equiv.Perm (Fin n)

/-- An element of the displayed monoid algebra depending on a natural number and one of its partitions. -/
def partitionIndexedElement' (k : Type*) [CommRing k] (n : ℕ) (la : Nat.Partition n) :
    MonoidAlgebra k (G' n) :=
  haveI : DecidablePred (· ∈ RepresentationTheory.SymmetricGroup.PartitionAuxiliaryConstructions.auxiliaryPartitionPermutationSubgroupB n la) := Classical.decPred _
  ∑ g : (RepresentationTheory.SymmetricGroup.PartitionAuxiliaryConstructions.auxiliaryPartitionPermutationSubgroupB n la), MonoidAlgebra.of k _ g.val

/-- An element of the displayed monoid algebra depending on a natural number and one of its partitions. -/
def partitionIndexedElement (k : Type*) [CommRing k] (n : ℕ) (la : Nat.Partition n) :
    MonoidAlgebra k (G' n) :=
  haveI : DecidablePred (· ∈ RepresentationTheory.SymmetricGroup.PartitionAuxiliaryConstructions.auxiliaryPartitionPermutationSubgroupA n la) := Classical.decPred _
  ∑ g : (RepresentationTheory.SymmetricGroup.PartitionAuxiliaryConstructions.auxiliaryPartitionPermutationSubgroupA n la),
    ((↑(Equiv.Perm.sign g.val) : ℤ) : k) • MonoidAlgebra.of k _ g.val

/-- The displayed element indexed by a partition equals the product of the two displayed factors. -/
theorem partitionIndexedElement_eq_mul (k : Type*) [CommRing k] (n : ℕ)
    (la : Nat.Partition n) :
    RepresentationTheory.GeneralLinearGroup.WeightCharacter.partitionSymmetrizer k n la = partitionIndexedElement k n la * partitionIndexedElement' k n la :=
  rfl

/-- Multiplying the displayed element on the right by the monoid-algebra embedding of a member of the displayed set leaves it unchanged. -/
theorem mul_monoidAlgebra_of_eq_self_of_mem {k : Type*} [CommRing k] {n : ℕ} {la : Nat.Partition n}
    (p : G' n) (hp : p ∈ RepresentationTheory.SymmetricGroup.PartitionAuxiliaryConstructions.auxiliaryPartitionPermutationSubgroupB n la) :
    partitionIndexedElement' k n la * MonoidAlgebra.of k (G' n) p = partitionIndexedElement' k n la := by
  classical
  simp only [partitionIndexedElement']
  rw [Finset.sum_mul]
  simp_rw [← (MonoidAlgebra.of k (G' n)).map_mul]
  exact Fintype.sum_equiv (Equiv.mulRight ⟨p, hp⟩) _ _
    (fun g => by simp [Subgroup.coe_mul])

/-- For a member of the displayed set, left multiplication by its monoid-algebra embedding equals scalar multiplication by its permutation sign. -/
theorem monoidAlgebra_of_mul_eq_sign_smul_of_mem {k : Type*} [CommRing k] {n : ℕ}
    {la : Nat.Partition n} (q : G' n) (hq : q ∈ RepresentationTheory.SymmetricGroup.PartitionAuxiliaryConstructions.auxiliaryPartitionPermutationSubgroupA n la) :
    MonoidAlgebra.of k (G' n) q * partitionIndexedElement k n la =
      ((↑(↑(Equiv.Perm.sign q) : ℤ) : k)) • partitionIndexedElement k n la := by
  classical
  simp only [partitionIndexedElement]
  rw [Finset.mul_sum, Finset.smul_sum]
  simp_rw [Algebra.mul_smul_comm, ← (MonoidAlgebra.of k (G' n)).map_mul, smul_smul]
  refine Fintype.sum_equiv (Equiv.mulLeft ⟨q, hq⟩) _ _ (fun g => ?_)
  simp only [Equiv.coe_mulLeft, Subgroup.coe_mul]
  congr 1
  have hZ : ((↑(Equiv.Perm.sign q) : ℤ)) * ((↑(Equiv.Perm.sign q) : ℤ)) = 1 := by
    rw [← Units.val_mul, Int.units_mul_self, Units.val_one]
  have hsqq : ((↑(↑(Equiv.Perm.sign q) : ℤ) : k)) * ((↑(↑(Equiv.Perm.sign q) : ℤ) : k)) = 1 := by
    rw [← Int.cast_mul, hZ, Int.cast_one]
  simp only [Equiv.Perm.sign_mul, Units.val_mul, Int.cast_mul]
  rw [← mul_assoc, hsqq, one_mul]

/-- If one partition does not dominate the other, the product of the displayed left factor, the monoid-algebra embedding of a permutation, and the displayed right factor is zero. -/
theorem left_mul_monoidAlgebra_of_perm_mul_right_eq_zero_of_not_dominates (k : Type*) [Field k] [CharZero k] (n : ℕ)
    (la mu : Nat.Partition n)
    (h : ¬ RepresentationTheory.SymmetricGroup.PartitionDominance.Partition.Dominates mu la)
    (σ : Equiv.Perm (Fin n)) :
    partitionIndexedElement' k n la * MonoidAlgebra.of k (G' n) σ *
      partitionIndexedElement k n mu = 0 := by
  obtain ⟨t, ht_row, hconj_col, ht_sign⟩ := RepresentationTheory.SymmetricGroup.PartitionDominance.dominates_aux n la mu h σ
  let of' := MonoidAlgebra.of k (G' n)
  set a := partitionIndexedElement' k n la
  set b := partitionIndexedElement k n mu
  set val := a * of' σ * b
  have hconj_sign : (↑(↑(Equiv.Perm.sign (σ⁻¹ * t * σ)) : ℤ) : k) = -1 := by
    simp [Equiv.Perm.sign_mul, ht_sign]
  have hab : a * of' t = a := mul_monoidAlgebra_of_eq_self_of_mem t ht_row
  have hcol := monoidAlgebra_of_mul_eq_sign_smul_of_mem (k := k) (σ⁻¹ * t * σ) hconj_col
  have hval_neg : val = (-1 : k) • val := by
    have step : a * of' σ = a * of' σ * of' (σ⁻¹ * t * σ) := by
      conv_lhs => rw [show a = a * of' t from hab.symm]
      rw [mul_assoc a (of' t) (of' σ), ← map_mul of' t σ,
          show t * σ = σ * (σ⁻¹ * t * σ) from by group,
          map_mul of' σ (σ⁻¹ * t * σ), ← mul_assoc]
    change a * of' σ * b = (-1 : k) • (a * of' σ * b)
    conv_lhs => rw [step, mul_assoc (a * of' σ) (of' (σ⁻¹ * t * σ)) b, hcol]
    rw [mul_smul_comm, hconj_sign]
  rw [neg_one_smul] at hval_neg
  have hadd : val + val = 0 := by nth_rw 1 [hval_neg]; exact neg_add_cancel val
  have h2 : (2 : k) • val = 0 := by rwa [two_smul]
  exact (smul_eq_zero.mp h2).resolve_left two_ne_zero

/-- If one partition does not dominate the other, multiplying the displayed left factor, any monoid-algebra element, and the displayed right factor gives zero. -/
theorem left_mul_mul_right_eq_zero_of_not_dominates (k : Type*) [Field k] [CharZero k] (n : ℕ)
    (la mu : Nat.Partition n)
    (h : ¬ RepresentationTheory.SymmetricGroup.PartitionDominance.Partition.Dominates mu la)
    (x : MonoidAlgebra k (G' n)) :
    partitionIndexedElement' k n la * x * partitionIndexedElement k n mu = 0 := by
  induction x using MonoidAlgebra.induction_linear with
  | zero => simp
  | add x y hx hy => rw [mul_add, add_mul, hx, hy, add_zero]
  | single g c =>
    have hsg : MonoidAlgebra.single g c =
        c • MonoidAlgebra.of k (G' n) g := by
      simp [MonoidAlgebra.of_apply, mul_one]
    rw [hsg, mul_smul_comm, smul_mul_assoc, left_mul_monoidAlgebra_of_perm_mul_right_eq_zero_of_not_dominates k n la mu h g, smul_zero]

/-- The square of the displayed element indexed by a partition is nonzero over a characteristic-zero field. -/
theorem partitionIndexedElement_mul_self_ne_zero (k : Type*) [Field k] [CharZero k] (n : ℕ)
    (la : Nat.Partition n) :
    RepresentationTheory.GeneralLinearGroup.WeightCharacter.partitionSymmetrizer k n la * RepresentationTheory.GeneralLinearGroup.WeightCharacter.partitionSymmetrizer k n la ≠ 0 := by
  obtain ⟨α, hα⟩ := RepresentationTheory.GeneralLinearGroup.WeightCharacter.partitionSymmetrizer_sq_smul k n la
  have hα_ne := RepresentationTheory.MonoidAlgebra.PartitionSubmoduleSandwich.ne_zero_of_self_mul_eq_smul k n la α hα
  intro hsq0
  have hαc : α • RepresentationTheory.GeneralLinearGroup.WeightCharacter.partitionSymmetrizer k n la = 0 := by rw [← hα, hsq0]
  have hc0 : RepresentationTheory.GeneralLinearGroup.WeightCharacter.partitionSymmetrizer k n la = 0 :=
    (smul_eq_zero.mp hαc).resolve_left hα_ne
  have hone : (RepresentationTheory.GeneralLinearGroup.WeightCharacter.partitionSymmetrizer k n la).coeff 1 = 1 := by
    rw [RepresentationTheory.GeneralLinearGroup.WeightCharacter.partitionSymmetrizer_eq_map_int k n la]
    simp [RepresentationTheory.GeneralLinearGroup.WeightCharacter.integralPartitionSymmetrizer_coeff_one]
  rw [hc0] at hone
  simp at hone

/-- If one partition does not dominate the other, the displayed left factor annihilates every value from the displayed subtype. -/
theorem left_mul_subtype_val_eq_zero_of_not_dominates (k : Type*) [Field k] [CharZero k]
    (n : ℕ) (la mu : Nat.Partition n)
    (h : ¬ RepresentationTheory.SymmetricGroup.PartitionDominance.Partition.Dominates mu la)
    (v : RepresentationTheory.MonoidAlgebra.PartitionSubmoduleSandwich.partitionSubmodule k n mu) :
    RepresentationTheory.GeneralLinearGroup.WeightCharacter.partitionSymmetrizer k n la * (v : MonoidAlgebra k (G' n)) = 0 := by
  obtain ⟨x, hx⟩ := Submodule.mem_span_singleton.mp v.2
  rw [← hx]
  change RepresentationTheory.GeneralLinearGroup.WeightCharacter.partitionSymmetrizer k n la * (x * RepresentationTheory.GeneralLinearGroup.WeightCharacter.partitionSymmetrizer k n mu) = 0
  rw [partitionIndexedElement_eq_mul k n la, partitionIndexedElement_eq_mul k n mu]
  rw [show partitionIndexedElement k n la * partitionIndexedElement' k n la *
    (x * (partitionIndexedElement k n mu * partitionIndexedElement' k n mu)) =
    partitionIndexedElement k n la *
      (partitionIndexedElement' k n la * x * partitionIndexedElement k n mu) *
      partitionIndexedElement' k n mu from by simp only [mul_assoc],
    left_mul_mul_right_eq_zero_of_not_dominates k n la mu h, mul_zero, zero_mul]

/-- Distinct partitions give subtypes for which the displayed linear equivalence type is empty. -/
theorem isEmpty_linearEquiv_between_subtypes_of_ne (k : Type*) [Field k] [CharZero k]
    (n : ℕ) (la mu : Nat.Partition n) (h : la ≠ mu) :
    IsEmpty ((RepresentationTheory.MonoidAlgebra.PartitionSubmoduleSandwich.partitionSubmodule k n la) ≃ₗ[MonoidAlgebra k (G' n)] (RepresentationTheory.MonoidAlgebra.PartitionSubmoduleSandwich.partitionSubmodule k n mu)) := by
  have hdom_or :
      ¬ RepresentationTheory.SymmetricGroup.PartitionDominance.Partition.Dominates mu la ∨
      ¬ RepresentationTheory.SymmetricGroup.PartitionDominance.Partition.Dominates la mu := by
    by_contra hall
    push Not at hall
    exact h (RepresentationTheory.SymmetricGroup.PartitionDominance.Partition.Dominates.antisymm
      hall.1 hall.2).symm
  constructor
  intro φ
  set c_la := RepresentationTheory.GeneralLinearGroup.WeightCharacter.partitionSymmetrizer k n la
  set c_mu := RepresentationTheory.GeneralLinearGroup.WeightCharacter.partitionSymmetrizer k n mu
  have hc_la_mem : c_la ∈ RepresentationTheory.MonoidAlgebra.PartitionSubmoduleSandwich.partitionSubmodule k n la := Submodule.subset_span rfl
  have hc_mu_mem : c_mu ∈ RepresentationTheory.MonoidAlgebra.PartitionSubmoduleSandwich.partitionSubmodule k n mu := Submodule.subset_span rfl
  suffices ∀ (V V' : Submodule (MonoidAlgebra k (G' n)) (MonoidAlgebra k (G' n)))
      (c : MonoidAlgebra k (G' n)) (hc_mem : c ∈ V')
      (hc_sq : c * c ≠ 0)
      (hvanish : ∀ v : V, c * (v : MonoidAlgebra k (G' n)) = 0)
      (ψ : V' ≃ₗ[MonoidAlgebra k (G' n)] V), False by
    rcases hdom_or with h1 | h2
    · exact this (RepresentationTheory.MonoidAlgebra.PartitionSubmoduleSandwich.partitionSubmodule k n mu) (RepresentationTheory.MonoidAlgebra.PartitionSubmoduleSandwich.partitionSubmodule k n la) c_la hc_la_mem
        (partitionIndexedElement_mul_self_ne_zero k n la)
        (fun v => left_mul_subtype_val_eq_zero_of_not_dominates k n la mu h1 v) φ
    · exact this (RepresentationTheory.MonoidAlgebra.PartitionSubmoduleSandwich.partitionSubmodule k n la) (RepresentationTheory.MonoidAlgebra.PartitionSubmoduleSandwich.partitionSubmodule k n mu) c_mu hc_mu_mem
        (partitionIndexedElement_mul_self_ne_zero k n mu)
        (fun v => left_mul_subtype_val_eq_zero_of_not_dominates k n mu la h2 v) φ.symm
  intro V V' c hc_mem hc_sq hvanish ψ
  have hc_sq_mem : c * c ∈ V' := V'.smul_mem c hc_mem
  have h1 : c * (ψ ⟨c, hc_mem⟩ : MonoidAlgebra k (G' n)) = 0 := hvanish (ψ ⟨c, hc_mem⟩)
  have h2 : c * (ψ ⟨c, hc_mem⟩ : MonoidAlgebra k (G' n)) =
      (ψ ⟨c * c, hc_sq_mem⟩ : MonoidAlgebra k (G' n)) := by
    change (c • ψ ⟨c, hc_mem⟩ : V).val = (ψ ⟨c * c, hc_sq_mem⟩ : V).val
    congr 1
    rw [← ψ.map_smul]; rfl
  have h3 : (ψ ⟨c * c, hc_sq_mem⟩ : MonoidAlgebra k (G' n)) = 0 := h2 ▸ h1
  have h4 : (⟨c * c, hc_sq_mem⟩ : V') = 0 :=
    ψ.injective (Subtype.ext (by simp [h3, map_zero]))
  exact hc_sq (congr_arg Subtype.val h4)

end

end RepresentationTheory.PartitionMonoidAlgebra
