/-
Copyright (c) 2026 mathlib-initiative. All rights reserved.
Released under Apache 2.0 license as described in the file LICENCE.
Authors: Kim Morrison
-/
import RepresentationTheory.LinearAlgebra.TensorOperations
import RepresentationTheory.Alignment.Attribute

/-! # Alternating tensors -/

namespace RepresentationTheory.LinearAlgebra.AlternatingTensors

open PiTensorProduct
open scoped TensorProduct

section Subspaces

variable (k : Type*) [Field k] (V : Type*) [AddCommGroup V] [Module k V]

/-- The submodule specified by the displayed construction. -/
def submodule_aux1 (n : ℕ) : Submodule k (RepresentationTheory.LinearAlgebra.TensorOperations.AuxiliaryType_aux2 k V n) where
  carrier := {T | ∀ i j : Fin n, i ≠ j → RepresentationTheory.LinearAlgebra.TensorOperations.linearEquiv_aux1 (Equiv.swap i j) T = T}
  add_mem' hx hy i j hij := by rw [map_add, hx i j hij, hy i j hij]
  zero_mem' i j _ := map_zero _
  smul_mem' c x hx i j hij := by rw [map_smul, hx i j hij]

/-- The submodule specified by the displayed construction. -/
def submodule (n : ℕ) : Submodule k (RepresentationTheory.LinearAlgebra.TensorOperations.AuxiliaryType_aux2 k V n) where
  carrier := {T | ∀ i j : Fin n, i ≠ j → RepresentationTheory.LinearAlgebra.TensorOperations.linearEquiv_aux1 (Equiv.swap i j) T = -T}
  add_mem' hx hy i j hij := by rw [map_add, hx i j hij, hy i j hij, neg_add]
  zero_mem' i j _ := by rw [map_zero, neg_zero]
  smul_mem' c x hx i j hij := by rw [map_smul, hx i j hij, smul_neg]

variable {k V}

/-- The specified element belongs to the indicated submodule. -/
lemma mem_submodule_aux3 {n : ℕ} {T : RepresentationTheory.LinearAlgebra.TensorOperations.AuxiliaryType_aux2 k V n} :
    T ∈ submodule_aux1 k V n ↔ ∀ i j : Fin n, i ≠ j → RepresentationTheory.LinearAlgebra.TensorOperations.linearEquiv_aux1 (Equiv.swap i j) T = T :=
  Iff.rfl

/-- The specified element belongs to the indicated submodule. -/
lemma mem_submodule_aux2 {n : ℕ} {T : RepresentationTheory.LinearAlgebra.TensorOperations.AuxiliaryType_aux2 k V n} :
    T ∈ submodule k V n ↔ ∀ i j : Fin n, i ≠ j → RepresentationTheory.LinearAlgebra.TensorOperations.linearEquiv_aux1 (Equiv.swap i j) T = -T :=
  Iff.rfl

/-- The sign of the displayed permutation has the stated value. -/
lemma permSign_eq_aux2 (k : Type*) [Field k] {n : ℕ} (σ : Equiv.Perm (Fin n)) :
    ((Equiv.Perm.sign σ : ℤ) : k) * ((Equiv.Perm.sign σ : ℤ) : k) = 1 := by
  rw [← Int.cast_mul, ← Units.val_mul, Int.units_mul_self, Units.val_one, Int.cast_one]

/-- Every permutation fixes a tensor in the displayed symmetric submodule. -/
lemma symmetricTensor_perm {n : ℕ} {T : RepresentationTheory.LinearAlgebra.TensorOperations.AuxiliaryType_aux2 k V n}
    (hT : T ∈ submodule_aux1 k V n) (σ : Equiv.Perm (Fin n)) : RepresentationTheory.LinearAlgebra.TensorOperations.linearEquiv_aux1 σ T = T := by
  induction σ using Equiv.Perm.swap_induction_on with
  | one => exact RepresentationTheory.LinearAlgebra.TensorOperations.map_apply_aux4 T
  | swap_mul τ i j hij ihτ => rw [RepresentationTheory.LinearAlgebra.TensorOperations.map_apply_aux3, ihτ, hT i j hij]

/-- A permutation acts on a tensor in the displayed alternating submodule by its sign. -/
lemma alternatingTensor_perm {n : ℕ} {T : RepresentationTheory.LinearAlgebra.TensorOperations.AuxiliaryType_aux2 k V n}
    (hT : T ∈ submodule k V n) (σ : Equiv.Perm (Fin n)) :
    RepresentationTheory.LinearAlgebra.TensorOperations.linearEquiv_aux1 σ T = ((Equiv.Perm.sign σ : ℤ) : k) • T := by
  induction σ using Equiv.Perm.swap_induction_on with
  | one => simp
  | swap_mul τ i j hij ihτ =>
      rw [RepresentationTheory.LinearAlgebra.TensorOperations.map_apply_aux3, ihτ, map_smul, hT i j hij, Equiv.Perm.sign_mul, Equiv.Perm.sign_swap hij,
        Units.val_mul]
      push_cast
      rw [smul_neg, neg_mul, one_mul, neg_smul]

end Subspaces

section Averaging

variable (k : Type*) [Field k] (V : Type*) [AddCommGroup V] [Module k V]

/-- A linear map between the displayed modules. -/
noncomputable def linearMap_aux1 (n : ℕ) : RepresentationTheory.LinearAlgebra.TensorOperations.AuxiliaryType_aux2 k V n →ₗ[k] RepresentationTheory.LinearAlgebra.TensorOperations.AuxiliaryType_aux2 k V n :=
  (n.factorial : k)⁻¹ • ∑ σ : Equiv.Perm (Fin n), (RepresentationTheory.LinearAlgebra.TensorOperations.linearEquiv_aux1 σ).toLinearMap

/-- A linear map between the displayed modules. -/
noncomputable def linearMap (n : ℕ) : RepresentationTheory.LinearAlgebra.TensorOperations.AuxiliaryType_aux2 k V n →ₗ[k] RepresentationTheory.LinearAlgebra.TensorOperations.AuxiliaryType_aux2 k V n :=
  (n.factorial : k)⁻¹ • ∑ σ : Equiv.Perm (Fin n),
    ((Equiv.Perm.sign σ : ℤ) : k) • (RepresentationTheory.LinearAlgebra.TensorOperations.linearEquiv_aux1 σ).toLinearMap

variable {V}

/-- The displayed natural-number scalar is nonzero. -/
lemma natCast_ne_zero [CharZero k] (n : ℕ) : (n.factorial : k) ≠ 0 :=
  Nat.cast_ne_zero.mpr n.factorial_ne_zero

/-- The specified element is nonzero. -/
lemma distinguished_ne_zero {n : ℕ} (hfac : (n.factorial : k) ≠ 0) (hn : 2 ≤ n) :
    (2 : k) ≠ 0 := by
  intro h2
  refine hfac ?_
  obtain ⟨m, hm⟩ := Nat.dvd_factorial (by norm_num) hn
  rw [hm]
  push_cast
  rw [h2, zero_mul]

/-- The two displayed expressions are equal. -/
lemma displayed_eq (n : ℕ) : Fintype.card (Equiv.Perm (Fin n)) = n.factorial := by
  simp [Fintype.card_perm]

variable {k}

/-- The existence of two distinct elements of `Fin n` implies `2 ≤ n`. -/
lemma two_le_of_fin_ne {n : ℕ} {i j : Fin n} (hij : i ≠ j) : 2 ≤ n := by
  have hi := i.isLt
  have hj := j.isLt
  have : (i : ℕ) ≠ (j : ℕ) := fun h => hij (Fin.ext h)
  omega

/-- The displayed map sends the specified input to the stated value. -/
lemma map_apply_aux3 {n : ℕ} (T : RepresentationTheory.LinearAlgebra.TensorOperations.AuxiliaryType_aux2 k V n) :
    linearMap_aux1 k V n T = (n.factorial : k)⁻¹ • ∑ σ : Equiv.Perm (Fin n), RepresentationTheory.LinearAlgebra.TensorOperations.linearEquiv_aux1 σ T := by
  simp [linearMap_aux1, LinearMap.sum_apply]

/-- The alternating projection is the factorial-normalized signed sum over all permutations. -/
lemma alternatingProjection_apply {n : ℕ} (T : RepresentationTheory.LinearAlgebra.TensorOperations.AuxiliaryType_aux2 k V n) :
    linearMap k V n T
      = (n.factorial : k)⁻¹ • ∑ σ : Equiv.Perm (Fin n),
          ((Equiv.Perm.sign σ : ℤ) : k) • RepresentationTheory.LinearAlgebra.TensorOperations.linearEquiv_aux1 σ T := by
  simp [linearMap, LinearMap.sum_apply]

/-- The two displayed expressions are equal. -/
lemma displayed_eq_aux5 {n : ℕ} (T : RepresentationTheory.LinearAlgebra.TensorOperations.AuxiliaryType_aux2 k V n) :
    (∑ _σ : Equiv.Perm (Fin n), T) = (n.factorial : k) • T := by
  rw [Finset.sum_const, Finset.card_univ, displayed_eq, Nat.cast_smul_eq_nsmul]

/-- The displayed map sends the specified input to the stated value. -/
lemma map_apply_aux5 {n : ℕ} (τ : Equiv.Perm (Fin n)) (T : RepresentationTheory.LinearAlgebra.TensorOperations.AuxiliaryType_aux2 k V n) :
    linearMap_aux1 k V n (RepresentationTheory.LinearAlgebra.TensorOperations.linearEquiv_aux1 τ T) = linearMap_aux1 k V n T := by
  rw [map_apply_aux3, map_apply_aux3]
  congr 1
  refine Fintype.sum_equiv (Equiv.mulRight τ) _ _ fun σ => ?_
  rw [Equiv.coe_mulRight, RepresentationTheory.LinearAlgebra.TensorOperations.map_apply_aux3]

/-- The displayed map sends the specified input to the stated value. -/
lemma map_apply_aux2 {n : ℕ} (τ : Equiv.Perm (Fin n)) (T : RepresentationTheory.LinearAlgebra.TensorOperations.AuxiliaryType_aux2 k V n) :
    RepresentationTheory.LinearAlgebra.TensorOperations.linearEquiv_aux1 τ (linearMap_aux1 k V n T) = linearMap_aux1 k V n T := by
  rw [map_apply_aux3, map_smul, map_sum]
  congr 1
  refine Fintype.sum_equiv (Equiv.mulLeft τ) _ _ fun σ => ?_
  rw [Equiv.coe_mulLeft, RepresentationTheory.LinearAlgebra.TensorOperations.map_apply_aux3]

/-- The specified element belongs to the indicated submodule. -/
lemma mem_submodule_aux8 {n : ℕ} (T : RepresentationTheory.LinearAlgebra.TensorOperations.AuxiliaryType_aux2 k V n) :
    linearMap_aux1 k V n T ∈ submodule_aux1 k V n :=
  fun _ _ _ => map_apply_aux2 _ T

/-- Permuting an alternating projection scales it by the sign of the permutation. -/
lemma alternatingProjection_perm {n : ℕ} (τ : Equiv.Perm (Fin n)) (T : RepresentationTheory.LinearAlgebra.TensorOperations.AuxiliaryType_aux2 k V n) :
    RepresentationTheory.LinearAlgebra.TensorOperations.linearEquiv_aux1 τ (linearMap k V n T)
      = ((Equiv.Perm.sign τ : ℤ) : k) • linearMap k V n T := by
  have key : ∑ σ : Equiv.Perm (Fin n), RepresentationTheory.LinearAlgebra.TensorOperations.linearEquiv_aux1 τ (((Equiv.Perm.sign σ : ℤ) : k) • RepresentationTheory.LinearAlgebra.TensorOperations.linearEquiv_aux1 σ T)
      = ∑ σ : Equiv.Perm (Fin n),
          ((Equiv.Perm.sign τ : ℤ) : k) • (((Equiv.Perm.sign σ : ℤ) : k) • RepresentationTheory.LinearAlgebra.TensorOperations.linearEquiv_aux1 σ T) := by
    refine Fintype.sum_equiv (Equiv.mulLeft τ)
      (fun σ => RepresentationTheory.LinearAlgebra.TensorOperations.linearEquiv_aux1 τ (((Equiv.Perm.sign σ : ℤ) : k) • RepresentationTheory.LinearAlgebra.TensorOperations.linearEquiv_aux1 σ T))
      (fun ρ => ((Equiv.Perm.sign τ : ℤ) : k) • (((Equiv.Perm.sign ρ : ℤ) : k) • RepresentationTheory.LinearAlgebra.TensorOperations.linearEquiv_aux1 ρ T))
      fun σ => ?_
    rw [Equiv.coe_mulLeft, map_smul, RepresentationTheory.LinearAlgebra.TensorOperations.map_apply_aux3, smul_smul]
    congr 1
    simp only [Equiv.Perm.sign_mul, Units.val_mul, Int.cast_mul]
    rw [← mul_assoc, permSign_eq_aux2, one_mul]
  rw [alternatingProjection_apply, map_smul, map_sum, key, ← Finset.smul_sum]
  exact smul_comm _ _ _

/-- The specified element belongs to the indicated submodule. -/
lemma mem_submodule_aux1 {n : ℕ} (T : RepresentationTheory.LinearAlgebra.TensorOperations.AuxiliaryType_aux2 k V n) :
    linearMap k V n T ∈ submodule k V n := by
  intro i j hij
  rw [alternatingProjection_perm, Equiv.Perm.sign_swap hij]
  push_cast
  rw [neg_one_smul]

/-- The displayed map sends the specified input to the stated value. -/
lemma map_apply_aux4 {n : ℕ} (hfac : (n.factorial : k) ≠ 0) {T : RepresentationTheory.LinearAlgebra.TensorOperations.AuxiliaryType_aux2 k V n}
    (hT : T ∈ submodule_aux1 k V n) : linearMap_aux1 k V n T = T := by
  rw [map_apply_aux3,
    Finset.sum_congr rfl fun σ _ => symmetricTensor_perm hT σ,
    displayed_eq_aux5, smul_smul, inv_mul_cancel₀ hfac, one_smul]

/-- The displayed map sends the specified input to the stated value. -/
lemma map_apply {n : ℕ} (hfac : (n.factorial : k) ≠ 0) {T : RepresentationTheory.LinearAlgebra.TensorOperations.AuxiliaryType_aux2 k V n}
    (hT : T ∈ submodule k V n) : linearMap k V n T = T := by
  rw [alternatingProjection_apply,
    Finset.sum_congr rfl fun σ _ => by
      rw [alternatingTensor_perm hT σ, smul_smul, permSign_eq_aux2,
        one_smul],
    displayed_eq_aux5, smul_smul, inv_mul_cancel₀ hfac, one_smul]

/-- The two displayed expressions are equal. -/
theorem displayed_eq_aux4 {n : ℕ} (hfac : (n.factorial : k) ≠ 0) :
    LinearMap.range (linearMap_aux1 k V n) = submodule_aux1 k V n := by
  refine le_antisymm ?_ fun T hT => ⟨T, map_apply_aux4 hfac hT⟩
  rintro _ ⟨T, rfl⟩
  exact mem_submodule_aux8 T

/-- The two displayed expressions are equal. -/
theorem displayed_eq_aux3 {n : ℕ} (hfac : (n.factorial : k) ≠ 0) :
    LinearMap.range (linearMap k V n) = submodule k V n := by
  refine le_antisymm ?_ fun T hT => ⟨T, map_apply hfac hT⟩
  rintro _ ⟨T, rfl⟩
  exact mem_submodule_aux1 T

end Averaging

section Kernels

variable {k : Type*} [Field k] {V : Type*} [AddCommGroup V] [Module k V]

/-- The specified element belongs to the indicated submodule. -/
lemma mem_submodule_aux5 {n : ℕ} (σ : Equiv.Perm (Fin n)) (T : RepresentationTheory.LinearAlgebra.TensorOperations.AuxiliaryType_aux2 k V n) :
    T - RepresentationTheory.LinearAlgebra.TensorOperations.linearEquiv_aux1 σ T ∈ RepresentationTheory.LinearAlgebra.TensorOperations.submodule_aux1 k V n := by
  induction σ using Equiv.Perm.swap_induction_on with
  | one => simp
  | swap_mul τ i j hij ihτ =>
      have hgen : RepresentationTheory.LinearAlgebra.TensorOperations.linearEquiv_aux1 τ T - RepresentationTheory.LinearAlgebra.TensorOperations.linearEquiv_aux1 (Equiv.swap i j) (RepresentationTheory.LinearAlgebra.TensorOperations.linearEquiv_aux1 τ T) ∈ RepresentationTheory.LinearAlgebra.TensorOperations.submodule_aux1 k V n :=
        Submodule.subset_span ⟨RepresentationTheory.LinearAlgebra.TensorOperations.linearEquiv_aux1 τ T, i, j, hij, rfl⟩
      have hsum := Submodule.add_mem _ ihτ hgen
      rwa [sub_add_sub_cancel, ← RepresentationTheory.LinearAlgebra.TensorOperations.map_apply_aux3] at hsum

/-- The specified element belongs to the indicated submodule. -/
lemma mem_submodule {n : ℕ} {i j : Fin n} (hij : i ≠ j)
    (T : RepresentationTheory.LinearAlgebra.TensorOperations.AuxiliaryType_aux2 k V n) :
    T + RepresentationTheory.LinearAlgebra.TensorOperations.linearEquiv_aux1 (Equiv.swap i j) T ∈ RepresentationTheory.LinearAlgebra.TensorOperations.submodule k V n := by
  refine Submodule.subset_span ⟨i, j, hij, ?_⟩
  rw [map_add, ← RepresentationTheory.LinearAlgebra.TensorOperations.map_apply_aux3, Equiv.swap_mul_self, RepresentationTheory.LinearAlgebra.TensorOperations.map_apply_aux4, add_comm]

/-- The specified element belongs to the indicated submodule. -/
lemma mem_submodule_aux6 {n : ℕ} (σ : Equiv.Perm (Fin n))
    (T : RepresentationTheory.LinearAlgebra.TensorOperations.AuxiliaryType_aux2 k V n) :
    T - ((Equiv.Perm.sign σ : ℤ) : k) • RepresentationTheory.LinearAlgebra.TensorOperations.linearEquiv_aux1 σ T ∈ RepresentationTheory.LinearAlgebra.TensorOperations.submodule k V n := by
  induction σ using Equiv.Perm.swap_induction_on with
  | one => simp
  | swap_mul τ i j hij ihτ =>
      set U : RepresentationTheory.LinearAlgebra.TensorOperations.AuxiliaryType_aux2 k V n := ((Equiv.Perm.sign τ : ℤ) : k) • RepresentationTheory.LinearAlgebra.TensorOperations.linearEquiv_aux1 τ T with hU
      have hgen : U + RepresentationTheory.LinearAlgebra.TensorOperations.linearEquiv_aux1 (Equiv.swap i j) U ∈ RepresentationTheory.LinearAlgebra.TensorOperations.submodule k V n :=
        mem_submodule hij U
      have hsum := Submodule.add_mem _ ihτ hgen
      have hrw : T - U + (U + RepresentationTheory.LinearAlgebra.TensorOperations.linearEquiv_aux1 (Equiv.swap i j) U)
          = T - ((Equiv.Perm.sign (Equiv.swap i j * τ) : ℤ) : k)
              • RepresentationTheory.LinearAlgebra.TensorOperations.linearEquiv_aux1 (Equiv.swap i j * τ) T := by
        rw [Equiv.Perm.sign_mul, Equiv.Perm.sign_swap hij, Units.val_mul, RepresentationTheory.LinearAlgebra.TensorOperations.map_apply_aux3, hU,
          map_smul]
        push_cast
        rw [neg_one_mul, neg_smul, sub_neg_eq_add]
        abel
      rwa [hrw] at hsum

/-- The specified element belongs to the indicated submodule. -/
lemma mem_submodule_aux7 {n : ℕ} (hfac : (n.factorial : k) ≠ 0)
    (T : RepresentationTheory.LinearAlgebra.TensorOperations.AuxiliaryType_aux2 k V n) :
    T - linearMap_aux1 k V n T ∈ RepresentationTheory.LinearAlgebra.TensorOperations.submodule_aux1 k V n := by
  have key : T - linearMap_aux1 k V n T
      = (n.factorial : k)⁻¹ • ∑ σ : Equiv.Perm (Fin n), (T - RepresentationTheory.LinearAlgebra.TensorOperations.linearEquiv_aux1 σ T) := by
    rw [Finset.sum_sub_distrib, displayed_eq_aux5, smul_sub, smul_smul, inv_mul_cancel₀ hfac,
      one_smul, map_apply_aux3]
  rw [key]
  exact Submodule.smul_mem _ _
    (Submodule.sum_mem _ fun σ _ => mem_submodule_aux5 σ T)

/-- The specified element belongs to the indicated submodule. -/
lemma mem_submodule_aux4 {n : ℕ} (hfac : (n.factorial : k) ≠ 0)
    (T : RepresentationTheory.LinearAlgebra.TensorOperations.AuxiliaryType_aux2 k V n) :
    T - linearMap k V n T ∈ RepresentationTheory.LinearAlgebra.TensorOperations.submodule k V n := by
  have key : T - linearMap k V n T
      = (n.factorial : k)⁻¹ • ∑ σ : Equiv.Perm (Fin n),
          (T - ((Equiv.Perm.sign σ : ℤ) : k) • RepresentationTheory.LinearAlgebra.TensorOperations.linearEquiv_aux1 σ T) := by
    rw [Finset.sum_sub_distrib, displayed_eq_aux5, smul_sub, smul_smul, inv_mul_cancel₀ hfac,
      one_smul, alternatingProjection_apply]
  rw [key]
  exact Submodule.smul_mem _ _
    (Submodule.sum_mem _ fun σ _ => mem_submodule_aux6 σ T)

/-- The displayed map sends the specified input to the stated value. -/
lemma map_apply_aux1 {n : ℕ} (hfac : (n.factorial : k) ≠ 0) {i j : Fin n}
    (hij : i ≠ j) {T : RepresentationTheory.LinearAlgebra.TensorOperations.AuxiliaryType_aux2 k V n} (hT : RepresentationTheory.LinearAlgebra.TensorOperations.linearEquiv_aux1 (Equiv.swap i j) T = T) :
    linearMap k V n T = 0 := by
  set S : RepresentationTheory.LinearAlgebra.TensorOperations.AuxiliaryType_aux2 k V n :=
    ∑ σ : Equiv.Perm (Fin n), ((Equiv.Perm.sign σ : ℤ) : k) • RepresentationTheory.LinearAlgebra.TensorOperations.linearEquiv_aux1 σ T with hS
  have hreindex : ∑ σ : Equiv.Perm (Fin n),
      ((Equiv.Perm.sign (σ * Equiv.swap i j) : ℤ) : k) • RepresentationTheory.LinearAlgebra.TensorOperations.linearEquiv_aux1 (σ * Equiv.swap i j) T = S :=
    Fintype.sum_equiv (Equiv.mulRight (Equiv.swap i j)) _ _ fun σ => by
      rw [Equiv.coe_mulRight]
  have hneg : ∑ σ : Equiv.Perm (Fin n),
      ((Equiv.Perm.sign (σ * Equiv.swap i j) : ℤ) : k) • RepresentationTheory.LinearAlgebra.TensorOperations.linearEquiv_aux1 (σ * Equiv.swap i j) T = -S := by
    rw [hS, ← Finset.sum_neg_distrib]
    refine Finset.sum_congr rfl fun σ _ => ?_
    rw [Equiv.Perm.sign_mul, Equiv.Perm.sign_swap hij, Units.val_mul, RepresentationTheory.LinearAlgebra.TensorOperations.map_apply_aux3, hT]
    push_cast
    rw [mul_neg_one, neg_smul]
  have h2 : (2 : k) ≠ 0 := distinguished_ne_zero k hfac (two_le_of_fin_ne hij)
  have hSS : (2 : k) • S = 0 := by
    rw [two_smul]
    nth_rewrite 1 [← hreindex, hneg]
    exact neg_add_cancel S
  rcases smul_eq_zero.mp hSS with h | h
  · exact absurd h h2
  · rw [alternatingProjection_apply, ← hS, h, smul_zero]

/-- The two displayed expressions are equal. -/
theorem displayed_eq_aux2 {n : ℕ} (hfac : (n.factorial : k) ≠ 0) :
    LinearMap.ker (linearMap_aux1 k V n) = RepresentationTheory.LinearAlgebra.TensorOperations.submodule_aux1 k V n := by
  refine le_antisymm (fun T hT => ?_) ?_
  · have h0 : linearMap_aux1 k V n T = 0 := hT
    have key := mem_submodule_aux7 hfac T
    rwa [h0, sub_zero] at key
  · rw [RepresentationTheory.LinearAlgebra.TensorOperations.submodule_aux1, Submodule.span_le]
    rintro _ ⟨T, i, j, hij, rfl⟩
    simp only [SetLike.mem_coe, LinearMap.mem_ker, map_sub, map_apply_aux5, sub_self]

/-- The two displayed expressions are equal. -/
theorem displayed_eq_aux1 {n : ℕ} (hfac : (n.factorial : k) ≠ 0) :
    LinearMap.ker (linearMap k V n) = RepresentationTheory.LinearAlgebra.TensorOperations.submodule k V n := by
  refine le_antisymm (fun T hT => ?_) ?_
  · have h0 : linearMap k V n T = 0 := hT
    have key := mem_submodule_aux4 hfac T
    rwa [h0, sub_zero] at key
  · rw [RepresentationTheory.LinearAlgebra.TensorOperations.submodule, Submodule.span_le]
    rintro T ⟨i, j, hij, hT⟩
    exact map_apply_aux1 hfac hij hT

end Kernels

section Identification

variable {k : Type*} [Field k] {V : Type*} [AddCommGroup V] [Module k V]

/-- A linear equivalence between the displayed modules. -/
@[source_ref "Chapter2/Problem2.11.3" (role := primary)]
noncomputable def linearEquiv_aux2 {n : ℕ} (hfac : (n.factorial : k) ≠ 0) :
    RepresentationTheory.LinearAlgebra.TensorOperations.AuxiliaryType_aux1 k V n ≃ₗ[k] submodule_aux1 k V n :=
  LinearEquiv.ofLinear
    (Submodule.liftQ _
      ((linearMap_aux1 k V n).codRestrict _ mem_submodule_aux8)
      (by rw [LinearMap.ker_codRestrict, displayed_eq_aux2 hfac]))
    ((RepresentationTheory.LinearAlgebra.TensorOperations.submodule_aux1 k V n).mkQ ∘ₗ (submodule_aux1 k V n).subtype)
    (by
      refine LinearMap.ext fun T => Subtype.ext ?_
      exact map_apply_aux4 hfac T.2)
    (by
      refine LinearMap.ext fun x => ?_
      obtain ⟨T, rfl⟩ := Submodule.mkQ_surjective _ x
      refine (Submodule.Quotient.eq _).2 ?_
      have h := mem_submodule_aux7 hfac T
      rw [← neg_sub] at h
      simpa using neg_mem h)

/-- A linear equivalence between the displayed modules. -/
@[source_ref "Chapter2/Problem2.11.3" (role := primary)]
noncomputable def linearEquiv {n : ℕ} (hfac : (n.factorial : k) ≠ 0) :
    RepresentationTheory.LinearAlgebra.TensorOperations.AuxiliaryType k V n ≃ₗ[k] submodule k V n :=
  LinearEquiv.ofLinear
    (Submodule.liftQ _
      ((linearMap k V n).codRestrict _ mem_submodule_aux1)
      (by rw [LinearMap.ker_codRestrict, displayed_eq_aux1 hfac]))
    ((RepresentationTheory.LinearAlgebra.TensorOperations.submodule k V n).mkQ ∘ₗ (submodule k V n).subtype)
    (by
      refine LinearMap.ext fun T => Subtype.ext ?_
      exact map_apply hfac T.2)
    (by
      refine LinearMap.ext fun x => ?_
      obtain ⟨T, rfl⟩ := Submodule.mkQ_surjective _ x
      refine (Submodule.Quotient.eq _).2 ?_
      have h := mem_submodule_aux4 hfac T
      rw [← neg_sub] at h
      simpa using neg_mem h)

/-- The displayed submodules are equal. -/
theorem submodule_eq_aux2 {n : ℕ} (hfac : (n.factorial : k) ≠ 0) (T : RepresentationTheory.LinearAlgebra.TensorOperations.AuxiliaryType_aux2 k V n) :
    (linearEquiv_aux2 (V := V) hfac ((RepresentationTheory.LinearAlgebra.TensorOperations.submodule_aux1 k V n).mkQ T) : RepresentationTheory.LinearAlgebra.TensorOperations.AuxiliaryType_aux2 k V n)
      = linearMap_aux1 k V n T := rfl

/-- Applying the displayed linear equivalence to a quotient class gives the alternating projection of its representative. -/
theorem linearEquiv_mkQ_apply {n : ℕ} (hfac : (n.factorial : k) ≠ 0) (T : RepresentationTheory.LinearAlgebra.TensorOperations.AuxiliaryType_aux2 k V n) :
    (linearEquiv (V := V) hfac ((RepresentationTheory.LinearAlgebra.TensorOperations.submodule k V n).mkQ T) : RepresentationTheory.LinearAlgebra.TensorOperations.AuxiliaryType_aux2 k V n)
      = linearMap k V n T := rfl

/-- The displayed submodules are equal. -/
@[simp]
theorem submodule_eq_aux3 {n : ℕ} (hfac : (n.factorial : k) ≠ 0)
    (T : submodule_aux1 k V n) :
    (linearEquiv_aux2 (V := V) hfac).symm T
      = (RepresentationTheory.LinearAlgebra.TensorOperations.submodule_aux1 k V n).mkQ (T : RepresentationTheory.LinearAlgebra.TensorOperations.AuxiliaryType_aux2 k V n) := rfl

/-- The inverse linear equivalence sends an alternating tensor to the quotient class of its underlying tensor. -/
@[simp]
theorem linearEquiv_symm_apply {n : ℕ} (hfac : (n.factorial : k) ≠ 0)
    (T : submodule k V n) :
    (linearEquiv (V := V) hfac).symm T
      = (RepresentationTheory.LinearAlgebra.TensorOperations.submodule k V n).mkQ (T : RepresentationTheory.LinearAlgebra.TensorOperations.AuxiliaryType_aux2 k V n) := rfl

/-- A linear equivalence between the displayed modules. -/
@[source_ref "Chapter2/Problem2.11.3" (role := supporting)]
noncomputable def linearEquiv_aux3 [CharZero k] (n : ℕ) :
    RepresentationTheory.LinearAlgebra.TensorOperations.AuxiliaryType_aux1 k V n ≃ₗ[k] submodule_aux1 k V n :=
  linearEquiv_aux2 (natCast_ne_zero k n)

/-- A linear equivalence between the displayed modules. -/
@[source_ref "Chapter2/Problem2.11.3" (role := supporting)]
noncomputable def linearEquiv_aux1 [CharZero k] (n : ℕ) :
    RepresentationTheory.LinearAlgebra.TensorOperations.AuxiliaryType k V n ≃ₗ[k] submodule k V n :=
  linearEquiv (natCast_ne_zero k n)

end Identification

end RepresentationTheory.LinearAlgebra.AlternatingTensors

attribute [nolint defsWithUnderscore]
  RepresentationTheory.LinearAlgebra.AlternatingTensors.submodule_aux1 RepresentationTheory.LinearAlgebra.AlternatingTensors.submodule
  RepresentationTheory.LinearAlgebra.AlternatingTensors.linearMap_aux1 RepresentationTheory.LinearAlgebra.AlternatingTensors.linearMap
  RepresentationTheory.LinearAlgebra.AlternatingTensors.linearEquiv_aux2 RepresentationTheory.LinearAlgebra.AlternatingTensors.linearEquiv
  RepresentationTheory.LinearAlgebra.AlternatingTensors.linearEquiv_aux3
  RepresentationTheory.LinearAlgebra.AlternatingTensors.linearEquiv_aux1
