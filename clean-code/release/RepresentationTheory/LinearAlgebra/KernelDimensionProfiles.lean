/-
Copyright (c) 2026 mathlib-initiative. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: mathlib-initiative
-/

import RepresentationTheory.LinearAlgebra.NilpotentOperators
import RepresentationTheory.Alignment.Attribute

namespace RepresentationTheory.LinearAlgebra.KernelDimensionProfiles

section PiMap

variable {ι : Type*} {W : ι → Type*} [∀ i, AddCommGroup (W i)] [∀ i, Module ℂ (W i)]

/-- Multiplication of pointwise families of endomorphisms is computed componentwise. -/
theorem piMap_mul (f g : ∀ i, Module.End ℂ (W i)) :
    LinearMap.piMap f * LinearMap.piMap g
      = LinearMap.piMap (fun i => f i * g i) := by
  apply LinearMap.ext; intro v; funext j
  simp only [Module.End.mul_apply, LinearMap.coe_piMap, Pi.map_apply]

/-- Powers of a pointwise family of endomorphisms are computed componentwise. -/
theorem piMap_pow (f : ∀ i, Module.End ℂ (W i)) (k : ℕ) :
    LinearMap.piMap f ^ k = LinearMap.piMap (fun i => f i ^ k) := by
  induction k with
  | zero =>
    apply LinearMap.ext; intro v; funext j
    simp only [pow_zero, Module.End.one_apply, LinearMap.coe_piMap, Pi.map_apply]
  | succ k ih =>
    rw [pow_succ, ih, piMap_mul]
    simp only [pow_succ]

/-- Identifies the kernel of a pointwise family map with the dependent product of its component kernels. -/
noncomputable def piKernelLinearEquiv (g : ∀ i, Module.End ℂ (W i)) :
    ↥(LinearMap.ker (LinearMap.piMap g)) ≃ₗ[ℂ] (∀ i, ↥(LinearMap.ker (g i))) where
  toFun v i := ⟨v.1 i, by
    have hv := v.2
    rw [LinearMap.mem_ker] at hv
    rw [LinearMap.mem_ker]
    have := congrFun hv i
    rwa [LinearMap.coe_piMap, Pi.map_apply, Pi.zero_apply] at this⟩
  map_add' u v := rfl
  map_smul' c v := rfl
  invFun w := ⟨fun i => (w i).1, by
    rw [LinearMap.mem_ker]
    funext i
    rw [LinearMap.coe_piMap, Pi.map_apply, Pi.zero_apply]
    exact (w i).2⟩
  left_inv v := rfl
  right_inv w := rfl

/-- The rank of the kernel of a finite pointwise family is the sum of the ranks of the component kernels. -/
theorem finrank_piMap_kernel [Fintype ι] [∀ i, FiniteDimensional ℂ (W i)]
    (g : ∀ i, Module.End ℂ (W i)) :
    Module.finrank ℂ (LinearMap.ker (LinearMap.piMap g))
      = ∑ i, Module.finrank ℂ (LinearMap.ker (g i)) := by
  rw [(piKernelLinearEquiv g).finrank_eq, Module.finrank_pi_fintype]

/-- The rank of the kernel of a power of a finite pointwise family is the sum of the corresponding component-kernel ranks. -/
theorem finrank_piMap_pow_kernel [Fintype ι] [∀ i, FiniteDimensional ℂ (W i)]
    (f : ∀ i, Module.End ℂ (W i)) (k : ℕ) :
    Module.finrank ℂ (LinearMap.ker (LinearMap.piMap f ^ k))
      = ∑ i, Module.finrank ℂ (LinearMap.ker (f i ^ k)) := by
  rw [piMap_pow, finrank_piMap_kernel]

end PiMap

/-- For the displayed component family, the kernel rank of a power is the sum of the truncated component sizes. -/
theorem finrank_piMap_component_pow_kernel {ι : Type*} [Fintype ι]
    (n : ι → ℕ) (k : ℕ) :
    Module.finrank ℂ
        (LinearMap.ker
          (LinearMap.piMap
            (fun i => RepresentationTheory.LinearAlgebra.NilpotentOperators.distinguishedElement
              (n i)) ^ k))
      = ∑ i, min k (n i) := by
  rw [finrank_piMap_pow_kernel]
  exact Finset.sum_congr rfl fun i _ =>
    RepresentationTheory.LinearAlgebra.NilpotentOperators.finrank_ker_pow (n i) k

/-- Counts entries of a multiset of natural numbers that are at least a given threshold. -/
def multisetCountGE (s : Multiset ℕ) (k : ℕ) : ℕ :=
  (s.filter (fun a => k ≤ a)).card

/-- Sums the minimum of a fixed natural number and each entry of a multiset. -/
def multisetSumMin (s : Multiset ℕ) (k : ℕ) : ℕ :=
  (s.map (fun a => min k a)).sum

/-- The truncated sum on a cons is the truncated head plus the truncated sum on the tail. -/
theorem multisetSumMin_cons (a : ℕ) (s : Multiset ℕ) (m : ℕ) :
    multisetSumMin (a ::ₘ s) m = min m a + multisetSumMin s m := by
  simp only [multisetSumMin, Multiset.map_cons, Multiset.sum_cons]

/-- Adjoining an entry increases the threshold count exactly when the threshold is at most that entry. -/
theorem multisetCountGE_cons (a : ℕ) (s : Multiset ℕ) (k : ℕ) :
    multisetCountGE (a ::ₘ s) k =
      (if k ≤ a then 1 else 0) + multisetCountGE s k := by
  simp only [multisetCountGE, Multiset.filter_cons, Multiset.card_add]
  congr 1
  by_cases h : k ≤ a <;> simp [h]

/-- Increasing the truncation bound by one adds the number of entries at least the new bound. -/
theorem multisetSumMin_succ (s : Multiset ℕ) (k : ℕ) :
    multisetSumMin s (k + 1) = multisetSumMin s k + multisetCountGE s (k + 1) := by
  induction s using Multiset.induction_on with
  | empty => simp [multisetSumMin, multisetCountGE]
  | cons a s ih =>
    rw [multisetSumMin_cons, multisetSumMin_cons, multisetCountGE_cons, ih]
    have hmin : min (k + 1) a = min k a + (if k + 1 ≤ a then 1 else 0) := by
      split <;> omega
    rw [hmin]; ring

/-- The number of entries at least a value is the multiplicity of that value plus the number at least its successor. -/
theorem multisetCountGE_eq_count_add_succ (s : Multiset ℕ) (v : ℕ) :
    multisetCountGE s v = Multiset.count v s + multisetCountGE s (v + 1) := by
  induction s using Multiset.induction_on with
  | empty => simp [multisetCountGE]
  | cons a s ih =>
    rw [multisetCountGE_cons, multisetCountGE_cons, Multiset.count_cons, ih]
    have hsplit : (if v ≤ a then (1 : ℕ) else 0)
        = (if v = a then 1 else 0) + (if v + 1 ≤ a then 1 else 0) := by
      split_ifs <;> omega
    rw [hsplit]; ring

/-- Multisets of positive natural numbers agree when all of their truncated sums agree. -/
theorem multiset_eq_of_sumMin_eq {s t : Multiset ℕ} (hs : 0 ∉ s) (ht : 0 ∉ t)
    (h : ∀ k, multisetSumMin s k = multisetSumMin t k) : s = t := by
  have hge : ∀ j, multisetCountGE s (j + 1) = multisetCountGE t (j + 1) := by
    intro j
    have hs' := multisetSumMin_succ s j
    have ht' := multisetSumMin_succ t j
    rw [h j, h (j + 1)] at hs'
    rw [ht'] at hs'
    exact (Nat.add_left_cancel hs').symm
  refine Multiset.ext.mpr fun v => ?_
  rcases Nat.eq_zero_or_pos v with rfl | hv
  · rw [Multiset.count_eq_zero.mpr hs, Multiset.count_eq_zero.mpr ht]
  · obtain ⟨w, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : v ≠ 0)
    have e1 := multisetCountGE_eq_count_add_succ s (w + 1)
    have e2 := multisetCountGE_eq_count_add_succ t (w + 1)
    rw [hge w, hge (w + 1), e2] at e1
    exact (Nat.add_right_cancel e1).symm

end RepresentationTheory.LinearAlgebra.KernelDimensionProfiles
