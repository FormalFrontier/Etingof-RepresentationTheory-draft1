/-
Copyright (c) 2026 mathlib-initiative. All rights reserved.
Released under Apache 2.0 license as described in the file LICENCE.
Authors: mathlib-initiative
-/

import RepresentationTheory.LinearAlgebra.NilpotentOperators

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

/-- For the displayed auxiliary component family, the kernel rank of a power is the sum of `min k (n i)` over the finite index type. -/
theorem finrank_piMap_auxiliary_pow_kernel {ι : Type*} [Fintype ι]
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

namespace AuxiliaryMultisetFunctions

/-- A first auxiliary natural-valued function of a multiset and a natural number. -/
def _root_.RepresentationTheory.LinearAlgebra.KernelDimensionProfiles.auxiliaryMultisetFunction1
    (s : Multiset ℕ) (k : ℕ) : ℕ :=
  (s.filter (fun a => k ≤ a)).card

/-- A second auxiliary natural-valued function of a multiset and a natural number. -/
def _root_.RepresentationTheory.LinearAlgebra.KernelDimensionProfiles.auxiliaryMultisetFunction2
    (s : Multiset ℕ) (k : ℕ) : ℕ :=
  (s.map (fun a => min k a)).sum

/-- On a cons, the second auxiliary function adds the minimum of the parameter and the new entry. -/
theorem _root_.RepresentationTheory.LinearAlgebra.KernelDimensionProfiles.auxiliaryMultisetFunction2_cons
    (a : ℕ) (s : Multiset ℕ) (m : ℕ) :
    auxiliaryMultisetFunction2 (a ::ₘ s) m = min m a + auxiliaryMultisetFunction2 s m := by
  simp only [auxiliaryMultisetFunction2, Multiset.map_cons, Multiset.sum_cons]

/-- On a cons, the first auxiliary function adds one exactly when the parameter is at most the new entry. -/
theorem _root_.RepresentationTheory.LinearAlgebra.KernelDimensionProfiles.auxiliaryMultisetFunction1_cons
    (a : ℕ) (s : Multiset ℕ) (k : ℕ) :
    auxiliaryMultisetFunction1 (a ::ₘ s) k =
      (if k ≤ a then 1 else 0) + auxiliaryMultisetFunction1 s k := by
  simp only [auxiliaryMultisetFunction1, Multiset.filter_cons, Multiset.card_add]
  congr 1
  by_cases h : k ≤ a <;> simp [h]

/-- At a successor, the second auxiliary function adds the first auxiliary function at that successor. -/
theorem _root_.RepresentationTheory.LinearAlgebra.KernelDimensionProfiles.auxiliaryMultisetFunction2_succ
    (s : Multiset ℕ) (k : ℕ) :
    auxiliaryMultisetFunction2 s (k + 1) =
      auxiliaryMultisetFunction2 s k + auxiliaryMultisetFunction1 s (k + 1) := by
  induction s using Multiset.induction_on with
  | empty => simp [auxiliaryMultisetFunction2, auxiliaryMultisetFunction1]
  | cons a s ih =>
    rw [auxiliaryMultisetFunction2_cons, auxiliaryMultisetFunction2_cons,
      auxiliaryMultisetFunction1_cons, ih]
    have hmin : min (k + 1) a = min k a + (if k + 1 ≤ a then 1 else 0) := by
      split <;> omega
    rw [hmin]; ring

/-- The first auxiliary function at a value equals its multiplicity plus the function at the successor. -/
theorem _root_.RepresentationTheory.LinearAlgebra.KernelDimensionProfiles.auxiliaryMultisetFunction1_eq_count_add_succ
    (s : Multiset ℕ) (v : ℕ) :
    auxiliaryMultisetFunction1 s v =
      Multiset.count v s + auxiliaryMultisetFunction1 s (v + 1) := by
  induction s using Multiset.induction_on with
  | empty => simp [auxiliaryMultisetFunction1]
  | cons a s ih =>
    rw [auxiliaryMultisetFunction1_cons, auxiliaryMultisetFunction1_cons,
      Multiset.count_cons, ih]
    have hsplit : (if v ≤ a then (1 : ℕ) else 0)
        = (if v = a then 1 else 0) + (if v + 1 ≤ a then 1 else 0) := by
      split_ifs <;> omega
    rw [hsplit]; ring

end AuxiliaryMultisetFunctions

/-- Two multisets not containing zero are equal when the second auxiliary function agrees at every natural number. -/
theorem multiset_eq_of_auxiliaryMultisetFunction2_eq {s t : Multiset ℕ}
    (hs : 0 ∉ s) (ht : 0 ∉ t)
    (h : ∀ k, auxiliaryMultisetFunction2 s k = auxiliaryMultisetFunction2 t k) : s = t := by
  have hge : ∀ j, auxiliaryMultisetFunction1 s (j + 1) =
      auxiliaryMultisetFunction1 t (j + 1) := by
    intro j
    have hs' := auxiliaryMultisetFunction2_succ s j
    have ht' := auxiliaryMultisetFunction2_succ t j
    rw [h j, h (j + 1)] at hs'
    rw [ht'] at hs'
    exact (Nat.add_left_cancel hs').symm
  refine Multiset.ext.mpr fun v => ?_
  rcases Nat.eq_zero_or_pos v with rfl | hv
  · rw [Multiset.count_eq_zero.mpr hs, Multiset.count_eq_zero.mpr ht]
  · obtain ⟨w, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : v ≠ 0)
    have e1 := auxiliaryMultisetFunction1_eq_count_add_succ s (w + 1)
    have e2 := auxiliaryMultisetFunction1_eq_count_add_succ t (w + 1)
    rw [hge w, hge (w + 1), e2] at e1
    exact (Nat.add_right_cancel e1).symm

end RepresentationTheory.LinearAlgebra.KernelDimensionProfiles
