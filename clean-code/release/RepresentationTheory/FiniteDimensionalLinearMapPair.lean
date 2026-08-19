/-
Copyright (c) 2026 mathlib-initiative. All rights reserved.
Released under Apache 2.0 license as described in the file LICENCE.
Authors: mathlib-initiative
-/

import Mathlib
import RepresentationTheory.RingTheory.Polynomial.JordanBlockModule
import RepresentationTheory.Alignment.Attribute

set_option backward.isDefEq.respectTransparency false

/-!
# Finite-dimensional linear-map pairs
-/

namespace RepresentationTheory.FiniteDimensionalLinearMapPair

open Matrix in
/-- The k-th power of the shift matrix has entry 1 at position (i, j) iff i = j + k. -/
private lemma shift_matrix_pow_entry {n : ℕ} (S : Matrix (Fin n) (Fin n) ℂ)
    (hS : ∀ (a b : Fin n), S a b = if a.val = b.val + 1 then 1 else 0)
    (k : ℕ) : ∀ (i j : Fin n),
    (S ^ k) i j = if i.val = j.val + k then 1 else 0 := by
  induction k with
  | zero =>
    intro i j
    simp only [pow_zero, one_apply, Nat.add_zero, Fin.ext_iff]
  | succ k ih =>
    intro i j
    rw [pow_succ', mul_apply]
    simp_rw [hS, ih]
    split_ifs with h
    · have hm : j.val + k < n := by omega
      rw [Finset.sum_eq_single ⟨j.val + k, hm⟩]
      · simp [show i.val = (j.val + k) + 1 from by omega]
      · intro m _ hne
        simp only [mul_ite, mul_one, mul_zero]
        split_ifs with h1 h2
        · exact absurd (Fin.ext (by omega)) hne
        all_goals rfl
      · simp
    · apply Finset.sum_eq_zero
      intro m _
      simp only [mul_ite, mul_one, mul_zero]
      split_ifs with h1 h2
      · exact absurd (by omega : i.val = j.val + (k + 1)) h
      all_goals rfl



/-- A pair of finite-dimensional vector spaces equipped with linear maps in opposite directions. -/
structure FiniteDimensionalLinearMapPair (k : Type*) [Field k] where
  /-- The left vector space of a finite-dimensional linear-map pair. -/
  Left : Type*
  /-- The right vector space of a finite-dimensional linear-map pair. -/
  Right : Type*
  /-- The additive commutative group structure on the left component. -/
  [instAddCommGroupLeft : AddCommGroup Left]
  /-- The module structure on the left component. -/
  [instModuleLeft : Module k Left]
  /-- The left component is finite-dimensional over the base field. -/
  [finiteDimensional_left : FiniteDimensional k Left]
  /-- The additive commutative group structure on the right component. -/
  [instAddCommGroupRight : AddCommGroup Right]
  /-- The module structure on the right component. -/
  [instModuleRight : Module k Right]
  /-- The right component is finite-dimensional over the base field. -/
  [finiteDimensional_right : FiniteDimensional k Right]
  /-- The linear map from the left component to the right component. -/
  leftToRight : Left →ₗ[k] Right
  /-- The linear map from the right component to the left component. -/
  rightToLeft : Right →ₗ[k] Left

attribute [instance] FiniteDimensionalLinearMapPair.instAddCommGroupLeft FiniteDimensionalLinearMapPair.instModuleLeft FiniteDimensionalLinearMapPair.finiteDimensional_left
  FiniteDimensionalLinearMapPair.instAddCommGroupRight FiniteDimensionalLinearMapPair.instModuleRight FiniteDimensionalLinearMapPair.finiteDimensional_right

/-- Swaps the two component spaces and their opposing linear maps. -/
def FiniteDimensionalLinearMapPair.dual {k : Type*} [Field k] (ρ : FiniteDimensionalLinearMapPair k) : FiniteDimensionalLinearMapPair k where
  Left := ρ.Right
  Right := ρ.Left
  leftToRight := ρ.rightToLeft
  rightToLeft := ρ.leftToRight

/-- An auxiliary condition on a finite-dimensional pair of opposite linear maps. -/
def FiniteDimensionalLinearMapPair.AuxiliaryCondition {k : Type*} [Field k] (ρ : FiniteDimensionalLinearMapPair k) : Prop :=
  (0 < Module.finrank k ρ.Left ∨ 0 < Module.finrank k ρ.Right) ∧
  ∀ (pV qV : Submodule k ρ.Left) (pW qW : Submodule k ρ.Right),
    IsCompl pV qV → IsCompl pW qW →
    (∀ x ∈ pV, ρ.leftToRight x ∈ pW) → (∀ x ∈ qV, ρ.leftToRight x ∈ qW) →
    (∀ x ∈ pW, ρ.rightToLeft x ∈ pV) → (∀ x ∈ qW, ρ.rightToLeft x ∈ qV) →
    (pV = ⊥ ∧ pW = ⊥) ∨ (qV = ⊥ ∧ qW = ⊥)

/-- An equivalence between finite-dimensional linear-map pairs. -/
structure FiniteDimensionalLinearMapPair.Equiv {k : Type*} [Field k] (ρ σ : FiniteDimensionalLinearMapPair k) where
  /-- The linear equivalence between the left components. -/
  leftMap : ρ.Left ≃ₗ[k] σ.Left
  /-- The linear equivalence between the right components. -/
  rightMap : ρ.Right ≃ₗ[k] σ.Right
  /-- The component equivalences intertwine the left-to-right maps. -/
  rightMap_leftToRight : ∀ v, rightMap (ρ.leftToRight v) = σ.leftToRight (leftMap v)
  /-- The component equivalences intertwine the right-to-left maps. -/
  leftMap_rightToLeft : ∀ w, leftMap (ρ.rightToLeft w) = σ.rightToLeft (rightMap w)

namespace FiniteDimensionalLinearMapPair.Equiv

/-- The identity equivalence of a finite-dimensional linear-map pair. -/
def refl {k : Type*} [Field k] (ρ : FiniteDimensionalLinearMapPair k) : ρ.Equiv ρ where
  leftMap := LinearEquiv.refl k ρ.Left
  rightMap := LinearEquiv.refl k ρ.Right
  rightMap_leftToRight := fun _ => rfl
  leftMap_rightToLeft := fun _ => rfl

/-- Reverses an equivalence of finite-dimensional linear-map pairs. -/
def symm {k : Type*} [Field k] {ρ σ : FiniteDimensionalLinearMapPair k} (e : ρ.Equiv σ) : σ.Equiv ρ where
  leftMap := e.leftMap.symm
  rightMap := e.rightMap.symm
  rightMap_leftToRight := fun w => by
    apply e.rightMap.injective
    simpa using (e.rightMap_leftToRight (e.leftMap.symm w)).symm
  leftMap_rightToLeft := fun v => by
    apply e.leftMap.injective
    simpa using (e.leftMap_rightToLeft (e.rightMap.symm v)).symm

/-- Composes equivalences of finite-dimensional linear-map pairs. -/
def trans {k : Type*} [Field k] {ρ σ τ : FiniteDimensionalLinearMapPair k} (e : ρ.Equiv σ) (f : σ.Equiv τ) :
    ρ.Equiv τ where
  leftMap := e.leftMap.trans f.leftMap
  rightMap := e.rightMap.trans f.rightMap
  rightMap_leftToRight := fun v => by
    calc
      f.rightMap (e.rightMap (ρ.leftToRight v)) = f.rightMap (σ.leftToRight (e.leftMap v)) := congrArg f.rightMap (e.rightMap_leftToRight v)
      _ = τ.leftToRight (f.leftMap (e.leftMap v)) := f.rightMap_leftToRight _
      _ = τ.leftToRight ((e.leftMap.trans f.leftMap) v) := rfl
  leftMap_rightToLeft := fun w => by
    calc
      f.leftMap (e.leftMap (ρ.rightToLeft w)) = f.leftMap (σ.rightToLeft (e.rightMap w)) := congrArg f.leftMap (e.leftMap_rightToLeft w)
      _ = τ.rightToLeft (f.rightMap (e.rightMap w)) := f.leftMap_rightToLeft _
      _ = τ.rightToLeft ((e.rightMap.trans f.rightMap) w) := rfl

end FiniteDimensionalLinearMapPair.Equiv

/-- Swapping the two components preserves the auxiliary condition. -/
theorem FiniteDimensionalLinearMapPair.auxiliaryCondition_dual_iff {k : Type*} [Field k] (ρ : FiniteDimensionalLinearMapPair k) :
    ρ.dual.AuxiliaryCondition ↔ ρ.AuxiliaryCondition := by
  constructor
  · rintro ⟨hne, h⟩
    refine ⟨hne.symm, ?_⟩
    intro pV qV pW qW hcV hcW hApV hAqV hBpW hBqW
    rcases h pW qW pV qV hcW hcV hBpW hBqW hApV hAqV with hp | hq
    · exact Or.inl hp.symm
    · exact Or.inr hq.symm
  · rintro ⟨hne, h⟩
    refine ⟨hne.symm, ?_⟩
    intro pW qW pV qV hcW hcV hBpW hBqW hApV hAqV
    rcases h pV qV pW qW hcV hcW hApV hAqV hBpW hBqW with hp | hq
    · exact Or.inl hp.symm
    · exact Or.inr hq.symm

/-- Equivalent pairs have equal dimensions in both components. -/
theorem FiniteDimensionalLinearMapPair.Equiv.finrank_eq {k : Type*} [Field k] {ρ σ : FiniteDimensionalLinearMapPair k} (e : ρ.Equiv σ) :
    Module.finrank k ρ.Left = Module.finrank k σ.Left ∧
      Module.finrank k ρ.Right = Module.finrank k σ.Right :=
  ⟨e.leftMap.finrank_eq, e.rightMap.finrank_eq⟩

/-- An equivalence transports the auxiliary condition to its target. -/
theorem FiniteDimensionalLinearMapPair.Equiv.auxiliaryCondition {k : Type*} [Field k] {ρ σ : FiniteDimensionalLinearMapPair k}
    (e : ρ.Equiv σ) (hρ : ρ.AuxiliaryCondition) : σ.AuxiliaryCondition := by
  let oV := Submodule.orderIsoMapComap e.leftMap
  let oW := Submodule.orderIsoMapComap e.rightMap
  constructor
  · rcases hρ.1 with hV | hW
    · left
      rwa [← e.leftMap.finrank_eq]
    · right
      rwa [← e.rightMap.finrank_eq]
  · intro pV qV pW qW hcV hcW hApV hAqV hBpW hBqW
    have hcV' : IsCompl (oV.symm pV) (oV.symm qV) := oV.symm.isCompl hcV
    have hcW' : IsCompl (oW.symm pW) (oW.symm qW) := oW.symm.isCompl hcW
    have hApV' : ∀ x ∈ oV.symm pV, ρ.leftToRight x ∈ oW.symm pW := by
      intro x hx
      change e.leftMap x ∈ pV at hx
      change e.rightMap (ρ.leftToRight x) ∈ pW
      rw [e.rightMap_leftToRight]
      exact hApV _ hx
    have hAqV' : ∀ x ∈ oV.symm qV, ρ.leftToRight x ∈ oW.symm qW := by
      intro x hx
      change e.leftMap x ∈ qV at hx
      change e.rightMap (ρ.leftToRight x) ∈ qW
      rw [e.rightMap_leftToRight]
      exact hAqV _ hx
    have hBpW' : ∀ x ∈ oW.symm pW, ρ.rightToLeft x ∈ oV.symm pV := by
      intro x hx
      change e.rightMap x ∈ pW at hx
      change e.leftMap (ρ.rightToLeft x) ∈ pV
      rw [e.leftMap_rightToLeft]
      exact hBpW _ hx
    have hBqW' : ∀ x ∈ oW.symm qW, ρ.rightToLeft x ∈ oV.symm qV := by
      intro x hx
      change e.rightMap x ∈ qW at hx
      change e.leftMap (ρ.rightToLeft x) ∈ qV
      rw [e.leftMap_rightToLeft]
      exact hBqW _ hx
    rcases hρ.2 _ _ _ _ hcV' hcW' hApV' hAqV' hBpW' hBqW' with hp | hq
    · left
      constructor
      · have := congrArg oV hp.1
        simpa using this
      · have := congrArg oW hp.2
        simpa using this
    · right
      constructor
      · have := congrArg oV hq.1
        simpa using this
      · have := congrArg oW hq.2
        simpa using this

/-- The auxiliary condition is invariant under equivalence. -/
theorem FiniteDimensionalLinearMapPair.Equiv.auxiliaryCondition_iff {k : Type*} [Field k] {ρ σ : FiniteDimensionalLinearMapPair k}
    (e : ρ.Equiv σ) : ρ.AuxiliaryCondition ↔ σ.AuxiliaryCondition :=
  ⟨e.auxiliaryCondition, e.symm.auxiliaryCondition⟩

/-! ## Shared Fitting decomposition infrastructure for Q₂ representations -/

/-- Intertwining identity: (AB)^n ∘ A = A ∘ (BA)^n -/
private lemma FiniteDimensionalLinearMapPair.intertwine_AB_A (ρ : FiniteDimensionalLinearMapPair ℂ) (n : ℕ) (v : ρ.Left) :
    ((ρ.leftToRight.comp ρ.rightToLeft) ^ n) (ρ.leftToRight v) = ρ.leftToRight (((ρ.rightToLeft.comp ρ.leftToRight) ^ n) v) := by
  induction n generalizing v with
  | zero => simp
  | succ n ih =>
    simp only [pow_succ, Module.End.mul_apply]
    rw [show (ρ.leftToRight.comp ρ.rightToLeft) (ρ.leftToRight v) = ρ.leftToRight ((ρ.rightToLeft.comp ρ.leftToRight) v) from rfl, ih]

/-- Intertwining identity: (BA)^n ∘ B = B ∘ (AB)^n -/
private lemma FiniteDimensionalLinearMapPair.intertwine_BA_B (ρ : FiniteDimensionalLinearMapPair ℂ) (n : ℕ) (w : ρ.Right) :
    ((ρ.rightToLeft.comp ρ.leftToRight) ^ n) (ρ.rightToLeft w) = ρ.rightToLeft (((ρ.leftToRight.comp ρ.rightToLeft) ^ n) w) := by
  induction n generalizing w with
  | zero => simp
  | succ n ih =>
    simp only [pow_succ, Module.End.mul_apply]
    rw [show (ρ.rightToLeft.comp ρ.leftToRight) (ρ.rightToLeft w) = ρ.rightToLeft ((ρ.leftToRight.comp ρ.rightToLeft) w) from rfl, ih]

private lemma FiniteDimensionalLinearMapPair.ker_AB_pow_directed (ρ : FiniteDimensionalLinearMapPair ℂ) :
    Directed (· ≤ ·) (fun n => LinearMap.ker ((ρ.leftToRight.comp ρ.rightToLeft) ^ n)) :=
  Monotone.directed_le fun m n hmn x hx => by
    rw [LinearMap.mem_ker] at hx ⊢
    rw [show n = (n - m) + m from by omega, pow_add, Module.End.mul_apply, hx, map_zero]

private lemma FiniteDimensionalLinearMapPair.ker_BA_pow_directed (ρ : FiniteDimensionalLinearMapPair ℂ) :
    Directed (· ≤ ·) (fun n => LinearMap.ker ((ρ.rightToLeft.comp ρ.leftToRight) ^ n)) :=
  Monotone.directed_le fun m n hmn x hx => by
    rw [LinearMap.mem_ker] at hx ⊢
    rw [show n = (n - m) + m from by omega, pow_add, Module.End.mul_apply, hx, map_zero]

/-- The left-to-right map sends the union of kernels of powers of the left composite into the analogous subspace on the right. -/
lemma FiniteDimensionalLinearMapPair.leftToRight_mem_iSup_ker_powers (ρ : FiniteDimensionalLinearMapPair ℂ) (x : ρ.Left)
    (hx : x ∈ ⨆ n, LinearMap.ker ((ρ.rightToLeft.comp ρ.leftToRight) ^ n)) :
    ρ.leftToRight x ∈ ⨆ n, LinearMap.ker ((ρ.leftToRight.comp ρ.rightToLeft) ^ n) := by
  rw [Submodule.mem_iSup_of_directed _ ρ.ker_BA_pow_directed] at hx
  rw [Submodule.mem_iSup_of_directed _ ρ.ker_AB_pow_directed]
  obtain ⟨n, hn⟩ := hx
  exact ⟨n, by rw [LinearMap.mem_ker] at hn ⊢; rw [ρ.intertwine_AB_A, hn, map_zero]⟩

/-- The left-to-right map sends the intersection of ranges of powers of the left composite into the analogous subspace on the right. -/
lemma FiniteDimensionalLinearMapPair.leftToRight_mem_iInf_range_powers (ρ : FiniteDimensionalLinearMapPair ℂ) (x : ρ.Left)
    (hx : x ∈ ⨅ n, LinearMap.range ((ρ.rightToLeft.comp ρ.leftToRight) ^ n)) :
    ρ.leftToRight x ∈ ⨅ n, LinearMap.range ((ρ.leftToRight.comp ρ.rightToLeft) ^ n) := by
  rw [Submodule.mem_iInf] at hx ⊢; intro n
  obtain ⟨y, hy⟩ := LinearMap.mem_range.mp (hx n)
  exact LinearMap.mem_range.mpr ⟨ρ.leftToRight y, by rw [← hy, ρ.intertwine_AB_A]⟩

/-- The right-to-left map sends the union of kernels of powers of the right composite into the analogous subspace on the left. -/
lemma FiniteDimensionalLinearMapPair.rightToLeft_mem_iSup_ker_powers (ρ : FiniteDimensionalLinearMapPair ℂ) (w : ρ.Right)
    (hw : w ∈ ⨆ n, LinearMap.ker ((ρ.leftToRight.comp ρ.rightToLeft) ^ n)) :
    ρ.rightToLeft w ∈ ⨆ n, LinearMap.ker ((ρ.rightToLeft.comp ρ.leftToRight) ^ n) := by
  rw [Submodule.mem_iSup_of_directed _ ρ.ker_AB_pow_directed] at hw
  rw [Submodule.mem_iSup_of_directed _ ρ.ker_BA_pow_directed]
  obtain ⟨n, hn⟩ := hw
  exact ⟨n, by rw [LinearMap.mem_ker] at hn ⊢; rw [ρ.intertwine_BA_B, hn, map_zero]⟩

/-- The right-to-left map sends the intersection of ranges of powers of the right composite into the analogous subspace on the left. -/
lemma FiniteDimensionalLinearMapPair.rightToLeft_mem_iInf_range_powers (ρ : FiniteDimensionalLinearMapPair ℂ) (w : ρ.Right)
    (hw : w ∈ ⨅ n, LinearMap.range ((ρ.leftToRight.comp ρ.rightToLeft) ^ n)) :
    ρ.rightToLeft w ∈ ⨅ n, LinearMap.range ((ρ.rightToLeft.comp ρ.leftToRight) ^ n) := by
  rw [Submodule.mem_iInf] at hw ⊢; intro n
  obtain ⟨y, hy⟩ := LinearMap.mem_range.mp (hw n)
  exact LinearMap.mem_range.mpr ⟨ρ.rightToLeft y, by rw [← hy, ρ.intertwine_BA_B]⟩

/-- The left-to-right map is injective on the intersection of the ranges of all powers of the left composite. -/
lemma FiniteDimensionalLinearMapPair.leftToRight_injectiveOn_iInf_range_powers (ρ : FiniteDimensionalLinearMapPair ℂ) {v₁ v₂ : ρ.Left}
    (hv₁ : v₁ ∈ ⨅ n, LinearMap.range ((ρ.rightToLeft.comp ρ.leftToRight) ^ n))
    (hv₂ : v₂ ∈ ⨅ n, LinearMap.range ((ρ.rightToLeft.comp ρ.leftToRight) ^ n))
    (h : ρ.leftToRight v₁ = ρ.leftToRight v₂) : v₁ = v₂ := by
  have h_diff : ρ.leftToRight (v₁ - v₂) = 0 := by rw [map_sub, sub_eq_zero.mpr h]
  have h_pV : v₁ - v₂ ∈ ⨆ n, LinearMap.ker ((ρ.rightToLeft.comp ρ.leftToRight) ^ n) :=
    Submodule.mem_iSup_of_mem 1 (by
      rw [pow_one, LinearMap.mem_ker, LinearMap.comp_apply, h_diff, map_zero])
  have h_qV : v₁ - v₂ ∈ ⨅ n, LinearMap.range ((ρ.rightToLeft.comp ρ.leftToRight) ^ n) :=
    (⨅ n, LinearMap.range ((ρ.rightToLeft.comp ρ.leftToRight) ^ n)).sub_mem hv₁ hv₂
  have h_bot := Submodule.mem_inf.mpr ⟨h_pV, h_qV⟩
  rw [(LinearMap.isCompl_iSup_ker_pow_iInf_range_pow (ρ.rightToLeft.comp ρ.leftToRight)).disjoint.eq_bot] at h_bot
  exact sub_eq_zero.mp h_bot

/-- The right-to-left map is injective on the intersection of the ranges of all powers of the right composite. -/
lemma FiniteDimensionalLinearMapPair.rightToLeft_injectiveOn_iInf_range_powers (ρ : FiniteDimensionalLinearMapPair ℂ) {w₁ w₂ : ρ.Right}
    (hw₁ : w₁ ∈ ⨅ n, LinearMap.range ((ρ.leftToRight.comp ρ.rightToLeft) ^ n))
    (hw₂ : w₂ ∈ ⨅ n, LinearMap.range ((ρ.leftToRight.comp ρ.rightToLeft) ^ n))
    (h : ρ.rightToLeft w₁ = ρ.rightToLeft w₂) : w₁ = w₂ := by
  have h_diff : ρ.rightToLeft (w₁ - w₂) = 0 := by rw [map_sub, sub_eq_zero.mpr h]
  have h_pW : w₁ - w₂ ∈ ⨆ n, LinearMap.ker ((ρ.leftToRight.comp ρ.rightToLeft) ^ n) :=
    Submodule.mem_iSup_of_mem 1 (by
      rw [pow_one, LinearMap.mem_ker, LinearMap.comp_apply, h_diff, map_zero])
  have h_qW : w₁ - w₂ ∈ ⨅ n, LinearMap.range ((ρ.leftToRight.comp ρ.rightToLeft) ^ n) :=
    (⨅ n, LinearMap.range ((ρ.leftToRight.comp ρ.rightToLeft) ^ n)).sub_mem hw₁ hw₂
  have h_bot := Submodule.mem_inf.mpr ⟨h_pW, h_qW⟩
  rw [(LinearMap.isCompl_iSup_ker_pow_iInf_range_pow (ρ.leftToRight.comp ρ.rightToLeft)).disjoint.eq_bot] at h_bot
  exact sub_eq_zero.mp h_bot

/-- An auxiliary finite-dimensional pair determined by a positive size and a complex parameter. -/
noncomputable def auxiliaryEigenvalueModel (n : ℕ) (hn : 0 < n) (eigenval : ℂ) : FiniteDimensionalLinearMapPair ℂ where
  Left := EuclideanSpace ℂ (Fin n)
  Right := EuclideanSpace ℂ (Fin n)
  leftToRight := Matrix.toEuclideanLin (Matrix.of fun (i j : Fin n) =>
    if i = j then eigenval else if i.val = j.val + 1 then 1 else 0)
  rightToLeft := LinearMap.id

/-- The parameterized auxiliary model satisfies the auxiliary condition. -/
theorem auxiliaryEigenvalueModel_condition (n : ℕ) (hn : 0 < n) (eigenval : ℂ) :
    (auxiliaryEigenvalueModel n hn eigenval).AuxiliaryCondition := by
  constructor
  · -- Nontriviality: dim V = n > 0
    left
    simp only [auxiliaryEigenvalueModel, finrank_euclideanSpace_fin]
    exact hn
  · -- No nontrivial compatible decomposition
    intro pV qV pW qW hcV hcW hApV hAqV hBpV hBqW
    -- B = LinearMap.id, so B(pW) ⊆ pV means pW ≤ pV, B(qW) ⊆ qV means qW ≤ qV
    have hpWpV : pW ≤ pV := fun x hx => hBpV x hx
    have hqWqV : qW ≤ qV := fun x hx => hBqW x hx
    -- pW ≤ pV and qW ≤ qV force pW = pV: decompose x ∈ pV via IsCompl pW qW,
    -- the qW-component lies in pV ∩ qV = ⊥, so x ∈ pW.
    -- Show pV ≤ pW (with pW ≤ pV this gives equality)
    -- For x ∈ pV, decompose x = p + q (p ∈ pW, q ∈ qW) via IsCompl pW qW.
    -- Then q ∈ pV (since p ∈ pW ≤ pV) and q ∈ qW ≤ qV, so q ∈ pV ⊓ qV = ⊥.
    have aux : ∀ (s₁ t₁ : Submodule ℂ (EuclideanSpace ℂ (Fin n)))
        (s₂ t₂ : Submodule ℂ (EuclideanSpace ℂ (Fin n))),
        IsCompl s₁ t₁ → IsCompl s₂ t₂ → s₂ ≤ s₁ → t₂ ≤ t₁ → s₁ ≤ s₂ := by
      intro s₁ t₁ s₂ t₂ hc1 hc2 hs ht x hx
      have hx_top : x ∈ (⊤ : Submodule ℂ _) := Submodule.mem_top
      rw [← hc2.codisjoint.eq_top] at hx_top
      obtain ⟨p, hp, q, hq, hpq⟩ := Submodule.mem_sup.mp hx_top
      have hq_s1 : q ∈ s₁ := by
        have heq : q = x + (-p) := by rw [← hpq]; abel
        rw [heq]; exact s₁.add_mem hx (s₁.neg_mem (hs hp))
      have hq_t1 : q ∈ t₁ := ht hq
      have hq_bot : q ∈ s₁ ⊓ t₁ := Submodule.mem_inf.mpr ⟨hq_s1, hq_t1⟩
      rw [hc1.disjoint.eq_bot] at hq_bot
      have hq0 : q = 0 := hq_bot
      rw [hq0, add_zero] at hpq; rwa [← hpq]
    have hpWeq : pW = pV := le_antisymm hpWpV (aux pV qV pW qW hcV hcW hpWpV hqWqV)
    have hqWeq : qW = qV := le_antisymm hqWqV (aux qV pV qW pW hcV.symm hcW.symm hqWqV hpWpV)
    -- Suffices to show pV = ⊥ ∨ qV = ⊥ (since pW = pV and qW = qV)
    suffices pV = ⊥ ∨ qV = ⊥ by
      rcases this with h | h
      · left; exact ⟨h, hpWeq ▸ h⟩
      · right; exact ⟨h, hqWeq ▸ h⟩
    -- By contradiction: assume both subspaces are nonzero
    by_contra h_both
    push Not at h_both
    obtain ⟨hpV_ne, hqV_ne⟩ := h_both
    -- Define the nilpotent part N = A - eigenval • id (the shift matrix)
    set N : Module.End ℂ (EuclideanSpace ℂ (Fin n)) :=
      (auxiliaryEigenvalueModel n hn eigenval).leftToRight - eigenval • LinearMap.id with hN_def
    -- A preserves pV and qV (using pW = pV, qW = qV)
    have hA_pV : ∀ x ∈ pV, (auxiliaryEigenvalueModel n hn eigenval).leftToRight x ∈ pV :=
      fun x hx => hpWeq ▸ hApV x hx
    have hA_qV : ∀ x ∈ qV, (auxiliaryEigenvalueModel n hn eigenval).leftToRight x ∈ qV :=
      fun x hx => hqWeq ▸ hAqV x hx
    -- N preserves pV and qV (since A does and scalar maps preserve submodules)
    have hN_pV : ∀ x ∈ pV, N x ∈ pV := fun x hx =>
      pV.sub_mem (hA_pV x hx) (pV.smul_mem eigenval hx)
    have hN_qV : ∀ x ∈ qV, N x ∈ qV := fun x hx =>
      qV.sub_mem (hA_qV x hx) (qV.smul_mem eigenval hx)
    -- N is nilpotent: the shift matrix satisfies N^n = 0
    -- Strategy: N = toEuclideanLin(S) where S is the shift matrix, and S^n = 0
    set S := Matrix.of fun (a b : Fin n) =>
      if a.val = b.val + 1 then (1 : ℂ) else 0 with hS_def
    have hS_entry : ∀ (a b : Fin n), S a b = if a.val = b.val + 1 then 1 else 0 := by
      intro a b; simp [S, Matrix.of_apply]
    have hN_eq : N = Matrix.toEuclideanLin S := by
      -- N = toEuclideanLin(J) - eigenval • id
      --   = toEuclideanLin(J - eigenval • 1) = toEuclideanLin(S)
      -- First show J - eigenval • 1 = S as matrices
      set J := Matrix.of fun (i j : Fin n) =>
        if i = j then eigenval else if i.val = j.val + 1 then (1 : ℂ) else 0 with hJ_def
      have hmat : J - eigenval • (1 : Matrix (Fin n) (Fin n) ℂ) = S := by
        ext i j
        simp only [Matrix.sub_apply, Matrix.smul_apply, Matrix.one_apply, smul_eq_mul,
          Matrix.of_apply, S, J]
        by_cases h1 : i = j
        · subst h1; simp
        · simp only [h1, ↓reduceIte, mul_zero, sub_zero]
      -- Now lift to linear maps via toEuclideanLin
      -- toEuclideanLin(J - eigenval • 1) = toEuclideanLin(J) - eigenval • toEuclideanLin(1)
      --   = toEuclideanLin(J) - eigenval • id = N
      have h1 : Matrix.toEuclideanLin S = Matrix.toEuclideanLin J -
          Matrix.toEuclideanLin (eigenval • (1 : Matrix (Fin n) (Fin n) ℂ)) := by
        rw [← map_sub, hmat]
      rw [h1, map_smul, Matrix.toLpLin_one]
      simp [N, auxiliaryEigenvalueModel, J]
    have hS_pow : S ^ n = 0 := by
      ext i j
      rw [shift_matrix_pow_entry S hS_entry]
      simp only [Matrix.zero_apply]
      split_ifs with h
      · exact absurd h (by omega)
      · rfl
    have hN_nilp : IsNilpotent N :=
      ⟨n, by rw [hN_eq, ← Matrix.toLpLin_pow 2, hS_pow, map_zero]⟩
    -- N^{n-1} ≠ 0: the shift by n-1 sends e₀ to e_{n-1}
    have hN_pow_ne : N ^ (n - 1) ≠ 0 := by
      rw [hN_eq, ← Matrix.toLpLin_pow 2]
      intro h
      have hS_pow_ne : S ^ (n - 1) = 0 :=
        (Matrix.toEuclideanLin).injective (by rw [h, map_zero])
      have h0 := congr_fun (congr_fun hS_pow_ne ⟨n - 1, by omega⟩) ⟨0, hn⟩
      simp only [Matrix.zero_apply] at h0
      rw [shift_matrix_pow_entry S hS_entry _ ⟨n - 1, by omega⟩ ⟨0, hn⟩] at h0
      simp  at h0
    -- Since pV ≠ ⊤ and qV ≠ ⊤ (from the complement being nonzero)
    have hpV_ne_top : pV ≠ ⊤ := by
      intro h
      apply hqV_ne
      have hd := hcV.disjoint.eq_bot
      rwa [h, top_inf_eq] at hd
    have hqV_ne_top : qV ≠ ⊤ := by
      intro h
      apply hpV_ne
      have hd := hcV.disjoint.eq_bot
      rwa [h, inf_top_eq] at hd
    -- finrank(pV) < n and finrank(qV) < n
    have hdim_pV : Module.finrank ℂ pV < n := by
      calc Module.finrank ℂ ↥pV
          < Module.finrank ℂ (EuclideanSpace ℂ (Fin n)) := Submodule.finrank_lt hpV_ne_top
        _ = n := finrank_euclideanSpace_fin
    have hdim_qV : Module.finrank ℂ qV < n := by
      calc Module.finrank ℂ ↥qV
          < Module.finrank ℂ (EuclideanSpace ℂ (Fin n)) := Submodule.finrank_lt hqV_ne_top
        _ = n := finrank_euclideanSpace_fin
    -- Helper: N^{n-1} kills any proper N-invariant submodule
    -- Proof: restrict N to S, it's nilpotent, Cayley-Hamilton gives (N|_S)^d = 0 where
    -- d = finrank S < n, so N^{n-1} = N^{n-1-d} ∘ N^d = 0 on S.
    have hN_kills_sub : ∀ (S : Submodule ℂ (EuclideanSpace ℂ (Fin n))),
        (hS : ∀ x ∈ S, N x ∈ S) → Module.finrank ℂ S < n →
        ∀ v ∈ S, (N ^ (n - 1)) v = 0 := by
      intro S hS hdimS v hv
      -- N restricted to S is nilpotent
      have hnil_S : IsNilpotent (N.restrict hS) := by
        obtain ⟨k, hk⟩ := hN_nilp
        exact ⟨k, LinearMap.ext fun ⟨m, hm⟩ => by
          rw [Module.End.pow_restrict, LinearMap.restrict_apply, LinearMap.zero_apply]
          exact Subtype.ext (show (N ^ k) m = 0 by
            exact LinearMap.congr_fun hk m)⟩
      -- By Cayley-Hamilton, (N.restrict)^{finrank S} = 0
      have hpow_S : (N.restrict hS) ^ Module.finrank ℂ ↥S = 0 := by
        have hchar := (LinearMap.isNilpotent_iff_charpoly (N.restrict hS)).mp hnil_S
        have hCH := LinearMap.aeval_self_charpoly (N.restrict hS)
        rw [hchar, Polynomial.aeval_X_pow] at hCH
        exact hCH
      -- So N^{finrank S} kills S
      have hkill : (N ^ Module.finrank ℂ ↥S) v = 0 := by
        have h := LinearMap.congr_fun hpow_S ⟨v, hv⟩
        rw [Module.End.pow_restrict, LinearMap.restrict_apply, LinearMap.zero_apply] at h
        exact congr_arg Subtype.val h
      -- N^{n-1} = N^{n-1-d} ∘ N^d where d = finrank S ≤ n-1
      rw [show n - 1 = (n - 1 - Module.finrank ℂ ↥S) + Module.finrank ℂ ↥S from by omega,
          pow_add, Module.End.mul_apply, hkill, map_zero]
    have hN_kills_pV : ∀ v ∈ pV, (N ^ (n - 1)) v = 0 :=
      hN_kills_sub pV hN_pV hdim_pV
    have hN_kills_qV : ∀ v ∈ qV, (N ^ (n - 1)) v = 0 :=
      hN_kills_sub qV hN_qV hdim_qV
    -- Since V = pV + qV (from IsCompl), N^{n-1} = 0 on all of V
    have hN_pow_zero : N ^ (n - 1) = 0 := by
      ext v
      simp only [LinearMap.zero_apply]
      have : v ∈ (⊤ : Submodule ℂ _) := Submodule.mem_top
      rw [← hcV.codisjoint.eq_top] at this
      obtain ⟨p, hp, q, hq, hpq⟩ := Submodule.mem_sup.mp this
      rw [← hpq, map_add, hN_kills_pV p hp, hN_kills_qV q hq, add_zero]
    exact absurd hN_pow_zero hN_pow_ne

/-- A second auxiliary finite-dimensional pair of positive size. -/
noncomputable def auxiliaryModelB (n : ℕ) (hn : 0 < n) : FiniteDimensionalLinearMapPair ℂ where
  Left := EuclideanSpace ℂ (Fin n)
  Right := EuclideanSpace ℂ (Fin (n - 1))
  leftToRight := Matrix.toEuclideanLin (Matrix.of fun (i : Fin (n - 1)) (j : Fin n) =>
    if i.val = j.val then (1 : ℂ) else 0)
  rightToLeft := Matrix.toEuclideanLin (Matrix.of fun (i : Fin n) (j : Fin (n - 1)) =>
    if i.val = j.val + 1 then (1 : ℂ) else 0)

/-- The second arrow in `H_n` is injective. -/
private theorem auxiliaryModelB_B_injective (n : ℕ) (hn : 0 < n) :
    Function.Injective (auxiliaryModelB n hn).rightToLeft := by
  intro x y hxy
  apply WithLp.ofLp_injective
  funext j
  have hcoord := congr_fun (congr_arg WithLp.ofLp hxy) ⟨j.val + 1, by omega⟩
  simp only [auxiliaryModelB, Matrix.toLpLin_apply, Matrix.mulVec, dotProduct,
    Matrix.of_apply, ite_mul, one_mul, zero_mul] at hcoord
  have hsum : ∀ z : Fin (n - 1) → ℂ,
      (∑ a, if j.val = a.val then z a else 0) = z j := by
    intro z
    simpa [Fin.ext_iff] using (Finset.sum_ite_eq (Finset.univ) j z)
  have hcoord' :
      (∑ a, if j.val = a.val then x.ofLp a else 0) =
        ∑ a, if j.val = a.val then y.ofLp a else 0 := by
    simpa only [Nat.add_right_cancel_iff] using hcoord
  rw [hsum, hsum] at hcoord'
  exact hcoord'

/-- The composite `BA` in `H_n` is the nilpotent single Jordan block used by
`E_{n,0}`. -/
private theorem auxiliaryModelB_BA (n : ℕ) (hn : 0 < n) :
    (auxiliaryModelB n hn).rightToLeft.comp (auxiliaryModelB n hn).leftToRight =
      (auxiliaryEigenvalueModel n hn 0).leftToRight := by
  rw [show (auxiliaryModelB n hn).rightToLeft.comp (auxiliaryModelB n hn).leftToRight =
      Matrix.toEuclideanLin
        ((Matrix.of fun (i : Fin n) (j : Fin (n - 1)) =>
            if i.val = j.val + 1 then (1 : ℂ) else 0) *
          (Matrix.of fun (i : Fin (n - 1)) (j : Fin n) =>
            if i.val = j.val then (1 : ℂ) else 0)) from by
        simp only [auxiliaryModelB]
        exact (Matrix.toLpLin_mul 2 2 2 _ _).symm]
  change Matrix.toEuclideanLin
      ((Matrix.of fun (i : Fin n) (j : Fin (n - 1)) =>
          if i.val = j.val + 1 then (1 : ℂ) else 0) *
        (Matrix.of fun (i : Fin (n - 1)) (j : Fin n) =>
          if i.val = j.val then (1 : ℂ) else 0)) =
    Matrix.toEuclideanLin (Matrix.of fun (i j : Fin n) =>
      if i = j then (0 : ℂ) else if i.val = j.val + 1 then 1 else 0)
  apply_fun Matrix.toEuclideanLin.symm using Matrix.toEuclideanLin.symm.injective
  simp only [LinearEquiv.symm_apply_apply]
  ext i j
  simp only [Matrix.mul_apply, Matrix.of_apply]
  by_cases hij : i.val = j.val + 1
  · have hj : j.val < n - 1 := by omega
    have hne : i ≠ j := by intro h; subst i; omega
    rw [Finset.sum_eq_single ⟨j.val, hj⟩]
    · simp [hij, hne]
    · intro a _ hne
      simp only [ite_mul, one_mul, zero_mul]
      split_ifs with hia haj
      · exact absurd (Fin.ext (by omega)) hne
      all_goals rfl
    · simp
  · rw [Finset.sum_eq_zero]
    · simp [hij]
    · intro a _
      simp only [ite_mul, one_mul, zero_mul]
      split_ifs with hia haj
      · exact absurd (by omega : i.val = j.val + 1) hij
      all_goals rfl

/-- The second auxiliary model satisfies the auxiliary condition. -/
theorem auxiliaryModelB_condition (n : ℕ) (hn : 0 < n) :
    (auxiliaryModelB n hn).AuxiliaryCondition := by
  constructor
  · left
    simpa [auxiliaryModelB] using hn
  · intro pV qV pW qW hcV hcW hApV hAqV hBpW hBqW
    have hBAp : ∀ x ∈ pV,
        (auxiliaryEigenvalueModel n hn 0).leftToRight x ∈ pV := by
      intro x hx
      rw [← auxiliaryModelB_BA]
      exact hBpW _ (hApV _ hx)
    have hBAq : ∀ x ∈ qV,
        (auxiliaryEigenvalueModel n hn 0).leftToRight x ∈ qV := by
      intro x hx
      rw [← auxiliaryModelB_BA]
      exact hBqW _ (hAqV _ hx)
    rcases (auxiliaryEigenvalueModel_condition n hn 0).2 pV qV pV qV hcV hcV
      hBAp hBAq (fun _ h => h) (fun _ h => h) with hp | hq
    · left
      refine ⟨hp.1, ?_⟩
      apply le_antisymm
      · intro w hw
        have : (auxiliaryModelB n hn).rightToLeft w = 0 := by
          have := hBpW w hw
          simpa [hp.1] using this
        have hw0 : w = 0 := auxiliaryModelB_B_injective n hn (by simpa using this)
        exact hw0 ▸ Submodule.zero_mem _
      · exact bot_le
    · right
      refine ⟨hq.1, ?_⟩
      apply le_antisymm
      · intro w hw
        have : (auxiliaryModelB n hn).rightToLeft w = 0 := by
          have := hBqW w hw
          simpa [hq.1] using this
        have hw0 : w = 0 := auxiliaryModelB_B_injective n hn (by simpa using this)
        exact hw0 ▸ Submodule.zero_mem _
      · exact bot_le

/-- A first auxiliary finite-dimensional pair of positive size. -/
noncomputable def auxiliaryModelA (n : ℕ) (hn : 0 < n) : FiniteDimensionalLinearMapPair ℂ :=
  (auxiliaryEigenvalueModel n hn 0).dual

/-- A third auxiliary finite-dimensional pair of positive size. -/
noncomputable def auxiliaryModelC (n : ℕ) (hn : 0 < n) : FiniteDimensionalLinearMapPair ℂ :=
  (auxiliaryModelB n hn).dual

/-- The first auxiliary model satisfies the auxiliary condition. -/
theorem auxiliaryModelA_condition (n : ℕ) (hn : 0 < n) :
    (auxiliaryModelA n hn).AuxiliaryCondition := by
  rw [auxiliaryModelA, FiniteDimensionalLinearMapPair.auxiliaryCondition_dual_iff]
  exact auxiliaryEigenvalueModel_condition n hn 0

/-- The third auxiliary model satisfies the auxiliary condition. -/
theorem auxiliaryModelC_condition (n : ℕ) (hn : 0 < n) :
    (auxiliaryModelC n hn).AuxiliaryCondition := by
  rw [auxiliaryModelC, FiniteDimensionalLinearMapPair.auxiliaryCondition_dual_iff]
  exact auxiliaryModelB_condition n hn

/-- The left composite is carried to the corresponding composite by conjugation along an equivalence. -/
theorem FiniteDimensionalLinearMapPair.Equiv.conj_rightToLeft_comp_leftToRight {k : Type*} [Field k] {ρ σ : FiniteDimensionalLinearMapPair k} (e : ρ.Equiv σ) :
    e.leftMap.conj (ρ.rightToLeft.comp ρ.leftToRight) = σ.rightToLeft.comp σ.leftToRight := by
  ext v
  change e.leftMap (ρ.rightToLeft (ρ.leftToRight (e.leftMap.symm v))) = σ.rightToLeft (σ.leftToRight v)
  calc
    e.leftMap (ρ.rightToLeft (ρ.leftToRight (e.leftMap.symm v))) = σ.rightToLeft (e.rightMap (ρ.leftToRight (e.leftMap.symm v))) :=
      e.leftMap_rightToLeft _
    _ = σ.rightToLeft (σ.leftToRight (e.leftMap (e.leftMap.symm v))) := congrArg σ.rightToLeft (e.rightMap_leftToRight _)
    _ = σ.rightToLeft (σ.leftToRight v) := by rw [LinearEquiv.apply_symm_apply]

/-- Equivalent complex pairs have the same trace for the left-side composite. -/
theorem FiniteDimensionalLinearMapPair.Equiv.trace_rightToLeft_comp_leftToRight_eq {ρ σ : FiniteDimensionalLinearMapPair ℂ} (e : ρ.Equiv σ) :
    LinearMap.trace ℂ ρ.Left (ρ.rightToLeft.comp ρ.leftToRight) =
      LinearMap.trace ℂ σ.Left (σ.rightToLeft.comp σ.leftToRight) := by
  have h := (LinearMap.trace_conj' (ρ.rightToLeft.comp ρ.leftToRight) e.leftMap).symm
  rwa [e.conj_rightToLeft_comp_leftToRight] at h

/-- Injectivity of the right-to-left map is invariant under equivalence. -/
theorem FiniteDimensionalLinearMapPair.Equiv.rightToLeft_injective_iff {k : Type*} [Field k] {ρ σ : FiniteDimensionalLinearMapPair k}
    (e : ρ.Equiv σ) : Function.Injective ρ.rightToLeft ↔ Function.Injective σ.rightToLeft := by
  constructor
  · intro h x y hxy
    apply e.rightMap.symm.injective
    apply h
    apply e.leftMap.injective
    rw [e.leftMap_rightToLeft, e.leftMap_rightToLeft]
    simpa using hxy
  · intro h x y hxy
    apply e.rightMap.injective
    apply h
    rw [← e.leftMap_rightToLeft, ← e.leftMap_rightToLeft, hxy]

/-- The trace of the composite in the parameterized auxiliary model is its size times its complex parameter. -/
theorem trace_comp_auxiliaryEigenvalueModel (n : ℕ) (hn : 0 < n) (eigenval : ℂ) :
    LinearMap.trace ℂ (auxiliaryEigenvalueModel n hn eigenval).Left
        ((auxiliaryEigenvalueModel n hn eigenval).rightToLeft.comp
          (auxiliaryEigenvalueModel n hn eigenval).leftToRight) = n * eigenval := by
  change LinearMap.trace ℂ (EuclideanSpace ℂ (Fin n))
      (Matrix.toLpLin 2 2 (Matrix.of fun (i j : Fin n) =>
        if i = j then eigenval else if i.val = j.val + 1 then 1 else 0)) = n * eigenval
  rw [Matrix.toLpLin_eq_toLin, Matrix.trace_toLin_eq]
  simp [Matrix.trace]

/-- The zero-parameter Jordan arrow in `E_{n,0}` is nilpotent. -/
private theorem auxiliaryEigenvalueModel_zero_A_nilpotent (n : ℕ) (_hn : 0 < n) :
    IsNilpotent (Matrix.toEuclideanLin (Matrix.of fun (i j : Fin n) =>
      if i = j then (0 : ℂ) else if i.val = j.val + 1 then 1 else 0) :
        Module.End ℂ (EuclideanSpace ℂ (Fin n))) := by
  set S := Matrix.of fun (a b : Fin n) =>
    if a.val = b.val + 1 then (1 : ℂ) else 0
  have hS_entry : ∀ (a b : Fin n), S a b =
      if a.val = b.val + 1 then 1 else 0 := by
    intro a b
    simp [S]
  have hmat : (Matrix.of fun (i j : Fin n) =>
      if i = j then (0 : ℂ) else if i.val = j.val + 1 then 1 else 0) = S := by
    ext i j
    by_cases h : i = j
    · subst i
      simp [S]
    · simp [S, h]
  rw [hmat]
  have hS_pow : S ^ n = 0 := by
    ext i j
    rw [shift_matrix_pow_entry S hS_entry]
    simp only [Matrix.zero_apply]
    split_ifs with h
    · exact absurd h (by omega)
    · rfl
  refine ⟨n, ?_⟩
  rw [← Matrix.toLpLin_pow 2, hS_pow, map_zero]

set_option synthInstance.maxHeartbeats 100000 in
-- Elaborating injectivity of powers of the bundled endomorphism needs a larger instance budget.
/-- For positive `n`, the nilpotent arrow of `E_{n,0}` is not injective. -/
private theorem auxiliaryEigenvalueModel_zero_A_not_injective (n : ℕ) (hn : 0 < n) :
    ¬Function.Injective (auxiliaryEigenvalueModel n hn 0).leftToRight := by
  change ¬Function.Injective (Matrix.toEuclideanLin (Matrix.of fun (i j : Fin n) =>
    if i = j then (0 : ℂ) else if i.val = j.val + 1 then 1 else 0))
  let T : Module.End ℂ (EuclideanSpace ℂ (Fin n)) :=
    Matrix.toEuclideanLin (Matrix.of fun (i j : Fin n) =>
      if i = j then (0 : ℂ) else if i.val = j.val + 1 then 1 else 0)
  intro hA
  change Function.Injective T at hA
  have hpow : ∀ m : ℕ, Function.Injective (T ^ m) := by
    intro m
    induction m with
    | zero =>
      intro x y hxy
      have hx : (1 : Module.End ℂ (EuclideanSpace ℂ (Fin n))) x = x := rfl
      have hy : (1 : Module.End ℂ (EuclideanSpace ℂ (Fin n))) y = y := rfl
      simpa only [pow_zero, hx, hy] using hxy
    | succ m ih =>
      intro x y hxy
      rw [pow_succ] at hxy
      simp only [Module.End.mul_apply] at hxy
      exact hA (ih hxy)
  have hnil : IsNilpotent T := by
    simpa [T] using auxiliaryEigenvalueModel_zero_A_nilpotent n hn
  obtain ⟨m, hm⟩ := hnil
  haveI : Nontrivial (EuclideanSpace ℂ (Fin n)) :=
    Module.finrank_pos_iff.mp (by rw [finrank_euclideanSpace_fin]; exact hn)
  obtain ⟨v, hv⟩ := exists_ne (0 : EuclideanSpace ℂ (Fin n))
  apply hv
  apply hpow m
  rw [hm]
  simp

/-- Equivalent parameterized auxiliary models have the same size and complex parameter. -/
theorem auxiliaryEigenvalueModel_equiv_iff {n m : ℕ} {hn : 0 < n} {hm : 0 < m}
    {eigenval eigenval' : ℂ} (e : (auxiliaryEigenvalueModel n hn eigenval).Equiv
      (auxiliaryEigenvalueModel m hm eigenval')) : n = m ∧ eigenval = eigenval' := by
  have hnm : n = m := by
    simpa [auxiliaryEigenvalueModel] using e.finrank_eq.1
  subst m
  have htrace := e.trace_rightToLeft_comp_leftToRight_eq
  rw [trace_comp_auxiliaryEigenvalueModel, trace_comp_auxiliaryEigenvalueModel] at htrace
  constructor
  · rfl
  · exact (mul_left_cancel₀ (show (n : ℂ) ≠ 0 by exact_mod_cast (Nat.ne_of_gt hn))) htrace

/-- An auxiliary type classifying selected finite-dimensional pairs. -/
inductive AuxiliaryClass where
  | finite (n : {n : ℕ // 0 < n}) (eigenval : ℂ)
  | infinity (n : {n : ℕ // 0 < n})
  | preprojective (n : {n : ℕ // 0 < n})
  | preinjective (n : {n : ℕ // 0 < n})

/-- Chooses a finite-dimensional pair representing an auxiliary class. -/
noncomputable def AuxiliaryClass.rep : AuxiliaryClass → FiniteDimensionalLinearMapPair ℂ
  | .finite n eigenval => auxiliaryEigenvalueModel n n.2 eigenval
  | .infinity n => auxiliaryModelA n n.2
  | .preprojective n => auxiliaryModelB n n.2
  | .preinjective n => auxiliaryModelC n n.2

/-- The chosen representative satisfies the auxiliary condition. -/
@[source_ref "Chapter6/Problem6.9.1" (role := supporting)]
theorem AuxiliaryClass.rep_auxiliaryCondition (c : AuxiliaryClass) :
    c.rep.AuxiliaryCondition := by
  cases c with
  | finite n eigenval => exact auxiliaryEigenvalueModel_condition n n.2 eigenval
  | infinity n => exact auxiliaryModelA_condition n n.2
  | preprojective n => exact auxiliaryModelB_condition n n.2
  | preinjective n => exact auxiliaryModelC_condition n n.2

/-- Computes the dimensions of the two components of the chosen representative. -/
theorem AuxiliaryClass.finrank_rep (c : AuxiliaryClass) :
    (Module.finrank ℂ c.rep.Left, Module.finrank ℂ c.rep.Right) =
      match c with
      | .finite n _ => (n, n)
      | .infinity n => (n, n)
      | .preprojective n => (n, n - 1)
      | .preinjective n => (n - 1, n) := by
  cases c <;> simp [AuxiliaryClass.rep, auxiliaryEigenvalueModel,
    auxiliaryModelA, auxiliaryModelB, auxiliaryModelC, FiniteDimensionalLinearMapPair.dual]

/-- An auxiliary predicate on finite-dimensional pairs of opposite linear maps. -/
def AuxiliaryPredicate (ρ : FiniteDimensionalLinearMapPair ℂ) : Prop :=
  ∃ c : AuxiliaryClass, Nonempty (ρ.Equiv c.rep)

private theorem auxiliaryEigenvalueModel_B_injective (n : ℕ) (hn : 0 < n) (eigenval : ℂ) :
    Function.Injective (auxiliaryEigenvalueModel n hn eigenval).rightToLeft := by
  simpa [auxiliaryEigenvalueModel] using (Function.injective_id : Function.Injective (id :
    EuclideanSpace ℂ (Fin n) → EuclideanSpace ℂ (Fin n)))

private theorem auxiliaryModelA_B_not_injective (n : ℕ) (hn : 0 < n) :
    ¬Function.Injective (auxiliaryModelA n hn).rightToLeft := by
  exact auxiliaryEigenvalueModel_zero_A_not_injective n hn

/-- Two auxiliary classes are equal when their representatives are equivalent. -/
@[source_ref "Chapter6/Problem6.9.1" (role := supporting)]
theorem AuxiliaryClass.eq_of_rep_equiv {c d : AuxiliaryClass} (e : c.rep.Equiv d.rep) :
    c = d := by
  cases c with
  | finite n eigenval =>
    cases d with
    | finite m eigenval' =>
      obtain ⟨hnm, he⟩ := auxiliaryEigenvalueModel_equiv_iff
        (hn := n.2) (hm := m.2) e
      have hnm' : n = m := Subtype.ext hnm
      subst m
      subst eigenval'
      rfl
    | infinity m =>
      exfalso
      exact auxiliaryModelA_B_not_injective m m.2
        (e.rightToLeft_injective_iff.mp (auxiliaryEigenvalueModel_B_injective n n.2 eigenval))
    | preprojective m =>
      have h := e.finrank_eq
      simp [AuxiliaryClass.rep, auxiliaryEigenvalueModel, auxiliaryModelB] at h
      omega
    | preinjective m =>
      have h := e.finrank_eq
      simp [AuxiliaryClass.rep, auxiliaryEigenvalueModel, auxiliaryModelC, auxiliaryModelB, FiniteDimensionalLinearMapPair.dual] at h
      omega
  | infinity n =>
    cases d with
    | finite m eigenval =>
      exfalso
      exact auxiliaryModelA_B_not_injective n n.2
        (e.rightToLeft_injective_iff.mpr (auxiliaryEigenvalueModel_B_injective m m.2 eigenval))
    | infinity m =>
      have h := e.finrank_eq
      have hnm : n.val = m.val := by
        simpa [AuxiliaryClass.rep, auxiliaryModelA, auxiliaryEigenvalueModel, FiniteDimensionalLinearMapPair.dual] using h.1
      cases Subtype.ext hnm
      rfl
    | preprojective m =>
      have h := e.finrank_eq
      simp [AuxiliaryClass.rep, auxiliaryModelA, auxiliaryEigenvalueModel, auxiliaryModelB,
        FiniteDimensionalLinearMapPair.dual] at h
      omega
    | preinjective m =>
      have h := e.finrank_eq
      simp [AuxiliaryClass.rep, auxiliaryModelA, auxiliaryEigenvalueModel, auxiliaryModelC, auxiliaryModelB,
        FiniteDimensionalLinearMapPair.dual] at h
      omega
  | preprojective n =>
    cases d with
    | finite m eigenval =>
      have h := e.finrank_eq
      simp [AuxiliaryClass.rep, auxiliaryEigenvalueModel, auxiliaryModelB] at h
      omega
    | infinity m =>
      have h := e.finrank_eq
      simp [AuxiliaryClass.rep, auxiliaryModelA, auxiliaryEigenvalueModel, auxiliaryModelB,
        FiniteDimensionalLinearMapPair.dual] at h
      omega
    | preprojective m =>
      have hnm : n.val = m.val := by
        simpa [AuxiliaryClass.rep, auxiliaryModelB] using e.finrank_eq.1
      cases Subtype.ext hnm
      rfl
    | preinjective m =>
      have h := e.finrank_eq
      simp [AuxiliaryClass.rep, auxiliaryModelC, auxiliaryModelB, FiniteDimensionalLinearMapPair.dual] at h
      omega
  | preinjective n =>
    cases d with
    | finite m eigenval =>
      have h := e.finrank_eq
      simp [AuxiliaryClass.rep, auxiliaryEigenvalueModel, auxiliaryModelC, auxiliaryModelB, FiniteDimensionalLinearMapPair.dual] at h
      omega
    | infinity m =>
      have h := e.finrank_eq
      simp [AuxiliaryClass.rep, auxiliaryModelA, auxiliaryEigenvalueModel, auxiliaryModelC, auxiliaryModelB,
        FiniteDimensionalLinearMapPair.dual] at h
      omega
    | preprojective m =>
      have h := e.finrank_eq
      simp [AuxiliaryClass.rep, auxiliaryModelC, auxiliaryModelB, FiniteDimensionalLinearMapPair.dual] at h
      omega
    | preinjective m =>
      have hnm : n.val = m.val := by
        simpa [AuxiliaryClass.rep, auxiliaryModelC, auxiliaryModelB, FiniteDimensionalLinearMapPair.dual] using e.finrank_eq.2
      cases Subtype.ext hnm
      rfl

/-- If the composite is not nilpotent, there are complementary decompositions respected by both maps whose second summands have equal dimension. -/
theorem exists_compatible_complements_of_not_isNilpotent (ρ : FiniteDimensionalLinearMapPair ℂ)
    (hAB : ¬IsNilpotent (ρ.leftToRight.comp ρ.rightToLeft)) :
    ∃ (pV qV : Submodule ℂ ρ.Left) (pW qW : Submodule ℂ ρ.Right),
      IsCompl pV qV ∧ IsCompl pW qW ∧
      (∀ x ∈ pV, ρ.leftToRight x ∈ pW) ∧ (∀ x ∈ qV, ρ.leftToRight x ∈ qW) ∧
      (∀ x ∈ pW, ρ.rightToLeft x ∈ pV) ∧ (∀ x ∈ qW, ρ.rightToLeft x ∈ qV) ∧
      -- The q-summand has equal dimensions (E_{n,λ} type with λ ≠ 0)
      Module.finrank ℂ (↥qV) = Module.finrank ℂ (↥qW) := by
  -- Fitting decomposition for AB on W and BA on V
  set AB := ρ.leftToRight.comp ρ.rightToLeft with hAB_def
  set BA := ρ.rightToLeft.comp ρ.leftToRight with hBA_def
  set pW := ⨆ n, LinearMap.ker (AB ^ n)
  set qW := ⨅ n, LinearMap.range (AB ^ n)
  set pV := ⨆ n, LinearMap.ker (BA ^ n)
  set qV := ⨅ n, LinearMap.range (BA ^ n)
  refine ⟨pV, qV, pW, qW, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  -- 1. IsCompl pV qV (Fitting for BA)
  · exact LinearMap.isCompl_iSup_ker_pow_iInf_range_pow BA
  -- 2. IsCompl pW qW (Fitting for AB)
  · exact LinearMap.isCompl_iSup_ker_pow_iInf_range_pow AB
  -- 3-6. A and B map Fitting subspaces to Fitting subspaces
  · exact fun x hx => ρ.leftToRight_mem_iSup_ker_powers x hx
  · exact fun x hx => ρ.leftToRight_mem_iInf_range_powers x hx
  · exact fun x hx => ρ.rightToLeft_mem_iSup_ker_powers x hx
  · exact fun x hx => ρ.rightToLeft_mem_iInf_range_powers x hx
  -- 7. dim qV = dim qW (via injectivity of restricted A and B on eventual ranges)
  · set A' : ↥qV →ₗ[ℂ] ↥qW :=
      (ρ.leftToRight.domRestrict qV).codRestrict qW (fun ⟨v, hv⟩ =>
        ρ.leftToRight_mem_iInf_range_powers v hv)
    set B' : ↥qW →ₗ[ℂ] ↥qV :=
      (ρ.rightToLeft.domRestrict qW).codRestrict qV (fun ⟨w, hw⟩ =>
        ρ.rightToLeft_mem_iInf_range_powers w hw)
    have hA'_inj : Function.Injective A' := by
      intro ⟨v₁, hv₁⟩ ⟨v₂, hv₂⟩ h
      exact Subtype.ext (ρ.leftToRight_injectiveOn_iInf_range_powers hv₁ hv₂ (by
        simpa [A', LinearMap.codRestrict_apply, LinearMap.domRestrict_apply]
          using congr_arg Subtype.val h))
    have hB'_inj : Function.Injective B' := by
      intro ⟨w₁, hw₁⟩ ⟨w₂, hw₂⟩ h
      exact Subtype.ext (ρ.rightToLeft_injectiveOn_iInf_range_powers hw₁ hw₂ (by
        simpa [B', LinearMap.codRestrict_apply, LinearMap.domRestrict_apply]
          using congr_arg Subtype.val h))
    exact le_antisymm
      (LinearMap.finrank_le_finrank_of_injective hA'_inj)
      (LinearMap.finrank_le_finrank_of_injective hB'_inj)

/-- If v₀ ∈ ker A, v₀ ≠ 0, v₀ ∉ range B, and dim W > 0, then ρ is decomposable.
Decomposition: (span{v₀}, ⊥) ⊕ (qV, ⊤) where qV contains range B. -/
private lemma FiniteDimensionalLinearMapPair.decomp_of_ker_A_not_range_B (ρ : FiniteDimensionalLinearMapPair ℂ) (hρ : ρ.AuxiliaryCondition)
    (hW_pos : 0 < Module.finrank ℂ ρ.Right)
    (v₀ : ρ.Left) (hv₀_ne : v₀ ≠ 0) (hv₀_kerA : ρ.leftToRight v₀ = 0)
    (hv₀_not_rangeB : v₀ ∉ LinearMap.range ρ.rightToLeft) : False := by
  set V₁ := Submodule.span ℂ ({v₀} : Set ρ.Left)
  set S := LinearMap.range ρ.rightToLeft
  have h_disj : Disjoint V₁ S := by
    rw [disjoint_comm]; exact (Submodule.disjoint_span_singleton' hv₀_ne).mpr hv₀_not_rangeB
  obtain ⟨C, hTC⟩ := (V₁ ⊔ S).exists_isCompl
  set qV := S ⊔ C
  have hcV : IsCompl V₁ qV := by
    constructor
    · rw [disjoint_iff]
      simp only [Submodule.eq_bot_iff]
      intro x hx
      have hx₁ : x ∈ V₁ := (Submodule.mem_inf.mp hx).1
      have hx₂ : x ∈ qV := (Submodule.mem_inf.mp hx).2
      obtain ⟨s, hs, c, hc, hsc⟩ := Submodule.mem_sup.mp hx₂
      have hc_T : c ∈ V₁ ⊔ S := by
        have heq : c = x - s := by rw [← hsc]; abel
        rw [heq]; exact (V₁ ⊔ S).sub_mem (Submodule.mem_sup_left hx₁) (Submodule.mem_sup_right hs)
      have hc0 : c = 0 := by
        have h := Submodule.mem_inf.mpr ⟨hc_T, hc⟩
        rwa [hTC.disjoint.eq_bot] at h
      have hxs : x = s := by rw [← hsc, hc0, add_zero]
      subst hxs
      exact h_disj.le_bot (Submodule.mem_inf.mpr ⟨hx₁, hs⟩)
    · simp only [codisjoint_iff]
      calc V₁ ⊔ qV = V₁ ⊔ (S ⊔ C) := rfl
        _ = (V₁ ⊔ S) ⊔ C := (sup_assoc _ _ _).symm
        _ = ⊤ := hTC.codisjoint.eq_top
  haveI : Nontrivial ρ.Right := Module.finrank_pos_iff.mp hW_pos
  rcases hρ.2 V₁ qV ⊥ ⊤ hcV isCompl_bot_top
    (fun x hx => by
      obtain ⟨c, rfl⟩ := Submodule.mem_span_singleton.mp hx
      simp [hv₀_kerA])
    (fun _ _ => Submodule.mem_top)
    (fun x hx => by
      have := (Submodule.mem_bot ℂ).mp hx
      rw [this, map_zero]; exact Submodule.zero_mem _)
    (fun x _ => (le_sup_left : S ≤ qV) (LinearMap.mem_range_self ρ.rightToLeft x))
  with ⟨hV₁_bot, _⟩ | ⟨_, hqW_bot⟩
  · exact hv₀_ne (show v₀ ∈ (⊥ : Submodule ℂ ρ.Left) from hV₁_bot ▸ Submodule.subset_span rfl)
  · exact absurd hqW_bot (top_ne_bot (α := Submodule ℂ ρ.Right))

/-- Symmetric version: if w₀ ∈ ker B, w₀ ≠ 0, w₀ ∉ range A, and dim V > 0,
then ρ is decomposable. -/
private lemma FiniteDimensionalLinearMapPair.decomp_of_ker_B_not_range_A (ρ : FiniteDimensionalLinearMapPair ℂ) (hρ : ρ.AuxiliaryCondition)
    (hV_pos : 0 < Module.finrank ℂ ρ.Left)
    (w₀ : ρ.Right) (hw₀_ne : w₀ ≠ 0) (hw₀_kerB : ρ.rightToLeft w₀ = 0)
    (hw₀_not_rangeA : w₀ ∉ LinearMap.range ρ.leftToRight) : False := by
  have hρ_swap : ρ.dual.AuxiliaryCondition := by
    refine ⟨hρ.1.symm, fun pW qW pV qV hcW hcV hBpW hBqW hApV hAqV => ?_⟩
    rcases hρ.2 pV qV pW qW hcV hcW hApV hAqV hBpW hBqW with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · exact Or.inl ⟨h2, h1⟩
    · exact Or.inr ⟨h2, h1⟩
  exact ρ.dual.decomp_of_ker_A_not_range_B hρ_swap hV_pos w₀ hw₀_ne hw₀_kerB hw₀_not_rangeA

/-- If ρ is indecomposable with AB nilpotent and both dims > 0, then ker A ⊆ range B. -/
private lemma FiniteDimensionalLinearMapPair.ker_A_sub_range_B (ρ : FiniteDimensionalLinearMapPair ℂ) (hρ : ρ.AuxiliaryCondition)
    (hAB : IsNilpotent (ρ.leftToRight.comp ρ.rightToLeft))
    (hV_pos : 0 < Module.finrank ℂ ρ.Left)
    (hW_pos : 0 < Module.finrank ℂ ρ.Right) :
    LinearMap.ker ρ.leftToRight ≤ LinearMap.range ρ.rightToLeft := by
  intro v hv
  by_contra h
  exact ρ.decomp_of_ker_A_not_range_B hρ hW_pos v
    (fun h0 => by simp [h0] at h) (LinearMap.mem_ker.mp hv) h

/-- If ρ is indecomposable with AB nilpotent and both dims > 0, then ker B ⊆ range A. -/
private lemma FiniteDimensionalLinearMapPair.ker_B_sub_range_A (ρ : FiniteDimensionalLinearMapPair ℂ) (hρ : ρ.AuxiliaryCondition)
    (hAB : IsNilpotent (ρ.leftToRight.comp ρ.rightToLeft))
    (hV_pos : 0 < Module.finrank ℂ ρ.Left)
    (hW_pos : 0 < Module.finrank ℂ ρ.Right) :
    LinearMap.ker ρ.rightToLeft ≤ LinearMap.range ρ.leftToRight := by
  intro w hw
  by_contra h
  exact ρ.decomp_of_ker_B_not_range_A hρ hV_pos w
    (fun h0 => by simp [h0] at h) (LinearMap.mem_ker.mp hw) h

private lemma ker_sum_ge_one (ρ : FiniteDimensionalLinearMapPair ℂ)
    (hAB : IsNilpotent (ρ.leftToRight.comp ρ.rightToLeft))
    (hV_pos : 0 < Module.finrank ℂ ρ.Left)
    (hW_pos : 0 < Module.finrank ℂ ρ.Right) :
    1 ≤ Module.finrank ℂ (LinearMap.ker ρ.leftToRight) + Module.finrank ℂ (LinearMap.ker ρ.rightToLeft) := by
  -- AB nilpotent on W (dim W > 0) implies ker(AB) ≠ ⊥
  -- Then take w ∈ ker(AB) \ {0}: Bw ∈ ker A. If Bw ≠ 0 → ker A ≠ ⊥; else w ∈ ker B.
  rw [Nat.one_le_iff_ne_zero]
  intro h
  have hA : Module.finrank ℂ (LinearMap.ker ρ.leftToRight) = 0 := by omega
  have hB : Module.finrank ℂ (LinearMap.ker ρ.rightToLeft) = 0 := by omega
  rw [Submodule.finrank_eq_zero] at hA hB
  -- A is injective and B is injective
  have hA_inj : Function.Injective ρ.leftToRight := LinearMap.ker_eq_bot.mp hA
  have hB_inj : Function.Injective ρ.rightToLeft := LinearMap.ker_eq_bot.mp hB
  -- AB injective → AB not nilpotent (contradiction with dim W > 0)
  have hAB_inj : Function.Injective (ρ.leftToRight.comp ρ.rightToLeft) := hA_inj.comp hB_inj
  obtain ⟨N, hN⟩ := hAB
  have hW_ntriv : Nontrivial ρ.Right := Module.finrank_pos_iff.mp hW_pos
  obtain ⟨w, hw⟩ := exists_ne (0 : ρ.Right)
  have : (ρ.leftToRight.comp ρ.rightToLeft) ^ N = 0 := hN
  have hw0 : ((ρ.leftToRight.comp ρ.rightToLeft) ^ N) w = 0 := by rw [hN, LinearMap.zero_apply]
  -- But (AB)^N is injective (composition of injective maps)
  -- (AB)^N w = 0 but w ≠ 0 contradicts AB injective
  -- Use: if AB injective and (AB)^N = 0, then N = 0 or W = 0
  -- Prove: ker((AB)^n) = ⊥ for all n (by induction, using AB injective)
  suffices ∀ n, LinearMap.ker ((ρ.leftToRight.comp ρ.rightToLeft) ^ n) = ⊥ by
    have hmem := LinearMap.mem_ker.mpr hw0
    rw [this N] at hmem
    exact hw ((Submodule.mem_bot ℂ).mp hmem)
  intro n; induction n with
  | zero => simp only [pow_zero, LinearMap.ker_eq_bot]; exact fun _ _ h => h
  | succ n ih =>
    rw [LinearMap.ker_eq_bot]
    intro x y hxy
    rw [pow_succ', Module.End.mul_apply, Module.End.mul_apply] at hxy
    exact LinearMap.ker_eq_bot.mp ih (hAB_inj hxy)

/-- When AB = 0, BA = 0, both ker A and ker B nontrivial, ker A ⊆ range B, ker B ⊆ range A:
the "cross-pairing" decomposition (ker A, complement of ker B) ⊕ (complement of ker A, ker B)
is a compatible Q₂-decomposition with both parts nontrivial. -/
private lemma decomp_of_AB_BA_zero (ρ : FiniteDimensionalLinearMapPair ℂ)
    (hAB_zero : ρ.leftToRight.comp ρ.rightToLeft = 0) (hBA_zero : ρ.rightToLeft.comp ρ.leftToRight = 0)
    (hkA_pos : 0 < Module.finrank ℂ (LinearMap.ker ρ.leftToRight))
    (hkB_pos : 0 < Module.finrank ℂ (LinearMap.ker ρ.rightToLeft))
    (hkA_rangeB : LinearMap.ker ρ.leftToRight ≤ LinearMap.range ρ.rightToLeft)
    (hkB_rangeA : LinearMap.ker ρ.rightToLeft ≤ LinearMap.range ρ.leftToRight) :
    ¬ρ.AuxiliaryCondition := by
  intro hρ
  -- ker A = range B (from AB = 0: range B ⊆ ker A, and ker A ⊆ range B)
  have hkA_eq : LinearMap.ker ρ.leftToRight = LinearMap.range ρ.rightToLeft := by
    exact le_antisymm hkA_rangeB (fun w hw => by
      rw [LinearMap.mem_ker]
      obtain ⟨x, rfl⟩ := LinearMap.mem_range.mp hw
      exact LinearMap.congr_fun hAB_zero x)
  have hkB_eq : LinearMap.ker ρ.rightToLeft = LinearMap.range ρ.leftToRight := by
    exact le_antisymm hkB_rangeA (fun v hv => by
      rw [LinearMap.mem_ker]
      obtain ⟨x, rfl⟩ := LinearMap.mem_range.mp hv
      exact LinearMap.congr_fun hBA_zero x)
  -- Get complements
  obtain ⟨qV, hcV⟩ := (LinearMap.ker ρ.leftToRight).exists_isCompl
  obtain ⟨qW, hcW⟩ := (LinearMap.ker ρ.rightToLeft).exists_isCompl
  -- The cross-pairing decomposition:
  -- pV = ker A, pW = qW (complement of ker B)
  -- qV' = qV (complement of ker A), qW' = ker B
  -- Check A maps:
  -- A(ker A) = {0} ⊆ qW ✓
  -- A(qV) ⊆ range A = ker B ✓ (since BA = 0 means range A ⊆ ker B, hence = ker B)
  -- Check B maps:
  -- B(qW) ⊆ range B = ker A ✓ (since AB = 0 means range B ⊆ ker A, hence = ker A)
  -- B(ker B) = {0} ⊆ qV ✓
  have hA_pV : ∀ x ∈ LinearMap.ker ρ.leftToRight, ρ.leftToRight x ∈ qW := by
    intro x hx; rw [LinearMap.mem_ker.mp hx]; exact Submodule.zero_mem _
  have hA_qV : ∀ x ∈ qV, ρ.leftToRight x ∈ LinearMap.ker ρ.rightToLeft := by
    intro x _; rw [hkB_eq]; exact LinearMap.mem_range_self ρ.leftToRight x
  have hB_qW : ∀ x ∈ qW, ρ.rightToLeft x ∈ LinearMap.ker ρ.leftToRight := by
    intro x _; rw [hkA_eq]; exact LinearMap.mem_range_self ρ.rightToLeft x
  have hB_kB : ∀ x ∈ LinearMap.ker ρ.rightToLeft, ρ.rightToLeft x ∈ qV := by
    intro x hx; rw [LinearMap.mem_ker.mp hx]; exact Submodule.zero_mem _
  -- Both summands nontrivial
  have hpV_ne : LinearMap.ker ρ.leftToRight ≠ ⊥ := by
    intro h; rw [h, finrank_bot] at hkA_pos; exact Nat.lt_irrefl 0 hkA_pos
  have hqW_ne : LinearMap.ker ρ.rightToLeft ≠ ⊥ := by
    intro h; rw [h, finrank_bot] at hkB_pos; exact Nat.lt_irrefl 0 hkB_pos
  -- Apply indecomposability
  rcases hρ.2 (LinearMap.ker ρ.leftToRight) qV qW (LinearMap.ker ρ.rightToLeft) hcV hcW.symm
    hA_pV hA_qV hB_qW hB_kB with ⟨h1, h2⟩ | ⟨h1, h2⟩
  · exact hpV_ne h1
  · exact hqW_ne h2

open Polynomial in
/-- In `ℂ[X] ⧸ (X ^ n)`, an element with `X ^ (n-1) • a ≠ 0` is a unit.
Such elements have maximal X-order, implying their lift is coprime to X. -/
private lemma quotient_X_pow_isUnit_of_maxOrder (n : ℕ) (hn : 0 < n)
    (a : ℂ[X] ⧸ Ideal.span {(X : ℂ[X]) ^ n})
    (ha : (X : ℂ[X]) ^ (n - 1) • a ≠ 0) : IsUnit a := by
  obtain ⟨pa, rfl⟩ := Ideal.Quotient.mk_surjective a
  -- X ∤ pa (otherwise X^n | X^{n-1} * pa, contradicting ha)
  have hXndvd : ¬ ((X : ℂ[X]) ∣ pa) := by
    intro ⟨q, hq⟩; apply ha
    change Ideal.Quotient.mk (Ideal.span {(X : ℂ[X]) ^ n}) (X ^ (n - 1) * pa) = 0
    rw [Ideal.Quotient.eq_zero_iff_mem, Ideal.mem_span_singleton]
    exact ⟨q, by rw [hq, ← mul_assoc, ← pow_succ, show n - 1 + 1 = n from by omega]⟩
  -- pa and X^n are coprime (X is irreducible and doesn't divide pa)
  have hcoprime : IsCoprime pa ((X : ℂ[X]) ^ n) :=
    ((Polynomial.irreducible_X.isRelPrime_iff_not_dvd.mpr hXndvd).isCoprime.symm).pow_right
  -- Bezout gives inverse
  obtain ⟨u, v, huv⟩ := hcoprime
  exact IsUnit.of_mul_eq_one (Ideal.Quotient.mk _ u) (by
    rw [← map_mul, show pa * u = 1 - v * X ^ n from by linear_combination (mul_comm u pa) + huv]
    rw [map_sub, map_one, map_mul, Ideal.Quotient.eq_zero_iff_mem.mpr
      (Ideal.mem_span_singleton_self _), mul_zero, sub_zero])

open Polynomial in
/-- In `ℂ[X] ⧸ (X ^ n)`, any element annihilated by `X` lies in the ℂ-span of
the image of `X ^ (n - 1)`. This shows the X-torsion is at most 1-dimensional. -/
private lemma quotient_X_torsion_mem_span (n : ℕ)
    (a : ℂ[X] ⧸ Ideal.span {(X : ℂ[X]) ^ n})
    (ha : (X : ℂ[X]) • a = 0) :
    a ∈ Submodule.span ℂ ({Ideal.Quotient.mk
      (Ideal.span {(X : ℂ[X]) ^ n}) ((X : ℂ[X]) ^ (n - 1))} : Set _) := by
  obtain ⟨pa, rfl⟩ := Ideal.Quotient.mk_surjective a
  -- X • mk(pa) = 0 means mk(X * pa) = 0, i.e., X^n ∣ X * pa
  have hmem : (X : ℂ[X]) ^ n ∣ X * pa := by
    rw [← Ideal.mem_span_singleton, ← Ideal.Quotient.eq_zero_iff_mem]
    exact ha
  cases n with
  | zero =>
    suffices h : (Ideal.Quotient.mk (Ideal.span {(X : ℂ[X]) ^ 0})) pa = 0 by
      rw [h]; exact Submodule.zero_mem _
    rw [Ideal.Quotient.eq_zero_iff_mem, Ideal.mem_span_singleton, pow_zero]
    exact one_dvd pa
  | succ m =>
    -- X^(m+1) ∣ X * pa → X^m ∣ pa (cancel X in integral domain)
    rw [pow_succ'] at hmem
    have hpa : X ^ m ∣ pa :=
      (mul_dvd_mul_iff_left (Polynomial.X_ne_zero (R := ℂ))).mp hmem
    obtain ⟨q, rfl⟩ := hpa
    -- mk(X^m * q) ∈ span{mk(X^m)}, witnessed by c = q.coeff 0
    rw [Submodule.mem_span_singleton, show m + 1 - 1 = m from rfl]
    refine ⟨q.coeff 0, ?_⟩
    -- q.coeff 0 • mk(X^m) = mk(C(q.coeff 0) * X^m)
    rw [← IsScalarTower.algebraMap_smul ℂ[X] (q.coeff 0),
      ← Ideal.Quotient.mk_eq_mk, ← Submodule.Quotient.mk_smul,
      smul_eq_mul, Polynomial.algebraMap_eq]
    apply Ideal.Quotient.eq.mpr
    rw [mul_comm (C _) _, ← mul_sub, Ideal.mem_span_singleton, pow_succ]
    apply mul_dvd_mul_left
    rw [show (X : ℂ[X]) = X - C 0 by simp, Polynomial.dvd_iff_isRoot]
    simp [Polynomial.IsRoot, Polynomial.coeff_zero_eq_eval_zero]

set_option maxHeartbeats 800000 in
-- PID structure theorem and direct sum manipulation require extra heartbeats
set_option synthInstance.maxHeartbeats 40000 in
/-- A nilpotent endomorphism with kernel of dimension ≥ 2 admits a nontrivial
invariant direct sum decomposition.

Case split: if ker T ⊄ range T, the elementary construction
  M₁ = span{v} (for v ∈ ker T \ range T), M₂ = range T ⊕ complement
gives the decomposition. The case ker T ⊆ range T requires the structure
theorem for modules over ℂ[X] (PID). -/
private lemma nilpotent_nontrivial_decomp {V : Type*} [AddCommGroup V] [Module ℂ V]
    [FiniteDimensional ℂ V] (T : V →ₗ[ℂ] V) (_hT : IsNilpotent T)
    (hker : 2 ≤ Module.finrank ℂ (LinearMap.ker T)) :
    ∃ (M₁ M₂ : Submodule ℂ V), M₁ ≠ ⊥ ∧ M₂ ≠ ⊥ ∧ IsCompl M₁ M₂ ∧
      (∀ v ∈ M₁, T v ∈ M₁) ∧ (∀ v ∈ M₂, T v ∈ M₂) := by
  -- Case 1: T = 0. Any nontrivial splitting works since every subspace is T-invariant.
  by_cases hT0 : T = 0
  · subst hT0
    -- dim V ≥ 2, so V has a nontrivial direct sum decomposition
    have hV : 2 ≤ Module.finrank ℂ V := le_trans hker (Submodule.finrank_le _)
    -- Pick a nonzero vector and its complement
    have : Nontrivial V := Module.finrank_pos_iff.mp (by linarith)
    obtain ⟨v, hv⟩ := exists_ne (0 : V)
    obtain ⟨M₂, hcompl⟩ := (Submodule.span ℂ {v}).exists_isCompl
    refine ⟨Submodule.span ℂ {v}, M₂, ?_, ?_, hcompl, ?_, ?_⟩
    · exact mt Submodule.span_singleton_eq_bot.mp hv
    · intro h
      have htop : Submodule.span ℂ {v} = ⊤ := eq_top_of_isCompl_bot (h ▸ hcompl)
      have h1 := finrank_span_singleton (K := ℂ) hv
      rw [htop] at h1
      simp at h1
      linarith
    · intro w _; simp
    · intro w _; simp
  -- Case 2: T ≠ 0.
  · by_cases hdisjoint : Disjoint (LinearMap.ker T) (LinearMap.range T)
    · -- Case 2a: ker T ∩ range T = 0. Use ker T and range T directly.
      refine ⟨LinearMap.ker T, LinearMap.range T, ?_, ?_, ?_, ?_, ?_⟩
      · -- ker T ≠ ⊥
        intro h; rw [h, finrank_bot] at hker; omega
      · -- range T ≠ ⊥
        rwa [ne_eq, LinearMap.range_eq_bot]
      · -- IsCompl: disjoint + dimensions add up
        have hdim := T.finrank_range_add_finrank_ker
        exact (Submodule.isCompl_iff_disjoint _ _
          (by linarith)).mpr hdisjoint
      · -- T-invariance of ker T
        intro v hv
        rw [LinearMap.mem_ker] at hv ⊢
        simp [hv]
      · -- T-invariance of range T
        intro v hv
        exact ⟨v, rfl⟩
    · -- Case 2b: ker T ∩ range T ≠ 0.
      -- Sub-case split: is there v ∈ ker T \ range T?
      by_cases hkR : LinearMap.ker T ≤ LinearMap.range T
      · -- Case 2b-ii: ker T ⊆ range T. Use PID structure theorem.
        -- View V as an X-torsion ℂ[X]-module via AEval'.
        open Polynomial in
        have htors : Module.IsTorsion' (Module.AEval' (R := ℂ) T)
            (Submonoid.powers (X : ℂ[X])) := by
          obtain ⟨n, hn⟩ := _hT
          intro m
          refine ⟨⟨X ^ n, n, rfl⟩, ?_⟩
          set v := (Module.AEval'.of (R := ℂ) T).symm m
          have hm : m = Module.AEval'.of T v := (LinearEquiv.apply_symm_apply _ m).symm
          rw [hm, Submonoid.smul_def, Module.AEval'.X_pow_smul_of,
            LinearEquiv.map_eq_zero_iff]
          change (T ^ n) v = 0
          simp [hn]
        -- Apply PID structure theorem: AEval' T ≅ ⨁ (i : Fin d) ℂ[X]/(X^kᵢ)
        open Polynomial in
        obtain ⟨d, k, ⟨e⟩⟩ := Module.torsion_by_prime_power_decomposition
          Polynomial.irreducible_X htors
        -- d ≥ 2: each summand contributes 1 to dim(ker T), and dim(ker T) ≥ 2
        have hd : 2 ≤ d := by
          by_contra hd_lt
          push Not at hd_lt
          interval_cases d
          · -- d = 0: direct sum is trivial, V = 0, contradicts dim(ker T) ≥ 2
            have hsub : Subsingleton V := by
              constructor
              intro a b
              have ha : e (Module.AEval'.of (R := ℂ) T a) = 0 :=
                DFinsupp.ext (fun i => Fin.elim0 i)
              have hb : e (Module.AEval'.of (R := ℂ) T b) = 0 :=
                DFinsupp.ext (fun i => Fin.elim0 i)
              have := e.injective (ha.trans hb.symm)
              exact (Module.AEval'.of (R := ℂ) T).injective this
            haveI := hsub
            have : Module.finrank ℂ V = 0 := Module.finrank_zero_of_subsingleton
            have := Submodule.finrank_le (LinearMap.ker T)
            omega
          · -- d = 1: AEval' T ≅ ℂ[X]/(X^k₀), ker T has dim ≤ 1
            exfalso
            have h1 : Module.finrank ℂ (LinearMap.ker T) ≤ 1 := by
              set j₀ : Fin 1 := ⟨0, by omega⟩
              set gen := (Submodule.Quotient.mk ((X : ℂ[X]) ^ (k j₀ - 1)) :
                ℂ[X] ⧸ ℂ[X] ∙ X ^ k j₀)
              set w : V := (Module.AEval'.of (R := ℂ) T).symm
                (e.symm (DirectSum.of _ j₀ gen)) with hw_def
              suffices h_le : LinearMap.ker T ≤ Submodule.span ℂ ({w} : Set V) by
                exact (Submodule.finrank_mono h_le).trans
                  ((finrank_span_le_card ({w} : Set V)).trans (by simp))
              intro v hv
              rw [LinearMap.mem_ker] at hv
              -- e(AEval'.of T v) has X • it = 0
              have hX_tors : (X : ℂ[X]) • e (Module.AEval'.of (R := ℂ) T v) = 0 := by
                have h := e.map_smul (X : ℂ[X]) (Module.AEval'.of (R := ℂ) T v)
                rw [Module.AEval'.X_smul_of, hv, map_zero, map_zero] at h
                exact h.symm
              -- Component j₀ also has X • it = 0
              set c₀ := DirectSum.component ℂ[X] _ _ j₀ (e (Module.AEval'.of (R := ℂ) T v))
              have hc₀_tors : (X : ℂ[X]) • c₀ = 0 := by
                have h := (DirectSum.component ℂ[X] _ _ j₀).map_smul
                  (X : ℂ[X]) (e (Module.AEval'.of (R := ℂ) T v))
                rw [hX_tors, map_zero] at h; exact h.symm
              -- By quotient_X_torsion_mem_span, c₀ = c • X^(k₀-1) for some c
              have hc₀_span := quotient_X_torsion_mem_span (k j₀) c₀ hc₀_tors
              rw [Submodule.mem_span_singleton] at hc₀_span
              obtain ⟨c, hc⟩ := hc₀_span
              -- Reconstruct: for Fin 1, the direct sum element = of j₀ (component j₀)
              have hds_eq : e (Module.AEval'.of (R := ℂ) T v) = DirectSum.of _ j₀ c₀ := by
                apply DFinsupp.ext; intro ⟨i, hi⟩
                have : i = 0 := by omega
                subst this
                rw [DirectSum.of_eq_same]; rfl
              -- v = c • w: both map to the same element under e ∘ AEval'.of
              have hv_eq : v = c • w := by
                apply (Module.AEval'.of (R := ℂ) T).injective
                apply e.injective
                -- LHS = of j₀ (c • gen)
                have lhs : e (Module.AEval'.of (R := ℂ) T v) =
                    DirectSum.of _ j₀ (c • gen) := by
                  rw [hds_eq]; congr 1; exact hc.symm
                -- RHS = of j₀ (c • gen)
                have rhs : e (Module.AEval'.of (R := ℂ) T (c • w)) =
                    DirectSum.of _ j₀ (c • gen) := by
                  rw [map_smul, hw_def, LinearEquiv.apply_symm_apply]
                  -- Goal: e (c • e.symm (of j₀ gen)) = of j₀ (c • gen)
                  conv_lhs =>
                    rw [← IsScalarTower.algebraMap_smul ℂ[X] c
                      (e.symm (DirectSum.of _ j₀ gen))]
                  rw [e.map_smul, LinearEquiv.apply_symm_apply]
                  -- Goal: (algebraMap ℂ ℂ[X] c) • of j₀ gen = of j₀ (c • gen)
                  conv_rhs =>
                    rw [← IsScalarTower.algebraMap_smul ℂ[X] c gen]
                  exact ((DirectSum.lof ℂ[X] (Fin 1)
                    (fun i => ℂ[X] ⧸ ℂ[X] ∙ X ^ k i) j₀).map_smul _ gen).symm
                exact lhs.trans rhs.symm
              rw [hv_eq]
              exact Submodule.smul_mem _ c (Submodule.subset_span rfl)
            omega
        -- Split the direct sum: one nontrivial summand vs the rest
        -- Define ℂ[X]-submodules of AEval' T via the isomorphism e
        let N : Fin d → Type := fun i => ℂ[X] ⧸ ℂ[X] ∙ (X : ℂ[X]) ^ k i
        -- Helper: N j is subsingleton when k j = 0
        have N_subsingleton : ∀ j, k j = 0 → Subsingleton (N j) := by
          intro j hj
          exact Submodule.Quotient.subsingleton_iff.mpr
            (by rw [hj, pow_zero]; exact Ideal.span_singleton_one)
        -- At least two summands are nontrivial (k > 0), otherwise dim(ker T) ≤ 1
        obtain ⟨j₀, j₁, hkj₀, hkj₁, hne⟩ :
            ∃ j₀ j₁ : Fin d, 0 < k j₀ ∧ 0 < k j₁ ∧ j₀ ≠ j₁ := by
          by_contra hall
          push Not at hall
          -- hall : ∀ a b, 0 < k a → 0 < k b → a = b
          -- At most one index has k > 0. Show finrank(ker T) ≤ 1.
          exfalso
          have hker_le : Module.finrank ℂ (LinearMap.ker T) ≤ 1 := by
            by_cases hk_all : ∀ j : Fin d, k j = 0
            · -- All summands trivial → V ≅ 0
              haveI : Subsingleton V := by
                constructor; intro a b
                have ha : e (Module.AEval'.of (R := ℂ) T a) = 0 :=
                  DFinsupp.ext (fun j => (N_subsingleton j (hk_all j)).elim _ _)
                have hb : e (Module.AEval'.of (R := ℂ) T b) = 0 :=
                  DFinsupp.ext (fun j => (N_subsingleton j (hk_all j)).elim _ _)
                exact (Module.AEval'.of (R := ℂ) T).injective (e.injective (ha.trans hb.symm))
              have := Submodule.finrank_le (LinearMap.ker T)
              have := Module.finrank_zero_of_subsingleton (M := V) (R := ℂ)
              omega
            · -- Exactly one nontrivial summand
              push Not at hk_all
              obtain ⟨j₀, hkj₀⟩ := hk_all
              have hkj₀_pos : 0 < k j₀ := Nat.pos_of_ne_zero hkj₀
              have hothers : ∀ j, j ≠ j₀ → k j = 0 := by
                intro j hj; by_contra hkj
                exact hj (hall j j₀ (Nat.pos_of_ne_zero hkj) hkj₀_pos)
              -- Every kernel element maps to span of one generator
              set gen := (Submodule.Quotient.mk (p := ℂ[X] ∙ (X : ℂ[X]) ^ k j₀)
                ((X : ℂ[X]) ^ (k j₀ - 1)) : N j₀)
              set w : V := (Module.AEval'.of (R := ℂ) T).symm
                (e.symm (DirectSum.of N j₀ gen)) with hw_def
              suffices h_le : LinearMap.ker T ≤ Submodule.span ℂ ({w} : Set V) by
                exact (Submodule.finrank_mono h_le).trans
                  ((finrank_span_le_card ({w} : Set V)).trans (by simp))
              intro v hv
              rw [LinearMap.mem_ker] at hv
              have hXv : (X : ℂ[X]) • e (Module.AEval'.of (R := ℂ) T v) = 0 := by
                have h := e.map_smul (X : ℂ[X]) (Module.AEval'.of (R := ℂ) T v)
                rw [Module.AEval'.X_smul_of, hv, map_zero, map_zero] at h
                exact h.symm
              set c₀ := DirectSum.component ℂ[X] _ _ j₀ (e (Module.AEval'.of (R := ℂ) T v))
              have hc₀_tors : (X : ℂ[X]) • c₀ = 0 := by
                have h := (DirectSum.component ℂ[X] _ _ j₀).map_smul
                  (X : ℂ[X]) (e (Module.AEval'.of (R := ℂ) T v))
                rw [hXv, map_zero] at h; exact h.symm
              have hc₀_span := quotient_X_torsion_mem_span (k j₀) c₀ hc₀_tors
              rw [Submodule.mem_span_singleton] at hc₀_span
              obtain ⟨c, hc⟩ := hc₀_span
              have hds_eq : e (Module.AEval'.of (R := ℂ) T v) = DirectSum.of _ j₀ c₀ := by
                apply DFinsupp.ext; intro j
                by_cases hj : j = j₀
                · subst hj; rw [DirectSum.of_eq_same]; rfl
                · haveI := N_subsingleton j (hothers j hj)
                  exact Subsingleton.elim _ _
              have hv_eq : v = c • w := by
                apply (Module.AEval'.of (R := ℂ) T).injective
                apply e.injective
                have lhs : e (Module.AEval'.of (R := ℂ) T v) =
                    DirectSum.of _ j₀ (c • gen) := by
                  rw [hds_eq]; congr 1; exact hc.symm
                have rhs : e (Module.AEval'.of (R := ℂ) T (c • w)) =
                    DirectSum.of _ j₀ (c • gen) := by
                  rw [map_smul, hw_def, LinearEquiv.apply_symm_apply]
                  conv_lhs =>
                    rw [← IsScalarTower.algebraMap_smul ℂ[X] c
                      (e.symm (DirectSum.of _ j₀ gen))]
                  rw [e.map_smul, LinearEquiv.apply_symm_apply]
                  conv_rhs =>
                    rw [← IsScalarTower.algebraMap_smul ℂ[X] c gen]
                  exact ((DirectSum.lof ℂ[X] (Fin d)
                    (fun i => ℂ[X] ⧸ ℂ[X] ∙ X ^ k i) j₀).map_smul _ gen).symm
                exact lhs.trans rhs.symm
              rw [hv_eq]
              exact Submodule.smul_mem _ c (Submodule.subset_span rfl)
          linarith
        -- Use j₀ for the direct sum splitting
        -- P₁, P₂ are complementary in the direct sum
        let DS := DirectSum (Fin d) N
        let P₁ : Submodule ℂ[X] DS :=
          LinearMap.range (DirectSum.lof ℂ[X] (Fin d) N j₀)
        let P₂ : Submodule ℂ[X] DS :=
          LinearMap.ker (DirectSum.component ℂ[X] (Fin d) N j₀)
        have hP : IsCompl P₁ P₂ := by
          constructor
          · rw [Submodule.disjoint_def]
            intro w hw₁ hw₂
            obtain ⟨y, rfl⟩ := LinearMap.mem_range.mp hw₁
            have := LinearMap.mem_ker.mp hw₂
            rw [DirectSum.component.lof_self] at this
            simp [this]
          · rw [codisjoint_iff, Submodule.eq_top_iff']
            intro w
            have hw : w = DirectSum.lof ℂ[X] (Fin d) N j₀
                (DirectSum.component ℂ[X] (Fin d) N j₀ w) +
              (w - DirectSum.lof ℂ[X] (Fin d) N j₀
                (DirectSum.component ℂ[X] (Fin d) N j₀ w)) := by abel
            rw [hw]
            apply Submodule.add_mem_sup
            · exact LinearMap.mem_range.mpr ⟨_, rfl⟩
            · rw [LinearMap.mem_ker, map_sub, DirectSum.component.lof_self, sub_self]
        -- Transfer IsCompl through the order isomorphism induced by e.symm
        let oe := Submodule.orderIsoMapComap e.symm
        have hScompl : IsCompl (oe P₁) (oe P₂) := oe.isCompl hP
        -- S₁ = oe P₁, S₂ = oe P₂ as ℂ[X]-submodules
        let S₁ := oe P₁
        let S₂ := oe P₂
        -- Use these as ℂ-submodules of V (AEval' T = V as a type)
        refine ⟨S₁.restrictScalars ℂ, S₂.restrictScalars ℂ, ?_, ?_, ?_, ?_, ?_⟩
        · -- S₁ ≠ ⊥: N j₀ is nontrivial (k j₀ > 0), so P₁ = range(lof j₀) ≠ ⊥
          intro h
          rw [Submodule.restrictScalars_eq_bot_iff] at h
          have hP₁ : P₁ = ⊥ := by rwa [← oe.map_bot, oe.eq_iff_eq] at h
          rw [LinearMap.range_eq_bot] at hP₁
          have h1 := DFunLike.congr_fun hP₁ (1 : N j₀)
          simp only [LinearMap.zero_apply] at h1
          have hlof := DirectSum.lof_apply ℂ[X] j₀ (1 : N j₀)
          rw [h1, DFinsupp.zero_apply] at hlof
          haveI : Nontrivial (N j₀) := Submodule.Quotient.nontrivial_iff.mpr
            (Ideal.span_singleton_ne_top
              ((isUnit_pow_iff (by omega : k j₀ ≠ 0)).not.mpr Polynomial.not_isUnit_X))
          exact one_ne_zero hlof.symm
        · -- S₂ ≠ ⊥: lof j₁ 1 ∈ P₂ (j₁ ≠ j₀) and is nonzero (N j₁ nontrivial)
          intro h
          rw [Submodule.restrictScalars_eq_bot_iff] at h
          have hP₂ : P₂ = ⊥ := by rwa [← oe.map_bot, oe.eq_iff_eq] at h
          have hmem : DirectSum.lof ℂ[X] (Fin d) N j₁ (1 : N j₁) ∈ P₂ := by
            rw [LinearMap.mem_ker, DirectSum.component.of, dif_neg hne.symm]
          have hzero := (Submodule.eq_bot_iff _).mp hP₂ _ hmem
          have hlof := DirectSum.lof_apply ℂ[X] j₁ (1 : N j₁)
          rw [hzero, DFinsupp.zero_apply] at hlof
          haveI : Nontrivial (N j₁) := Submodule.Quotient.nontrivial_iff.mpr
            (Ideal.span_singleton_ne_top
              ((isUnit_pow_iff (by omega : k j₁ ≠ 0)).not.mpr Polynomial.not_isUnit_X))
          exact one_ne_zero hlof.symm
        · -- IsCompl S₁ S₂ as ℂ-submodules
          constructor
          · rw [Submodule.disjoint_def]
            intro w hw₁ hw₂
            exact Submodule.disjoint_def.mp hScompl.disjoint w hw₁ hw₂
          · rw [codisjoint_iff, Submodule.eq_top_iff']
            intro w
            have := Submodule.eq_top_iff'.mp hScompl.codisjoint.eq_top
              (Module.AEval'.of (R := ℂ) T w)
            rw [Submodule.mem_sup] at this ⊢
            obtain ⟨a, ha, b, hb, hab⟩ := this
            exact ⟨(Module.AEval'.of (R := ℂ) T).symm a, ha,
              (Module.AEval'.of (R := ℂ) T).symm b, hb,
              (Module.AEval'.of (R := ℂ) T).injective (by simp [hab])⟩
        · -- T-invariance of S₁
          intro w hw
          let w' := Module.AEval'.of (R := ℂ) T w
          have hw' : w' ∈ S₁ := hw
          have hXw : (X : ℂ[X]) • w' ∈ S₁ := S₁.smul_mem X hw'
          rw [Module.AEval'.X_smul_of] at hXw
          exact hXw
        · -- T-invariance of S₂
          intro w hw
          let w' := Module.AEval'.of (R := ℂ) T w
          have hw' : w' ∈ S₂ := hw
          have hXw : (X : ℂ[X]) • w' ∈ S₂ := S₂.smul_mem X hw'
          rw [Module.AEval'.X_smul_of] at hXw
          exact hXw
      · -- Case 2b-i: ker T ⊄ range T. Elementary: use hyperplane containing range T.
        -- Find v ∈ ker T \ range T
        obtain ⟨v, hv_ker, hv_range⟩ := Set.not_subset.mp hkR
        have hTv : T v = 0 := LinearMap.mem_ker.mp hv_ker
        have hv_ne : v ≠ 0 := fun h => by subst h; exact hv_range (Submodule.zero_mem _)
        -- span{v} ∩ range T = ⊥ (since v ∉ range T and span{v} is 1-dim)
        have hdv : Disjoint (Submodule.span ℂ {v}) (LinearMap.range T) := by
          rw [Submodule.disjoint_def]
          intro w hw₁ hw₂
          rw [Submodule.mem_span_singleton] at hw₁
          obtain ⟨c, rfl⟩ := hw₁
          by_contra h
          exact hv_range (by
            have hc : c ≠ 0 := fun hc => h (by simp [hc])
            exact (Submodule.smul_mem_iff _ hc).mp hw₂)
        -- Get complement C of (span{v} ⊔ range T) in V
        obtain ⟨C, hC⟩ := (Submodule.span ℂ {v} ⊔ LinearMap.range T).exists_isCompl
        -- M₂ = range T ⊔ C is complement of span{v}:
        -- V = span{v} ⊔ range T ⊔ C, and span{v} ∩ (range T ⊔ C) = ⊥
        refine ⟨Submodule.span ℂ {v}, LinearMap.range T ⊔ C, ?_, ?_, ?_, ?_, ?_⟩
        · -- span{v} ≠ ⊥
          exact mt Submodule.span_singleton_eq_bot.mp hv_ne
        · -- range T ⊔ C ≠ ⊥ (contains range T which is ≠ ⊥ since T ≠ 0)
          exact ne_bot_of_le_ne_bot (by rwa [ne_eq, LinearMap.range_eq_bot]) le_sup_left
        · -- IsCompl
          constructor
          · -- Disjoint: if w ∈ span{v} ∩ (range T ⊔ C), then w = 0
            rw [Submodule.disjoint_def]
            intro w hw₁ hw₂
            -- w ∈ span{v}, w ∈ range T ⊔ C
            obtain ⟨r, hr, c, hc, rfl⟩ := Submodule.mem_sup.mp hw₂
            -- r + c ∈ span{v}, so c = (r + c) - r ∈ span{v} + range T
            have hc_in : c ∈ Submodule.span ℂ {v} ⊔ LinearMap.range T := by
              have : r + c - r ∈ Submodule.span ℂ {v} ⊔ LinearMap.range T :=
                (Submodule.span ℂ {v} ⊔ LinearMap.range T).sub_mem
                  (Submodule.mem_sup_left hw₁) (Submodule.mem_sup_right hr)
              simpa using this
            -- c ∈ C ∩ (span{v} ⊔ range T) = ⊥
            have hc0 : c = 0 := by
              have : c ∈ (Submodule.span ℂ {v} ⊔ LinearMap.range T) ⊓ C :=
                Submodule.mem_inf.mpr ⟨hc_in, hc⟩
              rwa [hC.inf_eq_bot, Submodule.mem_bot] at this
            -- so w = r + 0 = r ∈ span{v} ∩ range T = ⊥
            rw [hc0, add_zero] at hw₁ ⊢
            exact Submodule.disjoint_def.mp hdv _ hw₁ hr
          · -- Codisjoint: span{v} ⊔ (range T ⊔ C) = ⊤
            rw [codisjoint_iff]
            calc Submodule.span ℂ {v} ⊔ (LinearMap.range T ⊔ C)
                = (Submodule.span ℂ {v} ⊔ LinearMap.range T) ⊔ C := by
                    rw [sup_assoc]
              _ = ⊤ := hC.codisjoint.eq_top
        · -- T-invariance of span{v}: Tv = 0
          intro w hw
          rw [Submodule.mem_span_singleton] at hw
          obtain ⟨c, rfl⟩ := hw
          rw [map_smul, hTv, smul_zero]
          exact Submodule.zero_mem _
        · -- T-invariance of range T ⊔ C: T maps V into range T ⊆ range T ⊔ C
          intro w _
          exact Submodule.mem_sup_left ⟨w, rfl⟩

/-- Helper: if v ∈ ker A and v ∉ range B, then (span{v}, ⊥) ⊕ (qV, W) is a nontrivial
product-compatible decomposition. -/
private lemma product_decomp_of_ker_A_not_range_B
    {V : Type*} [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V]
    {W : Type*} [AddCommGroup W] [Module ℂ W] [FiniteDimensional ℂ W]
    (A : V →ₗ[ℂ] W) (B : W →ₗ[ℂ] V)
    (v₀ : V) (hv₀_ne : v₀ ≠ 0) (hv₀_ker : A v₀ = 0)
    (hv₀_not_range : v₀ ∉ LinearMap.range B)
    (hW_or_kerA : 0 < Module.finrank ℂ W ∨
        1 < Module.finrank ℂ (LinearMap.ker A)) :
    ∃ (pV qV : Submodule ℂ V) (pW qW : Submodule ℂ W),
      IsCompl pV qV ∧ IsCompl pW qW ∧
      (∀ x ∈ pV, A x ∈ pW) ∧ (∀ x ∈ qV, A x ∈ qW) ∧
      (∀ x ∈ pW, B x ∈ pV) ∧ (∀ x ∈ qW, B x ∈ qV) ∧
      ¬(pV = ⊥ ∧ pW = ⊥) ∧ ¬(qV = ⊥ ∧ qW = ⊥) := by
  set pV := Submodule.span ℂ ({v₀} : Set V)
  -- range B is disjoint from span{v₀} since v₀ ∉ range B
  have h_disj : Disjoint pV (LinearMap.range B) := by
    rw [disjoint_comm]
    exact (Submodule.disjoint_span_singleton' hv₀_ne).mpr hv₀_not_range
  -- Get complement of (span{v₀} ⊔ range B)
  obtain ⟨C, hTC⟩ := (pV ⊔ LinearMap.range B).exists_isCompl
  set qV := LinearMap.range B ⊔ C
  have hcV : IsCompl pV qV := by
    constructor
    · rw [disjoint_iff, Submodule.eq_bot_iff]
      intro x hx
      obtain ⟨hx₁, hx₂⟩ := Submodule.mem_inf.mp hx
      obtain ⟨r, hr, c, hc, hrc⟩ := Submodule.mem_sup.mp hx₂
      have hc_T : c ∈ pV ⊔ LinearMap.range B := by
        have : c = x - r := by rw [← hrc]; abel
        rw [this]; exact (pV ⊔ LinearMap.range B).sub_mem
          (Submodule.mem_sup_left hx₁) (Submodule.mem_sup_right hr)
      have hc0 : c = 0 := by
        have := Submodule.mem_inf.mpr ⟨hc_T, hc⟩
        rwa [hTC.disjoint.eq_bot] at this
      have hxr : x = r := by rw [← hrc, hc0, add_zero]
      subst hxr
      exact h_disj.le_bot (Submodule.mem_inf.mpr ⟨hx₁, hr⟩)
    · simp only [codisjoint_iff]
      calc pV ⊔ qV = pV ⊔ (LinearMap.range B ⊔ C) := rfl
        _ = (pV ⊔ LinearMap.range B) ⊔ C := (sup_assoc _ _ _).symm
        _ = ⊤ := hTC.codisjoint.eq_top
  refine ⟨pV, qV, ⊥, ⊤, hcV, isCompl_bot_top, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · -- A(pV) ⊆ ⊥: A(v₀) = 0
    intro x hx; obtain ⟨c, rfl⟩ := Submodule.mem_span_singleton.mp hx
    simp [hv₀_ker]
  · -- A(qV) ⊆ ⊤
    intro _ _; exact Submodule.mem_top
  · -- B(⊥) ⊆ pV
    intro x hx; rw [(Submodule.mem_bot ℂ).mp hx, map_zero]; exact Submodule.zero_mem _
  · -- B(⊤) ⊆ qV: range B ⊆ qV
    intro x _; exact Submodule.mem_sup_left (LinearMap.mem_range_self B x)
  · -- ¬(pV = ⊥ ∧ ⊥ = ⊥): pV ≠ ⊥
    intro ⟨h, _⟩; exact hv₀_ne (show v₀ ∈ (⊥ : Submodule ℂ V) from
      h ▸ Submodule.subset_span rfl)
  · -- ¬(qV = ⊥ ∧ ⊤ = ⊥)
    intro ⟨hqV, hW_top⟩
    rcases hW_or_kerA with hW_pos | hkerA_gt
    · -- dim W > 0 → ⊤ ≠ ⊥
      haveI : Nontrivial W := Module.finrank_pos_iff.mp hW_pos
      exact absurd hW_top top_ne_bot
    · -- dim(ker A) > 1 → qV ≠ ⊥
      have hpV_top : pV = ⊤ := eq_top_of_isCompl_bot (hqV ▸ hcV)
      have h1 : Module.finrank ℂ pV ≤ 1 :=
        (finrank_span_le_card ({v₀} : Set V)).trans (by simp)
      rw [hpV_top, finrank_top] at h1
      have : Module.finrank ℂ (LinearMap.ker A) ≤ Module.finrank ℂ V :=
        Submodule.finrank_le _
      linarith

/-- The swap operator X : V × W → V × W defined by X(v,w) = (Bw, Av).
Used in Problem 6.9.1(c): when AB is nilpotent, X is nilpotent on V ⊕ W
and admits a compatible chain basis. -/
private noncomputable def swapOp
    {V : Type*} [AddCommGroup V] [Module ℂ V]
    {W : Type*} [AddCommGroup W] [Module ℂ W]
    (A : V →ₗ[ℂ] W) (B : W →ₗ[ℂ] V) : (V × W) →ₗ[ℂ] (V × W) :=
  LinearMap.coprod ((LinearMap.inr ℂ V W).comp A) ((LinearMap.inl ℂ V W).comp B)

private lemma swapOp_apply
    {V : Type*} [AddCommGroup V] [Module ℂ V]
    {W : Type*} [AddCommGroup W] [Module ℂ W]
    (A : V →ₗ[ℂ] W) (B : W →ₗ[ℂ] V) (v : V) (w : W) :
    swapOp A B (v, w) = (B w, A v) := by
  simp [swapOp, LinearMap.coprod_apply, LinearMap.comp_apply,
    LinearMap.inl_apply, LinearMap.inr_apply, Prod.mk_add_mk]

private lemma swapOp_sq
    {V : Type*} [AddCommGroup V] [Module ℂ V]
    {W : Type*} [AddCommGroup W] [Module ℂ W]
    (A : V →ₗ[ℂ] W) (B : W →ₗ[ℂ] V) :
    (swapOp A B) ^ 2 = (B.comp A).prodMap (A.comp B) := by
  ext <;> simp [sq, swapOp_apply, LinearMap.prodMap_apply, LinearMap.comp_apply]

private lemma swapOp_nilpotent
    {V : Type*} [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V]
    {W : Type*} [AddCommGroup W] [Module ℂ W] [FiniteDimensional ℂ W]
    (A : V →ₗ[ℂ] W) (B : W →ₗ[ℂ] V)
    (hAB : IsNilpotent (A.comp B)) (hBA : IsNilpotent (B.comp A)) :
    IsNilpotent (swapOp A B) := by
  obtain ⟨n, hn⟩ := hAB
  obtain ⟨m, hm⟩ := hBA
  refine ⟨2 * max n m, ?_⟩
  suffices h : ∀ k, (swapOp A B) ^ (2 * k) =
      ((B.comp A) ^ k).prodMap ((A.comp B) ^ k) by
    rw [h]
    have hBA_zero : (B.comp A) ^ max n m = 0 := by
      rw [← Nat.sub_add_cancel (Nat.le_max_right n m), pow_add, hm, mul_zero]
    have hAB_zero : (A.comp B) ^ max n m = 0 := by
      rw [← Nat.sub_add_cancel (Nat.le_max_left n m), pow_add, hn, mul_zero]
    simp [hBA_zero, hAB_zero, LinearMap.prodMap_zero]
  intro k
  have hsq := swapOp_sq A B
  induction k with
  | zero => simp [LinearMap.prodMap_one]
  | succ k ih =>
    rw [show 2 * (k + 1) = 2 * k + 2 from by omega, pow_add, ih, hsq,
      LinearMap.prodMap_mul, pow_succ, pow_succ]

/-- The endomorphism of the product that applies each map to the opposite component. -/
noncomputable def FiniteDimensionalLinearMapPair.combinedEndomorphism (ρ : FiniteDimensionalLinearMapPair ℂ) :
    (ρ.Left × ρ.Right) →ₗ[ℂ] (ρ.Left × ρ.Right) :=
  swapOp ρ.leftToRight ρ.rightToLeft

/-- The combined endomorphism swaps the components while applying the two structure maps. -/
@[simp]
theorem FiniteDimensionalLinearMapPair.combinedEndomorphism_apply (ρ : FiniteDimensionalLinearMapPair ℂ) (v : ρ.Left) (w : ρ.Right) :
    ρ.combinedEndomorphism (v, w) = (ρ.rightToLeft w, ρ.leftToRight v) := by
  exact swapOp_apply ρ.leftToRight ρ.rightToLeft v w

/-- The indexed iterates of a vector are linearly independent when its final coordinate is nonzero. -/
lemma linearIndependent_iterates_of_last_ne_zero (n : ℕ) (hn : 0 < n)
    (q : Fin n → ℂ) (hq : q ⟨n - 1, by omega⟩ ≠ 0) :
    LinearIndependent ℂ (fun i : Fin n =>
      (RepresentationTheory.RingTheory.Polynomial.JordanBlockModule.jordanNilpotent n ^ (i : ℕ)) q) := by
  rw [Fintype.linearIndependent_iff]
  intro c hc i
  suffices hall : ∀ j (hj : j < n), c ⟨j, hj⟩ = 0 by
    exact hall i i.isLt
  intro j
  induction j using Nat.strong_induction_on with
  | h j ih =>
      intro hj
      let row : Fin n := ⟨n - 1 - j, by omega⟩
      have heval := congrFun hc row
      simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Pi.zero_apply,
        RepresentationTheory.RingTheory.Polynomial.JordanBlockModule.jordanNilpotent_boundary_formula] at heval
      rw [Finset.sum_eq_single ⟨j, hj⟩] at heval
      · simp only [row] at heval
        rw [dif_pos (by omega)] at heval
        have hindex : (⟨n - 1 - j + j, by omega⟩ : Fin n) = ⟨n - 1, by omega⟩ :=
          Fin.ext (by simp; omega)
        rw [hindex] at heval
        exact (mul_eq_zero.mp heval).resolve_right hq
      · intro a _ hne
        by_cases haj : (a : ℕ) < j
        · rw [ih (a : ℕ) haj a.isLt, zero_mul]
        · have hja : j < (a : ℕ) := by
            have : (a : ℕ) ≠ j := fun h => hne (Fin.ext h)
            omega
          rw [dif_neg (show ¬ ((row : ℕ) + (a : ℕ) < n) by
            dsimp [row]
            omega), mul_zero]
      · intro hnot
        exact (hnot (Finset.mem_univ _)).elim

/-- A nilpotent endomorphism with one-dimensional kernel satisfies the indicated polynomial-module property. -/
lemma auxiliaryPolynomialProperty_of_isNilpotent_finrank_ker_eq_one
    {M : Type*} [AddCommGroup M] [Module ℂ M] [FiniteDimensional ℂ M]
    (T : Module.End ℂ M) (hT : IsNilpotent T)
    (hker : Module.finrank ℂ (LinearMap.ker T) = 1) :
    RepresentationTheory.LinearAlgebra.ModuleDecompositions.AuxiliaryDecompositionPredicate (Polynomial ℂ) (Module.AEval' T) := by
  let of := Module.AEval'.of (R := ℂ) T
  have hMpos : 0 < Module.finrank ℂ M := by
    have := Submodule.finrank_le (LinearMap.ker T)
    omega
  letI : Nontrivial M := Module.finrank_pos_iff.mp hMpos
  letI : Nontrivial (Module.AEval' T) := of.symm.toEquiv.nontrivial
  refine ⟨inferInstance, ?_⟩
  intro P Q hPQ
  by_contra hboth
  push Not at hboth
  obtain ⟨hP, hQ⟩ := hboth
  let scalarPart (N : Submodule (Polynomial ℂ) (Module.AEval' T)) : Submodule ℂ M :=
    (N.restrictScalars ℂ).comap of.toLinearMap
  have scalarPart_ne (N : Submodule (Polynomial ℂ) (Module.AEval' T)) (hN : N ≠ ⊥) :
      scalarPart N ≠ ⊥ := by
    rw [Submodule.ne_bot_iff] at hN ⊢
    obtain ⟨x, hx, hx0⟩ := hN
    refine ⟨of.symm x, ?_, ?_⟩
    · exact hx
    · exact (map_ne_zero_iff of.symm of.symm.injective).mpr hx0
  have scalarPart_invariant (N : Submodule (Polynomial ℂ) (Module.AEval' T)) :
      Set.MapsTo T (scalarPart N : Set M) (scalarPart N : Set M) := by
    intro x hx
    change of (T x) ∈ N
    rw [← Module.AEval'.X_smul_of]
    exact N.smul_mem Polynomial.X hx
  have kernelVector (N : Submodule (Polynomial ℂ) (Module.AEval' T)) (hN : N ≠ ⊥) :
      ∃ x : M, x ≠ 0 ∧ T x = 0 ∧ of x ∈ N := by
    let S := scalarPart N
    let TS : Module.End ℂ S := T.restrict (scalarPart_invariant N)
    have hTS : IsNilpotent TS := Module.End.isNilpotent.restrict _ hT
    letI : Nontrivial S := Submodule.nontrivial_iff_ne_bot.mpr (scalarPart_ne N hN)
    obtain ⟨x, hx0, hxker⟩ :=
      RepresentationTheory.RingTheory.Polynomial.JordanBlockModule.exists_ne_zero_mem_ker_of_isNilpotent TS hTS
    refine ⟨x, ?_, ?_, x.2⟩
    · exact fun hx => hx0 (Subtype.ext hx)
    · exact congrArg Subtype.val hxker
  obtain ⟨u, hu0, huT, huP⟩ := kernelVector P hP
  obtain ⟨v, hv0, hvT, hvQ⟩ := kernelVector Q hQ
  have huv : LinearIndependent ℂ ![u, v] := by
    rw [LinearIndependent.pair_iff]
    intro a b hab
    have hauP : of (a • u) ∈ P := by
      rw [map_smul, ← IsScalarTower.algebraMap_smul (Polynomial ℂ) a (of u)]
      exact P.smul_mem (algebraMap ℂ (Polynomial ℂ) a) huP
    have hbvQ : of (b • v) ∈ Q := by
      rw [map_smul, ← IsScalarTower.algebraMap_smul (Polynomial ℂ) b (of v)]
      exact Q.smul_mem (algebraMap ℂ (Polynomial ℂ) b) hvQ
    have hsum : of (a • u) + of (b • v) = 0 := by simpa using congrArg of hab
    have hneg : of (a • u) = -(of (b • v)) := eq_neg_of_add_eq_zero_left hsum
    have hinter : of (a • u) ∈ P ⊓ Q :=
      Submodule.mem_inf.mpr ⟨hauP, hneg.symm ▸ Q.neg_mem hbvQ⟩
    rw [hPQ.disjoint.eq_bot, Submodule.mem_bot] at hinter
    have hau0 : a • u = 0 := of.injective (by simpa using hinter)
    have hbv0 : b • v = 0 := by
      rw [hau0, zero_add] at hab
      exact hab
    exact ⟨(smul_eq_zero.mp hau0).resolve_right hu0,
      (smul_eq_zero.mp hbv0).resolve_right hv0⟩
  let uvKer : Fin 2 → LinearMap.ker T := fun i =>
    Fin.cases ⟨u, LinearMap.mem_ker.mpr huT⟩
      (fun _ => ⟨v, LinearMap.mem_ker.mpr hvT⟩) i
  have huvKer : LinearIndependent ℂ uvKer := by
    apply LinearIndependent.of_comp (LinearMap.ker T).subtype
    convert huv using 1
    funext i
    fin_cases i <;> rfl
  have htwo := huvKer.fintype_card_le_finrank
  simp only [Fintype.card_fin] at htwo
  omega

/-- Even powers of swapOp decompose as a product map: X^{2m} = (BA)^m × (AB)^m. -/
private lemma swapOp_pow_even
    {V : Type*} [AddCommGroup V] [Module ℂ V]
    {W : Type*} [AddCommGroup W] [Module ℂ W]
    (A : V →ₗ[ℂ] W) (B : W →ₗ[ℂ] V) (m : ℕ) :
    (swapOp A B) ^ (2 * m) = ((B.comp A) ^ m).prodMap ((A.comp B) ^ m) := by
  induction m with
  | zero => simp [LinearMap.prodMap_one]
  | succ m ih =>
    rw [show 2 * (m + 1) = 2 * m + 2 from by omega, pow_add, ih, swapOp_sq,
      LinearMap.prodMap_mul, pow_succ, pow_succ]

/-- X^{2m}(v, 0) = ((BA)^m v, 0): even powers of swapOp on pure V-elements stay in V×{0}. -/
private lemma swapOp_pow_even_fst
    {V : Type*} [AddCommGroup V] [Module ℂ V]
    {W : Type*} [AddCommGroup W] [Module ℂ W]
    (A : V →ₗ[ℂ] W) (B : W →ₗ[ℂ] V) (m : ℕ) (v : V) :
    (swapOp A B ^ (2 * m)) (v, (0 : W)) = (((B.comp A) ^ m) v, (0 : W)) := by
  rw [swapOp_pow_even, LinearMap.prodMap_apply, map_zero]

/-- X^{2m+1}(v, 0) = (0, A(BA)^m v): odd powers of swapOp on pure V-elements land in {0}×W. -/
private lemma swapOp_pow_odd_fst
    {V : Type*} [AddCommGroup V] [Module ℂ V]
    {W : Type*} [AddCommGroup W] [Module ℂ W]
    (A : V →ₗ[ℂ] W) (B : W →ₗ[ℂ] V) (m : ℕ) (v : V) :
    (swapOp A B ^ (2 * m + 1)) (v, (0 : W)) =
      ((0 : V), A (((B.comp A) ^ m) v)) := by
  rw [pow_succ', Module.End.mul_apply, swapOp_pow_even_fst, swapOp_apply, map_zero]

/-- X^{2m}(0, w) = (0, (AB)^m w): even powers of swapOp on pure W-elements stay in {0}×W. -/
private lemma swapOp_pow_even_snd
    {V : Type*} [AddCommGroup V] [Module ℂ V]
    {W : Type*} [AddCommGroup W] [Module ℂ W]
    (A : V →ₗ[ℂ] W) (B : W →ₗ[ℂ] V) (m : ℕ) (w : W) :
    (swapOp A B ^ (2 * m)) ((0 : V), w) = ((0 : V), ((A.comp B) ^ m) w) := by
  rw [swapOp_pow_even, LinearMap.prodMap_apply, map_zero]

/-- X^{2m+1}(0, w) = (B(AB)^m w, 0): odd powers of swapOp on pure W-elements land in V×{0}. -/
private lemma swapOp_pow_odd_snd
    {V : Type*} [AddCommGroup V] [Module ℂ V]
    {W : Type*} [AddCommGroup W] [Module ℂ W]
    (A : V →ₗ[ℂ] W) (B : W →ₗ[ℂ] V) (m : ℕ) (w : W) :
    (swapOp A B ^ (2 * m + 1)) ((0 : V), w) =
      (B (((A.comp B) ^ m) w), (0 : W)) := by
  rw [pow_succ', Module.End.mul_apply, swapOp_pow_even_snd, swapOp_apply, map_zero]

/-- If X^k kills (v,w), it also kills (v,0) and (0,w) separately.
This follows because X^k(v,0) and X^k(0,w) live in complementary subspaces
(one in V×{0}, the other in {0}×W) for any given k, so their sum being zero
forces both to be zero. -/
private lemma swapOp_pow_zero_of_pure
    {V : Type*} [AddCommGroup V] [Module ℂ V]
    {W : Type*} [AddCommGroup W] [Module ℂ W]
    (A : V →ₗ[ℂ] W) (B : W →ₗ[ℂ] V) (k : ℕ) (v : V) (w : W)
    (hk : (swapOp A B ^ k) (v, w) = 0) :
    (swapOp A B ^ k) (v, (0 : W)) = 0 ∧
    (swapOp A B ^ k) ((0 : V), w) = 0 := by
  have hlin : (swapOp A B ^ k) (v, w) =
      (swapOp A B ^ k) (v, (0 : W)) + (swapOp A B ^ k) ((0 : V), w) := by
    rw [← map_add]; congr 1; simp
  rw [hk] at hlin
  -- The two summands live in complementary subspaces depending on parity of k
  obtain ⟨m, rfl | rfl⟩ := k.even_or_odd'
  · -- k = 2*m: even powers stay in respective components
    rw [swapOp_pow_even_fst, swapOp_pow_even_snd] at hlin ⊢
    simp only [Prod.mk_add_mk, add_zero, zero_add] at hlin
    obtain ⟨h1, h2⟩ := Prod.mk.inj hlin
    exact ⟨by ext <;> simp [h1], by ext <;> simp [h2]⟩
  · -- k = 2*m+1: odd powers swap components
    rw [swapOp_pow_odd_fst, swapOp_pow_odd_snd] at hlin ⊢
    simp only [Prod.mk_add_mk, add_zero, zero_add] at hlin
    obtain ⟨h1, h2⟩ := Prod.mk.inj hlin
    exact ⟨by ext <;> simp [h2], by ext <;> simp [h1]⟩

/-- For (v,w) with X^{k-1}(v,w) ≠ 0, at least one of (v,0) or (0,w) also has
X^{k-1} ≠ 0. Combined with `swapOp_pow_zero_of_pure` (both have order ≤ k),
this means at least one pure component has the same X-order as (v,w). -/
private lemma swapOp_pure_order
    {V : Type*} [AddCommGroup V] [Module ℂ V]
    {W : Type*} [AddCommGroup W] [Module ℂ W]
    (A : V →ₗ[ℂ] W) (B : W →ₗ[ℂ] V) (k : ℕ) (v : V) (w : W)
    (hk1 : (swapOp A B ^ k) (v, w) ≠ 0) :
    (swapOp A B ^ k) (v, (0 : W)) ≠ 0 ∨
    (swapOp A B ^ k) ((0 : V), w) ≠ 0 := by
  by_contra h
  push Not at h
  obtain ⟨h1, h2⟩ := h
  apply hk1
  have : (swapOp A B ^ k) (v, w) =
      (swapOp A B ^ k) (v, (0 : W)) + (swapOp A B ^ k) ((0 : V), w) := by
    rw [← map_add]; congr 1; simp
  rw [this, h1, h2, add_zero]

private lemma swapOp_ker_finrank
    {V : Type*} [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V]
    {W : Type*} [AddCommGroup W] [Module ℂ W] [FiniteDimensional ℂ W]
    (A : V →ₗ[ℂ] W) (B : W →ₗ[ℂ] V) :
    Module.finrank ℂ (LinearMap.ker (swapOp A B)) =
      Module.finrank ℂ (LinearMap.ker A) + Module.finrank ℂ (LinearMap.ker B) := by
  -- ker(swapOp A B) = {(v,w) : Bw = 0 ∧ Av = 0} = (ker A) × (ker B)
  have hker : LinearMap.ker (swapOp A B) =
      (LinearMap.ker A).prod (LinearMap.ker B) := by
    ext ⟨v, w⟩
    simp only [LinearMap.mem_ker, swapOp_apply, Prod.mk_eq_zero, Submodule.mem_prod,
      LinearMap.mem_ker]
    exact ⟨fun ⟨h1, h2⟩ => ⟨h2, h1⟩, fun ⟨h1, h2⟩ => ⟨h2, h1⟩⟩
  rw [hker]
  let e : ↥((LinearMap.ker A).prod (LinearMap.ker B)) ≃ₗ[ℂ]
      ↥(LinearMap.ker A) × ↥(LinearMap.ker B) :=
    { toFun := fun x => (⟨x.1.1, (Submodule.mem_prod.mp x.2).1⟩,
                          ⟨x.1.2, (Submodule.mem_prod.mp x.2).2⟩)
      invFun := fun x => ⟨(x.1.1, x.2.1), Submodule.mem_prod.mpr ⟨x.1.2, x.2.2⟩⟩
      left_inv := fun ⟨⟨_, _⟩, _⟩ => rfl
      right_inv := fun ⟨⟨_, _⟩, ⟨_, _⟩⟩ => rfl
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl }
  rw [LinearEquiv.finrank_eq e, Module.finrank_prod]

/-- The kernel dimension of the combined endomorphism is the sum of the kernel dimensions of the component maps. -/
theorem FiniteDimensionalLinearMapPair.finrank_ker_combinedEndomorphism (ρ : FiniteDimensionalLinearMapPair ℂ) :
    Module.finrank ℂ (LinearMap.ker ρ.combinedEndomorphism) =
      Module.finrank ℂ (LinearMap.ker ρ.leftToRight) + Module.finrank ℂ (LinearMap.ker ρ.rightToLeft) := by
  simpa [FiniteDimensionalLinearMapPair.combinedEndomorphism] using swapOp_ker_finrank ρ.leftToRight ρ.rightToLeft

set_option maxHeartbeats 1600000 in
/-- If V × W = M ⊕ C where M = V' × W' is a product subspace and both M, C are
X-invariant (for X = swapOp A B), then V and W decompose compatibly.

Key: the projection proj onto M along C commutes with X. Define π_V(v) = fst(proj(v,0)),
σ_W(w) = snd(proj(0,w)). These are idempotent (M is a product), so V = V' ⊕ ker(π_V),
W = W' ⊕ ker(σ_W). Commutativity of proj with X gives A/B-compatibility. -/
private lemma product_complement_decomp
    {V : Type*} [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V]
    {W : Type*} [AddCommGroup W] [Module ℂ W] [FiniteDimensional ℂ W]
    (A : V →ₗ[ℂ] W) (B : W →ₗ[ℂ] V)
    (V' : Submodule ℂ V) (W' : Submodule ℂ W) (C : Submodule ℂ (V × W))
    (hcompl : IsCompl (V'.prod W') C)
    (hM_inv : ∀ p ∈ V'.prod W', swapOp A B p ∈ V'.prod W')
    (hC_inv : ∀ p ∈ C, swapOp A B p ∈ C) :
    ∃ (qV : Submodule ℂ V) (qW : Submodule ℂ W),
      IsCompl V' qV ∧ IsCompl W' qW ∧
      (∀ x ∈ V', A x ∈ W') ∧ (∀ x ∈ qV, A x ∈ qW) ∧
      (∀ x ∈ W', B x ∈ V') ∧ (∀ x ∈ qW, B x ∈ qV) := by
  set M := V'.prod W'
  set projM := M.projectionOnto C hcompl
  set proj : (V × W) →ₗ[ℂ] (V × W) := M.subtype.comp projM
  -- proj fixes M
  have hproj_M : ∀ x ∈ M, proj x = x := by
    intro x hx
    have : projM x = ⟨x, hx⟩ :=
      Submodule.projectionOnto_apply_left hcompl ⟨x, hx⟩
    simp [proj, this]
  -- proj kills C
  have hproj_C : ∀ x ∈ C, proj x = 0 := by
    intro x hx
    -- v4.30: projectionOnto_apply_of_mem_right takes only the membership proof (x implicit)
    have : projM x = 0 := Submodule.projectionOnto_apply_of_mem_right hcompl hx
    simp [proj, this]
  -- image ⊆ M
  have hproj_mem : ∀ x, proj x ∈ M := fun x => (projM x).2
  -- x - proj(x) ∈ C
  have hx_sub_proj : ∀ x, x - proj x ∈ C := by
    intro x
    rw [← Submodule.ker_projectionOnto hcompl, LinearMap.mem_ker,
      show projM (x - proj x) = projM x - projM (proj x) from map_sub _ _ _]
    have : projM (proj x) = projM x := by
      change projM ↑(projM x) = projM x
      exact Submodule.projectionOnto_apply_left hcompl (projM x)
    rw [this, sub_self]
  -- proj commutes with X
  set X := swapOp A B
  have hcomm : ∀ x, proj (X x) = X (proj x) := by
    intro x
    have hXm : X (proj x) ∈ M := hM_inv _ (hproj_mem x)
    have hXc : X (x - proj x) ∈ C := hC_inv _ (hx_sub_proj x)
    have hXx : X x = X (proj x) + X (x - proj x) := by rw [map_sub, add_sub_cancel]
    rw [hXx, map_add, hproj_M _ hXm, hproj_C _ hXc, add_zero]
  -- Define π_V, σ_W
  set ιV := LinearMap.inl ℂ V W
  set ιW := LinearMap.inr ℂ V W
  set π_V : V →ₗ[ℂ] V := (LinearMap.fst ℂ V W).comp (proj.comp ιV)
  set σ_W : W →ₗ[ℂ] W := (LinearMap.snd ℂ V W).comp (proj.comp ιW)
  -- π_V maps into V', σ_W maps into W'
  have hπ_range : ∀ v, π_V v ∈ V' :=
    fun v => (Submodule.mem_prod.mp (hproj_mem (ιV v))).1
  have hσ_range : ∀ w, σ_W w ∈ W' :=
    fun w => (Submodule.mem_prod.mp (hproj_mem (ιW w))).2
  -- π_V fixes V'
  have hπ_fix : ∀ v ∈ V', π_V v = v := by
    intro v hv
    have hmem : ιV v ∈ M := Submodule.mem_prod.mpr ⟨hv, Submodule.zero_mem _⟩
    change (proj (ιV v)).1 = v
    rw [hproj_M _ hmem]; rfl
  -- σ_W fixes W'
  have hσ_fix : ∀ w ∈ W', σ_W w = w := by
    intro w hw
    have hmem : ιW w ∈ M := Submodule.mem_prod.mpr ⟨Submodule.zero_mem _, hw⟩
    change (proj (ιW w)).2 = w
    rw [hproj_M _ hmem]; rfl
  -- Build π_V' : V →ₗ V' and σ_W' : W →ₗ W'
  set π_V' : V →ₗ[ℂ] V' :=
    { toFun := fun v => ⟨π_V v, hπ_range v⟩
      map_add' := fun a b => by ext; simp [π_V]
      map_smul' := fun r v => by ext; simp [π_V] }
  have hπ_V'_proj : ∀ x : V', π_V' x = x := by
    intro ⟨v, hv⟩; ext; exact hπ_fix v hv
  set σ_W' : W →ₗ[ℂ] W' :=
    { toFun := fun w => ⟨σ_W w, hσ_range w⟩
      map_add' := fun a b => by ext; simp [σ_W]
      map_smul' := fun r w => by ext; simp [σ_W] }
  have hσ_W'_proj : ∀ x : W', σ_W' x = x := by
    intro ⟨w, hw⟩; ext; exact hσ_fix w hw
  -- qV, qW
  set qV := LinearMap.ker π_V'
  set qW := LinearMap.ker σ_W'
  have hqV_iff : ∀ v, v ∈ qV ↔ π_V v = 0 := by
    intro v; simp [qV, π_V', LinearMap.mem_ker, Subtype.ext_iff]
  have hqW_iff : ∀ w, w ∈ qW ↔ σ_W w = 0 := by
    intro w; simp [qW, σ_W', LinearMap.mem_ker, Subtype.ext_iff]
  refine ⟨qV, qW, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact LinearMap.isCompl_of_proj hπ_V'_proj
  · exact LinearMap.isCompl_of_proj hσ_W'_proj
  · -- A : V' → W'
    intro v hv
    have h_M : ιV v ∈ M := Submodule.mem_prod.mpr ⟨hv, Submodule.zero_mem _⟩
    have hX := hM_inv _ h_M
    have : X (ιV v) = ιW (A v) := by simp [X, ιV, ιW, swapOp_apply]
    rw [this] at hX
    exact (Submodule.mem_prod.mp hX).2
  · -- A : qV → qW (proj commutes with X, pure element argument)
    intro v hv
    rw [hqW_iff]
    have hv0 := (hqV_iff v).mp hv
    have hXeq : X (ιV v) = ιW (A v) := by simp [X, ιV, ιW, swapOp_apply]
    have hm_fst : (proj (ιV v)).1 = 0 := hv0
    have key : (X (proj (ιV v))).2 = 0 := by
      change (swapOp A B (proj (ιV v))).2 = 0
      rw [show proj (ιV v) = ((proj (ιV v)).1, (proj (ιV v)).2) from (Prod.eta _).symm,
        swapOp_apply, hm_fst, map_zero]
    calc σ_W (A v) = (proj (ιW (A v))).2 := rfl
      _ = (proj (X (ιV v))).2 := by rw [hXeq]
      _ = (X (proj (ιV v))).2 := by rw [hcomm]
      _ = 0 := key
  · -- B : W' → V'
    intro w hw
    have h_M : ιW w ∈ M := Submodule.mem_prod.mpr ⟨Submodule.zero_mem _, hw⟩
    have hX := hM_inv _ h_M
    have : X (ιW w) = ιV (B w) := by simp [X, ιV, ιW, swapOp_apply]
    rw [this] at hX
    exact (Submodule.mem_prod.mp hX).1
  · -- B : qW → qV (symmetric to A : qV → qW)
    intro w hw
    rw [hqV_iff]
    have hw0 := (hqW_iff w).mp hw
    have hXeq : X (ιW w) = ιV (B w) := by simp [X, ιV, ιW, swapOp_apply]
    have hm_snd : (proj (ιW w)).2 = 0 := hw0
    have key : (X (proj (ιW w))).1 = 0 := by
      change (swapOp A B (proj (ιW w))).1 = 0
      rw [show proj (ιW w) = ((proj (ιW w)).1, (proj (ιW w)).2) from (Prod.eta _).symm,
        swapOp_apply, hm_snd, map_zero]
    calc π_V (B w) = (proj (ιV (B w))).1 := rfl
      _ = (proj (X (ιW w))).1 := by rw [hXeq]
      _ = (X (proj (ιW w))).1 := by rw [hcomm]
      _ = 0 := key

set_option maxHeartbeats 6400000 in
-- The PID and AEval' manipulations are expensive
/-- A nilpotent operator on V × W (acting via swapOp) with ker dimension ≥ 2
admits a nonzero X-invariant product subspace V' × W' with an X-invariant
complement. This is the pure generator replacement lemma: in the PID decomposition,
replace a generator of maximal-order summand with its pure component (which has the
same X-order by swapOp_pure_order), show the cyclic module is a product subspace,
and split it off via the retraction r(m) = (u⁻¹ · πᵢ(m)) • p. -/
private lemma exists_invariant_product_complement
    {V : Type*} [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V]
    {W : Type*} [AddCommGroup W] [Module ℂ W] [FiniteDimensional ℂ W]
    (A : V →ₗ[ℂ] W) (B : W →ₗ[ℂ] V)
    (hAB : IsNilpotent (A.comp B)) (hBA : IsNilpotent (B.comp A))
    (hker : 2 ≤ Module.finrank ℂ (LinearMap.ker A) +
              Module.finrank ℂ (LinearMap.ker B)) :
    ∃ (V' : Submodule ℂ V) (W' : Submodule ℂ W) (C : Submodule ℂ (V × W)),
      IsCompl (V'.prod W') C ∧
      (∀ p ∈ V'.prod W', swapOp A B p ∈ V'.prod W') ∧
      (∀ p ∈ C, swapOp A B p ∈ C) ∧
      ¬(V' = ⊥ ∧ W' = ⊥) ∧ C ≠ ⊥ := by
  set X := swapOp A B
  have hX_nil := swapOp_nilpotent A B hAB hBA
  have hX_ker : 2 ≤ Module.finrank ℂ (LinearMap.ker X) := by
    rw [swapOp_ker_finrank]; exact hker
  -- PID decomposition of V×W as ℂ[X]-module
  open Polynomial in
  have htors : Module.IsTorsion' (Module.AEval' (R := ℂ) X)
      (Submonoid.powers (Polynomial.X : ℂ[X])) := by
    obtain ⟨n, hn⟩ := hX_nil
    intro m
    refine ⟨⟨Polynomial.X ^ n, n, rfl⟩, ?_⟩
    set v := (Module.AEval'.of (R := ℂ) X).symm m
    have hm : m = Module.AEval'.of X v := (LinearEquiv.apply_symm_apply _ m).symm
    rw [hm, Submonoid.smul_def, Module.AEval'.X_pow_smul_of,
      LinearEquiv.map_eq_zero_iff]
    change (X ^ n) v = 0
    rw [hn]; rfl
  open Polynomial in
  obtain ⟨d, k, ⟨e⟩⟩ := Module.torsion_by_prime_power_decomposition
    Polynomial.irreducible_X htors
  -- d ≥ 2 (reuse the argument from nilpotent_nontrivial_decomp)
  set_option synthInstance.maxHeartbeats 40000 in
  have hd : 2 ≤ d := by
    by_contra hd_lt
    push Not at hd_lt
    let N : Fin d → Type := fun i => ℂ[X] ⧸ ℂ[X] ∙ (Polynomial.X : ℂ[X]) ^ k i
    interval_cases d
    · haveI : Subsingleton (V × W) := by
        constructor; intro a b
        have ha : e (Module.AEval'.of (R := ℂ) X a) = 0 :=
          DFinsupp.ext (fun i => Fin.elim0 i)
        have hb : e (Module.AEval'.of (R := ℂ) X b) = 0 :=
          DFinsupp.ext (fun i => Fin.elim0 i)
        exact (Module.AEval'.of (R := ℂ) X).injective (e.injective (ha.trans hb.symm))
      have := Module.finrank_zero_of_subsingleton (R := ℂ) (M := V × W)
      linarith [Submodule.finrank_le (LinearMap.ker X)]
    · exfalso
      have h1 : Module.finrank ℂ (LinearMap.ker X) ≤ 1 := by
        set j₀ : Fin 1 := ⟨0, by omega⟩
        set gen := (Submodule.Quotient.mk ((Polynomial.X : ℂ[X]) ^ (k j₀ - 1)) :
          ℂ[X] ⧸ ℂ[X] ∙ Polynomial.X ^ k j₀)
        set w : V × W := (Module.AEval'.of (R := ℂ) X).symm
          (e.symm (DirectSum.of N j₀ gen)) with hw_def
        suffices h_le : LinearMap.ker X ≤ Submodule.span ℂ ({w} : Set (V × W)) by
          exact (Submodule.finrank_mono h_le).trans
            ((finrank_span_le_card ({w} : Set (V × W))).trans (by simp))
        intro v hv
        rw [LinearMap.mem_ker] at hv
        have hXv : (Polynomial.X : ℂ[X]) • e (Module.AEval'.of (R := ℂ) X v) = 0 := by
          have h := e.map_smul (Polynomial.X : ℂ[X]) (Module.AEval'.of (R := ℂ) X v)
          rw [Module.AEval'.X_smul_of, hv, map_zero, map_zero] at h
          exact h.symm
        set c₀ := DirectSum.component ℂ[X] _ _ j₀ (e (Module.AEval'.of (R := ℂ) X v))
        have hc₀_tors : (Polynomial.X : ℂ[X]) • c₀ = 0 := by
          have h := (DirectSum.component ℂ[X] _ _ j₀).map_smul
            (Polynomial.X : ℂ[X]) (e (Module.AEval'.of (R := ℂ) X v))
          rw [hXv, map_zero] at h; exact h.symm
        have hc₀_span := quotient_X_torsion_mem_span (k j₀) c₀ hc₀_tors
        rw [Submodule.mem_span_singleton] at hc₀_span
        obtain ⟨c, hc⟩ := hc₀_span
        have hds_eq : e (Module.AEval'.of (R := ℂ) X v) = DirectSum.of _ j₀ c₀ := by
          apply DFinsupp.ext; intro ⟨i, hi⟩
          have : i = 0 := by omega
          subst this; rw [DirectSum.of_eq_same]; rfl
        have hv_eq : v = c • w := by
          apply (Module.AEval'.of (R := ℂ) X).injective
          apply e.injective
          have lhs : e (Module.AEval'.of (R := ℂ) X v) =
              DirectSum.of _ j₀ (c • gen) := by
            rw [hds_eq]; congr 1; exact hc.symm
          have rhs : e (Module.AEval'.of (R := ℂ) X (c • w)) =
              DirectSum.of _ j₀ (c • gen) := by
            rw [map_smul, hw_def, LinearEquiv.apply_symm_apply]
            conv_lhs =>
              rw [← IsScalarTower.algebraMap_smul ℂ[X] c
                (e.symm (DirectSum.of _ j₀ gen))]
            rw [e.map_smul, LinearEquiv.apply_symm_apply]
            conv_rhs =>
              rw [← IsScalarTower.algebraMap_smul ℂ[X] c gen]
            exact ((DirectSum.lof ℂ[X] (Fin 1)
              (fun i => ℂ[X] ⧸ ℂ[X] ∙ Polynomial.X ^ k i) j₀).map_smul _ gen).symm
          exact lhs.trans rhs.symm
        rw [hv_eq]
        exact Submodule.smul_mem _ c (Submodule.subset_span rfl)
      omega
  -- Now: d ≥ 2, we have the PID decomposition.
  -- Strategy: find a pure element p whose ℂ[X]-cyclic module is a product
  -- subspace AND a direct summand (replacing one PID summand via dimension
  -- counting and disjointness).
  open Polynomial in
  let N : Fin d → Type := fun i => ℂ[X] ⧸ ℂ[X] ∙ (Polynomial.X : ℂ[X]) ^ k i
  -- Find j_max maximizing k
  have ⟨j_max, _, hj_max⟩ := Finset.exists_max_image Finset.univ k
    ⟨⟨0, by omega⟩, Finset.mem_univ _⟩
  -- Generator of j_max-th summand and its pullback to V × W
  set gen_jmax : N j_max := Submodule.Quotient.mk (1 : ℂ[X])
  set g : V × W := (Module.AEval'.of (R := ℂ) X).symm
    (e.symm (DirectSum.of N j_max gen_jmax))
  set v₁ := g.1; set w₁ := g.2
  -- X^{k j_max} kills g
  have hg_kill : (X ^ k j_max) g = 0 := by
    suffices h : (Polynomial.X : ℂ[X]) ^ k j_max •
        (Module.AEval'.of (R := ℂ) X g) = 0 by
      rwa [Module.AEval'.X_pow_smul_of, LinearEquiv.map_eq_zero_iff] at h
    simp only [g, LinearEquiv.apply_symm_apply]
    rw [← map_smul, LinearEquiv.map_eq_zero_iff]
    -- X^{k j_max} • of(gen_jmax) = of(X^{k j_max} • gen_jmax) = of(0) = 0
    have hann : (Polynomial.X : ℂ[X]) ^ k j_max • gen_jmax = (0 : N j_max) := by
      -- gen_jmax = mkQ(1), X^k • mkQ(1) = mkQ(X^k • 1) = mkQ(X^k) = 0
      change (Submodule.mkQ (ℂ[X] ∙ (Polynomial.X : ℂ[X]) ^ k j_max))
        ((Polynomial.X ^ k j_max) • (1 : ℂ[X])) = 0
      rw [smul_eq_mul, mul_one, Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero]
      exact Submodule.mem_span_singleton_self _
    -- Smul distributes through DirectSum.of (lof is ℂ[X]-linear)
    have : (Polynomial.X ^ k j_max) • DirectSum.of N j_max gen_jmax =
        DirectSum.of N j_max ((Polynomial.X ^ k j_max) • gen_jmax) :=
      ((DirectSum.lof ℂ[X] (Fin d) N j_max).map_smul _ _).symm
    rw [this, hann, map_zero]
  -- Both pure components are killed by X^{k j_max}
  have hv1_kill : (X ^ k j_max) (v₁, (0 : W)) = 0 :=
    (swapOp_pow_zero_of_pure A B _ v₁ w₁ (show (X ^ k j_max) (v₁, w₁) = 0 from hg_kill)).1
  have hw1_kill : (X ^ k j_max) ((0 : V), w₁) = 0 :=
    (swapOp_pow_zero_of_pure A B _ v₁ w₁ (show (X ^ k j_max) (v₁, w₁) = 0 from hg_kill)).2
  -- g has exact order k j_max: X^{k-1} g ≠ 0 (since gen_jmax = mk(1) has
  -- exact order k in ℂ[X]/(X^k), and the isomorphism preserves this)
  have hg_exact : 0 < k j_max → (X ^ (k j_max - 1)) g ≠ 0 := by
    intro hk habs
    -- Transfer: X^{k-1} g = 0 → mk(X^{k-1}) = 0 in ℂ[X]/(X^k) → X^k | X^{k-1}
    -- But deg(X^k) > deg(X^{k-1}), contradiction.
    -- Step 1: X^{k-1} • AEval'.of(g) = 0
    have h1 : (Polynomial.X : ℂ[X]) ^ (k j_max - 1) •
        (Module.AEval'.of (R := ℂ) X g) = 0 := by
      rw [Module.AEval'.X_pow_smul_of]
      exact (Module.AEval'.of (R := ℂ) X).map_eq_zero_iff.mpr habs
    -- Step 2: In the direct sum, j_max component vanishes
    simp only [g, LinearEquiv.apply_symm_apply] at h1
    rw [← map_smul, LinearEquiv.map_eq_zero_iff] at h1
    -- Step 3: X^{k-1} • gen_jmax = 0 in N j_max
    have h2 : (Polynomial.X : ℂ[X]) ^ (k j_max - 1) • gen_jmax = 0 := by
      apply DirectSum.of_injective (β := N) j_max
      simp only [map_zero]
      change (DirectSum.lof ℂ[X] (Fin d) N j_max) _ = 0
      rw [(DirectSum.lof ℂ[X] (Fin d) N j_max).map_smul]
      exact h1
    -- Step 4: mk(X^{k-1}) = 0 in ℂ[X]/(X^k) means X^{k-1} ∈ ℂ[X] ∙ X^k
    have h3 : (Polynomial.X : ℂ[X]) ^ (k j_max - 1) ∈
        (ℂ[X] ∙ (Polynomial.X : ℂ[X]) ^ k j_max : Submodule ℂ[X] ℂ[X]) := by
      have h4 : (Submodule.mkQ (ℂ[X] ∙ (Polynomial.X : ℂ[X]) ^ k j_max))
          ((Polynomial.X : ℂ[X]) ^ (k j_max - 1)) = (0 : N j_max) := by
        have : (Submodule.mkQ (ℂ[X] ∙ (Polynomial.X : ℂ[X]) ^ k j_max))
            ((Polynomial.X : ℂ[X]) ^ (k j_max - 1) • (1 : ℂ[X])) =
            (Polynomial.X : ℂ[X]) ^ (k j_max - 1) • gen_jmax := by
          rw [map_smul]; rfl
        rw [smul_eq_mul, mul_one] at this
        rw [this]; exact h2
      rwa [Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero] at h4
    -- Step 5: X^k | X^{k-1} contradicts degree
    rw [Submodule.mem_span_singleton] at h3
    obtain ⟨c, hc⟩ := h3
    have hdvd : (Polynomial.X : ℂ[X]) ^ k j_max ∣ Polynomial.X ^ (k j_max - 1) :=
      ⟨c, by rw [← hc, smul_eq_mul, mul_comm]⟩
    have hne : (Polynomial.X : ℂ[X]) ^ (k j_max - 1) ≠ 0 :=
      pow_ne_zero _ Polynomial.X_ne_zero
    have := Polynomial.natDegree_le_of_dvd hdvd hne
    simp [Polynomial.natDegree_pow, Polynomial.natDegree_X] at this
    omega
  -- By swapOp_pure_order, at least one pure component has same X-order as g
  -- k j_max > 0 since otherwise all summands are trivial → V×W = 0 → contradicts dim(ker X) ≥ 2
  have hk_pos : 0 < k j_max := by
    by_contra h; push Not at h
    have hk0 : ∀ j : Fin d, k j = 0 := fun j => by
      have := hj_max j (Finset.mem_univ j); omega
    haveI : Subsingleton (V × W) := by
      constructor; intro a b
      have ha : e (Module.AEval'.of (R := ℂ) X a) = 0 :=
        DFinsupp.ext (fun j => by
          haveI : Subsingleton (N j) := Submodule.Quotient.subsingleton_iff.mpr
            (by rw [hk0 j, pow_zero]; exact Ideal.span_singleton_one)
          exact Subsingleton.elim _ _)
      have hb : e (Module.AEval'.of (R := ℂ) X b) = 0 :=
        DFinsupp.ext (fun j => by
          haveI : Subsingleton (N j) := Submodule.Quotient.subsingleton_iff.mpr
            (by rw [hk0 j, pow_zero]; exact Ideal.span_singleton_one)
          exact Subsingleton.elim _ _)
      exact (Module.AEval'.of (R := ℂ) X).injective (e.injective (ha.trans hb.symm))
    linarith [Module.finrank_zero_of_subsingleton (R := ℂ) (M := V × W),
      Submodule.finrank_le (LinearMap.ker X)]
  have hg_ne : (X ^ (k j_max - 1)) g ≠ 0 := hg_exact hk_pos
  -- At least one pure component has X^{k-1} applied nonzero
  have hpure := swapOp_pure_order A B (k j_max - 1) v₁ w₁ hg_ne
  -- Pure generator replacement: handle both cases
  rcases hpure with hp_v | hp_w
  · -- Case: (v₁, 0) has X-order k_max
    open Polynomial in
    -- e(of(v₁, 0)) has order k_max in ⨁ N_i; find j₀ where component has max order
    set p_aeval := (Module.AEval'.of (R := ℂ) X) (v₁, (0 : W))
    have hp_ne : (Polynomial.X : ℂ[X]) ^ (k j_max - 1) • e p_aeval ≠ 0 := by
      intro h; apply hp_v
      have h1 : (Polynomial.X : ℂ[X]) ^ (k j_max - 1) • p_aeval = 0 :=
        e.injective (by rw [map_smul, h, map_zero])
      rw [Module.AEval'.X_pow_smul_of] at h1
      exact (Module.AEval'.of (R := ℂ) X).injective h1
    obtain ⟨j₀, hj₀_ne⟩ : ∃ j₀ : Fin d,
        ((Polynomial.X : ℂ[X]) ^ (k j_max - 1) • e p_aeval : DirectSum (Fin d) N) j₀ ≠ 0 := by
      by_contra h; push Not at h; apply hp_ne
      exact DFinsupp.ext fun j => by simpa using h j
    -- k j₀ = k j_max (otherwise X^{k_max-1} kills N j₀, contradicting hj₀_ne)
    have hk_j₀ : k j₀ = k j_max := by
      have hle := hj_max j₀ (Finset.mem_univ j₀)
      by_contra hne; apply hj₀_ne
      have hlt : k j₀ < k j_max := lt_of_le_of_ne hle hne
      -- X^{k j₀} kills all of N j₀; k_max - 1 ≥ k j₀ since k_max > k j₀
      have hge : k j₀ ≤ k j_max - 1 := by omega
      have hkill : ∀ (c : N j₀), (Polynomial.X : ℂ[X]) ^ (k j₀) • c = 0 := by
        intro c
        induction c using Quotient.inductionOn' with
        | h f =>
          change Submodule.Quotient.mk ((Polynomial.X ^ k j₀) • f) = 0
          rw [Submodule.Quotient.mk_eq_zero, smul_eq_mul]
          exact Submodule.mem_span_singleton.mpr ⟨f, by rw [smul_eq_mul, mul_comm]⟩
      rw [show (k j_max - 1 : ℕ) = k j₀ + (k j_max - 1 - k j₀) from by omega,
        pow_add, mul_smul]
      exact hkill _
    -- Define φ : V×W → N j₀ (ℂ-linear projection through PID decomp)
    set φ : (V × W) →ₗ[ℂ] (N j₀) :=
      ((DirectSum.component ℂ[X] (Fin d) N j₀).restrictScalars ℂ).comp
        ((e.toLinearMap.restrictScalars ℂ).comp
          (Module.AEval'.of (R := ℂ) X).toLinearMap) with hφ_def
    -- φ commutes with X: φ(Xq) = Polynomial.X • φ(q)
    have hof_comm : ∀ q : V × W, (Module.AEval'.of (R := ℂ) X) (X q) =
        (Polynomial.X : ℂ[X]) • (Module.AEval'.of (R := ℂ) X) q := by
      intro q; rw [Module.AEval'.X_smul_of]
    have hφ_comm : ∀ q : V × W, φ (X q) = (Polynomial.X : ℂ[X]) • φ q := by
      intro q
      change (DirectSum.component ℂ[X] (Fin d) N j₀)
        (e ((Module.AEval'.of (R := ℂ) X) (X q))) =
        (Polynomial.X : ℂ[X]) • (DirectSum.component ℂ[X] (Fin d) N j₀)
          (e ((Module.AEval'.of (R := ℂ) X) q))
      rw [hof_comm, map_smul, map_smul]
    -- C = ker φ
    set C := LinearMap.ker φ
    -- C is X-invariant
    have hC_inv : ∀ q ∈ C, X q ∈ C := by
      intro q hq; rw [LinearMap.mem_ker] at hq ⊢; rw [hφ_comm, hq, smul_zero]
    -- V' and W' from the X-orbit of (v₁, 0)
    set V'₀ := Submodule.span ℂ (Set.range (fun m : ℕ => ((B.comp A) ^ m) v₁)) with V'₀_def
    set W'₀ := Submodule.span ℂ (Set.range (fun m : ℕ => A (((B.comp A) ^ m) v₁))) with W'₀_def
    -- A maps V'₀ to W'₀ and B maps W'₀ to V'₀
    have hA_map : Submodule.map A V'₀ ≤ W'₀ := by
      rw [V'₀_def, Submodule.map_span]; apply Submodule.span_mono
      rintro _ ⟨_, ⟨m, rfl⟩, rfl⟩; exact ⟨m, rfl⟩
    have hB_map : Submodule.map B W'₀ ≤ V'₀ := by
      rw [W'₀_def, Submodule.map_span]; apply Submodule.span_mono
      rintro _ ⟨_, ⟨m, rfl⟩, rfl⟩
      exact ⟨m + 1, by simp [pow_succ', LinearMap.comp_apply]⟩
    -- V'₀.prod W'₀ is X-invariant
    have hVW_inv : ∀ q ∈ V'₀.prod W'₀, X q ∈ V'₀.prod W'₀ := by
      intro q hq; rw [Submodule.mem_prod] at hq ⊢; rw [swapOp_apply]
      exact ⟨hB_map ⟨q.2, hq.2, rfl⟩, hA_map ⟨q.1, hq.1, rfl⟩⟩
    -- V'₀ ≠ ⊥ (v₁ ≠ 0 since X^{k-1}(v₁, 0) ≠ 0)
    have hVW_ne : ¬(V'₀ = ⊥ ∧ W'₀ = ⊥) := by
      intro ⟨hV, _⟩
      have hv₁_mem : v₁ ∈ V'₀ := Submodule.subset_span ⟨0, by simp⟩
      rw [hV] at hv₁_mem
      rw [Submodule.mem_bot] at hv₁_mem
      have : (v₁, (0 : W)) = 0 := Prod.ext_iff.mpr ⟨hv₁_mem, rfl⟩
      exact hp_v (by rw [this, map_zero])
    -- IsCompl (V'₀.prod W'₀) C: follows from φ|_{V'₀.prod W'₀} being an isomorphism
    -- onto N j₀ ≅ ℂ[X]/(X^k_max). The pure element (v₁, 0) generates a cyclic module
    -- of dimension k_max that bijects onto N j₀ via φ, giving both disjointness
    -- (injectivity of φ on V'₀.prod W'₀) and dimension equality (rank-nullity).
    -- φ(p) is a unit in N j₀ (X^{k-1}•φ(p) ≠ 0 → coprime to X → unit)
    set p : V × W := (v₁, (0 : W))
    have hφp_ne : (Polynomial.X : ℂ[X]) ^ (k j₀ - 1) • φ p ≠ 0 := by
      change (Polynomial.X : ℂ[X]) ^ (k j₀ - 1) •
        (DirectSum.component ℂ[X] (Fin d) N j₀ (e p_aeval)) ≠ 0
      rw [← map_smul, show k j₀ - 1 = k j_max - 1 from by omega]
      exact hj₀_ne
    have hφp_unit : IsUnit (φ p) :=
      quotient_X_pow_isUnit_of_maxOrder (k j₀) (hk_j₀ ▸ hk_pos) (φ p) hφp_ne
    -- X^m(p) ∈ V'₀.prod W'₀ for all m (by X-invariance + p ∈ V'₀.prod W'₀)
    have hp_mem : p ∈ V'₀.prod W'₀ := by
      rw [Submodule.mem_prod]
      exact ⟨Submodule.subset_span ⟨0, by simp [p]⟩, Submodule.zero_mem _⟩
    have hXm_mem : ∀ m : ℕ, (X ^ m) p ∈ V'₀.prod W'₀ := by
      intro m; induction m with
      | zero => simpa using hp_mem
      | succ n ih =>
        have : (X ^ (n + 1)) p = X ((X ^ n) p) := by
          rw [pow_succ']; rfl
        rw [this]; exact hVW_inv _ ih
    -- φ(X^m(p)) = X^m • φ(p) (iterated commutation)
    have hφ_iter : ∀ m : ℕ, φ ((X ^ m) p) = (Polynomial.X : ℂ[X]) ^ m • φ p := by
      intro m; induction m with
      | zero => simp
      | succ n ih =>
        have : (X ^ (n + 1)) p = X ((X ^ n) p) := by
          rw [pow_succ']; rfl
        rw [this, hφ_comm, ih, smul_smul, pow_succ']
    -- IsCompl via codisjoint (unit section) + disjoint (dimension)
    -- Step A: φ composed with polynomial evaluation = polynomial action on φ(p)
    have hφ_aeval : ∀ f : ℂ[X], φ ((Polynomial.aeval X f) p) = f • φ p := by
      intro f
      change (DirectSum.component ℂ[X] (Fin d) N j₀)
        (e ((Module.AEval'.of (R := ℂ) X) ((Polynomial.aeval X f) p))) =
        f • (DirectSum.component ℂ[X] (Fin d) N j₀)
          (e ((Module.AEval'.of (R := ℂ) X) p))
      conv_lhs => rw [show (Module.AEval'.of (R := ℂ) X) ((Polynomial.aeval X f) p) =
          f • (Module.AEval'.of (R := ℂ) X) p from Module.AEval.of_aeval_smul ..]
      rw [map_smul, map_smul]
    -- Step B: polynomial evaluation at X preserves V'₀.prod W'₀
    have haeval_mem : ∀ f : ℂ[X], (Polynomial.aeval X f) p ∈ V'₀.prod W'₀ := by
      intro f; induction f using Polynomial.induction_on' with
      | add f g hf hg => rw [map_add, LinearMap.add_apply]; exact Submodule.add_mem _ hf hg
      | monomial n c =>
        rw [Polynomial.aeval_monomial, Algebra.algebraMap_eq_smul_one, smul_mul_assoc,
          one_mul, LinearMap.smul_apply]
        exact Submodule.smul_mem _ _ (hXm_mem n)
    -- Step C: φ is surjective (component ∘ iso ∘ iso)
    have hφ_surj : Function.Surjective φ := by
      intro a
      refine ⟨(Module.AEval'.of (R := ℂ) X).symm
        (e.symm ((DirectSum.lof ℂ[X] (Fin d) N j₀) a)), ?_⟩
      change (DirectSum.component ℂ[X] (Fin d) N j₀)
        (e ((Module.AEval'.of (R := ℂ) X)
          ((Module.AEval'.of (R := ℂ) X).symm
            (e.symm ((DirectSum.lof ℂ[X] (Fin d) N j₀) a))))) = a
      rw [LinearEquiv.apply_symm_apply, LinearEquiv.apply_symm_apply,
        DirectSum.component.lof_self]
    -- Step D: finrank(N j₀) = k j₀
    have hfr_N : Module.finrank ℂ (N j₀) = k j₀ := by
      change Module.finrank ℂ (ℂ[X] ⧸ (ℂ[X] ∙ (Polynomial.X : ℂ[X]) ^ k j₀)) = k j₀
      rw [show (ℂ[X] ∙ (Polynomial.X : ℂ[X]) ^ k j₀ : Submodule ℂ[X] ℂ[X]) =
          (Ideal.span {(Polynomial.X : ℂ[X]) ^ k j₀} : Ideal ℂ[X]) from
        (Ideal.submodule_span_eq).symm]
      rw [finrank_quotient_span_eq_natDegree, Polynomial.natDegree_pow,
        Polynomial.natDegree_X, mul_one]
    -- Step E: finrank(V'₀.prod W'₀) ≤ k j₀ (finite span)
    have hfr_le : Module.finrank ℂ ↥(V'₀.prod W'₀) ≤ k j₀ := by
      have hX_kill : ∀ m, k j₀ ≤ m → (X ^ m) p = 0 := by
        intro m hm
        have hm' : k j_max ≤ m := hk_j₀ ▸ hm
        calc (X ^ m) p = (X ^ (m - k j_max) * X ^ k j_max) p := by
              rw [← pow_add, Nat.sub_add_cancel hm']
            _ = (X ^ (m - k j_max)) ((X ^ k j_max) p) := by
              rw [Module.End.mul_apply]
            _ = 0 := by rw [hv1_kill, map_zero]
      -- V'₀.prod W'₀ ≤ ℂ-span{X^m p | m < k j₀} via generator containment
      classical
      set SF := Finset.univ.image (fun m : Fin (k j₀) => (X ^ (m : ℕ)) p)
      have h_le : V'₀.prod W'₀ ≤ Submodule.span ℂ (↑SF) := by
        intro ⟨v, w⟩ ⟨hv, hw⟩
        -- Decompose (v, w) = (v, 0) + (0, w)
        have hsum : (v, w) = (v, (0 : W)) + ((0 : V), w) := by ext <;> simp
        rw [hsum]; apply Submodule.add_mem
        -- (v, 0) ∈ span SF: use LinearMap.inl to map V'₀ generators into SF
        · have hmap : Submodule.map (LinearMap.inl ℂ V W) V'₀ ≤ Submodule.span ℂ (↑SF) := by
            rw [V'₀_def, Submodule.map_span]; apply Submodule.span_le.mpr
            rintro _ ⟨_, ⟨m, rfl⟩, rfl⟩
            change (((B.comp A) ^ m) v₁, (0 : W)) ∈ Submodule.span ℂ (↑SF)
            by_cases hm : 2 * m < k j₀
            · apply Submodule.subset_span; simp [SF]
              exact ⟨⟨2 * m, hm⟩, swapOp_pow_even_fst A B m v₁⟩
            · have hk := hX_kill (2 * m) (by omega)
              rw [swapOp_pow_even_fst A B m v₁, Prod.mk.injEq] at hk
              rw [hk.1]; exact Submodule.zero_mem _
          exact hmap ⟨v, hv, rfl⟩
        -- (0, w) ∈ span SF: use LinearMap.inr to map W'₀ generators into SF
        · have hmap : Submodule.map (LinearMap.inr ℂ V W) W'₀ ≤ Submodule.span ℂ (↑SF) := by
            rw [W'₀_def, Submodule.map_span]; apply Submodule.span_le.mpr
            rintro _ ⟨_, ⟨m, rfl⟩, rfl⟩
            change ((0 : V), A (((B.comp A) ^ m) v₁)) ∈ Submodule.span ℂ (↑SF)
            by_cases hm : 2 * m + 1 < k j₀
            · apply Submodule.subset_span; simp [SF]
              exact ⟨⟨2 * m + 1, hm⟩, swapOp_pow_odd_fst A B m v₁⟩
            · have hk := hX_kill (2 * m + 1) (by omega)
              rw [swapOp_pow_odd_fst A B m v₁, Prod.mk.injEq] at hk
              rw [hk.2]; exact Submodule.zero_mem _
          exact hmap ⟨w, hw, rfl⟩
      have h1 : Module.finrank ℂ ↥(V'₀.prod W'₀)
          ≤ Module.finrank ℂ ↥(Submodule.span ℂ (↑SF : Set (V × W))) :=
        Submodule.finrank_mono h_le
      have h2 : Module.finrank ℂ ↥(Submodule.span ℂ (↑SF : Set (V × W))) ≤ SF.card :=
        finrank_span_finset_le_card SF
      have h3 : SF.card ≤ k j₀ := by
        exact le_trans Finset.card_image_le (le_of_eq (Finset.card_fin _))
      linarith
    -- Step F: Codisjoint (unit section gives decomposition)
    have hcodisjoint : Codisjoint (V'₀.prod W'₀) C := by
      obtain ⟨u, hu⟩ := hφp_unit
      rw [codisjoint_iff, eq_top_iff]; intro q _
      obtain ⟨g, hg⟩ := Ideal.Quotient.mk_surjective (φ q * ↑u⁻¹ : N j₀)
      have hker : q - (Polynomial.aeval X g) p ∈ LinearMap.ker φ := by
        rw [LinearMap.mem_ker, map_sub, hφ_aeval]
        change φ q - (Ideal.Quotient.mk (ℂ[X] ∙ Polynomial.X ^ k j₀) g) * φ p = 0
        rw [hg, ← hu, mul_assoc,
          Units.inv_mul, mul_one, sub_self]
      have hq_decomp : q = (Polynomial.aeval X g) p + (q - (Polynomial.aeval X g) p) := by
        abel
      rw [hq_decomp]
      exact Submodule.add_mem_sup (haeval_mem g) hker
    -- Step G: Disjoint (dimension argument from codisjoint)
    have hdisjoint : Disjoint (V'₀.prod W'₀) C := by
      -- From codisjoint + rank-nullity + finrank bound
      have hfr_eq := Submodule.finrank_sup_add_finrank_inf_eq (V'₀.prod W'₀) C
      rw [hcodisjoint.eq_top, finrank_top] at hfr_eq
      have hfr_rn := LinearMap.finrank_range_add_finrank_ker φ
      rw [LinearMap.range_eq_top.mpr hφ_surj, finrank_top, hfr_N] at hfr_rn
      -- hfr_rn mentions LinearMap.ker φ, but C = LinearMap.ker φ; unify for omega
      change k j₀ + Module.finrank ℂ ↥C = Module.finrank ℂ (V × W) at hfr_rn
      have hfr_inf : Module.finrank ℂ ↥(V'₀.prod W'₀ ⊓ C) = 0 := by omega
      rw [disjoint_iff]
      exact Submodule.finrank_eq_zero.mp hfr_inf
    have hcompl : IsCompl (V'₀.prod W'₀) C := ⟨hdisjoint, hcodisjoint⟩
    -- C ≠ ⊥: φ is not injective since finrank(V×W) = Σ k_i > k_max = finrank(N j₀)
    -- (at least 2 nontrivial summands exist because dim(ker X) ≥ 2, and each
    -- nontrivial cyclic summand contributes exactly 1 to dim(ker X))
    have hC_ne : C ≠ ⊥ := by
      intro hC_bot
      have hinj : Function.Injective φ := LinearMap.ker_eq_bot.mp hC_bot
      -- The X-torsion of N j₀ is at most 1-dimensional (quotient_X_torsion_mem_span)
      set gen : N j₀ := Submodule.Quotient.mk ((Polynomial.X : ℂ[X]) ^ (k j₀ - 1))
      -- Pick w₀ ∈ ker X, w₀ ≠ 0
      haveI : Nontrivial (LinearMap.ker X) :=
        Module.finrank_pos_iff.mp (by linarith)
      obtain ⟨⟨w₀, hw₀_mem⟩, hw₀_ne⟩ := exists_ne (0 : LinearMap.ker X)
      have hw₀' : w₀ ≠ 0 := fun h => hw₀_ne (Subtype.ext h)
      have hw₀_ker : X w₀ = 0 := LinearMap.mem_ker.mp hw₀_mem
      -- φ(w₀) is X-torsion and nonzero (by injectivity)
      have hXφw₀ : (Polynomial.X : ℂ[X]) • φ w₀ = 0 := by
        rw [← hφ_comm, hw₀_ker, map_zero]
      have hφw₀_ne : φ w₀ ≠ 0 := fun h => hw₀' (hinj (h.trans (map_zero φ).symm))
      -- φ(w₀) ∈ span{gen}, so get scalar c₀ ≠ 0
      have hφw₀_span := quotient_X_torsion_mem_span (k j₀) (φ w₀) hXφw₀
      rw [Submodule.mem_span_singleton] at hφw₀_span
      obtain ⟨c₀, hc₀⟩ := hφw₀_span
      have hc₀_ne : c₀ ≠ 0 := by intro h; rw [h, zero_smul] at hc₀; exact hφw₀_ne hc₀.symm
      -- ker X ≤ span{w₀}, giving finrank ≤ 1, contradicting hX_ker ≥ 2
      suffices h_le : LinearMap.ker X ≤ Submodule.span ℂ ({w₀} : Set (V × W)) by
        have h1 := Submodule.finrank_mono h_le
        rw [finrank_span_singleton hw₀'] at h1
        linarith
      intro v hv
      have hv_ker : X v = 0 := LinearMap.mem_ker.mp hv
      have hXφv : (Polynomial.X : ℂ[X]) • φ v = 0 := by
        rw [← hφ_comm, hv_ker, map_zero]
      have hφv_span := quotient_X_torsion_mem_span (k j₀) (φ v) hXφv
      rw [Submodule.mem_span_singleton] at hφv_span
      obtain ⟨c, hc⟩ := hφv_span
      -- v = (c * c₀⁻¹) • w₀ by injectivity (both map to scalar multiples of gen)
      have hv_eq : v = (c * c₀⁻¹) • w₀ := by
        apply hinj; rw [map_smul]
        rw [show φ w₀ = c₀ • gen from hc₀.symm, smul_smul,
          mul_assoc, inv_mul_cancel₀ hc₀_ne, mul_one]
        exact hc.symm
      rw [hv_eq]; exact Submodule.smul_mem _ _ (Submodule.subset_span rfl)
    exact ⟨V'₀, W'₀, C, hcompl, hVW_inv, hC_inv, hVW_ne, hC_ne⟩
  · -- Case: (0, w₁) has X-order k_max, symmetric (swap A↔B, V↔W roles)
    open Polynomial in
    set p_aeval := (Module.AEval'.of (R := ℂ) X) ((0 : V), w₁)
    have hp_ne : (Polynomial.X : ℂ[X]) ^ (k j_max - 1) • e p_aeval ≠ 0 := by
      intro h; apply hp_w
      have h1 : (Polynomial.X : ℂ[X]) ^ (k j_max - 1) • p_aeval = 0 :=
        e.injective (by rw [map_smul, h, map_zero])
      rw [Module.AEval'.X_pow_smul_of] at h1
      exact (Module.AEval'.of (R := ℂ) X).injective h1
    obtain ⟨j₀, hj₀_ne⟩ : ∃ j₀ : Fin d,
        ((Polynomial.X : ℂ[X]) ^ (k j_max - 1) • e p_aeval : DirectSum (Fin d) N) j₀ ≠ 0 := by
      by_contra h; push Not at h; apply hp_ne
      exact DFinsupp.ext fun j => by simpa using h j
    have hk_j₀ : k j₀ = k j_max := by
      have hle := hj_max j₀ (Finset.mem_univ j₀)
      by_contra hne; apply hj₀_ne
      have hlt : k j₀ < k j_max := lt_of_le_of_ne hle hne
      have hge : k j₀ ≤ k j_max - 1 := by omega
      have hkill : ∀ (c : N j₀), (Polynomial.X : ℂ[X]) ^ (k j₀) • c = 0 := by
        intro c
        induction c using Quotient.inductionOn' with
        | h f =>
          change Submodule.Quotient.mk ((Polynomial.X ^ k j₀) • f) = 0
          rw [Submodule.Quotient.mk_eq_zero, smul_eq_mul]
          exact Submodule.mem_span_singleton.mpr ⟨f, by rw [smul_eq_mul, mul_comm]⟩
      rw [show (k j_max - 1 : ℕ) = k j₀ + (k j_max - 1 - k j₀) from by omega,
        pow_add, mul_smul]
      exact hkill _
    set φ : (V × W) →ₗ[ℂ] (N j₀) :=
      ((DirectSum.component ℂ[X] (Fin d) N j₀).restrictScalars ℂ).comp
        ((e.toLinearMap.restrictScalars ℂ).comp
          (Module.AEval'.of (R := ℂ) X).toLinearMap) with hφ_def
    have hof_comm : ∀ q : V × W, (Module.AEval'.of (R := ℂ) X) (X q) =
        (Polynomial.X : ℂ[X]) • (Module.AEval'.of (R := ℂ) X) q := by
      intro q; rw [Module.AEval'.X_smul_of]
    have hφ_comm : ∀ q : V × W, φ (X q) = (Polynomial.X : ℂ[X]) • φ q := by
      intro q
      change (DirectSum.component ℂ[X] (Fin d) N j₀)
        (e ((Module.AEval'.of (R := ℂ) X) (X q))) =
        (Polynomial.X : ℂ[X]) • (DirectSum.component ℂ[X] (Fin d) N j₀)
          (e ((Module.AEval'.of (R := ℂ) X) q))
      rw [hof_comm, map_smul, map_smul]
    set C := LinearMap.ker φ
    have hC_inv : ∀ q ∈ C, X q ∈ C := by
      intro q hq; rw [LinearMap.mem_ker] at hq ⊢; rw [hφ_comm, hq, smul_zero]
    -- W'₀ from (AB)^m orbits, V'₀ from B((AB)^m) orbits
    set W'₀ := Submodule.span ℂ (Set.range (fun m : ℕ => ((A.comp B) ^ m) w₁)) with W'₀_def
    set V'₀ := Submodule.span ℂ (Set.range (fun m : ℕ => B (((A.comp B) ^ m) w₁))) with V'₀_def
    have hB_map : Submodule.map B W'₀ ≤ V'₀ := by
      rw [W'₀_def, Submodule.map_span]; apply Submodule.span_mono
      rintro _ ⟨_, ⟨m, rfl⟩, rfl⟩; exact ⟨m, rfl⟩
    have hA_map : Submodule.map A V'₀ ≤ W'₀ := by
      rw [V'₀_def, Submodule.map_span]; apply Submodule.span_mono
      rintro _ ⟨_, ⟨m, rfl⟩, rfl⟩
      exact ⟨m + 1, by simp [pow_succ', LinearMap.comp_apply]⟩
    have hVW_inv : ∀ q ∈ V'₀.prod W'₀, X q ∈ V'₀.prod W'₀ := by
      intro q hq; rw [Submodule.mem_prod] at hq ⊢; rw [swapOp_apply]
      exact ⟨hB_map ⟨q.2, hq.2, rfl⟩, hA_map ⟨q.1, hq.1, rfl⟩⟩
    have hVW_ne : ¬(V'₀ = ⊥ ∧ W'₀ = ⊥) := by
      intro ⟨_, hW⟩
      have hw₁_mem : w₁ ∈ W'₀ := Submodule.subset_span ⟨0, by simp⟩
      rw [hW] at hw₁_mem
      rw [Submodule.mem_bot] at hw₁_mem
      have : ((0 : V), w₁) = 0 := Prod.ext_iff.mpr ⟨rfl, hw₁_mem⟩
      exact hp_w (by rw [this, map_zero])
    -- φ(p) is a unit in N j₀ (X^{k-1}•φ(p) ≠ 0 → coprime to X → unit)
    set p : V × W := ((0 : V), w₁)
    have hφp_ne : (Polynomial.X : ℂ[X]) ^ (k j₀ - 1) • φ p ≠ 0 := by
      change (Polynomial.X : ℂ[X]) ^ (k j₀ - 1) •
        (DirectSum.component ℂ[X] (Fin d) N j₀ (e p_aeval)) ≠ 0
      rw [← map_smul, show k j₀ - 1 = k j_max - 1 from by omega]
      exact hj₀_ne
    have hφp_unit : IsUnit (φ p) :=
      quotient_X_pow_isUnit_of_maxOrder (k j₀) (hk_j₀ ▸ hk_pos) (φ p) hφp_ne
    have hp_mem : p ∈ V'₀.prod W'₀ := by
      rw [Submodule.mem_prod]
      exact ⟨Submodule.zero_mem _, Submodule.subset_span ⟨0, by simp [p]⟩⟩
    have hXm_mem : ∀ m : ℕ, (X ^ m) p ∈ V'₀.prod W'₀ := by
      intro m; induction m with
      | zero => simpa using hp_mem
      | succ n ih =>
        have : (X ^ (n + 1)) p = X ((X ^ n) p) := by
          rw [pow_succ']; rfl
        rw [this]; exact hVW_inv _ ih
    have hφ_iter : ∀ m : ℕ, φ ((X ^ m) p) = (Polynomial.X : ℂ[X]) ^ m • φ p := by
      intro m; induction m with
      | zero => simp
      | succ n ih =>
        have : (X ^ (n + 1)) p = X ((X ^ n) p) := by
          rw [pow_succ']; rfl
        rw [this, hφ_comm, ih, smul_smul, pow_succ']
    -- Step A: φ ∘ aeval = polynomial action on φ(p)
    have hφ_aeval : ∀ f : ℂ[X], φ ((Polynomial.aeval X f) p) = f • φ p := by
      intro f
      change (DirectSum.component ℂ[X] (Fin d) N j₀)
        (e ((Module.AEval'.of (R := ℂ) X) ((Polynomial.aeval X f) p))) =
        f • (DirectSum.component ℂ[X] (Fin d) N j₀)
          (e ((Module.AEval'.of (R := ℂ) X) p))
      conv_lhs => rw [show (Module.AEval'.of (R := ℂ) X) ((Polynomial.aeval X f) p) =
          f • (Module.AEval'.of (R := ℂ) X) p from Module.AEval.of_aeval_smul ..]
      rw [map_smul, map_smul]
    -- Step B: aeval at X preserves V'₀.prod W'₀
    have haeval_mem : ∀ f : ℂ[X], (Polynomial.aeval X f) p ∈ V'₀.prod W'₀ := by
      intro f; induction f using Polynomial.induction_on' with
      | add f g hf hg => rw [map_add, LinearMap.add_apply]; exact Submodule.add_mem _ hf hg
      | monomial n c =>
        rw [Polynomial.aeval_monomial, Algebra.algebraMap_eq_smul_one, smul_mul_assoc,
          one_mul, LinearMap.smul_apply]
        exact Submodule.smul_mem _ _ (hXm_mem n)
    -- Step C: φ is surjective
    have hφ_surj : Function.Surjective φ := by
      intro a
      refine ⟨(Module.AEval'.of (R := ℂ) X).symm
        (e.symm ((DirectSum.lof ℂ[X] (Fin d) N j₀) a)), ?_⟩
      change (DirectSum.component ℂ[X] (Fin d) N j₀)
        (e ((Module.AEval'.of (R := ℂ) X)
          ((Module.AEval'.of (R := ℂ) X).symm
            (e.symm ((DirectSum.lof ℂ[X] (Fin d) N j₀) a))))) = a
      rw [LinearEquiv.apply_symm_apply, LinearEquiv.apply_symm_apply,
        DirectSum.component.lof_self]
    -- Step D: finrank(N j₀) = k j₀
    have hfr_N : Module.finrank ℂ (N j₀) = k j₀ := by
      change Module.finrank ℂ (ℂ[X] ⧸ (ℂ[X] ∙ (Polynomial.X : ℂ[X]) ^ k j₀)) = k j₀
      rw [show (ℂ[X] ∙ (Polynomial.X : ℂ[X]) ^ k j₀ : Submodule ℂ[X] ℂ[X]) =
          (Ideal.span {(Polynomial.X : ℂ[X]) ^ k j₀} : Ideal ℂ[X]) from
        (Ideal.submodule_span_eq).symm]
      rw [finrank_quotient_span_eq_natDegree, Polynomial.natDegree_pow,
        Polynomial.natDegree_X, mul_one]
    -- Step E: finrank(V'₀.prod W'₀) ≤ k j₀
    have hfr_le : Module.finrank ℂ ↥(V'₀.prod W'₀) ≤ k j₀ := by
      have hX_kill : ∀ m, k j₀ ≤ m → (X ^ m) p = 0 := by
        intro m hm
        have hm' : k j_max ≤ m := hk_j₀ ▸ hm
        calc (X ^ m) p = (X ^ (m - k j_max) * X ^ k j_max) p := by
              rw [← pow_add, Nat.sub_add_cancel hm']
            _ = (X ^ (m - k j_max)) ((X ^ k j_max) p) := by
              rw [Module.End.mul_apply]
            _ = 0 := by rw [hw1_kill, map_zero]
      classical
      set SF := Finset.univ.image (fun m : Fin (k j₀) => (X ^ (m : ℕ)) p)
      have h_le : V'₀.prod W'₀ ≤ Submodule.span ℂ (↑SF) := by
        intro ⟨v, w⟩ ⟨hv, hw⟩
        have hsum : (v, w) = (v, (0 : W)) + ((0 : V), w) := by ext <;> simp
        rw [hsum]; apply Submodule.add_mem
        -- (v, 0): V'₀ = span{B((AB)^m w₁)} → odd powers of X on p
        · have hmap : Submodule.map (LinearMap.inl ℂ V W) V'₀ ≤ Submodule.span ℂ (↑SF) := by
            rw [V'₀_def, Submodule.map_span]; apply Submodule.span_le.mpr
            rintro _ ⟨_, ⟨m, rfl⟩, rfl⟩
            change (B (((A.comp B) ^ m) w₁), (0 : W)) ∈ Submodule.span ℂ (↑SF)
            by_cases hm : 2 * m + 1 < k j₀
            · apply Submodule.subset_span; simp [SF]
              exact ⟨⟨2 * m + 1, hm⟩, swapOp_pow_odd_snd A B m w₁⟩
            · have hk := hX_kill (2 * m + 1) (by omega)
              rw [swapOp_pow_odd_snd A B m w₁, Prod.mk.injEq] at hk
              rw [hk.1]; exact Submodule.zero_mem _
          exact hmap ⟨v, hv, rfl⟩
        -- (0, w): W'₀ = span{(AB)^m w₁} → even powers of X on p
        · have hmap : Submodule.map (LinearMap.inr ℂ V W) W'₀ ≤ Submodule.span ℂ (↑SF) := by
            rw [W'₀_def, Submodule.map_span]; apply Submodule.span_le.mpr
            rintro _ ⟨_, ⟨m, rfl⟩, rfl⟩
            change ((0 : V), ((A.comp B) ^ m) w₁) ∈ Submodule.span ℂ (↑SF)
            by_cases hm : 2 * m < k j₀
            · apply Submodule.subset_span; simp [SF]
              exact ⟨⟨2 * m, hm⟩, swapOp_pow_even_snd A B m w₁⟩
            · have hk := hX_kill (2 * m) (by omega)
              rw [swapOp_pow_even_snd A B m w₁, Prod.mk.injEq] at hk
              rw [hk.2]; exact Submodule.zero_mem _
          exact hmap ⟨w, hw, rfl⟩
      have h1 : Module.finrank ℂ ↥(V'₀.prod W'₀)
          ≤ Module.finrank ℂ ↥(Submodule.span ℂ (↑SF : Set (V × W))) :=
        Submodule.finrank_mono h_le
      have h2 : Module.finrank ℂ ↥(Submodule.span ℂ (↑SF : Set (V × W))) ≤ SF.card :=
        finrank_span_finset_le_card SF
      have h3 : SF.card ≤ k j₀ := by
        exact le_trans Finset.card_image_le (le_of_eq (Finset.card_fin _))
      linarith
    -- Step F: Codisjoint
    have hcodisjoint : Codisjoint (V'₀.prod W'₀) C := by
      obtain ⟨u, hu⟩ := hφp_unit
      rw [codisjoint_iff, eq_top_iff]; intro q _
      obtain ⟨g, hg⟩ := Ideal.Quotient.mk_surjective (φ q * ↑u⁻¹ : N j₀)
      have hker : q - (Polynomial.aeval X g) p ∈ LinearMap.ker φ := by
        rw [LinearMap.mem_ker, map_sub, hφ_aeval]
        change φ q - (Ideal.Quotient.mk (ℂ[X] ∙ Polynomial.X ^ k j₀) g) * φ p = 0
        rw [hg, ← hu, mul_assoc,
          Units.inv_mul, mul_one, sub_self]
      have hq_decomp : q = (Polynomial.aeval X g) p + (q - (Polynomial.aeval X g) p) := by
        abel
      rw [hq_decomp]
      exact Submodule.add_mem_sup (haeval_mem g) hker
    -- Step G: Disjoint
    have hdisjoint : Disjoint (V'₀.prod W'₀) C := by
      have hfr_eq := Submodule.finrank_sup_add_finrank_inf_eq (V'₀.prod W'₀) C
      rw [hcodisjoint.eq_top, finrank_top] at hfr_eq
      have hfr_rn := LinearMap.finrank_range_add_finrank_ker φ
      rw [LinearMap.range_eq_top.mpr hφ_surj, finrank_top, hfr_N] at hfr_rn
      change k j₀ + Module.finrank ℂ ↥C = Module.finrank ℂ (V × W) at hfr_rn
      have hfr_inf : Module.finrank ℂ ↥(V'₀.prod W'₀ ⊓ C) = 0 := by omega
      rw [disjoint_iff]
      exact Submodule.finrank_eq_zero.mp hfr_inf
    have hcompl : IsCompl (V'₀.prod W'₀) C := ⟨hdisjoint, hcodisjoint⟩
    have hC_ne : C ≠ ⊥ := by
      intro hC_bot
      have hinj : Function.Injective φ := LinearMap.ker_eq_bot.mp hC_bot
      set gen : N j₀ := Submodule.Quotient.mk ((Polynomial.X : ℂ[X]) ^ (k j₀ - 1))
      haveI : Nontrivial (LinearMap.ker X) :=
        Module.finrank_pos_iff.mp (by linarith)
      obtain ⟨⟨w₀, hw₀_mem⟩, hw₀_ne⟩ := exists_ne (0 : LinearMap.ker X)
      have hw₀' : w₀ ≠ 0 := fun h => hw₀_ne (Subtype.ext h)
      have hw₀_ker : X w₀ = 0 := LinearMap.mem_ker.mp hw₀_mem
      have hXφw₀ : (Polynomial.X : ℂ[X]) • φ w₀ = 0 := by
        rw [← hφ_comm, hw₀_ker, map_zero]
      have hφw₀_ne : φ w₀ ≠ 0 := fun h => hw₀' (hinj (h.trans (map_zero φ).symm))
      have hφw₀_span := quotient_X_torsion_mem_span (k j₀) (φ w₀) hXφw₀
      rw [Submodule.mem_span_singleton] at hφw₀_span
      obtain ⟨c₀, hc₀⟩ := hφw₀_span
      have hc₀_ne : c₀ ≠ 0 := by intro h; rw [h, zero_smul] at hc₀; exact hφw₀_ne hc₀.symm
      suffices h_le : LinearMap.ker X ≤ Submodule.span ℂ ({w₀} : Set (V × W)) by
        have h1 := Submodule.finrank_mono h_le
        rw [finrank_span_singleton hw₀'] at h1
        linarith
      intro v hv
      have hv_ker : X v = 0 := LinearMap.mem_ker.mp hv
      have hXφv : (Polynomial.X : ℂ[X]) • φ v = 0 := by
        rw [← hφ_comm, hv_ker, map_zero]
      have hφv_span := quotient_X_torsion_mem_span (k j₀) (φ v) hXφv
      rw [Submodule.mem_span_singleton] at hφv_span
      obtain ⟨c, hc⟩ := hφv_span
      have hv_eq : v = (c * c₀⁻¹) • w₀ := by
        apply hinj; rw [map_smul]
        rw [show φ w₀ = c₀ • gen from hc₀.symm, smul_smul,
          mul_assoc, inv_mul_cancel₀ hc₀_ne, mul_one]
        exact hc.symm
      rw [hv_eq]; exact Submodule.smul_mem _ _ (Submodule.subset_span rfl)
    exact ⟨V'₀, W'₀, C, hcompl, hVW_inv, hC_inv, hVW_ne, hC_ne⟩

set_option maxHeartbeats 800000 in
/-- In the hard case (ker A ≤ range B, ker B ≤ range A), the swap operator X
on V × W provides a nontrivial compatible decomposition via the PID structure
theorem and compatible chain basis argument (Problem 6.9.1(c)). -/
private lemma compatible_product_decomp
    {V : Type*} [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V]
    {W : Type*} [AddCommGroup W] [Module ℂ W] [FiniteDimensional ℂ W]
    (A : V →ₗ[ℂ] W) (B : W →ₗ[ℂ] V)
    (hAB : IsNilpotent (A.comp B)) (hBA : IsNilpotent (B.comp A))
    (_h_kerA_le : LinearMap.ker A ≤ LinearMap.range B)
    (_h_kerB_le : LinearMap.ker B ≤ LinearMap.range A)
    (hker : 2 ≤ Module.finrank ℂ (LinearMap.ker A) +
              Module.finrank ℂ (LinearMap.ker B)) :
    ∃ (pV qV : Submodule ℂ V) (pW qW : Submodule ℂ W),
      IsCompl pV qV ∧ IsCompl pW qW ∧
      (∀ x ∈ pV, A x ∈ pW) ∧ (∀ x ∈ qV, A x ∈ qW) ∧
      (∀ x ∈ pW, B x ∈ pV) ∧ (∀ x ∈ qW, B x ∈ qV) ∧
      ¬(pV = ⊥ ∧ pW = ⊥) ∧ ¬(qV = ⊥ ∧ qW = ⊥) := by
  -- Step 1: Get an X-invariant product subspace with X-invariant complement
  obtain ⟨V', W', C, hcompl, hM_inv, hC_inv, hVW_ne, hC_ne⟩ :=
    exists_invariant_product_complement A B hAB hBA hker
  -- Step 2: Apply product_complement_decomp to extract compatible decompositions
  obtain ⟨qV, qW, hcV, hcW, hA_V', hA_qV, hB_W', hB_qV⟩ :=
    product_complement_decomp A B V' W' C hcompl hM_inv hC_inv
  -- Step 3: Package the result with nontriviality
  refine ⟨V', qV, W', qW, hcV, hcW, hA_V', hA_qV, hB_W', hB_qV, hVW_ne, ?_⟩
  -- qV = ⊥ ∧ qW = ⊥ would mean V' = ⊤ ∧ W' = ⊤, so V'.prod W' = ⊤, so C = ⊥
  intro ⟨hqV, hqW⟩
  apply hC_ne
  rw [hqV] at hcV; rw [hqW] at hcW
  have hV' : V' = ⊤ := by
    have h := hcV.sup_eq_top; simp  at h; exact h
  have hW' : W' = ⊤ := by
    have h := hcW.sup_eq_top; simp  at h; exact h
  have htop : V'.prod W' = ⊤ := by rw [hV', hW']; ext ⟨v, w⟩; simp
  have := hcompl.inf_eq_bot; rw [htop, top_inf_eq] at this; exact this

/-- A nilpotent composite with sufficiently large total kernel admits two nonzero complementary pairs of subspaces respected by both maps. -/
lemma exists_nontrivial_compatible_complements
    {V : Type*} [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V]
    {W : Type*} [AddCommGroup W] [Module ℂ W] [FiniteDimensional ℂ W]
    (A : V →ₗ[ℂ] W) (B : W →ₗ[ℂ] V)
    (_hAB : IsNilpotent (A.comp B))
    (hker : 2 ≤ Module.finrank ℂ (LinearMap.ker A) +
              Module.finrank ℂ (LinearMap.ker B)) :
    ∃ (pV qV : Submodule ℂ V) (pW qW : Submodule ℂ W),
      IsCompl pV qV ∧ IsCompl pW qW ∧
      (∀ x ∈ pV, A x ∈ pW) ∧ (∀ x ∈ qV, A x ∈ qW) ∧
      (∀ x ∈ pW, B x ∈ pV) ∧ (∀ x ∈ qW, B x ∈ qV) ∧
      ¬(pV = ⊥ ∧ pW = ⊥) ∧ ¬(qV = ⊥ ∧ qW = ⊥) := by
  -- Case split: is there v ∈ ker A \ range B or w ∈ ker B \ range A?
  by_cases h1 : ∃ v ∈ LinearMap.ker A, v ∉ LinearMap.range B
  · -- Easy case: v ∈ ker A, v ∉ range B
    obtain ⟨v₀, hv₀_ker, hv₀_not_range⟩ := h1
    have hv₀_ne : v₀ ≠ 0 := fun h => hv₀_not_range (h ▸ Submodule.zero_mem _)
    exact product_decomp_of_ker_A_not_range_B A B v₀ hv₀_ne
      (LinearMap.mem_ker.mp hv₀_ker) hv₀_not_range (by
        by_cases hW : 0 < Module.finrank ℂ W
        · exact Or.inl hW
        · right
          push Not at hW
          have : Module.finrank ℂ (LinearMap.ker B) = 0 :=
            le_antisymm (le_trans (Submodule.finrank_le _) (by omega)) (Nat.zero_le _)
          linarith)
  · push Not at h1
    -- h1 : ker A ≤ range B
    by_cases h2 : ∃ w ∈ LinearMap.ker B, w ∉ LinearMap.range A
    · -- Symmetric case: w ∈ ker B, w ∉ range A
      obtain ⟨w₀, hw₀_ker, hw₀_not_range⟩ := h2
      have hw₀_ne : w₀ ≠ 0 := fun h => hw₀_not_range (h ▸ Submodule.zero_mem _)
      -- Use the symmetric version with B and A swapped
      obtain ⟨pW, qW, pV, qV, hcW, hcV, hBpW, hBqW, hApV, hAqV, h1_ne, h2_ne⟩ :=
        product_decomp_of_ker_A_not_range_B B A w₀ hw₀_ne
          (LinearMap.mem_ker.mp hw₀_ker) hw₀_not_range (by
            by_cases hV : 0 < Module.finrank ℂ V
            · exact Or.inl hV
            · right
              push Not at hV
              have : Module.finrank ℂ (LinearMap.ker A) = 0 :=
                le_antisymm (le_trans (Submodule.finrank_le _) (by omega)) (Nat.zero_le _)
              linarith)
      refine ⟨pV, qV, pW, qW, hcV, hcW, hApV, hAqV, hBpW, hBqW, ?_, ?_⟩
      · intro ⟨hpV, hpW⟩; exact h1_ne ⟨hpW, hpV⟩
      · intro ⟨hqV, hqW⟩; exact h2_ne ⟨hqW, hqV⟩
    · push Not at h2
      -- Hard case: ker A ≤ range B AND ker B ≤ range A.
      -- Strategy: AB is nilpotent on W with dim(ker AB) ≥ 2,
      -- so nilpotent_nontrivial_decomp gives W = pW ⊕ qW both AB-invariant.
      -- Then construct V decomposition using B to transfer.
      -- Step 1: dim(ker(AB)) = dim(ker A) + dim(ker B) ≥ 2
      -- ker(AB) = comap B (ker A), and B⁻¹(ker A) splits as:
      -- dim = dim(ker B) + dim(ker A ∩ range B) = dim(ker B) + dim(ker A)
      -- Step 1: dim(ker(AB)) = dim(ker A) + dim(ker B) ≥ 2
      -- ker(AB) = comap B (ker A), and B⁻¹(ker A) decomposes via the short exact
      -- sequence: 0 → ker B → comap B (ker A) →B ker A → 0
      -- (surjectivity from ker A ≤ range B = map B ⊤ ⊇ map B (comap B (ker A)))
      have hAB_ker : 2 ≤ Module.finrank ℂ (LinearMap.ker (A.comp B)) := by
        rw [LinearMap.ker_comp]
        -- The restriction of B to S := comap B (ker A) has:
        -- - kernel = ker B (since ker B ≤ S)
        -- - range = ker A (since ker A ≤ range B)
        set S := Submodule.comap B (LinearMap.ker A)
        -- ker B ≤ S
        have hkerB_le : LinearMap.ker B ≤ S :=
          fun w hw => show B w ∈ LinearMap.ker A from by
            simp [LinearMap.mem_ker.mp hw]
        -- B maps S onto ker A ∩ range B = ker A
        have hBS : Submodule.map B S = LinearMap.ker A :=
          Submodule.map_comap_eq_self h1
        -- rank-nullity for the restriction of B to S:
        -- finrank S = finrank(map B S) + finrank(S ⊓ ker B)
        -- Since S ⊓ ker B = ker B (by hkerB_le):
        have hS_inf : S ⊓ LinearMap.ker B = LinearMap.ker B := inf_eq_right.mpr hkerB_le
        -- The restriction B|_S : S → V has range = ker A
        -- and kernel ≅ ker B
        -- dim(S) = dim(ker A) + dim(ker B)
        -- Approach: define the restriction explicitly and use rank-nullity
        set B_S := B.domRestrict S
        have hB_S_range : LinearMap.range B_S = LinearMap.ker A := by
          ext v; constructor
          · rintro ⟨⟨x, hx⟩, rfl⟩; exact hx
          · intro hv
            obtain ⟨x, rfl⟩ := h1 _ hv
            exact ⟨⟨x, hv⟩, rfl⟩
        have hB_S_ker : Module.finrank ℂ (LinearMap.ker B_S) =
            Module.finrank ℂ (LinearMap.ker B) := by
          have : LinearMap.ker B_S = (LinearMap.ker B).comap S.subtype := by
            ext ⟨x, _⟩; simp [B_S, LinearMap.domRestrict_apply]
          rw [this]
          exact (Submodule.comapSubtypeEquivOfLe hkerB_le).finrank_eq
        have hRN := B_S.finrank_range_add_finrank_ker
        rw [hB_S_range, hB_S_ker] at hRN
        -- finrank S = finrank(ker A) + finrank(ker B) ≥ 2
        linarith
      -- Step 2: Apply nilpotent_nontrivial_decomp to AB on W
      have hBA : IsNilpotent (B.comp A) := by
        obtain ⟨n, hn⟩ := _hAB
        exact ⟨n + 1, by ext v; simp only [LinearMap.zero_apply]
                         rw [pow_succ, Module.End.mul_apply, LinearMap.comp_apply]
                         have : ∀ (m : ℕ) (w : W),
                             ((B.comp A) ^ m) (B w) = B (((A.comp B) ^ m) w) := by
                           intro m; induction m with
                           | zero => intro w; simp
                           | succ m ih =>
                             intro w; rw [pow_succ, Module.End.mul_apply,
                               LinearMap.comp_apply, ih, pow_succ, Module.End.mul_apply,
                               ← LinearMap.comp_apply A B]
                         rw [this n (A v), LinearMap.congr_fun hn (A v),
                           LinearMap.zero_apply, map_zero]⟩
      have hBA_ker : 2 ≤ Module.finrank ℂ (LinearMap.ker (B.comp A)) := by
        rw [LinearMap.ker_comp]
        set S' := Submodule.comap A (LinearMap.ker B)
        have hkerA_le : LinearMap.ker A ≤ S' :=
          fun v hv => show A v ∈ LinearMap.ker B from by simp [LinearMap.mem_ker.mp hv]
        have hAS' : Submodule.map A S' = LinearMap.ker B :=
          Submodule.map_comap_eq_self h2
        set A_S' := A.domRestrict S'
        have hA_S'_range : LinearMap.range A_S' = LinearMap.ker B := by
          ext w; constructor
          · rintro ⟨⟨x, hx⟩, rfl⟩; exact hx
          · intro hw; obtain ⟨x, rfl⟩ := h2 _ hw; exact ⟨⟨x, hw⟩, rfl⟩
        have hA_S'_ker : Module.finrank ℂ (LinearMap.ker A_S') =
            Module.finrank ℂ (LinearMap.ker A) := by
          have : LinearMap.ker A_S' = (LinearMap.ker A).comap S'.subtype := by
            ext ⟨x, _⟩; simp [A_S', LinearMap.domRestrict_apply]
          rw [this]; exact (Submodule.comapSubtypeEquivOfLe hkerA_le).finrank_eq
        have hRN' := A_S'.finrank_range_add_finrank_ker
        rw [hA_S'_range, hA_S'_ker] at hRN'
        linarith
      -- Step 2: Construct the product-compatible decomposition
      -- using the swap operator X(v,w) = (Bw,Av) on V × W.
      exact compatible_product_decomp A B _hAB hBA h1 h2 hker

/-- If dim(ker A) + dim(ker B) ≥ 2 for a Q₂-rep with AB nilpotent and both dims > 0,
then the rep is decomposable. Uses `exists_nontrivial_compatible_complements` to construct
the nontrivial product-compatible decomposition contradicting indecomposability. -/
private lemma decomp_of_ker_sum_ge_two (ρ : FiniteDimensionalLinearMapPair ℂ)
    (hAB : IsNilpotent (ρ.leftToRight.comp ρ.rightToLeft))
    (_hV_pos : 0 < Module.finrank ℂ ρ.Left)
    (_hW_pos : 0 < Module.finrank ℂ ρ.Right)
    (hker : 2 ≤ Module.finrank ℂ (LinearMap.ker ρ.leftToRight) +
              Module.finrank ℂ (LinearMap.ker ρ.rightToLeft)) :
    ¬ρ.AuxiliaryCondition := by
  intro hρ
  -- Use exists_nontrivial_compatible_complements to get a nontrivial product-compatible
  -- decomposition, then derive contradiction with indecomposability.
  obtain ⟨pV, qV, pW, qW, hcV, hcW, hApV, hAqV, hBpW, hBqW, h1_ne, h2_ne⟩ :=
    exists_nontrivial_compatible_complements ρ.leftToRight ρ.rightToLeft hAB hker
  rcases hρ.2 pV qV pW qW hcV hcW hApV hAqV hBpW hBqW with h | h
  · exact h1_ne h
  · exact h2_ne h

/-- For indecomposable Q₂-reps with AB nilpotent and both dims > 0,
dim(ker A) + dim(ker B) ≤ 1. Combined with `ker_sum_ge_one`, gives sum = 1. -/
private lemma ker_sum_le_one (ρ : FiniteDimensionalLinearMapPair ℂ) (hρ : ρ.AuxiliaryCondition)
    (hAB : IsNilpotent (ρ.leftToRight.comp ρ.rightToLeft))
    (hV_pos : 0 < Module.finrank ℂ ρ.Left)
    (hW_pos : 0 < Module.finrank ℂ ρ.Right) :
    Module.finrank ℂ (LinearMap.ker ρ.leftToRight) + Module.finrank ℂ (LinearMap.ker ρ.rightToLeft) ≤ 1 := by
  by_contra h
  exact absurd hρ (decomp_of_ker_sum_ge_two ρ hAB hV_pos hW_pos (by omega))

private lemma ker_sum_eq_one (ρ : FiniteDimensionalLinearMapPair ℂ) (hρ : ρ.AuxiliaryCondition)
    (hAB : IsNilpotent (ρ.leftToRight.comp ρ.rightToLeft))
    (hV_pos : 0 < Module.finrank ℂ ρ.Left)
    (hW_pos : 0 < Module.finrank ℂ ρ.Right) :
    Module.finrank ℂ (LinearMap.ker ρ.leftToRight) + Module.finrank ℂ (LinearMap.ker ρ.rightToLeft) = 1 := by
  exact le_antisymm (ker_sum_le_one ρ hρ hAB hV_pos hW_pos) (ker_sum_ge_one ρ hAB hV_pos hW_pos)

/-- From `ker_sum_eq_one`: exactly one of A, B is injective and the other has
1-dimensional kernel. -/
private lemma exactly_one_injective (ρ : FiniteDimensionalLinearMapPair ℂ) (hρ : ρ.AuxiliaryCondition)
    (hAB : IsNilpotent (ρ.leftToRight.comp ρ.rightToLeft))
    (hV_pos : 0 < Module.finrank ℂ ρ.Left)
    (hW_pos : 0 < Module.finrank ℂ ρ.Right) :
    (LinearMap.ker ρ.leftToRight = ⊥ ∧ Module.finrank ℂ (LinearMap.ker ρ.rightToLeft) = 1) ∨
    (LinearMap.ker ρ.rightToLeft = ⊥ ∧ Module.finrank ℂ (LinearMap.ker ρ.leftToRight) = 1) := by
  have h := ker_sum_eq_one ρ hρ hAB hV_pos hW_pos
  rcases Nat.eq_zero_or_pos (Module.finrank ℂ (LinearMap.ker ρ.leftToRight)) with hA | hA
  · left
    exact ⟨Submodule.finrank_eq_zero.mp hA, by omega⟩
  · right
    have hB : Module.finrank ℂ (LinearMap.ker ρ.rightToLeft) = 0 := by omega
    exact ⟨Submodule.finrank_eq_zero.mp hB, by omega⟩

/-- Main nilpotent case: AB nilpotent + indecomposable + both dims > 0 → |dim V - dim W| ≤ 1.

Uses `exactly_one_injective` to get that exactly one of A, B is injective with the other
having 1-dimensional kernel, then derives the dimension bound via rank-nullity:
- If A injective (nullity B = 1): dim V = rank A ≤ dim W, and
  rank B = dim W - 1 ≤ dim V, so dim V ≤ dim W ≤ dim V + 1.
- If B injective (nullity A = 1): symmetric argument gives
  dim W ≤ dim V ≤ dim W + 1. -/
private theorem finrank_eq_or_eq_add_one_nilpotent (ρ : FiniteDimensionalLinearMapPair ℂ) (hρ : ρ.AuxiliaryCondition)
    (hAB : IsNilpotent (ρ.leftToRight.comp ρ.rightToLeft))
    (hV_pos : 0 < Module.finrank ℂ ρ.Left)
    (hW_pos : 0 < Module.finrank ℂ ρ.Right) :
    (Module.finrank ℂ ρ.Left = Module.finrank ℂ ρ.Right ∨
     Module.finrank ℂ ρ.Left = Module.finrank ℂ ρ.Right + 1 ∨
     Module.finrank ℂ ρ.Right = Module.finrank ℂ ρ.Left + 1) := by
  have hkA := ρ.ker_A_sub_range_B hρ hAB hV_pos hW_pos
  have hkB := ρ.ker_B_sub_range_A hρ hAB hV_pos hW_pos
  rcases exactly_one_injective ρ hρ hAB hV_pos hW_pos with ⟨hkA_bot, hkB_dim⟩ | ⟨hkB_bot, hkA_dim⟩
  · -- Case 1: A injective, nullity B = 1
    -- rank A = dim V (A injective), rank A ≤ dim W → dim V ≤ dim W
    have hV_le_W : Module.finrank ℂ ρ.Left ≤ Module.finrank ℂ ρ.Right := by
      have h_rA : Module.finrank ℂ (LinearMap.range ρ.leftToRight) = Module.finrank ℂ ρ.Left := by
        have := LinearMap.finrank_range_add_finrank_ker ρ.leftToRight
        rw [hkA_bot, finrank_bot] at this; omega
      calc Module.finrank ℂ ρ.Left
          = Module.finrank ℂ (LinearMap.range ρ.leftToRight) := h_rA.symm
        _ ≤ Module.finrank ℂ ρ.Right := Submodule.finrank_le _
    -- rank B ≤ dim V and rank B = dim W - 1 → dim W ≤ dim V + 1
    have hW_le_V1 : Module.finrank ℂ ρ.Right ≤ Module.finrank ℂ ρ.Left + 1 := by
      have h1 := LinearMap.finrank_range_add_finrank_ker ρ.rightToLeft
      have h2 : Module.finrank ℂ (LinearMap.range ρ.rightToLeft) ≤ Module.finrank ℂ ρ.Left :=
        Submodule.finrank_le _
      rw [hkB_dim] at h1; omega
    omega
  · -- Case 2: B injective, nullity A = 1 (symmetric)
    have hW_le_V : Module.finrank ℂ ρ.Right ≤ Module.finrank ℂ ρ.Left := by
      have h_rB : Module.finrank ℂ (LinearMap.range ρ.rightToLeft) = Module.finrank ℂ ρ.Right := by
        have := LinearMap.finrank_range_add_finrank_ker ρ.rightToLeft
        rw [hkB_bot, finrank_bot] at this; omega
      calc Module.finrank ℂ ρ.Right
          = Module.finrank ℂ (LinearMap.range ρ.rightToLeft) := h_rB.symm
        _ ≤ Module.finrank ℂ ρ.Left := Submodule.finrank_le _
    have hV_le_W1 : Module.finrank ℂ ρ.Left ≤ Module.finrank ℂ ρ.Right + 1 := by
      have h1 := LinearMap.finrank_range_add_finrank_ker ρ.leftToRight
      have h2 : Module.finrank ℂ (LinearMap.range ρ.leftToRight) ≤ Module.finrank ℂ ρ.Right :=
        Submodule.finrank_le _
      rw [hkA_dim] at h1; omega
    omega

/-- Under the auxiliary condition, the two component dimensions are equal or differ by one. -/
theorem finrank_eq_or_eq_add_one (ρ : FiniteDimensionalLinearMapPair ℂ) (hρ : ρ.AuxiliaryCondition) :
    -- The representation belongs to one of the four families (existential form):
    -- Either dim V = dim W (E_{n,λ} or E_{n,∞} family)
    -- or |dim V - dim W| = 1 (H_n or K_n family)
    (Module.finrank ℂ ρ.Left = Module.finrank ℂ ρ.Right ∨
     Module.finrank ℂ ρ.Left = Module.finrank ℂ ρ.Right + 1 ∨
     Module.finrank ℂ ρ.Right = Module.finrank ℂ ρ.Left + 1) := by
  by_cases hAB : IsNilpotent (ρ.leftToRight.comp ρ.rightToLeft)
  · -- Nilpotent case: AB nilpotent → |dim V - dim W| ≤ 1
    -- Tactic for showing all elements are zero when finrank = 0 over a field
    have allz_V : Module.finrank ℂ ρ.Left = 0 → ∀ x : ρ.Left, x = 0 := fun h0 x => by
      obtain ⟨c, hc, hcx⟩ := (Module.finrank_eq_zero_iff (R := ℂ) (M := ρ.Left)).mp h0 x
      exact (smul_eq_zero.mp hcx).resolve_left hc
    have allz_W : Module.finrank ℂ ρ.Right = 0 → ∀ x : ρ.Right, x = 0 := fun h0 x => by
      obtain ⟨c, hc, hcx⟩ := (Module.finrank_eq_zero_iff (R := ℂ) (M := ρ.Right)).mp h0 x
      exact (smul_eq_zero.mp hcx).resolve_left hc
    by_cases hV0 : Module.finrank ℂ ρ.Left = 0
    · -- dim V = 0: show dim W = 1
      right; right; rw [hV0, zero_add]
      have hW_pos : 0 < Module.finrank ℂ ρ.Right := by rcases hρ.1 with h | h <;> omega
      haveI hV_ss : Subsingleton ρ.Left :=
        ⟨fun a b => by rw [allz_V hV0 a, allz_V hV0 b]⟩
      by_contra hW_ne1
      have : Nontrivial ρ.Right := by
        by_contra h; rw [not_nontrivial_iff_subsingleton] at h
        exact absurd (Module.finrank_zero_of_subsingleton (R := ℂ) (M := ρ.Right)) (by omega)
      obtain ⟨w, hw⟩ := exists_ne (0 : ρ.Right)
      set pW := Submodule.span ℂ ({w} : Set ρ.Right)
      obtain ⟨qW, hcW⟩ := pW.exists_isCompl
      have hpW_ne : pW ≠ ⊥ := by
        intro h; apply hw
        have : w ∈ pW := Submodule.subset_span rfl
        rw [h] at this; simpa [Submodule.mem_bot] using this
      have hqW_ne : qW ≠ ⊥ := by
        intro h
        have h1 : Module.finrank ℂ ↥pW ≤ 1 :=
          (finrank_span_le_card ({w} : Set ρ.Right)).trans (by simp)
        have h2 : pW = ⊤ := eq_top_of_isCompl_bot (h ▸ hcW)
        rw [h2, finrank_top] at h1; omega
      rcases hρ.2 ⊥ ⊤ pW qW isCompl_bot_top hcW
        (fun x _ => by rw [allz_V hV0 x, map_zero]; exact zero_mem _)
        (fun x _ => by rw [allz_V hV0 x, map_zero]; exact zero_mem _)
        (fun x _ => by rw [allz_V hV0 (ρ.rightToLeft x)]; exact zero_mem _)
        (fun x _ => Submodule.mem_top) with ⟨_, h⟩ | ⟨_, h⟩
      · exact hpW_ne h
      · exact hqW_ne h
    · by_cases hW0 : Module.finrank ℂ ρ.Right = 0
      · -- dim W = 0: show dim V = 1 (symmetric)
        right; left; rw [hW0, zero_add]
        have hV_pos : 0 < Module.finrank ℂ ρ.Left := by rcases hρ.1 with h | h <;> omega
        haveI hW_ss : Subsingleton ρ.Right :=
          ⟨fun a b => by rw [allz_W hW0 a, allz_W hW0 b]⟩
        by_contra hV_ne1
        have : Nontrivial ρ.Left := by
          by_contra h; rw [not_nontrivial_iff_subsingleton] at h
          exact absurd (Module.finrank_zero_of_subsingleton (R := ℂ) (M := ρ.Left)) (by omega)
        obtain ⟨v, hv⟩ := exists_ne (0 : ρ.Left)
        set pV := Submodule.span ℂ ({v} : Set ρ.Left)
        obtain ⟨qV, hcV⟩ := pV.exists_isCompl
        have hpV_ne : pV ≠ ⊥ := by
          intro h; apply hv
          have : v ∈ pV := Submodule.subset_span rfl
          rw [h] at this; simpa [Submodule.mem_bot] using this
        have hqV_ne : qV ≠ ⊥ := by
          intro h
          have h1 : Module.finrank ℂ ↥pV ≤ 1 :=
            (finrank_span_le_card ({v} : Set ρ.Left)).trans (by simp)
          have h2 : pV = ⊤ := eq_top_of_isCompl_bot (h ▸ hcV)
          rw [h2, finrank_top] at h1; omega
        rcases hρ.2 pV qV ⊥ ⊤ hcV isCompl_bot_top
          (fun x _ => by rw [allz_W hW0 (ρ.leftToRight x)]; exact zero_mem _)
          (fun x _ => Submodule.mem_top)
          (fun x _ => by rw [allz_W hW0 x, map_zero]; exact zero_mem _)
          (fun x _ => by rw [allz_W hW0 x, map_zero]; exact zero_mem _) with ⟨h, _⟩ | ⟨h, _⟩
        · exact hpV_ne h
        · exact hqV_ne h
      · -- Both dims positive: main case
        exact finrank_eq_or_eq_add_one_nilpotent ρ hρ hAB
          (Nat.pos_of_ne_zero hV0) (Nat.pos_of_ne_zero hW0)
  · -- Non-nilpotent case: Fitting decomposition → dim V = dim W
    left
    -- Use Fitting decomposition directly
    set AB := ρ.leftToRight.comp ρ.rightToLeft
    set BA := ρ.rightToLeft.comp ρ.leftToRight
    set pW := ⨆ n, LinearMap.ker (AB ^ n)
    set qW := ⨅ n, LinearMap.range (AB ^ n)
    set pV := ⨆ n, LinearMap.ker (BA ^ n)
    set qV := ⨅ n, LinearMap.range (BA ^ n)
    have hcV := LinearMap.isCompl_iSup_ker_pow_iInf_range_pow BA
    have hcW := LinearMap.isCompl_iSup_ker_pow_iInf_range_pow AB
    -- Fitting compatibility (via shared lemmas)
    have hApV : ∀ x ∈ pV, ρ.leftToRight x ∈ pW := fun x hx => ρ.leftToRight_mem_iSup_ker_powers x hx
    have hAqV : ∀ x ∈ qV, ρ.leftToRight x ∈ qW := fun x hx => ρ.leftToRight_mem_iInf_range_powers x hx
    have hBpW : ∀ x ∈ pW, ρ.rightToLeft x ∈ pV := fun x hx => ρ.rightToLeft_mem_iSup_ker_powers x hx
    have hBqW : ∀ x ∈ qW, ρ.rightToLeft x ∈ qV := fun x hx => ρ.rightToLeft_mem_iInf_range_powers x hx
    -- qW ≠ ⊥ (since AB not nilpotent, the eventual range is nontrivial)
    have hqW_ne : qW ≠ ⊥ := by
      intro h
      apply hAB
      -- qW = ⊥ means pW = ⊤ (from IsCompl)
      have hpW_top : pW = ⊤ := eq_top_of_isCompl_bot (h ▸ hcW)
      -- pW = ⨆ ker(AB^n) = ⊤ means ker(AB^N) = ⊤ for some N (Noetherian stabilization)
      have h_sup_top : ⨆ n, LinearMap.ker (AB ^ n) = ⊤ := hpW_top
      obtain ⟨N, hN⟩ := Filter.Eventually.exists (LinearMap.eventually_iSup_ker_pow_eq AB)
      rw [h_sup_top] at hN
      exact ⟨N, LinearMap.ker_eq_top.mp hN.symm⟩
    -- By indecomposability
    rcases hρ.2 pV qV pW qW hcV hcW hApV hAqV hBpW hBqW with ⟨hpV, hpW⟩ | ⟨_, hqW⟩
    · -- pV = ⊥, pW = ⊥: qV = ⊤, qW = ⊤
      have hqV_top : qV = ⊤ := eq_top_of_bot_isCompl (hpV ▸ hcV)
      have hqW_top : qW = ⊤ := eq_top_of_bot_isCompl (hpW ▸ hcW)
      -- Dimension equality via injectivity (using shared Fitting injectivity lemmas)
      set A' : ↥qV →ₗ[ℂ] ↥qW :=
        (ρ.leftToRight.domRestrict qV).codRestrict qW (fun ⟨v, hv⟩ => hAqV v hv)
      set B' : ↥qW →ₗ[ℂ] ↥qV :=
        (ρ.rightToLeft.domRestrict qW).codRestrict qV (fun ⟨w, hw⟩ => hBqW w hw)
      have hA'_inj : Function.Injective A' := by
        intro ⟨v₁, hv₁⟩ ⟨v₂, hv₂⟩ h
        exact Subtype.ext (ρ.leftToRight_injectiveOn_iInf_range_powers hv₁ hv₂ (by
          simpa [A', LinearMap.codRestrict_apply, LinearMap.domRestrict_apply]
            using congr_arg Subtype.val h))
      have hB'_inj : Function.Injective B' := by
        intro ⟨w₁, hw₁⟩ ⟨w₂, hw₂⟩ h
        exact Subtype.ext (ρ.rightToLeft_injectiveOn_iInf_range_powers hw₁ hw₂ (by
          simpa [B', LinearMap.codRestrict_apply, LinearMap.domRestrict_apply]
            using congr_arg Subtype.val h))
      -- dim V = dim qV ≤ dim qW = dim W and vice versa
      apply le_antisymm
      · calc Module.finrank ℂ ρ.Left
            = Module.finrank ℂ ↥(⊤ : Submodule ℂ ρ.Left) := (finrank_top ℂ ρ.Left).symm
          _ = Module.finrank ℂ ↥qV := by rw [hqV_top]
          _ ≤ Module.finrank ℂ ↥qW := LinearMap.finrank_le_finrank_of_injective hA'_inj
          _ = Module.finrank ℂ ↥(⊤ : Submodule ℂ ρ.Right) := by rw [hqW_top]
          _ = Module.finrank ℂ ρ.Right := finrank_top ℂ ρ.Right
      · calc Module.finrank ℂ ρ.Right
            = Module.finrank ℂ ↥(⊤ : Submodule ℂ ρ.Right) := (finrank_top ℂ ρ.Right).symm
          _ = Module.finrank ℂ ↥qW := by rw [hqW_top]
          _ ≤ Module.finrank ℂ ↥qV := LinearMap.finrank_le_finrank_of_injective hB'_inj
          _ = Module.finrank ℂ ↥(⊤ : Submodule ℂ ρ.Left) := by rw [hqV_top]
          _ = Module.finrank ℂ ρ.Left := finrank_top ℂ ρ.Left
    · -- qW = ⊥: contradiction with AB not nilpotent
      exact absurd hqW hqW_ne

/-- Nilpotence of the composite on the second component implies nilpotence of the induced endomorphism on the product. -/
@[source_ref "Chapter6/Problem6.9.1" (role := supporting)]
theorem combinedEndomorphism_isNilpotent_of_comp_isNilpotent (ρ : FiniteDimensionalLinearMapPair ℂ)
    (hAB : IsNilpotent (ρ.leftToRight.comp ρ.rightToLeft)) :
    IsNilpotent ρ.combinedEndomorphism := by
  have hAB' := hAB
  obtain ⟨n, hn⟩ := hAB
  have hBA : IsNilpotent (ρ.rightToLeft.comp ρ.leftToRight) := by
    refine ⟨n + 1, ?_⟩
    have key : ∀ (m : ℕ) (w : ρ.Right),
        ((ρ.rightToLeft.comp ρ.leftToRight) ^ m) (ρ.rightToLeft w) = ρ.rightToLeft (((ρ.leftToRight.comp ρ.rightToLeft) ^ m) w) := by
      intro m; induction m with
      | zero => intro w; simp
      | succ m ih =>
        intro w
        rw [pow_succ, pow_succ, Module.End.mul_apply, LinearMap.comp_apply, ih,
            Module.End.mul_apply, ← LinearMap.comp_apply ρ.leftToRight ρ.rightToLeft]
    ext v
    simp only [LinearMap.zero_apply]
    rw [pow_succ, Module.End.mul_apply, LinearMap.comp_apply, key n (ρ.leftToRight v)]
    have := LinearMap.congr_fun hn (ρ.leftToRight v)
    simp only [LinearMap.zero_apply] at this
    rw [this, map_zero]
  simpa [FiniteDimensionalLinearMapPair.combinedEndomorphism] using swapOp_nilpotent ρ.leftToRight ρ.rightToLeft hAB' hBA

/-- For a nontrivial pair satisfying the auxiliary condition, nilpotence of the second composite forces the product endomorphism to have one-dimensional kernel. -/
theorem finrank_ker_combinedEndomorphism_eq_one (ρ : FiniteDimensionalLinearMapPair ℂ)
    (hρ : ρ.AuxiliaryCondition) (hAB : IsNilpotent (ρ.leftToRight.comp ρ.rightToLeft))
    (hV : 0 < Module.finrank ℂ ρ.Left) (hW : 0 < Module.finrank ℂ ρ.Right) :
    Module.finrank ℂ (LinearMap.ker ρ.combinedEndomorphism) = 1 := by
  rw [ρ.finrank_ker_combinedEndomorphism]
  exact ker_sum_eq_one ρ hρ hAB hV hW

end RepresentationTheory.FiniteDimensionalLinearMapPair
