/-
Copyright (c) 2026 mathlib-initiative. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: mathlib-initiative
-/

import Mathlib
import RepresentationTheory.GroupRepresentation.QuaternionGroup.ComplexIrreducibles
import RepresentationTheory.Alignment.Attribute

/-! # Auxiliary function submodule for the quaternion group -/

open QuaternionGroup Complex

namespace RepresentationTheory.QuaternionFunctionSubmodule


/-- A complex representation of the quaternion group on its complex-valued function space. -/
noncomputable def rightTranslationRepresentation :
    Representation ℂ (QuaternionGroup 2) (QuaternionGroup 2 → ℂ) where
  toFun g := LinearMap.funLeft ℂ ℂ (· * g)
  map_one' := by
    ext f x
    simp
  map_mul' g h := by
    ext f x
    simp [LinearMap.funLeft_apply, mul_assoc]

/-- The displayed representation acts on a function by right multiplication of its argument. -/
@[simp]
theorem rightTranslationRepresentation_apply (g : QuaternionGroup 2) (f : QuaternionGroup 2 → ℂ)
    (x : QuaternionGroup 2) : rightTranslationRepresentation g f x = f (x * g) := rfl


/-- An auxiliary complex submodule of functions on the quaternion group. -/
def auxiliaryFunctionSubmodule : Submodule ℂ (QuaternionGroup 2 → ℂ) where
  carrier := {f | ∀ g : QuaternionGroup 2, f (a 1 * g) = Complex.I * f g}
  add_mem' {f₁ f₂} hf₁ hf₂ := by
    intro g
    simp only [Pi.add_apply, hf₁ g, hf₂ g]
    ring
  zero_mem' := by
    intro g
    simp
  smul_mem' c f hf := by
    intro g
    simp only [Pi.smul_apply, smul_eq_mul, hf g]
    ring

/-- A complex function belongs to the auxiliary submodule exactly when left multiplication by `a 1` scales its values by the imaginary unit. -/
@[simp]
theorem mem_auxiliaryFunctionSubmodule_iff {f : QuaternionGroup 2 → ℂ} :
    f ∈ auxiliaryFunctionSubmodule ↔ ∀ g : QuaternionGroup 2, f (a 1 * g) = Complex.I * f g :=
  Iff.rfl


/-- The auxiliary function submodule is preserved by the displayed group representation. -/
@[source_ref "Chapter4/Exercise4.3.1" (role := supporting)]
theorem auxiliaryFunctionSubmodule_invariant (g : QuaternionGroup 2)
    (f : QuaternionGroup 2 → ℂ) (hf : f ∈ auxiliaryFunctionSubmodule) :
    rightTranslationRepresentation g f ∈ auxiliaryFunctionSubmodule := by
  rw [mem_auxiliaryFunctionSubmodule_iff]
  intro h
  change f (a 1 * h * g) = I * f (h * g)
  rw [mul_assoc]
  exact (mem_auxiliaryFunctionSubmodule_iff.mp hf) (h * g)


/-- Membership in the auxiliary submodule forces the displayed values at quaternion-group elements to differ by powers and signs of the imaginary unit. -/
theorem values_of_mem_auxiliaryFunctionSubmodule {f : QuaternionGroup 2 → ℂ} (hf : f ∈ auxiliaryFunctionSubmodule) :
    f (a 1) = I * f (a 0) ∧ f (a 2) = - f (a 0) ∧ f (a 3) = -I * f (a 0) ∧
      f (xa 3) = I * f (xa 0) ∧ f (xa 2) = - f (xa 0) ∧ f (xa 1) = -I * f (xa 0) := by
  have hf' := mem_auxiliaryFunctionSubmodule_iff.mp hf
  have e1 : f (a 1) = I * f (a 0) := by
    have := hf' (a 0); rwa [show a 1 * a 0 = a 1 from by decide] at this
  have e2 : f (a 2) = I * f (a 1) := by
    have := hf' (a 1); rwa [show a 1 * a 1 = a 2 from by decide] at this
  have e3 : f (a 3) = I * f (a 2) := by
    have := hf' (a 2); rwa [show a 1 * a 2 = a 3 from by decide] at this
  have x3 : f (xa 3) = I * f (xa 0) := by
    have := hf' (xa 0); rwa [show a 1 * xa 0 = xa 3 from by decide] at this
  have x2 : f (xa 2) = I * f (xa 3) := by
    have := hf' (xa 3); rwa [show a 1 * xa 3 = xa 2 from by decide] at this
  have x1 : f (xa 1) = I * f (xa 2) := by
    have := hf' (xa 2); rwa [show a 1 * xa 2 = xa 1 from by decide] at this
  refine ⟨e1, ?_, ?_, x3, ?_, ?_⟩
  · rw [e2, e1, ← mul_assoc, Complex.I_mul_I]; ring
  · rw [e3, e2, e1, ← mul_assoc, Complex.I_mul_I]; ring
  · rw [x2, x3, ← mul_assoc, Complex.I_mul_I]; ring
  · rw [x1, x2, x3, ← mul_assoc, Complex.I_mul_I]; ring


/-- A quaternion-group function constructed from two complex parameters. -/
noncomputable def quaternionFunctionOfValues (s t : ℂ) : QuaternionGroup 2 → ℂ
  | a i => if i = 0 then s else if i = 1 then I * s else if i = 2 then -s else -I * s
  | xa i => if i = 0 then t else if i = 1 then -I * t else if i = 2 then -t else I * t

/-- The constructed quaternion function takes its first parameter at `a 0`. -/
@[simp] theorem quaternionFunctionOfValues_a_zero (s t : ℂ) : quaternionFunctionOfValues s t (a 0) = s := rfl
/-- The constructed quaternion function takes the imaginary unit times its first parameter at `a 1`. -/
@[simp] theorem quaternionFunctionOfValues_a_one (s t : ℂ) : quaternionFunctionOfValues s t (a 1) = I * s := rfl
/-- The constructed quaternion function takes the negative of its first parameter at `a 2`. -/
@[simp] theorem quaternionFunctionOfValues_a_two (s t : ℂ) : quaternionFunctionOfValues s t (a 2) = -s := rfl
/-- The constructed quaternion function takes negative imaginary unit times its first parameter at `a 3`. -/
@[simp] theorem quaternionFunctionOfValues_a_three (s t : ℂ) : quaternionFunctionOfValues s t (a 3) = -I * s := rfl
/-- The constructed quaternion function takes its second parameter at `xa 0`. -/
@[simp] theorem quaternionFunctionOfValues_xa_zero (s t : ℂ) : quaternionFunctionOfValues s t (xa 0) = t := rfl
/-- The constructed quaternion function takes negative imaginary unit times its second parameter at `xa 1`. -/
@[simp] theorem quaternionFunctionOfValues_xa_one (s t : ℂ) : quaternionFunctionOfValues s t (xa 1) = -I * t := rfl
/-- The constructed quaternion function takes the negative of its second parameter at `xa 2`. -/
@[simp] theorem quaternionFunctionOfValues_xa_two (s t : ℂ) : quaternionFunctionOfValues s t (xa 2) = -t := rfl
/-- The constructed quaternion function takes the imaginary unit times its second parameter at `xa 3`. -/
@[simp] theorem quaternionFunctionOfValues_xa_three (s t : ℂ) : quaternionFunctionOfValues s t (xa 3) = I * t := rfl


/-- Every element of integers modulo four equals zero, one, two, or three. -/
theorem zmod_four_eq_zero_or_one_or_two_or_three (i : ZMod 4) : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 := by
  revert i; decide

/-- Every function constructed from two complex parameters belongs to the auxiliary submodule. -/
theorem quaternionFunctionOfValues_mem (s t : ℂ) : quaternionFunctionOfValues s t ∈ auxiliaryFunctionSubmodule := by
  rw [mem_auxiliaryFunctionSubmodule_iff]
  have p0 : (a 1 * a 0 : QuaternionGroup 2) = a 1 := by decide
  have p1 : (a 1 * a 1 : QuaternionGroup 2) = a 2 := by decide
  have p2 : (a 1 * a 2 : QuaternionGroup 2) = a 3 := by decide
  have p3 : (a 1 * a 3 : QuaternionGroup 2) = a 0 := by decide
  have q0 : (a 1 * xa 0 : QuaternionGroup 2) = xa 3 := by decide
  have q1 : (a 1 * xa 1 : QuaternionGroup 2) = xa 0 := by decide
  have q2 : (a 1 * xa 2 : QuaternionGroup 2) = xa 1 := by decide
  have q3 : (a 1 * xa 3 : QuaternionGroup 2) = xa 2 := by decide
  intro g
  rcases g with i | i <;> rcases zmod_four_eq_zero_or_one_or_two_or_three i with rfl | rfl | rfl | rfl <;>
    simp only [p0, p1, p2, p3, q0, q1, q2, q3,
      quaternionFunctionOfValues_a_zero, quaternionFunctionOfValues_a_one, quaternionFunctionOfValues_a_two, quaternionFunctionOfValues_a_three,
      quaternionFunctionOfValues_xa_zero, quaternionFunctionOfValues_xa_one, quaternionFunctionOfValues_xa_two, quaternionFunctionOfValues_xa_three] <;>
    norm_num [Complex.ext_iff]


/-- A function in the auxiliary submodule is determined by its values at the displayed two quaternion-group elements. -/
theorem eq_quaternionFunctionOfValues {f : QuaternionGroup 2 → ℂ} (hf : f ∈ auxiliaryFunctionSubmodule) :
    f = quaternionFunctionOfValues (f (a 0)) (f (xa 0)) := by
  obtain ⟨e1, e2, e3, x3, x2, x1⟩ := values_of_mem_auxiliaryFunctionSubmodule hf
  funext g
  rcases g with i | i <;> rcases zmod_four_eq_zero_or_one_or_two_or_three i with rfl | rfl | rfl | rfl <;>
    simp only [quaternionFunctionOfValues_a_zero, quaternionFunctionOfValues_a_one, quaternionFunctionOfValues_a_two, quaternionFunctionOfValues_a_three,
      quaternionFunctionOfValues_xa_zero, quaternionFunctionOfValues_xa_one, quaternionFunctionOfValues_xa_two, quaternionFunctionOfValues_xa_three] <;>
    first
      | rfl | (exact e1) | (exact e2) | (exact e3) | (exact x1) | (exact x2) | (exact x3)


/-- A complex-linear equivalence between the auxiliary function submodule and pairs of complex numbers. -/
noncomputable def auxiliarySubmoduleEquivFinTwo : auxiliaryFunctionSubmodule ≃ₗ[ℂ] (Fin 2 → ℂ) where
  toFun f := ![f.1 (a 0), f.1 (xa 0)]
  map_add' f g := by ext i; fin_cases i <;> simp
  map_smul' c f := by ext i; fin_cases i <;> simp
  invFun v := ⟨quaternionFunctionOfValues (v 0) (v 1), quaternionFunctionOfValues_mem _ _⟩
  left_inv f := by
    apply Subtype.ext
    simpa using (eq_quaternionFunctionOfValues f.2).symm
  right_inv v := by
    funext i; fin_cases i <;> rfl


/-- The auxiliary complex function submodule has dimension two. -/
@[source_ref "Chapter4/Exercise4.3.1" (role := supporting)]
theorem finrank_auxiliaryFunctionSubmodule :
    Module.finrank ℂ auxiliaryFunctionSubmodule = 2 := by
  rw [auxiliarySubmoduleEquivFinTwo.finrank_eq, Module.finrank_fin_fun]


/-- An invariant submodule contained in the auxiliary function submodule is either zero or the whole auxiliary submodule. -/
@[source_ref "Chapter4/Exercise4.3.1" (role := supporting)]
theorem invariant_submodule_eq_bot_or_auxiliaryFunctionSubmodule
    (U : Submodule ℂ (QuaternionGroup 2 → ℂ))
    (hUle : U ≤ auxiliaryFunctionSubmodule)
    (hUinv : ∀ g : QuaternionGroup 2, ∀ f ∈ U, rightTranslationRepresentation g f ∈ U) :
    U = ⊥ ∨ U = auxiliaryFunctionSubmodule := by
  rcases eq_or_ne U ⊥ with h | h
  · exact Or.inl h
  refine Or.inr ?_
  -- pick a nonzero `f ∈ U`
  obtain ⟨f, hfU, hf0⟩ := (Submodule.ne_bot_iff U).mp h
  have hfcov : f ∈ auxiliaryFunctionSubmodule := hUle hfU
  obtain ⟨e1, e2, _e3, _x3, _x2, x1⟩ := values_of_mem_auxiliaryFunctionSubmodule hfcov
  set s := f (a 0) with hs
  set t := f (xa 0) with ht
  -- if both free values vanish, `f = 0`, contradiction
  have hnot : ¬ (s = 0 ∧ t = 0) := by
    rintro ⟨hs0, ht0⟩
    apply hf0
    rw [eq_quaternionFunctionOfValues hfcov, ← hs, ← ht, hs0, ht0]
    funext g
    rcases g with i | i <;> rcases zmod_four_eq_zero_or_one_or_two_or_three i with rfl | rfl | rfl | rfl <;>
      simp only [quaternionFunctionOfValues_a_zero, quaternionFunctionOfValues_a_one, quaternionFunctionOfValues_a_two, quaternionFunctionOfValues_a_three,
        quaternionFunctionOfValues_xa_zero, quaternionFunctionOfValues_xa_one, quaternionFunctionOfValues_xa_two, quaternionFunctionOfValues_xa_three, Pi.zero_apply,
        mul_zero, neg_zero]
  -- A `2 × 2` nonzero determinant of coordinates gives an independent pair inside `U`.
  have indep_in_U : ∀ {x y : QuaternionGroup 2 → ℂ} (hx : x ∈ U) (hy : y ∈ U),
      x (a 0) * y (xa 0) - x (xa 0) * y (a 0) ≠ 0 →
      LinearIndependent ℂ ![(⟨x, hx⟩ : U), ⟨y, hy⟩] := by
    intro x y hx hy hdet
    rw [LinearIndependent.pair_iff]
    intro α β hab
    have E0 := congrArg (fun z : U => (z : QuaternionGroup 2 → ℂ) (a 0)) hab
    have E1 := congrArg (fun z : U => (z : QuaternionGroup 2 → ℂ) (xa 0)) hab
    simp only [Submodule.coe_add, Submodule.coe_smul, Pi.add_apply, Pi.smul_apply,
      smul_eq_mul, ZeroMemClass.coe_zero, Pi.zero_apply] at E0 E1
    -- E0 : α * x (a 0) + β * y (a 0) = 0 ; E1 : α * x (xa 0) + β * y (xa 0) = 0
    have hα : α * (x (a 0) * y (xa 0) - x (xa 0) * y (a 0)) = 0 := by
      linear_combination y (xa 0) * E0 - y (a 0) * E1
    have hβ : β * (x (a 0) * y (xa 0) - x (xa 0) * y (a 0)) = 0 := by
      linear_combination x (a 0) * E1 - x (xa 0) * E0
    exact ⟨(mul_eq_zero.mp hα).resolve_right hdet, (mul_eq_zero.mp hβ).resolve_right hdet⟩
  -- upgrade to `finrank U ≥ 2`, forcing `U = auxiliaryFunctionSubmodule`
  refine Submodule.eq_of_le_of_finrank_le hUle ?_
  rw [finrank_auxiliaryFunctionSubmodule]
  -- exhibit two linearly independent members of `U`
  by_cases hst : s = 0 ∨ t = 0
  · -- use `y := rightTranslationRepresentation (xa 0) f`, coordinates `(t, -s)`; det `= -(s² + t²)`
    have hhU : rightTranslationRepresentation (xa 0) f ∈ U := hUinv (xa 0) f hfU
    have hdet : f (a 0) * (rightTranslationRepresentation (xa 0) f) (xa 0)
        - f (xa 0) * (rightTranslationRepresentation (xa 0) f) (a 0) ≠ 0 := by
      rw [rightTranslationRepresentation_apply, rightTranslationRepresentation_apply, show xa 0 * xa 0 = a 2 from by decide,
        show a 0 * xa 0 = xa 0 from by decide, e2, ← hs, ← ht]
      rcases hst with h0 | h0
      · rw [h0]
        have ht0 : t ≠ 0 := fun hc => hnot ⟨h0, hc⟩
        simp only [neg_zero, mul_zero, zero_sub, neg_ne_zero]
        exact mul_ne_zero ht0 ht0
      · rw [h0]
        have hs0 : s ≠ 0 := fun hc => hnot ⟨hc, h0⟩
        simp only [mul_zero, sub_zero, mul_neg, neg_ne_zero]
        exact mul_ne_zero hs0 hs0
    have := (indep_in_U hfU hhU hdet).fintype_card_le_finrank
    simpa using this
  · -- both `s ≠ 0` and `t ≠ 0`: use `y := rightTranslationRepresentation (a 1) f`; det `= -2 I s t`
    rw [not_or] at hst
    obtain ⟨hs0, ht0⟩ := hst
    have hhU : rightTranslationRepresentation (a 1) f ∈ U := hUinv (a 1) f hfU
    have hdet : f (a 0) * (rightTranslationRepresentation (a 1) f) (xa 0)
        - f (xa 0) * (rightTranslationRepresentation (a 1) f) (a 0) ≠ 0 := by
      rw [rightTranslationRepresentation_apply, rightTranslationRepresentation_apply, show xa 0 * a 1 = xa 1 from by decide,
        show a 0 * a 1 = a 1 from by decide, e1, x1, ← hs, ← ht]
      have hne : s * (-I * t) - t * (I * s) = -(2 * I * (s * t)) := by ring
      rw [hne, neg_ne_zero]
      exact mul_ne_zero (mul_ne_zero (by norm_num) Complex.I_ne_zero) (mul_ne_zero hs0 ht0)
    have := (indep_in_U hfU hhU hdet).fintype_card_le_finrank
    simpa using this

end RepresentationTheory.QuaternionFunctionSubmodule

