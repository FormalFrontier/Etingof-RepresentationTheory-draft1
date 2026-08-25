/-
Copyright (c) 2026 mathlib-initiative. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: mathlib-initiative
-/

import Mathlib.Analysis.SpecialFunctions.Exponential
import Mathlib.Analysis.Normed.Algebra.Exponential
import Mathlib.Analysis.ODE.ExistUnique
import Mathlib.Analysis.Calculus.Deriv.Mul
import RepresentationTheory.Alignment.Attribute

/-!
# Exponentials of continuous derivations
-/

open NormedSpace

namespace RepresentationTheory.Analysis.Algebra.DerivationExponential

variable {A : Type*} [NormedRing A] [NormedAlgebra ℝ A] [FiniteDimensional ℝ A]

omit [FiniteDimensional ℝ A] in
/-- The derivative at zero of a differentiable curve of multiplicative linear maps starting at the identity satisfies the Leibniz rule. -/
@[source_ref "Chapter2/Remark2.9.4" (role := primary)]
theorem derivation_of_hasDerivAt_multiplicativeCurve (g : ℝ → (A →L[ℝ] A)) (D : A →L[ℝ] A)
    (hmul : ∀ t (x y : A), g t (x * y) = g t x * g t y) (hg0 : g 0 = 1)
    (hderiv : HasDerivAt g D 0) (x y : A) :
    D (x * y) = D x * y + x * D y := by
  have hxy : HasDerivAt (fun t => g t (x * y)) (D (x * y)) 0 := by
    simpa using hderiv.clm_apply (hasDerivAt_const (0 : ℝ) (x * y))
  have hx : HasDerivAt (fun t => g t x) (D x) 0 := by
    simpa using hderiv.clm_apply (hasDerivAt_const (0 : ℝ) x)
  have hy : HasDerivAt (fun t => g t y) (D y) 0 := by
    simpa using hderiv.clm_apply (hasDerivAt_const (0 : ℝ) y)
  have hprod : HasDerivAt ((fun t => g t x) * fun t => g t y) (D x * y + x * D y) 0 := by
    simpa [hg0] using hx.mul hy
  have hfun : (fun t => g t (x * y)) = ((fun t => g t x) * fun t => g t y) :=
    funext fun t => hmul t x y
  rw [hfun] at hxy
  exact hxy.unique hprod

variable (D : A →L[ℝ] A)

private theorem hasDerivAt_exp_smul_apply (a : A) (s : ℝ) :
    HasDerivAt (fun s => exp (s • D) a) (D (exp (s • D) a)) s := by
  simpa [mul_apply_eq_comp] using
    (hasDerivAt_exp_smul_const' D s).clm_apply (hasDerivAt_const s a)

omit [FiniteDimensional ℝ A] in
/-- The exponential of the zero scalar multiple of a continuous linear map is the identity. -/
@[source_ref "Chapter2/Remark2.9.4" (role := supporting)]
theorem exp_zero_smul : exp ((0 : ℝ) • D) = 1 := by
  rw [zero_smul ℝ D, exp_zero]

/-- Successive application of two scaled exponentials agrees with applying the exponential scaled by the sum. -/
theorem exp_smul_comp_apply (s t : ℝ) (a : A) :
    exp (s • D) (exp (t • D) a) = exp ((s + t) • D) a := by
  set c := exp (t • D) a with hc
  have hu : ∀ r, HasDerivAt (fun r => exp (r • D) c) (D (exp (r • D) c)) r :=
    fun r => hasDerivAt_exp_smul_apply D c r
  have hw : ∀ r, HasDerivAt (fun r => exp ((r + t) • D) a) (D (exp ((r + t) • D) a)) r := by
    intro r
    have h2 : HasDerivAt (fun r : ℝ => r + t) 1 r := (hasDerivAt_id r).add_const t
    have hchain := (hasDerivAt_exp_smul_const' D (r + t)).scomp r h2
    simpa [Function.comp, mul_apply_eq_comp] using hchain.clm_apply (hasDerivAt_const r a)
  have hinit : exp ((0 : ℝ) • D) c = exp ((0 + t) • D) a := by
    rw [exp_zero_smul D]
    simp [hc]
  have huniq : (fun r => exp (r • D) c) = fun r => exp ((r + t) • D) a :=
    ODE_solution_unique_univ (t₀ := (0 : ℝ)) (K := ‖D‖₊) (s := fun _ => Set.univ)
      (fun _ => (D.lipschitz).lipschitzOnWith)
      (fun r => ⟨hu r, Set.mem_univ _⟩)
      (fun r => ⟨hw r, Set.mem_univ _⟩)
      hinit
  simpa [hc] using congrFun huniq s

/-- Exponentials of two scalar multiples of the same continuous linear map multiply to the exponential of the sum of the scalars. -/
@[source_ref "Chapter2/Remark2.9.4" (role := supporting)]
theorem exp_add_smul (s t : ℝ) : exp ((s + t) • D) = exp (s • D) * exp (t • D) :=
  ContinuousLinearMap.ext fun a => by
    rw [mul_apply_eq_comp]; exact (exp_smul_comp_apply D s t a).symm

variable (hD : ∀ x y : A, D (x * y) = D x * y + x * D y)

include hD in
/-- The exponential of a scaled derivation preserves multiplication. -/
@[source_ref "Chapter2/Remark2.9.4" (role := supporting)]
theorem exp_smul_map_mul (t : ℝ) (a b : A) :
    exp (t • D) (a * b) = exp (t • D) a * exp (t • D) b := by
  set u : ℝ → A := fun s => exp (s • D) (a * b) with hu_def
  set v : ℝ → A := fun s => exp (s • D) a * exp (s • D) b with hv_def
  have hu : ∀ s, HasDerivAt u (D (u s)) s := fun s => hasDerivAt_exp_smul_apply D (a * b) s
  have hv : ∀ s, HasDerivAt v (D (v s)) s := by
    intro s
    have hmul := (hasDerivAt_exp_smul_apply D a s).mul (hasDerivAt_exp_smul_apply D b s)
    have hvs : D (v s) = D (exp (s • D) a) * exp (s • D) b + exp (s • D) a * D (exp (s • D) b) :=
      hD (exp (s • D) a) (exp (s • D) b)
    rw [hvs]
    exact hmul
  have hinit : u 0 = v 0 := by
    simp only [u, v]
    rw [exp_zero_smul D]
    rfl
  have huniq : u = v :=
    ODE_solution_unique_univ (t₀ := (0 : ℝ)) (K := ‖D‖₊) (s := fun _ => Set.univ)
      (fun _ => (D.lipschitz).lipschitzOnWith)
      (fun s => ⟨hu s, Set.mem_univ _⟩)
      (fun s => ⟨hv s, Set.mem_univ _⟩)
      hinit
  simpa [u, v] using congrFun huniq t

include hD in
omit [FiniteDimensional ℝ A] in
/-- A continuous linear map satisfying the Leibniz rule sends the multiplicative identity to zero. -/
theorem derivation_apply_one : D 1 = 0 := by
  have h : D 1 = D 1 + D 1 := by simpa using hD 1 1
  have h' : D 1 + 0 = D 1 + D 1 := by rwa [add_zero]
  exact (add_left_cancel h').symm

include hD in
/-- The exponential of a scaled derivation fixes the multiplicative identity. -/
@[source_ref "Chapter2/Remark2.9.4" (role := supporting)]
theorem exp_smul_apply_one (t : ℝ) : exp (t • D) 1 = 1 := by
  set u : ℝ → A := fun s => exp (s • D) 1 with hu_def
  have hu : ∀ s, HasDerivAt u (D (u s)) s := fun s => hasDerivAt_exp_smul_apply D 1 s
  have hc : ∀ s, HasDerivAt (fun _ : ℝ => (1 : A)) (D ((fun _ : ℝ => (1 : A)) s)) s := by
    intro s
    simpa [derivation_apply_one D hD] using hasDerivAt_const s (1 : A)
  have hinit : u 0 = (fun _ : ℝ => (1 : A)) 0 := by
    simp only [u]
    rw [exp_zero_smul D]
    rfl
  have huniq : u = fun _ : ℝ => (1 : A) :=
    ODE_solution_unique_univ (t₀ := (0 : ℝ)) (K := ‖D‖₊) (s := fun _ => Set.univ)
      (fun _ => (D.lipschitz).lipschitzOnWith)
      (fun s => ⟨hu s, Set.mem_univ _⟩)
      (fun s => ⟨hc s, Set.mem_univ _⟩)
      hinit
  simpa [u] using congrFun huniq t

include hD in
/-- The one-parameter family of algebra automorphisms obtained by exponentiating a continuous derivation of a finite-dimensional real normed algebra. -/
@[source_ref "Chapter2/Remark2.9.4" (role := supporting)]
noncomputable def derivationExponentialEquiv (t : ℝ) : A ≃ₐ[ℝ] A where
  toFun a := exp (t • D) a
  invFun a := exp ((-t) • D) a
  left_inv a := by
    have h := exp_smul_comp_apply D (-t) t a
    rw [neg_add_cancel, exp_zero_smul] at h
    simpa using h
  right_inv a := by
    have h := exp_smul_comp_apply D t (-t) a
    rw [add_neg_cancel, exp_zero_smul] at h
    simpa using h
  map_mul' a b := exp_smul_map_mul D hD t a b
  map_add' a b := map_add (exp (t • D)) a b
  commutes' r := by
    rw [Algebra.algebraMap_eq_smul_one, map_smul, exp_smul_apply_one D hD t]

/-- The algebra automorphism defined by a derivation acts as the exponential of the scaled continuous linear map. -/
@[simp]
theorem derivationExponentialEquiv_apply (t : ℝ) (a : A) :
    derivationExponentialEquiv D hD t a = exp (t • D) a := rfl

end RepresentationTheory.Analysis.Algebra.DerivationExponential
