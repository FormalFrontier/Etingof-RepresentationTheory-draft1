import Mathlib.Analysis.SpecialFunctions.Exponential
import Mathlib.Analysis.Normed.Algebra.Exponential
import Mathlib.Analysis.ODE.ExistUnique
import Mathlib.Analysis.Calculus.Deriv.Mul

/-!
# Remark 2.9.4: derivations are the infinitesimal version of automorphisms

Etingof's Remark 2.9.4 motivates Lie algebras by observing that derivations are the
"infinitesimal version" of automorphisms of an associative algebra. Two claims are left to the
reader:

* (**check it!**) if `g t` is a differentiable family of automorphisms of a finite-dimensional
  algebra `A` over `ℝ` or `ℂ` with `g 0 = id`, then `D := g'(0)` is a derivation, i.e. it satisfies
  the Leibniz rule `D (x * y) = D x * y + x * D y`;
* (**give a proof!**) conversely, if `D` is a derivation then `t ↦ exp (t • D)` is a one-parameter
  family of automorphisms.

We formalize both. Following the book, the parameter `t` ranges over `ℝ` (a "one-parameter"
family). We work over `ℝ`; the statements and proofs hold verbatim over `ℂ` (any `RCLike` field),
a complex algebra being in particular a real one.

## Main statements

* `Etingof.Remark2_9_4.hasDerivAt_leibniz`: the derivative at `0` of a differentiable family of
  algebra homomorphisms with `g 0 = 1` satisfies the Leibniz rule — so `g'(0)` is a derivation.
* `Etingof.Remark2_9_4.expDeriv_apply_apply`: the pointwise one-parameter group law
  `exp (s • D) (exp (t • D) a) = exp ((s + t) • D) a`, with corollary `expDeriv_add` at the operator
  level and `expDeriv_zero` for the identity at `t = 0`.
* `Etingof.Remark2_9_4.expDeriv_map_mul` / `expDeriv_map_one`: for a derivation `D`, each operator
  `exp (t • D)` is multiplicative and unital, hence an algebra homomorphism.
* `Etingof.Remark2_9_4.expDerivAut`: the resulting algebra automorphism `A ≃ₐ[ℝ] A`, with inverse
  `exp (-t • D)`; together with `expDeriv_zero`/`expDeriv_add` this is the promised one-parameter
  family of automorphisms.

## Implementation notes

The converse direction avoids the operator identity `exp (x + y) = exp x * exp y`, which in Mathlib
requires a `NormedAlgebra ℚ` structure unavailable on the operator algebra `A →L[ℝ] A`. Instead
everything is obtained from uniqueness of solutions of the linear ODE `w' = D ∘ w`
(`ODE_solution_unique_univ`): the relevant curves `s ↦ exp (s • D) x` all solve it, their
derivative being computed from `hasDerivAt_exp_smul_const'`, and their initial values determine
them. Multiplicativity, unitality and the group law each compare two such curves.
-/

open NormedSpace

namespace Etingof.Remark2_9_4

variable {A : Type*} [NormedRing A] [NormedAlgebra ℝ A] [FiniteDimensional ℝ A]

/-! ## The forward direction: `g'(0)` is a derivation -/

omit [FiniteDimensional ℝ A] in
/-- **Etingof Remark 2.9.4 (check it!).** If `g : ℝ → (A →L[ℝ] A)` is a family of algebra
homomorphisms (`g t` is multiplicative) with `g 0 = id`, differentiable at `0` with derivative `D`,
then `D` satisfies the Leibniz rule and so is a derivation. Only the value and derivative of `g` at
`0` are used, so the "automorphism" (bijectivity) hypothesis is not needed for this direction. -/
theorem hasDerivAt_leibniz (g : ℝ → (A →L[ℝ] A)) (D : A →L[ℝ] A)
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

/-! ## The converse direction: `exp (t • D)` is a one-parameter family of automorphisms -/

variable (D : A →L[ℝ] A)

/-- For a derivation `D`, the curve `s ↦ exp (s • D) a` has derivative `D (exp (s • D) a)`: the
building block for every ODE-uniqueness argument below. -/
private theorem hasDerivAt_expDeriv_apply (a : A) (s : ℝ) :
    HasDerivAt (fun s => exp (s • D) a) (D (exp (s • D) a)) s := by
  simpa [mul_apply_eq_comp] using
    (hasDerivAt_exp_smul_const' D s).clm_apply (hasDerivAt_const s a)

omit [FiniteDimensional ℝ A] in
/-- `exp (0 • D) = 1`: the family passes through the identity at `t = 0`. -/
theorem expDeriv_zero : exp ((0 : ℝ) • D) = 1 := by
  rw [zero_smul ℝ D, exp_zero]

/-- **Pointwise one-parameter group law.** `exp (s • D) (exp (t • D) a) = exp ((s + t) • D) a`.
Both `r ↦ exp (r • D) (exp (t • D) a)` and `r ↦ exp ((r + t) • D) a` solve `w' = D ∘ w` with the
same value at `r = 0`, so they agree; evaluating at `r = s` gives the claim. -/
theorem expDeriv_apply_apply (s t : ℝ) (a : A) :
    exp (s • D) (exp (t • D) a) = exp ((s + t) • D) a := by
  set c := exp (t • D) a with hc
  have hu : ∀ r, HasDerivAt (fun r => exp (r • D) c) (D (exp (r • D) c)) r :=
    fun r => hasDerivAt_expDeriv_apply D c r
  have hw : ∀ r, HasDerivAt (fun r => exp ((r + t) • D) a) (D (exp ((r + t) • D) a)) r := by
    intro r
    have h2 : HasDerivAt (fun r : ℝ => r + t) 1 r := (hasDerivAt_id r).add_const t
    have hchain := (hasDerivAt_exp_smul_const' D (r + t)).scomp r h2
    simpa [Function.comp, mul_apply_eq_comp] using hchain.clm_apply (hasDerivAt_const r a)
  have hinit : exp ((0 : ℝ) • D) c = exp ((0 + t) • D) a := by simp [hc]
  have huniq : (fun r => exp (r • D) c) = fun r => exp ((r + t) • D) a :=
    ODE_solution_unique_univ (t₀ := (0 : ℝ)) (K := ‖D‖₊) (s := fun _ => Set.univ)
      (fun _ => (D.lipschitz).lipschitzOnWith)
      (fun r => ⟨hu r, Set.mem_univ _⟩)
      (fun r => ⟨hw r, Set.mem_univ _⟩)
      hinit
  simpa [hc] using congrFun huniq s

/-- The one-parameter group law at the operator level:
`exp ((s + t) • D) = exp (s • D) * exp (t • D)`. -/
theorem expDeriv_add (s t : ℝ) : exp ((s + t) • D) = exp (s • D) * exp (t • D) :=
  ContinuousLinearMap.ext fun a => by
    rw [mul_apply_eq_comp]; exact (expDeriv_apply_apply D s t a).symm

variable (hD : ∀ x y : A, D (x * y) = D x * y + x * D y)

include hD in
/-- **Etingof Remark 2.9.4 (give a proof!), multiplicativity.** For a derivation `D`, the operator
`exp (t • D)` is multiplicative: `exp (t • D) (a * b) = exp (t • D) a * exp (t • D) b`.

Proof: `s ↦ exp (s • D) (a * b)` and `s ↦ exp (s • D) a * exp (s • D) b` both solve `w' = D ∘ w`
with initial value `a * b` (for the second curve, the Leibniz rule `hD` is exactly what makes its
derivative equal `D` of the product). By ODE uniqueness they coincide; evaluating at `t` gives the
claim. -/
theorem expDeriv_map_mul (t : ℝ) (a b : A) :
    exp (t • D) (a * b) = exp (t • D) a * exp (t • D) b := by
  set u : ℝ → A := fun s => exp (s • D) (a * b) with hu_def
  set v : ℝ → A := fun s => exp (s • D) a * exp (s • D) b with hv_def
  have hu : ∀ s, HasDerivAt u (D (u s)) s := fun s => hasDerivAt_expDeriv_apply D (a * b) s
  have hv : ∀ s, HasDerivAt v (D (v s)) s := by
    intro s
    have hmul := (hasDerivAt_expDeriv_apply D a s).mul (hasDerivAt_expDeriv_apply D b s)
    have hvs : D (v s) = D (exp (s • D) a) * exp (s • D) b + exp (s • D) a * D (exp (s • D) b) :=
      hD (exp (s • D) a) (exp (s • D) b)
    rw [hvs]
    exact hmul
  have hinit : u 0 = v 0 := by simp [u, v]
  have huniq : u = v :=
    ODE_solution_unique_univ (t₀ := (0 : ℝ)) (K := ‖D‖₊) (s := fun _ => Set.univ)
      (fun _ => (D.lipschitz).lipschitzOnWith)
      (fun s => ⟨hu s, Set.mem_univ _⟩)
      (fun s => ⟨hv s, Set.mem_univ _⟩)
      hinit
  simpa [u, v] using congrFun huniq t

include hD in
omit [FiniteDimensional ℝ A] in
/-- A derivation kills the unit: `D 1 = 0`. -/
theorem map_one_eq_zero : D 1 = 0 := by
  have h : D 1 = D 1 + D 1 := by simpa using hD 1 1
  have h' : D 1 + 0 = D 1 + D 1 := by rwa [add_zero]
  exact (add_left_cancel h').symm

include hD in
/-- **Etingof Remark 2.9.4 (give a proof!), unitality.** For a derivation `D`, the operator
`exp (t • D)` fixes the unit: `exp (t • D) 1 = 1`.

Proof: `s ↦ exp (s • D) 1` and the constant `1` both solve `w' = D ∘ w` (the constant because
`D 1 = 0`) with initial value `1`, so they agree. -/
theorem expDeriv_map_one (t : ℝ) : exp (t • D) 1 = 1 := by
  set u : ℝ → A := fun s => exp (s • D) 1 with hu_def
  have hu : ∀ s, HasDerivAt u (D (u s)) s := fun s => hasDerivAt_expDeriv_apply D 1 s
  have hc : ∀ s, HasDerivAt (fun _ : ℝ => (1 : A)) (D ((fun _ : ℝ => (1 : A)) s)) s := by
    intro s
    simpa [map_one_eq_zero D hD] using hasDerivAt_const s (1 : A)
  have hinit : u 0 = (fun _ : ℝ => (1 : A)) 0 := by simp [u]
  have huniq : u = fun _ : ℝ => (1 : A) :=
    ODE_solution_unique_univ (t₀ := (0 : ℝ)) (K := ‖D‖₊) (s := fun _ => Set.univ)
      (fun _ => (D.lipschitz).lipschitzOnWith)
      (fun s => ⟨hu s, Set.mem_univ _⟩)
      (fun s => ⟨hc s, Set.mem_univ _⟩)
      hinit
  simpa [u] using congrFun huniq t

include hD in
/-- **Etingof Remark 2.9.4 (give a proof!).** For a derivation `D` on a finite-dimensional real
algebra `A`, each `exp (t • D)` is an *algebra automorphism* of `A`, with inverse `exp (-t • D)`.
Together with `expDeriv_zero` and `expDeriv_add` this exhibits `t ↦ exp (t • D)` as the promised
one-parameter family of automorphisms. -/
noncomputable def expDerivAut (t : ℝ) : A ≃ₐ[ℝ] A where
  toFun a := exp (t • D) a
  invFun a := exp ((-t) • D) a
  left_inv a := by
    have h := expDeriv_apply_apply D (-t) t a
    rw [neg_add_cancel, expDeriv_zero] at h
    simpa using h
  right_inv a := by
    have h := expDeriv_apply_apply D t (-t) a
    rw [add_neg_cancel, expDeriv_zero] at h
    simpa using h
  map_mul' a b := expDeriv_map_mul D hD t a b
  map_add' a b := map_add (exp (t • D)) a b
  commutes' r := by
    rw [Algebra.algebraMap_eq_smul_one, map_smul, expDeriv_map_one D hD t]

@[simp] theorem expDerivAut_apply (t : ℝ) (a : A) : expDerivAut D hD t a = exp (t • D) a := rfl

end Etingof.Remark2_9_4
