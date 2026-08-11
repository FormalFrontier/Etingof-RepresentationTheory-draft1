import Mathlib
import EtingofRepresentationTheory.Chapter4.Example4_3_Q8

/-!
# Exercise 4.3.1: the 2-dimensional irreducible representation of `Q₈` on a function space

**Exercise 4.3.1.** Show that the 2-dimensional irreducible representation of `Q₈` can be
realized in the space of functions `f : Q₈ → ℂ` such that `f(g·i) = √(-1)·f(g)` (the action
of `G` is by right multiplication, `g ∘ f(x) = f(x·g)`).

## Formalization

We model `Q₈` by Mathlib's `QuaternionGroup 2` (order `8`), with the element `i` taken to be
`QuaternionGroup.a 1` (an element of order `4`, matching the matrix `rhoI` in
`Example4_3_Q8`), and `√(-1)` by `Complex.I`.

The action of `Q₈` on functions `Q₈ → ℂ` by right translation, `(g ∘ f)(x) = f(x·g)`, is the
right regular representation `rightRegular`. The book writes the covariance condition as
`f(g·i) = √(-1)·f(g)`; the subspace invariant under the right-translation action is the one
cut out by the left covariance `f(i·g) = √(-1)·f(g)` (the two are the standard equivalent
conventions for the induced representation `Ind_{⟨i⟩}^{Q₈} χ`, where `χ(i) = √(-1)`). We call
this invariant subspace `covariantSubspace`.

The main results are:
* `covariantSubspace_invariant`: the subspace is a subrepresentation of the right regular
  representation;
* `covariantSubspace_finrank`: it is `2`-dimensional;
* `covariantSubspace_irreducible`: it is irreducible (every invariant subspace of it is `⊥`
  or the whole space).

This representation is isomorphic to the concrete 2-dimensional irreducible
`Example4_3_Q8.repLin`.
-/

open QuaternionGroup Complex

namespace Etingof.Exercise4_3_1

/-- The right regular representation of `Q₈ = QuaternionGroup 2` on functions `Q₈ → ℂ`:
`(rightRegular g) f = fun x => f (x * g)`. This is the action `g ∘ f(x) = f(x·g)` from the
book. -/
noncomputable def rightRegular :
    Representation ℂ (QuaternionGroup 2) (QuaternionGroup 2 → ℂ) where
  toFun g := LinearMap.funLeft ℂ ℂ (· * g)
  map_one' := by
    ext f x
    simp
  map_mul' g h := by
    ext f x
    simp [LinearMap.funLeft_apply, mul_assoc]

@[simp]
theorem rightRegular_apply (g : QuaternionGroup 2) (f : QuaternionGroup 2 → ℂ)
    (x : QuaternionGroup 2) : rightRegular g f x = f (x * g) := rfl

/-- The subspace of functions `f : Q₈ → ℂ` satisfying the covariance condition
`f(i·g) = √(-1)·f(g)` for all `g`, where `i = a 1` and `√(-1) = Complex.I`. This is the space
in which the 2-dimensional irreducible representation of `Q₈` is realized. -/
def covariantSubspace : Submodule ℂ (QuaternionGroup 2 → ℂ) where
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

@[simp]
theorem mem_covariantSubspace {f : QuaternionGroup 2 → ℂ} :
    f ∈ covariantSubspace ↔ ∀ g : QuaternionGroup 2, f (a 1 * g) = Complex.I * f g :=
  Iff.rfl

/-- `covariantSubspace` is a subrepresentation of the right regular representation: it is
invariant under `rightRegular g` for every `g`. -/
theorem covariantSubspace_invariant (g : QuaternionGroup 2)
    (f : QuaternionGroup 2 → ℂ) (hf : f ∈ covariantSubspace) :
    rightRegular g f ∈ covariantSubspace := by
  rw [mem_covariantSubspace]
  intro h
  change f (a 1 * h * g) = I * f (h * g)
  rw [mul_assoc]
  exact (mem_covariantSubspace.mp hf) (h * g)

/-- The six non-free values of a covariant function `f`, all determined by `f (a 0)` and
`f (xa 0)` via the covariance relation `f (a 1 * g) = I * f g`. -/
theorem covariantSubspace_values {f : QuaternionGroup 2 → ℂ} (hf : f ∈ covariantSubspace) :
    f (a 1) = I * f (a 0) ∧ f (a 2) = - f (a 0) ∧ f (a 3) = -I * f (a 0) ∧
      f (xa 3) = I * f (xa 0) ∧ f (xa 2) = - f (xa 0) ∧ f (xa 1) = -I * f (xa 0) := by
  have hf' := mem_covariantSubspace.mp hf
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

/-- The explicit covariant function with `f (a 0) = s` and `f (xa 0) = t`. Its eight values are
determined by the covariance relation. -/
noncomputable def liftFun (s t : ℂ) : QuaternionGroup 2 → ℂ
  | a i => if i = 0 then s else if i = 1 then I * s else if i = 2 then -s else -I * s
  | xa i => if i = 0 then t else if i = 1 then -I * t else if i = 2 then -t else I * t

@[simp] theorem liftFun_a0 (s t : ℂ) : liftFun s t (a 0) = s := rfl
@[simp] theorem liftFun_a1 (s t : ℂ) : liftFun s t (a 1) = I * s := rfl
@[simp] theorem liftFun_a2 (s t : ℂ) : liftFun s t (a 2) = -s := rfl
@[simp] theorem liftFun_a3 (s t : ℂ) : liftFun s t (a 3) = -I * s := rfl
@[simp] theorem liftFun_xa0 (s t : ℂ) : liftFun s t (xa 0) = t := rfl
@[simp] theorem liftFun_xa1 (s t : ℂ) : liftFun s t (xa 1) = -I * t := rfl
@[simp] theorem liftFun_xa2 (s t : ℂ) : liftFun s t (xa 2) = -t := rfl
@[simp] theorem liftFun_xa3 (s t : ℂ) : liftFun s t (xa 3) = I * t := rfl

/-- Every `i : ZMod 4` is one of the four literals `0, 1, 2, 3` (used to enumerate the
eight group elements). -/
theorem zmod4_cases (i : ZMod 4) : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 := by
  revert i; decide

theorem liftFun_mem (s t : ℂ) : liftFun s t ∈ covariantSubspace := by
  rw [mem_covariantSubspace]
  have p0 : (a 1 * a 0 : QuaternionGroup 2) = a 1 := by decide
  have p1 : (a 1 * a 1 : QuaternionGroup 2) = a 2 := by decide
  have p2 : (a 1 * a 2 : QuaternionGroup 2) = a 3 := by decide
  have p3 : (a 1 * a 3 : QuaternionGroup 2) = a 0 := by decide
  have q0 : (a 1 * xa 0 : QuaternionGroup 2) = xa 3 := by decide
  have q1 : (a 1 * xa 1 : QuaternionGroup 2) = xa 0 := by decide
  have q2 : (a 1 * xa 2 : QuaternionGroup 2) = xa 1 := by decide
  have q3 : (a 1 * xa 3 : QuaternionGroup 2) = xa 2 := by decide
  intro g
  rcases g with i | i <;> rcases zmod4_cases i with rfl | rfl | rfl | rfl <;>
    simp only [p0, p1, p2, p3, q0, q1, q2, q3,
      liftFun_a0, liftFun_a1, liftFun_a2, liftFun_a3,
      liftFun_xa0, liftFun_xa1, liftFun_xa2, liftFun_xa3] <;>
    norm_num [Complex.ext_iff]

/-- Every covariant function equals `liftFun` of its two free values. -/
theorem covariantSubspace_eq_liftFun {f : QuaternionGroup 2 → ℂ} (hf : f ∈ covariantSubspace) :
    f = liftFun (f (a 0)) (f (xa 0)) := by
  obtain ⟨e1, e2, e3, x3, x2, x1⟩ := covariantSubspace_values hf
  funext g
  rcases g with i | i <;> rcases zmod4_cases i with rfl | rfl | rfl | rfl <;>
    simp only [liftFun_a0, liftFun_a1, liftFun_a2, liftFun_a3,
      liftFun_xa0, liftFun_xa1, liftFun_xa2, liftFun_xa3] <;>
    first
      | rfl | (exact e1) | (exact e2) | (exact e3) | (exact x1) | (exact x2) | (exact x3)

/-- The evaluation isomorphism `covariantSubspace ≃ₗ[ℂ] (Fin 2 → ℂ)`, `f ↦ ![f (a 0), f (xa 0)]`,
witnessing that `covariantSubspace` is 2-dimensional. -/
noncomputable def covEquiv : covariantSubspace ≃ₗ[ℂ] (Fin 2 → ℂ) where
  toFun f := ![f.1 (a 0), f.1 (xa 0)]
  map_add' f g := by ext i; fin_cases i <;> simp
  map_smul' c f := by ext i; fin_cases i <;> simp
  invFun v := ⟨liftFun (v 0) (v 1), liftFun_mem _ _⟩
  left_inv f := by
    apply Subtype.ext
    simpa using (covariantSubspace_eq_liftFun f.2).symm
  right_inv v := by
    funext i; fin_cases i <;> rfl

/-- The space `covariantSubspace` is `2`-dimensional. -/
theorem covariantSubspace_finrank :
    Module.finrank ℂ covariantSubspace = 2 := by
  rw [covEquiv.finrank_eq, Module.finrank_fin_fun]

/-- The realized representation is irreducible: every `Q₈`-invariant subspace `U` contained in
`covariantSubspace` is either `⊥` or all of `covariantSubspace`. -/
theorem covariantSubspace_irreducible
    (U : Submodule ℂ (QuaternionGroup 2 → ℂ))
    (hUle : U ≤ covariantSubspace)
    (hUinv : ∀ g : QuaternionGroup 2, ∀ f ∈ U, rightRegular g f ∈ U) :
    U = ⊥ ∨ U = covariantSubspace := by
  rcases eq_or_ne U ⊥ with h | h
  · exact Or.inl h
  refine Or.inr ?_
  -- pick a nonzero `f ∈ U`
  obtain ⟨f, hfU, hf0⟩ := (Submodule.ne_bot_iff U).mp h
  have hfcov : f ∈ covariantSubspace := hUle hfU
  obtain ⟨e1, e2, _e3, _x3, _x2, x1⟩ := covariantSubspace_values hfcov
  set s := f (a 0) with hs
  set t := f (xa 0) with ht
  -- if both free values vanish, `f = 0`, contradiction
  have hnot : ¬ (s = 0 ∧ t = 0) := by
    rintro ⟨hs0, ht0⟩
    apply hf0
    rw [covariantSubspace_eq_liftFun hfcov, ← hs, ← ht, hs0, ht0]
    funext g
    rcases g with i | i <;> rcases zmod4_cases i with rfl | rfl | rfl | rfl <;>
      simp only [liftFun_a0, liftFun_a1, liftFun_a2, liftFun_a3,
        liftFun_xa0, liftFun_xa1, liftFun_xa2, liftFun_xa3, Pi.zero_apply,
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
  -- upgrade to `finrank U ≥ 2`, forcing `U = covariantSubspace`
  refine Submodule.eq_of_le_of_finrank_le hUle ?_
  rw [covariantSubspace_finrank]
  -- exhibit two linearly independent members of `U`
  by_cases hst : s = 0 ∨ t = 0
  · -- use `y := rightRegular (xa 0) f`, coordinates `(t, -s)`; det `= -(s² + t²)`
    have hhU : rightRegular (xa 0) f ∈ U := hUinv (xa 0) f hfU
    have hdet : f (a 0) * (rightRegular (xa 0) f) (xa 0)
        - f (xa 0) * (rightRegular (xa 0) f) (a 0) ≠ 0 := by
      rw [rightRegular_apply, rightRegular_apply, show xa 0 * xa 0 = a 2 from by decide,
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
  · -- both `s ≠ 0` and `t ≠ 0`: use `y := rightRegular (a 1) f`; det `= -2 I s t`
    rw [not_or] at hst
    obtain ⟨hs0, ht0⟩ := hst
    have hhU : rightRegular (a 1) f ∈ U := hUinv (a 1) f hfU
    have hdet : f (a 0) * (rightRegular (a 1) f) (xa 0)
        - f (xa 0) * (rightRegular (a 1) f) (a 0) ≠ 0 := by
      rw [rightRegular_apply, rightRegular_apply, show xa 0 * a 1 = xa 1 from by decide,
        show a 0 * a 1 = a 1 from by decide, e1, x1, ← hs, ← ht]
      have hne : s * (-I * t) - t * (I * s) = -(2 * I * (s * t)) := by ring
      rw [hne, neg_ne_zero]
      exact mul_ne_zero (mul_ne_zero (by norm_num) Complex.I_ne_zero) (mul_ne_zero hs0 ht0)
    have := (indep_in_U hfU hhU hdet).fintype_card_le_finrank
    simpa using this

end Etingof.Exercise4_3_1
