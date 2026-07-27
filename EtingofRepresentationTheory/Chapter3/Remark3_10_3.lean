import Mathlib.RingTheory.TensorProduct.Maps
import Mathlib.FieldTheory.RatFunc.AsPolynomial
import Mathlib.FieldTheory.RatFunc.Basic
import Mathlib.RingTheory.Algebraic.Basic
import Mathlib.Data.Complex.Basic
import Mathlib.Algebra.MvPolynomial.PDeriv
import Mathlib.Algebra.Polynomial.Bivariate
import Mathlib.RingTheory.Derivation.Lie
import Mathlib.RingTheory.SimpleModule.Basic
import Mathlib.RingTheory.MvPolynomial
import Mathlib.LinearAlgebra.Basis.Basic
import Mathlib.Algebra.BigOperators.Finsupp.Fin
import EtingofRepresentationTheory.Chapter2.WeylAlgebraUniversal

/-!
# Remark 3.10.3: Failure of Theorem 3.10.2 for infinite dimensional representations

Theorem 3.10.2(i) states that if `V` is an irreducible finite dimensional representation
of `A` and `W` an irreducible finite dimensional representation of `B`, then `V ⊗ W` is an
irreducible representation of `A ⊗ B`. The finite dimensionality hypothesis is essential.

Etingof's Remark 3.10.3 gives an explicit counterexample: take
`A = B = V = W = ℂ(x)`, the field of rational functions. Each is irreducible as a module
over itself (a field has no nontrivial submodules), but part (i) fails because
`ℂ(x) ⊗_ℂ ℂ(x)` is not a field, so `V ⊗ W = ℂ(x) ⊗ ℂ(x)`, viewed as a module over
`A ⊗ B = ℂ(x) ⊗ ℂ(x)` itself, is not simple.

This file formalizes the core obstruction: `RatFunc ℂ ⊗[ℂ] RatFunc ℂ` is not a field. It also
constructs the operator-level Weyl-algebra example behind part (ii): on `ℂ[x,y]e^{xy}`, the two
Weyl algebras act by the pairs `(x, ∂x + y)` and `(y, ∂y + x)`. The four operators satisfy the
two Weyl relations and commute across the two factors, so they define a concrete representation
of `WeylAlgebra ℂ ⊗[ℂ] WeylAlgebra ℂ`.

## Proof strategy

The element `t := X ⊗ 1 - 1 ⊗ X` is nonzero but not a unit:

* **Not a unit.** The multiplication map `μ : ℂ(x) ⊗ ℂ(x) → ℂ(x)`, `a ⊗ b ↦ a * b`
  (`Algebra.TensorProduct.lmul'`), is a ring homomorphism sending `t` to `X - X = 0`.
  In a field every nonzero element is a unit, so if `t` were a unit `μ t = 0` would be a
  unit of `ℂ(x)`, which is impossible.

* **Nonzero.** The `ℂ`-algebra hom `Φ : ℂ(x) ⊗ ℂ(x) → ℂ(x)` built from the shift
  `f : X ↦ X + 1` on the left factor and the identity on the right sends `t` to
  `(X + 1) - X = 1 ≠ 0`, so `t ≠ 0`.
-/

open scoped TensorProduct
open Polynomial nonZeroDivisors

namespace EtingofRepresentationTheory.Chapter3.Remark3_10_3

noncomputable section

/-- `X + 1` is transcendental over `ℂ` inside `ℂ(x)`. -/
private lemma transcendental_X_add_one :
    Transcendental ℂ (RatFunc.X + 1 : RatFunc ℂ) := by
  have h : (RatFunc.X + 1 : RatFunc ℂ)
      = Polynomial.aeval (RatFunc.X : RatFunc ℂ) (Polynomial.X + 1 : ℂ[X]) := by
    simp
  rw [h]
  refine RatFunc.transcendental_X.aeval (Polynomial.X + 1 : ℂ[X]) ?_ ?_
  · rw [show (1 : ℂ[X]) = Polynomial.C 1 by simp, Polynomial.natDegree_X_add_C]
    exact one_ne_zero
  · rw [show (1 : ℂ[X]) = Polynomial.C 1 by simp, Polynomial.leadingCoeff_X_add_C]
    exact one_mem _

/-- The `ℂ`-algebra hom `ℂ[X] →ₐ[ℂ] ℂ(x)` sending `X` to `X + 1`. -/
private def φ : ℂ[X] →ₐ[ℂ] RatFunc ℂ := Polynomial.aeval (RatFunc.X + 1 : RatFunc ℂ)

private lemma hφ : (ℂ[X])⁰ ≤ (RatFunc ℂ)⁰.comap (φ : ℂ[X] →+* RatFunc ℂ) := by
  intro p hp
  rw [mem_nonZeroDivisors_iff_ne_zero] at hp
  rw [Submonoid.mem_comap, mem_nonZeroDivisors_iff_ne_zero]
  intro h
  exact hp (transcendental_iff.mp transcendental_X_add_one p h)

/-- The shift automorphism `f : ℂ(x) →ₐ[ℂ] ℂ(x)`, `X ↦ X + 1`. -/
private def f : RatFunc ℂ →ₐ[ℂ] RatFunc ℂ := RatFunc.liftAlgHom φ hφ

private lemma f_X : f (RatFunc.X : RatFunc ℂ) = RatFunc.X + 1 := by
  have h := RatFunc.liftAlgHom_apply_div φ hφ Polynomial.X 1
  simpa [f, φ, RatFunc.algebraMap_X] using h

/-- **Remark 3.10.3.** `ℂ(x) ⊗_ℂ ℂ(x)` is not a field: this is the obstruction to
Theorem 3.10.2(i) for infinite dimensional representations. -/
theorem ratFunc_tensor_ratFunc_not_isField :
    ¬ IsField (RatFunc ℂ ⊗[ℂ] RatFunc ℂ) := by
  intro hF
  set t : RatFunc ℂ ⊗[ℂ] RatFunc ℂ :=
    RatFunc.X ⊗ₜ[ℂ] 1 - 1 ⊗ₜ[ℂ] RatFunc.X with ht_def
  -- `Φ t = 1`, hence `t ≠ 0`.
  have hΦ :
      (Algebra.TensorProduct.lift f (AlgHom.id ℂ (RatFunc ℂ))
          (fun x y => Commute.all _ _)) t = 1 := by
    simp only [ht_def, map_sub, Algebra.TensorProduct.lift_tmul, AlgHom.id_apply, map_one,
      f_X, mul_one, one_mul]
    ring
  have ht : t ≠ 0 := by
    intro h
    rw [h, map_zero] at hΦ
    exact one_ne_zero hΦ.symm
  -- `t` has an inverse in the supposed field.
  obtain ⟨s, hs⟩ := hF.mul_inv_cancel ht
  -- Applying the multiplication map `μ` gives `μ t * μ s = 1`, but `μ t = 0`.
  have hμt : Algebra.TensorProduct.lmul' (S := RatFunc ℂ) ℂ t = 0 := by
    simp [ht_def, map_sub, Algebra.TensorProduct.lmul'_apply_tmul]
  have hcontra := congrArg (Algebra.TensorProduct.lmul' (S := RatFunc ℂ) ℂ) hs
  rw [map_mul, map_one, hμt, zero_mul] at hcontra
  exact zero_ne_one hcontra

/-! ## The Weyl-algebra arm: the entangled exponential module -/

open MvPolynomial

/-- The polynomial carrier of the algebraic `D`-module customarily denoted
`ℂ[x,y] e^{xy}`. The exponential is encoded in the twisted derivative actions below. -/
abbrev WeylCounterexampleModule := MvPolynomial (Fin 2) ℂ

/-- Multiplication by the variable `X i` on `ℂ[X 0, X 1]`. -/
noncomputable def mulVar (i : Fin 2) : Module.End ℂ WeylCounterexampleModule where
  toFun p := X i * p
  map_add' _ _ := mul_add _ _ _
  map_smul' c p := by
    simp only [MvPolynomial.smul_eq_C_mul, RingHom.id_apply]
    ring

/-- Partial differentiation with respect to `X i`. -/
noncomputable def pderivEnd (i : Fin 2) : Module.End ℂ WeylCounterexampleModule :=
  (pderiv i).toLinearMap

private lemma partials_commute (i j : Fin 2) :
    pderivEnd i * pderivEnd j = pderivEnd j * pderivEnd i := by
  have hbracket : ⁅(pderiv i : Derivation ℂ WeylCounterexampleModule
      WeylCounterexampleModule), pderiv j⁆ =
      (0 : Derivation ℂ WeylCounterexampleModule WeylCounterexampleModule) := by
    apply MvPolynomial.derivation_ext
    intro l
    fin_cases i <;> fin_cases j <;> fin_cases l <;>
      simp [Derivation.commutator_apply]
  apply LinearMap.ext
  intro p
  have hp := DFunLike.congr_fun hbracket p
  simpa [pderivEnd, Derivation.commutator_apply, Module.End.mul_apply] using sub_eq_zero.mp hp

private lemma partial_mulVar_self (i : Fin 2) :
    pderivEnd i * mulVar i = mulVar i * pderivEnd i + 1 := by
  apply LinearMap.ext
  intro p
  simp [pderivEnd, mulVar, Module.End.mul_apply]

private lemma partial_mulVar_of_ne {i j : Fin 2} (h : j ≠ i) :
    pderivEnd i * mulVar j = mulVar j * pderivEnd i := by
  apply LinearMap.ext
  intro p
  simp [pderivEnd, mulVar, Module.End.mul_apply,
    MvPolynomial.pderiv_X_of_ne h]

private lemma mulVars_commute (i j : Fin 2) :
    mulVar i * mulVar j = mulVar j * mulVar i := by
  apply LinearMap.ext
  intro p
  simp [mulVar, Module.End.mul_apply]
  ring

/-- The first Weyl generator `x`, acting by multiplication by `x`. -/
noncomputable def firstX : Module.End ℂ WeylCounterexampleModule := mulVar 0

/-- The first Weyl generator `∂x`, acting on `f e^{xy}` as `(∂x f + y f)e^{xy}`. -/
noncomputable def firstY : Module.End ℂ WeylCounterexampleModule := pderivEnd 0 + mulVar 1

/-- The second Weyl generator `y`, acting by multiplication by `y`. -/
noncomputable def secondX : Module.End ℂ WeylCounterexampleModule := mulVar 1

/-- The second Weyl generator `∂y`, acting on `f e^{xy}` as `(∂y f + x f)e^{xy}`. -/
noncomputable def secondY : Module.End ℂ WeylCounterexampleModule := pderivEnd 1 + mulVar 0

/-- The first twisted pair satisfies the Weyl relation. -/
theorem first_weyl_relation : firstY * firstX = firstX * firstY + 1 := by
  rw [firstY, firstX, add_mul, partial_mulVar_self, mul_add, mulVars_commute 1 0]
  abel

/-- The second twisted pair satisfies the Weyl relation. -/
theorem second_weyl_relation : secondY * secondX = secondX * secondY + 1 := by
  rw [secondY, secondX, add_mul, partial_mulVar_self, mul_add, mulVars_commute 0 1]
  abel

theorem firstX_secondX_commute : Commute firstX secondX := by
  change firstX * secondX = secondX * firstX
  simpa [firstX, secondX] using mulVars_commute 0 1

theorem firstX_secondY_commute : Commute firstX secondY := by
  change firstX * secondY = secondY * firstX
  rw [firstX, secondY, mul_add, add_mul,
    ← partial_mulVar_of_ne (by decide : (0 : Fin 2) ≠ 1)]

theorem firstY_secondX_commute : Commute firstY secondX := by
  change firstY * secondX = secondX * firstY
  rw [firstY, secondX, add_mul, mul_add,
    partial_mulVar_of_ne (by decide : (1 : Fin 2) ≠ 0), mulVars_commute 1 1]

theorem firstY_secondY_commute : Commute firstY secondY := by
  apply LinearMap.ext
  intro p
  have hp := LinearMap.congr_fun (partials_commute 0 1) p
  dsimp [firstY, secondY, pderivEnd, mulVar] at hp ⊢
  simp only [map_add, Derivation.leibniz, pderiv_X_self, smul_eq_mul] at ⊢
  rw [hp]
  ring

/-- The first Weyl-algebra action on the entangled polynomial module. -/
noncomputable def firstRep :
    Etingof.WeylAlgebra ℂ →ₐ[ℂ] Module.End ℂ WeylCounterexampleModule :=
  Etingof.WeylAlgebra.toEnd ℂ WeylCounterexampleModule firstX firstY first_weyl_relation

/-- The second Weyl-algebra action on the entangled polynomial module. -/
noncomputable def secondRep :
    Etingof.WeylAlgebra ℂ →ₐ[ℂ] Module.End ℂ WeylCounterexampleModule :=
  Etingof.WeylAlgebra.toEnd ℂ WeylCounterexampleModule secondX secondY second_weyl_relation

/-- Operators coming from the two Weyl-algebra factors commute. -/
theorem firstRep_secondRep_commute (a b : Etingof.WeylAlgebra ℂ) :
    Commute (firstRep a) (secondRep b) := by
  have commute_second (T : Module.End ℂ WeylCounterexampleModule)
      (hx : Commute T secondX) (hy : Commute T secondY) :
      ∀ b : Etingof.WeylAlgebra ℂ, Commute T (secondRep b) := by
    intro b
    refine Etingof.WeylAlgebra.induction_on (p := fun b => Commute T (secondRep b))
      ℂ b ?_ ?_ ?_ ?_ ?_
    · simpa [secondRep] using hx
    · simpa [secondRep] using hy
    · intro c
      rw [AlgHom.commutes]
      exact Algebra.commutes c T |>.symm
    · intro u v hu hv
      rw [map_add]
      exact hu.add_right hv
    · intro u v hu hv
      rw [map_mul]
      exact hu.mul_right hv
  refine Etingof.WeylAlgebra.induction_on
    (p := fun a => Commute (firstRep a) (secondRep b)) ℂ a ?_ ?_ ?_ ?_ ?_
  · simpa [firstRep] using
      commute_second firstX firstX_secondX_commute firstX_secondY_commute b
  · simpa [firstRep] using
      commute_second firstY firstY_secondX_commute firstY_secondY_commute b
  · intro c
    rw [AlgHom.commutes]
    exact Algebra.commutes c (secondRep b)
  · intro u v hu hv
    rw [map_add]
    exact hu.add_left hv
  · intro u v hu hv
    rw [map_mul]
    exact hu.mul_left hv

/-- The resulting representation of the tensor product of two Weyl algebras. This is the
algebraic `D`-module `ℂ[x,y]e^{xy}` appearing in the standard counterexample to the
infinite-dimensional analogue of Theorem 3.10.2(ii). -/
noncomputable def tensorRep :
    (Etingof.WeylAlgebra ℂ ⊗[ℂ] Etingof.WeylAlgebra ℂ) →ₐ[ℂ]
      Module.End ℂ WeylCounterexampleModule :=
  Algebra.TensorProduct.lift firstRep secondRep firstRep_secondRep_commute

/-- The tensor-product Weyl-algebra module carried by `ℂ[x,y]e^{xy}`. -/
@[reducible] noncomputable def tensorModule :
    Module (Etingof.WeylAlgebra ℂ ⊗[ℂ] Etingof.WeylAlgebra ℂ)
      WeylCounterexampleModule :=
  Module.compHom WeylCounterexampleModule tensorRep.toRingHom

@[simp] theorem tensorRep_tmul (a b : Etingof.WeylAlgebra ℂ) :
  tensorRep (a ⊗ₜ[ℂ] b) = firstRep a * secondRep b := by
  exact Algebra.TensorProduct.lift_tmul _ _ _ _ _

@[simp] theorem firstRep_x : firstRep (Etingof.WeylAlgebra.x ℂ) = firstX := by
  simp [firstRep]

@[simp] theorem firstRep_y : firstRep (Etingof.WeylAlgebra.y ℂ) = firstY := by
  simp [firstRep]

@[simp] theorem secondRep_x : secondRep (Etingof.WeylAlgebra.x ℂ) = secondX := by
  simp [secondRep]

@[simp] theorem secondRep_y : secondRep (Etingof.WeylAlgebra.y ℂ) = secondY := by
  simp [secondRep]

/-- The two derivative generators are genuinely coupled to the opposite polynomial variable
at the cyclic vector `1`: this is the algebraic content of the `e^{xy}` twist. -/
theorem entangled_generator_relations :
    firstRep (Etingof.WeylAlgebra.y ℂ) 1 =
        secondRep (Etingof.WeylAlgebra.x ℂ) 1 ∧
      secondRep (Etingof.WeylAlgebra.y ℂ) 1 =
        firstRep (Etingof.WeylAlgebra.x ℂ) 1 := by
  constructor <;>
    simp [firstY, firstX, secondY, secondX, pderivEnd, mulVar]

private lemma pderiv_zero_bivariate_C (p : ℂ[X]) :
    pderiv 0 (Polynomial.Bivariate.equivMvPolynomial ℂ (Polynomial.C p)) =
      Polynomial.Bivariate.equivMvPolynomial ℂ (Polynomial.C p.derivative) := by
  simpa using Polynomial.Bivariate.pderiv_zero_equivMvPolynomial (R := ℂ) (Polynomial.C p)

/-- The entangled tensor-product Weyl module is simple.  Indeed, stability under the four
Weyl generators implies stability under multiplication by both variables and under both
ordinary partial derivatives.  Repeated partial differentiation takes every nonzero
bivariate polynomial to a nonzero constant. -/
theorem tensorModule_isSimpleModule :
    letI := tensorModule
    IsSimpleModule (Etingof.WeylAlgebra ℂ ⊗[ℂ] Etingof.WeylAlgebra ℂ)
      WeylCounterexampleModule := by
  classical
  letI := tensorModule
  let A := Etingof.WeylAlgebra ℂ ⊗[ℂ] Etingof.WeylAlgebra ℂ
  refine { exists_pair_ne := ⟨⊥, ⊤, bot_ne_top⟩, eq_bot_or_eq_top := fun S => ?_ }
  rcases eq_or_ne S ⊥ with rfl | hS
  · exact Or.inl rfl
  right
  obtain ⟨p, hpS, hp0⟩ := (Submodule.ne_bot_iff S).mp hS
  have hact (a : A) (q : WeylCounterexampleModule) : a • q = tensorRep a q := rfl
  have hX0 (q : WeylCounterexampleModule) (hq : q ∈ S) : X 0 * q ∈ S := by
    have := S.smul_mem ((Etingof.WeylAlgebra.x ℂ) ⊗ₜ[ℂ] (1 : Etingof.WeylAlgebra ℂ)) hq
    simpa [hact, tensorRep_tmul, firstX, mulVar, Module.End.mul_apply] using this
  have hX1 (q : WeylCounterexampleModule) (hq : q ∈ S) : X 1 * q ∈ S := by
    have := S.smul_mem ((1 : Etingof.WeylAlgebra ℂ) ⊗ₜ[ℂ] Etingof.WeylAlgebra.x ℂ) hq
    simpa [hact, tensorRep_tmul, secondX, mulVar, Module.End.mul_apply] using this
  have hD0 (q : WeylCounterexampleModule) (hq : q ∈ S) : pderiv 0 q ∈ S := by
    have := S.smul_mem
      (((Etingof.WeylAlgebra.y ℂ) ⊗ₜ[ℂ] (1 : Etingof.WeylAlgebra ℂ)) -
        ((1 : Etingof.WeylAlgebra ℂ) ⊗ₜ[ℂ] Etingof.WeylAlgebra.x ℂ)) hq
    simpa [sub_smul, hact, tensorRep_tmul, firstY, secondX, pderivEnd, mulVar,
      Module.End.mul_apply] using this
  have hD1 (q : WeylCounterexampleModule) (hq : q ∈ S) : pderiv 1 q ∈ S := by
    have := S.smul_mem
      (((1 : Etingof.WeylAlgebra ℂ) ⊗ₜ[ℂ] Etingof.WeylAlgebra.y ℂ) -
        ((Etingof.WeylAlgebra.x ℂ) ⊗ₜ[ℂ] (1 : Etingof.WeylAlgebra ℂ))) hq
    simpa [sub_smul, hact, tensorRep_tmul, secondY, firstX, pderivEnd, mulVar,
      Module.End.mul_apply] using this
  let e := Polynomial.Bivariate.equivMvPolynomial ℂ
  let q : ℂ[X][X] := e.symm p
  have hp_eq : e q = p := e.apply_symm_apply p
  have hq0 : q ≠ 0 := by
    intro h
    apply hp0
    rw [← hp_eq, h, map_zero]
  have houter : ∀ n : ℕ, e (Polynomial.derivative^[n] q) ∈ S := by
    intro n
    induction n with
    | zero => simpa [e, q] using hpS
    | succ n ih =>
        rw [Function.iterate_succ_apply']
        rw [← Polynomial.Bivariate.pderiv_one_equivMvPolynomial]
        exact hD1 _ ih
  let q₁ := Polynomial.derivative^[q.natDegree] q
  have hq₁S : e q₁ ∈ S := houter q.natDegree
  have hq₁deg : q₁.natDegree = 0 := by
    exact Nat.le_zero.mp (by simpa [q₁] using Polynomial.natDegree_iterate_derivative q q.natDegree)
  have hq₁zero : q₁ ≠ 0 := by
    intro hz
    have hc := Polynomial.coeff_iterate_derivative (k := q.natDegree) q 0
    rw [show Polynomial.derivative^[q.natDegree] q = q₁ from rfl, hz,
      Polynomial.coeff_zero] at hc
    simp only [zero_add, Nat.descFactorial_self, Polynomial.coeff_natDegree] at hc
    exact hq0 (Polynomial.leadingCoeff_eq_zero.mp
      (smul_eq_zero.mp hc.symm |>.resolve_left (Nat.factorial_ne_zero _)))
  let r : ℂ[X] := q₁.coeff 0
  have hq₁_eq : q₁ = Polynomial.C r := Polynomial.eq_C_of_natDegree_eq_zero hq₁deg
  have hr0 : r ≠ 0 := by
    intro hr
    exact hq₁zero (by simp [hq₁_eq, r, hr])
  have hinner : ∀ n : ℕ, e (Polynomial.C (Polynomial.derivative^[n] r)) ∈ S := by
    intro n
    induction n with
    | zero => simpa [hq₁_eq] using hq₁S
    | succ n ih =>
        rw [Function.iterate_succ_apply']
        rw [← pderiv_zero_bivariate_C]
        exact hD0 _ ih
  let r₁ := Polynomial.derivative^[r.natDegree] r
  have hr₁S : e (Polynomial.C r₁) ∈ S := hinner r.natDegree
  have hr₁deg : r₁.natDegree = 0 := by
    exact Nat.le_zero.mp (by simpa [r₁] using Polynomial.natDegree_iterate_derivative r r.natDegree)
  have hr₁zero : r₁ ≠ 0 := by
    intro hz
    have hc := Polynomial.coeff_iterate_derivative (k := r.natDegree) r 0
    rw [show Polynomial.derivative^[r.natDegree] r = r₁ from rfl, hz,
      Polynomial.coeff_zero] at hc
    simp only [zero_add, Nat.descFactorial_self, Polynomial.coeff_natDegree] at hc
    exact hr0 (Polynomial.leadingCoeff_eq_zero.mp
      (smul_eq_zero.mp hc.symm |>.resolve_left (Nat.factorial_ne_zero _)))
  let c : ℂ := r₁.coeff 0
  have hr₁_eq : r₁ = Polynomial.C c := Polynomial.eq_C_of_natDegree_eq_zero hr₁deg
  have hc0 : c ≠ 0 := by
    intro hc
    exact hr₁zero (by simp [hr₁_eq, c, hc])
  have hcS : MvPolynomial.C c ∈ S := by
    simpa [e, hr₁_eq] using hr₁S
  apply top_unique
  intro z _
  have hscale := S.smul_mem (algebraMap ℂ A c⁻¹) hcS
  have hone : (1 : WeylCounterexampleModule) ∈ S := by
    rw [hact, tensorRep.commutes] at hscale
    change c⁻¹ • MvPolynomial.C c ∈ S at hscale
    rw [MvPolynomial.smul_eq_C_mul, ← MvPolynomial.C_mul] at hscale
    simpa [hc0] using hscale
  have hC (d : ℂ) : MvPolynomial.C d ∈ S := by
    have hs := S.smul_mem (algebraMap ℂ A d) hone
    rw [hact, tensorRep.commutes] at hs
    simpa [MvPolynomial.smul_eq_C_mul] using hs
  have hall : ∀ z : WeylCounterexampleModule, z ∈ S := by
    intro z
    induction z using MvPolynomial.induction_on with
    | C d => exact hC d
    | add u v hu hv => exact S.add_mem hu hv
    | mul_X u i hu =>
        fin_cases i
        · simpa [mul_comm] using hX0 u hu
        · simpa [mul_comm] using hX1 u hu
  exact hall z

/-- The entangled representation does not factor through a finite-dimensional algebra.  If it
did, the orbit of the nonzero cyclic vector `1` would be a quotient of a finite-dimensional
vector space.  Simplicity says that orbit is the whole polynomial module, contradicting the
infinite dimension of a polynomial ring in two variables. -/
theorem tensorRep_not_factors_finiteDimensional
    (Q : Type*) [Ring Q] [Algebra ℂ Q] [FiniteDimensional ℂ Q]
    (q : (Etingof.WeylAlgebra ℂ ⊗[ℂ] Etingof.WeylAlgebra ℂ) →ₐ[ℂ] Q)
    (r : Q →ₐ[ℂ] Module.End ℂ WeylCounterexampleModule) :
    tensorRep ≠ r.comp q := by
  classical
  intro hfactor
  let A := Etingof.WeylAlgebra ℂ ⊗[ℂ] Etingof.WeylAlgebra ℂ
  letI := tensorModule
  letI : IsSimpleModule A WeylCounterexampleModule := tensorModule_isSimpleModule
  let orbitQ : Q →ₗ[ℂ] WeylCounterexampleModule := {
    toFun a := r a 1
    map_add' a b := by simp
    map_smul' c a := by simp }
  have horbitQ : Function.Surjective orbitQ := by
    intro p
    obtain ⟨a, ha⟩ := IsSimpleModule.toSpanSingleton_surjective A (one_ne_zero :
      (1 : WeylCounterexampleModule) ≠ 0) p
    refine ⟨q a, ?_⟩
    change r (q a) 1 = p
    rw [← AlgHom.comp_apply, ← hfactor]
    exact ha
  letI : FiniteDimensional ℂ WeylCounterexampleModule :=
    FiniteDimensional.of_surjective orbitQ horbitQ
  have hfinrank : Module.finrank ℂ WeylCounterexampleModule = 0 :=
    MvPolynomial.finrank_eq_zero
  exact one_ne_zero (finrank_zero_iff_forall_zero.mp hfinrank 1)

/-! ### The one-factor restriction is the regular Weyl module -/

/-- The PBW basis of the characteristic-zero Weyl algebra. -/
private noncomputable def weylBasis :
    Module.Basis (ℕ × ℕ) ℂ (Etingof.WeylAlgebra ℂ) :=
  Module.Basis.mk (Etingof.Proposition_2_7_1 (k := ℂ)).1
    (Etingof.Proposition_2_7_1 (k := ℂ)).2

/-- The bivariate monomial basis, indexed compatibly with the Weyl PBW basis. -/
private noncomputable def bivariateBasis :
    Module.Basis (ℕ × ℕ) ℂ WeylCounterexampleModule :=
  (MvPolynomial.basisMonomials (Fin 2) ℂ).reindex
    (finTwoArrowEquiv' ℕ)

private theorem bivariateBasis_apply (i j : ℕ) :
    bivariateBasis (i, j) = X 0 ^ i * X 1 ^ j := by
  rw [bivariateBasis, Module.Basis.reindex_apply, MvPolynomial.coe_basisMonomials]
  simp [finTwoArrowEquiv', MvPolynomial.monomial_eq]

/-- The PBW linear equivalence between the Weyl algebra and the polynomial carrier. -/
noncomputable def regularLinearEquiv :
    Etingof.WeylAlgebra ℂ ≃ₗ[ℂ] WeylCounterexampleModule :=
  weylBasis.equiv bivariateBasis (Equiv.refl (ℕ × ℕ))

@[simp] theorem regularLinearEquiv_monomial (i j : ℕ) :
    regularLinearEquiv (Etingof.WeylAlgebra.monomial ℂ i j) = X 0 ^ i * X 1 ^ j := by
  rw [← show weylBasis (i, j) = Etingof.WeylAlgebra.monomial ℂ i j by
    exact Module.Basis.mk_apply _ _ _]
  rw [regularLinearEquiv, Module.Basis.equiv_apply, bivariateBasis_apply]
  rfl

/-- The orbit of the cyclic vector `1` under the first Weyl factor. -/
noncomputable def firstOrbit :
    Etingof.WeylAlgebra ℂ →ₗ[ℂ] WeylCounterexampleModule where
  toFun a := firstRep a 1
  map_add' a b := by simp
  map_smul' c a := by simp

private lemma firstY_pow_one (j : ℕ) :
    (firstY ^ j) (1 : WeylCounterexampleModule) = X 1 ^ j := by
  induction j with
  | zero => simp
  | succ j ih =>
      rw [pow_succ', Module.End.mul_apply, ih]
      simp [firstY, pderivEnd, mulVar]
      rw [mul_comm, pow_succ]

@[simp] theorem firstOrbit_monomial (i j : ℕ) :
    firstOrbit (Etingof.WeylAlgebra.monomial ℂ i j) = X 0 ^ i * X 1 ^ j := by
  change firstRep (Etingof.WeylAlgebra.monomial ℂ i j) 1 = _
  rw [Etingof.WeylAlgebra.monomial, map_mul, map_pow, map_pow,
    Module.End.mul_apply, firstRep_x, firstRep_y, firstY_pow_one]
  induction i with
  | zero => simp
  | succ i ih =>
      rw [pow_succ', Module.End.mul_apply, ih]
      simp [firstX, mulVar]
      ring

/-- The PBW equivalence is exactly the orbit map `a ↦ a · 1`. In particular, restricting the
entangled module to its first Weyl factor gives the left regular Weyl module. -/
theorem regularLinearEquiv_eq_firstOrbit :
    regularLinearEquiv.toLinearMap = firstOrbit := by
  apply weylBasis.ext
  intro p
  rw [show weylBasis p = Etingof.WeylAlgebra.monomial ℂ p.1 p.2 by
    exact Module.Basis.mk_apply _ _ _]
  simp [regularLinearEquiv_monomial, firstOrbit_monomial]

end

end EtingofRepresentationTheory.Chapter3.Remark3_10_3
