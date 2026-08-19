/-
Copyright (c) 2026 mathlib-initiative. All rights reserved.
Released under Apache 2.0 license as described in the file LICENCE.
Authors: mathlib-initiative
-/

import Mathlib.FieldTheory.RatFunc.AsPolynomial
import Mathlib.Data.Complex.Basic
import Mathlib.Algebra.Polynomial.Bivariate
import Mathlib.RingTheory.Derivation.Lie
import Mathlib.RingTheory.MvPolynomial
import RepresentationTheory.RingTheory.EndomorphismRelationAction
import RepresentationTheory.RingTheory.OrderedMonomialBasis
import RepresentationTheory.Alignment.Attribute

/-!
# Polynomial bimodules for Weyl-type algebras

A polynomial carrier with two commuting actions of a Weyl-type complex algebra.
-/

open scoped TensorProduct
open Polynomial nonZeroDivisors

namespace RepresentationTheory.Algebra.WeylAlgebra.PolynomialBimodule

noncomputable section

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

private def φ : ℂ[X] →ₐ[ℂ] RatFunc ℂ := Polynomial.aeval (RatFunc.X + 1 : RatFunc ℂ)

private lemma hφ : (ℂ[X])⁰ ≤ (RatFunc ℂ)⁰.comap (φ : ℂ[X] →+* RatFunc ℂ) := by
  intro p hp
  rw [mem_nonZeroDivisors_iff_ne_zero] at hp
  rw [Submonoid.mem_comap, mem_nonZeroDivisors_iff_ne_zero]
  intro h
  exact hp (transcendental_iff.mp transcendental_X_add_one p h)

private def f : RatFunc ℂ →ₐ[ℂ] RatFunc ℂ := RatFunc.liftAlgHom φ hφ

private lemma f_X : f (RatFunc.X : RatFunc ℂ) = RatFunc.X + 1 := by
  have h := RatFunc.liftAlgHom_apply_div φ hφ Polynomial.X 1
  simpa [f, φ, RatFunc.algebraMap_X] using h

/-- The tensor product over the complex numbers of the rational-function field with itself is not a field. -/
@[source_ref "Chapter3/Remark3.10.3" (role := supporting)]
theorem not_isField_tensorProduct_ratFunc_self :
    ¬ IsField (RatFunc ℂ ⊗[ℂ] RatFunc ℂ) := by
  intro hF
  set t : RatFunc ℂ ⊗[ℂ] RatFunc ℂ :=
    RatFunc.X ⊗ₜ[ℂ] 1 - 1 ⊗ₜ[ℂ] RatFunc.X with ht_def

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

  obtain ⟨s, hs⟩ := hF.mul_inv_cancel ht

  have hμt : Algebra.TensorProduct.lmul' (S := RatFunc ℂ) ℂ t = 0 := by
    simp [ht_def, map_sub, Algebra.TensorProduct.lmul'_apply_tmul]
  have hcontra := congrArg (Algebra.TensorProduct.lmul' (S := RatFunc ℂ) ℂ) hs
  rw [map_mul, map_one, hμt, zero_mul] at hcontra
  exact zero_ne_one hcontra

open MvPolynomial

/-- The polynomial carrier for two commuting actions of a Weyl-type complex algebra. -/
abbrev PolynomialCarrier := MvPolynomial (Fin 2) ℂ

/-- An auxiliary pair of complex-linear endomorphisms of the polynomial carrier. -/
noncomputable def endomorphismPair_aux1 (i : Fin 2) : Module.End ℂ PolynomialCarrier where
  toFun p := X i * p
  map_add' _ _ := mul_add _ _ _
  map_smul' c p := by
    simp only [MvPolynomial.smul_eq_C_mul, RingHom.id_apply]
    ring

/-- A second auxiliary pair of complex-linear endomorphisms of the polynomial carrier. -/
noncomputable def endomorphismPair_aux2 (i : Fin 2) : Module.End ℂ PolynomialCarrier :=
  (pderiv i).toLinearMap

private lemma partials_commute (i j : Fin 2) :
    endomorphismPair_aux2 i * endomorphismPair_aux2 j = endomorphismPair_aux2 j * endomorphismPair_aux2 i := by
  have hbracket : ⁅(pderiv i : Derivation ℂ PolynomialCarrier
      PolynomialCarrier), pderiv j⁆ =
      (0 : Derivation ℂ PolynomialCarrier PolynomialCarrier) := by
    apply MvPolynomial.derivation_ext
    intro l
    fin_cases i <;> fin_cases j <;> fin_cases l <;>
      simp [Derivation.commutator_apply]
  apply LinearMap.ext
  intro p
  have hp := DFunLike.congr_fun hbracket p
  simpa [endomorphismPair_aux2, Derivation.commutator_apply, Module.End.mul_apply] using sub_eq_zero.mp hp

private lemma partial_mulVar_self (i : Fin 2) :
    endomorphismPair_aux2 i * endomorphismPair_aux1 i = endomorphismPair_aux1 i * endomorphismPair_aux2 i + 1 := by
  apply LinearMap.ext
  intro p
  simp [endomorphismPair_aux2, endomorphismPair_aux1, Module.End.mul_apply]

private lemma partial_mulVar_of_ne {i j : Fin 2} (h : j ≠ i) :
    endomorphismPair_aux2 i * endomorphismPair_aux1 j = endomorphismPair_aux1 j * endomorphismPair_aux2 i := by
  apply LinearMap.ext
  intro p
  simp [endomorphismPair_aux2, endomorphismPair_aux1, Module.End.mul_apply,
    MvPolynomial.pderiv_X_of_ne h]

private lemma mulVars_commute (i j : Fin 2) :
    endomorphismPair_aux1 i * endomorphismPair_aux1 j = endomorphismPair_aux1 j * endomorphismPair_aux1 i := by
  apply LinearMap.ext
  intro p
  simp [endomorphismPair_aux1, Module.End.mul_apply]
  ring

/-- The first complex-linear endomorphism in the left action on the polynomial carrier. -/
noncomputable def leftFirstOperator : Module.End ℂ PolynomialCarrier := endomorphismPair_aux1 0

/-- The second complex-linear endomorphism in the left action on the polynomial carrier. -/
noncomputable def leftSecondOperator : Module.End ℂ PolynomialCarrier := endomorphismPair_aux2 0 + endomorphismPair_aux1 1

/-- The first complex-linear endomorphism in the right action on the polynomial carrier. -/
noncomputable def rightFirstOperator : Module.End ℂ PolynomialCarrier := endomorphismPair_aux1 1

/-- The second complex-linear endomorphism in the right action on the polynomial carrier. -/
noncomputable def rightSecondOperator : Module.End ℂ PolynomialCarrier := endomorphismPair_aux2 1 + endomorphismPair_aux1 0

/-- The product of the second and first left operators equals the reverse product plus the identity. -/
theorem leftSecondOperator_mul_leftFirstOperator : leftSecondOperator * leftFirstOperator = leftFirstOperator * leftSecondOperator + 1 := by
  rw [leftSecondOperator, leftFirstOperator, add_mul, partial_mulVar_self, mul_add, mulVars_commute 1 0]
  abel

/-- The product of the second and first right operators equals the reverse product plus the identity. -/
theorem rightSecondOperator_mul_rightFirstOperator : rightSecondOperator * rightFirstOperator = rightFirstOperator * rightSecondOperator + 1 := by
  rw [rightSecondOperator, rightFirstOperator, add_mul, partial_mulVar_self, mul_add, mulVars_commute 0 1]
  abel

/-- The first left operator commutes with the first right operator. -/
theorem leftFirstOperator_commute_rightFirstOperator : Commute leftFirstOperator rightFirstOperator := by
  change leftFirstOperator * rightFirstOperator = rightFirstOperator * leftFirstOperator
  simpa [leftFirstOperator, rightFirstOperator] using mulVars_commute 0 1

/-- The first left operator commutes with the second right operator. -/
theorem leftFirstOperator_commute_rightSecondOperator : Commute leftFirstOperator rightSecondOperator := by
  change leftFirstOperator * rightSecondOperator = rightSecondOperator * leftFirstOperator
  rw [leftFirstOperator, rightSecondOperator, mul_add, add_mul,
    ← partial_mulVar_of_ne (by decide : (0 : Fin 2) ≠ 1)]

/-- The second left operator commutes with the first right operator. -/
theorem leftSecondOperator_commute_rightFirstOperator : Commute leftSecondOperator rightFirstOperator := by
  change leftSecondOperator * rightFirstOperator = rightFirstOperator * leftSecondOperator
  rw [leftSecondOperator, rightFirstOperator, add_mul, mul_add,
    partial_mulVar_of_ne (by decide : (1 : Fin 2) ≠ 0), mulVars_commute 1 1]

/-- The second left operator commutes with the second right operator. -/
theorem leftSecondOperator_commute_rightSecondOperator : Commute leftSecondOperator rightSecondOperator := by
  apply LinearMap.ext
  intro p
  have hp := LinearMap.congr_fun (partials_commute 0 1) p
  dsimp [leftSecondOperator, rightSecondOperator, endomorphismPair_aux2, endomorphismPair_aux1] at hp ⊢
  simp only [map_add, Derivation.leibniz, pderiv_X_self, smul_eq_mul] at ⊢
  rw [hp]
  ring

/-- The left algebra action on the polynomial carrier by complex-linear endomorphisms. -/
noncomputable def leftPolynomialRepresentation :
    RepresentationTheory.FreeAlgebra.PolynomialOperators.OperatorAlgebra ℂ →ₐ[ℂ] Module.End ℂ PolynomialCarrier :=
  RepresentationTheory.FreeAlgebra.PolynomialOperators.OperatorAlgebra.endomorphismAction ℂ PolynomialCarrier leftFirstOperator leftSecondOperator leftSecondOperator_mul_leftFirstOperator

/-- The right algebra action on the polynomial carrier by complex-linear endomorphisms. -/
noncomputable def rightPolynomialRepresentation :
    RepresentationTheory.FreeAlgebra.PolynomialOperators.OperatorAlgebra ℂ →ₐ[ℂ] Module.End ℂ PolynomialCarrier :=
  RepresentationTheory.FreeAlgebra.PolynomialOperators.OperatorAlgebra.endomorphismAction ℂ PolynomialCarrier rightFirstOperator rightSecondOperator rightSecondOperator_mul_rightFirstOperator

/-- Every endomorphism from the left polynomial representation commutes with every endomorphism from the right representation. -/
theorem left_right_polynomialRepresentations_commute (a b : RepresentationTheory.FreeAlgebra.PolynomialOperators.OperatorAlgebra ℂ) :
    Commute (leftPolynomialRepresentation a) (rightPolynomialRepresentation b) := by
  have commute_second (T : Module.End ℂ PolynomialCarrier)
      (hx : Commute T rightFirstOperator) (hy : Commute T rightSecondOperator) :
      ∀ b : RepresentationTheory.FreeAlgebra.PolynomialOperators.OperatorAlgebra ℂ, Commute T (rightPolynomialRepresentation b) := by
    intro b
    refine RepresentationTheory.FreeAlgebra.PolynomialOperators.OperatorAlgebra.induction_on (p := fun b => Commute T (rightPolynomialRepresentation b))
      ℂ b ?_ ?_ ?_ ?_ ?_
    · simpa [rightPolynomialRepresentation] using hx
    · simpa [rightPolynomialRepresentation] using hy
    · intro c
      rw [AlgHom.commutes]
      exact Algebra.commutes c T |>.symm
    · intro u v hu hv
      rw [map_add]
      exact hu.add_right hv
    · intro u v hu hv
      rw [map_mul]
      exact hu.mul_right hv
  refine RepresentationTheory.FreeAlgebra.PolynomialOperators.OperatorAlgebra.induction_on
    (p := fun a => Commute (leftPolynomialRepresentation a) (rightPolynomialRepresentation b)) ℂ a ?_ ?_ ?_ ?_ ?_
  · simpa [leftPolynomialRepresentation] using
      commute_second leftFirstOperator leftFirstOperator_commute_rightFirstOperator leftFirstOperator_commute_rightSecondOperator b
  · simpa [leftPolynomialRepresentation] using
      commute_second leftSecondOperator leftSecondOperator_commute_rightFirstOperator leftSecondOperator_commute_rightSecondOperator b
  · intro c
    rw [AlgHom.commutes]
    exact Algebra.commutes c (rightPolynomialRepresentation b)
  · intro u v hu hv
    rw [map_add]
    exact hu.add_left hv
  · intro u v hu hv
    rw [map_mul]
    exact hu.mul_left hv

/-- The tensor-product algebra representation on the polynomial carrier. -/
noncomputable def tensorProductPolynomialRepresentation :
    (RepresentationTheory.FreeAlgebra.PolynomialOperators.OperatorAlgebra ℂ ⊗[ℂ] RepresentationTheory.FreeAlgebra.PolynomialOperators.OperatorAlgebra ℂ) →ₐ[ℂ]
      Module.End ℂ PolynomialCarrier :=
  Algebra.TensorProduct.lift leftPolynomialRepresentation rightPolynomialRepresentation left_right_polynomialRepresentations_commute

/-- The module structure on the polynomial carrier over the tensor product of the two acting algebras. -/
@[reducible] noncomputable def polynomialTensorProductModule :
    Module (RepresentationTheory.FreeAlgebra.PolynomialOperators.OperatorAlgebra ℂ ⊗[ℂ] RepresentationTheory.FreeAlgebra.PolynomialOperators.OperatorAlgebra ℂ)
      PolynomialCarrier :=
  Module.compHom PolynomialCarrier tensorProductPolynomialRepresentation.toRingHom

/-- On a pure tensor, the tensor-product representation is the product of the corresponding left and right actions. -/
@[simp] theorem tensorProductPolynomialRepresentation_tmul (a b : RepresentationTheory.FreeAlgebra.PolynomialOperators.OperatorAlgebra ℂ) :
  tensorProductPolynomialRepresentation (a ⊗ₜ[ℂ] b) = leftPolynomialRepresentation a * rightPolynomialRepresentation b := by
  exact Algebra.TensorProduct.lift_tmul _ _ _ _ _

/-- The left polynomial representation sends the first distinguished algebra element to the first left operator. -/
@[simp] theorem leftPolynomialRepresentation_firstDistinguishedElement : leftPolynomialRepresentation (RepresentationTheory.FreeAlgebra.PolynomialOperators.OperatorAlgebra.firstOperator ℂ) = leftFirstOperator := by
  simp [leftPolynomialRepresentation]

/-- The left polynomial representation sends the second distinguished algebra element to the second left operator. -/
@[simp] theorem leftPolynomialRepresentation_secondDistinguishedElement : leftPolynomialRepresentation (RepresentationTheory.FreeAlgebra.PolynomialOperators.OperatorAlgebra.secondOperator ℂ) = leftSecondOperator := by
  simp [leftPolynomialRepresentation]

/-- The right polynomial representation sends the first distinguished algebra element to the first right operator. -/
@[simp] theorem rightPolynomialRepresentation_firstDistinguishedElement : rightPolynomialRepresentation (RepresentationTheory.FreeAlgebra.PolynomialOperators.OperatorAlgebra.firstOperator ℂ) = rightFirstOperator := by
  simp [rightPolynomialRepresentation]

/-- The right polynomial representation sends the second distinguished algebra element to the second right operator. -/
@[simp] theorem rightPolynomialRepresentation_secondDistinguishedElement : rightPolynomialRepresentation (RepresentationTheory.FreeAlgebra.PolynomialOperators.OperatorAlgebra.secondOperator ℂ) = rightSecondOperator := by
  simp [rightPolynomialRepresentation]

/-- On the unit polynomial, the two actions exchange the values of two distinguished algebra elements. -/
theorem left_right_distinguishedElement_actions_one :
    leftPolynomialRepresentation (RepresentationTheory.FreeAlgebra.PolynomialOperators.OperatorAlgebra.secondOperator ℂ) 1 =
        rightPolynomialRepresentation (RepresentationTheory.FreeAlgebra.PolynomialOperators.OperatorAlgebra.firstOperator ℂ) 1 ∧
      rightPolynomialRepresentation (RepresentationTheory.FreeAlgebra.PolynomialOperators.OperatorAlgebra.secondOperator ℂ) 1 =
        leftPolynomialRepresentation (RepresentationTheory.FreeAlgebra.PolynomialOperators.OperatorAlgebra.firstOperator ℂ) 1 := by
  constructor <;>
    simp [leftSecondOperator, leftFirstOperator, rightSecondOperator, rightFirstOperator, endomorphismPair_aux2, endomorphismPair_aux1]

private lemma pderiv_zero_bivariate_C (p : ℂ[X]) :
    pderiv 0 (Polynomial.Bivariate.equivMvPolynomial ℂ (Polynomial.C p)) =
      Polynomial.Bivariate.equivMvPolynomial ℂ (Polynomial.C p.derivative) := by
  simpa using Polynomial.Bivariate.pderiv_zero_equivMvPolynomial (R := ℂ) (Polynomial.C p)

/-- The polynomial carrier is simple as a module over the tensor product algebra. -/
@[source_ref "Chapter3/Remark3.10.3" (role := supporting)]
theorem polynomialTensorProductModule_isSimpleModule :
    letI := polynomialTensorProductModule
    IsSimpleModule (RepresentationTheory.FreeAlgebra.PolynomialOperators.OperatorAlgebra ℂ ⊗[ℂ] RepresentationTheory.FreeAlgebra.PolynomialOperators.OperatorAlgebra ℂ)
      PolynomialCarrier := by
  classical
  letI := polynomialTensorProductModule
  let A := RepresentationTheory.FreeAlgebra.PolynomialOperators.OperatorAlgebra ℂ ⊗[ℂ] RepresentationTheory.FreeAlgebra.PolynomialOperators.OperatorAlgebra ℂ
  refine { exists_pair_ne := ⟨⊥, ⊤, bot_ne_top⟩, eq_bot_or_eq_top := fun S => ?_ }
  rcases eq_or_ne S ⊥ with rfl | hS
  · exact Or.inl rfl
  right
  obtain ⟨p, hpS, hp0⟩ := (Submodule.ne_bot_iff S).mp hS
  have hact (a : A) (q : PolynomialCarrier) : a • q = tensorProductPolynomialRepresentation a q := rfl
  have hX0 (q : PolynomialCarrier) (hq : q ∈ S) : X 0 * q ∈ S := by
    have := S.smul_mem ((RepresentationTheory.FreeAlgebra.PolynomialOperators.OperatorAlgebra.firstOperator ℂ) ⊗ₜ[ℂ] (1 : RepresentationTheory.FreeAlgebra.PolynomialOperators.OperatorAlgebra ℂ)) hq
    simpa [hact, tensorProductPolynomialRepresentation_tmul, leftFirstOperator, endomorphismPair_aux1, Module.End.mul_apply] using this
  have hX1 (q : PolynomialCarrier) (hq : q ∈ S) : X 1 * q ∈ S := by
    have := S.smul_mem ((1 : RepresentationTheory.FreeAlgebra.PolynomialOperators.OperatorAlgebra ℂ) ⊗ₜ[ℂ] RepresentationTheory.FreeAlgebra.PolynomialOperators.OperatorAlgebra.firstOperator ℂ) hq
    simpa [hact, tensorProductPolynomialRepresentation_tmul, rightFirstOperator, endomorphismPair_aux1, Module.End.mul_apply] using this
  have hD0 (q : PolynomialCarrier) (hq : q ∈ S) : pderiv 0 q ∈ S := by
    have := S.smul_mem
      (((RepresentationTheory.FreeAlgebra.PolynomialOperators.OperatorAlgebra.secondOperator ℂ) ⊗ₜ[ℂ] (1 : RepresentationTheory.FreeAlgebra.PolynomialOperators.OperatorAlgebra ℂ)) -
        ((1 : RepresentationTheory.FreeAlgebra.PolynomialOperators.OperatorAlgebra ℂ) ⊗ₜ[ℂ] RepresentationTheory.FreeAlgebra.PolynomialOperators.OperatorAlgebra.firstOperator ℂ)) hq
    simpa [sub_smul, hact, tensorProductPolynomialRepresentation_tmul, leftSecondOperator, rightFirstOperator, endomorphismPair_aux2, endomorphismPair_aux1,
      Module.End.mul_apply] using this
  have hD1 (q : PolynomialCarrier) (hq : q ∈ S) : pderiv 1 q ∈ S := by
    have := S.smul_mem
      (((1 : RepresentationTheory.FreeAlgebra.PolynomialOperators.OperatorAlgebra ℂ) ⊗ₜ[ℂ] RepresentationTheory.FreeAlgebra.PolynomialOperators.OperatorAlgebra.secondOperator ℂ) -
        ((RepresentationTheory.FreeAlgebra.PolynomialOperators.OperatorAlgebra.firstOperator ℂ) ⊗ₜ[ℂ] (1 : RepresentationTheory.FreeAlgebra.PolynomialOperators.OperatorAlgebra ℂ))) hq
    simpa [sub_smul, hact, tensorProductPolynomialRepresentation_tmul, rightSecondOperator, leftFirstOperator, endomorphismPair_aux2, endomorphismPair_aux1,
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
  have hone : (1 : PolynomialCarrier) ∈ S := by
    rw [hact, tensorProductPolynomialRepresentation.commutes] at hscale
    change c⁻¹ • MvPolynomial.C c ∈ S at hscale
    rw [MvPolynomial.smul_eq_C_mul, ← MvPolynomial.C_mul] at hscale
    simpa [hc0] using hscale
  have hC (d : ℂ) : MvPolynomial.C d ∈ S := by
    have hs := S.smul_mem (algebraMap ℂ A d) hone
    rw [hact, tensorProductPolynomialRepresentation.commutes] at hs
    simpa [MvPolynomial.smul_eq_C_mul] using hs
  have hall : ∀ z : PolynomialCarrier, z ∈ S := by
    intro z
    induction z using MvPolynomial.induction_on with
    | C d => exact hC d
    | add u v hu hv => exact S.add_mem hu hv
    | mul_X u i hu =>
        fin_cases i
        · simpa [mul_comm] using hX0 u hu
        · simpa [mul_comm] using hX1 u hu
  exact hall z

/-- The tensor-product polynomial representation does not factor through any finite-dimensional complex algebra. -/
theorem tensorProductPolynomialRepresentation_not_factor_finiteDimensional
    (Q : Type*) [Ring Q] [Algebra ℂ Q] [FiniteDimensional ℂ Q]
    (q : (RepresentationTheory.FreeAlgebra.PolynomialOperators.OperatorAlgebra ℂ ⊗[ℂ] RepresentationTheory.FreeAlgebra.PolynomialOperators.OperatorAlgebra ℂ) →ₐ[ℂ] Q)
    (r : Q →ₐ[ℂ] Module.End ℂ PolynomialCarrier) :
    tensorProductPolynomialRepresentation ≠ r.comp q := by
  classical
  intro hfactor
  let A := RepresentationTheory.FreeAlgebra.PolynomialOperators.OperatorAlgebra ℂ ⊗[ℂ] RepresentationTheory.FreeAlgebra.PolynomialOperators.OperatorAlgebra ℂ
  letI := polynomialTensorProductModule
  letI : IsSimpleModule A PolynomialCarrier := polynomialTensorProductModule_isSimpleModule
  let orbitQ : Q →ₗ[ℂ] PolynomialCarrier := {
    toFun a := r a 1
    map_add' a b := by simp
    map_smul' c a := by simp }
  have horbitQ : Function.Surjective orbitQ := by
    intro p
    obtain ⟨a, ha⟩ := IsSimpleModule.toSpanSingleton_surjective A (one_ne_zero :
      (1 : PolynomialCarrier) ≠ 0) p
    refine ⟨q a, ?_⟩
    change r (q a) 1 = p
    rw [← AlgHom.comp_apply, ← hfactor]
    exact ha
  letI : FiniteDimensional ℂ PolynomialCarrier :=
    FiniteDimensional.of_surjective orbitQ horbitQ
  have hfinrank : Module.finrank ℂ PolynomialCarrier = 0 :=
    MvPolynomial.finrank_eq_zero
  exact one_ne_zero (finrank_zero_iff_forall_zero.mp hfinrank 1)

private noncomputable def weylBasis :
    Module.Basis (ℕ × ℕ) ℂ (RepresentationTheory.FreeAlgebra.PolynomialOperators.OperatorAlgebra ℂ) :=
  Module.Basis.mk (RepresentationTheory.FreeAlgebra.PolynomialOperators.polynomialOperators_basis (k := ℂ)).1
    (RepresentationTheory.FreeAlgebra.PolynomialOperators.polynomialOperators_basis (k := ℂ)).2

private noncomputable def bivariateBasis :
    Module.Basis (ℕ × ℕ) ℂ PolynomialCarrier :=
  (MvPolynomial.basisMonomials (Fin 2) ℂ).reindex
    (finTwoArrowEquiv' ℕ)

private theorem bivariateBasis_apply (i j : ℕ) :
    bivariateBasis (i, j) = X 0 ^ i * X 1 ^ j := by
  rw [bivariateBasis, Module.Basis.reindex_apply, MvPolynomial.coe_basisMonomials]
  simp [finTwoArrowEquiv', MvPolynomial.monomial_eq]

/-- A complex-linear equivalence between the Weyl-type algebra and its polynomial normal-form carrier. -/
noncomputable def normalFormLinearEquiv :
    RepresentationTheory.FreeAlgebra.PolynomialOperators.OperatorAlgebra ℂ ≃ₗ[ℂ] PolynomialCarrier :=
  weylBasis.equiv bivariateBasis (Equiv.refl (ℕ × ℕ))

/-- The normal-form equivalence sends the algebra element indexed by two natural numbers to the corresponding product of polynomial-variable powers. -/
@[simp] theorem normalFormLinearEquiv_indexedElement (i j : ℕ) :
    normalFormLinearEquiv (RepresentationTheory.FreeAlgebra.PolynomialOperators.OperatorAlgebra.monomialOperator ℂ i j) = X 0 ^ i * X 1 ^ j := by
  rw [← show weylBasis (i, j) = RepresentationTheory.FreeAlgebra.PolynomialOperators.OperatorAlgebra.monomialOperator ℂ i j by
    exact Module.Basis.mk_apply _ _ _]
  rw [normalFormLinearEquiv, Module.Basis.equiv_apply, bivariateBasis_apply]
  rfl

/-- The complex-linear polynomial normal-form map from the Weyl-type algebra. -/
noncomputable def normalFormLinearMap :
    RepresentationTheory.FreeAlgebra.PolynomialOperators.OperatorAlgebra ℂ →ₗ[ℂ] PolynomialCarrier where
  toFun a := leftPolynomialRepresentation a 1
  map_add' a b := by simp
  map_smul' c a := by simp

private lemma firstY_pow_one (j : ℕ) :
    (leftSecondOperator ^ j) (1 : PolynomialCarrier) = X 1 ^ j := by
  induction j with
  | zero => simp
  | succ j ih =>
      rw [pow_succ', Module.End.mul_apply, ih]
      simp only [leftSecondOperator, endomorphismPair_aux2, Fin.isValue, endomorphismPair_aux1, LinearMap.add_apply,
        Derivation.coeFn_coe, Derivation.leibniz_pow, pderiv_X, ne_eq, one_ne_zero,
        not_false_eq_true, Pi.single_eq_of_ne, smul_eq_mul, mul_zero, nsmul_zero,
        LinearMap.coe_mk, AddHom.coe_mk, zero_add]
      rw [mul_comm, pow_succ]

/-- The normal-form map sends the algebra element indexed by two natural numbers to the corresponding product of powers of the first two polynomial variables. -/
@[simp] theorem normalFormLinearMap_indexedElement (i j : ℕ) :
    normalFormLinearMap (RepresentationTheory.FreeAlgebra.PolynomialOperators.OperatorAlgebra.monomialOperator ℂ i j) = X 0 ^ i * X 1 ^ j := by
  change leftPolynomialRepresentation (RepresentationTheory.FreeAlgebra.PolynomialOperators.OperatorAlgebra.monomialOperator ℂ i j) 1 = _
  rw [RepresentationTheory.FreeAlgebra.PolynomialOperators.OperatorAlgebra.monomialOperator, map_mul, map_pow, map_pow,
    Module.End.mul_apply, leftPolynomialRepresentation_firstDistinguishedElement, leftPolynomialRepresentation_secondDistinguishedElement, firstY_pow_one]
  induction i with
  | zero => simp
  | succ i ih =>
      rw [pow_succ', Module.End.mul_apply, ih]
      simp [leftFirstOperator, endomorphismPair_aux1]
      ring

/-- The linear map underlying the normal-form equivalence is the polynomial normal-form map. -/
theorem normalFormLinearEquiv_toLinearMap :
    normalFormLinearEquiv.toLinearMap = normalFormLinearMap := by
  apply weylBasis.ext
  intro p
  rw [show weylBasis p = RepresentationTheory.FreeAlgebra.PolynomialOperators.OperatorAlgebra.monomialOperator ℂ p.1 p.2 by
    exact Module.Basis.mk_apply _ _ _]
  simp [normalFormLinearEquiv_indexedElement, normalFormLinearMap_indexedElement]

/-- An auxiliary module structure over the Weyl-type algebra on the polynomial carrier. -/
@[reducible] noncomputable def polynomialAlgebraModule_aux1 :
    Module (RepresentationTheory.FreeAlgebra.PolynomialOperators.OperatorAlgebra ℂ) PolynomialCarrier :=
  Module.compHom PolynomialCarrier leftPolynomialRepresentation.toRingHom

/-- A second auxiliary module structure over the Weyl-type algebra on the polynomial carrier. -/
local instance polynomialAlgebraModule_aux2 : Module (RepresentationTheory.FreeAlgebra.PolynomialOperators.OperatorAlgebra ℂ) PolynomialCarrier :=
  polynomialAlgebraModule_aux1

private noncomputable def firstOrbitLinear :
    RepresentationTheory.FreeAlgebra.PolynomialOperators.OperatorAlgebra ℂ →ₗ[RepresentationTheory.FreeAlgebra.PolynomialOperators.OperatorAlgebra ℂ] PolynomialCarrier where
  toFun a := leftPolynomialRepresentation a 1
  map_add' a b := by simp
  map_smul' a b := by
    change leftPolynomialRepresentation (a * b) 1 = leftPolynomialRepresentation a (leftPolynomialRepresentation b 1)
    rw [map_mul, Module.End.mul_apply]

private theorem firstOrbitLinear_bijective : Function.Bijective firstOrbitLinear := by
  have h : Function.Bijective normalFormLinearMap := by
    rw [← normalFormLinearEquiv_toLinearMap]
    exact normalFormLinearEquiv.bijective
  constructor
  · intro a b hab
    exact h.1 hab
  · intro p
    exact h.2 p

/-- A module-linear equivalence from the regular module to the polynomial normal-form module. -/
noncomputable def regularLinearEquivPolynomialNormalForm :
    RepresentationTheory.FreeAlgebra.PolynomialOperators.OperatorAlgebra ℂ ≃ₗ[RepresentationTheory.FreeAlgebra.PolynomialOperators.OperatorAlgebra ℂ] PolynomialCarrier :=
  LinearEquiv.ofBijective firstOrbitLinear firstOrbitLinear_bijective

/-- The regular-module equivalence sends an algebra element to its left action on the unit polynomial. -/
@[simp] theorem regularLinearEquivPolynomialNormalForm_apply (a : RepresentationTheory.FreeAlgebra.PolynomialOperators.OperatorAlgebra ℂ) :
    regularLinearEquivPolynomialNormalForm a = leftPolynomialRepresentation a 1 := rfl

/-- If a nonzero element of a domain cannot be multiplied on the left to obtain one, no submodule of the regular module is simple. -/
theorem submodule_not_isSimpleModule_of_no_mul_eq_one
    (R : Type*) [Ring R] [Nontrivial R] [NoZeroDivisors R]
    (y : R) (hy : y ≠ 0) (hyleft : ∀ r : R, r * y ≠ 1)
    (I : Submodule R R) : ¬ IsSimpleModule R I := by
  intro hI
  letI : IsSimpleModule R I := hI
  letI : Nontrivial I := IsSimpleModule.nontrivial R I
  obtain ⟨a, ha⟩ := exists_ne (0 : I)
  have hya : y • a ≠ 0 := by
    intro h
    apply ha
    apply Subtype.ext
    have hval : y * (a : R) = 0 := congrArg Subtype.val h
    exact (mul_eq_zero.mp hval).resolve_left hy
  obtain ⟨r, hr⟩ := IsSimpleModule.toSpanSingleton_surjective R hya a
  simp only [LinearMap.toSpanSingleton_apply] at hr
  have hmul : (r * y) * (a : R) = 1 * (a : R) := by
    simpa [smul_smul] using congrArg Subtype.val hr
  exact hyleft r (mul_right_cancel₀ (Subtype.coe_ne_coe.mpr ha) hmul)

/-- No element of the Weyl-type complex algebra multiplied by its second distinguished algebra element equals one. -/
theorem mul_secondDistinguishedElement_ne_one (r : RepresentationTheory.FreeAlgebra.PolynomialOperators.OperatorAlgebra ℂ) :
    r * RepresentationTheory.FreeAlgebra.PolynomialOperators.OperatorAlgebra.secondOperator ℂ ≠ 1 := by
  intro h
  have hop := congrArg (fun f : Module.End ℂ (Polynomial ℂ) => f 1)
    (congrArg (RepresentationTheory.FreeAlgebra.PolynomialOperators.toPolynomialEnd ℂ) h)
  simp [map_mul, RepresentationTheory.FreeAlgebra.PolynomialOperators.toPolynomialEnd_secondOperator] at hop

/-- No submodule of the regular module of the Weyl-type complex algebra is simple. -/
theorem regularSubmodule_not_isSimpleModule
    (I : Submodule (RepresentationTheory.FreeAlgebra.PolynomialOperators.OperatorAlgebra ℂ) (RepresentationTheory.FreeAlgebra.PolynomialOperators.OperatorAlgebra ℂ)) :
    ¬ IsSimpleModule (RepresentationTheory.FreeAlgebra.PolynomialOperators.OperatorAlgebra ℂ) I := by
  have hy : RepresentationTheory.FreeAlgebra.PolynomialOperators.OperatorAlgebra.secondOperator ℂ ≠ 0 := by
    rw [show RepresentationTheory.FreeAlgebra.PolynomialOperators.OperatorAlgebra.secondOperator ℂ = RepresentationTheory.FreeAlgebra.PolynomialOperators.OperatorAlgebra.monomialOperator ℂ 0 1 by
      simp [RepresentationTheory.FreeAlgebra.PolynomialOperators.OperatorAlgebra.monomialOperator]]
    exact (RepresentationTheory.FreeAlgebra.PolynomialOperators.polynomialOperators_basis (k := ℂ)).1.ne_zero (0, 1)
  letI : Nontrivial (RepresentationTheory.FreeAlgebra.PolynomialOperators.OperatorAlgebra ℂ) := ⟨⟨RepresentationTheory.FreeAlgebra.PolynomialOperators.OperatorAlgebra.secondOperator ℂ, 0, hy⟩⟩
  exact submodule_not_isSimpleModule_of_no_mul_eq_one _ (RepresentationTheory.FreeAlgebra.PolynomialOperators.OperatorAlgebra.secondOperator ℂ)
    hy mul_secondDistinguishedElement_ne_one I

/-- The polynomial tensor-product-algebra module cannot be obtained from the stated equivariant tensor product of two modules when the first is simple and the second is nontrivial. -/
@[source_ref "Chapter3/Remark3.10.3" (role := primary)]
theorem not_equivariant_tensorProductFactorization
    (V W : Type*)
    [AddCommGroup V] [Module ℂ V]
    [Module (RepresentationTheory.FreeAlgebra.PolynomialOperators.OperatorAlgebra ℂ) V]
    [IsScalarTower ℂ (RepresentationTheory.FreeAlgebra.PolynomialOperators.OperatorAlgebra ℂ) V]
    [AddCommGroup W] [Module ℂ W]
    [Module (RepresentationTheory.FreeAlgebra.PolynomialOperators.OperatorAlgebra ℂ) W]
    [IsScalarTower ℂ (RepresentationTheory.FreeAlgebra.PolynomialOperators.OperatorAlgebra ℂ) W]
    [IsSimpleModule (RepresentationTheory.FreeAlgebra.PolynomialOperators.OperatorAlgebra ℂ) V] [Nontrivial W]
    (e : V ⊗[ℂ] W ≃ₗ[ℂ] PolynomialCarrier)
    (hequiv : ∀ (a b : RepresentationTheory.FreeAlgebra.PolynomialOperators.OperatorAlgebra ℂ) (t : V ⊗[ℂ] W),
      e (TensorProduct.map
          ((Algebra.lsmul ℂ ℂ V : RepresentationTheory.FreeAlgebra.PolynomialOperators.OperatorAlgebra ℂ →ₐ[ℂ] Module.End ℂ V) a)
          ((Algebra.lsmul ℂ ℂ W : RepresentationTheory.FreeAlgebra.PolynomialOperators.OperatorAlgebra ℂ →ₐ[ℂ] Module.End ℂ W) b) t) =
        tensorProductPolynomialRepresentation (a ⊗ₜ[ℂ] b) (e t)) : False := by
  classical
  let R := RepresentationTheory.FreeAlgebra.PolynomialOperators.OperatorAlgebra ℂ
  obtain ⟨w, hw⟩ := exists_ne (0 : W)
  obtain ⟨ψ, hψ⟩ := Module.Projective.exists_dual_eq_one ℂ hw
  let f : V →ₗ[R] PolynomialCarrier :=
    { toFun := fun v => e (v ⊗ₜ[ℂ] w)
      map_add' := fun v v' => by
        rw [TensorProduct.add_tmul, map_add]
      map_smul' := fun a v => by
        change e ((a • v) ⊗ₜ[ℂ] w) = leftPolynomialRepresentation a (e (v ⊗ₜ[ℂ] w))
        have h := hequiv a 1 (v ⊗ₜ[ℂ] w)
        simpa [TensorProduct.map_tmul, Algebra.lsmul_coe, Module.End.mul_apply] using h }
  have hf : Function.Injective f := by
    intro v v' hv
    have ht : v ⊗ₜ[ℂ] w = v' ⊗ₜ[ℂ] w := e.injective hv
    have hmap := congrArg
      (fun z : V ⊗[ℂ] W =>
        (TensorProduct.rid ℂ V) (TensorProduct.map LinearMap.id ψ z)) ht
    simpa [TensorProduct.map_tmul, TensorProduct.rid_tmul, hψ] using hmap
  let g : V →ₗ[R] R := regularLinearEquivPolynomialNormalForm.symm.toLinearMap.comp f
  have hg : Function.Injective g := regularLinearEquivPolynomialNormalForm.symm.injective.comp hf
  let I : Submodule R R := LinearMap.range g
  letI : IsSimpleModule R I :=
    (LinearEquiv.isSimpleModule_iff (LinearEquiv.ofInjective g hg)).mp inferInstance
  exact regularSubmodule_not_isSimpleModule I inferInstance

end

end RepresentationTheory.Algebra.WeylAlgebra.PolynomialBimodule
