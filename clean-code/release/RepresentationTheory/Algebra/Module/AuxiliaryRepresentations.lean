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
import RepresentationTheory.FreeAlgebra.PolynomialOperators
import RepresentationTheory.RingTheory.LexicographicIndexedBasis
import RepresentationTheory.RingTheory.EndomorphismRelationAction
import RepresentationTheory.Alignment.Attribute



open scoped TensorProduct
open Polynomial nonZeroDivisors

namespace RepresentationTheory.Algebra.Module.AuxiliaryRepresentations

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


/-- An auxiliary type. -/
abbrev AuxiliaryCarrier := MvPolynomial (Fin 2) ℂ


/-- An auxiliary pair of complex-linear endomorphisms of the auxiliary carrier. -/
noncomputable def endomorphismPair_aux1 (i : Fin 2) : Module.End ℂ AuxiliaryCarrier where
  toFun p := X i * p
  map_add' _ _ := mul_add _ _ _
  map_smul' c p := by
    simp only [MvPolynomial.smul_eq_C_mul, RingHom.id_apply]
    ring


/-- A second auxiliary pair of complex-linear endomorphisms of the auxiliary carrier. -/
noncomputable def endomorphismPair_aux2 (i : Fin 2) : Module.End ℂ AuxiliaryCarrier :=
  (pderiv i).toLinearMap

private lemma partials_commute (i j : Fin 2) :
    endomorphismPair_aux2 i * endomorphismPair_aux2 j = endomorphismPair_aux2 j * endomorphismPair_aux2 i := by
  have hbracket : ⁅(pderiv i : Derivation ℂ AuxiliaryCarrier
      AuxiliaryCarrier), pderiv j⁆ =
      (0 : Derivation ℂ AuxiliaryCarrier AuxiliaryCarrier) := by
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


/-- A first auxiliary complex-linear endomorphism of the auxiliary carrier. -/
noncomputable def auxiliaryEndomorphism1 : Module.End ℂ AuxiliaryCarrier := endomorphismPair_aux1 0


/-- A second auxiliary complex-linear endomorphism of the auxiliary carrier. -/
noncomputable def auxiliaryEndomorphism2 : Module.End ℂ AuxiliaryCarrier := endomorphismPair_aux2 0 + endomorphismPair_aux1 1


/-- A third auxiliary complex-linear endomorphism of the auxiliary carrier. -/
noncomputable def auxiliaryEndomorphism3 : Module.End ℂ AuxiliaryCarrier := endomorphismPair_aux1 1


/-- A fourth auxiliary complex-linear endomorphism of the auxiliary carrier. -/
noncomputable def auxiliaryEndomorphism4 : Module.End ℂ AuxiliaryCarrier := endomorphismPair_aux2 1 + endomorphismPair_aux1 0


/-- The product of the second and first auxiliary endomorphisms equals the reverse product plus the identity. -/
theorem auxiliaryEndomorphism2_mul_auxiliaryEndomorphism1 : auxiliaryEndomorphism2 * auxiliaryEndomorphism1 = auxiliaryEndomorphism1 * auxiliaryEndomorphism2 + 1 := by
  rw [auxiliaryEndomorphism2, auxiliaryEndomorphism1, add_mul, partial_mulVar_self, mul_add, mulVars_commute 1 0]
  abel


/-- The product of the fourth and third auxiliary endomorphisms equals the reverse product plus the identity. -/
theorem auxiliaryEndomorphism4_mul_auxiliaryEndomorphism3 : auxiliaryEndomorphism4 * auxiliaryEndomorphism3 = auxiliaryEndomorphism3 * auxiliaryEndomorphism4 + 1 := by
  rw [auxiliaryEndomorphism4, auxiliaryEndomorphism3, add_mul, partial_mulVar_self, mul_add, mulVars_commute 0 1]
  abel

/-- The first auxiliary endomorphism commutes with the third. -/
theorem auxiliaryEndomorphism1_commute_auxiliaryEndomorphism3 : Commute auxiliaryEndomorphism1 auxiliaryEndomorphism3 := by
  change auxiliaryEndomorphism1 * auxiliaryEndomorphism3 = auxiliaryEndomorphism3 * auxiliaryEndomorphism1
  simpa [auxiliaryEndomorphism1, auxiliaryEndomorphism3] using mulVars_commute 0 1

/-- The first auxiliary endomorphism commutes with the fourth. -/
theorem auxiliaryEndomorphism1_commute_auxiliaryEndomorphism4 : Commute auxiliaryEndomorphism1 auxiliaryEndomorphism4 := by
  change auxiliaryEndomorphism1 * auxiliaryEndomorphism4 = auxiliaryEndomorphism4 * auxiliaryEndomorphism1
  rw [auxiliaryEndomorphism1, auxiliaryEndomorphism4, mul_add, add_mul,
    ← partial_mulVar_of_ne (by decide : (0 : Fin 2) ≠ 1)]

/-- The second auxiliary endomorphism commutes with the third. -/
theorem auxiliaryEndomorphism2_commute_auxiliaryEndomorphism3 : Commute auxiliaryEndomorphism2 auxiliaryEndomorphism3 := by
  change auxiliaryEndomorphism2 * auxiliaryEndomorphism3 = auxiliaryEndomorphism3 * auxiliaryEndomorphism2
  rw [auxiliaryEndomorphism2, auxiliaryEndomorphism3, add_mul, mul_add,
    partial_mulVar_of_ne (by decide : (1 : Fin 2) ≠ 0), mulVars_commute 1 1]

/-- The second auxiliary endomorphism commutes with the fourth. -/
theorem auxiliaryEndomorphism2_commute_auxiliaryEndomorphism4 : Commute auxiliaryEndomorphism2 auxiliaryEndomorphism4 := by
  apply LinearMap.ext
  intro p
  have hp := LinearMap.congr_fun (partials_commute 0 1) p
  dsimp [auxiliaryEndomorphism2, auxiliaryEndomorphism4, endomorphismPair_aux2, endomorphismPair_aux1] at hp ⊢
  simp only [map_add, Derivation.leibniz, pderiv_X_self, smul_eq_mul] at ⊢
  rw [hp]
  ring


/-- A first algebra homomorphism to the complex-linear endomorphisms of the auxiliary carrier. -/
noncomputable def firstRepresentation :
    RepresentationTheory.FreeAlgebra.PolynomialOperators.AuxiliaryAlgebra ℂ →ₐ[ℂ] Module.End ℂ AuxiliaryCarrier :=
  RepresentationTheory.FreeAlgebra.PolynomialOperators.AuxiliaryAlgebra.endomorphismAction ℂ AuxiliaryCarrier auxiliaryEndomorphism1 auxiliaryEndomorphism2 auxiliaryEndomorphism2_mul_auxiliaryEndomorphism1


/-- A second algebra homomorphism to the complex-linear endomorphisms of the auxiliary carrier. -/
noncomputable def secondRepresentation :
    RepresentationTheory.FreeAlgebra.PolynomialOperators.AuxiliaryAlgebra ℂ →ₐ[ℂ] Module.End ℂ AuxiliaryCarrier :=
  RepresentationTheory.FreeAlgebra.PolynomialOperators.AuxiliaryAlgebra.endomorphismAction ℂ AuxiliaryCarrier auxiliaryEndomorphism3 auxiliaryEndomorphism4 auxiliaryEndomorphism4_mul_auxiliaryEndomorphism3


/-- Every endomorphism from the first representation commutes with every endomorphism from the second representation. -/
theorem first_second_representations_commute (a b : RepresentationTheory.FreeAlgebra.PolynomialOperators.AuxiliaryAlgebra ℂ) :
    Commute (firstRepresentation a) (secondRepresentation b) := by
  have commute_second (T : Module.End ℂ AuxiliaryCarrier)
      (hx : Commute T auxiliaryEndomorphism3) (hy : Commute T auxiliaryEndomorphism4) :
      ∀ b : RepresentationTheory.FreeAlgebra.PolynomialOperators.AuxiliaryAlgebra ℂ, Commute T (secondRepresentation b) := by
    intro b
    refine RepresentationTheory.FreeAlgebra.PolynomialOperators.AuxiliaryAlgebra.induction_on (p := fun b => Commute T (secondRepresentation b))
      ℂ b ?_ ?_ ?_ ?_ ?_
    · simpa [secondRepresentation] using hx
    · simpa [secondRepresentation] using hy
    · intro c
      rw [AlgHom.commutes]
      exact Algebra.commutes c T |>.symm
    · intro u v hu hv
      rw [map_add]
      exact hu.add_right hv
    · intro u v hu hv
      rw [map_mul]
      exact hu.mul_right hv
  refine RepresentationTheory.FreeAlgebra.PolynomialOperators.AuxiliaryAlgebra.induction_on
    (p := fun a => Commute (firstRepresentation a) (secondRepresentation b)) ℂ a ?_ ?_ ?_ ?_ ?_
  · simpa [firstRepresentation] using
      commute_second auxiliaryEndomorphism1 auxiliaryEndomorphism1_commute_auxiliaryEndomorphism3 auxiliaryEndomorphism1_commute_auxiliaryEndomorphism4 b
  · simpa [firstRepresentation] using
      commute_second auxiliaryEndomorphism2 auxiliaryEndomorphism2_commute_auxiliaryEndomorphism3 auxiliaryEndomorphism2_commute_auxiliaryEndomorphism4 b
  · intro c
    rw [AlgHom.commutes]
    exact Algebra.commutes c (secondRepresentation b)
  · intro u v hu hv
    rw [map_add]
    exact hu.add_left hv
  · intro u v hu hv
    rw [map_mul]
    exact hu.mul_left hv


/-- An algebra homomorphism from the displayed tensor-product algebra to endomorphisms of the auxiliary carrier. -/
noncomputable def tensorProductRepresentation :
    (RepresentationTheory.FreeAlgebra.PolynomialOperators.AuxiliaryAlgebra ℂ ⊗[ℂ] RepresentationTheory.FreeAlgebra.PolynomialOperators.AuxiliaryAlgebra ℂ) →ₐ[ℂ]
      Module.End ℂ AuxiliaryCarrier :=
  Algebra.TensorProduct.lift firstRepresentation secondRepresentation first_second_representations_commute


/-- A module structure on the auxiliary carrier over the displayed tensor-product algebra. -/
@[reducible]
noncomputable def auxiliaryTensorProductModule :
    Module (RepresentationTheory.FreeAlgebra.PolynomialOperators.AuxiliaryAlgebra ℂ ⊗[ℂ] RepresentationTheory.FreeAlgebra.PolynomialOperators.AuxiliaryAlgebra ℂ)
      AuxiliaryCarrier :=
  Module.compHom AuxiliaryCarrier tensorProductRepresentation.toRingHom

/-- A second auxiliary module structure over the displayed algebra on the auxiliary carrier. -/
instance auxiliaryAlgebraModule2 : Module (RepresentationTheory.FreeAlgebra.PolynomialOperators.AuxiliaryAlgebra ℂ ⊗[ℂ] RepresentationTheory.FreeAlgebra.PolynomialOperators.AuxiliaryAlgebra ℂ) AuxiliaryCarrier :=
  auxiliaryTensorProductModule

/-- On a pure tensor, the tensor-product representation is the product of the corresponding first and second representations. -/
@[simp]
theorem tensorProductRepresentation_tmul (a b : RepresentationTheory.FreeAlgebra.PolynomialOperators.AuxiliaryAlgebra ℂ) :
  tensorProductRepresentation (a ⊗ₜ[ℂ] b) = firstRepresentation a * secondRepresentation b := by
  exact Algebra.TensorProduct.lift_tmul _ _ _ _ _

/-- The first representation sends one displayed algebra element to the first auxiliary endomorphism. -/
@[simp]
theorem firstRepresentation_auxiliaryElement1 : firstRepresentation (RepresentationTheory.FreeAlgebra.PolynomialOperators.AuxiliaryAlgebra.firstOperator ℂ) = auxiliaryEndomorphism1 := by
  simp [firstRepresentation]

/-- The first representation sends the other displayed algebra element to the second auxiliary endomorphism. -/
@[simp]
theorem firstRepresentation_auxiliaryElement2 : firstRepresentation (RepresentationTheory.FreeAlgebra.PolynomialOperators.AuxiliaryAlgebra.secondOperator ℂ) = auxiliaryEndomorphism2 := by
  simp [firstRepresentation]

/-- The second representation sends one displayed algebra element to the third auxiliary endomorphism. -/
@[simp]
theorem secondRepresentation_auxiliaryElement1 : secondRepresentation (RepresentationTheory.FreeAlgebra.PolynomialOperators.AuxiliaryAlgebra.firstOperator ℂ) = auxiliaryEndomorphism3 := by
  simp [secondRepresentation]

/-- The second representation sends the other displayed algebra element to the fourth auxiliary endomorphism. -/
@[simp]
theorem secondRepresentation_auxiliaryElement2 : secondRepresentation (RepresentationTheory.FreeAlgebra.PolynomialOperators.AuxiliaryAlgebra.secondOperator ℂ) = auxiliaryEndomorphism4 := by
  simp [secondRepresentation]


/-- At one, the first representation of one displayed element equals the second representation of the other, and conversely. -/
theorem first_second_representation_auxiliaryElements_apply_one :
    firstRepresentation (RepresentationTheory.FreeAlgebra.PolynomialOperators.AuxiliaryAlgebra.secondOperator ℂ) 1 =
        secondRepresentation (RepresentationTheory.FreeAlgebra.PolynomialOperators.AuxiliaryAlgebra.firstOperator ℂ) 1 ∧
      secondRepresentation (RepresentationTheory.FreeAlgebra.PolynomialOperators.AuxiliaryAlgebra.secondOperator ℂ) 1 =
        firstRepresentation (RepresentationTheory.FreeAlgebra.PolynomialOperators.AuxiliaryAlgebra.firstOperator ℂ) 1 := by
  constructor <;>
    simp [auxiliaryEndomorphism2, auxiliaryEndomorphism1, auxiliaryEndomorphism4, auxiliaryEndomorphism3, endomorphismPair_aux2, endomorphismPair_aux1]

private lemma pderiv_zero_bivariate_C (p : ℂ[X]) :
    pderiv 0 (Polynomial.Bivariate.equivMvPolynomial ℂ (Polynomial.C p)) =
      Polynomial.Bivariate.equivMvPolynomial ℂ (Polynomial.C p.derivative) := by
  simpa using Polynomial.Bivariate.pderiv_zero_equivMvPolynomial (R := ℂ) (Polynomial.C p)


/-- The auxiliary carrier is simple as a module over the displayed tensor-product algebra. -/
@[source_ref "Chapter3/Remark3.10.3" (role := supporting)]
theorem auxiliaryTensorProductModule_isSimpleModule :
    letI := auxiliaryTensorProductModule
    IsSimpleModule (RepresentationTheory.FreeAlgebra.PolynomialOperators.AuxiliaryAlgebra ℂ ⊗[ℂ] RepresentationTheory.FreeAlgebra.PolynomialOperators.AuxiliaryAlgebra ℂ)
      AuxiliaryCarrier := by
  classical
  letI := auxiliaryTensorProductModule
  let A := RepresentationTheory.FreeAlgebra.PolynomialOperators.AuxiliaryAlgebra ℂ ⊗[ℂ] RepresentationTheory.FreeAlgebra.PolynomialOperators.AuxiliaryAlgebra ℂ
  refine { exists_pair_ne := ⟨⊥, ⊤, bot_ne_top⟩, eq_bot_or_eq_top := fun S => ?_ }
  rcases eq_or_ne S ⊥ with rfl | hS
  · exact Or.inl rfl
  right
  obtain ⟨p, hpS, hp0⟩ := (Submodule.ne_bot_iff S).mp hS
  have hact (a : A) (q : AuxiliaryCarrier) : a • q = tensorProductRepresentation a q := rfl
  have hX0 (q : AuxiliaryCarrier) (hq : q ∈ S) : X 0 * q ∈ S := by
    have := S.smul_mem ((RepresentationTheory.FreeAlgebra.PolynomialOperators.AuxiliaryAlgebra.firstOperator ℂ) ⊗ₜ[ℂ] (1 : RepresentationTheory.FreeAlgebra.PolynomialOperators.AuxiliaryAlgebra ℂ)) hq
    simpa [hact, tensorProductRepresentation_tmul, auxiliaryEndomorphism1, endomorphismPair_aux1, Module.End.mul_apply] using this
  have hX1 (q : AuxiliaryCarrier) (hq : q ∈ S) : X 1 * q ∈ S := by
    have := S.smul_mem ((1 : RepresentationTheory.FreeAlgebra.PolynomialOperators.AuxiliaryAlgebra ℂ) ⊗ₜ[ℂ] RepresentationTheory.FreeAlgebra.PolynomialOperators.AuxiliaryAlgebra.firstOperator ℂ) hq
    simpa [hact, tensorProductRepresentation_tmul, auxiliaryEndomorphism3, endomorphismPair_aux1, Module.End.mul_apply] using this
  have hD0 (q : AuxiliaryCarrier) (hq : q ∈ S) : pderiv 0 q ∈ S := by
    have := S.smul_mem
      (((RepresentationTheory.FreeAlgebra.PolynomialOperators.AuxiliaryAlgebra.secondOperator ℂ) ⊗ₜ[ℂ] (1 : RepresentationTheory.FreeAlgebra.PolynomialOperators.AuxiliaryAlgebra ℂ)) -
        ((1 : RepresentationTheory.FreeAlgebra.PolynomialOperators.AuxiliaryAlgebra ℂ) ⊗ₜ[ℂ] RepresentationTheory.FreeAlgebra.PolynomialOperators.AuxiliaryAlgebra.firstOperator ℂ)) hq
    simpa [sub_smul, hact, tensorProductRepresentation_tmul, auxiliaryEndomorphism2, auxiliaryEndomorphism3, endomorphismPair_aux2, endomorphismPair_aux1,
      Module.End.mul_apply] using this
  have hD1 (q : AuxiliaryCarrier) (hq : q ∈ S) : pderiv 1 q ∈ S := by
    have := S.smul_mem
      (((1 : RepresentationTheory.FreeAlgebra.PolynomialOperators.AuxiliaryAlgebra ℂ) ⊗ₜ[ℂ] RepresentationTheory.FreeAlgebra.PolynomialOperators.AuxiliaryAlgebra.secondOperator ℂ) -
        ((RepresentationTheory.FreeAlgebra.PolynomialOperators.AuxiliaryAlgebra.firstOperator ℂ) ⊗ₜ[ℂ] (1 : RepresentationTheory.FreeAlgebra.PolynomialOperators.AuxiliaryAlgebra ℂ))) hq
    simpa [sub_smul, hact, tensorProductRepresentation_tmul, auxiliaryEndomorphism4, auxiliaryEndomorphism1, endomorphismPair_aux2, endomorphismPair_aux1,
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
  have hone : (1 : AuxiliaryCarrier) ∈ S := by
    rw [hact, tensorProductRepresentation.commutes] at hscale
    change c⁻¹ • MvPolynomial.C c ∈ S at hscale
    rw [MvPolynomial.smul_eq_C_mul, ← MvPolynomial.C_mul] at hscale
    simpa [hc0] using hscale
  have hC (d : ℂ) : MvPolynomial.C d ∈ S := by
    have hs := S.smul_mem (algebraMap ℂ A d) hone
    rw [hact, tensorProductRepresentation.commutes] at hs
    simpa [MvPolynomial.smul_eq_C_mul] using hs
  have hall : ∀ z : AuxiliaryCarrier, z ∈ S := by
    intro z
    induction z using MvPolynomial.induction_on with
    | C d => exact hC d
    | add u v hu hv => exact S.add_mem hu hv
    | mul_X u i hu =>
        fin_cases i
        · simpa [mul_comm] using hX0 u hu
        · simpa [mul_comm] using hX1 u hu
  exact hall z


/-- The displayed tensor-product representation does not factor through any finite-dimensional complex algebra. -/
theorem tensorProductRepresentation_not_factor_finiteDimensional
    (Q : Type*) [Ring Q] [Algebra ℂ Q] [FiniteDimensional ℂ Q]
    (q : (RepresentationTheory.FreeAlgebra.PolynomialOperators.AuxiliaryAlgebra ℂ ⊗[ℂ] RepresentationTheory.FreeAlgebra.PolynomialOperators.AuxiliaryAlgebra ℂ) →ₐ[ℂ] Q)
    (r : Q →ₐ[ℂ] Module.End ℂ AuxiliaryCarrier) :
    tensorProductRepresentation ≠ r.comp q := by
  classical
  intro hfactor
  let A := RepresentationTheory.FreeAlgebra.PolynomialOperators.AuxiliaryAlgebra ℂ ⊗[ℂ] RepresentationTheory.FreeAlgebra.PolynomialOperators.AuxiliaryAlgebra ℂ
  letI := auxiliaryTensorProductModule
  letI : IsSimpleModule A AuxiliaryCarrier := auxiliaryTensorProductModule_isSimpleModule
  let orbitQ : Q →ₗ[ℂ] AuxiliaryCarrier := {
    toFun a := r a 1
    map_add' a b := by simp
    map_smul' c a := by simp }
  have horbitQ : Function.Surjective orbitQ := by
    intro p
    obtain ⟨a, ha⟩ := IsSimpleModule.toSpanSingleton_surjective A (one_ne_zero :
      (1 : AuxiliaryCarrier) ≠ 0) p
    refine ⟨q a, ?_⟩
    change r (q a) 1 = p
    rw [← AlgHom.comp_apply, ← hfactor]
    exact ha
  letI : FiniteDimensional ℂ AuxiliaryCarrier :=
    FiniteDimensional.of_surjective orbitQ horbitQ
  have hfinrank : Module.finrank ℂ AuxiliaryCarrier = 0 :=
    MvPolynomial.finrank_eq_zero
  exact one_ne_zero (finrank_zero_iff_forall_zero.mp hfinrank 1)




private noncomputable def weylBasis :
    Module.Basis (ℕ × ℕ) ℂ (RepresentationTheory.FreeAlgebra.PolynomialOperators.AuxiliaryAlgebra ℂ) :=
  Module.Basis.mk (RepresentationTheory.FreeAlgebra.PolynomialOperators.indexedElement_linearIndependent_and_span (k := ℂ)).1
    (RepresentationTheory.FreeAlgebra.PolynomialOperators.indexedElement_linearIndependent_and_span (k := ℂ)).2


private noncomputable def bivariateBasis :
    Module.Basis (ℕ × ℕ) ℂ AuxiliaryCarrier :=
  (MvPolynomial.basisMonomials (Fin 2) ℂ).reindex
    (finTwoArrowEquiv' ℕ)

private theorem bivariateBasis_apply (i j : ℕ) :
    bivariateBasis (i, j) = X 0 ^ i * X 1 ^ j := by
  rw [bivariateBasis, Module.Basis.reindex_apply, MvPolynomial.coe_basisMonomials]
  simp [finTwoArrowEquiv', MvPolynomial.monomial_eq]


/-- A complex-linear equivalence between the displayed algebra and the auxiliary carrier. -/
noncomputable def auxiliaryLinearEquiv :
    RepresentationTheory.FreeAlgebra.PolynomialOperators.AuxiliaryAlgebra ℂ ≃ₗ[ℂ] AuxiliaryCarrier :=
  weylBasis.equiv bivariateBasis (Equiv.refl (ℕ × ℕ))

/-- The auxiliary equivalence sends the displayed doubly indexed element to the corresponding product of polynomial-variable powers. -/
@[simp]
theorem auxiliaryLinearEquiv_indexedElement (i j : ℕ) :
    auxiliaryLinearEquiv (RepresentationTheory.FreeAlgebra.PolynomialOperators.AuxiliaryAlgebra.indexedElement ℂ i j) = X 0 ^ i * X 1 ^ j := by
  rw [← show weylBasis (i, j) = RepresentationTheory.FreeAlgebra.PolynomialOperators.AuxiliaryAlgebra.indexedElement ℂ i j by
    exact Module.Basis.mk_apply _ _ _]
  rw [auxiliaryLinearEquiv, Module.Basis.equiv_apply, bivariateBasis_apply]
  rfl


/-- A complex-linear map from the displayed algebra to the auxiliary carrier. -/
noncomputable def auxiliaryLinearMap :
    RepresentationTheory.FreeAlgebra.PolynomialOperators.AuxiliaryAlgebra ℂ →ₗ[ℂ] AuxiliaryCarrier where
  toFun a := firstRepresentation a 1
  map_add' a b := by simp
  map_smul' c a := by simp

private lemma firstY_pow_one (j : ℕ) :
    (auxiliaryEndomorphism2 ^ j) (1 : AuxiliaryCarrier) = X 1 ^ j := by
  induction j with
  | zero => simp
  | succ j ih =>
      rw [pow_succ', Module.End.mul_apply, ih]
      simp only [auxiliaryEndomorphism2, endomorphismPair_aux2, Fin.isValue, endomorphismPair_aux1, LinearMap.add_apply,
        Derivation.coeFn_coe, Derivation.leibniz_pow, pderiv_X, ne_eq, one_ne_zero,
        not_false_eq_true, Pi.single_eq_of_ne, smul_eq_mul, mul_zero, nsmul_zero,
        LinearMap.coe_mk, AddHom.coe_mk, zero_add]
      rw [mul_comm, pow_succ]

/-- The auxiliary linear map sends the displayed doubly indexed element to the corresponding product of powers of the first two polynomial variables. -/
@[simp]
theorem auxiliaryLinearMap_indexedElement (i j : ℕ) :
    auxiliaryLinearMap (RepresentationTheory.FreeAlgebra.PolynomialOperators.AuxiliaryAlgebra.indexedElement ℂ i j) = X 0 ^ i * X 1 ^ j := by
  change firstRepresentation (RepresentationTheory.FreeAlgebra.PolynomialOperators.AuxiliaryAlgebra.indexedElement ℂ i j) 1 = _
  rw [RepresentationTheory.FreeAlgebra.PolynomialOperators.AuxiliaryAlgebra.indexedElement, map_mul, map_pow, map_pow,
    Module.End.mul_apply, firstRepresentation_auxiliaryElement1, firstRepresentation_auxiliaryElement2, firstY_pow_one]
  induction i with
  | zero => simp
  | succ i ih =>
      rw [pow_succ', Module.End.mul_apply, ih]
      simp [auxiliaryEndomorphism1, endomorphismPair_aux1]
      ring


/-- The linear map underlying the auxiliary equivalence is the displayed auxiliary linear map. -/
theorem auxiliaryLinearEquiv_toLinearMap :
    auxiliaryLinearEquiv.toLinearMap = auxiliaryLinearMap := by
  apply weylBasis.ext
  intro p
  rw [show weylBasis p = RepresentationTheory.FreeAlgebra.PolynomialOperators.AuxiliaryAlgebra.indexedElement ℂ p.1 p.2 by
    exact Module.Basis.mk_apply _ _ _]
  simp [auxiliaryLinearEquiv_indexedElement, auxiliaryLinearMap_indexedElement]


/-- An auxiliary module structure over the displayed algebra on the auxiliary carrier. -/
@[reducible]
noncomputable def auxiliaryAlgebraModule1 :
    Module (RepresentationTheory.FreeAlgebra.PolynomialOperators.AuxiliaryAlgebra ℂ) AuxiliaryCarrier :=
  Module.compHom AuxiliaryCarrier firstRepresentation.toRingHom

local instance : Module (RepresentationTheory.FreeAlgebra.PolynomialOperators.AuxiliaryAlgebra ℂ) AuxiliaryCarrier :=
  auxiliaryAlgebraModule1

private noncomputable def firstOrbitLinear :
    RepresentationTheory.FreeAlgebra.PolynomialOperators.AuxiliaryAlgebra ℂ →ₗ[RepresentationTheory.FreeAlgebra.PolynomialOperators.AuxiliaryAlgebra ℂ] AuxiliaryCarrier where
  toFun a := firstRepresentation a 1
  map_add' a b := by simp
  map_smul' a b := by
    change firstRepresentation (a * b) 1 = firstRepresentation a (firstRepresentation b 1)
    rw [map_mul, Module.End.mul_apply]

private theorem firstOrbitLinear_bijective : Function.Bijective firstOrbitLinear := by
  have h : Function.Bijective auxiliaryLinearMap := by
    rw [← auxiliaryLinearEquiv_toLinearMap]
    exact auxiliaryLinearEquiv.bijective
  constructor
  · intro a b hab
    exact h.1 hab
  · intro p
    exact h.2 p


/-- A module-linear equivalence from the regular module of the displayed algebra to the auxiliary carrier. -/
noncomputable def regularLinearEquivAuxiliaryCarrier :
    RepresentationTheory.FreeAlgebra.PolynomialOperators.AuxiliaryAlgebra ℂ ≃ₗ[RepresentationTheory.FreeAlgebra.PolynomialOperators.AuxiliaryAlgebra ℂ] AuxiliaryCarrier :=
  LinearEquiv.ofBijective firstOrbitLinear firstOrbitLinear_bijective

/-- The regular-module equivalence sends an algebra element to the value at one of its image under the first representation. -/
@[simp]
theorem regularLinearEquivAuxiliaryCarrier_apply (a : RepresentationTheory.FreeAlgebra.PolynomialOperators.AuxiliaryAlgebra ℂ) :
    regularLinearEquivAuxiliaryCarrier a = firstRepresentation a 1 := rfl




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


/-- No element of the displayed complex algebra multiplied by the displayed auxiliary element equals one. -/
theorem mul_auxiliaryElement_ne_one (r : RepresentationTheory.FreeAlgebra.PolynomialOperators.AuxiliaryAlgebra ℂ) :
    r * RepresentationTheory.FreeAlgebra.PolynomialOperators.AuxiliaryAlgebra.secondOperator ℂ ≠ 1 := by
  intro h
  have hop := congrArg (fun f : Module.End ℂ (Polynomial ℂ) => f 1)
    (congrArg (RepresentationTheory.FreeAlgebra.PolynomialOperators.toPolynomialEnd ℂ) h)
  simp [map_mul, RepresentationTheory.FreeAlgebra.PolynomialOperators.toPolynomialEnd_secondOperator] at hop


/-- No submodule of the regular module of the displayed complex algebra is simple. -/
theorem regularSubmodule_not_isSimpleModule
    (I : Submodule (RepresentationTheory.FreeAlgebra.PolynomialOperators.AuxiliaryAlgebra ℂ) (RepresentationTheory.FreeAlgebra.PolynomialOperators.AuxiliaryAlgebra ℂ)) :
    ¬ IsSimpleModule (RepresentationTheory.FreeAlgebra.PolynomialOperators.AuxiliaryAlgebra ℂ) I := by
  have hy : RepresentationTheory.FreeAlgebra.PolynomialOperators.AuxiliaryAlgebra.secondOperator ℂ ≠ 0 := by
    rw [show RepresentationTheory.FreeAlgebra.PolynomialOperators.AuxiliaryAlgebra.secondOperator ℂ = RepresentationTheory.FreeAlgebra.PolynomialOperators.AuxiliaryAlgebra.indexedElement ℂ 0 1 by
      simp [RepresentationTheory.FreeAlgebra.PolynomialOperators.AuxiliaryAlgebra.indexedElement]]
    exact (RepresentationTheory.FreeAlgebra.PolynomialOperators.indexedElement_linearIndependent_and_span (k := ℂ)).1.ne_zero (0, 1)
  letI : Nontrivial (RepresentationTheory.FreeAlgebra.PolynomialOperators.AuxiliaryAlgebra ℂ) := ⟨⟨RepresentationTheory.FreeAlgebra.PolynomialOperators.AuxiliaryAlgebra.secondOperator ℂ, 0, hy⟩⟩
  exact submodule_not_isSimpleModule_of_no_mul_eq_one _ (RepresentationTheory.FreeAlgebra.PolynomialOperators.AuxiliaryAlgebra.secondOperator ℂ)
    hy mul_auxiliaryElement_ne_one I


/-- No displayed linear equivalence from the tensor product of the two modules to the auxiliary carrier can satisfy the stated equivariance relation when the first module is simple and the second is nontrivial. -/
@[source_ref "Chapter3/Remark3.10.3" (role := supporting)]
theorem not_equivariant_tensorProductEquiv
    (V W : Type*)
    [AddCommGroup V] [Module ℂ V]
    [Module (RepresentationTheory.FreeAlgebra.PolynomialOperators.AuxiliaryAlgebra ℂ) V]
    [IsScalarTower ℂ (RepresentationTheory.FreeAlgebra.PolynomialOperators.AuxiliaryAlgebra ℂ) V]
    [AddCommGroup W] [Module ℂ W]
    [Module (RepresentationTheory.FreeAlgebra.PolynomialOperators.AuxiliaryAlgebra ℂ) W]
    [IsScalarTower ℂ (RepresentationTheory.FreeAlgebra.PolynomialOperators.AuxiliaryAlgebra ℂ) W]
    [IsSimpleModule (RepresentationTheory.FreeAlgebra.PolynomialOperators.AuxiliaryAlgebra ℂ) V] [Nontrivial W]
    (e : V ⊗[ℂ] W ≃ₗ[ℂ] AuxiliaryCarrier)
    (hequiv : ∀ (a b : RepresentationTheory.FreeAlgebra.PolynomialOperators.AuxiliaryAlgebra ℂ) (t : V ⊗[ℂ] W),
      e (TensorProduct.map
          ((Algebra.lsmul ℂ ℂ V : RepresentationTheory.FreeAlgebra.PolynomialOperators.AuxiliaryAlgebra ℂ →ₐ[ℂ] Module.End ℂ V) a)
          ((Algebra.lsmul ℂ ℂ W : RepresentationTheory.FreeAlgebra.PolynomialOperators.AuxiliaryAlgebra ℂ →ₐ[ℂ] Module.End ℂ W) b) t) =
        tensorProductRepresentation (a ⊗ₜ[ℂ] b) (e t)) : False := by
  classical
  let R := RepresentationTheory.FreeAlgebra.PolynomialOperators.AuxiliaryAlgebra ℂ
  obtain ⟨w, hw⟩ := exists_ne (0 : W)
  obtain ⟨ψ, hψ⟩ := Module.Projective.exists_dual_eq_one ℂ hw
  let f : V →ₗ[R] AuxiliaryCarrier :=
    { toFun := fun v => e (v ⊗ₜ[ℂ] w)
      map_add' := fun v v' => by
        rw [TensorProduct.add_tmul, map_add]
      map_smul' := fun a v => by
        change e ((a • v) ⊗ₜ[ℂ] w) = firstRepresentation a (e (v ⊗ₜ[ℂ] w))
        have h := hequiv a 1 (v ⊗ₜ[ℂ] w)
        simpa [TensorProduct.map_tmul, Algebra.lsmul_coe, Module.End.mul_apply] using h }
  have hf : Function.Injective f := by
    intro v v' hv
    have ht : v ⊗ₜ[ℂ] w = v' ⊗ₜ[ℂ] w := e.injective hv
    have hmap := congrArg
      (fun z : V ⊗[ℂ] W =>
        (TensorProduct.rid ℂ V) (TensorProduct.map LinearMap.id ψ z)) ht
    simpa [TensorProduct.map_tmul, TensorProduct.rid_tmul, hψ] using hmap
  let g : V →ₗ[R] R := regularLinearEquivAuxiliaryCarrier.symm.toLinearMap.comp f
  have hg : Function.Injective g := regularLinearEquivAuxiliaryCarrier.symm.injective.comp hf
  let I : Submodule R R := LinearMap.range g
  letI : IsSimpleModule R I :=
    (LinearEquiv.isSimpleModule_iff (LinearEquiv.ofInjective g hg)).mp inferInstance
  exact regularSubmodule_not_isSimpleModule I inferInstance

end

end RepresentationTheory.Algebra.Module.AuxiliaryRepresentations
