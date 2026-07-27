import Mathlib.RingTheory.TensorProduct.Maps
import Mathlib.FieldTheory.RatFunc.AsPolynomial
import Mathlib.FieldTheory.RatFunc.Basic
import Mathlib.RingTheory.Algebraic.Basic
import Mathlib.Data.Complex.Basic
import Mathlib.Algebra.MvPolynomial.PDeriv
import Mathlib.RingTheory.Derivation.Lie
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

end

end EtingofRepresentationTheory.Chapter3.Remark3_10_3
