import Mathlib
import EtingofRepresentationTheory.Chapter2.Problem2_7_5
import EtingofRepresentationTheory.Chapter2.QWeylAlgebraUniversal

/-!
# Problem 2.7.5(c): the explicit family of irreducible `q`-Weyl modules

Let `q` be a primitive root of unity of order `n = orderOf q`. `Problem2_7_5.lean` proves that
every finite-dimensional irreducible representation of the `q`-Weyl algebra `A = qWeylAlgebra ℂ q`
has dimension exactly `n`. This file constructs the classifying family and (in follow-up work)
proves it exhausts the isomorphism classes.

## The family

For parameters `(α, β) ∈ ℂˣ × ℂˣ` we build the `n`-dimensional module `V(α,β)` on `Fin n → ℂ`
via the universal property `Etingof.QWeyl.module` (from `QWeylAlgebraUniversal.lean`), with

* `x` acting as the twisted cyclic shift `Xlin`: `x·eⱼ = e_{j+1}` and `x·e_{n-1} = α·e₀`;
* `y` acting diagonally by `Ylin`: `y·eⱼ = β·qʲ·eⱼ`.

These satisfy the defining relation `y x = q·(x y)`, and the central elements `xⁿ`, `yⁿ` act by
the scalars `α`, `βⁿ` respectively (their common values are the *central character* `(α, βⁿ)`).

## Main definitions and results (this file)

* `Etingof.Problem2_7_5.Xunit` / `Yunit` — the invertible operators realizing `x`, `y`.
* `Etingof.Problem2_7_5.famRel` — the defining relation `Ylin·Xlin = q•(Xlin·Ylin)`.
* `Etingof.Problem2_7_5.Xlin_pow_orderOf` / `Ylin_pow_orderOf` — the central-scalar actions
  `Xⁿ = α·1`, `Yⁿ = βⁿ·1`.
-/

namespace Etingof.Problem2_7_5

open Etingof Finsupp Module

section Family

variable (q α β : ℂˣ) (N : ℕ) [NeZero N]

/-! ### The twisted cyclic shift `x` and the diagonal `y` -/

/-- The weight of the twisted shift `x` at index `k`: `α` when the shift wraps around
(`k = 0`), otherwise `1`. -/
noncomputable def wX (k : Fin N) : ℂ := if k = 0 then (α : ℂ) else 1

theorem wX_ne (k : Fin N) : wX α N k ≠ 0 := by
  unfold wX; split_ifs with h
  · exact α.ne_zero
  · exact one_ne_zero

/-- The twisted cyclic shift operator `x`: `(x·f) k = wX k · f (k-1)`, i.e. `x·eⱼ = e_{j+1}`
for `j < n-1` and `x·e_{n-1} = α·e₀`. -/
noncomputable def Xlin : (Fin N → ℂ) →ₗ[ℂ] (Fin N → ℂ) where
  toFun f := fun k => wX α N k • f (k - 1)
  map_add' f g := by funext k; simp only [Pi.add_apply, smul_eq_mul]; ring
  map_smul' c f := by funext k; simp only [Pi.smul_apply, smul_eq_mul, RingHom.id_apply]; ring

/-- The inverse of the twisted shift. -/
noncomputable def Xinv : (Fin N → ℂ) →ₗ[ℂ] (Fin N → ℂ) where
  toFun f := fun k => (wX α N (k + 1))⁻¹ • f (k + 1)
  map_add' f g := by funext k; simp only [Pi.add_apply, smul_eq_mul]; ring
  map_smul' c f := by funext k; simp only [Pi.smul_apply, smul_eq_mul, RingHom.id_apply]; ring

theorem Xinv_Xlin : (Xinv α N).comp (Xlin α N) = LinearMap.id := by
  ext f k
  simp only [LinearMap.comp_apply, Xinv, Xlin, LinearMap.coe_mk, AddHom.coe_mk, LinearMap.id_coe,
    id]
  rw [add_sub_cancel_right k 1, smul_smul, inv_mul_cancel₀ (wX_ne α N (k + 1)), one_smul]

theorem Xlin_Xinv : (Xlin α N).comp (Xinv α N) = LinearMap.id := by
  ext f k
  simp only [LinearMap.comp_apply, Xinv, Xlin, LinearMap.coe_mk, AddHom.coe_mk, LinearMap.id_coe,
    id]
  rw [sub_add_cancel k 1, smul_smul, mul_inv_cancel₀ (wX_ne α N k), one_smul]

/-- The twisted cyclic shift `x` as an invertible operator (a unit of `End`). -/
noncomputable def Xunit : (Module.End ℂ (Fin N → ℂ))ˣ where
  val := Xlin α N
  inv := Xinv α N
  val_inv := Xlin_Xinv α N
  inv_val := Xinv_Xlin α N

@[simp] theorem Xunit_val : (Xunit α N : Module.End ℂ (Fin N → ℂ)) = Xlin α N := rfl

/-- The diagonal weight of `y` at index `k`: `β·qᵏ`. -/
noncomputable def wY (k : Fin N) : ℂ := (β : ℂ) * (q : ℂ) ^ (k : ℕ)

omit [NeZero N] in
theorem wY_ne (k : Fin N) : wY q β N k ≠ 0 :=
  mul_ne_zero β.ne_zero (pow_ne_zero _ q.ne_zero)

/-- The diagonal operator `y`: `(y·f) k = β·qᵏ·f k`, i.e. `y·eⱼ = β·qʲ·eⱼ`. -/
noncomputable def Ylin : (Fin N → ℂ) →ₗ[ℂ] (Fin N → ℂ) where
  toFun f := fun k => wY q β N k • f k
  map_add' f g := by funext k; simp only [Pi.add_apply, smul_eq_mul]; ring
  map_smul' c f := by funext k; simp only [Pi.smul_apply, smul_eq_mul, RingHom.id_apply]; ring

/-- The inverse diagonal operator. -/
noncomputable def Yinv : (Fin N → ℂ) →ₗ[ℂ] (Fin N → ℂ) where
  toFun f := fun k => (wY q β N k)⁻¹ • f k
  map_add' f g := by funext k; simp only [Pi.add_apply, smul_eq_mul]; ring
  map_smul' c f := by funext k; simp only [Pi.smul_apply, smul_eq_mul, RingHom.id_apply]; ring

omit [NeZero N] in
theorem Yinv_Ylin : (Yinv q β N).comp (Ylin q β N) = LinearMap.id := by
  ext f k
  simp only [LinearMap.comp_apply, Yinv, Ylin, LinearMap.coe_mk, AddHom.coe_mk, LinearMap.id_coe,
    id]
  rw [smul_smul, inv_mul_cancel₀ (wY_ne q β N k), one_smul]

omit [NeZero N] in
theorem Ylin_Yinv : (Ylin q β N).comp (Yinv q β N) = LinearMap.id := by
  ext f k
  simp only [LinearMap.comp_apply, Yinv, Ylin, LinearMap.coe_mk, AddHom.coe_mk, LinearMap.id_coe,
    id]
  rw [smul_smul, mul_inv_cancel₀ (wY_ne q β N k), one_smul]

/-- The diagonal operator `y` as an invertible operator (a unit of `End`). -/
noncomputable def Yunit : (Module.End ℂ (Fin N → ℂ))ˣ where
  val := Ylin q β N
  inv := Yinv q β N
  val_inv := Ylin_Yinv q β N
  inv_val := Yinv_Ylin q β N

@[simp] theorem Yunit_val : (Yunit q β N : Module.End ℂ (Fin N → ℂ)) = Ylin q β N := rfl

/-! ### The defining relation -/

/-- The exponent identity underlying the relation: `qᵏ = q·q^{k-1}` (cyclically), which holds
because `q` has order `N`. -/
theorem q_pow_val_sub_one (hqorder : orderOf q = N) (k : Fin N) :
    (q : ℂ) ^ (k : ℕ) = q * (q : ℂ) ^ ((k - 1 : Fin N) : ℕ) := by
  have hmod : k.val ≡ (k - 1).val + 1 [MOD N] := by
    have h : ((k - 1) + 1 : Fin N) = k := sub_add_cancel k 1
    calc k.val = ((k - 1) + 1 : Fin N).val := by rw [h]
      _ = ((k - 1).val + (1 : Fin N).val) % N := by rw [Fin.val_add]
      _ ≡ (k - 1).val + (1 : Fin N).val [MOD N] := Nat.mod_modEq _ _
      _ ≡ (k - 1).val + 1 [MOD N] := Nat.ModEq.add_left _ (Nat.mod_modEq 1 N)
  have huq : q ^ (k : ℕ) = q ^ ((k - 1 : Fin N).val + 1) := by
    rw [pow_eq_pow_iff_modEq, hqorder]; exact hmod
  have hcast : (q : ℂ) ^ (k : ℕ) = (q : ℂ) ^ ((k - 1 : Fin N).val + 1) := by
    have := congrArg Units.val huq; push_cast at this ⊢; simpa using this
  rw [hcast, pow_succ]; ring

/-- **Defining relation of the family.** The operators `Ylin`, `Xlin` satisfy `y x = q·(x y)`,
matching the hypothesis required by the universal property `Etingof.QWeyl.toEnd`. -/
theorem famRel (hqorder : orderOf q = N) :
    (Ylin q β N) * (Xlin α N) = (q : ℂ) • ((Xlin α N) * (Ylin q β N)) := by
  refine LinearMap.ext fun f => ?_
  funext k
  simp only [Module.End.mul_apply, LinearMap.smul_apply, Xlin, Ylin, wY, LinearMap.coe_mk,
    AddHom.coe_mk, Pi.smul_apply, smul_eq_mul]
  rw [q_pow_val_sub_one q N hqorder k]; ring

/-- The relation in the form required by the universal property `Etingof.QWeyl.module`
(same statement as `famRel`, phrased for the coerced units). -/
theorem famRel_unit (hqorder : orderOf q = N) :
    ((Yunit q β N : Module.End ℂ (Fin N → ℂ))) * (Xunit α N : Module.End ℂ (Fin N → ℂ))
      = (q : ℂ) • ((Xunit α N : Module.End ℂ (Fin N → ℂ))
          * (Yunit q β N : Module.End ℂ (Fin N → ℂ))) := by
  rw [Xunit_val, Yunit_val]; exact famRel q α β N hqorder

/-! ### The classifying module `V(α,β)` -/

/-- The classifying module `V(α,β)`: the `qWeylAlgebra ℂ q`-module structure on `Fin n → ℂ`
obtained from the twisted shift `x` and the diagonal `y`. Here `xⁱyʲ` acts as `Xⁱ Yʲ`. -/
@[reducible] noncomputable def famModule (hqorder : orderOf q = N) :
    Module (qWeylAlgebra ℂ q) (Fin N → ℂ) :=
  Etingof.QWeyl.module q (Xunit α N) (Yunit q β N) (famRel_unit q α β N hqorder)

omit [NeZero N] in
/-- `V(α,β)` has dimension `n` over `ℂ` (the `ℂ`-vector space structure is the standard one on
`Fin n → ℂ`, unaffected by the `q`-Weyl action). -/
theorem famModule_finrank : Module.finrank ℂ (Fin N → ℂ) = N := by simp

/-- The generator `x` acts on `V(α,β)` as the twisted cyclic shift `Xlin`. -/
theorem famModule_x_smul (hqorder : orderOf q = N) (f : Fin N → ℂ) :
    letI := famModule q α β N hqorder
    (Etingof.QWeyl.qWeylMono q (1, 0)) • f = Xlin α N f := by
  letI := famModule q α β N hqorder
  rw [Etingof.QWeyl.module_smul]
  change Etingof.QWeyl.toEnd q (Xunit α N) (Yunit q β N) _ (Etingof.QWeyl.qWeylMono q (1, 0)) f = _
  rw [Etingof.QWeyl.toEnd_x, Xunit_val]

/-- The generator `y` acts on `V(α,β)` as the diagonal operator `Ylin`. -/
theorem famModule_y_smul (hqorder : orderOf q = N) (f : Fin N → ℂ) :
    letI := famModule q α β N hqorder
    (Etingof.QWeyl.qWeylMono q (0, 1)) • f = Ylin q β N f := by
  letI := famModule q α β N hqorder
  rw [Etingof.QWeyl.module_smul]
  change Etingof.QWeyl.toEnd q (Xunit α N) (Yunit q β N) _ (Etingof.QWeyl.qWeylMono q (0, 1)) f = _
  rw [Etingof.QWeyl.toEnd_y, Yunit_val]

/-- `V(α,β)` is compatible with the ambient `ℂ`-action: `k → qWeylAlgebra ℂ q → V(α,β)` is a
scalar tower, matching the representation API used in `Problem2_7_5.lean`. -/
theorem famModule_isScalarTower (hqorder : orderOf q = N) :
    letI := famModule q α β N hqorder
    IsScalarTower ℂ (qWeylAlgebra ℂ q) (Fin N → ℂ) :=
  Etingof.QWeyl.module_isScalarTower q (Xunit α N) (Yunit q β N) (famRel_unit q α β N hqorder)

end Family

end Etingof.Problem2_7_5
