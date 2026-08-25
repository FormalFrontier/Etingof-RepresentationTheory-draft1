import Mathlib
import EtingofRepresentationTheory.Chapter2.Proposition2_7_1_ii

/-!
# Universal mapping property for the `q`-Weyl algebra

`Etingof.qWeylAlgebra k q` (Proposition 2.7.1(ii)) is realized *concretely* as a subalgebra
of `Module.End k (QWeylModule k)`. To build finite-dimensional representations (for example the
classification in Problem 2.7.5(c)) we need to construct a module over it by specifying how the
generators act. This file supplies exactly that: from a pair of invertible operators `X, Y` on a
`k`-module `V` satisfying the defining relation `Y X = q • (X Y)`, we build an algebra
homomorphism `qWeylAlgebra k q →ₐ[k] Module.End k V`.

The construction rests on the fact (Proposition 2.7.1(ii)) that the monomials `qMono (i, j)` form
a `k`-basis of the algebra, so `qWeylAlgebra k q` is the twisted group algebra `k_q[ℤ²]`. The
target monomial `X^i Y^j` obeys the same reordering law `qMono_mul`, which makes the
basis-defined linear map multiplicative.

## Main definitions

* `Etingof.QWeyl.op X Y i j = X^i * Y^j` — the target operator realizing `xⁱyʲ`.
* `Etingof.QWeyl.toEnd` — the algebra hom `qWeylAlgebra k q →ₐ[k] Module.End k V`.
* `Etingof.QWeyl.module` / `Etingof.QWeyl.isScalarTower` — the resulting `qWeylAlgebra`-module
  structure on `V`, compatible with the ambient `k`-action.
-/

namespace Etingof.QWeyl

open Etingof Finsupp Module

variable {k : Type*} [CommRing k] (q : kˣ)
variable {V : Type*} [AddCommGroup V] [Module k V]

/-- The target operator realizing the monomial `xⁱyʲ` from invertible operators `X, Y`:
`op X Y i j = X^i * Y^j` (integer powers taken in the unit group `(End V)ˣ`). -/
noncomputable def op (X Y : (Module.End k V)ˣ) (i j : ℤ) : Module.End k V :=
  ↑(X ^ i) * ↑(Y ^ j)

variable (X Y : (Module.End k V)ˣ)

@[simp] theorem op_zero_zero : op X Y 0 0 = 1 := by
  simp [op]

/-- Powers of `X` collapse: `X^i * X^i' = X^(i+i')` on the underlying operators. -/
theorem valX_mul (i i' : ℤ) : (↑(X ^ i) : Module.End k V) * ↑(X ^ i') = ↑(X ^ (i + i')) := by
  rw [zpow_add]; rfl

/-- Powers of `Y` collapse: `Y^j * Y^j' = Y^(j+j')` on the underlying operators. -/
theorem valY_mul (j j' : ℤ) : (↑(Y ^ j) : Module.End k V) * ↑(Y ^ j') = ↑(Y ^ (j + j')) := by
  rw [zpow_add]; rfl

/-- The central scalar unit `q • 1` inside the unit group `(End V)ˣ`. Working with the
reordering law at the unit-group level (rather than with `k`-scalar multiplication on `End V`)
lets us reason with the group operations directly. -/
noncomputable def qU : (Module.End k V)ˣ :=
  Units.map (algebraMap k (Module.End k V)).toMonoidHom q

@[simp] theorem coe_qU :
    ((qU q : (Module.End k V)ˣ) : Module.End k V) = algebraMap k (Module.End k V) (q : k) := rfl

/-- An integer power of the central unit `qU q` is `qU (q^a)`, i.e. `algebraMap (q^a)`. -/
theorem coe_qU_zpow (a : ℤ) :
    ((qU q ^ a : (Module.End k V)ˣ) : Module.End k V)
      = algebraMap k (Module.End k V) ((q ^ a : kˣ) : k) := by
  have h : (qU q : (Module.End k V)ˣ) ^ a = qU (q ^ a) :=
    (map_zpow (Units.map (algebraMap k (Module.End k V)).toMonoidHom) q a).symm
  rw [h, coe_qU]

/-- Multiplying by the central unit `qU q` is the same as scaling by `q`. -/
theorem qU_smul (m : Module.End k V) :
    ((qU q : (Module.End k V)ˣ) : Module.End k V) * m = (q : k) • m := by
  rw [coe_qU, ← Algebra.smul_def]

/-- The scalar unit `qU q` commutes with every unit. -/
theorem commute_qU (u : (Module.End k V)ˣ) : Commute (qU q) u := by
  refine Units.ext ?_
  rw [Units.val_mul, Units.val_mul, coe_qU]
  exact Algebra.commutes (q : k) (u : Module.End k V)

section Relation

/-- The defining relation, transported to the unit group: `Y X = (qU q) X Y`. -/
theorem hrelU (hrel : (↑Y : Module.End k V) * ↑X = (q : k) • (↑X * ↑Y)) :
    Y * X = qU q * X * Y := by
  refine Units.ext ?_
  rw [Units.val_mul, Units.val_mul, Units.val_mul, coe_qU, ← Algebra.smul_def,
    smul_mul_assoc, ← hrel]

/-- The inverse relation at the unit-group level: `Y X⁻¹ = (qU q)⁻¹ X⁻¹ Y`. -/
theorem hrelU_inv (hrel : (↑Y : Module.End k V) * ↑X = (q : k) • (↑X * ↑Y)) :
    Y * X⁻¹ = (qU q)⁻¹ * X⁻¹ * Y := by
  have hU := hrelU q X Y hrel
  have hc : X⁻¹ * qU q = qU q * X⁻¹ := ((commute_qU q X⁻¹).symm).eq
  have h1 : X⁻¹ * Y = qU q * Y * X⁻¹ := by
    calc X⁻¹ * Y = X⁻¹ * (Y * X) * X⁻¹ := by group
      _ = X⁻¹ * (qU q * X * Y) * X⁻¹ := by rw [hU]
      _ = (X⁻¹ * qU q) * X * Y * X⁻¹ := by group
      _ = (qU q * X⁻¹) * X * Y * X⁻¹ := by rw [hc]
      _ = qU q * Y * X⁻¹ := by group
  calc Y * X⁻¹ = (qU q)⁻¹ * (qU q * Y * X⁻¹) := by group
    _ = (qU q)⁻¹ * (X⁻¹ * Y) := by rw [← h1]
    _ = (qU q)⁻¹ * X⁻¹ * Y := by group

/-- Unit-group reordering, one `Y`: `Y X^n = (qU q)^n X^n Y`. -/
theorem unit_YXpow (hrel : (↑Y : Module.End k V) * ↑X = (q : k) • (↑X * ↑Y)) (n : ℤ) :
    Y * X ^ n = qU q ^ n * X ^ n * Y := by
  have hU := hrelU q X Y hrel
  have hUi := hrelU_inv q X Y hrel
  induction n using Int.induction_on with
  | zero => simp
  | succ n ih =>
      have hc : X ^ (n : ℤ) * qU q = qU q * X ^ (n : ℤ) := ((commute_qU q (X ^ (n : ℤ))).symm).eq
      rw [zpow_add_one X n, zpow_add_one (qU q) n, ← mul_assoc, ih,
        mul_assoc (qU q ^ (n : ℤ) * X ^ (n : ℤ)) Y X, hU,
        show (qU q ^ (n : ℤ) * X ^ (n : ℤ)) * (qU q * X * Y)
            = qU q ^ (n : ℤ) * (X ^ (n : ℤ) * qU q) * X * Y from by group,
        hc]
      group
  | pred n ih =>
      have hc : X ^ (-(n : ℤ)) * (qU q)⁻¹ = (qU q)⁻¹ * X ^ (-(n : ℤ)) :=
        ((commute_qU q (X ^ (-(n : ℤ)))).symm).inv_right.eq
      rw [zpow_sub_one X (-(n : ℤ)), zpow_sub_one (qU q) (-(n : ℤ)), ← mul_assoc, ih,
        mul_assoc (qU q ^ (-(n : ℤ)) * X ^ (-(n : ℤ))) Y X⁻¹, hUi,
        show (qU q ^ (-(n : ℤ)) * X ^ (-(n : ℤ))) * ((qU q)⁻¹ * X⁻¹ * Y)
            = qU q ^ (-(n : ℤ)) * (X ^ (-(n : ℤ)) * (qU q)⁻¹) * X⁻¹ * Y from by group,
        hc]
      group

/-- Unit-group reordering, general powers: `Y^m X^n = (qU q)^(m n) X^n Y^m`. -/
theorem unit_YpowXpow (hrel : (↑Y : Module.End k V) * ↑X = (q : k) • (↑X * ↑Y)) (m n : ℤ) :
    Y ^ m * X ^ n = qU q ^ (m * n) * X ^ n * Y ^ m := by
  have hR := unit_YXpow q X Y hrel
  induction m using Int.induction_on with
  | zero => simp
  | succ m ih =>
      have hc : Y ^ (m : ℤ) * qU q ^ n = qU q ^ n * Y ^ (m : ℤ) :=
        (((commute_qU q (Y ^ (m : ℤ))).symm).zpow_right n).eq
      rw [zpow_add_one Y m, mul_assoc, hR n,
        show Y ^ (m : ℤ) * (qU q ^ n * X ^ n * Y)
            = (Y ^ (m : ℤ) * qU q ^ n) * X ^ n * Y from by group,
        hc,
        show qU q ^ n * Y ^ (m : ℤ) * X ^ n * Y
            = qU q ^ n * (Y ^ (m : ℤ) * X ^ n) * Y from by group,
        ih,
        show qU q ^ n * (qU q ^ ((m : ℤ) * n) * X ^ n * Y ^ (m : ℤ)) * Y
            = (qU q ^ n * qU q ^ ((m : ℤ) * n)) * X ^ n * (Y ^ (m : ℤ) * Y) from by group,
        ← zpow_add, ← zpow_add_one Y m,
        show n + (m : ℤ) * n = ((m : ℤ) + 1) * n from by ring]
  | pred m ih =>
      have hc : Y ^ (-(m : ℤ)) * qU q ^ (-n) = qU q ^ (-n) * Y ^ (-(m : ℤ)) :=
        (((commute_qU q (Y ^ (-(m : ℤ)))).symm).zpow_right (-n)).eq
      have hRi : Y⁻¹ * X ^ n = qU q ^ (-n) * X ^ n * Y⁻¹ := by
        have e1 : X ^ n * Y⁻¹ = qU q ^ n * (Y⁻¹ * X ^ n) := by
          calc X ^ n * Y⁻¹ = (Y⁻¹ * (Y * X ^ n)) * Y⁻¹ := by group
            _ = (Y⁻¹ * (qU q ^ n * X ^ n * Y)) * Y⁻¹ := by rw [hR n]
            _ = (Y⁻¹ * qU q ^ n) * X ^ n * (Y * Y⁻¹) := by group
            _ = (qU q ^ n * Y⁻¹) * X ^ n * (Y * Y⁻¹) := by
                  rw [(((commute_qU q Y).symm).zpow_right n).inv_left.eq]
            _ = qU q ^ n * (Y⁻¹ * X ^ n) := by group
        calc Y⁻¹ * X ^ n
            = qU q ^ (-n) * (qU q ^ n * (Y⁻¹ * X ^ n)) := by
                rw [show qU q ^ (-n) * (qU q ^ n * (Y⁻¹ * X ^ n))
                      = (qU q ^ (-n) * qU q ^ n) * (Y⁻¹ * X ^ n) from by group, ← zpow_add]
                simp
          _ = qU q ^ (-n) * (X ^ n * Y⁻¹) := by rw [← e1]
          _ = qU q ^ (-n) * X ^ n * Y⁻¹ := by group
      rw [zpow_sub_one Y (-(m : ℤ)), mul_assoc, hRi,
        show Y ^ (-(m : ℤ)) * (qU q ^ (-n) * X ^ n * Y⁻¹)
            = (Y ^ (-(m : ℤ)) * qU q ^ (-n)) * X ^ n * Y⁻¹ from by group,
        hc,
        show qU q ^ (-n) * Y ^ (-(m : ℤ)) * X ^ n * Y⁻¹
            = qU q ^ (-n) * (Y ^ (-(m : ℤ)) * X ^ n) * Y⁻¹ from by group,
        ih,
        show qU q ^ (-n) * (qU q ^ ((-(m : ℤ)) * n) * X ^ n * Y ^ (-(m : ℤ))) * Y⁻¹
            = (qU q ^ (-n) * qU q ^ ((-(m : ℤ)) * n)) * X ^ n * (Y ^ (-(m : ℤ)) * Y⁻¹)
              from by group,
        ← zpow_add, ← zpow_sub_one Y (-(m : ℤ)),
        show (-n) + (-(m : ℤ)) * n = ((-(m : ℤ)) - 1) * n from by ring]

/-- The reordering law for the target monomials, matching `qMono_mul`:
`op (i,j) * op (i',j') = q^(j i') • op (i+i', j+j')`. -/
theorem op_mul (hrel : (↑Y : Module.End k V) * ↑X = (q : k) • (↑X * ↑Y)) (i j i' j' : ℤ) :
    op X Y i j * op X Y i' j'
      = ((q ^ (j * i') : kˣ) : k) • op X Y (i + i') (j + j') := by
  have h := congrArg (fun u : (Module.End k V)ˣ => (u : Module.End k V))
    (unit_YpowXpow q X Y hrel j i')
  simp only [Units.val_mul, coe_qU_zpow] at h
  simp only [op]
  calc (↑(X ^ i) * ↑(Y ^ j)) * (↑(X ^ i') * ↑(Y ^ j'))
      = ↑(X ^ i) * (↑(Y ^ j) * ↑(X ^ i')) * ↑(Y ^ j') := by group
    _ = ↑(X ^ i) * (algebraMap k (Module.End k V) ((q ^ (j * i') : kˣ) : k) * ↑(X ^ i') * ↑(Y ^ j))
          * ↑(Y ^ j') := by rw [h]
    _ = ((q ^ (j * i') : kˣ) : k) • (↑(X ^ (i + i')) * ↑(Y ^ (j + j'))) := by
          rw [← Algebra.smul_def, smul_mul_assoc, mul_smul_comm, smul_mul_assoc]
          congr 1
          rw [← valX_mul, ← valY_mul]
          simp only [mul_assoc]

end Relation

/-! ### The monomial basis of the source algebra -/

/-- `xⁱyʲ` as an element of the concrete subalgebra `qWeylAlgebra k q`. -/
noncomputable def qWeylMono (p : ℤ × ℤ) : qWeylAlgebra k q :=
  ⟨qMono k q p, qMono_mem k q p⟩

@[simp] theorem coe_qWeylMono (p : ℤ × ℤ) :
    ((qWeylMono q p : qWeylAlgebra k q) : Module.End k (QWeylModule k)) = qMono k q p := rfl

theorem qWeylMono_zero : qWeylMono q (0, 0) = 1 := by
  apply Subtype.ext
  rw [coe_qWeylMono, OneMemClass.coe_one, qMono_zero]

/-- The reordering law on the source algebra, mirroring `qMono_mul`. -/
theorem qWeylMono_mul (p r : ℤ × ℤ) :
    qWeylMono q p * qWeylMono q r
      = (↑(q ^ (p.2 * r.1)) : k) • qWeylMono q (p.1 + r.1, p.2 + r.2) := by
  apply Subtype.ext
  rw [MulMemClass.coe_mul, coe_qWeylMono, coe_qWeylMono, Subalgebra.coe_smul, coe_qWeylMono,
    qMono_mul]

/-- Natural powers of a pure `x`-monomial: `(xⁱ)ᵐ = x^{i·m}`. The reordering scalars all vanish
because the `y`-exponent is zero. -/
theorem qWeylMono_x_pow (i : ℤ) (m : ℕ) : qWeylMono q (i, 0) ^ m = qWeylMono q (i * m, 0) := by
  induction m with
  | zero => rw [pow_zero, Nat.cast_zero, mul_zero, qWeylMono_zero]
  | succ m ih =>
    rw [pow_succ, ih, qWeylMono_mul]
    simp only [zero_mul, zpow_zero, Units.val_one, one_smul, add_zero]
    congr 2
    push_cast
    ring

/-- Natural powers of a pure `y`-monomial: `(yʲ)ᵐ = y^{j·m}`. -/
theorem qWeylMono_y_pow (j : ℤ) (m : ℕ) : qWeylMono q (0, j) ^ m = qWeylMono q (0, j * m) := by
  induction m with
  | zero => rw [pow_zero, Nat.cast_zero, mul_zero, qWeylMono_zero]
  | succ m ih =>
    rw [pow_succ, ih, qWeylMono_mul]
    simp only [mul_zero, zpow_zero, Units.val_one, one_smul, add_zero]
    congr 2
    push_cast
    ring

theorem qWeylMono_linearIndependent : LinearIndependent k (qWeylMono q) := by
  apply LinearIndependent.of_comp (qWeylAlgebra k q).val.toLinearMap
  have h : (qWeylAlgebra k q).val.toLinearMap ∘ qWeylMono q = qMono k q := rfl
  rw [h]
  exact qMono_linearIndependent k q

theorem qWeylMono_span : ⊤ ≤ Submodule.span k (Set.range (qWeylMono q)) := by
  rintro a -
  have h1 : (a : Module.End k (QWeylModule k)) ∈ Submodule.span k (Set.range (qMono k q)) := by
    rw [← qWeyl_toSubmodule_eq_span, Subalgebra.mem_toSubmodule]
    exact a.2
  have himg : Submodule.map (qWeylAlgebra k q).val.toLinearMap
        (Submodule.span k (Set.range (qWeylMono q)))
      = Submodule.span k (Set.range (qMono k q)) := by
    rw [Submodule.map_span]
    congr 1
    rw [← Set.range_comp]
    rfl
  rw [← himg] at h1
  obtain ⟨a', ha'mem, ha'eq⟩ := h1
  have hpa : a' = a := Subtype.ext ha'eq
  rwa [hpa] at ha'mem

/-- The monomial basis `{xⁱyʲ}` of the concrete `q`-Weyl algebra (Proposition 2.7.1(ii)). -/
noncomputable def basis : Basis (ℤ × ℤ) k (qWeylAlgebra k q) :=
  Basis.mk (qWeylMono_linearIndependent q) (qWeylMono_span q)

@[simp] theorem basis_apply (p : ℤ × ℤ) : basis q p = qWeylMono q p :=
  Basis.mk_apply _ _ _

/-! ### The lift `qWeylAlgebra k q →ₐ[k] Module.End k V` -/

/-- The underlying `k`-linear map of the lift, `xⁱyʲ ↦ Xⁱ Yʲ`. -/
noncomputable def toEndLinear : qWeylAlgebra k q →ₗ[k] Module.End k V :=
  (basis q).constr k (fun p => op X Y p.1 p.2)

@[simp] theorem toEndLinear_qWeylMono (p : ℤ × ℤ) :
    toEndLinear q X Y (qWeylMono q p) = op X Y p.1 p.2 := by
  rw [toEndLinear, ← basis_apply, Basis.constr_basis]

/-- Multiplicativity of the lift on two basis monomials (this is exactly `op_mul`). -/
theorem toEndLinear_key (hrel : (↑Y : Module.End k V) * ↑X = (q : k) • (↑X * ↑Y)) (p r : ℤ × ℤ) :
    toEndLinear q X Y (qWeylMono q p * qWeylMono q r)
      = toEndLinear q X Y (qWeylMono q p) * toEndLinear q X Y (qWeylMono q r) := by
  rw [qWeylMono_mul, map_smul, toEndLinear_qWeylMono, toEndLinear_qWeylMono, toEndLinear_qWeylMono,
    op_mul q X Y hrel]

/-- Multiplicativity of the lift with the right argument a basis monomial. -/
theorem toEndLinear_mul_right (hrel : (↑Y : Module.End k V) * ↑X = (q : k) • (↑X * ↑Y))
    (a : qWeylAlgebra k q) (r : ℤ × ℤ) :
    toEndLinear q X Y (a * qWeylMono q r)
      = toEndLinear q X Y a * toEndLinear q X Y (qWeylMono q r) := by
  have h : (toEndLinear q X Y).comp (LinearMap.mulRight k (qWeylMono q r))
      = (LinearMap.mulRight k (toEndLinear q X Y (qWeylMono q r))).comp (toEndLinear q X Y) := by
    apply (basis q).ext
    intro p
    simp only [LinearMap.comp_apply, LinearMap.mulRight_apply, basis_apply]
    exact toEndLinear_key q X Y hrel p r
  have hcf := DFunLike.congr_fun h a
  simpa only [LinearMap.comp_apply, LinearMap.mulRight_apply] using hcf

/-- Full multiplicativity of the lift. -/
theorem toEndLinear_mul (hrel : (↑Y : Module.End k V) * ↑X = (q : k) • (↑X * ↑Y))
    (a b : qWeylAlgebra k q) :
    toEndLinear q X Y (a * b) = toEndLinear q X Y a * toEndLinear q X Y b := by
  have h : (toEndLinear q X Y).comp (LinearMap.mulLeft k a)
      = (LinearMap.mulLeft k (toEndLinear q X Y a)).comp (toEndLinear q X Y) := by
    apply (basis q).ext
    intro r
    simp only [LinearMap.comp_apply, LinearMap.mulLeft_apply, basis_apply]
    exact toEndLinear_mul_right q X Y hrel a r
  have hcf := DFunLike.congr_fun h b
  simpa only [LinearMap.comp_apply, LinearMap.mulLeft_apply] using hcf

/-- **Universal mapping property of the `q`-Weyl algebra.** Given invertible operators `X, Y` on a
`k`-module `V` satisfying `Y X = q • (X Y)`, the assignment `xⁱyʲ ↦ Xⁱ Yʲ` extends to an algebra
homomorphism `qWeylAlgebra k q →ₐ[k] Module.End k V`. -/
noncomputable def toEnd (hrel : (↑Y : Module.End k V) * ↑X = (q : k) • (↑X * ↑Y)) :
    qWeylAlgebra k q →ₐ[k] Module.End k V :=
  AlgHom.ofLinearMap (toEndLinear q X Y)
    (by
      rw [show (1 : qWeylAlgebra k q) = qWeylMono q (0, 0) from (qWeylMono_zero q).symm,
        toEndLinear_qWeylMono]
      simp)
    (toEndLinear_mul q X Y hrel)

@[simp] theorem toEnd_qWeylMono (hrel : (↑Y : Module.End k V) * ↑X = (q : k) • (↑X * ↑Y))
    (p : ℤ × ℤ) : toEnd q X Y hrel (qWeylMono q p) = op X Y p.1 p.2 :=
  toEndLinear_qWeylMono q X Y p

/-- Characterizing equation: the lift sends the generator `x = qMono (1,0)` to `X`. -/
theorem toEnd_x (hrel : (↑Y : Module.End k V) * ↑X = (q : k) • (↑X * ↑Y)) :
    toEnd q X Y hrel (qWeylMono q (1, 0)) = (↑X : Module.End k V) := by
  rw [toEnd_qWeylMono]
  simp [op]

/-- Characterizing equation: the lift sends the generator `y = qMono (0,1)` to `Y`. -/
theorem toEnd_y (hrel : (↑Y : Module.End k V) * ↑X = (q : k) • (↑X * ↑Y)) :
    toEnd q X Y hrel (qWeylMono q (0, 1)) = (↑Y : Module.End k V) := by
  rw [toEnd_qWeylMono]
  simp [op]

/-! ### Convenience wrapper: `(V, X, Y)` data as a `qWeylAlgebra`-module -/

/-- The `qWeylAlgebra k q`-module structure on `V` obtained from the generator actions `X, Y`.
Here `a • v = toEnd a v`. -/
@[reducible] noncomputable def module
    (hrel : (↑Y : Module.End k V) * ↑X = (q : k) • (↑X * ↑Y)) :
    Module (qWeylAlgebra k q) V :=
  Module.compHom V (toEnd q X Y hrel).toRingHom

theorem module_smul (hrel : (↑Y : Module.End k V) * ↑X = (q : k) • (↑X * ↑Y))
    (a : qWeylAlgebra k q) (v : V) :
    letI := module q X Y hrel
    a • v = toEnd q X Y hrel a v := rfl

/-- The module produced by `module` is compatible with the ambient `k`-action: it forms a scalar
tower `k → qWeylAlgebra k q → V`, matching the representation API used in `Problem2_7_5.lean`. -/
theorem module_isScalarTower (hrel : (↑Y : Module.End k V) * ↑X = (q : k) • (↑X * ↑Y)) :
    letI := module q X Y hrel
    IsScalarTower k (qWeylAlgebra k q) V := by
  letI := module q X Y hrel
  refine ⟨fun c a v => ?_⟩
  change toEnd q X Y hrel (c • a) v = c • (toEnd q X Y hrel a v)
  rw [map_smul, LinearMap.smul_apply]

end Etingof.QWeyl
