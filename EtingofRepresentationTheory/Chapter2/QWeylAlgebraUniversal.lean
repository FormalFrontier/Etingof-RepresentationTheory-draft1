import EtingofRepresentationTheory.Chapter2.Proposition2_7_1_ii
import Mathlib.LinearAlgebra.Basis.Basic
import Mathlib.Tactic.Group

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

open Etingof Finsupp

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

end Etingof.QWeyl
