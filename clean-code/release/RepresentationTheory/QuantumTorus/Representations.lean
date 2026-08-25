/-
Copyright (c) 2026 mathlib-initiative. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: mathlib-initiative
-/

import Mathlib
import RepresentationTheory.Algebra.Module.TwistedLatticeShifts

/-!
# Representations of the quantum torus

This module constructs representations of the quantum torus from pairs of invertible
endomorphisms satisfying the quantum commutation relation. It develops the monomial basis of the
concrete twisted-lattice-shift algebra, constructs the induced algebra homomorphism, and packages
it as a compatible module structure.
-/

namespace RepresentationTheory.QuantumTorus.Representations

open RepresentationTheory.Algebra.Module.TwistedLatticeShifts Finsupp Module

variable {k : Type*} [CommRing k] (q : kˣ)
variable {V : Type*} [AddCommGroup V] [Module k V]

/-- The endomorphism monomial determined by two invertible endomorphisms and two integer exponents. -/
noncomputable def monomialEnd (X Y : (Module.End k V)ˣ) (i j : ℤ) : Module.End k V :=
  ↑(X ^ i) * ↑(Y ^ j)

variable (X Y : (Module.End k V)ˣ)

/-- The endomorphism monomial with both exponents zero is one. -/
@[simp] theorem monomialEnd_zero_zero : monomialEnd X Y 0 0 = 1 := by
  simp [monomialEnd]

/-- The product of the underlying endomorphisms of two integer powers of a unit is the underlying endomorphism at the sum of the exponents. -/
theorem val_zpow_mul_val_zpow (i i' : ℤ) :
    (↑(X ^ i) : Module.End k V) * ↑(X ^ i') = ↑(X ^ (i + i')) := by
  rw [zpow_add];
  rfl

/-- An auxiliary form of the identity multiplying the underlying endomorphisms of two integer powers of a unit. -/
theorem auxiliaryValZpowMulValZpow (j j' : ℤ) :
    (↑(Y ^ j) : Module.End k V) * ↑(Y ^ j') = ↑(Y ^ (j + j')) := by
  rw [zpow_add];
  rfl

/-- The unit of the endomorphism algebra induced by a unit of the coefficient ring. -/
noncomputable def scalarEndUnit : (Module.End k V)ˣ :=
  Units.map (algebraMap k (Module.End k V)).toMonoidHom q

/-- The endomorphism underlying the scalar unit is the image of the coefficient-ring unit under the algebra map. -/
@[simp] theorem scalarEndUnit_val :
    ((scalarEndUnit q : (Module.End k V)ˣ) : Module.End k V) =
      algebraMap k (Module.End k V) (q : k) := rfl

/-- The endomorphism underlying an integer power of the scalar unit is the algebra-map image of the corresponding power of the coefficient-ring unit. -/
theorem scalarEndUnit_zpow_val (a : ℤ) :
    ((scalarEndUnit q ^ a : (Module.End k V)ˣ) : Module.End k V) =
      algebraMap k (Module.End k V) ((q ^ a : kˣ) : k) := by
  have h : (scalarEndUnit q : (Module.End k V)ˣ) ^ a = scalarEndUnit (q ^ a) :=
    (map_zpow (Units.map (algebraMap k (Module.End k V)).toMonoidHom) q a).symm
  rw [h, scalarEndUnit_val]

/-- Left multiplication by the endomorphism underlying the scalar unit is scalar multiplication by the coefficient-ring unit. -/
theorem scalarEndUnit_val_mul (m : Module.End k V) :
    ((scalarEndUnit q : (Module.End k V)ˣ) : Module.End k V) * m = (q : k) • m := by
  rw [scalarEndUnit_val, ← Algebra.smul_def]

/-- The scalar endomorphism unit commutes with every unit of the endomorphism algebra. -/
theorem scalarEndUnit_commute (u : (Module.End k V)ˣ) : Commute (scalarEndUnit q) u := by
  refine Units.ext ?_
  rw [Units.val_mul, Units.val_mul, scalarEndUnit_val]
  exact Algebra.commutes (q : k) (u : Module.End k V)

section Relation

/-- For quantum-commuting endomorphism units, `Y * X` is the scalar endomorphism unit times `X * Y`. -/
theorem mul_eq_scalarEndUnit_mul_of_qCommute
    (hrel : (↑Y : Module.End k V) * ↑X = (q : k) • (↑X * ↑Y)) :
    Y * X = scalarEndUnit q * X * Y := by
  refine Units.ext ?_
  rw [Units.val_mul, Units.val_mul, Units.val_mul, scalarEndUnit_val, ← Algebra.smul_def,
    smul_mul_assoc, ← hrel]

/-- For quantum-commuting endomorphism units, moving `Y` past `X⁻¹` introduces the inverse scalar endomorphism unit. -/
theorem mul_inv_eq_invScalarEndUnit_mul_of_qCommute
    (hrel : (↑Y : Module.End k V) * ↑X = (q : k) • (↑X * ↑Y)) :
    Y * X⁻¹ = (scalarEndUnit q)⁻¹ * X⁻¹ * Y := by
  have hU := mul_eq_scalarEndUnit_mul_of_qCommute q X Y hrel
  have hc : X⁻¹ * scalarEndUnit q = scalarEndUnit q * X⁻¹ :=
    ((scalarEndUnit_commute q X⁻¹).symm).eq
  have h1 : X⁻¹ * Y = scalarEndUnit q * Y * X⁻¹ := by
    calc X⁻¹ * Y = X⁻¹ * (Y * X) * X⁻¹ := by group
      _ = X⁻¹ * (scalarEndUnit q * X * Y) * X⁻¹ := by rw [hU]
      _ = (X⁻¹ * scalarEndUnit q) * X * Y * X⁻¹ := by group
      _ = (scalarEndUnit q * X⁻¹) * X * Y * X⁻¹ := by rw [hc]
      _ = scalarEndUnit q * Y * X⁻¹ := by group
  calc Y * X⁻¹ = (scalarEndUnit q)⁻¹ * (scalarEndUnit q * Y * X⁻¹) := by group
    _ = (scalarEndUnit q)⁻¹ * (X⁻¹ * Y) := by rw [← h1]
    _ = (scalarEndUnit q)⁻¹ * X⁻¹ * Y := by group

/-- Moving `Y` past an integer power of `X` introduces the same integer power of the scalar endomorphism unit. -/
theorem mul_zpow_eq_scalarEndUnit_zpow_mul_of_qCommute
    (hrel : (↑Y : Module.End k V) * ↑X = (q : k) • (↑X * ↑Y)) (n : ℤ) :
    Y * X ^ n = scalarEndUnit q ^ n * X ^ n * Y := by
  have hU := mul_eq_scalarEndUnit_mul_of_qCommute q X Y hrel
  have hUi := mul_inv_eq_invScalarEndUnit_mul_of_qCommute q X Y hrel
  induction n using Int.induction_on with
  | zero => simp
  | succ n ih =>
      have hc : X ^ (n : ℤ) * scalarEndUnit q = scalarEndUnit q * X ^ (n : ℤ) :=
        ((scalarEndUnit_commute q (X ^ (n : ℤ))).symm).eq
      rw [zpow_add_one X n, zpow_add_one (scalarEndUnit q) n, ← mul_assoc, ih,
        mul_assoc (scalarEndUnit q ^ (n : ℤ) * X ^ (n : ℤ)) Y X, hU,
        show (scalarEndUnit q ^ (n : ℤ) * X ^ (n : ℤ)) * (scalarEndUnit q * X * Y) =
            scalarEndUnit q ^ (n : ℤ) * (X ^ (n : ℤ) * scalarEndUnit q) * X * Y from by
          group,
        hc]
      group
  | pred n ih =>
      have hc : X ^ (-(n : ℤ)) * (scalarEndUnit q)⁻¹ =
          (scalarEndUnit q)⁻¹ * X ^ (-(n : ℤ)) :=
        ((scalarEndUnit_commute q (X ^ (-(n : ℤ)))).symm).inv_right.eq
      rw [zpow_sub_one X (-(n : ℤ)), zpow_sub_one (scalarEndUnit q) (-(n : ℤ)), ← mul_assoc,
        ih, mul_assoc (scalarEndUnit q ^ (-(n : ℤ)) * X ^ (-(n : ℤ))) Y X⁻¹, hUi,
        show (scalarEndUnit q ^ (-(n : ℤ)) * X ^ (-(n : ℤ))) *
              ((scalarEndUnit q)⁻¹ * X⁻¹ * Y) =
            scalarEndUnit q ^ (-(n : ℤ)) * (X ^ (-(n : ℤ)) * (scalarEndUnit q)⁻¹) * X⁻¹ * Y from by
          group,
        hc]
      group

/-- Moving an integer power of `Y` past an integer power of `X` introduces the scalar endomorphism unit raised to the product of the exponents. -/
theorem zpow_mul_zpow_eq_scalarEndUnit_zpow_mul_of_qCommute
    (hrel : (↑Y : Module.End k V) * ↑X = (q : k) • (↑X * ↑Y)) (m n : ℤ) :
    Y ^ m * X ^ n = scalarEndUnit q ^ (m * n) * X ^ n * Y ^ m := by
  have hR := mul_zpow_eq_scalarEndUnit_zpow_mul_of_qCommute q X Y hrel
  induction m using Int.induction_on with
  | zero => simp
  | succ m ih =>
      have hc : Y ^ (m : ℤ) * scalarEndUnit q ^ n =
          scalarEndUnit q ^ n * Y ^ (m : ℤ) :=
        (((scalarEndUnit_commute q (Y ^ (m : ℤ))).symm).zpow_right n).eq
      rw [zpow_add_one Y m, mul_assoc, hR n,
        show Y ^ (m : ℤ) * (scalarEndUnit q ^ n * X ^ n * Y) =
            (Y ^ (m : ℤ) * scalarEndUnit q ^ n) * X ^ n * Y from by group,
        hc,
        show scalarEndUnit q ^ n * Y ^ (m : ℤ) * X ^ n * Y =
            scalarEndUnit q ^ n * (Y ^ (m : ℤ) * X ^ n) * Y from by group,
        ih,
        show scalarEndUnit q ^ n *
              (scalarEndUnit q ^ ((m : ℤ) * n) * X ^ n * Y ^ (m : ℤ)) * Y =
            (scalarEndUnit q ^ n * scalarEndUnit q ^ ((m : ℤ) * n)) * X ^ n *
              (Y ^ (m : ℤ) * Y) from by group,
        ← zpow_add, ← zpow_add_one Y m,
        show n + (m : ℤ) * n = ((m : ℤ) + 1) * n from by ring]
  | pred m ih =>
      have hc : Y ^ (-(m : ℤ)) * scalarEndUnit q ^ (-n) =
          scalarEndUnit q ^ (-n) * Y ^ (-(m : ℤ)) :=
        (((scalarEndUnit_commute q (Y ^ (-(m : ℤ)))).symm).zpow_right (-n)).eq
      have hRi : Y⁻¹ * X ^ n = scalarEndUnit q ^ (-n) * X ^ n * Y⁻¹ := by
        have e1 : X ^ n * Y⁻¹ = scalarEndUnit q ^ n * (Y⁻¹ * X ^ n) := by
          calc X ^ n * Y⁻¹ = (Y⁻¹ * (Y * X ^ n)) * Y⁻¹ := by group
            _ = (Y⁻¹ * (scalarEndUnit q ^ n * X ^ n * Y)) * Y⁻¹ := by rw [hR n]
            _ = (Y⁻¹ * scalarEndUnit q ^ n) * X ^ n * (Y * Y⁻¹) := by group
            _ = (scalarEndUnit q ^ n * Y⁻¹) * X ^ n * (Y * Y⁻¹) := by
                  rw [(((scalarEndUnit_commute q Y).symm).zpow_right n).inv_left.eq]
            _ = scalarEndUnit q ^ n * (Y⁻¹ * X ^ n) := by group
        calc Y⁻¹ * X ^ n
            = scalarEndUnit q ^ (-n) * (scalarEndUnit q ^ n * (Y⁻¹ * X ^ n)) := by
                rw [show scalarEndUnit q ^ (-n) *
                      (scalarEndUnit q ^ n * (Y⁻¹ * X ^ n)) =
                    (scalarEndUnit q ^ (-n) * scalarEndUnit q ^ n) *
                      (Y⁻¹ * X ^ n) from by group, ← zpow_add]
                simp
          _ = scalarEndUnit q ^ (-n) * (X ^ n * Y⁻¹) := by rw [← e1]
          _ = scalarEndUnit q ^ (-n) * X ^ n * Y⁻¹ := by group
      rw [zpow_sub_one Y (-(m : ℤ)), mul_assoc, hRi,
        show Y ^ (-(m : ℤ)) * (scalarEndUnit q ^ (-n) * X ^ n * Y⁻¹) =
            (Y ^ (-(m : ℤ)) * scalarEndUnit q ^ (-n)) * X ^ n * Y⁻¹ from by group,
        hc,
        show scalarEndUnit q ^ (-n) * Y ^ (-(m : ℤ)) * X ^ n * Y⁻¹ =
            scalarEndUnit q ^ (-n) * (Y ^ (-(m : ℤ)) * X ^ n) * Y⁻¹ from by group,
        ih,
        show scalarEndUnit q ^ (-n) *
              (scalarEndUnit q ^ ((-(m : ℤ)) * n) * X ^ n * Y ^ (-(m : ℤ))) * Y⁻¹ =
            (scalarEndUnit q ^ (-n) * scalarEndUnit q ^ ((-(m : ℤ)) * n)) * X ^ n *
              (Y ^ (-(m : ℤ)) * Y⁻¹) from by group,
        ← zpow_add, ← zpow_sub_one Y (-(m : ℤ)),
        show (-n) + (-(m : ℤ)) * n = ((-(m : ℤ)) - 1) * n from by ring]

/-- Products of endomorphism monomials satisfy the displayed twisted exponent-addition formula under the quantum commutation relation. -/
theorem monomialEnd_mul
    (hrel : (↑Y : Module.End k V) * ↑X = (q : k) • (↑X * ↑Y)) (i j i' j' : ℤ) :
    monomialEnd X Y i j * monomialEnd X Y i' j' =
      ((q ^ (j * i') : kˣ) : k) • monomialEnd X Y (i + i') (j + j') := by
  have h := congrArg (fun u : (Module.End k V)ˣ => (u : Module.End k V))
    (zpow_mul_zpow_eq_scalarEndUnit_zpow_mul_of_qCommute q X Y hrel j i')
  simp only [Units.val_mul, scalarEndUnit_zpow_val] at h
  simp only [monomialEnd]
  calc (↑(X ^ i) * ↑(Y ^ j)) * (↑(X ^ i') * ↑(Y ^ j')) =
      ↑(X ^ i) * (↑(Y ^ j) * ↑(X ^ i')) * ↑(Y ^ j') := by group
    _ = ↑(X ^ i) *
          (algebraMap k (Module.End k V) ((q ^ (j * i') : kˣ) : k) * ↑(X ^ i') *
            ↑(Y ^ j)) * ↑(Y ^ j') := by rw [h]
    _ = ((q ^ (j * i') : kˣ) : k) • (↑(X ^ (i + i')) * ↑(Y ^ (j + j'))) := by
          rw [← Algebra.smul_def, smul_mul_assoc, mul_smul_comm, smul_mul_assoc]
          congr 1
          rw [← val_zpow_mul_val_zpow, ← auxiliaryValZpowMulValZpow]
          simp only [mul_assoc]

end Relation

/-! ### The monomial basis of the source algebra -/

/-- The quantum-torus monomial associated with a pair of integer exponents. -/
noncomputable def monomial (p : ℤ × ℤ) : twistedLatticeShiftSubalgebra k q :=
  ⟨twistedLatticeShift k q p, twistedLatticeShift_mem_generatedSubalgebra k q p⟩

/-- The underlying value of a quantum-torus monomial is the corresponding displayed ambient element. -/
@[simp] theorem monomial_val (p : ℤ × ℤ) :
    ((monomial q p : twistedLatticeShiftSubalgebra k q) :
        Module.End k (Auxiliary k)) = twistedLatticeShift k q p := rfl

/-- The quantum-torus monomial with both exponents zero is one. -/
theorem monomial_zero_zero : monomial q (0, 0) = 1 := by
  apply Subtype.ext
  rw [monomial_val, OneMemClass.coe_one, twistedLatticeShift_zero_zero]

/-- The product of two quantum-torus monomials is the monomial at the sum of their exponent pairs, scaled by the indicated power of the quantum parameter. -/
theorem monomial_mul (p r : ℤ × ℤ) :
    monomial q p * monomial q r =
      (↑(q ^ (p.2 * r.1)) : k) • monomial q (p.1 + r.1, p.2 + r.2) := by
  apply Subtype.ext
  rw [MulMemClass.coe_mul, monomial_val, monomial_val, Subalgebra.coe_smul, monomial_val,
    twistedLatticeShift_mul]

/-- A natural power of a monomial supported in the first exponent multiplies that exponent by the power. -/
theorem monomial_firstExponent_pow (i : ℤ) (m : ℕ) :
    monomial q (i, 0) ^ m = monomial q (i * m, 0) := by
  induction m with
  | zero => rw [pow_zero, Nat.cast_zero, mul_zero, monomial_zero_zero]
  | succ m ih =>
    rw [pow_succ, ih, monomial_mul]
    simp only [zero_mul, zpow_zero, Units.val_one, one_smul, add_zero]
    congr 2
    push_cast
    ring

/-- A natural power of a monomial supported in the second exponent multiplies that exponent by the power. -/
theorem monomial_secondExponent_pow (j : ℤ) (m : ℕ) :
    monomial q (0, j) ^ m = monomial q (0, j * m) := by
  induction m with
  | zero => rw [pow_zero, Nat.cast_zero, mul_zero, monomial_zero_zero]
  | succ m ih =>
    rw [pow_succ, ih, monomial_mul]
    simp only [mul_zero, zpow_zero, Units.val_one, one_smul, add_zero]
    congr 2
    push_cast
    ring

/-- The quantum-torus monomials are linearly independent over the coefficient ring. -/
theorem monomial_linearIndependent : LinearIndependent k (monomial q) := by
  apply LinearIndependent.of_comp (twistedLatticeShiftSubalgebra k q).val.toLinearMap
  have h : (twistedLatticeShiftSubalgebra k q).val.toLinearMap ∘ monomial q =
      twistedLatticeShift k q := rfl
  rw [h]
  exact twistedLatticeShift_linearIndependent k q

/-- The span of the quantum-torus monomials contains the whole algebra. -/
theorem top_le_span_range_monomial : ⊤ ≤ Submodule.span k (Set.range (monomial q)) := by
  rintro a -
  have h1 : (a : Module.End k (Auxiliary k)) ∈
      Submodule.span k (Set.range (twistedLatticeShift k q)) := by
    rw [← twistedLatticeShiftSubalgebra_toSubmodule, Subalgebra.mem_toSubmodule]
    exact a.2
  have himg : Submodule.map (twistedLatticeShiftSubalgebra k q).val.toLinearMap
        (Submodule.span k (Set.range (monomial q))) =
      Submodule.span k (Set.range (twistedLatticeShift k q)) := by
    rw [Submodule.map_span]
    congr 1
    rw [← Set.range_comp]
    rfl
  rw [← himg] at h1
  obtain ⟨a', ha'mem, ha'eq⟩ := h1
  have hpa : a' = a := Subtype.ext ha'eq
  rwa [hpa] at ha'mem

/-- The basis of the quantum torus indexed by pairs of integer exponents. -/
noncomputable def monomialBasis : Basis (ℤ × ℤ) k (twistedLatticeShiftSubalgebra k q) :=
  Basis.mk (monomial_linearIndependent q) (top_le_span_range_monomial q)

/-- The basis vector at a pair of integer exponents is the corresponding quantum-torus monomial. -/
@[simp] theorem monomialBasis_apply (p : ℤ × ℤ) : monomialBasis q p = monomial q p :=
  Basis.mk_apply _ _ _

/-! ### The representation into the endomorphism algebra -/

/-- The coefficient-linear map from the quantum torus to endomorphisms determined by two invertible endomorphisms. -/
noncomputable def monomialLinearMap :
    twistedLatticeShiftSubalgebra k q →ₗ[k] Module.End k V :=
  (monomialBasis q).constr k (fun p => monomialEnd X Y p.1 p.2)

/-- The monomial linear map sends a quantum-torus monomial to the endomorphism monomial with the same exponent pair. -/
@[simp] theorem monomialLinearMap_monomial (p : ℤ × ℤ) :
    monomialLinearMap q X Y (monomial q p) = monomialEnd X Y p.1 p.2 := by
  rw [monomialLinearMap, ← monomialBasis_apply, Basis.constr_basis]

/-- Under the quantum commutation relation, the monomial linear map preserves products of basis monomials. -/
theorem monomialLinearMap_map_mul_monomial
    (hrel : (↑Y : Module.End k V) * ↑X = (q : k) • (↑X * ↑Y)) (p r : ℤ × ℤ) :
    monomialLinearMap q X Y (monomial q p * monomial q r) =
      monomialLinearMap q X Y (monomial q p) * monomialLinearMap q X Y (monomial q r) := by
  rw [monomial_mul, map_smul, monomialLinearMap_monomial, monomialLinearMap_monomial,
    monomialLinearMap_monomial, monomialEnd_mul q X Y hrel]

/-- Under the quantum commutation relation, the monomial linear map preserves multiplication when the right factor is a basis monomial. -/
theorem monomialLinearMap_map_mul_monomial_right
    (hrel : (↑Y : Module.End k V) * ↑X = (q : k) • (↑X * ↑Y))
    (a : twistedLatticeShiftSubalgebra k q) (r : ℤ × ℤ) :
    monomialLinearMap q X Y (a * monomial q r) =
      monomialLinearMap q X Y a * monomialLinearMap q X Y (monomial q r) := by
  have h : (monomialLinearMap q X Y).comp (LinearMap.mulRight k (monomial q r)) =
      (LinearMap.mulRight k (monomialLinearMap q X Y (monomial q r))).comp
        (monomialLinearMap q X Y) := by
    apply (monomialBasis q).ext
    intro p
    simp only [LinearMap.comp_apply, LinearMap.mulRight_apply, monomialBasis_apply]
    exact monomialLinearMap_map_mul_monomial q X Y hrel p r
  have hcf := DFunLike.congr_fun h a
  simpa only [LinearMap.comp_apply, LinearMap.mulRight_apply] using hcf

/-- Under the quantum commutation relation, the monomial linear map preserves multiplication on all quantum-torus elements. -/
theorem monomialLinearMap_map_mul
    (hrel : (↑Y : Module.End k V) * ↑X = (q : k) • (↑X * ↑Y))
    (a b : twistedLatticeShiftSubalgebra k q) :
    monomialLinearMap q X Y (a * b) = monomialLinearMap q X Y a * monomialLinearMap q X Y b := by
  have h : (monomialLinearMap q X Y).comp (LinearMap.mulLeft k a) =
      (LinearMap.mulLeft k (monomialLinearMap q X Y a)).comp (monomialLinearMap q X Y) := by
    apply (monomialBasis q).ext
    intro r
    simp only [LinearMap.comp_apply, LinearMap.mulLeft_apply, monomialBasis_apply]
    exact monomialLinearMap_map_mul_monomial_right q X Y hrel a r
  have hcf := DFunLike.congr_fun h b
  simpa only [LinearMap.comp_apply, LinearMap.mulLeft_apply] using hcf

/-- The quantum-torus algebra representation determined by two invertible endomorphisms satisfying the quantum commutation relation. -/
noncomputable def representationOfQCommute
    (hrel : (↑Y : Module.End k V) * ↑X = (q : k) • (↑X * ↑Y)) :
    twistedLatticeShiftSubalgebra k q →ₐ[k] Module.End k V :=
  AlgHom.ofLinearMap (monomialLinearMap q X Y)
    (by
      rw [show (1 : twistedLatticeShiftSubalgebra k q) = monomial q (0, 0) from
        (monomial_zero_zero q).symm, monomialLinearMap_monomial]
      simp)
    (monomialLinearMap_map_mul q X Y hrel)

/-- The representation determined by quantum-commuting units sends a quantum-torus monomial to the corresponding endomorphism monomial. -/
@[simp] theorem representationOfQCommute_monomial
    (hrel : (↑Y : Module.End k V) * ↑X = (q : k) • (↑X * ↑Y)) (p : ℤ × ℤ) :
    representationOfQCommute q X Y hrel (monomial q p) = monomialEnd X Y p.1 p.2 :=
  monomialLinearMap_monomial q X Y p

/-- The representation determined by quantum-commuting units sends the first distinguished monomial to the first endomorphism unit. -/
theorem representationOfQCommute_firstGenerator
    (hrel : (↑Y : Module.End k V) * ↑X = (q : k) • (↑X * ↑Y)) :
    representationOfQCommute q X Y hrel (monomial q (1, 0)) =
      (↑X : Module.End k V) := by
  rw [representationOfQCommute_monomial]
  simp [monomialEnd]

/-- The representation determined by quantum-commuting units sends the second distinguished monomial to the second endomorphism unit. -/
theorem representationOfQCommute_secondGenerator
    (hrel : (↑Y : Module.End k V) * ↑X = (q : k) • (↑X * ↑Y)) :
    representationOfQCommute q X Y hrel (monomial q (0, 1)) =
      (↑Y : Module.End k V) := by
  rw [representationOfQCommute_monomial]
  simp [monomialEnd]

/-! ### The induced module structure -/

/-- The quantum-torus module structure determined by two invertible endomorphisms satisfying the quantum commutation relation. -/
@[reducible] noncomputable def moduleOfQCommute
    (hrel : (↑Y : Module.End k V) * ↑X = (q : k) • (↑X * ↑Y)) :
    Module (twistedLatticeShiftSubalgebra k q) V :=
  Module.compHom V (representationOfQCommute q X Y hrel).toRingHom

/-- The quantum-torus module action agrees with evaluation of the representation determined by the two quantum-commuting units. -/
theorem moduleOfQCommute_smul_eq_representation_apply
    (hrel : (↑Y : Module.End k V) * ↑X = (q : k) • (↑X * ↑Y))
    (a : twistedLatticeShiftSubalgebra k q) (v : V) :
    letI := moduleOfQCommute q X Y hrel
    a • v = representationOfQCommute q X Y hrel a v := rfl

/-- The coefficient-ring action and quantum-torus action determined by quantum-commuting units form a scalar tower. -/
theorem moduleOfQCommute_isScalarTower
    (hrel : (↑Y : Module.End k V) * ↑X = (q : k) • (↑X * ↑Y)) :
    letI := moduleOfQCommute q X Y hrel
    IsScalarTower k (twistedLatticeShiftSubalgebra k q) V := by
  letI := moduleOfQCommute q X Y hrel
  refine ⟨fun c a v => ?_⟩
  change representationOfQCommute q X Y hrel (c • a) v =
    c • (representationOfQCommute q X Y hrel a v)
  rw [map_smul, LinearMap.smul_apply]

end RepresentationTheory.QuantumTorus.Representations
