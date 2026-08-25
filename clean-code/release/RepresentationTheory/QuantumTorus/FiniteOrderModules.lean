/-
Copyright (c) 2026 mathlib-initiative. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: mathlib-initiative
-/

import RepresentationTheory.ParameterizedAlgebra.FiniteSimpleModules

/-! # Finite-Order Modules -/

namespace RepresentationTheory.QuantumTorus.FiniteOrderModules

open RepresentationTheory.Algebra.Module.TwistedLatticeShifts
  RepresentationTheory.QuantumTorus.Representations Finsupp Module

section Family

variable (q α β : ℂˣ) (N : ℕ) [NeZero N]

/-! ### The twisted cyclic shift `x` and the diagonal `y` -/

/-- A complex scalar indexed by `Fin N` and parameterized by a complex unit. -/
noncomputable def unitIndexedScalar (k : Fin N) : ℂ := if k = 0 then (α : ℂ) else 1

/-- Every scalar in the unit-parameterized indexed family is nonzero. -/
theorem unitIndexedScalar_ne_zero (k : Fin N) : unitIndexedScalar α N k ≠ 0 := by
  unfold unitIndexedScalar; split_ifs with h
  · exact α.ne_zero
  · exact one_ne_zero

/-- The parameterized cyclic shift endomorphism on complex-valued functions on `Fin N`. -/
noncomputable def cyclicShiftEnd : (Fin N → ℂ) →ₗ[ℂ] (Fin N → ℂ) where
  toFun f := fun k => unitIndexedScalar α N k • f (k - 1)
  map_add' f g := by funext k; simp only [Pi.add_apply, smul_eq_mul]; ring
  map_smul' c f := by funext k; simp only [Pi.smul_apply, smul_eq_mul, RingHom.id_apply]; ring

/-- The inverse of the parameterized cyclic shift endomorphism on complex-valued functions on `Fin N`. -/
noncomputable def inverseCyclicShiftEnd : (Fin N → ℂ) →ₗ[ℂ] (Fin N → ℂ) where
  toFun f := fun k => (unitIndexedScalar α N (k + 1))⁻¹ • f (k + 1)
  map_add' f g := by funext k; simp only [Pi.add_apply, smul_eq_mul]; ring
  map_smul' c f := by funext k; simp only [Pi.smul_apply, smul_eq_mul, RingHom.id_apply]; ring

/-- The inverse cyclic shift composed with the cyclic shift is the identity. -/
theorem inverseCyclicShiftEnd_comp_cyclicShiftEnd :
    (inverseCyclicShiftEnd α N).comp (cyclicShiftEnd α N) = LinearMap.id := by
  ext f k
  simp only [LinearMap.comp_apply, inverseCyclicShiftEnd, cyclicShiftEnd, LinearMap.coe_mk,
    AddHom.coe_mk, LinearMap.id_coe, id]
  rw [add_sub_cancel_right k 1, smul_smul,
    inv_mul_cancel₀ (unitIndexedScalar_ne_zero α N (k + 1)), one_smul]

/-- The cyclic shift composed with its inverse is the identity. -/
theorem cyclicShiftEnd_comp_inverseCyclicShiftEnd :
    (cyclicShiftEnd α N).comp (inverseCyclicShiftEnd α N) = LinearMap.id := by
  ext f k
  simp only [LinearMap.comp_apply, inverseCyclicShiftEnd, cyclicShiftEnd, LinearMap.coe_mk,
    AddHom.coe_mk, LinearMap.id_coe, id]
  rw [sub_add_cancel k 1, smul_smul, mul_inv_cancel₀ (unitIndexedScalar_ne_zero α N k), one_smul]

/-- The unit of the endomorphism algebra defined by the cyclic shift and its inverse. -/
noncomputable def cyclicShiftUnit : (Module.End ℂ (Fin N → ℂ))ˣ where
  val := cyclicShiftEnd α N
  inv := inverseCyclicShiftEnd α N
  val_inv := cyclicShiftEnd_comp_inverseCyclicShiftEnd α N
  inv_val := inverseCyclicShiftEnd_comp_cyclicShiftEnd α N

/-- The endomorphism underlying the cyclic shift unit is the cyclic shift. -/
@[simp] theorem cyclicShiftUnit_val :
    (cyclicShiftUnit α N : Module.End ℂ (Fin N → ℂ)) = cyclicShiftEnd α N := rfl

/-- A complex scalar indexed by `Fin N` and parameterized by two complex units. -/
noncomputable def twoUnitIndexedScalar (k : Fin N) : ℂ := (β : ℂ) * (q : ℂ) ^ (k : ℕ)

omit [NeZero N] in
/-- Every scalar in the two-unit-parameterized indexed family is nonzero. -/
theorem twoUnitIndexedScalar_ne_zero (k : Fin N) : twoUnitIndexedScalar q β N k ≠ 0 :=
  mul_ne_zero β.ne_zero (pow_ne_zero _ q.ne_zero)

/-- The parameterized diagonal weight endomorphism on complex-valued functions on `Fin N`. -/
noncomputable def diagonalWeightEnd : (Fin N → ℂ) →ₗ[ℂ] (Fin N → ℂ) where
  toFun f := fun k => twoUnitIndexedScalar q β N k • f k
  map_add' f g := by funext k; simp only [Pi.add_apply, smul_eq_mul]; ring
  map_smul' c f := by funext k; simp only [Pi.smul_apply, smul_eq_mul, RingHom.id_apply]; ring

/-- The inverse of the parameterized diagonal weight endomorphism on complex-valued functions on `Fin N`. -/
noncomputable def inverseDiagonalWeightEnd : (Fin N → ℂ) →ₗ[ℂ] (Fin N → ℂ) where
  toFun f := fun k => (twoUnitIndexedScalar q β N k)⁻¹ • f k
  map_add' f g := by funext k; simp only [Pi.add_apply, smul_eq_mul]; ring
  map_smul' c f := by funext k; simp only [Pi.smul_apply, smul_eq_mul, RingHom.id_apply]; ring

omit [NeZero N] in
/-- The inverse diagonal weight endomorphism composed with the diagonal weight endomorphism is the identity. -/
theorem inverseDiagonalWeightEnd_comp_diagonalWeightEnd :
    (inverseDiagonalWeightEnd q β N).comp (diagonalWeightEnd q β N) = LinearMap.id := by
  ext f k
  simp only [LinearMap.comp_apply, inverseDiagonalWeightEnd, diagonalWeightEnd,
    LinearMap.coe_mk, AddHom.coe_mk, LinearMap.id_coe, id]
  rw [smul_smul, inv_mul_cancel₀ (twoUnitIndexedScalar_ne_zero q β N k), one_smul]

omit [NeZero N] in
/-- The diagonal weight endomorphism composed with its inverse is the identity. -/
theorem diagonalWeightEnd_comp_inverseDiagonalWeightEnd :
    (diagonalWeightEnd q β N).comp (inverseDiagonalWeightEnd q β N) = LinearMap.id := by
  ext f k
  simp only [LinearMap.comp_apply, inverseDiagonalWeightEnd, diagonalWeightEnd,
    LinearMap.coe_mk, AddHom.coe_mk, LinearMap.id_coe, id]
  rw [smul_smul, mul_inv_cancel₀ (twoUnitIndexedScalar_ne_zero q β N k), one_smul]

/-- The unit of the endomorphism algebra defined by the diagonal weight endomorphism and its inverse. -/
noncomputable def diagonalWeightUnit : (Module.End ℂ (Fin N → ℂ))ˣ where
  val := diagonalWeightEnd q β N
  inv := inverseDiagonalWeightEnd q β N
  val_inv := diagonalWeightEnd_comp_inverseDiagonalWeightEnd q β N
  inv_val := inverseDiagonalWeightEnd_comp_diagonalWeightEnd q β N

omit [NeZero N] in
/-- The endomorphism underlying the diagonal weight unit is the diagonal weight endomorphism. -/
@[simp] theorem diagonalWeightUnit_val :
    (diagonalWeightUnit q β N : Module.End ℂ (Fin N → ℂ)) = diagonalWeightEnd q β N := rfl

/-! ### The generator actions on the standard basis -/

/-- The cyclic shift sends a coordinate vector to the next coordinate vector scaled by the corresponding indexed scalar. -/
theorem cyclicShiftEnd_single (m : Fin N) :
    cyclicShiftEnd α N (Pi.single m (1 : ℂ)) =
      unitIndexedScalar α N (m + 1) • Pi.single (m + 1) (1 : ℂ) := by
  classical
  funext i
  simp only [cyclicShiftEnd, LinearMap.coe_mk, AddHom.coe_mk, Pi.smul_apply, smul_eq_mul]
  by_cases hi : i = m + 1
  · subst hi; simp
  · have hne : i - 1 ≠ m := fun h => hi (sub_eq_iff_eq_add.mp h)
    simp [hne, hi]

omit [NeZero N] in
/-- Each coordinate vector is an eigenvector of the diagonal weight endomorphism with the corresponding indexed scalar. -/
theorem diagonalWeightEnd_single (m : Fin N) :
    diagonalWeightEnd q β N (Pi.single m (1 : ℂ)) =
      twoUnitIndexedScalar q β N m • Pi.single m (1 : ℂ) := by
  classical
  funext i
  simp only [diagonalWeightEnd, LinearMap.coe_mk, AddHom.coe_mk, Pi.smul_apply, smul_eq_mul]
  by_cases hi : i = m
  · subst hi; simp
  · simp [hi]

/-! ### The defining relation -/

/-- At an index modulo the order of a complex unit, the indexed power is the unit times the power at the preceding index. -/
theorem pow_val_eq_mul_pow_pred (hqorder : orderOf q = N) (k : Fin N) :
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

/-- The diagonal weight and cyclic shift endomorphisms commute up to the scalar parameter. -/
theorem diagonalWeightEnd_mul_cyclicShiftEnd (hqorder : orderOf q = N) :
    (diagonalWeightEnd q β N) * (cyclicShiftEnd α N) =
      (q : ℂ) • ((cyclicShiftEnd α N) * (diagonalWeightEnd q β N)) := by
  refine LinearMap.ext fun f => ?_
  funext k
  simp only [Module.End.mul_apply, LinearMap.smul_apply, cyclicShiftEnd, diagonalWeightEnd,
    twoUnitIndexedScalar, LinearMap.coe_mk, AddHom.coe_mk, Pi.smul_apply, smul_eq_mul]
  rw [pow_val_eq_mul_pow_pred q N hqorder k]; ring

/-- The endomorphisms underlying the diagonal weight and cyclic shift units commute up to the scalar parameter. -/
theorem diagonalWeightUnit_val_mul_cyclicShiftUnit_val (hqorder : orderOf q = N) :
    ((diagonalWeightUnit q β N : Module.End ℂ (Fin N → ℂ))) *
        (cyclicShiftUnit α N : Module.End ℂ (Fin N → ℂ)) =
      (q : ℂ) • ((cyclicShiftUnit α N : Module.End ℂ (Fin N → ℂ)) *
        (diagonalWeightUnit q β N : Module.End ℂ (Fin N → ℂ))) := by
  rw [cyclicShiftUnit_val, diagonalWeightUnit_val];
  exact diagonalWeightEnd_mul_cyclicShiftEnd q α β N hqorder

/-! ### The classifying module `V(α,β)` -/

/-- The module structure on complex-valued functions on `Fin N` determined by finite-order, shift, and weight parameters. -/
@[reducible] noncomputable def finiteOrderModule (hqorder : orderOf q = N) :
    Module (twistedLatticeShiftSubalgebra ℂ q) (Fin N → ℂ) :=
  moduleOfQCommute q (cyclicShiftUnit α N) (diagonalWeightUnit q β N)
    (diagonalWeightUnit_val_mul_cyclicShiftUnit_val q α β N hqorder)

omit [NeZero N] in
/-- The complex-valued functions on `Fin N` have finrank `N`. -/
theorem finrank_finFunction : Module.finrank ℂ (Fin N → ℂ) = N := by simp

/-- The first distinguished generator acts by the cyclic shift endomorphism. -/
theorem firstGenerator_smul (hqorder : orderOf q = N) (f : Fin N → ℂ) :
    letI := finiteOrderModule q α β N hqorder
    (monomial q (1, 0)) • f = cyclicShiftEnd α N f := by
  letI := finiteOrderModule q α β N hqorder
  rw [moduleOfQCommute_smul_eq_representation_apply]
  change representationOfQCommute q (cyclicShiftUnit α N) (diagonalWeightUnit q β N) _
    (monomial q (1, 0)) f = _
  rw [representationOfQCommute_firstGenerator, cyclicShiftUnit_val]

/-- The second distinguished generator acts by the diagonal weight endomorphism. -/
theorem secondGenerator_smul (hqorder : orderOf q = N) (f : Fin N → ℂ) :
    letI := finiteOrderModule q α β N hqorder
    (monomial q (0, 1)) • f = diagonalWeightEnd q β N f := by
  letI := finiteOrderModule q α β N hqorder
  rw [moduleOfQCommute_smul_eq_representation_apply]
  change representationOfQCommute q (cyclicShiftUnit α N) (diagonalWeightUnit q β N) _
    (monomial q (0, 1)) f = _
  rw [representationOfQCommute_secondGenerator, diagonalWeightUnit_val]

/-- The complex scalar action and the displayed algebra action on the finite-order module form a scalar tower. -/
theorem finiteOrderModule_isScalarTower (hqorder : orderOf q = N) :
    letI := finiteOrderModule q α β N hqorder
    IsScalarTower ℂ (twistedLatticeShiftSubalgebra ℂ q) (Fin N → ℂ) :=
  moduleOfQCommute_isScalarTower q (cyclicShiftUnit α N) (diagonalWeightUnit q β N)
    (diagonalWeightUnit_val_mul_cyclicShiftUnit_val q α β N hqorder)

/-! ### Shifting the index set

`Fin N` carries only an additive group structure here (there is no `NatCast`, since `N` is a
variable constrained merely by `NeZero N`), so "shift by `m` steps" is written as the `ℕ`-multiple
`m • (1 : Fin N)`. -/

/-- The value of a natural multiple of one in `Fin N` is the natural number modulo `N`. -/
theorem nsmul_one_val_eq_mod (m : ℕ) : ((m • (1 : Fin N) : Fin N) : ℕ) = m % N := by
  induction m with
  | zero => simp
  | succ m ih => rw [succ_nsmul, Fin.val_add, ih, Fin.val_one', ← Nat.add_mod]

/-- In `Fin N`, adding one to itself the value of an index times gives that index. -/
theorem val_nsmul_one_fin (k : Fin N) : ((k : ℕ) • (1 : Fin N)) = k :=
  Fin.ext (by rw [nsmul_one_val_eq_mod, Nat.mod_eq_of_lt k.isLt])

/-- In `Fin N`, adding one to itself `N` times gives zero. -/
theorem card_nsmul_one_fin : (N • (1 : Fin N)) = 0 :=
  Fin.ext (by rw [nsmul_one_val_eq_mod, Nat.mod_self]; rfl)

/-! ### Powers of the generators: the central-scalar actions -/

/-- The product of the unit-parameterized indexed scalars around a complete cycle equals the unit parameter. -/
theorem prod_unitIndexedScalar (k : Fin N) :
    ∏ i ∈ Finset.range N, unitIndexedScalar α N (k - i • (1 : Fin N)) = (α : ℂ) := by
  rw [← Fin.prod_univ_eq_prod_range
    (fun i : ℕ => unitIndexedScalar α N (k - i • (1 : Fin N))) N]
  have h : ∀ i : Fin N,
      unitIndexedScalar α N (k - (i : ℕ) • (1 : Fin N)) =
        unitIndexedScalar α N (Equiv.subLeft k i) := by
    intro i; rw [val_nsmul_one_fin]; rfl
  simp_rw [h]
  rw [Equiv.prod_comp (Equiv.subLeft k) (unitIndexedScalar α N)]
  simp only [unitIndexedScalar]
  rw [Finset.prod_ite_eq' Finset.univ (0 : Fin N) (fun _ => (α : ℂ))]
  simp

/-- A power of the cyclic shift evaluates by shifting the index backward and multiplying by the product of the intervening indexed scalars. -/
theorem cyclicShiftEnd_pow_apply (m : ℕ) (f : Fin N → ℂ) (k : Fin N) :
    ((cyclicShiftEnd α N) ^ m) f k =
      (∏ i ∈ Finset.range m, unitIndexedScalar α N (k - i • (1 : Fin N))) •
        f (k - m • (1 : Fin N)) := by
  induction m generalizing f with
  | zero => simp
  | succ m ih =>
    rw [pow_succ, Module.End.mul_apply, ih (cyclicShiftEnd α N f), Finset.prod_range_succ]
    simp only [cyclicShiftEnd, LinearMap.coe_mk, AddHom.coe_mk, smul_eq_mul]
    rw [succ_nsmul, ← sub_sub]
    ring

/-- The `N`-th power of the cyclic shift is scalar multiplication by its parameter. -/
theorem cyclicShiftEnd_pow_card :
    (cyclicShiftEnd α N) ^ N = (α : ℂ) • (1 : Module.End ℂ (Fin N → ℂ)) := by
  refine LinearMap.ext fun f => ?_
  funext k
  rw [cyclicShiftEnd_pow_apply, prod_unitIndexedScalar, card_nsmul_one_fin, sub_zero]
  simp

omit [NeZero N] in
/-- A power of the diagonal weight endomorphism acts pointwise by the corresponding power of the indexed scalar. -/
theorem diagonalWeightEnd_pow_apply (m : ℕ) (f : Fin N → ℂ) (k : Fin N) :
    ((diagonalWeightEnd q β N) ^ m) f k = (twoUnitIndexedScalar q β N k) ^ m • f k := by
  induction m generalizing f with
  | zero => simp
  | succ m ih =>
    rw [pow_succ, Module.End.mul_apply, ih (diagonalWeightEnd q β N f)]
    simp only [diagonalWeightEnd, LinearMap.coe_mk, AddHom.coe_mk, smul_eq_mul, pow_succ]
    ring

omit [NeZero N] in
/-- A complex unit raised to its specified order is one. -/
theorem pow_eq_one_of_orderOf_eq (hqorder : orderOf q = N) : (q : ℂ) ^ N = 1 := by
  have h : q ^ N = 1 := by rw [← hqorder]; exact pow_orderOf_eq_one q
  have hval := congrArg Units.val h
  push_cast at hval
  simpa using hval

omit [NeZero N] in
/-- When the parameter has order `N`, the `N`-th power of the diagonal weight endomorphism is scalar multiplication by the `N`-th power of its scalar parameter. -/
theorem diagonalWeightEnd_pow_card (hqorder : orderOf q = N) :
    (diagonalWeightEnd q β N) ^ N =
      ((β : ℂ) ^ N) • (1 : Module.End ℂ (Fin N → ℂ)) := by
  refine LinearMap.ext fun f => ?_
  funext k
  have hk : ((q : ℂ) ^ (k : ℕ)) ^ N = 1 := by
    rw [← pow_mul, mul_comm, pow_mul, pow_eq_one_of_orderOf_eq q N hqorder, one_pow]
  rw [diagonalWeightEnd_pow_apply]
  simp [twoUnitIndexedScalar, mul_pow, hk]

/-! ### The central character of `V(α,β)`

The elements `xⁿ` and `yⁿ` are central in the quantum torus; on `V(α,β)` they act by the scalars
`α` and `βⁿ`, so the central character of `V(α,β)` is `(α, βⁿ)`. -/

/-- The distinguished element with first exponent `N` acts by the shift parameter. -/
theorem firstGenerator_cardExponent_smul (hqorder : orderOf q = N) (f : Fin N → ℂ) :
    letI := finiteOrderModule q α β N hqorder
    (monomial q ((N : ℤ), 0)) • f = (α : ℂ) • f := by
  letI := finiteOrderModule q α β N hqorder
  rw [moduleOfQCommute_smul_eq_representation_apply]
  change representationOfQCommute q (cyclicShiftUnit α N) (diagonalWeightUnit q β N) _
    (monomial q ((N : ℤ), 0)) f = _
  rw [representationOfQCommute_monomial]
  simp only [monomialEnd, zpow_zero, Units.val_one, mul_one, zpow_natCast,
    Units.val_pow_eq_pow_val, cyclicShiftUnit_val, cyclicShiftEnd_pow_card]
  simp

/-- The distinguished element with second exponent `N` acts by the `N`-th power of the weight parameter. -/
theorem secondGenerator_cardExponent_smul (hqorder : orderOf q = N) (f : Fin N → ℂ) :
    letI := finiteOrderModule q α β N hqorder
    (monomial q (0, (N : ℤ))) • f = ((β : ℂ) ^ N) • f := by
  letI := finiteOrderModule q α β N hqorder
  rw [moduleOfQCommute_smul_eq_representation_apply]
  change representationOfQCommute q (cyclicShiftUnit α N) (diagonalWeightUnit q β N) _
    (monomial q (0, (N : ℤ))) f = _
  rw [representationOfQCommute_monomial]
  simp only [monomialEnd, zpow_zero, Units.val_one, one_mul, zpow_natCast,
    Units.val_pow_eq_pow_val, diagonalWeightUnit_val,
    diagonalWeightEnd_pow_card q β N hqorder]
  simp

/-- The `N`-th power of the first distinguished generator acts by the shift parameter. -/
theorem firstGenerator_pow_card_smul (hqorder : orderOf q = N) (f : Fin N → ℂ) :
    letI := finiteOrderModule q α β N hqorder
    ((monomial q (1, 0)) ^ N) • f = (α : ℂ) • f := by
  rw [monomial_firstExponent_pow, one_mul]
  exact firstGenerator_cardExponent_smul q α β N hqorder f

/-- The `N`-th power of the second distinguished generator acts by the `N`-th power of the weight parameter. -/
theorem secondGenerator_pow_card_smul (hqorder : orderOf q = N) (f : Fin N → ℂ) :
    letI := finiteOrderModule q α β N hqorder
    ((monomial q (0, 1)) ^ N) • f = ((β : ℂ) ^ N) • f := by
  rw [monomial_secondExponent_pow, one_mul]
  exact secondGenerator_cardExponent_smul q α β N hqorder f

end Family

end RepresentationTheory.QuantumTorus.FiniteOrderModules

attribute [nolint defsWithUnderscore]
  RepresentationTheory.QuantumTorus.FiniteOrderModules.unitIndexedScalar
  RepresentationTheory.QuantumTorus.FiniteOrderModules.cyclicShiftEnd
  RepresentationTheory.QuantumTorus.FiniteOrderModules.inverseCyclicShiftEnd
  RepresentationTheory.QuantumTorus.FiniteOrderModules.cyclicShiftUnit
  RepresentationTheory.QuantumTorus.FiniteOrderModules.twoUnitIndexedScalar
  RepresentationTheory.QuantumTorus.FiniteOrderModules.diagonalWeightEnd
  RepresentationTheory.QuantumTorus.FiniteOrderModules.inverseDiagonalWeightEnd
  RepresentationTheory.QuantumTorus.FiniteOrderModules.diagonalWeightUnit
  RepresentationTheory.QuantumTorus.FiniteOrderModules.finiteOrderModule
