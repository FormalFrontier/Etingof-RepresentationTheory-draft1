/-
Copyright (c) 2026 mathlib-initiative. All rights reserved.
Released under Apache 2.0 license as described in the file LICENCE.
Authors: mathlib-initiative
-/

import RepresentationTheory.Algebra.FiniteOrderShiftWeightModules
import RepresentationTheory.QuantumTorus.Representations
import RepresentationTheory.Alignment.Attribute

namespace RepresentationTheory.Algebra.FiniteOrderShiftWeightEquivalences

open Module

variable {k : Type*} [CommRing k] (q : kˣ)
variable {V : Type*} [AddCommGroup V] [Module k V]
/-- The displayed unit indexed by two integers and evaluated on conjugated endomorphism units is the conjugate of its value on the original units. -/



theorem auxiliaryIndexedUnit_conj (X Y E : (Module.End k V)ˣ) (i j : ℤ) :
    op (E * X * E⁻¹) (E * Y * E⁻¹) i j = ↑E * op X Y i j * ↑E⁻¹ := by
  have hconj : ∀ u : (Module.End k V)ˣ, E * u * E⁻¹ = MulAut.conj E u := fun _ => rfl
  have key : (E * X * E⁻¹) ^ i * (E * Y * E⁻¹) ^ j = E * (X ^ i * Y ^ j) * E⁻¹ := by
    rw [hconj X, hconj Y, ← map_zpow, ← map_zpow, ← map_mul, hconj]
  have hval := congrArg Units.val key
  simpa [op, mul_assoc] using hval
/-- If a unit intertwines each of two pairs of generators satisfying the same displayed commutation relation, then it conjugates the associated representations on every algebra element. -/




theorem representation_apply_eq_conj_of_intertwines_generators (X Y X' Y' E : (Module.End k V)ˣ)
    (hrel : (↑Y : Module.End k V) * ↑X = (q : k) • (↑X * ↑Y))
    (hrel' : (↑Y' : Module.End k V) * ↑X' = (q : k) • (↑X' * ↑Y'))
    (hX : E * X = X' * E) (hY : E * Y = Y' * E) (a : qWeylAlgebra k q) :
    toEnd q X' Y' hrel' a = ↑E * toEnd q X Y hrel a * ↑E⁻¹ := by
  have hX' : X' = E * X * E⁻¹ := by rw [hX, mul_inv_cancel_right]
  have hY' : Y' = E * Y * E⁻¹ := by rw [hY, mul_inv_cancel_right]
  subst hX'
  subst hY'
  have key : (toEnd q (E * X * E⁻¹) (E * Y * E⁻¹) hrel').toLinearMap
      = (LinearMap.mulRight k (↑E⁻¹ : Module.End k V)).comp
          ((LinearMap.mulLeft k (↑E : Module.End k V)).comp
            (toEnd q X Y hrel).toLinearMap) := by
    refine (basis q).ext fun p => ?_
    simp only [basis_apply, AlgHom.toLinearMap_apply, LinearMap.coe_comp, Function.comp_apply,
      LinearMap.mulRight_apply, LinearMap.mulLeft_apply, toEnd_qWeylMono]
    exact auxiliaryIndexedUnit_conj X Y E p.1 p.2
  exact DFunLike.congr_fun key a

end RepresentationTheory.Algebra.FiniteOrderShiftWeightEquivalences



namespace RepresentationTheory.Algebra.FiniteOrderShiftWeightEquivalences

open Module



section QPow

variable (q : ℂˣ) (N : ℕ) [NeZero N]
/-- For finite indices modulo the order of a complex unit, the power at their difference times the power at the second index equals the power at the first index. -/



theorem pow_sub_val_mul_pow_val (hqorder : orderOf q = N) (k s : Fin N) :
    (q : ℂ) ^ ((k - s : Fin N) : ℕ) * (q : ℂ) ^ ((s : Fin N) : ℕ)
      = (q : ℂ) ^ ((k : Fin N) : ℕ) := by
  have hmod : ((k - s : Fin N) : ℕ) + ((s : Fin N) : ℕ) ≡ ((k : Fin N) : ℕ) [MOD N] := by
    have h : ((k - s) + s : Fin N) = k := sub_add_cancel k s
    calc ((k - s : Fin N) : ℕ) + ((s : Fin N) : ℕ)
        ≡ (((k - s : Fin N) : ℕ) + ((s : Fin N) : ℕ)) % N [MOD N] := (Nat.mod_modEq _ _).symm
      _ = (((k - s) + s : Fin N) : ℕ) := (Fin.val_add _ _).symm
      _ = ((k : Fin N) : ℕ) := by rw [h]
  have huq : q ^ (((k - s : Fin N) : ℕ) + ((s : Fin N) : ℕ)) = q ^ ((k : Fin N) : ℕ) := by
    rw [pow_eq_pow_iff_modEq, hqorder]; exact hmod
  have hval := congrArg Units.val huq
  push_cast at hval
  simpa [pow_add] using hval
/-- When a complex unit has order `N`, exponentiation by the finite residue of a natural number agrees with exponentiation by that natural number. -/


theorem pow_fin_nsmul_one_val (hqorder : orderOf q = N) (m : ℕ) :
    (q : ℂ) ^ (((m • (1 : Fin N) : Fin N) : Fin N) : ℕ) = (q : ℂ) ^ m := by
  rw [nsmul_one_val_eq_mod]
  have huq : q ^ (m % N) = q ^ m := by
    rw [pow_eq_pow_iff_modEq, hqorder]; exact Nat.mod_modEq m N
  have hval := congrArg Units.val huq
  push_cast at hval
  simpa using hval

omit [NeZero N] in
/-- A complex unit whose order is `N` is a primitive `N`-th root. -/

theorem isPrimitiveRoot_of_orderOf_eq (hqorder : orderOf q = N) : IsPrimitiveRoot q N :=
  hqorder ▸ IsPrimitiveRoot.orderOf q
/-- If a complex unit has order `N`, equality of the `N`-th powers of two further units yields an exponent relating them by a power of the first unit. -/



theorem exists_orbitExponent_of_pow_eq (β β' : ℂˣ) (hqorder : orderOf q = N)
    (hβ : (β : ℂ) ^ N = (β' : ℂ) ^ N) : ∃ m : ℕ, (β : ℂ) = (β' : ℂ) * (q : ℂ) ^ m := by
  have hprim : IsPrimitiveRoot ((q : ℂ)) N :=
    IsPrimitiveRoot.coe_units_iff.mpr (isPrimitiveRoot_of_orderOf_eq q N hqorder)
  have hξ : ((β : ℂ) / (β' : ℂ)) ^ N = 1 := by
    rw [div_pow, hβ, div_self (pow_ne_zero _ β'.ne_zero)]
  obtain ⟨m, -, hm⟩ := hprim.eq_pow_of_pow_eq_one hξ
  exact ⟨m, by rw [hm, mul_div_cancel₀ _ β'.ne_zero]⟩

end QPow



section Intertwine

variable (q α β β' : ℂˣ) (N : ℕ) [NeZero N]
/-- Shifting the index of a diagonal weight coefficient matches changing the weight parameter by the corresponding first-unit-parameter power. -/



theorem diagonalWeightCoeff_sub_nsmul_eq (hqorder : orderOf q = N) (m : ℕ) (hβ : (β : ℂ) = (β' : ℂ) * (q : ℂ) ^ m)
    (k : Fin N) : twoUnitIndexedScalar q β N (k - m • (1 : Fin N)) = twoUnitIndexedScalar q β' N k := by
  have h := pow_sub_val_mul_pow_val q N hqorder k (m • (1 : Fin N))
  unfold twoUnitIndexedScalar
  rw [hβ, ← pow_fin_nsmul_one_val q N hqorder m]
  calc ((β' : ℂ) * (q : ℂ) ^ (((m • (1 : Fin N) : Fin N) : Fin N) : ℕ))
        * (q : ℂ) ^ ((k - m • (1 : Fin N) : Fin N) : ℕ)
      = (β' : ℂ) * ((q : ℂ) ^ ((k - m • (1 : Fin N) : Fin N) : ℕ)
          * (q : ℂ) ^ (((m • (1 : Fin N) : Fin N) : Fin N) : ℕ)) := by ring
    _ = (β' : ℂ) * (q : ℂ) ^ ((k : Fin N) : ℕ) := by rw [h]
/-- A power of the cyclic shift intertwines diagonal weight endomorphisms whose weight parameters differ by the corresponding power of the first unit parameter. -/



theorem cyclicShiftEnd_pow_mul_diagonalWeightEnd (hqorder : orderOf q = N) (m : ℕ)
    (hβ : (β : ℂ) = (β' : ℂ) * (q : ℂ) ^ m) :
    (cyclicShiftEnd α N ^ m) * (diagonalWeightEnd q β N) = (diagonalWeightEnd q β' N) * (cyclicShiftEnd α N ^ m) := by
  refine LinearMap.ext fun f => ?_
  funext k
  simp only [Module.End.mul_apply, diagonalWeightEnd, LinearMap.coe_mk, AddHom.coe_mk, smul_eq_mul]
  rw [cyclicShiftEnd_pow_apply, cyclicShiftEnd_pow_apply, ← diagonalWeightCoeff_sub_nsmul_eq q β β' N hqorder m hβ k]
  simp only [smul_eq_mul]
  ring
/-- A power of the cyclic shift unit intertwines diagonal weight units whose weight parameters differ by the corresponding power of the first unit parameter. -/


theorem cyclicShiftUnit_pow_mul_diagonalWeightUnit (hqorder : orderOf q = N) (m : ℕ)
    (hβ : (β : ℂ) = (β' : ℂ) * (q : ℂ) ^ m) :
    (cyclicShiftUnit α N ^ m) * (diagonalWeightUnit q β N) = (diagonalWeightUnit q β' N) * (cyclicShiftUnit α N ^ m) := by
  refine Units.ext ?_
  simp only [Units.val_mul, Units.val_pow_eq_pow_val, cyclicShiftUnit_val, diagonalWeightUnit_val]
  exact cyclicShiftEnd_pow_mul_diagonalWeightEnd q α β β' N hqorder m hβ
/-- Every power of the cyclic shift unit commutes with the cyclic shift unit. -/


theorem cyclicShiftUnit_pow_mul_cyclicShiftUnit (m : ℕ) :
    (cyclicShiftUnit α N ^ m) * (cyclicShiftUnit α N) = (cyclicShiftUnit α N) * (cyclicShiftUnit α N ^ m) :=
  (Commute.refl (cyclicShiftUnit α N)).pow_left m

end Intertwine



section Carrier

variable (q α β : ℂˣ)
/-- An auxiliary type parameterized by three complex units. -/






def ThreeUnitParameterType (_q _α _β : ℂˣ) : Type := Fin (orderOf _q) → ℂ
/-- The additive commutative group structure on the three-unit-parameter type. -/

instance threeUnitParameterAddCommGroup : AddCommGroup (ThreeUnitParameterType q α β) := inferInstanceAs (AddCommGroup (Fin (orderOf q) → ℂ))
/-- The complex module structure on the three-unit-parameter type. -/

instance threeUnitParameterComplexModule : Module ℂ (ThreeUnitParameterType q α β) := inferInstanceAs (Module ℂ (Fin (orderOf q) → ℂ))

variable [NeZero (orderOf q)]
/-- The three-unit-parameter type is nontrivial when the order of its first unit parameter is nonzero. -/


instance threeUnitParameter_nontrivial : Nontrivial (ThreeUnitParameterType q α β) := inferInstanceAs (Nontrivial (Fin (orderOf q) → ℂ))
/-- The displayed algebra module structure on the type parameterized by three complex units. -/


noncomputable instance threeUnitParameterModule : Module (qWeylAlgebra ℂ q) (ThreeUnitParameterType q α β) :=
  finiteOrderModule q α β (orderOf q) rfl


/-- The complex scalar action and displayed algebra action on the three-unit-parameter type form a scalar tower. -/
instance threeUnitParameterIsScalarTower : IsScalarTower ℂ (qWeylAlgebra ℂ q) (ThreeUnitParameterType q α β) :=
  finiteOrderModule_isScalarTower q α β (orderOf q) rfl
/-- The displayed algebra action agrees with evaluation of the representation determined by the corresponding cyclic shift and diagonal weight units. -/


theorem threeUnitParameter_smul_eq_representation_apply (a : qWeylAlgebra ℂ q) (f : ThreeUnitParameterType q α β) :
    a • f = RepresentationTheory.QuantumTorus.Representations.representationOfQCommute q (cyclicShiftUnit α (orderOf q)) (diagonalWeightUnit q β (orderOf q))
      (diagonalWeightUnit_val_mul_cyclicShiftUnit_val q α β (orderOf q) rfl) a f := rfl

omit [NeZero (orderOf q)] in
/-- The complex finrank of the three-unit-parameter type equals the order of its first unit parameter. -/


theorem finrank_threeUnitParameterType : Module.finrank ℂ (ThreeUnitParameterType q α β) = orderOf q :=
  finrank_finFunction (orderOf q)
/-- The first distinguished generator acts on the three-unit-parameter type by the cyclic shift endomorphism. -/


theorem firstGenerator_smul_threeUnitParameterType (f : ThreeUnitParameterType q α β) :
    (RepresentationTheory.QuantumTorus.Representations.monomial q (1, 0)) • f = cyclicShiftEnd α (orderOf q) f :=
  firstGenerator_smul q α β (orderOf q) rfl f
/-- The second distinguished generator acts on the three-unit-parameter type by the diagonal weight endomorphism. -/


theorem secondGenerator_smul_threeUnitParameterType (f : ThreeUnitParameterType q α β) :
    (RepresentationTheory.QuantumTorus.Representations.monomial q (0, 1)) • f = diagonalWeightEnd q β (orderOf q) f :=
  secondGenerator_smul q α β (orderOf q) rfl f
/-- The distinguished element with first exponent equal to the first unit parameter order acts by the shift parameter. -/


theorem firstGenerator_orderExponent_smul_threeUnitParameterType (f : ThreeUnitParameterType q α β) :
    (RepresentationTheory.QuantumTorus.Representations.monomial q ((orderOf q : ℤ), 0)) • f = (α : ℂ) • f :=
  firstGenerator_cardExponent_smul q α β (orderOf q) rfl f
/-- The distinguished element with second exponent equal to the first unit parameter order acts by the corresponding power of the weight parameter. -/


theorem secondGenerator_orderExponent_smul_threeUnitParameterType (f : ThreeUnitParameterType q α β) :
    (RepresentationTheory.QuantumTorus.Representations.monomial q (0, (orderOf q : ℤ))) • f = ((β : ℂ) ^ orderOf q) • f :=
  secondGenerator_cardExponent_smul q α β (orderOf q) rfl f

end Carrier



section Equiv

variable (q α β β' : ℂˣ) [NeZero (orderOf q)]
/-- An auxiliary unit of the complex endomorphism algebra of the finite function space, parameterized by a natural exponent. -/


noncomputable def auxiliaryEndomorphismUnit (m : ℕ) : (Module.End ℂ (Fin (orderOf q) → ℂ))ˣ :=
  cyclicShiftUnit α (orderOf q) ^ m
/-- Applying the inverse of the auxiliary endomorphism unit after the unit leaves every vector unchanged. -/


theorem auxiliaryEndomorphismUnit_inv_apply_apply (m : ℕ) (g : Fin (orderOf q) → ℂ) :
    (((auxiliaryEndomorphismUnit q α m)⁻¹ : (Module.End ℂ (Fin (orderOf q) → ℂ))ˣ) :
        Module.End ℂ (Fin (orderOf q) → ℂ))
      (((auxiliaryEndomorphismUnit q α m : (Module.End ℂ (Fin (orderOf q) → ℂ))ˣ) :
        Module.End ℂ (Fin (orderOf q) → ℂ)) g) = g := by
  rw [← Module.End.mul_apply, ← Units.val_mul, inv_mul_cancel, Units.val_one]
  rfl
/-- Applying the auxiliary endomorphism unit after its inverse leaves every vector unchanged. -/


theorem auxiliaryEndomorphismUnit_apply_inv_apply (m : ℕ) (g : Fin (orderOf q) → ℂ) :
    ((auxiliaryEndomorphismUnit q α m : (Module.End ℂ (Fin (orderOf q) → ℂ))ˣ) :
        Module.End ℂ (Fin (orderOf q) → ℂ))
      ((((auxiliaryEndomorphismUnit q α m)⁻¹ : (Module.End ℂ (Fin (orderOf q) → ℂ))ˣ) :
        Module.End ℂ (Fin (orderOf q) → ℂ)) g) = g := by
  rw [← Module.End.mul_apply, ← Units.val_mul, mul_inv_cancel, Units.val_one]
  rfl
/-- A power relation between two third unit parameters gives a module-linear equivalence between the corresponding instances with the same first and second parameters. -/



noncomputable def moduleLinearEquivOfUnitPowerRelation (m : ℕ) (hβ : (β : ℂ) = (β' : ℂ) * (q : ℂ) ^ m) :
    ThreeUnitParameterType q α β ≃ₗ[qWeylAlgebra ℂ q] ThreeUnitParameterType q α β' where
  toFun f := ((auxiliaryEndomorphismUnit q α m : (Module.End ℂ (Fin (orderOf q) → ℂ))ˣ) :
    Module.End ℂ (Fin (orderOf q) → ℂ)) f
  invFun f := (((auxiliaryEndomorphismUnit q α m)⁻¹ : (Module.End ℂ (Fin (orderOf q) → ℂ))ˣ) :
    Module.End ℂ (Fin (orderOf q) → ℂ)) f
  map_add' f g := map_add _ f g
  map_smul' a f := by
    have hconj := RepresentationTheory.Algebra.FiniteOrderShiftWeightEquivalences.representation_apply_eq_conj_of_intertwines_generators q (cyclicShiftUnit α (orderOf q)) (diagonalWeightUnit q β (orderOf q))
      (cyclicShiftUnit α (orderOf q)) (diagonalWeightUnit q β' (orderOf q)) (auxiliaryEndomorphismUnit q α m)
      (diagonalWeightUnit_val_mul_cyclicShiftUnit_val q α β (orderOf q) rfl) (diagonalWeightUnit_val_mul_cyclicShiftUnit_val q α β' (orderOf q) rfl)
      (cyclicShiftUnit_pow_mul_cyclicShiftUnit α (orderOf q) m)
      (cyclicShiftUnit_pow_mul_diagonalWeightUnit q α β β' (orderOf q) rfl m hβ) a
    change ((auxiliaryEndomorphismUnit q α m : (Module.End ℂ (Fin (orderOf q) → ℂ))ˣ) :
        Module.End ℂ (Fin (orderOf q) → ℂ))
        (RepresentationTheory.QuantumTorus.Representations.representationOfQCommute q (cyclicShiftUnit α (orderOf q)) (diagonalWeightUnit q β (orderOf q))
          (diagonalWeightUnit_val_mul_cyclicShiftUnit_val q α β (orderOf q) rfl) a f)
      = RepresentationTheory.QuantumTorus.Representations.representationOfQCommute q (cyclicShiftUnit α (orderOf q)) (diagonalWeightUnit q β' (orderOf q))
          (diagonalWeightUnit_val_mul_cyclicShiftUnit_val q α β' (orderOf q) rfl) a
          (((auxiliaryEndomorphismUnit q α m : (Module.End ℂ (Fin (orderOf q) → ℂ))ˣ) :
            Module.End ℂ (Fin (orderOf q) → ℂ)) f)
    rw [hconj]
    simp only [Module.End.mul_apply, auxiliaryEndomorphismUnit_inv_apply_apply]
  left_inv f := auxiliaryEndomorphismUnit_inv_apply_apply q α m f
  right_inv f := auxiliaryEndomorphismUnit_apply_inv_apply q α m f

end Equiv



section Classification

variable (q α β α' β' : ℂˣ) [NeZero (orderOf q)]
/-- A module-linear equivalence between two instances forces equality of their second unit parameters and equality of the order-th powers of their third unit parameters. -/



theorem parameters_eq_of_moduleLinearEquiv (e : ThreeUnitParameterType q α β ≃ₗ[qWeylAlgebra ℂ q] ThreeUnitParameterType q α' β') :
    α = α' ∧ (β : ℂ) ^ orderOf q = (β' : ℂ) ^ orderOf q := by
  obtain ⟨v, hv⟩ := exists_ne (0 : ThreeUnitParameterType q α β)
  have hev : e v ≠ 0 := fun h => hv (e.map_eq_zero_iff.mp h)
  constructor
  · have h1 : e ((RepresentationTheory.QuantumTorus.Representations.monomial q ((orderOf q : ℤ), 0)) • v)
        = (RepresentationTheory.QuantumTorus.Representations.monomial q ((orderOf q : ℤ), 0)) • e v := e.map_smul _ _
    rw [firstGenerator_orderExponent_smul_threeUnitParameterType, firstGenerator_orderExponent_smul_threeUnitParameterType, LinearMapClass.map_smul_of_tower e] at h1
    have h2 : ((α : ℂ) - (α' : ℂ)) • e v = 0 := by rw [sub_smul, h1, sub_self]
    rcases smul_eq_zero.mp h2 with h | h
    · exact Units.ext (sub_eq_zero.mp h)
    · exact absurd h hev
  · have h1 : e ((RepresentationTheory.QuantumTorus.Representations.monomial q (0, (orderOf q : ℤ))) • v)
        = (RepresentationTheory.QuantumTorus.Representations.monomial q (0, (orderOf q : ℤ))) • e v := e.map_smul _ _
    rw [secondGenerator_orderExponent_smul_threeUnitParameterType, secondGenerator_orderExponent_smul_threeUnitParameterType, LinearMapClass.map_smul_of_tower e] at h1
    have h2 : ((β : ℂ) ^ orderOf q - (β' : ℂ) ^ orderOf q) • e v = 0 := by
      rw [sub_smul, h1, sub_self]
    rcases smul_eq_zero.mp h2 with h | h
    · exact sub_eq_zero.mp h
    · exact absurd h hev
/-- Two instances are module-linearly equivalent exactly when their second unit parameters agree and the order-th powers of their third unit parameters agree. -/
@[source_ref "Chapter2/Problem2.7.5" (role := supporting)]





theorem nonempty_moduleLinearEquiv_iff :
    Nonempty (ThreeUnitParameterType q α β ≃ₗ[qWeylAlgebra ℂ q] ThreeUnitParameterType q α' β')
      ↔ α = α' ∧ (β : ℂ) ^ orderOf q = (β' : ℂ) ^ orderOf q := by
  constructor
  · rintro ⟨e⟩
    exact parameters_eq_of_moduleLinearEquiv q α β α' β' e
  · rintro ⟨rfl, hβ⟩
    obtain ⟨m, hm⟩ := exists_orbitExponent_of_pow_eq q (orderOf q) β β' rfl hβ
    exact ⟨moduleLinearEquivOfUnitPowerRelation q α β β' m hm⟩

end Classification

end RepresentationTheory.Algebra.FiniteOrderShiftWeightEquivalences



attribute [nolint defsWithUnderscore]
  RepresentationTheory.Algebra.FiniteOrderShiftWeightEquivalences.threeUnitParameterAddCommGroup
  RepresentationTheory.Algebra.FiniteOrderShiftWeightEquivalences.threeUnitParameterComplexModule RepresentationTheory.Algebra.FiniteOrderShiftWeightEquivalences.threeUnitParameterModule
  RepresentationTheory.Algebra.FiniteOrderShiftWeightEquivalences.auxiliaryEndomorphismUnit RepresentationTheory.Algebra.FiniteOrderShiftWeightEquivalences.moduleLinearEquivOfUnitPowerRelation



attribute [nolint defsWithUnderscore unusedArguments] RepresentationTheory.Algebra.FiniteOrderShiftWeightEquivalences.ThreeUnitParameterType
