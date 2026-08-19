/-
Copyright (c) 2026 mathlib-initiative. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: mathlib-initiative
-/

import RepresentationTheory.Algebra.IntegerIndexedPolynomialOperators
import Mathlib.RingTheory.SimpleModule.Basic
import Mathlib.LinearAlgebra.Eigenspace.Triangularizable
import Mathlib.Data.Nat.Prime.Factorial
import Mathlib.LinearAlgebra.Trace
import RepresentationTheory.Alignment.Attribute

/-!
# Polynomial operators in positive characteristic
-/



namespace RepresentationTheory.NoncommutativeAlgebra.PositiveCharacteristic

open RepresentationTheory




private lemma y_mul_x_pow_succ (k : Type*) [Field k] (n : ℕ) :
    RepresentationTheory.FreeAlgebra.PolynomialOperators.OperatorAlgebra.secondOperator k * RepresentationTheory.FreeAlgebra.PolynomialOperators.OperatorAlgebra.firstOperator k ^ (n + 1)
      = RepresentationTheory.FreeAlgebra.PolynomialOperators.OperatorAlgebra.firstOperator k ^ (n + 1) * RepresentationTheory.FreeAlgebra.PolynomialOperators.OperatorAlgebra.secondOperator k + (n + 1) • RepresentationTheory.FreeAlgebra.PolynomialOperators.OperatorAlgebra.firstOperator k ^ n := by
  induction n with
  | zero => simp only [zero_add, pow_one, pow_zero, one_smul]; exact RepresentationTheory.FreeAlgebra.PolynomialOperators.OperatorAlgebra.secondOperator_mul_firstOperator k
  | succ n ih =>
    calc RepresentationTheory.FreeAlgebra.PolynomialOperators.OperatorAlgebra.secondOperator k * RepresentationTheory.FreeAlgebra.PolynomialOperators.OperatorAlgebra.firstOperator k ^ (n + 1 + 1)
        = RepresentationTheory.FreeAlgebra.PolynomialOperators.OperatorAlgebra.secondOperator k * RepresentationTheory.FreeAlgebra.PolynomialOperators.OperatorAlgebra.firstOperator k ^ (n + 1) * RepresentationTheory.FreeAlgebra.PolynomialOperators.OperatorAlgebra.firstOperator k := by
          rw [pow_succ, mul_assoc]
      _ = (RepresentationTheory.FreeAlgebra.PolynomialOperators.OperatorAlgebra.firstOperator k ^ (n + 1) * RepresentationTheory.FreeAlgebra.PolynomialOperators.OperatorAlgebra.secondOperator k + (n + 1) • RepresentationTheory.FreeAlgebra.PolynomialOperators.OperatorAlgebra.firstOperator k ^ n)
            * RepresentationTheory.FreeAlgebra.PolynomialOperators.OperatorAlgebra.firstOperator k := by rw [ih]
      _ = RepresentationTheory.FreeAlgebra.PolynomialOperators.OperatorAlgebra.firstOperator k ^ (n + 1) * (RepresentationTheory.FreeAlgebra.PolynomialOperators.OperatorAlgebra.secondOperator k * RepresentationTheory.FreeAlgebra.PolynomialOperators.OperatorAlgebra.firstOperator k)
            + (n + 1) • RepresentationTheory.FreeAlgebra.PolynomialOperators.OperatorAlgebra.firstOperator k ^ (n + 1) := by
          rw [add_mul, mul_assoc, smul_mul_assoc, ← pow_succ]
      _ = RepresentationTheory.FreeAlgebra.PolynomialOperators.OperatorAlgebra.firstOperator k ^ (n + 1) * (RepresentationTheory.FreeAlgebra.PolynomialOperators.OperatorAlgebra.firstOperator k * RepresentationTheory.FreeAlgebra.PolynomialOperators.OperatorAlgebra.secondOperator k + 1)
            + (n + 1) • RepresentationTheory.FreeAlgebra.PolynomialOperators.OperatorAlgebra.firstOperator k ^ (n + 1) := by rw [RepresentationTheory.FreeAlgebra.PolynomialOperators.OperatorAlgebra.secondOperator_mul_firstOperator]
      _ = RepresentationTheory.FreeAlgebra.PolynomialOperators.OperatorAlgebra.firstOperator k ^ (n + 1 + 1) * RepresentationTheory.FreeAlgebra.PolynomialOperators.OperatorAlgebra.secondOperator k
            + (n + 1 + 1) • RepresentationTheory.FreeAlgebra.PolynomialOperators.OperatorAlgebra.firstOperator k ^ (n + 1) := by
          rw [mul_add, mul_one, ← mul_assoc, ← pow_succ, add_assoc,
            add_comm (RepresentationTheory.FreeAlgebra.PolynomialOperators.OperatorAlgebra.firstOperator k ^ (n + 1)) ((n + 1) • RepresentationTheory.FreeAlgebra.PolynomialOperators.OperatorAlgebra.firstOperator k ^ (n + 1)),
            ← succ_nsmul]


private lemma x_mul_y_pow_succ (k : Type*) [Field k] (n : ℕ) :
    RepresentationTheory.FreeAlgebra.PolynomialOperators.OperatorAlgebra.firstOperator k * RepresentationTheory.FreeAlgebra.PolynomialOperators.OperatorAlgebra.secondOperator k ^ (n + 1)
      = RepresentationTheory.FreeAlgebra.PolynomialOperators.OperatorAlgebra.secondOperator k ^ (n + 1) * RepresentationTheory.FreeAlgebra.PolynomialOperators.OperatorAlgebra.firstOperator k - (n + 1) • RepresentationTheory.FreeAlgebra.PolynomialOperators.OperatorAlgebra.secondOperator k ^ n := by
  have hxy : RepresentationTheory.FreeAlgebra.PolynomialOperators.OperatorAlgebra.firstOperator k * RepresentationTheory.FreeAlgebra.PolynomialOperators.OperatorAlgebra.secondOperator k = RepresentationTheory.FreeAlgebra.PolynomialOperators.OperatorAlgebra.secondOperator k * RepresentationTheory.FreeAlgebra.PolynomialOperators.OperatorAlgebra.firstOperator k - 1 := by
    rw [eq_sub_iff_add_eq]; exact (RepresentationTheory.FreeAlgebra.PolynomialOperators.OperatorAlgebra.secondOperator_mul_firstOperator k).symm
  induction n with
  | zero => simp only [zero_add, pow_one, pow_zero, one_smul]; exact hxy
  | succ n ih =>
    calc RepresentationTheory.FreeAlgebra.PolynomialOperators.OperatorAlgebra.firstOperator k * RepresentationTheory.FreeAlgebra.PolynomialOperators.OperatorAlgebra.secondOperator k ^ (n + 1 + 1)
        = RepresentationTheory.FreeAlgebra.PolynomialOperators.OperatorAlgebra.firstOperator k * RepresentationTheory.FreeAlgebra.PolynomialOperators.OperatorAlgebra.secondOperator k ^ (n + 1) * RepresentationTheory.FreeAlgebra.PolynomialOperators.OperatorAlgebra.secondOperator k := by
          rw [pow_succ, mul_assoc]
      _ = (RepresentationTheory.FreeAlgebra.PolynomialOperators.OperatorAlgebra.secondOperator k ^ (n + 1) * RepresentationTheory.FreeAlgebra.PolynomialOperators.OperatorAlgebra.firstOperator k - (n + 1) • RepresentationTheory.FreeAlgebra.PolynomialOperators.OperatorAlgebra.secondOperator k ^ n)
            * RepresentationTheory.FreeAlgebra.PolynomialOperators.OperatorAlgebra.secondOperator k := by rw [ih]
      _ = RepresentationTheory.FreeAlgebra.PolynomialOperators.OperatorAlgebra.secondOperator k ^ (n + 1) * (RepresentationTheory.FreeAlgebra.PolynomialOperators.OperatorAlgebra.firstOperator k * RepresentationTheory.FreeAlgebra.PolynomialOperators.OperatorAlgebra.secondOperator k)
            - (n + 1) • RepresentationTheory.FreeAlgebra.PolynomialOperators.OperatorAlgebra.secondOperator k ^ (n + 1) := by
          rw [sub_mul, mul_assoc, smul_mul_assoc, ← pow_succ]
      _ = RepresentationTheory.FreeAlgebra.PolynomialOperators.OperatorAlgebra.secondOperator k ^ (n + 1) * (RepresentationTheory.FreeAlgebra.PolynomialOperators.OperatorAlgebra.secondOperator k * RepresentationTheory.FreeAlgebra.PolynomialOperators.OperatorAlgebra.firstOperator k - 1)
            - (n + 1) • RepresentationTheory.FreeAlgebra.PolynomialOperators.OperatorAlgebra.secondOperator k ^ (n + 1) := by rw [hxy]
      _ = RepresentationTheory.FreeAlgebra.PolynomialOperators.OperatorAlgebra.secondOperator k ^ (n + 1 + 1) * RepresentationTheory.FreeAlgebra.PolynomialOperators.OperatorAlgebra.firstOperator k
            - (n + 1 + 1) • RepresentationTheory.FreeAlgebra.PolynomialOperators.OperatorAlgebra.secondOperator k ^ (n + 1) := by
          rw [mul_sub, mul_one, ← mul_assoc, ← pow_succ, sub_sub,
            add_comm (RepresentationTheory.FreeAlgebra.PolynomialOperators.OperatorAlgebra.secondOperator k ^ (n + 1)) ((n + 1) • RepresentationTheory.FreeAlgebra.PolynomialOperators.OperatorAlgebra.secondOperator k ^ (n + 1)),
            ← succ_nsmul]


private theorem mem_center_of_comm_gen (k : Type*) [Field k] {z : RepresentationTheory.FreeAlgebra.PolynomialOperators.OperatorAlgebra k}
    (hx : z * RepresentationTheory.FreeAlgebra.PolynomialOperators.OperatorAlgebra.firstOperator k = RepresentationTheory.FreeAlgebra.PolynomialOperators.OperatorAlgebra.firstOperator k * z)
    (hy : z * RepresentationTheory.FreeAlgebra.PolynomialOperators.OperatorAlgebra.secondOperator k = RepresentationTheory.FreeAlgebra.PolynomialOperators.OperatorAlgebra.secondOperator k * z) :
    z ∈ Subalgebra.center k (RepresentationTheory.FreeAlgebra.PolynomialOperators.OperatorAlgebra k) := by
  rw [Subalgebra.mem_center_iff]
  intro b
  obtain ⟨a, rfl⟩ := RingQuot.mkAlgHom_surjective k (RepresentationTheory.FreeAlgebra.PolynomialOperators.freeAlgebraRelation k) b
  have ha : a ∈ Algebra.adjoin k (Set.range (FreeAlgebra.ι k)) := by
    rw [FreeAlgebra.adjoin_range_ι]; exact Algebra.mem_top
  induction ha using Algebra.adjoin_induction with
  | mem g hg =>
    obtain ⟨i, rfl⟩ := hg
    fin_cases i
    · exact hx.symm
    · exact hy.symm
  | algebraMap r => rw [AlgHom.commutes]; exact Algebra.commutes r z
  | add p q _ _ ihp ihq => rw [map_add, add_mul, mul_add, ihp, ihq]
  | mul p q _ _ ihp ihq => rw [map_mul, mul_assoc, ihq, ← mul_assoc, ihp, mul_assoc]




/-- Every finite-dimensional module of the displayed algebra has zero base-field dimension in characteristic zero. -/
@[source_ref "Chapter2/Problem2.7.4" (role := primary)]
theorem finrank_eq_zero_of_charZero (k : Type*) [Field k] [CharZero k]
    (V : Type*) [AddCommGroup V] [Module k V] [Module (RepresentationTheory.FreeAlgebra.PolynomialOperators.OperatorAlgebra k) V]
    [IsScalarTower k (RepresentationTheory.FreeAlgebra.PolynomialOperators.OperatorAlgebra k) V] [FiniteDimensional k V] :
    Module.finrank k V = 0 := by


  haveI : SMulCommClass (RepresentationTheory.FreeAlgebra.PolynomialOperators.OperatorAlgebra k) k V :=
    ⟨fun a c v => by
      simp only [← algebraMap_smul (RepresentationTheory.FreeAlgebra.PolynomialOperators.OperatorAlgebra k) c, ← mul_smul, Algebra.commutes]⟩
  let φ : RepresentationTheory.FreeAlgebra.PolynomialOperators.OperatorAlgebra k →ₐ[k] Module.End k V := Algebra.lsmul k k V
  set X := φ (RepresentationTheory.FreeAlgebra.PolynomialOperators.OperatorAlgebra.firstOperator k) with hX
  set Y := φ (RepresentationTheory.FreeAlgebra.PolynomialOperators.OperatorAlgebra.secondOperator k) with hY
  have hcomm : Y * X = X * Y + 1 := by
    rw [hX, hY, ← map_mul, ← map_mul, ← map_one φ, ← map_add, RepresentationTheory.FreeAlgebra.PolynomialOperators.OperatorAlgebra.secondOperator_mul_firstOperator]

  have htr : LinearMap.trace k V (Y * X) = LinearMap.trace k V (X * Y) :=
    LinearMap.trace_mul_comm k Y X
  rw [hcomm, map_add, LinearMap.trace_one] at htr
  have hfin : (Module.finrank k V : k) = 0 := by linear_combination htr
  exact_mod_cast hfin



section AdDerivations

variable (k : Type*) [Field k]

open RepresentationTheory.FreeAlgebra.PolynomialOperators.OperatorAlgebra


private noncomputable def adx : RepresentationTheory.FreeAlgebra.PolynomialOperators.OperatorAlgebra k →ₗ[k] RepresentationTheory.FreeAlgebra.PolynomialOperators.OperatorAlgebra k :=
  LinearMap.mulLeft k (RepresentationTheory.FreeAlgebra.PolynomialOperators.OperatorAlgebra.firstOperator k) - LinearMap.mulRight k (RepresentationTheory.FreeAlgebra.PolynomialOperators.OperatorAlgebra.firstOperator k)


private noncomputable def ady : RepresentationTheory.FreeAlgebra.PolynomialOperators.OperatorAlgebra k →ₗ[k] RepresentationTheory.FreeAlgebra.PolynomialOperators.OperatorAlgebra k :=
  LinearMap.mulLeft k (RepresentationTheory.FreeAlgebra.PolynomialOperators.OperatorAlgebra.secondOperator k) - LinearMap.mulRight k (RepresentationTheory.FreeAlgebra.PolynomialOperators.OperatorAlgebra.secondOperator k)

private lemma adx_apply (a : RepresentationTheory.FreeAlgebra.PolynomialOperators.OperatorAlgebra k) :
    adx k a = RepresentationTheory.FreeAlgebra.PolynomialOperators.OperatorAlgebra.firstOperator k * a - a * RepresentationTheory.FreeAlgebra.PolynomialOperators.OperatorAlgebra.firstOperator k := by
  simp [adx, LinearMap.mulLeft_apply, LinearMap.mulRight_apply]

private lemma ady_apply (a : RepresentationTheory.FreeAlgebra.PolynomialOperators.OperatorAlgebra k) :
    ady k a = RepresentationTheory.FreeAlgebra.PolynomialOperators.OperatorAlgebra.secondOperator k * a - a * RepresentationTheory.FreeAlgebra.PolynomialOperators.OperatorAlgebra.secondOperator k := by
  simp [ady, LinearMap.mulLeft_apply, LinearMap.mulRight_apply]

private lemma adx_monomial_zero (i : ℕ) : adx k (RepresentationTheory.FreeAlgebra.PolynomialOperators.OperatorAlgebra.monomialOperator k i 0) = 0 := by
  rw [adx_apply, RepresentationTheory.FreeAlgebra.PolynomialOperators.OperatorAlgebra.monomialOperator, pow_zero, mul_one, ← pow_succ, ← pow_succ', sub_self]

private lemma adx_monomial_succ (i n : ℕ) :
    adx k (RepresentationTheory.FreeAlgebra.PolynomialOperators.OperatorAlgebra.monomialOperator k i (n + 1))
      = (-((n : k) + 1)) • RepresentationTheory.FreeAlgebra.PolynomialOperators.OperatorAlgebra.monomialOperator k i n := by
  have hYX : RepresentationTheory.FreeAlgebra.PolynomialOperators.OperatorAlgebra.secondOperator k ^ (n + 1) * RepresentationTheory.FreeAlgebra.PolynomialOperators.OperatorAlgebra.firstOperator k
      = RepresentationTheory.FreeAlgebra.PolynomialOperators.OperatorAlgebra.firstOperator k * RepresentationTheory.FreeAlgebra.PolynomialOperators.OperatorAlgebra.secondOperator k ^ (n + 1)
        + (n + 1) • RepresentationTheory.FreeAlgebra.PolynomialOperators.OperatorAlgebra.secondOperator k ^ n := by
    have h := x_mul_y_pow_succ k n; rw [h]; abel
  simp only [adx_apply, RepresentationTheory.FreeAlgebra.PolynomialOperators.OperatorAlgebra.monomialOperator]
  rw [← mul_assoc, ← pow_succ', mul_assoc (RepresentationTheory.FreeAlgebra.PolynomialOperators.OperatorAlgebra.firstOperator k ^ i), hYX, mul_add,
    ← mul_assoc, ← pow_succ, mul_smul_comm, sub_add_eq_sub_sub, sub_self, zero_sub,
    ← Nat.cast_smul_eq_nsmul (R := k) (n + 1)]
  push_cast
  module

private lemma ady_monomial_zero (j : ℕ) : ady k (RepresentationTheory.FreeAlgebra.PolynomialOperators.OperatorAlgebra.monomialOperator k 0 j) = 0 := by
  rw [ady_apply, RepresentationTheory.FreeAlgebra.PolynomialOperators.OperatorAlgebra.monomialOperator, pow_zero, one_mul, ← pow_succ, ← pow_succ', sub_self]

private lemma ady_monomial_succ (n j : ℕ) :
    ady k (RepresentationTheory.FreeAlgebra.PolynomialOperators.OperatorAlgebra.monomialOperator k (n + 1) j)
      = ((n : k) + 1) • RepresentationTheory.FreeAlgebra.PolynomialOperators.OperatorAlgebra.monomialOperator k n j := by
  have hYX : RepresentationTheory.FreeAlgebra.PolynomialOperators.OperatorAlgebra.secondOperator k * RepresentationTheory.FreeAlgebra.PolynomialOperators.OperatorAlgebra.firstOperator k ^ (n + 1)
      = RepresentationTheory.FreeAlgebra.PolynomialOperators.OperatorAlgebra.firstOperator k ^ (n + 1) * RepresentationTheory.FreeAlgebra.PolynomialOperators.OperatorAlgebra.secondOperator k + (n + 1) • RepresentationTheory.FreeAlgebra.PolynomialOperators.OperatorAlgebra.firstOperator k ^ n :=
    y_mul_x_pow_succ k n
  simp only [ady_apply, RepresentationTheory.FreeAlgebra.PolynomialOperators.OperatorAlgebra.monomialOperator]
  rw [← mul_assoc, hYX, add_mul,
    mul_assoc (RepresentationTheory.FreeAlgebra.PolynomialOperators.OperatorAlgebra.firstOperator k ^ (n + 1)), ← pow_succ', smul_mul_assoc,
    mul_assoc (RepresentationTheory.FreeAlgebra.PolynomialOperators.OperatorAlgebra.firstOperator k ^ (n + 1)), ← pow_succ,
    add_sub_cancel_left, ← Nat.cast_smul_eq_nsmul (R := k) (n + 1)]
  congr 1
  push_cast; ring

end AdDerivations



section CharZeroSimple

variable (k : Type*) [Field k] [CharZero k]

open RepresentationTheory.FreeAlgebra.PolynomialOperators.OperatorAlgebra Module


private noncomputable def monBasis : Basis (ℕ × ℕ) k (RepresentationTheory.FreeAlgebra.PolynomialOperators.OperatorAlgebra k) :=
  Basis.mk (RepresentationTheory.FreeAlgebra.PolynomialOperators.polynomialOperators_basis k).1 (RepresentationTheory.FreeAlgebra.PolynomialOperators.polynomialOperators_basis k).2

private lemma monBasis_apply (p : ℕ × ℕ) :
    monBasis k p = RepresentationTheory.FreeAlgebra.PolynomialOperators.OperatorAlgebra.monomialOperator k p.1 p.2 :=
  Basis.mk_apply _ _ _

private lemma repr_monomial (i j : ℕ) :
    (monBasis k).repr (RepresentationTheory.FreeAlgebra.PolynomialOperators.OperatorAlgebra.monomialOperator k i j) = Finsupp.single (i, j) 1 := by
  rw [← monBasis_apply k (i, j)]; exact (monBasis k).repr_self _


private lemma repr_adx_apply (a : RepresentationTheory.FreeAlgebra.PolynomialOperators.OperatorAlgebra k) (i j : ℕ) :
    (monBasis k).repr (adx k a) (i, j)
      = -((j : k) + 1) * (monBasis k).repr a (i, j + 1) := by
  have key :
      (Finsupp.lapply (i, j)).comp (((monBasis k).repr.toLinearMap).comp (adx k))
        = (-((j : k) + 1)) •
            (Finsupp.lapply (i, j + 1)).comp ((monBasis k).repr.toLinearMap) := by
    apply (monBasis k).ext
    rintro ⟨i', j'⟩
    simp only [LinearMap.smul_apply, LinearMap.coe_comp, Function.comp_apply,
      LinearEquiv.coe_coe, Finsupp.lapply_apply, smul_eq_mul]
    rw [monBasis_apply k (i', j'), repr_monomial]
    cases j' with
    | zero =>
      rw [adx_monomial_zero, map_zero]
      simp [Prod.ext_iff]
    | succ n =>
      rw [adx_monomial_succ, map_smul, repr_monomial, Finsupp.smul_apply,
        Finsupp.single_apply, Finsupp.single_apply, smul_eq_mul]
      by_cases h : (i', n) = (i, j)
      · obtain ⟨rfl, rfl⟩ := Prod.mk.injEq _ _ _ _ ▸ h
        simp
      · rw [if_neg h]
        rw [if_neg (by simp only [Prod.ext_iff] at h ⊢; omega)]
        ring
  have := LinearMap.congr_fun key a
  simpa only [LinearMap.smul_apply, LinearMap.coe_comp, Function.comp_apply,
    LinearEquiv.coe_coe, Finsupp.lapply_apply, smul_eq_mul] using this


private lemma repr_ady_apply (a : RepresentationTheory.FreeAlgebra.PolynomialOperators.OperatorAlgebra k) (i j : ℕ) :
    (monBasis k).repr (ady k a) (i, j)
      = ((i : k) + 1) * (monBasis k).repr a (i + 1, j) := by
  have key :
      (Finsupp.lapply (i, j)).comp (((monBasis k).repr.toLinearMap).comp (ady k))
        = (((i : k) + 1)) •
            (Finsupp.lapply (i + 1, j)).comp ((monBasis k).repr.toLinearMap) := by
    apply (monBasis k).ext
    rintro ⟨i', j'⟩
    simp only [LinearMap.smul_apply, LinearMap.coe_comp, Function.comp_apply,
      LinearEquiv.coe_coe, Finsupp.lapply_apply, smul_eq_mul]
    rw [monBasis_apply k (i', j'), repr_monomial]
    cases i' with
    | zero =>
      rw [ady_monomial_zero, map_zero]
      simp [Prod.ext_iff]
    | succ m =>
      rw [ady_monomial_succ, map_smul, repr_monomial, Finsupp.smul_apply,
        Finsupp.single_apply, Finsupp.single_apply, smul_eq_mul]
      by_cases h : (m, j') = (i, j)
      · obtain ⟨rfl, rfl⟩ := Prod.mk.injEq _ _ _ _ ▸ h
        simp
      · rw [if_neg h]
        rw [if_neg (by simp only [Prod.ext_iff] at h ⊢; omega)]
        ring
  have := LinearMap.congr_fun key a
  simpa only [LinearMap.smul_apply, LinearMap.coe_comp, Function.comp_apply,
    LinearEquiv.coe_coe, Finsupp.lapply_apply, smul_eq_mul] using this


private noncomputable def yDeg (a : RepresentationTheory.FreeAlgebra.PolynomialOperators.OperatorAlgebra k) : ℕ :=
  ((monBasis k).repr a).support.sup Prod.snd


private noncomputable def xDeg (a : RepresentationTheory.FreeAlgebra.PolynomialOperators.OperatorAlgebra k) : ℕ :=
  ((monBasis k).repr a).support.sup Prod.fst

private lemma repr_ne_zero_of_ne_zero {a : RepresentationTheory.FreeAlgebra.PolynomialOperators.OperatorAlgebra k} (ha : a ≠ 0) :
    (monBasis k).repr a ≠ 0 := fun h => ha (by
  have := (monBasis k).linearCombination_repr a
  rw [h, map_zero] at this; exact this.symm)

private lemma adx_ne_zero {a : RepresentationTheory.FreeAlgebra.PolynomialOperators.OperatorAlgebra k} (ha : a ≠ 0) (hy : 0 < yDeg k a) :
    adx k a ≠ 0 := by
  obtain ⟨m, hm⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.pos_iff_ne_zero.mp hy)
  have hsupne : ((monBasis k).repr a).support.Nonempty :=
    Finsupp.support_nonempty_iff.mpr (repr_ne_zero_of_ne_zero k ha)
  obtain ⟨p, hp, hpe⟩ :=
    Finset.exists_mem_eq_sup ((monBasis k).repr a).support hsupne Prod.snd
  have hp2 : p.2 = m + 1 := by rw [← hpe]; exact hm
  intro hzero
  have hval : (monBasis k).repr (adx k a) (p.1, m) = 0 := by rw [hzero, map_zero]; rfl
  rw [repr_adx_apply] at hval
  have hpa : (monBasis k).repr a (p.1, m + 1) ≠ 0 := by
    have : (p.1, p.2) ∈ ((monBasis k).repr a).support := hp
    rw [hp2] at this
    exact Finsupp.mem_support_iff.mp this
  have hcoeff : -((m : k) + 1) ≠ 0 :=
    neg_ne_zero.mpr (by exact_mod_cast Nat.succ_ne_zero m)
  exact (mul_ne_zero hcoeff hpa) hval

private lemma ady_ne_zero {a : RepresentationTheory.FreeAlgebra.PolynomialOperators.OperatorAlgebra k} (ha : a ≠ 0) (hx : 0 < xDeg k a) :
    ady k a ≠ 0 := by
  obtain ⟨m, hm⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.pos_iff_ne_zero.mp hx)
  have hsupne : ((monBasis k).repr a).support.Nonempty :=
    Finsupp.support_nonempty_iff.mpr (repr_ne_zero_of_ne_zero k ha)
  obtain ⟨p, hp, hpe⟩ :=
    Finset.exists_mem_eq_sup ((monBasis k).repr a).support hsupne Prod.fst
  have hp1 : p.1 = m + 1 := by rw [← hpe]; exact hm
  intro hzero
  have hval : (monBasis k).repr (ady k a) (m, p.2) = 0 := by rw [hzero, map_zero]; rfl
  rw [repr_ady_apply] at hval
  have hpa : (monBasis k).repr a (m + 1, p.2) ≠ 0 := by
    have : (p.1, p.2) ∈ ((monBasis k).repr a).support := hp
    rw [hp1] at this
    exact Finsupp.mem_support_iff.mp this
  have hcoeff : ((m : k) + 1) ≠ 0 := by exact_mod_cast Nat.succ_ne_zero m
  exact (mul_ne_zero hcoeff hpa) hval

private lemma yDeg_adx_lt {a : RepresentationTheory.FreeAlgebra.PolynomialOperators.OperatorAlgebra k} (hy : 0 < yDeg k a) :
    yDeg k (adx k a) < yDeg k a := by
  rw [yDeg, Finset.sup_lt_iff hy]
  intro q hq
  rw [Finsupp.mem_support_iff, repr_adx_apply] at hq
  have hr : (monBasis k).repr a (q.1, q.2 + 1) ≠ 0 := fun h => hq (by rw [h, mul_zero])
  have hle : q.2 + 1 ≤ yDeg k a :=
    Finset.le_sup (f := Prod.snd) (Finsupp.mem_support_iff.mpr hr)
  omega

private lemma xDeg_ady_lt {a : RepresentationTheory.FreeAlgebra.PolynomialOperators.OperatorAlgebra k} (hx : 0 < xDeg k a) :
    xDeg k (ady k a) < xDeg k a := by
  rw [xDeg, Finset.sup_lt_iff hx]
  intro q hq
  rw [Finsupp.mem_support_iff, repr_ady_apply] at hq
  have hr : (monBasis k).repr a (q.1 + 1, q.2) ≠ 0 := fun h => hq (by rw [h, mul_zero])
  have hle : q.1 + 1 ≤ xDeg k a :=
    Finset.le_sup (f := Prod.fst) (Finsupp.mem_support_iff.mpr hr)
  omega

private lemma yDeg_ady_eq_zero {a : RepresentationTheory.FreeAlgebra.PolynomialOperators.OperatorAlgebra k} (hy : yDeg k a = 0) :
    yDeg k (ady k a) = 0 := by
  rw [yDeg]
  refine Nat.le_zero.mp (Finset.sup_le fun q hq => ?_)
  rw [Finsupp.mem_support_iff, repr_ady_apply] at hq
  have hr : (monBasis k).repr a (q.1 + 1, q.2) ≠ 0 := fun h => hq (by rw [h, mul_zero])
  have hle : q.2 ≤ yDeg k a :=
    Finset.le_sup (f := Prod.snd) (b := (q.1 + 1, q.2)) (Finsupp.mem_support_iff.mpr hr)
  omega


private lemma one_mem_of_yDeg_zero (I : TwoSidedIdeal (RepresentationTheory.FreeAlgebra.PolynomialOperators.OperatorAlgebra k)) :
    ∀ (n : ℕ) (a : RepresentationTheory.FreeAlgebra.PolynomialOperators.OperatorAlgebra k), xDeg k a = n → yDeg k a = 0 → a ∈ I → a ≠ 0 →
      (1 : RepresentationTheory.FreeAlgebra.PolynomialOperators.OperatorAlgebra k) ∈ I := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro a hn hy haI ha
    rcases Nat.eq_zero_or_pos (xDeg k a) with h0 | hpos
    ·
      set c : k := (monBasis k).repr a ((0 : ℕ), (0 : ℕ)) with hc_def
      have hsupp : ∀ p ∈ ((monBasis k).repr a).support, p = (0, 0) := by
        rintro ⟨q1, q2⟩ hp
        have h1 : q1 ≤ xDeg k a := Finset.le_sup (f := Prod.fst) hp
        have h2 : q2 ≤ yDeg k a := Finset.le_sup (f := Prod.snd) hp
        rw [h0] at h1; rw [hy] at h2
        simp only [Prod.mk.injEq]
        exact ⟨Nat.le_zero.mp h1, Nat.le_zero.mp h2⟩
      have hc : c ≠ 0 := by
        have hne := repr_ne_zero_of_ne_zero k ha
        have hsupne := Finsupp.support_nonempty_iff.mpr hne
        obtain ⟨p, hp⟩ := hsupne
        have hp0 : p = (0, 0) := hsupp p hp
        rw [hp0] at hp
        exact Finsupp.mem_support_iff.mp hp
      have hrepr : (monBasis k).repr a = Finsupp.single (0, 0) c := by
        ext p
        rw [Finsupp.single_apply]
        by_cases hp : p = (0, 0)
        · rw [hp, if_pos rfl]
        · rw [if_neg (Ne.symm hp), Finsupp.notMem_support_iff.mp (fun h => hp (hsupp p h))]
      have hone : monBasis k (0, 0) = (1 : RepresentationTheory.FreeAlgebra.PolynomialOperators.OperatorAlgebra k) := by
        rw [monBasis_apply, RepresentationTheory.FreeAlgebra.PolynomialOperators.OperatorAlgebra.monomialOperator]; simp
      have ha1 : a = c • (1 : RepresentationTheory.FreeAlgebra.PolynomialOperators.OperatorAlgebra k) := by
        have h := (monBasis k).linearCombination_repr a
        rw [hrepr, Finsupp.linearCombination_single, hone] at h
        exact h.symm
      have hmem : c⁻¹ • a ∈ I := by
        rw [Algebra.smul_def]; exact I.mul_mem_left _ _ haI
      rwa [ha1, smul_smul, inv_mul_cancel₀ hc, one_smul] at hmem
    ·
      have hlt : xDeg k (ady k a) < n := hn ▸ xDeg_ady_lt k hpos
      have hne : ady k a ≠ 0 := ady_ne_zero k ha hpos
      have hy' : yDeg k (ady k a) = 0 := yDeg_ady_eq_zero k hy
      have hmem : ady k a ∈ I := by
        rw [ady_apply]
        exact I.sub_mem (I.mul_mem_left _ _ haI) (I.mul_mem_right _ _ haI)
      exact ih _ hlt (ady k a) rfl hy' hmem hne


private lemma one_mem_of_mem (I : TwoSidedIdeal (RepresentationTheory.FreeAlgebra.PolynomialOperators.OperatorAlgebra k)) :
    ∀ (n : ℕ) (a : RepresentationTheory.FreeAlgebra.PolynomialOperators.OperatorAlgebra k), yDeg k a = n → a ∈ I → a ≠ 0 →
      (1 : RepresentationTheory.FreeAlgebra.PolynomialOperators.OperatorAlgebra k) ∈ I := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro a hn haI ha
    rcases Nat.eq_zero_or_pos (yDeg k a) with h0 | hpos
    · exact one_mem_of_yDeg_zero k I (xDeg k a) a rfl h0 haI ha
    · have hlt : yDeg k (adx k a) < n := hn ▸ yDeg_adx_lt k hpos
      have hne : adx k a ≠ 0 := adx_ne_zero k ha hpos
      have hmem : adx k a ∈ I := by
        rw [adx_apply]
        exact I.sub_mem (I.mul_mem_left _ _ haI) (I.mul_mem_right _ _ haI)
      exact ih _ hlt (adx k a) rfl hmem hne


/-- The displayed algebra is a simple ring over any characteristic-zero field. -/
@[source_ref "Chapter2/Problem2.7.4" (role := primary)]
theorem isSimpleRing_of_charZero : IsSimpleRing (RepresentationTheory.FreeAlgebra.PolynomialOperators.OperatorAlgebra k) := by
  have hnt : (0 : RepresentationTheory.FreeAlgebra.PolynomialOperators.OperatorAlgebra k) ≠ 1 := by
    intro h
    have h2 := congrArg (RepresentationTheory.FreeAlgebra.PolynomialOperators.toPolynomialEnd k) h
    rw [map_zero, map_one] at h2
    have h3 := congrArg (fun f : Module.End k (Polynomial k) => f Polynomial.X) h2
    simp only [LinearMap.zero_apply, Module.End.one_apply] at h3
    exact Polynomial.X_ne_zero h3.symm
  haveI : Nontrivial (RepresentationTheory.FreeAlgebra.PolynomialOperators.OperatorAlgebra k) := ⟨0, 1, hnt⟩
  apply IsSimpleRing.of_eq_bot_or_eq_top
  intro I
  rw [or_iff_not_imp_left]
  intro hI
  obtain ⟨a, haI, ha⟩ :=
    SetLike.exists_of_lt (bot_lt_iff_ne_bot.mpr hI : (⊥ : TwoSidedIdeal (RepresentationTheory.FreeAlgebra.PolynomialOperators.OperatorAlgebra k)) < I)
  rw [TwoSidedIdeal.mem_bot] at ha
  exact (I.one_mem_iff).mp (one_mem_of_mem k I (yDeg k a) a rfl haI ha)

end CharZeroSimple




/-- The p-th power of the first displayed generator belongs to the center in characteristic p. -/
@[source_ref "Chapter2/Problem2.7.4" (role := supporting)]
theorem power_firstGenerator_mem_center (k : Type*) [Field k] (p : ℕ) [CharP k p] :
    RepresentationTheory.FreeAlgebra.PolynomialOperators.OperatorAlgebra.firstOperator k ^ p ∈ Subalgebra.center k (RepresentationTheory.FreeAlgebra.PolynomialOperators.OperatorAlgebra k) := by
  apply mem_center_of_comm_gen
  · exact (Commute.refl (RepresentationTheory.FreeAlgebra.PolynomialOperators.OperatorAlgebra.firstOperator k)).pow_left p
  ·
    cases p with
    | zero => simp
    | succ n =>
      have h := y_mul_x_pow_succ k n
      have hz : (n + 1 : ℕ) • RepresentationTheory.FreeAlgebra.PolynomialOperators.OperatorAlgebra.firstOperator k ^ n = 0 := by
        rw [← Nat.cast_smul_eq_nsmul (R := k), CharP.cast_eq_zero, zero_smul]
      rw [hz, add_zero] at h
      exact h.symm


/-- The p-th power of the second displayed generator belongs to the center in characteristic p. -/
@[source_ref "Chapter2/Problem2.7.4" (role := supporting)]
theorem power_secondGenerator_mem_center (k : Type*) [Field k] (p : ℕ) [CharP k p] :
    RepresentationTheory.FreeAlgebra.PolynomialOperators.OperatorAlgebra.secondOperator k ^ p ∈ Subalgebra.center k (RepresentationTheory.FreeAlgebra.PolynomialOperators.OperatorAlgebra k) := by
  apply mem_center_of_comm_gen
  ·
    cases p with
    | zero => simp
    | succ n =>
      have h := x_mul_y_pow_succ k n
      have hz : (n + 1 : ℕ) • RepresentationTheory.FreeAlgebra.PolynomialOperators.OperatorAlgebra.secondOperator k ^ n = 0 := by
        rw [← Nat.cast_smul_eq_nsmul (R := k), CharP.cast_eq_zero, zero_smul]
      rw [hz, sub_zero] at h
      exact h.symm
  · exact (Commute.refl (RepresentationTheory.FreeAlgebra.PolynomialOperators.OperatorAlgebra.secondOperator k)).pow_left p



section CharPCenter

variable (k : Type*) [Field k]

open RepresentationTheory.FreeAlgebra.PolynomialOperators.OperatorAlgebra Module


private noncomputable def monBasisP : Basis (ℕ × ℕ) k (RepresentationTheory.FreeAlgebra.PolynomialOperators.OperatorAlgebra k) :=
  Basis.mk (RepresentationTheory.Algebra.IntegerIndexedPolynomialOperators.operatorMonomials_linearIndependent_and_span k).1 (RepresentationTheory.Algebra.IntegerIndexedPolynomialOperators.operatorMonomials_linearIndependent_and_span k).2

private lemma monBasisP_apply (p : ℕ × ℕ) :
    monBasisP k p = RepresentationTheory.FreeAlgebra.PolynomialOperators.OperatorAlgebra.monomialOperator k p.1 p.2 :=
  Basis.mk_apply _ _ _

private lemma repr_monomialP (i j : ℕ) :
    (monBasisP k).repr (RepresentationTheory.FreeAlgebra.PolynomialOperators.OperatorAlgebra.monomialOperator k i j) = Finsupp.single (i, j) 1 := by
  rw [← monBasisP_apply k (i, j)]; exact (monBasisP k).repr_self _


private lemma repr_adx_applyP (a : RepresentationTheory.FreeAlgebra.PolynomialOperators.OperatorAlgebra k) (i j : ℕ) :
    (monBasisP k).repr (adx k a) (i, j)
      = -((j : k) + 1) * (monBasisP k).repr a (i, j + 1) := by
  have key :
      (Finsupp.lapply (i, j)).comp (((monBasisP k).repr.toLinearMap).comp (adx k))
        = (-((j : k) + 1)) •
            (Finsupp.lapply (i, j + 1)).comp ((monBasisP k).repr.toLinearMap) := by
    apply (monBasisP k).ext
    rintro ⟨i', j'⟩
    simp only [LinearMap.smul_apply, LinearMap.coe_comp, Function.comp_apply,
      LinearEquiv.coe_coe, Finsupp.lapply_apply, smul_eq_mul]
    rw [monBasisP_apply k (i', j'), repr_monomialP]
    cases j' with
    | zero =>
      rw [adx_monomial_zero, map_zero]
      simp [Prod.ext_iff]
    | succ n =>
      rw [adx_monomial_succ, map_smul, repr_monomialP, Finsupp.smul_apply,
        Finsupp.single_apply, Finsupp.single_apply, smul_eq_mul]
      by_cases h : (i', n) = (i, j)
      · obtain ⟨rfl, rfl⟩ := Prod.mk.injEq _ _ _ _ ▸ h
        simp
      · rw [if_neg h]
        rw [if_neg (by simp only [Prod.ext_iff] at h ⊢; omega)]
        ring
  have := LinearMap.congr_fun key a
  simpa only [LinearMap.smul_apply, LinearMap.coe_comp, Function.comp_apply,
    LinearEquiv.coe_coe, Finsupp.lapply_apply, smul_eq_mul] using this


private lemma repr_ady_applyP (a : RepresentationTheory.FreeAlgebra.PolynomialOperators.OperatorAlgebra k) (i j : ℕ) :
    (monBasisP k).repr (ady k a) (i, j)
      = ((i : k) + 1) * (monBasisP k).repr a (i + 1, j) := by
  have key :
      (Finsupp.lapply (i, j)).comp (((monBasisP k).repr.toLinearMap).comp (ady k))
        = (((i : k) + 1)) •
            (Finsupp.lapply (i + 1, j)).comp ((monBasisP k).repr.toLinearMap) := by
    apply (monBasisP k).ext
    rintro ⟨i', j'⟩
    simp only [LinearMap.smul_apply, LinearMap.coe_comp, Function.comp_apply,
      LinearEquiv.coe_coe, Finsupp.lapply_apply, smul_eq_mul]
    rw [monBasisP_apply k (i', j'), repr_monomialP]
    cases i' with
    | zero =>
      rw [ady_monomial_zero, map_zero]
      simp [Prod.ext_iff]
    | succ m =>
      rw [ady_monomial_succ, map_smul, repr_monomialP, Finsupp.smul_apply,
        Finsupp.single_apply, Finsupp.single_apply, smul_eq_mul]
      by_cases h : (m, j') = (i, j)
      · obtain ⟨rfl, rfl⟩ := Prod.mk.injEq _ _ _ _ ▸ h
        simp
      · rw [if_neg h]
        rw [if_neg (by simp only [Prod.ext_iff] at h ⊢; omega)]
        ring
  have := LinearMap.congr_fun key a
  simpa only [LinearMap.smul_apply, LinearMap.coe_comp, Function.comp_apply,
    LinearEquiv.coe_coe, Finsupp.lapply_apply, smul_eq_mul] using this

end CharPCenter


/-- In prime characteristic, the center is generated by the displayed p-th powers. -/
@[source_ref "Chapter2/Problem2.7.4" (role := primary)]
theorem center_eq_adjoin_powers (k : Type*) [Field k] (p : ℕ) [Fact (Nat.Prime p)] [CharP k p] :
    Subalgebra.center k (RepresentationTheory.FreeAlgebra.PolynomialOperators.OperatorAlgebra k)
      = Algebra.adjoin k {RepresentationTheory.FreeAlgebra.PolynomialOperators.OperatorAlgebra.firstOperator k ^ p, RepresentationTheory.FreeAlgebra.PolynomialOperators.OperatorAlgebra.secondOperator k ^ p} := by
  apply le_antisymm
  ·

    intro z hz

    have hadx : adx k z = 0 := by
      rw [adx_apply, sub_eq_zero]
      exact Subalgebra.mem_center_iff.mp hz (RepresentationTheory.FreeAlgebra.PolynomialOperators.OperatorAlgebra.firstOperator k)
    have hady : ady k z = 0 := by
      rw [ady_apply, sub_eq_zero]
      exact Subalgebra.mem_center_iff.mp hz (RepresentationTheory.FreeAlgebra.PolynomialOperators.OperatorAlgebra.secondOperator k)
    set c := (monBasisP k).repr z with hc

    have hcoefY : ∀ (i j : ℕ), 1 ≤ j → (j : k) * c (i, j) = 0 := by
      intro i j hj
      obtain ⟨j, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : j ≠ 0)
      have h := repr_adx_applyP k z i j
      rw [hadx, map_zero, Finsupp.zero_apply] at h
      have h2 : ((j : k) + 1) * c (i, j + 1) = 0 :=
        neg_eq_zero.mp (by rw [← neg_mul]; exact h.symm)
      rw [show ((j + 1 : ℕ) : k) = (j : k) + 1 by push_cast; ring]
      exact h2

    have hcoefX : ∀ (i j : ℕ), 1 ≤ i → (i : k) * c (i, j) = 0 := by
      intro i j hi
      obtain ⟨i, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : i ≠ 0)
      have h := repr_ady_applyP k z i j
      rw [hady, map_zero, Finsupp.zero_apply] at h
      have h2 : ((i : k) + 1) * c (i + 1, j) = 0 := by rw [← h]
      rw [show ((i + 1 : ℕ) : k) = (i : k) + 1 by push_cast; ring]
      exact h2

    have hsupp : ∀ q ∈ c.support, p ∣ q.1 ∧ p ∣ q.2 := by
      rintro ⟨i, j⟩ hq
      have hne : c (i, j) ≠ 0 := Finsupp.mem_support_iff.mp hq
      refine ⟨?_, ?_⟩
      · rcases Nat.eq_zero_or_pos i with hi | hi
        · rw [hi]; exact dvd_zero p
        · have hik : (i : k) = 0 :=
            (mul_eq_zero.mp (hcoefX i j hi)).resolve_right hne
          exact (CharP.cast_eq_zero_iff k p i).mp hik
      · rcases Nat.eq_zero_or_pos j with hj | hj
        · rw [hj]; exact dvd_zero p
        · have hjk : (j : k) = 0 :=
            (mul_eq_zero.mp (hcoefY i j hj)).resolve_right hne
          exact (CharP.cast_eq_zero_iff k p j).mp hjk

    have hz_eq : z = c.sum (fun q a => a • monBasisP k q) := by
      rw [hc, ← Finsupp.linearCombination_apply, (monBasisP k).linearCombination_repr]
    rw [hz_eq, Finsupp.sum]
    apply Subalgebra.sum_mem
    rintro ⟨i, j⟩ hq
    obtain ⟨hd1, hd2⟩ := hsupp (i, j) hq

    have hmem : RepresentationTheory.FreeAlgebra.PolynomialOperators.OperatorAlgebra.monomialOperator k i j ∈
        Algebra.adjoin k {RepresentationTheory.FreeAlgebra.PolynomialOperators.OperatorAlgebra.firstOperator k ^ p, RepresentationTheory.FreeAlgebra.PolynomialOperators.OperatorAlgebra.secondOperator k ^ p} := by
      have hxpS : RepresentationTheory.FreeAlgebra.PolynomialOperators.OperatorAlgebra.firstOperator k ^ p ∈
          Algebra.adjoin k {RepresentationTheory.FreeAlgebra.PolynomialOperators.OperatorAlgebra.firstOperator k ^ p, RepresentationTheory.FreeAlgebra.PolynomialOperators.OperatorAlgebra.secondOperator k ^ p} :=
        Algebra.subset_adjoin (Set.mem_insert _ _)
      have hypS : RepresentationTheory.FreeAlgebra.PolynomialOperators.OperatorAlgebra.secondOperator k ^ p ∈
          Algebra.adjoin k {RepresentationTheory.FreeAlgebra.PolynomialOperators.OperatorAlgebra.firstOperator k ^ p, RepresentationTheory.FreeAlgebra.PolynomialOperators.OperatorAlgebra.secondOperator k ^ p} :=
        Algebra.subset_adjoin (Set.mem_insert_of_mem _ rfl)
      have hx1 : RepresentationTheory.FreeAlgebra.PolynomialOperators.OperatorAlgebra.firstOperator k ^ i = (RepresentationTheory.FreeAlgebra.PolynomialOperators.OperatorAlgebra.firstOperator k ^ p) ^ (i / p) := by
        rw [← pow_mul, Nat.mul_div_cancel' hd1]
      have hy1 : RepresentationTheory.FreeAlgebra.PolynomialOperators.OperatorAlgebra.secondOperator k ^ j = (RepresentationTheory.FreeAlgebra.PolynomialOperators.OperatorAlgebra.secondOperator k ^ p) ^ (j / p) := by
        rw [← pow_mul, Nat.mul_div_cancel' hd2]
      rw [RepresentationTheory.FreeAlgebra.PolynomialOperators.OperatorAlgebra.monomialOperator, hx1, hy1]
      exact mul_mem (pow_mem hxpS _) (pow_mem hypS _)
    rw [monBasisP_apply]
    exact Subalgebra.smul_mem _ hmem _
  ·
    apply Algebra.adjoin_le
    intro w hw
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hw
    rcases hw with rfl | rfl
    · exact power_firstGenerator_mem_center k p
    · exact power_secondGenerator_mem_center k p




private lemma mem_of_invariant (k : Type*) [Field k] (V : Type*) [AddCommGroup V] [Module k V]
    [Module (RepresentationTheory.FreeAlgebra.PolynomialOperators.OperatorAlgebra k) V] [IsScalarTower k (RepresentationTheory.FreeAlgebra.PolynomialOperators.OperatorAlgebra k) V]
    [IsSimpleModule (RepresentationTheory.FreeAlgebra.PolynomialOperators.OperatorAlgebra k) V] (Wk : Submodule k V)
    (hstab : ∀ (a : RepresentationTheory.FreeAlgebra.PolynomialOperators.OperatorAlgebra k) (z : V), z ∈ Wk → a • z ∈ Wk)
    (hne : ∃ z ∈ Wk, z ≠ 0) : ∀ z : V, z ∈ Wk := by
  let WA : Submodule (RepresentationTheory.FreeAlgebra.PolynomialOperators.OperatorAlgebra k) V :=
    { carrier := Wk
      add_mem' := fun ha hb => Wk.add_mem ha hb
      zero_mem' := Wk.zero_mem
      smul_mem' := fun a z hz => hstab a z hz }
  have hbot : WA ≠ ⊥ := by
    obtain ⟨z, hz, hz0⟩ := hne
    intro h
    apply hz0
    have hzWA : z ∈ WA := hz
    rw [h, Submodule.mem_bot] at hzWA
    exact hzWA
  have hWA : WA = ⊤ := (eq_bot_or_eq_top WA).resolve_left hbot
  intro z
  have : z ∈ WA := hWA ▸ Submodule.mem_top
  exact this


private lemma central_smul_scalar (k : Type*) [Field k] [IsAlgClosed k] (V : Type*)
    [AddCommGroup V] [Module k V] [Module (RepresentationTheory.FreeAlgebra.PolynomialOperators.OperatorAlgebra k) V] [IsScalarTower k (RepresentationTheory.FreeAlgebra.PolynomialOperators.OperatorAlgebra k) V]
    [FiniteDimensional k V] [IsSimpleModule (RepresentationTheory.FreeAlgebra.PolynomialOperators.OperatorAlgebra k) V]
    (z : RepresentationTheory.FreeAlgebra.PolynomialOperators.OperatorAlgebra k) (hz : z ∈ Subalgebra.center k (RepresentationTheory.FreeAlgebra.PolynomialOperators.OperatorAlgebra k)) :
    ∃ μ : k, ∀ w : V, z • w = μ • w := by
  haveI : Nontrivial V := IsSimpleModule.nontrivial (RepresentationTheory.FreeAlgebra.PolynomialOperators.OperatorAlgebra k) V
  obtain ⟨μ, hμ⟩ := (Algebra.lsmul k k V z).exists_eigenvalue
  refine ⟨μ, ?_⟩
  have hstab : ∀ (a : RepresentationTheory.FreeAlgebra.PolynomialOperators.OperatorAlgebra k) (w : V),
      w ∈ Module.End.eigenspace (Algebra.lsmul k k V z) μ →
      a • w ∈ Module.End.eigenspace (Algebra.lsmul k k V z) μ := by
    intro a w hw
    rw [Module.End.mem_eigenspace_iff, Algebra.lsmul_apply] at hw ⊢
    calc z • (a • w) = (a * z) • w := by
              rw [← mul_smul, ← Subalgebra.mem_center_iff.mp hz a]
      _ = a • (z • w) := by rw [mul_smul]
      _ = a • (μ • w) := by rw [hw]
      _ = μ • (a • w) := by rw [smul_comm]
  obtain ⟨w0, hw0⟩ := hμ.exists_hasEigenvector
  have hmem := mem_of_invariant k V (Module.End.eigenspace (Algebra.lsmul k k V z) μ)
    hstab ⟨w0, hw0.1, hw0.2⟩
  intro w
  have hw := hmem w
  rw [Module.End.mem_eigenspace_iff, Algebra.lsmul_apply] at hw
  exact hw


private lemma val_add_one (p : ℕ) [Fact (Nat.Prime p)] (i : Fin p) :
    ((i + 1 : Fin p) : ℕ) = ((i : ℕ) + 1) % p := by
  haveI : NeZero p := ⟨(Fact.out : p.Prime).ne_zero⟩
  rw [Fin.val_add, Fin.val_one', Nat.mod_eq_of_lt (Fact.out : p.Prime).one_lt]


private lemma add_one_cases (p : ℕ) [Fact (Nat.Prime p)] (i : Fin p) :
    ((i : ℕ) + 1 = p ∧ (i + 1 : Fin p) = 0) ∨
      ((i : ℕ) + 1 < p ∧ ((i + 1 : Fin p) : ℕ) = (i : ℕ) + 1) := by
  haveI : NeZero p := ⟨(Fact.out : p.Prime).ne_zero⟩
  have hval := val_add_one p i
  rcases Nat.lt_or_ge ((i : ℕ) + 1) p with h | h
  · exact Or.inr ⟨h, by rw [hval, Nat.mod_eq_of_lt h]⟩
  · have hp : (i : ℕ) + 1 = p := le_antisymm i.isLt h
    refine Or.inl ⟨hp, Fin.ext ?_⟩
    rw [hval, hp, Nat.mod_self, Fin.val_zero]


/-- A finite-dimensional simple module in prime characteristic admits parameters and a cyclically indexed basis with the stated actions. -/
@[source_ref "Chapter2/Problem2.7.4" (role := supporting)]
theorem exists_cyclic_basis_of_simpleModule (k : Type*) [Field k] [IsAlgClosed k] (p : ℕ)
    [Fact (Nat.Prime p)] [CharP k p]
    (V : Type*) [AddCommGroup V] [Module k V] [Module (RepresentationTheory.FreeAlgebra.PolynomialOperators.OperatorAlgebra k) V]
    [IsScalarTower k (RepresentationTheory.FreeAlgebra.PolynomialOperators.OperatorAlgebra k) V] [FiniteDimensional k V]
    [IsSimpleModule (RepresentationTheory.FreeAlgebra.PolynomialOperators.OperatorAlgebra k) V] :
    ∃ (α c : k) (b : Module.Basis (Fin p) k V),
      (∀ i : Fin p,
        RepresentationTheory.FreeAlgebra.PolynomialOperators.OperatorAlgebra.firstOperator k • b i = (if (i + 1 : Fin p) = 0 then α else 1) • b (i + 1)) ∧
      (∀ i : Fin p,
        RepresentationTheory.FreeAlgebra.PolynomialOperators.OperatorAlgebra.secondOperator k • b (i + 1) = c • b (i + 1) + (((i : ℕ) + 1 : ℕ) : k) • b i) := by
  haveI : Nontrivial V := IsSimpleModule.nontrivial (RepresentationTheory.FreeAlgebra.PolynomialOperators.OperatorAlgebra k) V
  have p_pos : 0 < p := (Fact.out : p.Prime).pos
  have hfac : ∀ m : ℕ, m < p → ((m.factorial : ℕ) : k) ≠ 0 := by
    intro m hm
    rw [ne_eq, CharP.cast_eq_zero_iff k p, Nat.Prime.dvd_factorial Fact.out]
    exact Nat.not_le.mpr hm

  obtain ⟨lam, hlam⟩ := (Algebra.lsmul k k V (RepresentationTheory.FreeAlgebra.PolynomialOperators.OperatorAlgebra.secondOperator k)).exists_eigenvalue
  obtain ⟨v, hv⟩ := hlam.exists_hasEigenvector
  have hyv : RepresentationTheory.FreeAlgebra.PolynomialOperators.OperatorAlgebra.secondOperator k • v = lam • v := by
    have h := Module.End.mem_eigenspace_iff.mp hv.1
    rwa [Algebra.lsmul_apply] at h
  have hv0 : v ≠ 0 := hv.2
  set w : ℕ → V := fun i => RepresentationTheory.FreeAlgebra.PolynomialOperators.OperatorAlgebra.firstOperator k ^ i • v with hwdef
  have hwv : ∀ i, w i = RepresentationTheory.FreeAlgebra.PolynomialOperators.OperatorAlgebra.firstOperator k ^ i • v := fun _ => rfl
  have hw0 : w 0 = v := by rw [hwv, pow_zero, one_smul]

  obtain ⟨μ, hμ⟩ := central_smul_scalar k V (RepresentationTheory.FreeAlgebra.PolynomialOperators.OperatorAlgebra.firstOperator k ^ p) (power_firstGenerator_mem_center k p)

  set N : Module.End k V := Algebra.lsmul k k V (RepresentationTheory.FreeAlgebra.PolynomialOperators.OperatorAlgebra.secondOperator k) - lam • 1 with hN
  have hNstep : ∀ i : ℕ, N (w (i + 1)) = ((i + 1 : ℕ) : k) • w i := by
    intro i
    rw [hwv (i + 1), hN, LinearMap.sub_apply, LinearMap.smul_apply, Module.End.one_apply,
      Algebra.lsmul_apply, ← mul_smul, y_mul_x_pow_succ k i, add_smul, mul_smul, hyv,
      smul_comm (RepresentationTheory.FreeAlgebra.PolynomialOperators.OperatorAlgebra.firstOperator k ^ (i + 1)) lam v,
      ← Nat.cast_smul_eq_nsmul k (i + 1) (RepresentationTheory.FreeAlgebra.PolynomialOperators.OperatorAlgebra.firstOperator k ^ i), smul_assoc, hwv i]
    abel
  have hN0 : N (w 0) = 0 := by
    rw [hwv, hN, LinearMap.sub_apply, LinearMap.smul_apply, Module.End.one_apply,
      Algebra.lsmul_apply, pow_zero, one_smul, hyv, sub_self]
  have hkill1 : ∀ i : ℕ, (N ^ (i + 1)) (w i) = 0 := by
    intro i
    induction i with
    | zero => rw [pow_one]; exact hN0
    | succ n ih => rw [pow_succ, Module.End.mul_apply, hNstep, map_smul, ih, smul_zero]
  have hval : ∀ i : ℕ, (N ^ i) (w i) = ((i.factorial : ℕ) : k) • v := by
    intro i
    induction i with
    | zero => rw [pow_zero, Module.End.one_apply, hw0, Nat.factorial_zero, Nat.cast_one, one_smul]
    | succ n ih =>
      rw [pow_succ, Module.End.mul_apply, hNstep, map_smul, ih, smul_smul, ← Nat.cast_mul,
        ← Nat.factorial_succ]
  have hkill_gen : ∀ (m j : ℕ), j < m → (N ^ m) (w j) = 0 := by
    intro m j hjm
    obtain ⟨t, ht⟩ : ∃ t, m = t + (j + 1) := ⟨m - (j + 1), by omega⟩
    rw [ht, pow_add, Module.End.mul_apply, hkill1, map_zero]

  have hli : ∀ n : ℕ, n ≤ p → LinearIndependent k (fun i : Fin n => w (i : ℕ)) := by
    intro n
    induction n with
    | zero => intro _; exact linearIndependent_empty_type
    | succ m ih =>
      intro hmp
      have hmp' : m ≤ p := Nat.le_of_succ_le hmp
      have hmlt : m < p := hmp
      have hfun : (fun i : Fin (m + 1) => w (i : ℕ))
          = Fin.snoc (fun i : Fin m => w (i : ℕ)) (w m) := by
        funext i
        induction i using Fin.lastCases with
        | last => simp
        | cast j => simp
      rw [hfun]
      refine (ih hmp').finSnoc ?_
      intro hmem
      have hzero : (N ^ m) (w m) = 0 := by
        have hsub : Submodule.span k (Set.range (fun i : Fin m => w (i : ℕ)))
            ≤ LinearMap.ker (N ^ m) := by
          rw [Submodule.span_le]
          rintro _ ⟨i, rfl⟩
          simp only [SetLike.mem_coe, LinearMap.mem_ker]
          exact hkill_gen m (i : ℕ) i.isLt
        have hk := hsub hmem
        rwa [LinearMap.mem_ker] at hk
      rw [hval m] at hzero
      rcases smul_eq_zero.mp hzero with h | h
      · exact hfac m hmlt h
      · exact hv0 h

  set Wk : Submodule k V := Submodule.span k (Set.range (fun i : Fin p => w (i : ℕ))) with hWk
  have hgen_mem : ∀ i : Fin p, w (i : ℕ) ∈ Wk := fun i => Submodule.subset_span ⟨i, rfl⟩
  have hshift : ∀ t : ℕ, w (p + t) = μ • w t := by
    intro t
    rw [hwv (p + t), hwv t, pow_add, mul_smul, hμ (RepresentationTheory.FreeAlgebra.PolynomialOperators.OperatorAlgebra.firstOperator k ^ t • v)]
  have hall_mem : ∀ j : ℕ, w j ∈ Wk := by
    intro j
    induction j using Nat.strong_induction_on with
    | _ j ih =>
      by_cases hjp : j < p
      · exact hgen_mem ⟨j, hjp⟩
      · obtain ⟨t, ht⟩ : ∃ t, j = p + t := ⟨j - p, by omega⟩
        subst ht
        rw [hshift]
        exact Wk.smul_mem μ (ih t (by omega))
  have hx_stab : ∀ z ∈ Wk, RepresentationTheory.FreeAlgebra.PolynomialOperators.OperatorAlgebra.firstOperator k • z ∈ Wk := by
    intro z hz
    rw [hWk] at hz
    induction hz using Submodule.span_induction with
    | mem u hu =>
        obtain ⟨i, rfl⟩ := hu
        change RepresentationTheory.FreeAlgebra.PolynomialOperators.OperatorAlgebra.firstOperator k • w (i : ℕ) ∈ Wk
        rw [hwv, ← mul_smul, ← pow_succ', ← hwv]
        exact hall_mem ((i : ℕ) + 1)
    | zero => rw [smul_zero]; exact Wk.zero_mem
    | add a b _ _ ha hb => rw [smul_add]; exact Wk.add_mem ha hb
    | smul c a _ ha => rw [smul_comm]; exact Wk.smul_mem c ha
  have hy_stab : ∀ z ∈ Wk, RepresentationTheory.FreeAlgebra.PolynomialOperators.OperatorAlgebra.secondOperator k • z ∈ Wk := by
    intro z hz
    rw [hWk] at hz
    induction hz using Submodule.span_induction with
    | mem u hu =>
        obtain ⟨i, rfl⟩ := hu
        change RepresentationTheory.FreeAlgebra.PolynomialOperators.OperatorAlgebra.secondOperator k • w (i : ℕ) ∈ Wk
        have hNexp : N (w (i : ℕ)) = RepresentationTheory.FreeAlgebra.PolynomialOperators.OperatorAlgebra.secondOperator k • w (i : ℕ) - lam • w (i : ℕ) := by
          rw [hN, LinearMap.sub_apply, LinearMap.smul_apply, Module.End.one_apply,
            Algebra.lsmul_apply]
        have hNwi : N (w (i : ℕ)) ∈ Wk := by
          cases hci : (i : ℕ) with
          | zero => rw [hN0]; exact Wk.zero_mem
          | succ j =>
              rw [hNstep]
              exact Wk.smul_mem _ (hall_mem j)
        have key : RepresentationTheory.FreeAlgebra.PolynomialOperators.OperatorAlgebra.secondOperator k • w (i : ℕ) = N (w (i : ℕ)) + lam • w (i : ℕ) := by
          rw [hNexp]; abel
        rw [key]
        exact Wk.add_mem hNwi (Wk.smul_mem lam (hall_mem (i : ℕ)))
    | zero => rw [smul_zero]; exact Wk.zero_mem
    | add a b _ _ ha hb => rw [smul_add]; exact Wk.add_mem ha hb
    | smul c a _ ha => rw [smul_comm]; exact Wk.smul_mem c ha
  have ha_stab : ∀ (a : RepresentationTheory.FreeAlgebra.PolynomialOperators.OperatorAlgebra k) (z : V), z ∈ Wk → a • z ∈ Wk := by
    intro a
    obtain ⟨a', rfl⟩ := RingQuot.mkAlgHom_surjective k (RepresentationTheory.FreeAlgebra.PolynomialOperators.freeAlgebraRelation k) a
    have ha' : a' ∈ Algebra.adjoin k (Set.range (FreeAlgebra.ι k)) := by
      rw [FreeAlgebra.adjoin_range_ι]; exact Algebra.mem_top
    induction ha' using Algebra.adjoin_induction with
    | mem g hg =>
        obtain ⟨idx, rfl⟩ := hg
        intro z hz
        fin_cases idx
        · exact hx_stab z hz
        · exact hy_stab z hz
    | algebraMap r =>
        intro z hz
        rw [AlgHom.commutes, algebraMap_smul]
        exact Wk.smul_mem r hz
    | add p q _ _ ihp ihq =>
        intro z hz
        rw [map_add, add_smul]
        exact Wk.add_mem (ihp z hz) (ihq z hz)
    | mul p q _ _ ihp ihq =>
        intro z hz
        rw [map_mul, mul_smul]
        exact ihp _ (ihq z hz)
  have hspan_top : ∀ z : V, z ∈ Wk :=
    mem_of_invariant k V Wk ha_stab ⟨v, hw0 ▸ hgen_mem ⟨0, p_pos⟩, hv0⟩
  have hsp : ⊤ ≤ Submodule.span k (Set.range (fun i : Fin p => w (i : ℕ))) := by
    rw [← hWk]; intro z _; exact hspan_top z
  have hli_p : LinearIndependent k (fun i : Fin p => w (i : ℕ)) := hli p le_rfl

  refine ⟨μ, lam, Module.Basis.mk hli_p hsp, ?_, ?_⟩
  · intro i
    simp only [Module.Basis.mk_apply]
    have hstep : RepresentationTheory.FreeAlgebra.PolynomialOperators.OperatorAlgebra.firstOperator k • w (i : ℕ) = w ((i : ℕ) + 1) := by
      rw [hwv, hwv, ← mul_smul, ← pow_succ']
    rcases add_one_cases p i with ⟨hp, h0⟩ | ⟨hlt, hval⟩
    · rw [h0, if_pos rfl, hstep, hp, Fin.val_zero, hw0]
      exact hμ v
    · have hne : (i + 1 : Fin p) ≠ 0 := by
        intro h
        rw [h, Fin.val_zero] at hval
        omega
      rw [if_neg hne, one_smul, hval, hstep]
  · intro i
    simp only [Module.Basis.mk_apply]
    rcases add_one_cases p i with ⟨hp, h0⟩ | ⟨_, hval⟩
    ·
      rw [h0, Fin.val_zero, hw0, hyv, hp, CharP.cast_eq_zero k p, zero_smul, add_zero]
    ·
      have hN' := hNstep (i : ℕ)
      rw [hN, LinearMap.sub_apply, LinearMap.smul_apply, Module.End.one_apply,
        Algebra.lsmul_apply, sub_eq_iff_eq_add'] at hN'
      rw [hval, hN']


/-- A finite-dimensional simple module over an algebraically closed field of prime characteristic has dimension p. -/
theorem finrank_eq_prime_of_simpleModule (k : Type*) [Field k] [IsAlgClosed k] (p : ℕ)
    [Fact (Nat.Prime p)] [CharP k p]
    (V : Type*) [AddCommGroup V] [Module k V] [Module (RepresentationTheory.FreeAlgebra.PolynomialOperators.OperatorAlgebra k) V]
    [IsScalarTower k (RepresentationTheory.FreeAlgebra.PolynomialOperators.OperatorAlgebra k) V] [FiniteDimensional k V]
    [IsSimpleModule (RepresentationTheory.FreeAlgebra.PolynomialOperators.OperatorAlgebra k) V] :
    Module.finrank k V = p := by
  obtain ⟨_, _, b, _, _⟩ := exists_cyclic_basis_of_simpleModule k p V
  rw [Module.finrank_eq_card_basis b, Fintype.card_fin]

end RepresentationTheory.NoncommutativeAlgebra.PositiveCharacteristic

