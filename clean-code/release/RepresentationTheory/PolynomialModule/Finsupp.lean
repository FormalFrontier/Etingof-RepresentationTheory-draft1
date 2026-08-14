/-
Copyright (c) 2026 FormalFrontier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: FormalFrontier
-/
import Mathlib.Algebra.Category.ModuleCat.ChangeOfRings
import Mathlib.RingTheory.Polynomial.Basic
import Mathlib.Algebra.Polynomial.Module.TensorProduct
import Mathlib.LinearAlgebra.Finsupp.VectorSpace
import Mathlib.Algebra.Polynomial.Inductions

/-!
# Finitely supported coordinates for polynomial-module tensors

This module identifies polynomial tensors with finitely supported coefficient families and records
auxiliary recurrence and finite-sum identities.
-/

set_option backward.isDefEq.respectTransparency false

universe u

open Polynomial CategoryTheory

namespace RepresentationTheory.PolynomialModule.Finsupp

variable {R : Type u} [CommRing R]

/-- A finitely supported family satisfying a successor recurrence with a zero-preserving map is
zero. -/
theorem finsupp_eq_zero_of_apply_eq_map_succ {M : Type u} [AddCommGroup M]
    (g : M → M) (hg0 : g 0 = 0)
    (f : ℕ →₀ M) (h : ∀ k, f (k) = g (f (k + 1))) :
    f = 0 := by
  by_contra hf
  have hsup : f.support.Nonempty := Finsupp.support_nonempty_iff.mpr hf
  set N := f.support.max' hsup
  have hN : f N ≠ 0 := Finsupp.mem_support_iff.mp (Finset.max'_mem _ hsup)
  have hN1 : f (N + 1) = 0 := by
    by_contra h'
    have : N + 1 ∈ f.support := Finsupp.mem_support_iff.mpr h'
    exact Nat.not_succ_le_self N (Finset.le_max' _ _ this)
  exact hN (by rw [h N, hN1, hg0])

/-- The module structure obtained by restricting polynomial scalars along constants agrees with
the standard one. -/
theorem restrictScalars_polynomial_module_eq :
    ((ModuleCat.restrictScalars.{u} (Polynomial.C (R := R))).obj
      (ModuleCat.of (Polynomial R) (Polynomial R))).isModule =
    Polynomial.module (R := R) := by
  apply Module.ext'; intro r p
  let p' : Polynomial R := p
  change Polynomial.C r * p' = r • p'
  rw [← Polynomial.smul_eq_C_mul]

/-- The polynomial-module endomorphism given by multiplication by `X` minus a mapped linear action
is injective. -/
theorem X_smul_id_sub_map_injective
    {N : Type u} [AddCommGroup N] [Module R N]
    (xAct : N →ₗ[R] N) :
    Function.Injective
      (((Polynomial.X : Polynomial R) • LinearMap.id (M := PolynomialModule R N) -
        PolynomialModule.map R xAct : PolynomialModule R N →ₗ[R] PolynomialModule R N)) := by
  rw [← LinearMap.ker_eq_bot, Submodule.eq_bot_iff]
  intro f hf
  have hdf : ∀ n,
      ((Polynomial.X : Polynomial R) • f - PolynomialModule.map R xAct f).coeff n = 0 := by
    intro n
    exact DFunLike.congr_fun (congrArg PolynomialModule.coeff (LinearMap.mem_ker.mp hf)) n
  have hshift : ∀ k, f.coeff k = xAct (f.coeff (k + 1)) := by
    intro k
    have := hdf (k + 1)
    change ((Polynomial.X : Polynomial R) • f).coeff (k + 1) -
        (PolynomialModule.map R xAct f).coeff (k + 1) = 0 at this
    rw [show (Polynomial.X : Polynomial R) = Polynomial.monomial 1 1 from rfl,
        PolynomialModule.monomial_smul_apply,
        if_pos (Nat.one_le_iff_ne_zero.mpr (Nat.succ_ne_zero k))] at this
    simp only [Nat.add_sub_cancel, one_smul, PolynomialModule.map] at this
    change f.coeff k - xAct (f.coeff (k + 1)) = 0 at this
    exact sub_eq_zero.mp this
  by_contra hf_ne
  have hcoeff_ne : f.coeff ≠ 0 := by
    intro h
    exact hf_ne (PolynomialModule.coeff_inj.mp h)
  have hsup : f.coeff.support.Nonempty := Finsupp.support_nonempty_iff.mpr hcoeff_ne
  set K := f.coeff.support.max' hsup
  exact Finsupp.mem_support_iff.mp (Finset.max'_mem _ hsup)
    (by rw [hshift K, show f.coeff (K + 1) = 0 from by
      by_contra h'; exact Nat.not_succ_le_self K
        (Finset.le_max' _ _ (Finsupp.mem_support_iff.mpr h')), map_zero])

/-- Sends a tensor of a polynomial with a module element to its finitely supported coefficient
family. -/
noncomputable def tensorPolynomialToFinsupp
    (N : Type u) [AddCommGroup N] [Module R N] :
    letI : Module R (Polynomial R) :=
      ((ModuleCat.restrictScalars.{u} (Polynomial.C (R := R))).obj
        (ModuleCat.of (Polynomial R) (Polynomial R))).isModule
    @TensorProduct R _ (Polynomial R) N _ _ _ _ →ₗ[R] (ℕ →₀ N) := by
  letI : Module R (Polynomial R) :=
    ((ModuleCat.restrictScalars.{u} (Polynomial.C (R := R))).obj
      (ModuleCat.of (Polynomial R) (Polynomial R))).isModule
  exact TensorProduct.lift
    { toFun := fun (p : Polynomial R) =>
        { toFun := fun (m : N) => p.toFinsupp.coeff.mapRange (· • m) (by simp)
          map_add' := fun m₁ m₂ => by ext k; simp [smul_add]
          map_smul' := fun r m => by
            ext k
            simp only [Finsupp.mapRange_apply, RingHom.id_apply, Finsupp.coe_smul,
              Pi.smul_apply]
            exact smul_comm _ _ _ }
      map_add' := fun p q => by ext m k; simp [add_smul, Polynomial.toFinsupp_add]
      map_smul' := fun r p => by
        ext m k
        simp only [Finsupp.mapRange_apply, LinearMap.coe_mk, AddHom.coe_mk,
          RingHom.id_apply, LinearMap.smul_apply, Finsupp.smul_apply]
        change (Polynomial.C r * p).toFinsupp.coeff k • m =
          r • (p.toFinsupp.coeff k • m)
        rw [show (Polynomial.C r * p).toFinsupp.coeff k = r * p.toFinsupp.coeff k from
          Polynomial.coeff_C_mul p]
        exact mul_smul _ _ _ }

/-- Builds a polynomial tensor expression from a finitely supported family indexed by natural
numbers. -/
noncomputable def finsuppToTensorPolynomial
    (N : Type u) [AddCommGroup N] [Module R N] :
    letI : Module R (Polynomial R) :=
      ((ModuleCat.restrictScalars.{u} (Polynomial.C (R := R))).obj
        (ModuleCat.of (Polynomial R) (Polynomial R))).isModule
    (ℕ →₀ N) →ₗ[R] @TensorProduct R _ (Polynomial R) N _ _ _ _ := by
  letI : Module R (Polynomial R) :=
    ((ModuleCat.restrictScalars.{u} (Polynomial.C (R := R))).obj
      (ModuleCat.of (Polynomial R) (Polynomial R))).isModule
  exact
    { toFun := fun f => f.sum (fun (k : ℕ) (m : N) =>
        @TensorProduct.tmul R _ (Polynomial R) N _ _ _ _ ((X : Polynomial R) ^ k) m)
      map_add' := fun f g =>
        Finsupp.sum_add_index'
          (fun k => TensorProduct.tmul_zero (R := R) (M := Polynomial R) (N := N) _)
          (fun k _ _ => TensorProduct.tmul_add (R := R) (M := Polynomial R) _ _ _)
      map_smul' := fun r f => by
        simp only [RingHom.id_apply]
        conv_rhs => rw [Finsupp.smul_sum]
        rw [Finsupp.sum_smul_index'
          (fun (k : ℕ) => TensorProduct.tmul_zero (R := R) (M := Polynomial R) (N := N) _)]
        congr 1; ext k m
        exact (Quotient.sound' (AddConGen.Rel.of _ _
          (TensorProduct.Eqv.of_smul r ((X : Polynomial R) ^ k) m))).symm }

/-- Converting a polynomial tensor to coefficients and back recovers the original tensor. -/
theorem finsuppToTensorPolynomial_leftInverse_tensorPolynomialToFinsupp
    (N : Type u) [AddCommGroup N] [Module R N] :
    Function.LeftInverse (finsuppToTensorPolynomial N (R := R))
      (tensorPolynomialToFinsupp N (R := R)) := by
  letI : Module R (Polynomial R) :=
    ((ModuleCat.restrictScalars.{u} (Polynomial.C (R := R))).obj
      (ModuleCat.of (Polynomial R) (Polynomial R))).isModule
  intro t
  refine TensorProduct.induction_on t ?_ ?_ ?_
  · simp only [map_zero]
  · intro p m
    refine Polynomial.induction_on' p ?_ ?_
    · intro p₁ p₂ ih₁ ih₂
      rw [TensorProduct.add_tmul, map_add, map_add, ih₁, ih₂]
    · intro n a
      simp only [tensorPolynomialToFinsupp, TensorProduct.lift.tmul, LinearMap.coe_mk,
        AddHom.coe_mk]
      rw [Polynomial.toFinsupp_monomial, AddMonoidAlgebra.coeff_single,
        Finsupp.mapRange_single]
      simp only [finsuppToTensorPolynomial, LinearMap.coe_mk, AddHom.coe_mk]
      have key : ((Finsupp.single n (a • m)).sum fun (k : ℕ) (v : N) =>
          @TensorProduct.tmul R _ (Polynomial R) N _ _ _ _ ((X : Polynomial R) ^ k) v) =
          @TensorProduct.tmul R _ (Polynomial R) N _ _ _ _ ((X : Polynomial R) ^ n) (a • m) :=
        Finsupp.sum_single_index
          (TensorProduct.tmul_zero (R := R) (M := Polynomial R) (N := N) _)
      rw [key]
      symm
      have h_monomial : (Polynomial.monomial n) a = @HSMul.hSMul R _ _
          (@instHSMul R _ (((ModuleCat.restrictScalars.{u} (Polynomial.C (R := R))).obj
            (ModuleCat.of (Polynomial R) (Polynomial R))).isModule).toSMul) a
          ((X : Polynomial R) ^ n) :=
        (Polynomial.C_mul_X_pow_eq_monomial).symm
      rw [h_monomial]
      exact Quotient.sound' (AddConGen.Rel.of _ _
        (TensorProduct.Eqv.of_smul a ((Polynomial.X : Polynomial R) ^ n) m))
  · intro x y hx hy; simp only [map_add, hx, hy]

/-- Converting a finitely supported coefficient family to a polynomial tensor and back recovers the
family. -/
theorem finsuppToTensorPolynomial_rightInverse_tensorPolynomialToFinsupp
    (N : Type u) [AddCommGroup N] [Module R N] :
    Function.RightInverse (finsuppToTensorPolynomial N (R := R))
      (tensorPolynomialToFinsupp N (R := R)) := by
  letI : Module R (Polynomial R) :=
    ((ModuleCat.restrictScalars.{u} (Polynomial.C (R := R))).obj
      (ModuleCat.of (Polynomial R) (Polynomial R))).isModule
  intro f
  refine Finsupp.ext fun k => ?_
  simp only [finsuppToTensorPolynomial, LinearMap.coe_mk, AddHom.coe_mk]
  rw [Finsupp.sum, map_sum]
  simp only [tensorPolynomialToFinsupp, TensorProduct.lift.tmul, LinearMap.coe_mk,
    AddHom.coe_mk, Polynomial.toFinsupp_X_pow, AddMonoidAlgebra.coeff_single,
    Finsupp.mapRange_single, one_smul, Finsupp.finsetSum_apply, Finsupp.single_apply]
  rw [Finset.sum_eq_single k
    (fun n _ hne => if_neg hne)
    (fun h => by simp [Finsupp.mem_support_iff, not_not] at h; simp [h])]
  exact if_pos rfl

/-- The coefficient-family map on polynomial tensors is injective. -/
theorem tensorPolynomialToFinsupp_injective
    (N : Type u) [AddCommGroup N] [Module R N] :
    Function.Injective (tensorPolynomialToFinsupp N (R := R)) :=
  (finsuppToTensorPolynomial_leftInverse_tensorPolynomialToFinsupp N).injective

/-- The map from polynomial tensors to finitely supported coefficient families is bijective. -/
theorem tensorPolynomialToFinsupp_bijective
    (N : Type u) [AddCommGroup N] [Module R N] :
    Function.Bijective (tensorPolynomialToFinsupp N (R := R)) :=
  ⟨tensorPolynomialToFinsupp_injective N,
    (finsuppToTensorPolynomial_rightInverse_tensorPolynomialToFinsupp N).surjective⟩

/-- Rewrites a finite sum of iterated linear-map actions using its zeroth term and shifted
coefficient sum. -/
theorem finsupp_sum_powers_eq_zero_add_map_sum_range
    {M : Type u} [AddCommGroup M] [Module R M]
    (φ : M →ₗ[R] M) (f : ℕ →₀ M)
    (B : ℕ) (hB : ∀ n ∈ f.support, n < B) :
    f 0 + φ ((Finset.range (B + 1)).sum (fun j => (φ ^ j) (f (0 + 1 + j)))) =
    f.sum (fun k m => (φ ^ k) m) := by
  rw [map_sum]
  have key : f 0 + (Finset.range (B + 1)).sum
      (fun j => φ ((φ ^ j) (f (0 + 1 + j)))) =
      (Finset.range (B + 2)).sum (fun i => (φ ^ i) (f i)) := by
    have hsum_eq : (Finset.range (B + 1)).sum
        (fun j => φ ((φ ^ j) (f (0 + 1 + j)))) =
        (Finset.range (B + 1)).sum (fun j => (φ ^ (j + 1)) (f (j + 1))) := by
      apply Finset.sum_congr rfl; intro j _
      rw [show 0 + 1 + j = j + 1 from by omega, pow_succ' φ j]; rfl
    rw [hsum_eq, show f 0 = (φ ^ 0) (f 0) from by simp [pow_zero], add_comm,
        show B + 1 + 1 = B + 2 from by omega]
    exact (Finset.sum_range_succ' (fun i => (φ ^ i) (f i)) (B + 1)).symm
  rw [key]
  rw [Finsupp.sum]
  have hsub : f.support ⊆ Finset.range (B + 2) :=
    fun k hk => Finset.mem_range.mpr (by linarith [hB k hk])
  have hzero : ∀ k ∈ Finset.range (B + 2), k ∉ f.support → (φ ^ k) (f k) = 0 :=
    fun k _ hk => by simp [Finsupp.mem_support_iff] at hk; rw [hk, map_zero]
  exact (Finset.sum_subset hsub hzero).symm

end RepresentationTheory.PolynomialModule.Finsupp
