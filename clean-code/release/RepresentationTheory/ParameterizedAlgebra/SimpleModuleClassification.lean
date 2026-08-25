/-
Copyright (c) 2026 mathlib-initiative. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: mathlib-initiative
-/

import RepresentationTheory.QuantumTorus.FiniteOrderModuleEquivalences
import RepresentationTheory.ParameterizedAlgebra.ModelModules
import RepresentationTheory.Alignment.Attribute

/-! # Simple Module Classification -/

namespace RepresentationTheory.ParameterizedAlgebra.SimpleModuleClassification

open RepresentationTheory.Algebra.Module.TwistedLatticeShifts
  RepresentationTheory.ParameterizedAlgebra.FiniteSimpleModules
  RepresentationTheory.QuantumTorus.FiniteOrderModules
  RepresentationTheory.QuantumTorus.FiniteOrderModuleEquivalences
  RepresentationTheory.QuantumTorus.Representations Module

section Exhaustive

variable (q : ℂˣ)

private theorem smul_inv_of_smul {A W V : Type*} [Ring A] [AddCommGroup W] [Module A W]
    [AddCommGroup V] [Module A V] (E : W → V) (u u' : A) (huu' : u * u' = 1) (hu'u : u' * u = 1)
    (hE : ∀ f : W, E (u • f) = u • E f) (f : W) : E (u' • f) = u' • E f := by
  have h1 : u • E (u' • f) = E f := by rw [← hE (u' • f), ← mul_smul, huu', one_smul]
  have h2 : u • (u' • E f) = E f := by rw [← mul_smul, huu', one_smul]
  have h3 : u' • (u • E (u' • f)) = u' • (u • (u' • E f)) := by rw [h1, h2]
  rwa [← mul_smul, hu'u, one_smul, ← mul_smul, hu'u, one_smul] at h3

/-- A complex linear equivalence commuting with both displayed generators is an equivalence of modules. -/
theorem linearEquiv_of_commutes_with_generators
    {W V : Type*} [AddCommGroup W] [Module ℂ W]
    [Module (twistedLatticeShiftSubalgebra ℂ q) W]
    [IsScalarTower ℂ (twistedLatticeShiftSubalgebra ℂ q) W]
    [AddCommGroup V] [Module ℂ V] [Module (twistedLatticeShiftSubalgebra ℂ q) V]
    [IsScalarTower ℂ (twistedLatticeShiftSubalgebra ℂ q) V] (E : W ≃ₗ[ℂ] V)
    (hx : ∀ f : W, E (monomial q (1, 0) • f) = monomial q (1, 0) • E f)
    (hy : ∀ f : W, E (monomial q (0, 1) • f) = monomial q (0, 1) • E f) :
    Nonempty (W ≃ₗ[twistedLatticeShiftSubalgebra ℂ q] V) := by
  have hxinv : ∀ f : W,
      E (monomial q (-1, 0) • f) = monomial q (-1, 0) • E f := by
    have h1 : monomial q (1, 0) * monomial q (-1, 0) = 1 := by
      rw [monomial_mul]; norm_num [monomial_zero_zero]
    have h2 : monomial q (-1, 0) * monomial q (1, 0) = 1 := by
      rw [monomial_mul]; norm_num [monomial_zero_zero]
    exact fun f =>
      smul_inv_of_smul (A := twistedLatticeShiftSubalgebra ℂ q) (W := W) (V := V)
        E _ _ h1 h2 hx f
  have hyinv : ∀ f : W,
      E (monomial q (0, -1) • f) = monomial q (0, -1) • E f := by
    have h1 : monomial q (0, 1) * monomial q (0, -1) = 1 := by
      rw [monomial_mul]; norm_num [monomial_zero_zero]
    have h2 : monomial q (0, -1) * monomial q (0, 1) = 1 := by
      rw [monomial_mul]; norm_num [monomial_zero_zero]
    exact fun f =>
      smul_inv_of_smul (A := twistedLatticeShiftSubalgebra ℂ q) (W := W) (V := V)
        E _ _ h1 h2 hy f
  have hpre :
      (((↑) : twistedLatticeShiftSubalgebra ℂ q →
          Module.End ℂ (Auxiliary ℂ)) ⁻¹'
        {twistedLatticeShift ℂ q (1, 0), twistedLatticeShift ℂ q (-1, 0),
          twistedLatticeShift ℂ q (0, 1), twistedLatticeShift ℂ q (0, -1)}) =
      ({monomial q (1, 0), monomial q (-1, 0), monomial q (0, 1),
          monomial q (0, -1)} : Set (twistedLatticeShiftSubalgebra ℂ q)) := by
    ext a
    simp [Set.mem_preimage, Subtype.ext_iff]
  have htop : Algebra.adjoin ℂ
      ({monomial q (1, 0), monomial q (-1, 0), monomial q (0, 1),
        monomial q (0, -1)} : Set (twistedLatticeShiftSubalgebra ℂ q)) = ⊤ := by
    rw [← hpre]
    exact Algebra.adjoin_adjoin_coe_preimage
  have hall : ∀ (a : twistedLatticeShiftSubalgebra ℂ q) (f : W), E (a • f) = a • E f := by
    intro a
    have ha : a ∈ Algebra.adjoin ℂ
        ({monomial q (1, 0), monomial q (-1, 0), monomial q (0, 1),
          monomial q (0, -1)} : Set (twistedLatticeShiftSubalgebra ℂ q)) := by
      rw [htop]; exact Algebra.mem_top
    induction ha using Algebra.adjoin_induction with
    | mem g hg =>
        simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hg
        rcases hg with rfl | rfl | rfl | rfl
        · exact hx
        · exact hxinv
        · exact hy
        · exact hyinv
    | algebraMap r =>
        intro f
        rw [algebraMap_smul, algebraMap_smul, map_smul]
    | add u v _ _ ihu ihv =>
        intro f
        rw [add_smul, map_add, ihu f, ihv f, add_smul]
    | mul u v _ _ ihu ihv =>
        intro f
        rw [mul_smul, ihu, ihv, ← mul_smul]
  exact ⟨{ E with map_smul' := fun a f => hall a f }⟩

/-- A finite simple module is equivalent to a function-space model for suitable parameters. -/
theorem exists_model_equiv_finFunctions
    (V : Type*) [AddCommGroup V] [Module ℂ V]
    [Module (twistedLatticeShiftSubalgebra ℂ q) V]
    [IsScalarTower ℂ (twistedLatticeShiftSubalgebra ℂ q) V] [FiniteDimensional ℂ V]
    [IsSimpleModule (twistedLatticeShiftSubalgebra ℂ q) V]
    (N : ℕ) [NeZero N] (hqorder : orderOf q = N) :
    ∃ α β : ℂˣ, letI := finiteOrderModule q α β N hqorder
      Nonempty ((Fin N → ℂ) ≃ₗ[twistedLatticeShiftSubalgebra ℂ q] V) := by
  classical
  obtain ⟨α, β, b, hY, hX⟩ := exists_generator_eigenbasis q V N hqorder
  refine ⟨α, β, ?_⟩
  letI := finiteOrderModule q α β N hqorder
  haveI : IsScalarTower ℂ (twistedLatticeShiftSubalgebra ℂ q) (Fin N → ℂ) :=
    finiteOrderModule_isScalarTower q α β N hqorder
  obtain ⟨E, hEsingle⟩ :
      ∃ E : (Fin N → ℂ) ≃ₗ[ℂ] V, ∀ i : Fin N, E (Pi.single i (1 : ℂ)) = b i := by
    refine ⟨b.equivFun.symm, fun i => ?_⟩
    simp [Module.Basis.equivFun_symm_apply, Pi.single_apply]
  have hdecomp : ∀ f : Fin N → ℂ, f = ∑ i : Fin N, f i • Pi.single i (1 : ℂ) := by
    intro f
    funext j
    simp [Finset.sum_apply, Pi.single_apply]
  have hlin : ∀ (T : (Fin N → ℂ) →ₗ[ℂ] (Fin N → ℂ))
      (a : twistedLatticeShiftSubalgebra ℂ q),
      (∀ i : Fin N, E (T (Pi.single i (1 : ℂ))) = a • E (Pi.single i (1 : ℂ))) →
      ∀ f : Fin N → ℂ, E (T f) = a • E f := by
    intro T a h f
    have hL : E (T f) = ∑ i : Fin N, f i • E (T (Pi.single i (1 : ℂ))) := by
      conv_lhs => rw [hdecomp f]
      simp only [map_sum, map_smul]
    have hR : a • E f = ∑ i : Fin N, f i • (a • E (Pi.single i (1 : ℂ))) := by
      conv_lhs => rw [hdecomp f]
      rw [map_sum, Finset.smul_sum]
      exact Finset.sum_congr rfl fun i _ => by rw [map_smul, smul_comm]
    rw [hL, hR]
    exact Finset.sum_congr rfl fun i _ => by rw [h i]
  have hx : ∀ f : Fin N → ℂ,
      E (monomial q (1, 0) • f) = monomial q (1, 0) • E f := by
    have key := hlin (cyclicShiftEnd α N) (monomial q (1, 0)) fun i => by
      rw [cyclicShiftEnd_single, map_smul, hEsingle (i + 1), hEsingle i, hX i]
      rfl
    intro f
    rw [firstGenerator_smul q α β N hqorder f]
    exact key f
  have hy : ∀ f : Fin N → ℂ,
      E (monomial q (0, 1) • f) = monomial q (0, 1) • E f := by
    have key := hlin (diagonalWeightEnd q β N) (monomial q (0, 1)) fun i => by
      rw [diagonalWeightEnd_single, map_smul, hEsingle i, hY i]
      rfl
    intro f
    rw [secondGenerator_smul q α β N hqorder f]
    exact key f
  exact linearEquiv_of_commutes_with_generators q E hx hy

variable [NeZero (orderOf q)]

/-- A finite simple module is equivalent to one of the displayed parameterized model modules. -/
@[source_ref "Chapter2/Problem2.7.5" (role := primary)]
theorem exists_model_equiv
    (V : Type*) [AddCommGroup V] [Module ℂ V]
    [Module (twistedLatticeShiftSubalgebra ℂ q) V]
    [IsScalarTower ℂ (twistedLatticeShiftSubalgebra ℂ q) V] [FiniteDimensional ℂ V]
    [IsSimpleModule (twistedLatticeShiftSubalgebra ℂ q) V] :
    ∃ α β : ℂˣ,
      Nonempty (ThreeUnitParameterType q α β ≃ₗ[twistedLatticeShiftSubalgebra ℂ q] V) := by
  obtain ⟨α, β, he⟩ := exists_model_equiv_finFunctions q V (orderOf q) rfl
  exact ⟨α, β, he⟩

/-- The dimension of a finite simple module is the order of the parameter. -/
@[source_ref "Chapter2/Problem2.7.5" (role := primary)]
theorem finiteSimpleModule_finrank_eq_orderOf
    (V : Type*) [AddCommGroup V] [Module ℂ V]
    [Module (twistedLatticeShiftSubalgebra ℂ q) V]
    [IsScalarTower ℂ (twistedLatticeShiftSubalgebra ℂ q) V] [FiniteDimensional ℂ V]
    [IsSimpleModule (twistedLatticeShiftSubalgebra ℂ q) V] :
    Module.finrank ℂ V = orderOf q := by
  obtain ⟨α, β, ⟨e⟩⟩ := exists_model_equiv q V
  rw [← LinearEquiv.finrank_eq (e.restrictScalars ℂ), finrank_threeUnitParameterType]

/-- There are model parameters for the module, uniquely determined up to the stated power relation. -/
@[source_ref "Chapter2/Problem2.7.5" (role := supporting)]
theorem exists_model_parameters_unique
    (V : Type*) [AddCommGroup V] [Module ℂ V]
    [Module (twistedLatticeShiftSubalgebra ℂ q) V]
    [IsScalarTower ℂ (twistedLatticeShiftSubalgebra ℂ q) V] [FiniteDimensional ℂ V]
    [IsSimpleModule (twistedLatticeShiftSubalgebra ℂ q) V] :
    ∃ α β : ℂˣ,
      Nonempty (ThreeUnitParameterType q α β ≃ₗ[twistedLatticeShiftSubalgebra ℂ q] V) ∧
      ∀ α' β' : ℂˣ,
        Nonempty (ThreeUnitParameterType q α' β' ≃ₗ[twistedLatticeShiftSubalgebra ℂ q] V) ↔
          α = α' ∧ (β : ℂ) ^ orderOf q = (β' : ℂ) ^ orderOf q := by
  obtain ⟨α, β, ⟨e⟩⟩ := exists_model_equiv q V
  refine ⟨α, β, ⟨e⟩, fun α' β' => ?_⟩
  constructor
  · rintro ⟨e'⟩
    exact (nonempty_moduleLinearEquiv_iff q α β α' β').mp ⟨e.trans e'.symm⟩
  · intro h
    obtain ⟨f⟩ := (nonempty_moduleLinearEquiv_iff q α β α' β').mpr h
    exact ⟨f.symm.trans e⟩

end Exhaustive

end RepresentationTheory.ParameterizedAlgebra.SimpleModuleClassification
