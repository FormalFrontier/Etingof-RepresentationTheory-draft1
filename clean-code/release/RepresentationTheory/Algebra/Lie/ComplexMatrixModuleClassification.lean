/-
Copyright (c) 2026 mathlib-initiative. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: mathlib-initiative
-/

import RepresentationTheory.LieAlgebra.ModuleProducts
import RepresentationTheory.LinearAlgebra.KernelDimensionProfiles

open LieModule Module

namespace RepresentationTheory.Algebra.Lie.ComplexMatrixModuleClassification

section Intertwine

variable {M N : Type*} [AddCommGroup M] [Module ℂ M] [AddCommGroup N] [Module ℂ N]

/-- Endomorphisms intertwined by a linear equivalence have kernels of equal dimension. -/
theorem finrank_ker_eq_of_intertwining_equiv (φ : M ≃ₗ[ℂ] N) (A : Module.End ℂ M) (B : Module.End ℂ N)
    (h : B ∘ₗ (φ : M →ₗ[ℂ] N) = (φ : M →ₗ[ℂ] N) ∘ₗ A) :
    Module.finrank ℂ (LinearMap.ker A) = Module.finrank ℂ (LinearMap.ker B) := by
  have hmap : Submodule.map (φ : M →ₗ[ℂ] N) (LinearMap.ker A) = LinearMap.ker B := by
    ext y
    simp only [Submodule.mem_map, LinearMap.mem_ker]
    constructor
    · rintro ⟨x, hx, rfl⟩
      have hc := LinearMap.congr_fun h x
      simp only [LinearMap.comp_apply] at hc
      rw [hc, hx, map_zero]
    · intro hy
      refine ⟨φ.symm y, ?_, by simp⟩
      have hc := LinearMap.congr_fun h (φ.symm y)
      simp only [LinearMap.comp_apply, LinearEquiv.coe_coe, LinearEquiv.apply_symm_apply] at hc
      apply φ.injective
      rw [map_zero, ← hc]
      exact hy
  rw [← hmap]
  exact (Submodule.equivMapOfInjective (φ : M →ₗ[ℂ] N) φ.injective (LinearMap.ker A)).finrank_eq

/-- A linear equivalence that intertwines two endomorphisms also intertwines every natural power of them. -/
theorem pow_intertwines_of_intertwines (φ : M ≃ₗ[ℂ] N) (A : Module.End ℂ M) (B : Module.End ℂ N)
    (h : B ∘ₗ (φ : M →ₗ[ℂ] N) = (φ : M →ₗ[ℂ] N) ∘ₗ A) (k : ℕ) :
    (B ^ k) ∘ₗ (φ : M →ₗ[ℂ] N) = (φ : M →ₗ[ℂ] N) ∘ₗ (A ^ k) := by
  induction k with
  | zero => simp [pow_zero, Module.End.one_eq_id]
  | succ k ih =>
    simp only [pow_succ, Module.End.mul_eq_comp]
    rw [LinearMap.comp_assoc, h, ← LinearMap.comp_assoc, ih, LinearMap.comp_assoc]

end Intertwine

/-- The module endomorphism obtained by applying a representation of the distinguished matrix Lie subalgebra to a fixed element. -/
noncomputable abbrev distinguishedActionEndomorphism (V : Type*) [AddCommGroup V] [Module ℂ V]
    [LieRingModule _root_.RepresentationTheory.Algebra.Lie.ComplexTwoByTwoMatrices.complexTwoByTwoMatrixLieSubalgebra V] [LieModule ℂ _root_.RepresentationTheory.Algebra.Lie.ComplexTwoByTwoMatrices.complexTwoByTwoMatrixLieSubalgebra V] : Module.End ℂ V :=
  LieModule.toEnd ℂ _root_.RepresentationTheory.Algebra.Lie.ComplexTwoByTwoMatrices.complexTwoByTwoMatrixLieSubalgebra V _root_.RepresentationTheory.LieAlgebra.Sl2Representations.raisingElement

section NullSeq

variable {V W : Type*} [AddCommGroup V] [Module ℂ V] [LieRingModule _root_.RepresentationTheory.Algebra.Lie.ComplexTwoByTwoMatrices.complexTwoByTwoMatrixLieSubalgebra V] [LieModule ℂ _root_.RepresentationTheory.Algebra.Lie.ComplexTwoByTwoMatrices.complexTwoByTwoMatrixLieSubalgebra V]
  [AddCommGroup W] [Module ℂ W] [LieRingModule _root_.RepresentationTheory.Algebra.Lie.ComplexTwoByTwoMatrices.complexTwoByTwoMatrixLieSubalgebra W] [LieModule ℂ _root_.RepresentationTheory.Algebra.Lie.ComplexTwoByTwoMatrices.complexTwoByTwoMatrixLieSubalgebra W]

/-- A Lie-module equivalence intertwines the distinguished action endomorphisms of its source and target. -/
theorem distinguishedActionEndomorphism_intertwines (φ : V ≃ₗ⁅ℂ,_root_.RepresentationTheory.Algebra.Lie.ComplexTwoByTwoMatrices.complexTwoByTwoMatrixLieSubalgebra⁆ W) :
    distinguishedActionEndomorphism W ∘ₗ (φ.toLinearEquiv : V →ₗ[ℂ] W)
      = (φ.toLinearEquiv : V →ₗ[ℂ] W) ∘ₗ distinguishedActionEndomorphism V := by
  ext v
  simp only [LinearMap.comp_apply, LinearEquiv.coe_coe, LieModuleEquiv.coe_toLinearEquiv,
    distinguishedActionEndomorphism, LieModule.toEnd_apply_apply]
  exact ((φ : V →ₗ⁅ℂ,_root_.RepresentationTheory.Algebra.Lie.ComplexTwoByTwoMatrices.complexTwoByTwoMatrixLieSubalgebra⁆ W).map_lie _root_.RepresentationTheory.LieAlgebra.Sl2Representations.raisingElement v).symm

/-- Equivalent Lie modules have equal dimensions of the kernels of every power of their distinguished action endomorphisms. -/
theorem finrank_ker_distinguishedAction_pow_eq_of_equiv (φ : V ≃ₗ⁅ℂ,_root_.RepresentationTheory.Algebra.Lie.ComplexTwoByTwoMatrices.complexTwoByTwoMatrixLieSubalgebra⁆ W) (k : ℕ) :
    Module.finrank ℂ (LinearMap.ker (distinguishedActionEndomorphism V ^ k))
      = Module.finrank ℂ (LinearMap.ker (distinguishedActionEndomorphism W ^ k)) :=
  finrank_ker_eq_of_intertwining_equiv φ.toLinearEquiv (distinguishedActionEndomorphism V ^ k) (distinguishedActionEndomorphism W ^ k)
    (pow_intertwines_of_intertwines φ.toLinearEquiv (distinguishedActionEndomorphism V) (distinguishedActionEndomorphism W) (distinguishedActionEndomorphism_intertwines φ) k)

end NullSeq

/-- On the standard finite-coordinate module, the distinguished action endomorphism is evaluation of the representation at the selected Lie element. -/
theorem distinguishedActionEndomorphism_standardModule (d : ℕ) : distinguishedActionEndomorphism (Fin d → ℂ) = _root_.RepresentationTheory.LieAlgebra.Sl2Representations.finFunctionRepresentation d _root_.RepresentationTheory.LieAlgebra.Sl2Representations.raisingElement := by
  refine LinearMap.ext fun v => ?_
  rw [distinguishedActionEndomorphism, LieModule.toEnd_apply_apply]
  rfl

/-- The kernel of the specified power of the standard endomorphism on a finite coordinate space has dimension equal to the minimum of the exponent and the space dimension. -/
theorem finrank_ker_standardEndomorphism_pow (d k : ℕ) :
    Module.finrank ℂ (LinearMap.ker (distinguishedActionEndomorphism (Fin d → ℂ) ^ k)) = min k d := by

  have hconj : _root_.RepresentationTheory.LinearAlgebra.NilpotentOperators.distinguishedElement d ∘ₗ (_root_.RepresentationTheory.LinearAlgebra.NilpotentOperators.linearEquiv_aux1 d : (Fin d → ℂ) →ₗ[ℂ] (Fin d → ℂ))
      = (_root_.RepresentationTheory.LinearAlgebra.NilpotentOperators.linearEquiv_aux1 d : (Fin d → ℂ) →ₗ[ℂ] (Fin d → ℂ)) ∘ₗ _root_.RepresentationTheory.LieAlgebra.Sl2Representations.finFunctionRepresentation d _root_.RepresentationTheory.LieAlgebra.Sl2Representations.raisingElement := by
    have hb := _root_.RepresentationTheory.LinearAlgebra.NilpotentOperators.map_apply_aux12 d
    rw [_root_.RepresentationTheory.LinearAlgebra.NilpotentOperators.map_apply_aux11, LinearEquiv.conjAlgEquiv_apply] at hb

    have hsymm : (_root_.RepresentationTheory.LinearAlgebra.NilpotentOperators.linearEquiv_aux1 d).symm.toLinearMap ∘ₗ (_root_.RepresentationTheory.LinearAlgebra.NilpotentOperators.linearEquiv_aux1 d : (Fin d → ℂ) →ₗ[ℂ] (Fin d → ℂ))
        = LinearMap.id := by ext v; simp
    rw [← hb]
    simp only [LinearMap.comp_assoc]
    rw [hsymm, LinearMap.comp_id]
  rw [distinguishedActionEndomorphism_standardModule,
    finrank_ker_eq_of_intertwining_equiv (_root_.RepresentationTheory.LinearAlgebra.NilpotentOperators.linearEquiv_aux1 d) (_root_.RepresentationTheory.LieAlgebra.Sl2Representations.finFunctionRepresentation d _root_.RepresentationTheory.LieAlgebra.Sl2Representations.raisingElement ^ k) (_root_.RepresentationTheory.LinearAlgebra.NilpotentOperators.distinguishedElement d ^ k)
      (pow_intertwines_of_intertwines (_root_.RepresentationTheory.LinearAlgebra.NilpotentOperators.linearEquiv_aux1 d) (_root_.RepresentationTheory.LieAlgebra.Sl2Representations.finFunctionRepresentation d _root_.RepresentationTheory.LieAlgebra.Sl2Representations.raisingElement) (_root_.RepresentationTheory.LinearAlgebra.NilpotentOperators.distinguishedElement d) hconj k),
    _root_.RepresentationTheory.LinearAlgebra.NilpotentOperators.finrank_ker_pow]

section Pi

variable {ι : Type*} [Fintype ι] {W : ι → Type*}
  [∀ i, AddCommGroup (W i)] [∀ i, Module ℂ (W i)]
  [∀ i, LieRingModule _root_.RepresentationTheory.Algebra.Lie.ComplexTwoByTwoMatrices.complexTwoByTwoMatrixLieSubalgebra (W i)] [∀ i, LieModule ℂ _root_.RepresentationTheory.Algebra.Lie.ComplexTwoByTwoMatrices.complexTwoByTwoMatrixLieSubalgebra (W i)]

omit [Fintype ι] in

/-- The distinguished action endomorphism on a dependent function module is the pointwise family of component endomorphisms. -/
theorem distinguishedActionEndomorphism_pi : distinguishedActionEndomorphism (∀ i, W i) = LinearMap.piMap fun i => distinguishedActionEndomorphism (W i) := by
  ext v j
  simp only [distinguishedActionEndomorphism, LieModule.toEnd_apply_apply, LinearMap.coe_piMap, Pi.map_apply,
    _root_.RepresentationTheory.LieAlgebra.ModuleProducts.bracket_pi_apply]

/-- For a finite product of finite-dimensional Lie modules, the kernel dimension of a power of the distinguished action is the sum of the component kernel dimensions. -/
theorem finrank_ker_distinguishedAction_pi_pow [∀ i, FiniteDimensional ℂ (W i)] (k : ℕ) :
    Module.finrank ℂ (LinearMap.ker (distinguishedActionEndomorphism (∀ i, W i) ^ k))
      = ∑ i, Module.finrank ℂ (LinearMap.ker (distinguishedActionEndomorphism (W i) ^ k)) := by
  rw [distinguishedActionEndomorphism_pi, _root_.RepresentationTheory.LinearAlgebra.KernelDimensionProfiles.finrank_piMap_pow_kernel]

end Pi

/-- For a finite product of standard modules, the kernel dimension of a distinguished-action power is the sum of the minima of the exponent and the component dimensions. -/
theorem finrank_ker_distinguishedAction_standardPi_pow {ι : Type*} [Fintype ι] (n : ι → ℕ) (k : ℕ) :
    Module.finrank ℂ (LinearMap.ker (distinguishedActionEndomorphism (∀ i, (Fin (n i + 1) → ℂ)) ^ k))
      = ∑ i, min k (n i + 1) := by
  rw [finrank_ker_distinguishedAction_pi_pow]
  exact Finset.sum_congr rfl fun i _ => finrank_ker_standardEndomorphism_pow (n i + 1) k

section Reindex

variable {ι κ : Type*}

/-- Equality of two natural-number parameters induces an equivalence between the corresponding standard Lie modules. -/
noncomputable def standardModuleEquivOfNatEq {a b : ℕ} (h : a = b) :
    (Fin (a + 1) → ℂ) ≃ₗ⁅ℂ,_root_.RepresentationTheory.Algebra.Lie.ComplexTwoByTwoMatrices.complexTwoByTwoMatrixLieSubalgebra⁆ (Fin (b + 1) → ℂ) := by
  subst h; exact LieModuleEquiv.refl

/-- A pointwise family of Lie-module equivalences induces an equivalence between the corresponding dependent function modules. -/
noncomputable def piLieModuleEquiv {M N : ι → Type*}
    [∀ i, AddCommGroup (M i)] [∀ i, Module ℂ (M i)]
    [∀ i, LieRingModule _root_.RepresentationTheory.Algebra.Lie.ComplexTwoByTwoMatrices.complexTwoByTwoMatrixLieSubalgebra (M i)]
    [∀ i, AddCommGroup (N i)] [∀ i, Module ℂ (N i)]
    [∀ i, LieRingModule _root_.RepresentationTheory.Algebra.Lie.ComplexTwoByTwoMatrices.complexTwoByTwoMatrixLieSubalgebra (N i)]
    (e : ∀ i, M i ≃ₗ⁅ℂ,_root_.RepresentationTheory.Algebra.Lie.ComplexTwoByTwoMatrices.complexTwoByTwoMatrixLieSubalgebra⁆ N i) : (∀ i, M i) ≃ₗ⁅ℂ,_root_.RepresentationTheory.Algebra.Lie.ComplexTwoByTwoMatrices.complexTwoByTwoMatrixLieSubalgebra⁆ (∀ i, N i) where
  toFun v i := e i (v i)
  invFun w i := (e i).symm (w i)
  map_add' u v := by funext i; simp
  map_smul' c v := by funext i; simp
  map_lie' := by
    intro x v; funext i
    exact (e i : M i →ₗ⁅ℂ,_root_.RepresentationTheory.Algebra.Lie.ComplexTwoByTwoMatrices.complexTwoByTwoMatrixLieSubalgebra⁆ N i).map_lie x (v i)
  left_inv v := by funext i; simp
  right_inv w := by funext i; simp

/-- An equivalence of index types induces a Lie-module equivalence that reindexes a dependent function module. -/
noncomputable def reindexPiLieModuleEquiv (σ : ι ≃ κ) (N : κ → Type*)
    [∀ j, AddCommGroup (N j)] [∀ j, Module ℂ (N j)]
    [∀ j, LieRingModule _root_.RepresentationTheory.Algebra.Lie.ComplexTwoByTwoMatrices.complexTwoByTwoMatrixLieSubalgebra (N j)] :
    (∀ j, N j) ≃ₗ⁅ℂ,_root_.RepresentationTheory.Algebra.Lie.ComplexTwoByTwoMatrices.complexTwoByTwoMatrixLieSubalgebra⁆ (∀ i, N (σ.symm.symm i)) :=
  { LinearEquiv.piCongrLeft' ℂ N σ.symm with
    map_lie' := by intro x v; funext i; rfl }

end Reindex

/-- Equal value multisets for functions on finite types yield an equivalence of the index types that matches the function values. -/
theorem exists_equiv_matching_values_of_valueMultiset_eq {ι κ : Type*} [Fintype ι] [Fintype κ] (f : ι → ℕ) (g : κ → ℕ)
    (h : Multiset.map f Finset.univ.val = Multiset.map g Finset.univ.val) :
    ∃ σ : ι ≃ κ, ∀ i, f i = g (σ i) := by
  classical

  have hcard : ∀ v : ℕ, Fintype.card {i // f i = v} = Fintype.card {j // g j = v} := by
    intro v
    have e := congrArg (Multiset.count v) h
    rw [Multiset.count_map, Multiset.count_map] at e
    rw [Fintype.card_subtype, Fintype.card_subtype,
      show (Finset.univ.filter fun i => f i = v)
        = (Finset.univ.filter fun i => v = f i) from
        Finset.filter_congr (by intro i _; rw [eq_comm]),
      show (Finset.univ.filter fun j => g j = v)
        = (Finset.univ.filter fun j => v = g j) from
        Finset.filter_congr (by intro j _; rw [eq_comm])]
    rw [← Finset.filter_val, ← Finset.filter_val] at e
    exact e

  let eqv : ∀ v : ℕ, {i // f i = v} ≃ {j // g j = v} := fun v => Fintype.equivOfCardEq (hcard v)
  set σ : ι ≃ κ := (Equiv.sigmaFiberEquiv f).symm.trans
    ((Equiv.sigmaCongrRight eqv).trans (Equiv.sigmaFiberEquiv g)) with hσdef
  refine ⟨σ, fun i => ?_⟩

  have hval : σ i = (eqv (f i) ⟨i, rfl⟩).1 := rfl
  rw [hval]
  exact (eqv (f i) ⟨i, rfl⟩).2.symm

/-- The multiset of values of a natural-number-valued function on a finite type. -/
def fintypeValueMultiset {ι : Type*} [Fintype ι] (n : ι → ℕ) : Multiset ℕ :=
  Multiset.map (fun i => n i + 1) Finset.univ.val

/-- The natural-number invariant associated to a finite multiset of module parameters is a sum of truncated parameter successors. -/
theorem valueMultisetInvariant_eq_sum_min {ι : Type*} [Fintype ι] (n : ι → ℕ) (k : ℕ) :
    _root_.RepresentationTheory.LinearAlgebra.KernelDimensionProfiles.auxiliaryMultisetFunction2 (fintypeValueMultiset n) k = ∑ i, min k (n i + 1) := by
  simp only [_root_.RepresentationTheory.LinearAlgebra.KernelDimensionProfiles.auxiliaryMultisetFunction2, fintypeValueMultiset, Multiset.map_map, Function.comp]
  rfl

/-- Zero does not occur in the value multiset of the specified natural-number parameter family. -/
theorem zero_not_mem_fintypeValueMultiset {ι : Type*} [Fintype ι] (n : ι → ℕ) :
    (0 : ℕ) ∉ fintypeValueMultiset n := by
  simp only [fintypeValueMultiset, Multiset.mem_map]
  rintro ⟨i, -, hi⟩
  omega

/-- Two finite-dimensional modules for the distinguished matrix Lie subalgebra are equivalent when all powers of their distinguished action endomorphisms have kernels of equal dimension. -/
theorem nonempty_equiv_of_distinguishedAction_kernelProfile_eq
    {V W : Type*} [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V]
    [LieRingModule _root_.RepresentationTheory.Algebra.Lie.ComplexTwoByTwoMatrices.complexTwoByTwoMatrixLieSubalgebra V] [LieModule ℂ _root_.RepresentationTheory.Algebra.Lie.ComplexTwoByTwoMatrices.complexTwoByTwoMatrixLieSubalgebra V]
    [AddCommGroup W] [Module ℂ W] [FiniteDimensional ℂ W]
    [LieRingModule _root_.RepresentationTheory.Algebra.Lie.ComplexTwoByTwoMatrices.complexTwoByTwoMatrixLieSubalgebra W] [LieModule ℂ _root_.RepresentationTheory.Algebra.Lie.ComplexTwoByTwoMatrices.complexTwoByTwoMatrixLieSubalgebra W]
    (h : ∀ k, Module.finrank ℂ (LinearMap.ker (distinguishedActionEndomorphism V ^ k))
      = Module.finrank ℂ (LinearMap.ker (distinguishedActionEndomorphism W ^ k))) :
    Nonempty (V ≃ₗ⁅ℂ,_root_.RepresentationTheory.Algebra.Lie.ComplexTwoByTwoMatrices.complexTwoByTwoMatrixLieSubalgebra⁆ W) := by
  obtain ⟨mV, nV, ⟨eV⟩⟩ := _root_.RepresentationTheory.LieAlgebra.ModuleProducts.nonempty_lieModuleEquiv_pi_of_finiteDimensional V
  obtain ⟨mW, nW, ⟨eW⟩⟩ := _root_.RepresentationTheory.LieAlgebra.ModuleProducts.nonempty_lieModuleEquiv_pi_of_finiteDimensional W

  have hnull : ∀ k, _root_.RepresentationTheory.LinearAlgebra.KernelDimensionProfiles.auxiliaryMultisetFunction2 (fintypeValueMultiset nV) k
      = _root_.RepresentationTheory.LinearAlgebra.KernelDimensionProfiles.auxiliaryMultisetFunction2 (fintypeValueMultiset nW) k := by
    intro k
    rw [valueMultisetInvariant_eq_sum_min, valueMultisetInvariant_eq_sum_min, ← finrank_ker_distinguishedAction_standardPi_pow, ← finrank_ker_distinguishedAction_standardPi_pow,
      ← finrank_ker_distinguishedAction_pow_eq_of_equiv eV, ← finrank_ker_distinguishedAction_pow_eq_of_equiv eW, h]

  have hmulti : fintypeValueMultiset nV = fintypeValueMultiset nW :=
    _root_.RepresentationTheory.LinearAlgebra.KernelDimensionProfiles.multiset_eq_of_auxiliaryMultisetFunction2_eq (zero_not_mem_fintypeValueMultiset nV) (zero_not_mem_fintypeValueMultiset nW) hnull

  obtain ⟨σ, hσ⟩ := exists_equiv_matching_values_of_valueMultiset_eq (fun i => nV i + 1) (fun j => nW j + 1) hmulti
  have hσ' : ∀ i, nV i = nW (σ i) := fun i => by have := hσ i; omega
  refine ⟨eV.trans (((piLieModuleEquiv fun i => standardModuleEquivOfNatEq (hσ' i)).trans
    (reindexPiLieModuleEquiv σ (fun j => (Fin (nW j + 1) → ℂ))).symm).trans eW.symm)⟩

end RepresentationTheory.Algebra.Lie.ComplexMatrixModuleClassification
