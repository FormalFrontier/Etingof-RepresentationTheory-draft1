/-
Copyright (c) 2026 mathlib-initiative. All rights reserved.
Released under Apache 2.0 license as described in the file LICENCE.
Authors: mathlib-initiative
-/

import RepresentationTheory.Algebra.Module.ExtensionCocycles
import RepresentationTheory.LinearAlgebra.ModuleDecompositions
import RepresentationTheory.Alignment.Attribute
import Mathlib.Algebra.RingQuot
import Mathlib.Algebra.MvPolynomial.Derivation
import Mathlib.LinearAlgebra.Eigenspace.Triangularizable
import Mathlib.Analysis.Complex.Polynomial.Basic

/-! # Polynomial Evaluation Modules

Evaluation modules for finite-variable complex polynomial algebras and auxiliary modules for a square-zero quotient of a free algebra.
-/


namespace RepresentationTheory.Algebra.Module.PolynomialEvaluationModules

open RepresentationTheory.Algebra.Module.ExtensionCocycles (AuxiliaryData)

/-- The complex polynomial algebra with a finite family of variables. -/
@[source_ref "Chapter3/Problem3.9.2" (role := supporting)]
abbrev PolynomialAlgebra (n : ℕ) : Type := MvPolynomial (Fin n) ℂ

/-- The ideal of the polynomial algebra associated with evaluation at a tuple of complex scalars. -/
noncomputable def evaluationIdeal {n : ℕ} (a : Fin n → ℂ) : Ideal (PolynomialAlgebra n) :=
  Ideal.span (Set.range fun i => MvPolynomial.X i - MvPolynomial.C (a i))

/-- The module associated with evaluation at a tuple of complex scalars. -/
@[source_ref "Chapter3/Problem3.9.2" (role := supporting)]
abbrev EvaluationModule {n : ℕ} (a : Fin n → ℂ) : Type := PolynomialAlgebra n ⧸ evaluationIdeal a

open RepresentationTheory.Algebra.Module.ExtensionCocycles
open MvPolynomial

private lemma X_sub_C_mem_maxIdeal {n : ℕ} (a : Fin n → ℂ) (i : Fin n) :
    (X i - C (a i) : PolynomialAlgebra n) ∈ evaluationIdeal a :=
  Ideal.subset_span ⟨i, rfl⟩

private lemma sub_C_aeval_mem {n : ℕ} (a : Fin n → ℂ) (p : PolynomialAlgebra n) :
    p - C (aeval a p) ∈ evaluationIdeal a := by
  induction p using MvPolynomial.induction_on with
  | C c => rw [aeval_C]; simp
  | add p q hp hq =>
    have : (p + q) - C (aeval a (p + q))
        = (p - C (aeval a p)) + (q - C (aeval a q)) := by rw [map_add, map_add]; ring
    rw [this]; exact Ideal.add_mem _ hp hq
  | mul_X p i hp =>
    have key : p * X i - C (aeval a (p * X i))
        = p * (X i - C (a i)) + C (a i) * (p - C (aeval a p)) := by
      simp only [map_mul, aeval_X]; ring
    rw [key]
    exact Ideal.add_mem _ (Ideal.mul_mem_left _ _ (X_sub_C_mem_maxIdeal a i))
      (Ideal.mul_mem_left _ _ hp)

private lemma aeval_eq_zero_of_mem_maxIdeal {n : ℕ} (a : Fin n → ℂ) {p : PolynomialAlgebra n}
    (hp : p ∈ evaluationIdeal a) : aeval a p = 0 := by
  have hle : evaluationIdeal a ≤ RingHom.ker (aeval a : PolynomialAlgebra n →ₐ[ℂ] ℂ).toRingHom := by
    rw [evaluationIdeal, Ideal.span_le]
    rintro _ ⟨i, rfl⟩
    simp [RingHom.mem_ker]
  exact RingHom.mem_ker.mp (hle hp)

private lemma smul_quot_eq_zero {n : ℕ} (a : Fin n → ℂ) {r : PolynomialAlgebra n} (hr : r ∈ evaluationIdeal a)
    (v : EvaluationModule a) : r • v = 0 := by
  induction v using Submodule.Quotient.induction_on with
  | H p =>
    rw [show r • (Submodule.Quotient.mk p : EvaluationModule a) = Submodule.Quotient.mk (r * p) from rfl,
      Submodule.Quotient.mk_eq_zero]
    exact Ideal.mul_mem_right p _ hr

/-- Polynomial scalar multiplication on an evaluation module agrees with multiplication by the evaluated scalar. -/
@[source_ref "Chapter3/Problem3.9.2" (role := supporting)]
lemma smul_eq_aeval_smul {n : ℕ} (a : Fin n → ℂ) (q : PolynomialAlgebra n) (v : EvaluationModule a) :
    q • v = aeval a q • v := by
  rw [← algebraMap_smul (PolynomialAlgebra n) (aeval a q) v, MvPolynomial.algebraMap_eq, ← sub_eq_zero,
    ← sub_smul]
  exact smul_quot_eq_zero a (sub_C_aeval_mem a q) v

private lemma mk_eq_aeval_smul_mk_one {n : ℕ} (a : Fin n → ℂ) (p : PolynomialAlgebra n) :
    (Submodule.Quotient.mk p : EvaluationModule a) = aeval a p • Submodule.Quotient.mk 1 := by
  rw [← algebraMap_smul (PolynomialAlgebra n) (aeval a p) (Submodule.Quotient.mk (1 : PolynomialAlgebra n)),
    MvPolynomial.algebraMap_eq]
  change (Submodule.Quotient.mk p : EvaluationModule a) = Submodule.Quotient.mk (C (aeval a p) * 1)
  rw [Submodule.Quotient.eq, mul_one]
  exact sub_C_aeval_mem a p

/-- The image of one in the quotient by an evaluation ideal is nonzero. -/
lemma quotientMkOne_ne_zero {n : ℕ} (a : Fin n → ℂ) :
    (Submodule.Quotient.mk (1 : PolynomialAlgebra n) : EvaluationModule a) ≠ 0 := by
  rw [Ne, Submodule.Quotient.mk_eq_zero]
  intro h
  have := aeval_eq_zero_of_mem_maxIdeal a h
  simp at this

private noncomputable def VrepEquivC {n : ℕ} (a : Fin n → ℂ) : EvaluationModule a ≃ₗ[ℂ] ℂ := by
  refine (LinearEquiv.ofBijective
    (LinearMap.toSpanSingleton ℂ (EvaluationModule a) (Submodule.Quotient.mk 1)) ⟨?_, ?_⟩).symm
  ·
    intro c₁ c₂ h
    simp only [LinearMap.toSpanSingleton_apply] at h
    have hsub : (c₁ - c₂) • (Submodule.Quotient.mk 1 : EvaluationModule a) = 0 := by
      rw [sub_smul, h, sub_self]
    rcases smul_eq_zero.mp hsub with hc | hc
    · exact sub_eq_zero.mp hc
    · exact absurd hc (quotientMkOne_ne_zero a)
  ·
    intro v
    induction v using Submodule.Quotient.induction_on with
    | H p =>
      refine ⟨aeval a p, ?_⟩
      simp only [LinearMap.toSpanSingleton_apply]
      exact (mk_eq_aeval_smul_mk_one a p).symm

private lemma VrepEquivC_symm_apply {n : ℕ} (a : Fin n → ℂ) (c : ℂ) :
    (VrepEquivC a).symm c = c • (Submodule.Quotient.mk 1 : EvaluationModule a) := rfl

attribute [irreducible] VrepEquivC

private lemma VrepEquivC_smul_mk_one {n : ℕ} (a : Fin n → ℂ) (w : EvaluationModule a) :
    (VrepEquivC a w) • (Submodule.Quotient.mk 1 : EvaluationModule a) = w := by
  rw [← VrepEquivC_symm_apply, LinearEquiv.symm_apply_apply]

private lemma VrepEquivC_mk_one {n : ℕ} (a : Fin n → ℂ) :
    VrepEquivC a (Submodule.Quotient.mk 1) = 1 := by
  rw [← LinearEquiv.eq_symm_apply, VrepEquivC_symm_apply, one_smul]

private noncomputable def cocycleToDer {n : ℕ} (a : Fin n → ℂ)
    (f : RepresentationTheory.Algebra.Module.ExtensionCocycles.auxiliaryMapSubmodule ℂ (PolynomialAlgebra n) (EvaluationModule a) (EvaluationModule a)) : Derivation ℂ (PolynomialAlgebra n) (EvaluationModule a) where
  toFun p := f.val p (Submodule.Quotient.mk 1)
  map_add' p q := by simp
  map_smul' c p := by simp
  map_one_eq_zero' := by
    have hc := LinearMap.congr_fun (f.property 1 1) (Submodule.Quotient.mk 1 : EvaluationModule a)
    simp only [mul_one, LinearMap.add_apply, LinearMap.comp_apply, Algebra.lsmul_coe,
      one_smul] at hc
    have h2 : f.val 1 (Submodule.Quotient.mk 1) + f.val 1 (Submodule.Quotient.mk 1)
        = f.val 1 (Submodule.Quotient.mk 1) + 0 := by rw [add_zero]; exact hc.symm
    exact add_left_cancel h2
  leibniz' p q := by
    have hc := LinearMap.congr_fun (f.property p q) (Submodule.Quotient.mk 1 : EvaluationModule a)
    simp only [LinearMap.add_apply, LinearMap.comp_apply, Algebra.lsmul_coe] at hc
    change f.val (p * q) (Submodule.Quotient.mk 1)
      = p • f.val q (Submodule.Quotient.mk 1) + q • f.val p (Submodule.Quotient.mk 1)
    rw [hc, smul_eq_aeval_smul a q (Submodule.Quotient.mk 1), map_smul,
      ← smul_eq_aeval_smul a q (f.val p (Submodule.Quotient.mk 1))]

private lemma cocycleToDer_apply {n : ℕ} (a : Fin n → ℂ)
    (f : RepresentationTheory.Algebra.Module.ExtensionCocycles.auxiliaryMapSubmodule ℂ (PolynomialAlgebra n) (EvaluationModule a) (EvaluationModule a)) (p : PolynomialAlgebra n) :
    cocycleToDer a f p = f.val p (Submodule.Quotient.mk 1) := rfl

private noncomputable def derToCocycleMap {n : ℕ} (a : Fin n → ℂ)
    (D : Derivation ℂ (PolynomialAlgebra n) (EvaluationModule a)) : PolynomialAlgebra n →ₗ[ℂ] (EvaluationModule a →ₗ[ℂ] EvaluationModule a) where
  toFun p := VrepEquivC a (D p) • (LinearMap.id : EvaluationModule a →ₗ[ℂ] EvaluationModule a)
  map_add' p q := by simp only [map_add, add_smul]
  map_smul' c p := by
    have hD : D (c • p) = c • D p := D.toLinearMap.map_smul c p
    rw [hD, map_smul (VrepEquivC a), RingHom.id_apply, smul_eq_mul, mul_smul]

private lemma derToCocycleMap_apply {n : ℕ} (a : Fin n → ℂ)
    (D : Derivation ℂ (PolynomialAlgebra n) (EvaluationModule a)) (p : PolynomialAlgebra n) (w : EvaluationModule a) :
    derToCocycleMap a D p w = VrepEquivC a (D p) • w := by
  simp only [derToCocycleMap, LinearMap.coe_mk, AddHom.coe_mk, LinearMap.smul_apply,
    LinearMap.id_coe, id_eq]

private lemma end_eq_coord_smul {n : ℕ} (a : Fin n → ℂ) (g : EvaluationModule a →ₗ[ℂ] EvaluationModule a) (w : EvaluationModule a) :
    VrepEquivC a (g (Submodule.Quotient.mk 1)) • w = g w := by
  apply (VrepEquivC a).injective
  rw [map_smul, smul_eq_mul]
  conv_rhs => rw [← VrepEquivC_smul_mk_one a w, map_smul, map_smul, smul_eq_mul]
  ring

set_option maxHeartbeats 1000000 in

private lemma derToCocycle_isCocycle {n : ℕ} (a : Fin n → ℂ)
    (D : Derivation ℂ (PolynomialAlgebra n) (EvaluationModule a)) :
    RepresentationTheory.Algebra.Module.ExtensionCocycles.IsExtensionCocycle ℂ (PolynomialAlgebra n) (EvaluationModule a) (EvaluationModule a) (derToCocycleMap a D) := by
  intro p q
  refine LinearMap.ext fun w => ?_
  simp only [LinearMap.add_apply, LinearMap.comp_apply, derToCocycleMap_apply, Algebra.lsmul_coe]
  rw [Derivation.leibniz, map_add, add_smul]
  congr 1
  · rw [smul_eq_aeval_smul a p (D q), map_smul, smul_eq_mul,
      smul_eq_aeval_smul a p (VrepEquivC a (D q) • w), smul_smul]
  · rw [smul_eq_aeval_smul a q (D p), map_smul, smul_eq_mul, smul_eq_aeval_smul a q w, smul_smul, mul_comm]

set_option maxHeartbeats 1000000 in

private noncomputable def cocyclesEquivDer {n : ℕ} (a : Fin n → ℂ) :
    RepresentationTheory.Algebra.Module.ExtensionCocycles.auxiliaryMapSubmodule ℂ (PolynomialAlgebra n) (EvaluationModule a) (EvaluationModule a) ≃ₗ[ℂ] Derivation ℂ (PolynomialAlgebra n) (EvaluationModule a) where
  toFun := cocycleToDer a
  invFun D := ⟨derToCocycleMap a D, derToCocycle_isCocycle a D⟩
  map_add' f g := by
    apply Derivation.ext; intro p
    rw [cocycleToDer_apply, Derivation.add_apply, cocycleToDer_apply, cocycleToDer_apply]
    rfl
  map_smul' c f := by
    apply Derivation.ext; intro p
    rw [cocycleToDer_apply, Derivation.smul_apply, cocycleToDer_apply]
    rfl
  left_inv f := by
    apply Subtype.ext
    refine LinearMap.ext fun p => LinearMap.ext fun w => ?_
    rw [derToCocycleMap_apply, cocycleToDer_apply]
    exact end_eq_coord_smul a (f.val p) w
  right_inv D := by
    apply Derivation.ext; intro p
    change derToCocycleMap a D p (Submodule.Quotient.mk 1) = D p
    rw [derToCocycleMap_apply]
    exact VrepEquivC_smul_mk_one a (D p)

private lemma coboundaries_eq_bot {n : ℕ} (a : Fin n → ℂ) :
    RepresentationTheory.Algebra.Module.ExtensionCocycles.coboundaries ℂ (PolynomialAlgebra n) (EvaluationModule a) (EvaluationModule a) = ⊥ := by
  rw [RepresentationTheory.Algebra.Module.ExtensionCocycles.coboundaries, Submodule.span_eq_bot]
  rintro _ ⟨X, rfl⟩
  refine LinearMap.ext fun p => LinearMap.ext fun w => ?_
  simp only [coboundary_apply_apply, LinearMap.zero_apply]
  rw [smul_eq_aeval_smul a p w, map_smul X, smul_eq_aeval_smul a p (X w), sub_self]

/-- The displayed auxiliary type associated with an evaluation module is nonempty linearly equivalent to the space of complex tuples. -/
@[source_ref "Chapter3/Problem3.9.2" (role := primary)]
theorem nonempty_auxiliaryType_linearEquiv {n : ℕ} (a : Fin n → ℂ) :
    Nonempty (RepresentationTheory.Algebra.Module.ExtensionCocycles.AuxiliaryData ℂ (PolynomialAlgebra n) (EvaluationModule a) (EvaluationModule a) ≃ₗ[ℂ] (Fin n → ℂ)) := by
  have hbot : (RepresentationTheory.Algebra.Module.ExtensionCocycles.coboundaries ℂ (PolynomialAlgebra n) (EvaluationModule a) (EvaluationModule a)).submoduleOf
      (RepresentationTheory.Algebra.Module.ExtensionCocycles.auxiliaryMapSubmodule ℂ (PolynomialAlgebra n) (EvaluationModule a) (EvaluationModule a)) = ⊥ := by
    rw [coboundaries_eq_bot, Submodule.submoduleOf, Submodule.comap_bot, Submodule.ker_subtype]
  refine ⟨?_⟩
  exact (Submodule.quotEquivOfEqBot _ hbot).trans
    ((cocyclesEquivDer a).trans
      (((MvPolynomial.mkDerivationEquiv ℂ).symm).trans
        (LinearEquiv.piCongrRight (fun _ => VrepEquivC a))))

private lemma twisted_deriv_eq_zero {n : ℕ} {M : Type*} [AddCommGroup M] [Module ℂ M]
    (α β : PolynomialAlgebra n →ₐ[ℂ] ℂ) (h : PolynomialAlgebra n →ₗ[ℂ] M)
    (hL : ∀ p q, h (p * q) = β p • h q + α q • h p) (hgen : ∀ i, h (X i) = 0) : h = 0 := by
  have h1 : h 1 = 0 := by
    have hone := hL 1 1
    simp only [mul_one, map_one, one_smul] at hone
    have h2 : h 1 + h 1 = h 1 + 0 := by rw [add_zero]; exact hone.symm
    exact add_left_cancel h2
  refine LinearMap.ext fun p => ?_
  rw [LinearMap.zero_apply]
  induction p using MvPolynomial.induction_on with
  | C c =>
    rw [show (C c : PolynomialAlgebra n) = c • 1 by rw [smul_eq_C_mul, mul_one], map_smul, h1, smul_zero]
  | add p q hp hq => rw [map_add, hp, hq, add_zero]
  | mul_X p i hp => rw [hL, hgen, hp, smul_zero, smul_zero, add_zero]

/-- The displayed auxiliary type associated with two distinct evaluation points is a subsingleton. -/
@[source_ref "Chapter3/Problem3.9.2" (role := primary)]
theorem auxiliaryType_subsingleton_of_ne {n : ℕ} (a b : Fin n → ℂ) (hab : a ≠ b) :
    Subsingleton (RepresentationTheory.Algebra.Module.ExtensionCocycles.AuxiliaryData ℂ (PolynomialAlgebra n) (EvaluationModule b) (EvaluationModule a)) := by

  rw [RepresentationTheory.Algebra.Module.ExtensionCocycles.AuxiliaryData, Submodule.Quotient.subsingleton_iff, Submodule.eq_top_iff']
  intro f
  rw [Submodule.submoduleOf, Submodule.mem_comap, RepresentationTheory.Algebra.Module.ExtensionCocycles.mem_coboundaries_iff]

  set h : PolynomialAlgebra n →ₗ[ℂ] EvaluationModule b := f.val.flip (Submodule.Quotient.mk 1) with hh
  have h_apply : ∀ p, h p = f.val p (Submodule.Quotient.mk 1) := fun p => rfl
  have hL : ∀ p q, h (p * q) = aeval b p • h q + aeval a q • h p := by
    intro p q
    have hc := LinearMap.congr_fun (f.property p q) (Submodule.Quotient.mk 1 : EvaluationModule a)
    simp only [LinearMap.add_apply, LinearMap.comp_apply, Algebra.lsmul_coe] at hc
    rw [h_apply, h_apply, h_apply, hc, smul_eq_aeval_smul b p (f.val q (Submodule.Quotient.mk 1)),
      smul_eq_aeval_smul a q (Submodule.Quotient.mk 1), map_smul (f.val p)]

  have hcomm : ∀ i j, (b i - a i) • h (X j) = (b j - a j) • h (X i) := by
    intro i j
    have e1 := hL (X i) (X j)
    have e2 := hL (X j) (X i)
    rw [aeval_X, aeval_X] at e1 e2
    have heq : b i • h (X j) + a j • h (X i) = b j • h (X i) + a i • h (X j) := by
      rw [← e1, ← e2, mul_comm]
    rw [sub_smul, sub_smul, sub_eq_sub_iff_add_eq_add]; exact heq

  obtain ⟨jj, hjj⟩ : ∃ j, a j ≠ b j := by
    by_contra hcon; push Not at hcon; exact hab (funext hcon)
  have hbaj : (b jj - a jj) ≠ 0 := sub_ne_zero.mpr (Ne.symm hjj)
  set ξ : EvaluationModule b := (b jj - a jj)⁻¹ • h (X jj) with hξ

  set cbMap : PolynomialAlgebra n →ₗ[ℂ] EvaluationModule b :=
    (LinearMap.toSpanSingleton ℂ (EvaluationModule b) ξ).comp ((aeval b).toLinearMap - (aeval a).toLinearMap)
    with hcbMap
  have cb_apply : ∀ p, cbMap p = (aeval b p - aeval a p) • ξ := by
    intro p; rw [hcbMap]; simp [LinearMap.toSpanSingleton_apply]

  have he : h - cbMap = 0 := by
    refine twisted_deriv_eq_zero (aeval a) (aeval b) (h - cbMap) ?_ ?_
    · intro p q
      simp only [LinearMap.sub_apply]
      rw [hL p q, cb_apply, cb_apply, cb_apply, map_mul, map_mul]
      module
    · intro i
      simp only [LinearMap.sub_apply]
      rw [cb_apply, aeval_X, aeval_X, hξ, smul_smul, mul_comm, ← smul_smul, hcomm i jj, smul_smul,
        inv_mul_cancel₀ hbaj, one_smul, sub_self]
  have key : ∀ p, (aeval b p - aeval a p) • ξ = f.val p (Submodule.Quotient.mk 1) := by
    intro p
    have hz := LinearMap.congr_fun he p
    simp only [LinearMap.sub_apply, LinearMap.zero_apply] at hz
    rw [h_apply, cb_apply, sub_eq_zero] at hz
    exact hz.symm

  set X : EvaluationModule a →ₗ[ℂ] EvaluationModule b :=
    (LinearMap.toSpanSingleton ℂ (EvaluationModule b) ξ).comp (VrepEquivC a).toLinearMap with hX
  have X_apply : ∀ w, X w = VrepEquivC a w • ξ := by
    intro w; rw [hX]; simp [LinearMap.toSpanSingleton_apply]
  refine ⟨X, ?_⟩
  refine LinearMap.ext fun p => LinearMap.ext fun w => ?_
  conv_rhs => rw [← VrepEquivC_smul_mk_one a w, map_smul]
  rw [coboundary_apply_apply, smul_eq_aeval_smul b p (X w), smul_eq_aeval_smul a p w, map_smul X, ← sub_smul,
    X_apply, smul_comm, key p]
  rfl

/-- If every polynomial generator acts on a vector by its assigned scalar, then every polynomial acts by evaluation at those scalars. -/
lemma smul_eq_aeval_smul_of_generator_smul {n : ℕ} {M : Type*} [AddCommGroup M] [Module ℂ M]
    [Module (PolynomialAlgebra n) M] [IsScalarTower ℂ (PolynomialAlgebra n) M]
    (c : Fin n → ℂ) (m₀ : M) (hc : ∀ i, (X i : PolynomialAlgebra n) • m₀ = c i • m₀) (p : PolynomialAlgebra n) :
    p • m₀ = aeval c p • m₀ := by
  haveI : SMulCommClass (PolynomialAlgebra n) ℂ M := ⟨fun q r m => by
    rw [← algebraMap_smul (PolynomialAlgebra n) r m, ← mul_smul, ← algebraMap_smul (PolynomialAlgebra n) r (q • m),
      ← mul_smul, Algebra.commutes]⟩
  induction p using MvPolynomial.induction_on with
  | C x =>
    rw [aeval_C, ← MvPolynomial.algebraMap_eq, algebraMap_smul]
    rw [algebraMap_smul]
  | add p q hp hq => rw [add_smul, hp, hq, ← add_smul, ← map_add]
  | mul_X p i hp => rw [mul_smul, hc i, smul_comm, hp, smul_smul, map_mul, aeval_X, mul_comm]

/-- A one-dimensional module with a nonzero simultaneous generator eigenvector is linearly equivalent to the corresponding evaluation module. -/
noncomputable def linearEquivEvaluationModuleOfEigenvector {n : ℕ} {M : Type*} [AddCommGroup M] [Module ℂ M]
    [Module (PolynomialAlgebra n) M] [IsScalarTower ℂ (PolynomialAlgebra n) M] [FiniteDimensional ℂ M]
    (c : Fin n → ℂ) (m₀ : M) (hm₀ : m₀ ≠ 0) (hdim : Module.finrank ℂ M = 1)
    (hc : ∀ i, (X i : PolynomialAlgebra n) • m₀ = c i • m₀) :
    M ≃ₗ[PolynomialAlgebra n] EvaluationModule c := by
  let φ : PolynomialAlgebra n →ₗ[PolynomialAlgebra n] M := LinearMap.toSpanSingleton (PolynomialAlgebra n) M m₀
  have hφ : ∀ p, φ p = p • m₀ := fun p => rfl
  have hker : LinearMap.ker φ = evaluationIdeal c := by
    ext p
    simp only [LinearMap.mem_ker, hφ]
    rw [smul_eq_aeval_smul_of_generator_smul c m₀ hc p]
    constructor
    · intro h
      have hp0 : aeval c p = 0 := by
        rcases smul_eq_zero.mp h with h1 | h1
        · exact h1
        · exact absurd h1 hm₀
      have hmem := sub_C_aeval_mem c p
      rwa [hp0, map_zero, sub_zero] at hmem
    · intro h
      rw [aeval_eq_zero_of_mem_maxIdeal c h, zero_smul]
  have hsurj : Function.Surjective φ := by
    intro m
    obtain ⟨d, hd⟩ := (finrank_eq_one_iff_of_nonzero' m₀ hm₀).mp hdim m
    refine ⟨C d, ?_⟩
    rw [hφ, ← hd, ← MvPolynomial.algebraMap_eq, algebraMap_smul]
  exact (LinearMap.quotKerEquivOfSurjective φ hsurj).symm.trans
    (Submodule.quotEquivOfEq _ _ hker)

private lemma oneDim_common_eigen {n : ℕ} {M : Type*} [AddCommGroup M] [Module ℂ M]
    [Module (PolynomialAlgebra n) M] [IsScalarTower ℂ (PolynomialAlgebra n) M] [FiniteDimensional ℂ M]
    (hdim : Module.finrank ℂ M = 1) :
    ∃ (a : Fin n → ℂ) (m₀ : M), m₀ ≠ 0 ∧ ∀ i, (X i : PolynomialAlgebra n) • m₀ = a i • m₀ := by
  haveI : Nontrivial M := Module.nontrivial_of_finrank_pos (by rw [hdim]; norm_num)
  obtain ⟨m₀, hm₀⟩ := exists_ne (0 : M)
  have hspan := (finrank_eq_one_iff_of_nonzero' m₀ hm₀).mp hdim
  have key : ∀ i, ∃ c : ℂ, (X i : PolynomialAlgebra n) • m₀ = c • m₀ := by
    intro i
    obtain ⟨c, hc⟩ := hspan ((X i : PolynomialAlgebra n) • m₀)
    exact ⟨c, hc.symm⟩
  choose a ha using key
  exact ⟨a, m₀, hm₀, ha⟩

/-- A two-dimensional complex module over the polynomial algebra has a nonzero common eigenvector for all polynomial generators. -/
lemma exists_common_eigenvector_of_finrank_two {n : ℕ} (U : Type)
    [AddCommGroup U] [Module ℂ U] [Module (PolynomialAlgebra n) U] [IsScalarTower ℂ (PolynomialAlgebra n) U]
    [FiniteDimensional ℂ U] (hdim : Module.finrank ℂ U = 2) :
    ∃ (b : Fin n → ℂ) (v : U), v ≠ 0 ∧ ∀ i, (X i : PolynomialAlgebra n) • v = b i • v := by
  haveI : Nontrivial U := Module.nontrivial_of_finrank_pos (by rw [hdim]; norm_num)
  haveI : SMulCommClass (PolynomialAlgebra n) ℂ U := ⟨fun q r m => by
    rw [← algebraMap_smul (PolynomialAlgebra n) r m, ← mul_smul, ← algebraMap_smul (PolynomialAlgebra n) r (q • m),
      ← mul_smul, Algebra.commutes]⟩
  by_cases hall : ∀ i, ∃ c : ℂ, ∀ u : U, (X i : PolynomialAlgebra n) • u = c • u
  · choose b hb using hall
    obtain ⟨v, hv⟩ := exists_ne (0 : U)
    exact ⟨b, v, hv, fun i => hb i v⟩
  · push Not at hall
    obtain ⟨j, hj⟩ := hall
    let T : Module.End ℂ U :=
      { toFun := fun u => (X j : PolynomialAlgebra n) • u
        map_add' := fun a b => smul_add _ _ _
        map_smul' := fun r u => by
          simp only [RingHom.id_apply]
          exact smul_comm (X j : PolynomialAlgebra n) r u }
    have hTapp : ∀ u, T u = (X j : PolynomialAlgebra n) • u := fun u => rfl
    obtain ⟨μ, hμ⟩ := Module.End.exists_eigenvalue T
    obtain ⟨v₀, hv₀⟩ := hμ.exists_hasEigenvector
    rw [Module.End.hasEigenvector_iff] at hv₀
    obtain ⟨hv₀mem, hv₀ne⟩ := hv₀
    rw [Module.End.mem_eigenspace_iff, hTapp] at hv₀mem
    set E := Module.End.eigenspace T μ with hE
    have hEtop : E ≠ ⊤ := by
      intro hEq
      obtain ⟨u, hu⟩ := hj μ
      apply hu
      have hmem : u ∈ E := hEq ▸ Submodule.mem_top
      rw [hE, Module.End.mem_eigenspace_iff, hTapp] at hmem
      exact hmem
    have hv₀E : v₀ ∈ E := by rw [hE, Module.End.mem_eigenspace_iff, hTapp]; exact hv₀mem
    have hEbot : E ≠ ⊥ := by rw [Submodule.ne_bot_iff]; exact ⟨v₀, hv₀E, hv₀ne⟩
    have hlt_bot : (⊥ : Submodule ℂ U) < E := bot_lt_iff_ne_bot.mpr hEbot
    have hlt_top : E < ⊤ := lt_top_iff_ne_top.mpr hEtop
    have h0 : 0 < Module.finrank ℂ E := by
      have h := Submodule.finrank_lt_finrank_of_lt hlt_bot
      rwa [finrank_bot] at h
    have h2 : Module.finrank ℂ E < 2 := by
      have h := Submodule.finrank_lt_finrank_of_lt hlt_top
      rw [finrank_top, hdim] at h; exact h
    have hE1 : Module.finrank ℂ E = 1 := by omega
    have hv₀E' : (⟨v₀, hv₀E⟩ : E) ≠ 0 := by rw [Ne, Submodule.mk_eq_zero]; exact hv₀ne
    have hspanE := (finrank_eq_one_iff_of_nonzero' (⟨v₀, hv₀E⟩ : E) hv₀E').mp hE1
    have key : ∀ i, ∃ c : ℂ, (X i : PolynomialAlgebra n) • v₀ = c • v₀ := by
      intro i
      have hi : (X i : PolynomialAlgebra n) • v₀ ∈ E := by
        rw [hE, Module.End.mem_eigenspace_iff, hTapp, ← mul_smul, mul_comm, mul_smul, hv₀mem,
          smul_comm]
      obtain ⟨c, hc⟩ := hspanE ⟨(X i : PolynomialAlgebra n) • v₀, hi⟩
      refine ⟨c, ?_⟩
      have hval := congrArg (Subtype.val) hc
      simp only [SetLike.val_smul] at hval
      exact hval.symm
    choose b hb using key
    exact ⟨b, v₀, hv₀ne, hb⟩

/-- A two-dimensional complex module over the polynomial algebra has a submodule equivalent to one evaluation module whose quotient is equivalent to another. -/
@[source_ref "Chapter3/Problem3.9.2" (role := supporting)]
theorem exists_evaluation_submodule_and_quotient_of_finrank_two {n : ℕ} (U : Type)
    [AddCommGroup U] [Module ℂ U] [Module (PolynomialAlgebra n) U] [IsScalarTower ℂ (PolynomialAlgebra n) U]
    [FiniteDimensional ℂ U] (hdim : Module.finrank ℂ U = 2) :
    ∃ (a b : Fin n → ℂ) (S : Submodule (PolynomialAlgebra n) U),
      Nonempty (S ≃ₗ[PolynomialAlgebra n] EvaluationModule b) ∧ Nonempty ((U ⧸ S) ≃ₗ[PolynomialAlgebra n] EvaluationModule a) := by
  obtain ⟨b, v, hv, hb⟩ := exists_common_eigenvector_of_finrank_two (n := n) U hdim
  set S : Submodule (PolynomialAlgebra n) U := Submodule.span (PolynomialAlgebra n) {v} with hS
  have hvS : v ∈ S := by rw [hS]; exact Submodule.mem_span_singleton_self v

  have hSspan : S.restrictScalars ℂ = Submodule.span ℂ {v} := by
    apply le_antisymm
    · rw [SetLike.le_def]
      intro x hx
      rw [Submodule.restrictScalars_mem, hS, Submodule.mem_span_singleton] at hx
      obtain ⟨p, rfl⟩ := hx
      rw [smul_eq_aeval_smul_of_generator_smul b v hb p]
      exact Submodule.smul_mem _ _ (Submodule.mem_span_singleton_self v)
    · rw [Submodule.span_le]
      simp only [Set.singleton_subset_iff, SetLike.mem_coe, Submodule.restrictScalars_mem]
      exact hvS
  have hS'fin : Module.finrank ℂ (S.restrictScalars ℂ) = 1 := by
    rw [hSspan]; exact finrank_span_singleton hv
  have hSfin : Module.finrank ℂ ↥S = 1 := hS'fin
  haveI : FiniteDimensional ℂ ↥S :=
    inferInstanceAs (FiniteDimensional ℂ ↥(S.restrictScalars ℂ))

  have hSiso : Nonempty (↥S ≃ₗ[PolynomialAlgebra n] EvaluationModule b) := by
    refine ⟨linearEquivEvaluationModuleOfEigenvector b (⟨v, hvS⟩ : ↥S) ?_ hSfin ?_⟩
    · rw [Ne, Submodule.mk_eq_zero]; exact hv
    · intro i
      apply Subtype.ext
      change (X i : PolynomialAlgebra n) • v = b i • v
      exact hb i

  have hQfin : Module.finrank ℂ (U ⧸ S) = 1 := by
    have e := Submodule.Quotient.restrictScalarsEquiv ℂ S
    have hadd := Submodule.finrank_quotient_add_finrank (S.restrictScalars ℂ)
    rw [e.finrank_eq, hS'fin, hdim] at hadd
    omega

  obtain ⟨a, m₀, hm₀, ha⟩ := oneDim_common_eigen (n := n) (M := U ⧸ S) hQfin
  exact ⟨a, b, S, hSiso, ⟨linearEquivEvaluationModuleOfEigenvector a m₀ hm₀ hQfin ha⟩⟩

/-- An auxiliary relation on pairs of elements of a free algebra with finitely many generators. -/
inductive AuxiliaryFreeAlgebraRel (n : ℕ) : FreeAlgebra ℂ (Fin n) → FreeAlgebra ℂ (Fin n) → Prop
  | mul (i j : Fin n) :
      AuxiliaryFreeAlgebraRel n (FreeAlgebra.ι ℂ i * FreeAlgebra.ι ℂ j) 0

/-- An auxiliary algebra type indexed by a natural number. -/
@[source_ref "Chapter3/Problem3.9.2" (role := supporting)]
abbrev AuxiliaryAlgebra (n : ℕ) : Type := RingQuot (AuxiliaryFreeAlgebraRel n)

/-- A distinguished complex-valued vector indexed by a two-element finite type. -/
def finTwoDistinguishedVector : Fin 2 → ℂ := ![0, 1]

/-- An auxiliary complex-valued vector indexed by a two-element finite type. -/
def auxiliaryFinTwoVector : Fin 2 → ℂ := ![1, 0]

/-- An auxiliary endomorphism of complex vectors indexed by a two-element finite type. -/
noncomputable def finTwoCoordinateEndomorphism : Module.End ℂ (Fin 2 → ℂ) where
  toFun m := m 0 • finTwoDistinguishedVector
  map_add' a b := by simp [add_smul]
  map_smul' c m := by simp [mul_smul]

/-- The auxiliary endomorphism on two-component vectors is scalar multiplication of its distinguished vector by the zeroth coordinate. -/
@[simp] lemma finTwoCoordinateEndomorphism_apply (m : Fin 2 → ℂ) : finTwoCoordinateEndomorphism m = m 0 • finTwoDistinguishedVector := rfl

/-- The square of the auxiliary endomorphism on two-component vectors is zero. -/
lemma finTwoCoordinateEndomorphism_sq : finTwoCoordinateEndomorphism * finTwoCoordinateEndomorphism = (0 : Module.End ℂ (Fin 2 → ℂ)) := by
  ext m i
  fin_cases i <;> simp [Module.End.mul_apply, finTwoCoordinateEndomorphism_apply, finTwoDistinguishedVector]

/-- An auxiliary family of types indexed by two natural numbers. -/
def AuxiliaryModuleType (n k : ℕ) : Type := Fin 2 → ℂ

/-- The additive commutative group structure on the auxiliary module type. -/
instance auxiliaryModuleAddCommGroup (n k : ℕ) : AddCommGroup (AuxiliaryModuleType n k) := inferInstanceAs (AddCommGroup (Fin 2 → ℂ))
/-- The complex vector-space structure on the auxiliary module type. -/
noncomputable instance auxiliaryModuleComplexModule (n k : ℕ) : Module ℂ (AuxiliaryModuleType n k) := inferInstanceAs (Module ℂ (Fin 2 → ℂ))
/-- The auxiliary module type is nontrivial. -/
instance auxiliaryModuleNontrivial (n k : ℕ) : Nontrivial (AuxiliaryModuleType n k) := inferInstanceAs (Nontrivial (Fin 2 → ℂ))

/-- A distinguished nonzero vector in the auxiliary module type. -/
def distinguishedVector (n k : ℕ) : AuxiliaryModuleType n k := (finTwoDistinguishedVector : Fin 2 → ℂ)

/-- A distinguished element of the auxiliary module type. -/
def auxiliaryElement (n k : ℕ) : AuxiliaryModuleType n k := (auxiliaryFinTwoVector : Fin 2 → ℂ)

/-- The endomorphism of the auxiliary module determined by its zeroth coordinate and a distinguished vector. -/
noncomputable def coordinateEndomorphism (n k : ℕ) : Module.End ℂ (AuxiliaryModuleType n k) := finTwoCoordinateEndomorphism

/-- The auxiliary endomorphism sends a vector to its zeroth coordinate times the distinguished vector. -/
@[simp] lemma coordinateEndomorphism_apply (n k : ℕ) (m : AuxiliaryModuleType n k) : coordinateEndomorphism n k m = m 0 • distinguishedVector n k := rfl

/-- The square of the auxiliary coordinate endomorphism is zero. -/
lemma coordinateEndomorphism_sq (n k : ℕ) : coordinateEndomorphism n k * coordinateEndomorphism n k = (0 : Module.End ℂ (AuxiliaryModuleType n k)) := finTwoCoordinateEndomorphism_sq

/-- The distinguished vector in the auxiliary module is nonzero. -/
lemma distinguishedVector_ne_zero (n k : ℕ) : distinguishedVector n k ≠ (0 : AuxiliaryModuleType n k) := by
  have h : (finTwoDistinguishedVector : Fin 2 → ℂ) ≠ 0 := by
    intro h; simpa [finTwoDistinguishedVector] using congrFun h 1
  exact h

/-- A family of complex coefficient tuples indexed by a natural-number parameter. -/
def parameterCoefficients (k : ℕ) {n : ℕ} (i : Fin n) : ℂ :=
  if (i : ℕ) = 0 then 1 else if (i : ℕ) = 1 then (k : ℂ) else 0

/-- The zeroth parameter coefficient is one. -/
@[simp] lemma parameterCoefficients_zero (k : ℕ) {n : ℕ} [NeZero n] : parameterCoefficients k (0 : Fin n) = 1 := by simp [parameterCoefficients]

/-- For at least two coordinates, the first-coordinate parameter coefficient equals the natural-number parameter cast to the complex numbers. -/
lemma parameterCoefficients_one (k : ℕ) {n : ℕ} [NeZero n] (hn : 1 < n) : parameterCoefficients k (1 : Fin n) = (k : ℂ) := by
  have h1 : ((1 : Fin n) : ℕ) = 1 := by rw [Fin.val_one']; exact Nat.mod_eq_of_lt hn
  unfold parameterCoefficients
  rw [h1]
  norm_num

/-- An auxiliary family of complex-linear endomorphisms indexed by a finite type. -/
noncomputable def auxiliaryEndomorphism (n k : ℕ) (i : Fin n) : Module.End ℂ (AuxiliaryModuleType n k) := parameterCoefficients k i • coordinateEndomorphism n k

/-- The product of any two endomorphisms in the auxiliary family is zero. -/
lemma auxiliaryEndomorphism_mul (n k : ℕ) (i j : Fin n) : auxiliaryEndomorphism n k i * auxiliaryEndomorphism n k j = 0 := by
  simp only [auxiliaryEndomorphism, smul_mul_assoc, mul_smul_comm, coordinateEndomorphism_sq, smul_zero]

/-- The representation of the free algebra on the auxiliary module type. -/
noncomputable def freeAlgebraRepresentation (n k : ℕ) :
    FreeAlgebra ℂ (Fin n) →ₐ[ℂ] Module.End ℂ (AuxiliaryModuleType n k) :=
  FreeAlgebra.lift ℂ (auxiliaryEndomorphism n k)

/-- Related elements of the free algebra have equal images under the auxiliary representation. -/
lemma freeAlgebraRepresentation_eq_of_rel (n k : ℕ) : ∀ ⦃a b⦄, AuxiliaryFreeAlgebraRel n a b → freeAlgebraRepresentation n k a = freeAlgebraRepresentation n k b := by
  intro a b hab
  cases hab with
  | mul i j =>
    simp only [freeAlgebraRepresentation, map_mul, map_zero, FreeAlgebra.lift_ι_apply]
    exact auxiliaryEndomorphism_mul n k i j

/-- The representation of the auxiliary algebra on the auxiliary module type. -/
noncomputable def auxiliaryAlgebraRepresentation (n k : ℕ) : AuxiliaryAlgebra n →ₐ[ℂ] Module.End ℂ (AuxiliaryModuleType n k) :=
  RingQuot.liftAlgHom ℂ ⟨freeAlgebraRepresentation n k, freeAlgebraRepresentation_eq_of_rel n k⟩

/-- A finite family of distinguished elements of the auxiliary algebra. -/
noncomputable def distinguishedAlgebraElement (n : ℕ) (i : Fin n) : AuxiliaryAlgebra n :=
  RingQuot.mkAlgHom ℂ (AuxiliaryFreeAlgebraRel n) (FreeAlgebra.ι ℂ i)

/-- The auxiliary-algebra representation sends a distinguished indexed element to the corresponding coefficient times the coordinate endomorphism. -/
lemma auxiliaryAlgebraRepresentation_distinguishedElement (n k : ℕ) (i : Fin n) : auxiliaryAlgebraRepresentation n k (distinguishedAlgebraElement n i) = parameterCoefficients k i • coordinateEndomorphism n k := by
  simp only [auxiliaryAlgebraRepresentation, distinguishedAlgebraElement, RingQuot.liftAlgHom_mkAlgHom_apply, freeAlgebraRepresentation, FreeAlgebra.lift_ι_apply,
    auxiliaryEndomorphism]

/-- The module structure of the auxiliary algebra on the auxiliary module type. -/
noncomputable instance auxiliaryModuleAlgebraModule (n k : ℕ) : Module (AuxiliaryAlgebra n) (AuxiliaryModuleType n k) :=
  Module.compHom (AuxiliaryModuleType n k) (auxiliaryAlgebraRepresentation n k).toRingHom

/-- The auxiliary-algebra representation sends an algebra-map scalar to scalar multiplication. -/
lemma auxiliaryAlgebraRepresentation_algebraMap_apply (n k : ℕ) (c : ℂ) (y : AuxiliaryModuleType n k) :
    auxiliaryAlgebraRepresentation n k (algebraMap ℂ (AuxiliaryAlgebra n) c) y = c • y := by
  rw [AlgHom.commutes, Module.algebraMap_end_apply]

/-- When there is more than one generator, there is a natural-number-indexed family of auxiliary modules satisfying the displayed predicate and pairwise nonisomorphic over the auxiliary algebra. -/
@[source_ref "Chapter3/Problem3.9.2" (role := supporting)]
theorem exists_pairwise_nonisomorphic_auxiliaryModules {n : ℕ} (hn : 1 < n) :
    ∃ (M : ℕ → Type) (_ : ∀ k, AddCommGroup (M k)) (_ : ∀ k, Module (AuxiliaryAlgebra n) (M k)),
      (∀ k, RepresentationTheory.LinearAlgebra.ModuleDecompositions.AuxiliaryDecompositionPredicate (AuxiliaryAlgebra n) (M k)) ∧
      (∀ k l, Nonempty ((M k) ≃ₗ[AuxiliaryAlgebra n] (M l)) → k = l) := by
  haveI : NeZero n := ⟨by omega⟩
  refine ⟨fun k => AuxiliaryModuleType n k, fun _ => inferInstance, fun _ => inferInstance, ?_, ?_⟩
  ·
    intro k

    have csmul_mem : ∀ (c : ℂ) (x : AuxiliaryModuleType n k) (W : Submodule (AuxiliaryAlgebra n) (AuxiliaryModuleType n k)),
        x ∈ W → c • x ∈ W := by
      intro c x W hx
      have hc : c • x = (algebraMap ℂ (AuxiliaryAlgebra n) c) • x := (auxiliaryAlgebraRepresentation_algebraMap_apply n k c x).symm
      rw [hc]; exact W.smul_mem _ hx

    have mem_of_ne_bot : ∀ W : Submodule (AuxiliaryAlgebra n) (AuxiliaryModuleType n k), W ≠ ⊥ → distinguishedVector n k ∈ W := by
      intro W hW
      obtain ⟨w, hwW, hw0⟩ := (Submodule.ne_bot_iff W).mp hW
      by_cases h0 : w 0 = 0
      ·
        set a : ℂ := w 1 with ha
        have hwv : w = a • distinguishedVector n k := by
          funext j; fin_cases j
          · change w 0 = a • distinguishedVector n k 0
            simp [distinguishedVector, finTwoDistinguishedVector, h0]
          · change w 1 = a • distinguishedVector n k 1
            simp [distinguishedVector, finTwoDistinguishedVector, ha]
        have hw1 : a ≠ 0 := fun h1 => hw0 (by rw [hwv, h1, zero_smul])
        have hv : distinguishedVector n k = a⁻¹ • w := by
          rw [hwv, smul_smul, inv_mul_cancel₀ hw1, one_smul]
        rw [hv]; exact csmul_mem _ _ _ hwW
      ·
        have hxw : (distinguishedAlgebraElement n (0 : Fin n)) • w ∈ W := W.smul_mem _ hwW
        have hact : (distinguishedAlgebraElement n (0 : Fin n)) • w = w 0 • distinguishedVector n k := by
          change auxiliaryAlgebraRepresentation n k (distinguishedAlgebraElement n 0) w = w 0 • distinguishedVector n k
          rw [auxiliaryAlgebraRepresentation_distinguishedElement, parameterCoefficients_zero]; simp
        rw [hact] at hxw
        have hv : distinguishedVector n k = (w 0)⁻¹ • (w 0 • distinguishedVector n k) := by
          rw [smul_smul, inv_mul_cancel₀ h0, one_smul]
        rw [hv]; exact csmul_mem _ _ _ hxw
    refine ⟨inferInstance, ?_⟩
    intro W₁ W₂ hcompl
    by_contra hcon
    push Not at hcon
    obtain ⟨hW1, hW2⟩ := hcon
    have hv : distinguishedVector n k ∈ W₁ ⊓ W₂ := ⟨mem_of_ne_bot _ hW1, mem_of_ne_bot _ hW2⟩
    rw [disjoint_iff.mp hcompl.disjoint] at hv
    exact distinguishedVector_ne_zero n k ((Submodule.mem_bot _).mp hv)
  ·
    rintro k l ⟨φ⟩

    have hmap : ∀ (r : AuxiliaryAlgebra n) (x : AuxiliaryModuleType n k), φ (auxiliaryAlgebraRepresentation n k r x) = auxiliaryAlgebraRepresentation n l r (φ x) :=
      fun r x => map_smul φ r x

    have philin : ∀ (c : ℂ) (x : AuxiliaryModuleType n k), φ (c • x) = c • φ x := by
      intro c x
      have h := hmap (algebraMap ℂ (AuxiliaryAlgebra n) c) x
      rw [auxiliaryAlgebraRepresentation_algebraMap_apply, auxiliaryAlgebraRepresentation_algebraMap_apply] at h
      exact h

    have hN : ∀ x, φ (coordinateEndomorphism n k x) = coordinateEndomorphism n l (φ x) := by
      intro x
      have h := hmap (distinguishedAlgebraElement n (0 : Fin n)) x
      rw [auxiliaryAlgebraRepresentation_distinguishedElement, auxiliaryAlgebraRepresentation_distinguishedElement, parameterCoefficients_zero, parameterCoefficients_zero, LinearMap.smul_apply, LinearMap.smul_apply,
        one_smul, one_smul] at h
      exact h

    have hK : φ ((k : ℂ) • coordinateEndomorphism n k (auxiliaryElement n k)) = (l : ℂ) • coordinateEndomorphism n l (φ (auxiliaryElement n k)) := by
      have h := hmap (distinguishedAlgebraElement n (1 : Fin n)) (auxiliaryElement n k)
      rw [auxiliaryAlgebraRepresentation_distinguishedElement, auxiliaryAlgebraRepresentation_distinguishedElement, parameterCoefficients_one _ hn, parameterCoefficients_one _ hn, LinearMap.smul_apply,
        LinearMap.smul_apply] at h
      exact h
    have hNu : coordinateEndomorphism n k (auxiliaryElement n k) = distinguishedVector n k := by
      simp [coordinateEndomorphism_apply, auxiliaryElement, auxiliaryFinTwoVector]
    rw [hNu, philin] at hK
    rw [← hN (auxiliaryElement n k), hNu] at hK

    have hφv : φ (distinguishedVector n k) ≠ 0 :=
      fun h => distinguishedVector_ne_zero n k (φ.injective (by rw [map_zero]; exact h))
    have hkl : ((k : ℂ) - (l : ℂ)) • φ (distinguishedVector n k) = 0 := by rw [sub_smul, hK, sub_self]
    rcases smul_eq_zero.mp hkl with hc | hc
    · rw [sub_eq_zero] at hc; exact_mod_cast hc
    · exact absurd hc hφv

end RepresentationTheory.Algebra.Module.PolynomialEvaluationModules
