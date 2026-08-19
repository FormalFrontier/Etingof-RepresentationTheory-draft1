/-
Copyright (c) 2026 mathlib-initiative. All rights reserved.
Released under Apache 2.0 license as described in the file LICENCE.
Authors: mathlib-initiative
-/

import Mathlib.LinearAlgebra.Eigenspace.Semisimple
import RepresentationTheory.LieAlgebra.TensorProductDecomposition
import RepresentationTheory.Alignment.Attribute

/-! # Weight Ladder -/

open RepresentationTheory.Algebra.Lie.ComplexTwoByTwoMatrices
open RepresentationTheory.LieAlgebra.Sl2Representations
open RepresentationTheory.LieAlgebra.TensorProductDecomposition
open LieModule Module Polynomial
open Set

namespace RepresentationTheory.LieModule.WeightLadder

section MaximalGeneralizedWeight

variable {M : Type*} [AddCommGroup M] [Module ℂ M]
  [LieRingModule complexTwoByTwoMatrixLieSubalgebra M] [LieModule ℂ complexTwoByTwoMatrixLieSubalgebra M]

/-- The endomorphism defined by the action of the weight element. -/
private noncomputable abbrev H : Module.End ℂ M := LieModule.toEnd ℂ complexTwoByTwoMatrixLieSubalgebra M weightElement

/-- The endomorphism defined by the action of the raising element. -/
private noncomputable abbrev E : Module.End ℂ M := LieModule.toEnd ℂ complexTwoByTwoMatrixLieSubalgebra M raisingElement

/-- The raising action intertwines the weight action with its shift by two. -/
private theorem shifted_firstAction_apply (lambda : ℂ) (v : M) :
    (H (M := M) - (lambda + 2) • 1) (E (M := M) v) =
      E (M := M) ((H (M := M) - lambda • 1) v) := by
  change ⁅weightElement, ⁅raisingElement, v⁆⁆ - (lambda + 2) • ⁅raisingElement, v⁆ =
    ⁅raisingElement, ⁅weightElement, v⁆ - lambda • v⁆
  rw [leibniz_lie weightElement raisingElement v, bracket_weight_raising, nsmul_lie, lie_sub, lie_smul]
  module

/-- Iterating the shifted intertwining identity gives the corresponding power identity. -/
private theorem shifted_firstAction_pow_apply (lambda : ℂ) (k : ℕ) (v : M) :
    ((H (M := M) - (lambda + 2) • 1) ^ k) (E (M := M) v) =
      E (M := M) (((H (M := M) - lambda • 1) ^ k) v) := by
  induction k with
  | zero => simp
  | succ k ih =>
      rw [pow_succ', Module.End.mul_apply, ih, shifted_firstAction_apply]
      congr 1
      rw [← Module.End.mul_apply, ← pow_succ']

/-- Vectors in the given generalized eigenspace are annihilated by the first action when the shifted eigenvalue is absent. -/
@[source_ref "Chapter2/Problem2.15.1" (role := primary)]
theorem firstAction_eq_zero_of_no_shifted_eigenvalue (lambda : ℂ)
    (hmax : ¬ (H (M := M)).HasEigenvalue (lambda + 2))
    {v : M} (hv : v ∈ (H (M := M)).maxGenEigenspace lambda) :
    ⁅raisingElement, v⁆ = 0 := by
  rw [Module.End.mem_maxGenEigenspace] at hv
  obtain ⟨k, hk⟩ := hv
  by_contra hne
  apply hmax
  apply Module.End.hasEigenvalue_of_hasGenEigenvalue (k := k)
  intro hbot
  have hmem : ⁅raisingElement, v⁆ ∈
      (H (M := M)).genEigenspace (lambda + 2) k := by
    rw [Module.End.mem_genEigenspace_nat, LinearMap.mem_ker]
    change ((H (M := M) - (lambda + 2) • 1) ^ k) (E (M := M) v) = 0
    rw [shifted_firstAction_pow_apply (M := M), hk, map_zero]
  have : ⁅raisingElement, v⁆ ∈ (⊥ : Submodule ℂ M) := hbot ▸ hmem
  exact hne (by simpa using this)

end MaximalGeneralizedWeight

section FactorialRootPolynomial

variable {M : Type*} [AddCommGroup M] [Module ℂ M]
  [LieRingModule complexTwoByTwoMatrixLieSubalgebra M] [LieModule ℂ complexTwoByTwoMatrixLieSubalgebra M]

/-- The endomorphism obtained by iterating the displayed representation operator. -/
noncomputable def iteratedOperator (n : ℕ) (w : M) : M :=
  ((LieModule.toEnd ℂ complexTwoByTwoMatrixLieSubalgebra M raisingElement) ^ n) w

/-- The zeroth iterate is the identity on the module. -/
@[simp] theorem iteratedOperator_zero (w : M) : iteratedOperator 0 w = w := by simp [iteratedOperator]

/-- Expresses the successor iterate as one fewer iterate following the first displayed action. -/
theorem iteratedOperator_succ (n : ℕ) (w : M) :
    iteratedOperator (n + 1) w = iteratedOperator n ⁅raisingElement, w⁆ := by
  simp only [iteratedOperator, pow_succ, Module.End.mul_apply, LieModule.toEnd_apply_apply]

/-- A sequence of complex polynomials indexed by natural numbers. -/
@[source_ref "Chapter2/Problem2.15.1" (role := supporting)]
noncomputable def factorialRootPolynomial : ℕ → Polynomial ℂ
  | 0 => 1
  | k + 1 => C (k + 1 : ℂ) * factorialRootPolynomial k * (X - C (k : ℂ))

/-- The initial polynomial of the sequence is one. -/
@[simp] theorem factorialRootPolynomial_zero : factorialRootPolynomial 0 = 1 := rfl

/-- Expands the successor polynomial by its new scalar and linear factor. -/
theorem factorialRootPolynomial_succ (k : ℕ) :
    factorialRootPolynomial (k + 1) =
      C (k + 1 : ℂ) * factorialRootPolynomial k * (X - C (k : ℂ)) := rfl

/-- No polynomial in the indexed sequence is zero. -/
theorem factorialRootPolynomial_ne_zero (k : ℕ) : factorialRootPolynomial k ≠ 0 := by
  induction k with
  | zero => simp
  | succ k ih =>
      rw [factorialRootPolynomial_succ]
      exact mul_ne_zero (mul_ne_zero (C_ne_zero.mpr (by exact_mod_cast Nat.succ_ne_zero k)) ih)
        (X_sub_C_ne_zero (k : ℂ))

/-- Identifies each polynomial with a factorial scalar times its product of linear factors. -/
theorem factorialRootPolynomial_eq_factorial_mul_prod (k : ℕ) :
    factorialRootPolynomial k =
      C (k.factorial : ℂ) * ∏ i ∈ Finset.range k, (X - C (i : ℂ)) := by
  induction k with
  | zero => simp
  | succ k ih =>
      rw [factorialRootPolynomial_succ, ih, Finset.prod_range_succ, Nat.factorial_succ]
      push_cast
      simp only [map_add, map_mul, map_one]
      ring

/-- Every polynomial in the sequence is squarefree. -/
@[source_ref "Chapter2/Problem2.15.1" (role := supporting)]
theorem squarefree_factorialRootPolynomial (k : ℕ) :
    Squarefree (factorialRootPolynomial k) := by
  rw [factorialRootPolynomial_eq_factorial_mul_prod, squarefree_mul_iff]
  have hscalar : IsUnit (C (k.factorial : ℂ)) :=
    isUnit_C.mpr (isUnit_iff_ne_zero.mpr (by exact_mod_cast Nat.factorial_ne_zero k))
  refine ⟨hscalar.isRelPrime_left, hscalar.squarefree,
    Finset.squarefree_prod_of_pairwise_isCoprime ?_ ?_⟩
  · intro i hi j hj hij
    have hijc : (i : ℂ) ≠ (j : ℂ) := by exact_mod_cast hij
    exact (isCoprime_X_sub_C_of_isUnit_sub
      ((sub_ne_zero.mpr hijc).isUnit)).isRelPrime
  · intro i hi
    exact (prime_X_sub_C (i : ℂ)).squarefree

/-- The polynomial indexed by k has natural degree k. -/
@[source_ref "Chapter2/Problem2.15.1" (role := supporting)]
theorem natDegree_factorialRootPolynomial (k : ℕ) :
    (factorialRootPolynomial k).natDegree = k := by
  induction k with
  | zero => simp
  | succ k ih =>
      rw [factorialRootPolynomial_succ,
        natDegree_mul (mul_ne_zero
          (C_ne_zero.mpr (by exact_mod_cast Nat.succ_ne_zero k))
          (factorialRootPolynomial_ne_zero k))
          (X_sub_C_ne_zero (k : ℂ)),
        natDegree_mul (C_ne_zero.mpr (by exact_mod_cast Nat.succ_ne_zero k))
          (factorialRootPolynomial_ne_zero k),
        natDegree_C, ih, natDegree_X_sub_C]
      omega

/-- Describes the second action on an iterate, including its scalar correction term. -/
theorem secondAction_auxiliaryIterate (k : ℕ) (w : M) :
    ⁅weightElement, distinguishedElement_aux1 k w⁆ =
      distinguishedElement_aux1 k ⁅weightElement, w⁆ - (2 * k : ℂ) • distinguishedElement_aux1 k w := by
  induction k with
  | zero => simp
  | succ k ih =>
      rw [bracket_eq_aux5, leibniz_lie weightElement loweringElement, bracket_weight_lowering, ih,
        neg_lie, nsmul_lie, lie_sub, lie_smul]
      simp only [show ∀ u : M, ⁅loweringElement, distinguishedElement_aux1 k u⁆ = distinguishedElement_aux1 (k + 1) u from
        fun u => (bracket_eq_aux5 k u).symm]
      push_cast
      module

/-- An auxiliary iterate intertwines the weight action with its shifted action. -/
private theorem shifted_auxiliaryIterate_apply (lambda : ℂ) (n : ℕ) (w : M) :
    ((LieModule.toEnd ℂ complexTwoByTwoMatrixLieSubalgebra M weightElement - (lambda - 2 * n) • 1) (distinguishedElement_aux1 n w)) =
      distinguishedElement_aux1 n ((LieModule.toEnd ℂ complexTwoByTwoMatrixLieSubalgebra M weightElement - lambda • 1) w) := by
  simp only [LinearMap.sub_apply, LinearMap.smul_apply, Module.End.one_apply,
    LieModule.toEnd_apply_apply]
  rw [secondAction_auxiliaryIterate]
  simp only [iterate_eq_pow_action, map_sub, map_smul]
  module

/-- Iterating the auxiliary shifted intertwining identity gives the corresponding power identity. -/
private theorem shifted_auxiliaryIterate_pow_apply (lambda : ℂ) (n k : ℕ) (w : M) :
    ((LieModule.toEnd ℂ complexTwoByTwoMatrixLieSubalgebra M weightElement - (lambda - 2 * n) • 1) ^ k) (distinguishedElement_aux1 n w) =
      distinguishedElement_aux1 n (((LieModule.toEnd ℂ complexTwoByTwoMatrixLieSubalgebra M weightElement - lambda • 1) ^ k) w) := by
  induction k with
  | zero => simp
  | succ k ih =>
      rw [pow_succ', Module.End.mul_apply, ih, shifted_auxiliaryIterate_apply]
      congr 1
      rw [← Module.End.mul_apply, ← pow_succ']

/-- Tracks the generalized eigenspace containing each iterate, with eigenvalue shifted by twice the index. -/
theorem auxiliaryIterate_mem_maxGenEigenspace (lambda : ℂ) {w : M}
    (hw : w ∈ (LieModule.toEnd ℂ complexTwoByTwoMatrixLieSubalgebra M weightElement).maxGenEigenspace lambda) (n : ℕ) :
    distinguishedElement_aux1 n w ∈ (LieModule.toEnd ℂ complexTwoByTwoMatrixLieSubalgebra M weightElement).maxGenEigenspace
      (lambda - 2 * n) := by
  rw [Module.End.mem_maxGenEigenspace] at hw ⊢
  obtain ⟨k, hk⟩ := hw
  refine ⟨k, ?_⟩
  rw [shifted_auxiliaryIterate_pow_apply, hk]
  simp only [iterate_eq_pow_action, map_zero]

/-- A vector in the stated generalized eigenspace is killed by a positive iterate. -/
@[source_ref "Chapter2/Problem2.15.1" (role := primary)]
theorem exists_auxiliaryIterate_eq_zero_of_mem_maxGenEigenspace [FiniteDimensional ℂ M]
    (lambda : ℂ) {v : M}
    (hv : v ∈ (LieModule.toEnd ℂ complexTwoByTwoMatrixLieSubalgebra M weightElement).maxGenEigenspace lambda) :
    ∃ N : ℕ, 0 < N ∧ distinguishedElement_aux1 N v = 0 := by
  by_cases hv0 : v = 0
  · exact ⟨1, by omega, by simp [hv0, iterate_eq_pow_action]⟩
  by_contra htermination
  push Not at htermination
  have hnonzero : ∀ n : ℕ, distinguishedElement_aux1 n v ≠ 0 := by
    intro n
    rcases n with _ | n
    · simpa using hv0
    · exact htermination (n + 1) (by omega)
  have hweight : Function.Injective (fun n : ℕ => lambda - 2 * (n : ℂ)) := by
    intro a b hab
    have hmul : (2 : ℂ) * (a : ℂ) = 2 * (b : ℂ) :=
      neg_injective (add_left_cancel
        (show lambda + -(2 * (a : ℂ)) = lambda + -(2 * (b : ℂ)) by
          simpa only [sub_eq_add_neg] using hab))
    have hcast : (a : ℂ) = (b : ℂ) :=
      mul_left_cancel₀ (two_ne_zero (α := ℂ)) hmul
    exact_mod_cast hcast
  have hli : LinearIndependent ℂ (fun n : ℕ => distinguishedElement_aux1 n v) :=
    ((Module.End.independent_maxGenEigenspace
      (LieModule.toEnd ℂ complexTwoByTwoMatrixLieSubalgebra M weightElement)).comp hweight).linearIndependent _
      (fun n => auxiliaryIterate_mem_maxGenEigenspace lambda hv n) hnonzero
  exact Module.Finite.not_linearIndependent_of_infinite
    (fun n : ℕ => distinguishedElement_aux1 n v) hli

/-- A single auxiliary iterate annihilates every vector in the specified generalized eigenspace. -/
private theorem exists_uniform_auxiliaryIterate_eq_zero_on_maxGenEigenspace [FiniteDimensional ℂ M]
    (lambda : ℂ) :
    ∃ N : ℕ, ∀ v : M,
      v ∈ (LieModule.toEnd ℂ complexTwoByTwoMatrixLieSubalgebra M weightElement).maxGenEigenspace lambda → distinguishedElement_aux1 N v = 0 := by
  classical
  let W := (LieModule.toEnd ℂ complexTwoByTwoMatrixLieSubalgebra M weightElement).maxGenEigenspace lambda
  let b := Module.finBasis ℂ W
  choose n hnpos hnzero using fun i =>
    exists_auxiliaryIterate_eq_zero_of_mem_maxGenEigenspace (M := M) lambda
      (v := ((b i : W) : M)) (b i).property
  let N := Finset.univ.sup n
  have hnle (i : Fin (Module.finrank ℂ W)) : n i ≤ N :=
    Finset.le_sup (f := n) (Finset.mem_univ i)
  have hbzero (i : Fin (Module.finrank ℂ W)) : distinguishedElement_aux1 N ((b i : W) : M) = 0 := by
    have hni := hnle i
    rw [iterate_eq_pow_action, show N = (N - n i) + n i by omega, pow_add,
      Module.End.mul_apply,
      ← iterate_eq_pow_action (M := M) (n i) (((b i : W) : M)), hnzero i, map_zero]
  let T : W →ₗ[ℂ] M :=
    ((LieModule.toEnd ℂ complexTwoByTwoMatrixLieSubalgebra M loweringElement) ^ N).comp W.subtype
  have hT : T = 0 := by
    apply b.ext
    intro i
    change ((LieModule.toEnd ℂ complexTwoByTwoMatrixLieSubalgebra M loweringElement) ^ N) (((b i : W) : M)) = 0
    rw [← iterate_eq_pow_action]
    exact hbzero i
  refine ⟨N, fun v hv => ?_⟩
  have := LinearMap.congr_fun hT (⟨v, hv⟩ : W)
  change ((LieModule.toEnd ℂ complexTwoByTwoMatrixLieSubalgebra M loweringElement) ^ N) v = 0 at this
  rwa [← iterate_eq_pow_action] at this

/-- Expands the first action on a successor iterate into an iterate and a correction term. -/
theorem firstAction_auxiliaryIterate_succ (k : ℕ) (w : M) :
    ⁅raisingElement, distinguishedElement_aux1 (k + 1) w⁆ =
      distinguishedElement_aux1 (k + 1) ⁅raisingElement, w⁆ +
        (k + 1 : ℂ) • distinguishedElement_aux1 k (⁅weightElement, w⁆ - (k : ℂ) • w) := by
  induction k with
  | zero =>
      rw [bracket_eq_aux5, displayed_eq_aux6, leibniz_lie raisingElement loweringElement, bracket_raising_lowering]
      rw [bracket_eq_aux5, displayed_eq_aux6]
      simp
      abel
  | succ k ih =>
      rw [bracket_eq_aux5, leibniz_lie raisingElement loweringElement, bracket_raising_lowering, ih,
        lie_add, lie_smul, secondAction_auxiliaryIterate]
      simp only [show ∀ u : M, ⁅loweringElement, distinguishedElement_aux1 (k + 1) u⁆ = distinguishedElement_aux1 (k + 2) u from
        fun u => by simpa [Nat.add_assoc] using (bracket_eq_aux5 (k + 1) u).symm,
        show ∀ u : M, ⁅loweringElement, distinguishedElement_aux1 k u⁆ = distinguishedElement_aux1 (k + 1) u from
        fun u => (bracket_eq_aux5 k u).symm]
      simp only [iterate_eq_pow_action, map_sub, map_smul]
      push_cast
      module

/-- On a vector annihilated by the first displayed action, relates two iterated operators to polynomial evaluation. -/
@[source_ref "Chapter2/Problem2.15.1" (role := supporting)]
theorem polynomialAction_after_iteratedOperator (k : ℕ) (w : M)
    (hE : ⁅raisingElement, w⁆ = 0) :
    iteratedOperator k (distinguishedElement_aux1 k w) =
      Polynomial.aeval (LieModule.toEnd ℂ complexTwoByTwoMatrixLieSubalgebra M weightElement) (factorialRootPolynomial k) w := by
  induction k generalizing w with
  | zero => simp [factorialRootPolynomial, iteratedOperator]
  | succ k ih =>
      rw [iteratedOperator_succ, firstAction_auxiliaryIterate_succ, hE]
      have hfzero : distinguishedElement_aux1 (k + 1) (0 : M) = 0 := by
        rw [iterate_eq_pow_action, map_zero]
      rw [hfzero, zero_add]
      change ((LieModule.toEnd ℂ complexTwoByTwoMatrixLieSubalgebra M raisingElement) ^ k)
          ((k + 1 : ℂ) • distinguishedElement_aux1 k (⁅weightElement, w⁆ - (k : ℂ) • w)) = _
      rw [map_smul]
      change (k + 1 : ℂ) • iteratedOperator k
          (distinguishedElement_aux1 k (⁅weightElement, w⁆ - (k : ℂ) • w)) = _
      rw [ih]
      · rw [factorialRootPolynomial_succ, map_mul, map_mul, Polynomial.aeval_C]
        have heval : Polynomial.aeval (LieModule.toEnd ℂ complexTwoByTwoMatrixLieSubalgebra M weightElement)
            (X - C (k : ℂ)) =
            LieModule.toEnd ℂ complexTwoByTwoMatrixLieSubalgebra M weightElement -
              algebraMap ℂ (Module.End ℂ M) (k : ℂ) := by
          rw [map_sub, Polynomial.aeval_X, Polynomial.aeval_C]
        rw [heval]
        simp only [Module.End.mul_apply, Module.algebraMap_end_apply,
          LinearMap.sub_apply,
          map_sub, map_smul, LieModule.toEnd_apply_apply]
        module
      · rw [lie_sub, lie_smul, hE]
        have heh : ⁅raisingElement, weightElement⁆ = -(2 • raisingElement) := by
          rw [(lie_skew raisingElement weightElement).symm, bracket_weight_raising]
        have hEHw : ⁅raisingElement, ⁅weightElement, w⁆⁆ = 0 := by
          rw [leibniz_lie, heh, neg_lie, nsmul_lie, hE, lie_zero]
          simp
        simpa using hEHw

/-- Under absence of the shifted eigenvalue, the generalized eigenspace equals the ordinary eigenspace. -/
@[source_ref "Chapter2/Problem2.15.1" (role := primary)]
theorem maxGenEigenspace_eq_eigenspace_of_no_shifted_eigenvalue [FiniteDimensional ℂ M]
    (lambda : ℂ)
    (hmax : ¬ (LieModule.toEnd ℂ complexTwoByTwoMatrixLieSubalgebra M weightElement).HasEigenvalue (lambda + 2)) :
    (LieModule.toEnd ℂ complexTwoByTwoMatrixLieSubalgebra M weightElement).maxGenEigenspace lambda =
      (LieModule.toEnd ℂ complexTwoByTwoMatrixLieSubalgebra M weightElement).eigenspace lambda := by
  let H : Module.End ℂ M := LieModule.toEnd ℂ complexTwoByTwoMatrixLieSubalgebra M weightElement
  let W := H.maxGenEigenspace lambda
  let hH : MapsTo H W W := Module.End.mapsTo_maxGenEigenspace_of_comm rfl lambda
  let HW : Module.End ℂ W := LinearMap.restrict H hH
  obtain ⟨N, hN⟩ := exists_uniform_auxiliaryIterate_eq_zero_on_maxGenEigenspace (M := M) lambda
  have hP (v : M) (hv : v ∈ W) :
      Polynomial.aeval H (factorialRootPolynomial N) v = 0 := by
    have hident := polynomialAction_after_iteratedOperator (M := M) N v
      (firstAction_eq_zero_of_no_shifted_eigenvalue (M := M) lambda hmax hv)
    rw [hN v hv] at hident
    simpa [iteratedOperator] using hident.symm
  have hpow (n : ℕ) (w : W) : (((HW ^ n) w : W) : M) = (H ^ n) (w : M) := by
    induction n with
    | zero => simp
    | succ n ih =>
        rw [pow_succ', pow_succ', Module.End.mul_apply, Module.End.mul_apply]
        change H (((HW ^ n) w : W) : M) = H ((H ^ n) (w : M))
        rw [ih]
  have haeval_restrict (p : Polynomial ℂ) (w : W) :
      ((Polynomial.aeval HW p w : W) : M) = Polynomial.aeval H p (w : M) := by
    induction p using Polynomial.induction_on' with
    | add p q hp hq =>
        simp only [map_add, LinearMap.add_apply, Submodule.coe_add]
        rw [hp, hq]
    | monomial n a =>
        rw [Polynomial.aeval_monomial, Polynomial.aeval_monomial,
          Module.End.mul_apply, Module.End.mul_apply]
        change a • (((HW ^ n) w : W) : M) = a • (H ^ n) (w : M)
        rw [hpow]
  have haeval : Polynomial.aeval HW (factorialRootPolynomial N) = 0 := by
    ext w
    change ((Polynomial.aeval HW (factorialRootPolynomial N) w : W) : M) = 0
    rw [haeval_restrict]
    exact hP (w : M) w.property
  have hsemisimple : HW.IsSemisimple :=
    Module.End.isSemisimple_of_squarefree_aeval_eq_zero
      (squarefree_factorialRootPolynomial N) haeval
  have hnil : IsNilpotent (HW - algebraMap ℂ (Module.End ℂ W) lambda) := by
    let hsub : MapsTo (H - algebraMap ℂ (Module.End ℂ M) lambda) W W :=
      Module.End.mapsTo_maxGenEigenspace_of_comm
        (Algebra.mul_sub_algebraMap_commutes H lambda) lambda
    have h := Module.End.isNilpotent_restrict_maxGenEigenspace_sub_algebraMap H lambda hsub
    have heq : LinearMap.restrict (H - algebraMap ℂ (Module.End ℂ M) lambda) hsub =
        HW - algebraMap ℂ (Module.End ℂ W) lambda := by
      ext w
      rfl
    rw [← heq]
    exact h
  have hzero : HW - algebraMap ℂ (Module.End ℂ W) lambda = 0 :=
    Module.End.eq_zero_of_isNilpotent_isSemisimple hnil
      (Module.End.isSemisimple_sub_algebraMap_iff.mpr hsemisimple)
  apply le_antisymm
  · intro v hv
    rw [Module.End.mem_eigenspace_iff]
    change H v = lambda • v
    have hz := LinearMap.congr_fun hzero (⟨v, hv⟩ : W)
    have hz' : HW (⟨v, hv⟩ : W) = lambda • (⟨v, hv⟩ : W) := by
      simpa only [LinearMap.sub_apply, Module.algebraMap_end_apply,
        LinearMap.zero_apply, sub_eq_zero] using hz
    exact congrArg Subtype.val hz'
  · exact Module.End.eigenspace_le_maxGenEigenspace

/-- Determines an eigenvalue from the first vanishing iterate under the displayed eigenvector hypotheses. -/
theorem eigenvalue_eq_pred_of_minimal_iterate (lambda : ℂ) (v : M) (N : ℕ)
    (_hv : v ≠ 0) (hE : ⁅raisingElement, v⁆ = 0) (hH : ⁅weightElement, v⁆ = lambda • v)
    (hNpos : 0 < N) (hN : distinguishedElement_aux1 N v = 0)
    (hmin : ∀ m : ℕ, m < N → distinguishedElement_aux1 m v ≠ 0) :
    lambda = (N - 1 : ℕ) := by
  obtain ⟨n, rfl⟩ : ∃ n, N = n + 1 := ⟨N - 1, by omega⟩
  have hraise := raising_bracket_iterate lambda v hE hH n
  rw [hN, lie_zero] at hraise
  have hscalar : ((n : ℂ) + 1) * (lambda - n) = 0 := by
    exact (smul_eq_zero.mp hraise.symm).resolve_right (hmin n (by omega))
  have hfirst : (n : ℂ) + 1 ≠ 0 := by
    exact_mod_cast Nat.succ_ne_zero n
  have hlambda : lambda - (n : ℂ) = 0 :=
    (mul_eq_zero.mp hscalar).resolve_left hfirst
  have : lambda = (n : ℂ) := sub_eq_zero.mp hlambda
  simpa using this

/-- Determines an eigenvalue from generalized-eigenspace membership and a minimal vanishing iterate. -/
@[source_ref "Chapter2/Problem2.15.1" (role := primary)]
theorem eigenvalue_eq_pred_of_mem_maxGenEigenspace
    [FiniteDimensional ℂ M] (lambda : ℂ) (v : M) (N : ℕ)
    (hmax : ¬ (LieModule.toEnd ℂ complexTwoByTwoMatrixLieSubalgebra M weightElement).HasEigenvalue (lambda + 2))
    (hvweight : v ∈ (LieModule.toEnd ℂ complexTwoByTwoMatrixLieSubalgebra M weightElement).maxGenEigenspace lambda)
    (hv : v ≠ 0) (hNpos : 0 < N) (hN : distinguishedElement_aux1 N v = 0)
    (hmin : ∀ m : ℕ, m < N → distinguishedElement_aux1 m v ≠ 0) :
    lambda = (N - 1 : ℕ) := by
  have heigen : v ∈ (LieModule.toEnd ℂ complexTwoByTwoMatrixLieSubalgebra M weightElement).eigenspace lambda := by
    rw [← maxGenEigenspace_eq_eigenspace_of_no_shifted_eigenvalue (M := M) lambda hmax]
    exact hvweight
  exact eigenvalue_eq_pred_of_minimal_iterate lambda v N hv
    (firstAction_eq_zero_of_no_shifted_eigenvalue lambda hmax hvweight)
    (Module.End.mem_eigenspace_iff.mp heigen) hNpos hN hmin

end FactorialRootPolynomial

end RepresentationTheory.LieModule.WeightLadder
