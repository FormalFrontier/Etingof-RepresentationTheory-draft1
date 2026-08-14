/-
Copyright (c) 2026 FormalFrontier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENCE.
Authors: FormalFrontier
-/

import Mathlib
import RepresentationTheory.GeneralLinearGroup.WeightCharacter
import RepresentationTheory.AuxiliaryCharacter

set_option linter.style.longLine false

open MvPolynomial Matrix

namespace RepresentationTheory.UnitTupleActions

noncomputable section

variable (k : Type*) [Field k] [IsAlgClosed k] (N : ℕ)

/-- Associates a general linear group element to a tuple of units. -/
noncomputable def unitTupleElement (t : Fin N → kˣ) :
    Matrix.GeneralLinearGroup (Fin N) k where
  val := Matrix.diagonal (fun i => (t i : k))
  inv := Matrix.diagonal (fun i => ((t i)⁻¹ : k))
  val_inv := by
    rw [Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_one]
    congr 1; ext i; simp
  inv_val := by
    rw [Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_one]
    congr 1; ext i; simp

/-- Associates an auxiliary general linear element to a finite support and a tuple of units. -/
noncomputable def supportedUnitTupleElement (s : Finset (Fin N)) (t : Fin N → kˣ) :
    Matrix.GeneralLinearGroup (Fin N) k where
  val := Matrix.diagonal (fun i => if i ∈ s then (t i : k) else 1)
  inv := Matrix.diagonal (fun i => if i ∈ s then ((t i)⁻¹ : k) else 1)
  val_inv := by
    rw [Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_one]
    congr 1; funext i; by_cases h : i ∈ s <;> simp [h]
  inv_val := by
    rw [Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_one]
    congr 1; funext i; by_cases h : i ∈ s <;> simp [h]

omit [IsAlgClosed k] in
/-- Full support recovers the unit-tuple element. -/
theorem supportedUnitTupleElement_univ (t : Fin N → kˣ) :
    supportedUnitTupleElement k N Finset.univ t = unitTupleElement k N t := by
  apply Units.ext
  change Matrix.diagonal (fun i => if i ∈ Finset.univ then (t i : k) else 1) =
    Matrix.diagonal (fun i => (t i : k))
  simp

omit [IsAlgClosed k] in
/-- The supported unit-tuple element with empty support is the identity. -/
theorem supportedUnitTupleElement_empty (t : Fin N → kˣ) :
    supportedUnitTupleElement k N ∅ t = 1 := by
  apply Units.ext
  change Matrix.diagonal (fun i => if i ∈ (∅ : Finset (Fin N)) then (t i : k) else 1) =
    (1 : Matrix (Fin N) (Fin N) k)
  simp

omit [IsAlgClosed k] in
/-- Adding a fresh index factors the supported unit-tuple element by the associated auxiliary coordinate element. -/
theorem supportedUnitTupleElement_insert (a : Fin N) (s : Finset (Fin N)) (t : Fin N → kˣ)
    (ha : a ∉ s) :
    supportedUnitTupleElement k N (insert a s) t = RepresentationTheory.GeneralLinearGroup.WeightCharacter.diagonalUnit k N a (t a) * supportedUnitTupleElement k N s t := by
  apply Units.ext
  rw [Units.val_mul]
  change Matrix.diagonal (fun i => if i ∈ insert a s then (t i : k) else 1) =
    Matrix.diagonal (Function.update (1 : Fin N → k) a ((t a : k))) *
      Matrix.diagonal (fun i => if i ∈ s then (t i : k) else 1)
  rw [Matrix.diagonal_mul_diagonal]
  congr 1; funext i
  by_cases hia : i = a
  · subst hia; simp [Finset.mem_insert, ha, Function.update_self]
  · simp [Finset.mem_insert, hia]

variable {k N}

/-- The auxiliary coordinate element acts on an auxiliary weight vector by the corresponding coordinate power. -/
theorem auxiliaryCoordinateElement_smul_of_mem_auxiliaryWeightSpace
    (M : FDRep k (Matrix.GeneralLinearGroup (Fin N) k))
    (μ : Fin N → ℕ) (i : Fin N) (s : kˣ)
    {v : M} (hv : v ∈ RepresentationTheory.GeneralLinearGroup.WeightCharacter.weightSpace k N M μ) :
    M.ρ (RepresentationTheory.GeneralLinearGroup.WeightCharacter.diagonalUnit k N i s) v = (s : k) ^ μ i • v := by
  have h1 : RepresentationTheory.GeneralLinearGroup.WeightCharacter.weightSpace k N M μ ≤ ⨅ (u : kˣ),
      LinearMap.ker (M.ρ (RepresentationTheory.GeneralLinearGroup.WeightCharacter.diagonalUnit k N i u) - ((u : k) ^ μ i) • LinearMap.id) :=
    iInf_le _ i
  have h2 : (⨅ (u : kˣ),
      LinearMap.ker (M.ρ (RepresentationTheory.GeneralLinearGroup.WeightCharacter.diagonalUnit k N i u) - ((u : k) ^ μ i) • LinearMap.id)) ≤
      LinearMap.ker (M.ρ (RepresentationTheory.GeneralLinearGroup.WeightCharacter.diagonalUnit k N i s) - ((s : k) ^ μ i) • LinearMap.id) :=
    iInf_le _ s
  have hker := LinearMap.mem_ker.mp (h2 (h1 hv))
  rwa [LinearMap.sub_apply, LinearMap.smul_apply, LinearMap.id_apply, sub_eq_zero] at hker

/-- On a vector in an auxiliary weight space, a supported unit-tuple element acts by the indicated finite product of powers. -/
theorem supportedUnitTupleElement_smul_of_mem_auxiliaryWeightSpace
    (M : FDRep k (Matrix.GeneralLinearGroup (Fin N) k))
    (μ : Fin N → ℕ) (t : Fin N → kˣ) (s : Finset (Fin N))
    {v : M} (hv : v ∈ RepresentationTheory.GeneralLinearGroup.WeightCharacter.weightSpace k N M μ) :
    M.ρ (supportedUnitTupleElement k N s t) v = (∏ i ∈ s, (t i : k) ^ μ i) • v := by
  induction s using Finset.induction with
  | empty => rw [supportedUnitTupleElement_empty, map_one]; simp
  | insert a s ha ih =>
    rw [supportedUnitTupleElement_insert k N a s t ha, map_mul, Module.End.mul_apply, ih, map_smul,
      auxiliaryCoordinateElement_smul_of_mem_auxiliaryWeightSpace M μ a (t a) hv, Finset.prod_insert ha, smul_smul,
      mul_comm ((t a : k) ^ μ a) (∏ i ∈ s, (t i : k) ^ μ i)]

/-- On an auxiliary weight vector, the unit-tuple element acts through the full product of the indexed powers. -/
theorem unitTupleElement_smul_of_mem_auxiliaryWeightSpace
    (M : FDRep k (Matrix.GeneralLinearGroup (Fin N) k))
    (μ : Fin N → ℕ) (t : Fin N → kˣ)
    {v : M} (hv : v ∈ RepresentationTheory.GeneralLinearGroup.WeightCharacter.weightSpace k N M μ) :
    M.ρ (unitTupleElement k N t) v = (∏ i, (t i : k) ^ μ i) • v := by
  rw [← supportedUnitTupleElement_univ k N t]
  exact supportedUnitTupleElement_smul_of_mem_auxiliaryWeightSpace M μ t Finset.univ hv

variable (k N)
variable [CharZero k]

/-- Evaluating the auxiliary polynomial on unit values gives the trace of the corresponding unit-tuple action. -/
theorem auxiliaryPolynomial_eval_eq_trace_unitTupleAction
    (M : FDRep k (Matrix.GeneralLinearGroup (Fin N) k))
    (h_top : ⨆ (μ : Fin N →₀ ℕ), RepresentationTheory.GeneralLinearGroup.WeightCharacter.weightSpace k N M (fun i => μ i) = ⊤)
    (t : Fin N → kˣ) :
    MvPolynomial.aeval (fun i => (t i : k)) (RepresentationTheory.GeneralLinearGroup.WeightCharacter.weightCharacter k N M) =
      LinearMap.trace k M (M.ρ (unitTupleElement k N t)) := by
  have h_indep : iSupIndep (fun μ : Fin N →₀ ℕ => RepresentationTheory.GeneralLinearGroup.WeightCharacter.weightSpace k N M (fun i => μ i)) :=
    RepresentationTheory.AuxiliaryCharacter.iSupIndep_auxiliaryWeightSpace k N M
  have hfin : {μ : Fin N →₀ ℕ | RepresentationTheory.GeneralLinearGroup.WeightCharacter.weightSpace k N M (fun i => μ i) ≠ ⊥}.Finite :=
    RepresentationTheory.GeneralLinearGroup.WeightCharacter.finite_support_weightSpace k N M
  have h_internal :
      DirectSum.IsInternal (fun μ : Fin N →₀ ℕ => RepresentationTheory.GeneralLinearGroup.WeightCharacter.weightSpace k N M (fun i => μ i)) :=
    (DirectSum.isInternal_submodule_iff_iSupIndep_and_iSup_eq_top _).mpr ⟨h_indep, h_top⟩
  have hmaps : ∀ μ : Fin N →₀ ℕ,
      Set.MapsTo (M.ρ (unitTupleElement k N t)) (RepresentationTheory.GeneralLinearGroup.WeightCharacter.weightSpace k N M (fun i => μ i))
        (RepresentationTheory.GeneralLinearGroup.WeightCharacter.weightSpace k N M (fun i => μ i)) := by
    intro μ v hv
    rw [unitTupleElement_smul_of_mem_auxiliaryWeightSpace M (fun i => μ i) t hv]
    exact Submodule.smul_mem _ _ hv
  rw [LinearMap.trace_eq_sum_trace_restrict' h_internal hfin hmaps]
  have hsummand : ∀ μ ∈ hfin.toFinset,
      LinearMap.trace k _ ((M.ρ (unitTupleElement k N t)).restrict (hmaps μ)) =
        (Module.finrank k (RepresentationTheory.GeneralLinearGroup.WeightCharacter.weightSpace k N M (fun i => μ i)) : k) *
          ∏ i, (t i : k) ^ (μ i) := by
    intro μ _
    have hrestrict : (M.ρ (unitTupleElement k N t)).restrict (hmaps μ) =
        (∏ i, (t i : k) ^ (μ i)) • LinearMap.id := by
      ext ⟨w, hw⟩
      simp only [LinearMap.coe_restrict_apply, LinearMap.smul_apply, LinearMap.id_coe, id_eq,
        SetLike.val_smul]
      exact unitTupleElement_smul_of_mem_auxiliaryWeightSpace M (fun i => μ i) t hw
    rw [hrestrict, map_smul, LinearMap.trace_id, smul_eq_mul, mul_comm]
  rw [Finset.sum_congr rfl hsummand]
  unfold RepresentationTheory.GeneralLinearGroup.WeightCharacter.weightCharacter
  rw [map_sum]
  refine Finset.sum_congr rfl (fun μ _ => ?_)
  rw [map_smul, MvPolynomial.aeval_monomial, map_one, one_mul,
    Finsupp.prod_fintype _ _ (fun i => pow_zero _), Algebra.smul_def, map_natCast]

/-- A rational relation among the displayed auxiliary polynomials yields a vanishing weighted sum of unit-tuple action traces. -/
theorem sum_trace_unitTupleAction_eq_zero_of_auxiliaryPolynomialRelation
    {ι : Type*} (s : Finset ι) (c : ι → ℚ)
    (L : ι → FDRep k (Matrix.GeneralLinearGroup (Fin N) k))
    (h_top : ∀ i ∈ s, ⨆ (μ : Fin N →₀ ℕ), RepresentationTheory.GeneralLinearGroup.WeightCharacter.weightSpace k N (L i) (fun j => μ j) = ⊤)
    (h_char : ∑ i ∈ s, c i • RepresentationTheory.GeneralLinearGroup.WeightCharacter.weightCharacter k N (L i) = 0)
    (t : Fin N → kˣ) :
    ∑ i ∈ s, (c i : k) • LinearMap.trace k (L i) ((L i).ρ (unitTupleElement k N t)) = 0 := by
  have key : ∑ i ∈ s, (c i : k) • LinearMap.trace k (L i) ((L i).ρ (unitTupleElement k N t)) =
      MvPolynomial.aeval (fun j => (t j : k))
        (∑ i ∈ s, c i • RepresentationTheory.GeneralLinearGroup.WeightCharacter.weightCharacter k N (L i)) := by
    rw [map_sum]
    refine Finset.sum_congr rfl (fun i hi => ?_)
    rw [map_smul, auxiliaryPolynomial_eval_eq_trace_unitTupleAction k N (L i) (h_top i hi) t, Rat.smul_def,
      Algebra.smul_def, map_ratCast]
  rw [key, h_char, map_zero]

end

end RepresentationTheory.UnitTupleActions
