/-
Copyright (c) 2026 mathlib-initiative. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: mathlib-initiative
-/

import Mathlib
import RepresentationTheory.FiniteFieldMatrixCharacterValues

namespace RepresentationTheory.GaloisFieldAuxiliary










variable (p : ℕ) [hp : Fact (Nat.Prime p)] (n : ℕ)

private abbrev GL2 := Matrix.GeneralLinearGroup (Fin 2) (GaloisField p n)

open scoped Matrix



/-- An auxiliary element depending on a prime and a natural parameter. -/
noncomputable def auxiliaryElement : GL2 p n := by
  by_cases hn : n = 0
  · exact 1
  · letI := RepresentationTheory.FiniteFieldMatrixCharacterValues.quadraticFiniteFieldAlgebra p n
    letI := RepresentationTheory.FiniteFieldMatrixCharacterValues.primeField_finiteField_quadraticExtension_isScalarTower p n
    haveI := RepresentationTheory.FiniteFieldMatrixCharacterValues.quadraticFiniteField_finiteDimensional p n
    haveI : Fintype (GaloisField p n) := Fintype.ofFinite _
    haveI : Fintype (GaloisField p (2 * n)) := Fintype.ofFinite _
    haveI : Algebra.IsAlgebraic (GaloisField p n) (GaloisField p (2 * n)) :=
      Algebra.IsAlgebraic.of_finite _ _
    let b := Module.finBasisOfFinrankEq (R := GaloisField p n)
      (M := GaloisField p (2 * n)) (RepresentationTheory.FiniteFieldMatrixCharacterValues.quadraticFiniteField_finrank p n hn)
    let σ := (FiniteField.frobeniusAlgEquivOfAlgebraic
      (GaloisField p n) (GaloisField p (2 * n))).toLinearEquiv
    let M := LinearMap.toMatrix b b σ.toLinearMap
    let M_inv := LinearMap.toMatrix b b σ.symm.toLinearMap
    refine ⟨M, M_inv, ?_, ?_⟩
    · 
      rw [← LinearMap.toMatrix_mul, show σ.toLinearMap * σ.symm.toLinearMap = LinearMap.id from by
        ext x; simp, LinearMap.toMatrix_id]
    · 
      rw [← LinearMap.toMatrix_mul, show σ.symm.toLinearMap * σ.toLinearMap = LinearMap.id from by
        ext x; simp, LinearMap.toMatrix_id]


/-- The square of the auxiliary element is one. -/
lemma auxiliaryElement_sq_eq_one (hn : n ≠ 0) :
    auxiliaryElement p n ^ 2 = 1 := by
  letI := RepresentationTheory.FiniteFieldMatrixCharacterValues.quadraticFiniteFieldAlgebra p n
  letI := RepresentationTheory.FiniteFieldMatrixCharacterValues.primeField_finiteField_quadraticExtension_isScalarTower p n
  haveI := RepresentationTheory.FiniteFieldMatrixCharacterValues.quadraticFiniteField_finiteDimensional p n
  haveI : Fintype (GaloisField p n) := Fintype.ofFinite _
  haveI : Fintype (GaloisField p (2 * n)) := Fintype.ofFinite _
  haveI : Algebra.IsAlgebraic (GaloisField p n) (GaloisField p (2 * n)) :=
    Algebra.IsAlgebraic.of_finite _ _
  let b := Module.finBasisOfFinrankEq (R := GaloisField p n)
    (M := GaloisField p (2 * n)) (RepresentationTheory.FiniteFieldMatrixCharacterValues.quadraticFiniteField_finrank p n hn)
  let σ := (FiniteField.frobeniusAlgEquivOfAlgebraic
    (GaloisField p n) (GaloisField p (2 * n))).toLinearEquiv
  rw [sq]
  apply Units.ext
  
  have hval : (auxiliaryElement p n).val =
      LinearMap.toMatrix b b σ.toLinearMap := by
    simp only [auxiliaryElement, dif_neg hn]
    congr; exact Subsingleton.elim _ _
  simp only [Units.val_mul, Units.val_one, hval, ← LinearMap.toMatrix_mul]
  have hσ2 : σ.toLinearMap * σ.toLinearMap = LinearMap.id := by
    ext x
    change σ (σ x) = x
    
    let σ_alg := FiniteField.frobeniusAlgEquivOfAlgebraic
      (GaloisField p n) (GaloisField p (2 * n))
    change σ_alg (σ_alg x) = x
    rw [FiniteField.coe_frobeniusAlgEquivOfAlgebraic]
    
    simp only [← pow_mul]
    
    have hcard : Fintype.card (GaloisField p n) * Fintype.card (GaloisField p n) =
        Fintype.card (GaloisField p (2 * n)) := by
      simp only [Fintype.card_eq_nat_card]
      have h1 := @GaloisField.card p _ n hn
      have h2 := @GaloisField.card p _ (2 * n) (by omega : 2 * n ≠ 0)
      rw [h1, h2]
      ring
    rw [hcard]
    exact FiniteField.pow_card x
  rw [hσ2, LinearMap.toMatrix_id]


/-- The inverse of the auxiliary element equals itself. -/
lemma auxiliaryElement_inv_eq (hn : n ≠ 0) :
    (auxiliaryElement p n)⁻¹ = auxiliaryElement p n := by
  have h2 := auxiliaryElement_sq_eq_one p n hn
  rw [sq] at h2
  exact inv_eq_of_mul_eq_one_left h2


/-- Conjugating the displayed function value at α by the auxiliary element gives the function value at the unit constructed using the cardinality power. -/
lemma conjugate_auxiliaryFunctionValue_eq_auxiliaryFunctionValue_cardPowerUnit [Fintype (GaloisField p n)] (hn : n ≠ 0)
    (α : (GaloisField p (2 * n))ˣ) :
    (auxiliaryElement p n)⁻¹ *
    RepresentationTheory.FiniteFieldMatrixCharacterValues.quadraticFieldUnitsToMatrixUnits p n α *
    auxiliaryElement p n =
    RepresentationTheory.FiniteFieldMatrixCharacterValues.quadraticFieldUnitsToMatrixUnits p n
      ⟨(α : GaloisField p (2 * n)) ^ Fintype.card (GaloisField p n),
       (α⁻¹ : GaloisField p (2 * n)) ^ Fintype.card (GaloisField p n),
       by rw [← mul_pow]; simp ,
       by rw [← mul_pow]; simp ⟩ := by
  letI := RepresentationTheory.FiniteFieldMatrixCharacterValues.quadraticFiniteFieldAlgebra p n
  letI := RepresentationTheory.FiniteFieldMatrixCharacterValues.primeField_finiteField_quadraticExtension_isScalarTower p n
  haveI := RepresentationTheory.FiniteFieldMatrixCharacterValues.quadraticFiniteField_finiteDimensional p n
  
  haveI : Fintype (GaloisField p (2 * n)) := Fintype.ofFinite _
  haveI : Algebra.IsAlgebraic (GaloisField p n) (GaloisField p (2 * n)) :=
    Algebra.IsAlgebraic.of_finite _ _
  let b := Module.finBasisOfFinrankEq (R := GaloisField p n)
    (M := GaloisField p (2 * n)) (RepresentationTheory.FiniteFieldMatrixCharacterValues.quadraticFiniteField_finrank p n hn)
  let σ_alg := FiniteField.frobeniusAlgEquivOfAlgebraic
    (GaloisField p n) (GaloisField p (2 * n))
  let σ := σ_alg.toLinearEquiv
  rw [auxiliaryElement_inv_eq p n hn]
  apply Units.ext
  have hfrob : (auxiliaryElement p n).val =
      LinearMap.toMatrix b b σ.toLinearMap := by
    simp only [auxiliaryElement, dif_neg hn]
    congr; exact Subsingleton.elim _ _
  have hembed : ∀ (β : (GaloisField p (2 * n))ˣ),
      (RepresentationTheory.FiniteFieldMatrixCharacterValues.quadraticFieldUnitsToMatrixUnits p n β).val =
      Algebra.leftMulMatrix b (β : GaloisField p (2 * n)) := by
    intro β
    simp only [RepresentationTheory.FiniteFieldMatrixCharacterValues.quadraticFieldUnitsToMatrixUnits, dif_neg hn]
    congr 1
  simp only [Units.val_mul, hfrob, hembed, Algebra.leftMulMatrix_apply,
    ← LinearMap.toMatrix_mul]
  congr 1
  ext x
  
  
  change σ ((Algebra.lmul (GaloisField p n) (GaloisField p (2 * n)) (↑α)) (σ x)) =
    (Algebra.lmul (GaloisField p n) (GaloisField p (2 * n))
      ((↑α : GaloisField p (2 * n)) ^ Fintype.card (GaloisField p n))) x
  
  change σ ((↑α : GaloisField p (2 * n)) * σ x) =
    (↑α : GaloisField p (2 * n)) ^ Fintype.card (GaloisField p n) * x
  
  change σ_alg ((↑α : GaloisField p (2 * n)) * σ_alg x) =
    (↑α : GaloisField p (2 * n)) ^ Fintype.card (GaloisField p n) * x
  rw [map_mul]
  
  have hσσ : ∀ y, σ_alg (σ_alg y) = y := by
    intro y
    rw [show (σ_alg : GaloisField p (2 * n) → GaloisField p (2 * n)) = (· ^ Fintype.card (GaloisField p n)) from
      FiniteField.coe_frobeniusAlgEquivOfAlgebraic (GaloisField p n) (GaloisField p (2 * n))]
    simp only [← pow_mul]
    have hcard : Fintype.card (GaloisField p n) * Fintype.card (GaloisField p n) =
        Fintype.card (GaloisField p (2 * n)) := by
      simp only [Fintype.card_eq_nat_card]
      rw [@GaloisField.card p _ n hn, @GaloisField.card p _ (2 * n) (by omega : 2 * n ≠ 0)]
      ring
    rw [hcard]; exact FiniteField.pow_card y
  rw [hσσ, show (σ_alg (↑α : GaloisField p (2 * n))) =
    (↑α : GaloisField p (2 * n)) ^ Fintype.card (GaloisField p n) from
    congrFun (FiniteField.coe_frobeniusAlgEquivOfAlgebraic
      (GaloisField p n) (GaloisField p (2 * n))) ↑α]


/-- Auxiliary-set membership is preserved by conjugation with the auxiliary element. -/
lemma mem_auxiliarySet_conjugate_by_auxiliaryElement [Fintype (GaloisField p n)] (hn : n ≠ 0)
    (k : GL2 p n) (hk : k ∈ RepresentationTheory.FiniteFieldMatrixCharacterValues.distinguishedMatrixSubgroup p n) :
    (auxiliaryElement p n)⁻¹ * k * auxiliaryElement p n ∈
    RepresentationTheory.FiniteFieldMatrixCharacterValues.distinguishedMatrixSubgroup p n := by
  obtain ⟨α, rfl⟩ := hk
  rw [conjugate_auxiliaryFunctionValue_eq_auxiliaryFunctionValue_cardPowerUnit p n hn α]
  exact ⟨_, rfl⟩


/-- The square of the auxiliary element belongs to the auxiliary set. -/
lemma auxiliaryElement_sq_mem_auxiliarySet (hn : n ≠ 0) :
    auxiliaryElement p n ^ 2 ∈ RepresentationTheory.FiniteFieldMatrixCharacterValues.distinguishedMatrixSubgroup p n := by
  rw [auxiliaryElement_sq_eq_one p n hn]
  exact Subgroup.one_mem _

section Centralizer






/-- An element commuting with a member outside the auxiliary condition belongs to the auxiliary set. -/
lemma mem_auxiliarySet_of_commutes_with_nonAuxiliaryCondition_mem (hn : n ≠ 0)
    (ζ : GL2 p n) (hζ_mem : ζ ∈ RepresentationTheory.FiniteFieldMatrixCharacterValues.distinguishedMatrixSubgroup p n)
    (hζ_ns : ¬RepresentationTheory.FiniteFieldUnitClassDecomposition.Auxiliary.classPredicateGamma (p := p) (n := n) ζ)
    (g : GL2 p n) (hcomm : g * ζ = ζ * g) :
    g ∈ RepresentationTheory.FiniteFieldMatrixCharacterValues.distinguishedMatrixSubgroup p n := by
  letI := RepresentationTheory.FiniteFieldMatrixCharacterValues.quadraticFiniteFieldAlgebra p n
  letI := RepresentationTheory.FiniteFieldMatrixCharacterValues.primeField_finiteField_quadraticExtension_isScalarTower p n
  haveI := RepresentationTheory.FiniteFieldMatrixCharacterValues.quadraticFiniteField_finiteDimensional p n
  obtain ⟨α, rfl⟩ := hζ_mem
  set b := Module.finBasisOfFinrankEq (R := GaloisField p n)
    (M := GaloisField p (2 * n)) (RepresentationTheory.FiniteFieldMatrixCharacterValues.quadraticFiniteField_finrank p n hn)
  
  have hembed : ∀ u : (GaloisField p (2 * n))ˣ,
      (RepresentationTheory.FiniteFieldMatrixCharacterValues.quadraticFieldUnitsToMatrixUnits p n u).val =
      Algebra.leftMulMatrix b (u : GaloisField p (2 * n)) := by
    intro u; change (RepresentationTheory.FiniteFieldMatrixCharacterValues.quadraticFieldUnitsToMatrixUnits p n u).val = _
    simp only [RepresentationTheory.FiniteFieldMatrixCharacterValues.quadraticFieldUnitsToMatrixUnits, dif_neg hn]; congr 1
  
  have hcomm_mat : g.val * Algebra.leftMulMatrix b (α : GaloisField p (2 * n)) =
      Algebra.leftMulMatrix b (α : GaloisField p (2 * n)) * g.val := by
    have := congr_arg (fun u : GL2 p n => u.val) hcomm
    simp only [Units.val_mul] at this; rwa [hembed] at this
  
  set φ : GaloisField p (2 * n) →ₗ[GaloisField p n] GaloisField p (2 * n) :=
    Matrix.toLinAlgEquiv b g.val with hφ_def
  
  have hφα : ∀ x, φ ((↑α : GaloisField p (2 * n)) * x) =
      (↑α : GaloisField p (2 * n)) * φ x := by
    intro x
    
    have hlm : ∀ y, Matrix.toLinAlgEquiv b (Algebra.leftMulMatrix b (↑α : GaloisField p (2 * n))) y =
        (↑α : GaloisField p (2 * n)) * y := by
      intro y
      
      
      
      change Matrix.toLin b b (LinearMap.toMatrix b b ((Algebra.lmul _ _) ↑α)) y = _
      rw [Matrix.toLin_toMatrix]; rfl
    
    have heq := congr_arg (Matrix.toLinAlgEquiv b) hcomm_mat
    simp only [map_mul] at heq
    
    have := congr_fun (congr_arg DFunLike.coe heq) x
    change φ (Matrix.toLinAlgEquiv b (Algebra.leftMulMatrix b ↑α) x) =
      Matrix.toLinAlgEquiv b (Algebra.leftMulMatrix b ↑α) (φ x) at this
    rw [hlm, hlm] at this; exact this
  
  have hα_not_base : (↑α : GaloisField p (2 * n)) ∉
      Set.range (algebraMap (GaloisField p n) (GaloisField p (2 * n))) := by
    intro ⟨c, hc⟩
    apply hζ_ns; rw [RepresentationTheory.FiniteFieldUnitClassDecomposition.classPredicateGamma_iff_matrixEntries]
    have hscalar : Algebra.leftMulMatrix b (↑α : GaloisField p (2 * n)) =
        (algebraMap (GaloisField p n) (Matrix (Fin 2) (Fin 2) (GaloisField p n))) c := by
      rw [← hc]; exact (Algebra.leftMulMatrix b).commutes c
    rw [hembed α, hscalar, Matrix.algebraMap_eq_diagonal]
    exact ⟨Matrix.diagonal_apply_ne _ (by decide : (0 : Fin 2) ≠ 1),
           Matrix.diagonal_apply_ne _ (by decide : (1 : Fin 2) ≠ 0),
           by simp [Matrix.diagonal_apply_eq]⟩
  
  have hli : LinearIndependent (GaloisField p n) ![1, (↑α : GaloisField p (2 * n))] := by
    rw [Fintype.linearIndependent_iff]
    intro f hf
    simp only [Fin.sum_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.head_fin_const] at hf
    intro i; fin_cases i
    · 
      by_contra h0
      have hf1 : f 1 ≠ 0 := by
        intro hf1; rw [hf1, zero_smul, add_zero, smul_eq_zero] at hf
        exact h0 (hf.resolve_right one_ne_zero)
      apply hα_not_base
      refine ⟨(f 1)⁻¹ * (-f 0), ?_⟩
      have h1 := eq_neg_of_add_eq_zero_right hf
      rw [Algebra.smul_def, Algebra.smul_def, mul_one] at h1
      have hne : algebraMap (GaloisField p n) (GaloisField p (2 * n)) (f 1) ≠ 0 := by
        intro he; exact hf1 ((algebraMap (GaloisField p n) (GaloisField p (2 * n))).injective
          (he.trans (map_zero _).symm))
      calc algebraMap _ _ ((f 1)⁻¹ * (-f 0))
          = (algebraMap (GaloisField p n) (GaloisField p (2 * n)) (f 1))⁻¹ *
            algebraMap _ _ (-f 0) := by rw [map_mul, map_inv₀]
        _ = (algebraMap _ (GaloisField p (2 * n)) (f 1))⁻¹ *
            -(algebraMap _ _ (f 0)) := by rw [map_neg]
        _ = (algebraMap _ _ (f 1))⁻¹ *
            (algebraMap _ _ (f 1) * ↑α) := by rw [h1]
        _ = ↑α := by rw [← mul_assoc, inv_mul_cancel₀ hne, one_mul]
    · 
      by_contra hf1
      apply hα_not_base
      refine ⟨(f 1)⁻¹ * (-f 0), ?_⟩
      have h1 := eq_neg_of_add_eq_zero_right hf
      rw [Algebra.smul_def, Algebra.smul_def, mul_one] at h1
      have hne : algebraMap (GaloisField p n) (GaloisField p (2 * n)) (f 1) ≠ 0 := by
        intro he; exact hf1 ((algebraMap (GaloisField p n) (GaloisField p (2 * n))).injective
          (he.trans (map_zero _).symm))
      calc algebraMap _ _ ((f 1)⁻¹ * (-f 0))
          = (algebraMap (GaloisField p n) (GaloisField p (2 * n)) (f 1))⁻¹ *
            algebraMap _ _ (-f 0) := by rw [map_mul, map_inv₀]
        _ = (algebraMap _ (GaloisField p (2 * n)) (f 1))⁻¹ *
            -(algebraMap _ _ (f 0)) := by rw [map_neg]
        _ = (algebraMap _ _ (f 1))⁻¹ *
            (algebraMap _ _ (f 1) * ↑α) := by rw [h1]
        _ = ↑α := by rw [← mul_assoc, inv_mul_cancel₀ hne, one_mul]
  
  have hspan : Submodule.span (GaloisField p n) (Set.range ![1, (↑α : GaloisField p (2 * n))]) = ⊤ :=
    hli.span_eq_top_of_card_eq_finrank (by simp [RepresentationTheory.FiniteFieldMatrixCharacterValues.quadraticFiniteField_finrank p n hn])
  
  have hφ_eq : ∀ x, φ x = φ 1 * x := by
    intro x
    have hx_mem : x ∈ (⊤ : Submodule (GaloisField p n) (GaloisField p (2 * n))) := trivial
    rw [← hspan] at hx_mem
    rw [Submodule.mem_span_range_iff_exists_fun] at hx_mem
    obtain ⟨c, hcx⟩ := hx_mem
    simp only [Fin.sum_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.head_fin_const] at hcx
    rw [← hcx, map_add, map_smul, map_smul]
    have hφα1 : φ (↑α : GaloisField p (2 * n)) = (↑α : GaloisField p (2 * n)) * φ 1 := by
      have := hφα 1; rwa [mul_one] at this
    rw [hφα1]; simp only [Algebra.smul_def]; ring
  
  have hg_eq : g.val = Algebra.leftMulMatrix b (φ 1) := by
    have hg_mat : g.val = LinearMap.toMatrixAlgEquiv b φ := by
      rw [hφ_def]; exact (LinearMap.toMatrixAlgEquiv_toLinAlgEquiv b g.val).symm
    ext i j
    rw [hg_mat, LinearMap.toMatrixAlgEquiv_apply,
        Algebra.leftMulMatrix_apply, LinearMap.toMatrix_apply]
    congr 2; exact hφ_eq (b j)
  
  have hφ1_ne : φ 1 ≠ 0 := by
    intro h
    have hg_zero : g.val = 0 := by rw [hg_eq, h, map_zero]
    have h1 := congr_arg Units.val (mul_inv_cancel g)
    simp only [Units.val_mul, Units.val_one, hg_zero, zero_mul] at h1
    exact zero_ne_one h1
  
  exact ⟨Units.mk0 (φ 1) hφ1_ne, by
    apply Units.ext; simp only [hembed, Units.val_mk0, hg_eq]⟩

end Centralizer

section Normalizer




/-- A predicate on the displayed auxiliary type. -/
def auxiliaryPredicate (g : GL2 p n) : Prop :=
  ∀ k ∈ RepresentationTheory.FiniteFieldMatrixCharacterValues.distinguishedMatrixSubgroup p n,
    g⁻¹ * k * g ∈ RepresentationTheory.FiniteFieldMatrixCharacterValues.distinguishedMatrixSubgroup p n


/-- Membership in the auxiliary set implies the auxiliary predicate. -/
lemma auxiliaryPredicate_of_mem
    (k : GL2 p n) (hk : k ∈ RepresentationTheory.FiniteFieldMatrixCharacterValues.distinguishedMatrixSubgroup p n) :
    auxiliaryPredicate p n k := by
  intro k' hk'
  obtain ⟨α, rfl⟩ := hk
  obtain ⟨β, rfl⟩ := hk'
  change (RepresentationTheory.FiniteFieldMatrixCharacterValues.quadraticFieldUnitsToMatrixUnits p n α)⁻¹ *
    RepresentationTheory.FiniteFieldMatrixCharacterValues.quadraticFieldUnitsToMatrixUnits p n β *
    RepresentationTheory.FiniteFieldMatrixCharacterValues.quadraticFieldUnitsToMatrixUnits p n α ∈ _
  rw [← map_inv, ← map_mul, ← map_mul, inv_mul_cancel_comm]
  exact ⟨β, rfl⟩


/-- The auxiliary element satisfies the auxiliary predicate. -/
lemma auxiliaryPredicate_auxiliaryElement [Fintype (GaloisField p n)] (hn : n ≠ 0) :
    auxiliaryPredicate p n (auxiliaryElement p n) :=
  fun k hk => mem_auxiliarySet_conjugate_by_auxiliaryElement p n hn k hk


/-- Left multiplication of an auxiliary-set member by the auxiliary element satisfies the auxiliary predicate. -/
lemma auxiliaryPredicate_auxiliaryElement_mul_of_mem [Fintype (GaloisField p n)] (hn : n ≠ 0)
    (k : GL2 p n) (hk : k ∈ RepresentationTheory.FiniteFieldMatrixCharacterValues.distinguishedMatrixSubgroup p n) :
    auxiliaryPredicate p n (auxiliaryElement p n * k) := by
  intro k' hk'
  have : (auxiliaryElement p n * k)⁻¹ * k' *
    (auxiliaryElement p n * k) =
    k⁻¹ * ((auxiliaryElement p n)⁻¹ * k' *
      auxiliaryElement p n) * k := by group
  rw [this]
  exact auxiliaryPredicate_of_mem p n k hk _
    (mem_auxiliarySet_conjugate_by_auxiliaryElement p n hn k' hk')


private lemma GL2.isScalar_of_conj_isScalar (z g : GL2 p n)
    (h : RepresentationTheory.FiniteFieldUnitClassDecomposition.Auxiliary.classPredicateGamma (p := p) (n := n) (z⁻¹ * g * z)) :
    RepresentationTheory.FiniteFieldUnitClassDecomposition.Auxiliary.classPredicateGamma (p := p) (n := n) g := by
  rw [RepresentationTheory.FiniteFieldUnitClassDecomposition.classPredicateGamma_iff_matrixEntries] at h ⊢
  obtain ⟨h01, h10, h00_eq_h11⟩ := h
  
  set c := (z⁻¹ * g * z).val 0 0
  have hscalar : (z⁻¹ * g * z).val = c • (1 : Matrix (Fin 2) (Fin 2) (GaloisField p n)) := by
    ext i j; fin_cases i <;> fin_cases j <;> simp [c, h01, h10, h00_eq_h11]
  
  have hrecover : g = z * (z⁻¹ * g * z) * z⁻¹ := by group
  have hg_val : g.val = c • 1 := by
    have := congr_arg Units.val hrecover
    simp only [Units.val_mul] at this
    rw [this]
    
    
    conv_lhs => rw [show (z⁻¹).val * g.val * z.val = (z⁻¹ * g * z).val from by
      simp [Units.val_mul]]
    rw [hscalar, Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_one]
    have hzz : z.val * (z⁻¹).val = 1 :=
      show (z * z⁻¹).val = (1 : GL2 p n).val from congr_arg Units.val (mul_inv_cancel z)
    rw [hzz]
  constructor
  · have := congr_fun (congr_fun hg_val 0) 1; simp at this; exact this
  constructor
  · have := congr_fun (congr_fun hg_val 1) 0; simp at this; exact this
  · have h0 := congr_fun (congr_fun hg_val 0) 0
    have h1 := congr_fun (congr_fun hg_val 1) 1
    simp at h0 h1; rw [h0, h1]


/-- Derives the auxiliary predicate from membership, a negated auxiliary condition, and conjugate membership. -/
lemma auxiliaryPredicate_of_mem_of_notAuxiliaryCondition_of_conjugate_mem (hn : n ≠ 0)
    (hp2 : p ≠ 2)
    (k : GL2 p n) (hk_mem : k ∈ RepresentationTheory.FiniteFieldMatrixCharacterValues.distinguishedMatrixSubgroup p n)
    (hk_ns : ¬RepresentationTheory.FiniteFieldUnitClassDecomposition.Auxiliary.classPredicateGamma (p := p) (n := n) k)
    (z : GL2 p n) (hz : z⁻¹ * k * z ∈ RepresentationTheory.FiniteFieldMatrixCharacterValues.distinguishedMatrixSubgroup p n) :
    auxiliaryPredicate p n z := by
  intro k' hk'
  
  have hcomm : z⁻¹ * k' * z * (z⁻¹ * k * z) = z⁻¹ * k * z * (z⁻¹ * k' * z) := by
    
    obtain ⟨α, rfl⟩ := hk_mem
    obtain ⟨β, rfl⟩ := hk'
    
    have : z⁻¹ * RepresentationTheory.FiniteFieldMatrixCharacterValues.quadraticFieldUnitsToMatrixUnits p n β * z *
      (z⁻¹ * RepresentationTheory.FiniteFieldMatrixCharacterValues.quadraticFieldUnitsToMatrixUnits p n α * z) =
      z⁻¹ * (RepresentationTheory.FiniteFieldMatrixCharacterValues.quadraticFieldUnitsToMatrixUnits p n β *
      RepresentationTheory.FiniteFieldMatrixCharacterValues.quadraticFieldUnitsToMatrixUnits p n α) * z := by group
    have : z⁻¹ * RepresentationTheory.FiniteFieldMatrixCharacterValues.quadraticFieldUnitsToMatrixUnits p n α * z *
      (z⁻¹ * RepresentationTheory.FiniteFieldMatrixCharacterValues.quadraticFieldUnitsToMatrixUnits p n β * z) =
      z⁻¹ * (RepresentationTheory.FiniteFieldMatrixCharacterValues.quadraticFieldUnitsToMatrixUnits p n α *
      RepresentationTheory.FiniteFieldMatrixCharacterValues.quadraticFieldUnitsToMatrixUnits p n β) * z := by group
    rw [show z⁻¹ * RepresentationTheory.FiniteFieldMatrixCharacterValues.quadraticFieldUnitsToMatrixUnits p n β * z *
      (z⁻¹ * RepresentationTheory.FiniteFieldMatrixCharacterValues.quadraticFieldUnitsToMatrixUnits p n α * z) =
      z⁻¹ * (RepresentationTheory.FiniteFieldMatrixCharacterValues.quadraticFieldUnitsToMatrixUnits p n β *
      RepresentationTheory.FiniteFieldMatrixCharacterValues.quadraticFieldUnitsToMatrixUnits p n α) * z from by group,
      show z⁻¹ * RepresentationTheory.FiniteFieldMatrixCharacterValues.quadraticFieldUnitsToMatrixUnits p n α * z *
      (z⁻¹ * RepresentationTheory.FiniteFieldMatrixCharacterValues.quadraticFieldUnitsToMatrixUnits p n β * z) =
      z⁻¹ * (RepresentationTheory.FiniteFieldMatrixCharacterValues.quadraticFieldUnitsToMatrixUnits p n α *
      RepresentationTheory.FiniteFieldMatrixCharacterValues.quadraticFieldUnitsToMatrixUnits p n β) * z from by group,
      ← map_mul, ← map_mul, mul_comm β α]
  
  have hns : ¬RepresentationTheory.FiniteFieldUnitClassDecomposition.Auxiliary.classPredicateGamma (p := p) (n := n) (z⁻¹ * k * z) :=
    fun h => hk_ns (GL2.isScalar_of_conj_isScalar p n z k h)
  
  exact mem_auxiliarySet_of_commutes_with_nonAuxiliaryCondition_mem p n hn
    (z⁻¹ * k * z) hz hns (z⁻¹ * k' * z) hcomm




/-- The auxiliary element does not belong to the auxiliary set. -/
lemma auxiliaryElement_not_mem_auxiliarySet (hn : n ≠ 0)
    [Fintype (GaloisField p n)] :
    auxiliaryElement p n ∉ RepresentationTheory.FiniteFieldMatrixCharacterValues.distinguishedMatrixSubgroup p n := by
  intro ⟨α, hα⟩
  
  
  
  letI := RepresentationTheory.FiniteFieldMatrixCharacterValues.quadraticFiniteFieldAlgebra p n
  letI := RepresentationTheory.FiniteFieldMatrixCharacterValues.primeField_finiteField_quadraticExtension_isScalarTower p n
  haveI := RepresentationTheory.FiniteFieldMatrixCharacterValues.quadraticFiniteField_finiteDimensional p n
  haveI : Fintype (GaloisField p (2 * n)) := Fintype.ofFinite _
  haveI : Algebra.IsAlgebraic (GaloisField p n) (GaloisField p (2 * n)) :=
    Algebra.IsAlgebraic.of_finite _ _
  
  set b := Module.finBasisOfFinrankEq (R := GaloisField p n)
    (M := GaloisField p (2 * n)) (RepresentationTheory.FiniteFieldMatrixCharacterValues.quadraticFiniteField_finrank p n hn)
  have hembed : ∀ (w : (GaloisField p (2 * n))ˣ),
      (RepresentationTheory.FiniteFieldMatrixCharacterValues.quadraticFieldUnitsToMatrixUnits p n w).val =
      Algebra.leftMulMatrix b (w : GaloisField p (2 * n)) := by
    intro w; simp only [RepresentationTheory.FiniteFieldMatrixCharacterValues.quadraticFieldUnitsToMatrixUnits, dif_neg hn]; congr 1
  have hembed_inj : Function.Injective (RepresentationTheory.FiniteFieldMatrixCharacterValues.quadraticFieldUnitsToMatrixUnits p n) := by
    intro u v huv
    have hval : (RepresentationTheory.FiniteFieldMatrixCharacterValues.quadraticFieldUnitsToMatrixUnits p n u).val =
        (RepresentationTheory.FiniteFieldMatrixCharacterValues.quadraticFieldUnitsToMatrixUnits p n v).val := congr_arg Units.val huv
    rw [hembed u, hembed v] at hval
    exact Units.ext (Algebra.leftMulMatrix_injective b hval)
  
  
  
  have htriv : ∀ β : (GaloisField p (2 * n))ˣ,
      (β : GaloisField p (2 * n)) ^ Fintype.card (GaloisField p n) = β := by
    intro β
    have hconj := conjugate_auxiliaryFunctionValue_eq_auxiliaryFunctionValue_cardPowerUnit p n hn β
    rw [← hα] at hconj
    have hcomm : (RepresentationTheory.FiniteFieldMatrixCharacterValues.quadraticFieldUnitsToMatrixUnits p n α)⁻¹ *
      RepresentationTheory.FiniteFieldMatrixCharacterValues.quadraticFieldUnitsToMatrixUnits p n β *
      RepresentationTheory.FiniteFieldMatrixCharacterValues.quadraticFieldUnitsToMatrixUnits p n α = RepresentationTheory.FiniteFieldMatrixCharacterValues.quadraticFieldUnitsToMatrixUnits p n β := by
      rw [← map_inv, ← map_mul, ← map_mul, inv_mul_cancel_comm]
    rw [hcomm] at hconj
    have := hembed_inj hconj
    simp only [Units.ext_iff] at this
    exact this.symm
  
  have h_unit_eq : ∀ β : (GaloisField p (2 * n))ˣ,
      β ^ Fintype.card (GaloisField p n) = β := by
    intro β
    exact Units.val_injective (by rw [Units.val_pow_eq_pow_val]; exact htriv β)
  
  have h_pow_one : ∀ β : (GaloisField p (2 * n))ˣ,
      β ^ (Fintype.card (GaloisField p n) - 1) = 1 := by
    intro β
    have heq := h_unit_eq β
    rw [show Fintype.card (GaloisField p n) =
        Fintype.card (GaloisField p n) - 1 + 1 from
      (Nat.succ_pred_eq_of_pos Fintype.card_pos).symm, pow_succ] at heq
    exact mul_right_cancel (by rw [one_mul]; exact heq)
  
  have hdvd : Fintype.card (GaloisField p (2 * n)) - 1 ∣
      Fintype.card (GaloisField p n) - 1 :=
    (FiniteField.forall_pow_eq_one_iff
      (K := GaloisField p (2 * n)) (Fintype.card (GaloisField p n) - 1)).mp h_pow_one
  
  have hq := @GaloisField.card p _ n hn
  have hq2 := @GaloisField.card p _ (2 * n) (by omega : 2 * n ≠ 0)
  simp only [Fintype.card_eq_nat_card] at hdvd
  rw [hq, hq2] at hdvd
  have hpn_ge : p ^ n ≥ 2 := by
    calc p ^ n ≥ 2 ^ n := Nat.pow_le_pow_left (Nat.Prime.two_le hp.out) n
      _ ≥ 2 ^ 1 := Nat.pow_le_pow_right (by omega) (by omega)
      _ = 2 := by norm_num
  have h2n : p ^ (2 * n) = p ^ n * p ^ n := by rw [two_mul, pow_add]
  have hgt : p ^ (2 * n) > p ^ n := by nlinarith
  exact absurd (Nat.le_of_dvd (by omega) hdvd) (by omega)


private lemma GL2.exists_nonscalar_elliptic (hn : n ≠ 0) :
    ∃ α : (GaloisField p (2 * n))ˣ,
      ¬RepresentationTheory.FiniteFieldUnitClassDecomposition.Auxiliary.classPredicateGamma (p := p) (n := n) (RepresentationTheory.FiniteFieldMatrixCharacterValues.quadraticFieldUnitsToMatrixUnits p n α) := by
  letI := RepresentationTheory.FiniteFieldMatrixCharacterValues.quadraticFiniteFieldAlgebra p n
  letI := RepresentationTheory.FiniteFieldMatrixCharacterValues.primeField_finiteField_quadraticExtension_isScalarTower p n
  haveI := RepresentationTheory.FiniteFieldMatrixCharacterValues.quadraticFiniteField_finiteDimensional p n
  
  
  by_contra h
  push Not at h 
  set b := Module.finBasisOfFinrankEq (R := GaloisField p n)
    (M := GaloisField p (2 * n)) (RepresentationTheory.FiniteFieldMatrixCharacterValues.quadraticFiniteField_finrank p n hn)
  have hembed : ∀ (u : (GaloisField p (2 * n))ˣ),
      (RepresentationTheory.FiniteFieldMatrixCharacterValues.quadraticFieldUnitsToMatrixUnits p n u).val =
      Algebra.leftMulMatrix b (u : GaloisField p (2 * n)) := by
    intro u; simp only [RepresentationTheory.FiniteFieldMatrixCharacterValues.quadraticFieldUnitsToMatrixUnits, dif_neg hn]; congr 1
  
  have h_all_in_range : ∀ x : GaloisField p (2 * n),
      x ∈ Set.range (algebraMap (GaloisField p n) (GaloisField p (2 * n))) := by
    intro x
    by_cases hx : x = 0
    · exact ⟨0, by rw [hx, map_zero]⟩
    · 
      let α : (GaloisField p (2 * n))ˣ := Units.mk0 x hx
      have hscalar := h α
      rw [RepresentationTheory.FiniteFieldUnitClassDecomposition.classPredicateGamma_iff_matrixEntries] at hscalar
      
      
      have hmat := hembed α
      
      
      have h01 : (Algebra.leftMulMatrix b x) 0 1 = 0 := by
        have := hscalar.1; rwa [hembed] at this
      have h10 : (Algebra.leftMulMatrix b x) 1 0 = 0 := by
        have := hscalar.2.1; rwa [hembed] at this
      have h_diag : (Algebra.leftMulMatrix b x) 0 0 =
          (Algebra.leftMulMatrix b x) 1 1 := by
        have := hscalar.2.2; rwa [hembed] at this
      
      set c := (Algebra.leftMulMatrix b x) 0 0
      have hmat_eq : Algebra.leftMulMatrix b x =
          (algebraMap (GaloisField p n)
            (Matrix (Fin 2) (Fin 2) (GaloisField p n))) c := by
        rw [Matrix.algebraMap_eq_diagonal]
        ext i j; fin_cases i <;> fin_cases j <;>
          simp [c, h01, h10, h_diag, Matrix.diagonal_apply_eq, Matrix.diagonal_apply_ne]
      
      have := Algebra.leftMulMatrix_injective b
        (show Algebra.leftMulMatrix b x =
          Algebra.leftMulMatrix b (algebraMap (GaloisField p n) _ c) by
          rw [hmat_eq, (Algebra.leftMulMatrix b).commutes c])
      exact ⟨c, this.symm⟩
  
  have hsurj : Function.Surjective
      (algebraMap (GaloisField p n) (GaloisField p (2 * n))) :=
    fun x => h_all_in_range x
  have : Module.finrank (GaloisField p n) (GaloisField p (2 * n)) ≤ 1 :=
    finrank_le_one (1 : GaloisField p (2 * n)) (fun w => by
      obtain ⟨c, hc⟩ := hsurj w
      exact ⟨c, by rw [Algebra.smul_def, mul_one, hc]⟩)
  have := RepresentationTheory.FiniteFieldMatrixCharacterValues.quadraticFiniteField_finrank p n hn
  omega



private lemma GL2.isRoot_charpoly_leftMulMatrix (hn : n ≠ 0)
    (α : GaloisField p (2 * n)) :
    letI := RepresentationTheory.FiniteFieldMatrixCharacterValues.quadraticFiniteFieldAlgebra p n
    letI := RepresentationTheory.FiniteFieldMatrixCharacterValues.primeField_finiteField_quadraticExtension_isScalarTower p n
    haveI := RepresentationTheory.FiniteFieldMatrixCharacterValues.quadraticFiniteField_finiteDimensional p n
    let b := Module.finBasisOfFinrankEq (R := GaloisField p n)
      (M := GaloisField p (2 * n)) (RepresentationTheory.FiniteFieldMatrixCharacterValues.quadraticFiniteField_finrank p n hn)
    Polynomial.aeval α (Algebra.leftMulMatrix b α).charpoly = 0 := by
  letI := RepresentationTheory.FiniteFieldMatrixCharacterValues.quadraticFiniteFieldAlgebra p n
  letI := RepresentationTheory.FiniteFieldMatrixCharacterValues.primeField_finiteField_quadraticExtension_isScalarTower p n
  haveI := RepresentationTheory.FiniteFieldMatrixCharacterValues.quadraticFiniteField_finiteDimensional p n
  set b := Module.finBasisOfFinrankEq (R := GaloisField p n)
    (M := GaloisField p (2 * n)) (RepresentationTheory.FiniteFieldMatrixCharacterValues.quadraticFiniteField_finrank p n hn)
  apply Algebra.leftMulMatrix_injective b
  rw [map_zero, ← Polynomial.aeval_algHom_apply (Algebra.leftMulMatrix b)]
  exact Matrix.aeval_self_charpoly _


private lemma GL2.frobenius_root_of_basefield_poly (hn : n ≠ 0)
    [Fintype (GaloisField p n)]
    (α : GaloisField p (2 * n))
    (P : Polynomial (GaloisField p n))
    (hroot : Polynomial.aeval α P = 0) :
    Polynomial.aeval (α ^ Fintype.card (GaloisField p n)) P = 0 := by
  letI := RepresentationTheory.FiniteFieldMatrixCharacterValues.quadraticFiniteFieldAlgebra p n
  letI := RepresentationTheory.FiniteFieldMatrixCharacterValues.primeField_finiteField_quadraticExtension_isScalarTower p n
  haveI := RepresentationTheory.FiniteFieldMatrixCharacterValues.quadraticFiniteField_finiteDimensional p n
  haveI : Fintype (GaloisField p (2 * n)) := Fintype.ofFinite _
  haveI : Algebra.IsAlgebraic (GaloisField p n) (GaloisField p (2 * n)) :=
    Algebra.IsAlgebraic.of_finite _ _
  let φ := FiniteField.frobeniusAlgEquivOfAlgebraic
    (GaloisField p n) (GaloisField p (2 * n))
  have hφ_eq : ∀ x : GaloisField p (2 * n),
      φ x = x ^ Fintype.card (GaloisField p n) := by
    intro x; exact congrFun (FiniteField.coe_frobeniusAlgEquivOfAlgebraic _ _) x
  have key : Polynomial.aeval (φ.toAlgHom α) P = 0 := by
    rw [Polynomial.aeval_algHom_apply, hroot, map_zero]
  
  rw [← hφ_eq α]; exact key


private lemma GL2.root_dichotomy_of_deg_two
    {R F : Type*} [Field R] [Field F] [Algebra R F]
    (P : Polynomial R) (hdeg : P.natDegree = 2)
    (a b c : F) (ha : Polynomial.aeval a P = 0) (hb : Polynomial.aeval b P = 0)
    (hc : Polynomial.aeval c P = 0) (hab : a ≠ b) :
    c = a ∨ c = b := by
  
  set Q := P.map (algebraMap R F) with hQ_def
  have hdQ : Q.natDegree = 2 := by rw [hQ_def, Polynomial.natDegree_map]; exact hdeg
  have hQ_ne : Q ≠ 0 := by intro h; rw [h, Polynomial.natDegree_zero] at hdQ; omega
  
  have ha' : Q.IsRoot a := by
    simp only [Polynomial.IsRoot, hQ_def, Polynomial.eval_map, ← Polynomial.aeval_def]; exact ha
  have hb' : Q.IsRoot b := by
    simp only [Polynomial.IsRoot, hQ_def, Polynomial.eval_map, ← Polynomial.aeval_def]; exact hb
  have hc' : Q.IsRoot c := by
    simp only [Polynomial.IsRoot, hQ_def, Polynomial.eval_map, ← Polynomial.aeval_def]; exact hc
  
  have hda : (Polynomial.X - Polynomial.C a) ∣ Q := Polynomial.dvd_iff_isRoot.mpr ha'
  have hdb : (Polynomial.X - Polynomial.C b) ∣ Q := Polynomial.dvd_iff_isRoot.mpr hb'
  have hcop : IsCoprime (Polynomial.X - Polynomial.C a : Polynomial F)
      (Polynomial.X - Polynomial.C b) :=
    Polynomial.isCoprime_X_sub_C_of_isUnit_sub (sub_ne_zero.mpr hab).isUnit
  
  obtain ⟨r, hr⟩ := hcop.mul_dvd hda hdb
  
  have hr_ne : r ≠ 0 := right_ne_zero_of_mul (hr ▸ hQ_ne)
  have hprod_ne : (Polynomial.X - Polynomial.C a) *
      (Polynomial.X - Polynomial.C b : Polynomial F) ≠ 0 :=
    mul_ne_zero (Polynomial.X_sub_C_ne_zero a) (Polynomial.X_sub_C_ne_zero b)
  have hr_deg : r.natDegree = 0 := by
    have hprod_deg : ((Polynomial.X - Polynomial.C a) *
        (Polynomial.X - Polynomial.C b) : Polynomial F).natDegree = 2 := by
      rw [Polynomial.natDegree_mul (Polynomial.X_sub_C_ne_zero a) (Polynomial.X_sub_C_ne_zero b)]
      simp
    by_contra h
    have : Q.natDegree ≥ 3 := by
      rw [hr, Polynomial.natDegree_mul hprod_ne hr_ne, hprod_deg]; omega
    omega
  
  have heval : (c - a) * (c - b) * r.eval c = 0 := by
    have := hc'
    rw [Polynomial.IsRoot, hr, Polynomial.eval_mul, Polynomial.eval_mul,
      Polynomial.eval_sub, Polynomial.eval_X, Polynomial.eval_C,
      Polynomial.eval_sub, Polynomial.eval_X, Polynomial.eval_C] at this
    exact this
  
  have hr_eval_ne : r.eval c ≠ 0 := by
    have hk := Polynomial.eq_C_of_natDegree_eq_zero hr_deg
    rw [hk, Polynomial.eval_C]
    intro h; exact hr_ne (by rw [hk, h, map_zero])
  
  have hab0 : (c - a) * (c - b) = 0 := by
    rcases mul_eq_zero.mp heval with h | h
    · exact h
    · exact absurd h hr_eval_ne
  rcases mul_eq_zero.mp hab0 with h | h
  · left; exact sub_eq_zero.mp h
  · right; exact sub_eq_zero.mp h

set_option maxHeartbeats 1600000 in

/-- An auxiliary-predicate element is in the auxiliary set or has the displayed auxiliary-element factorization. -/
lemma mem_auxiliarySet_or_exists_auxiliaryElement_mul_of_auxiliaryPredicate (hn : n ≠ 0) (hp2 : p ≠ 2)
    [Fintype (GaloisField p n)]
    (g : GL2 p n) (hg : auxiliaryPredicate p n g) :
    g ∈ RepresentationTheory.FiniteFieldMatrixCharacterValues.distinguishedMatrixSubgroup p n ∨
    ∃ α : (GaloisField p (2 * n))ˣ,
      g = auxiliaryElement p n * RepresentationTheory.FiniteFieldMatrixCharacterValues.quadraticFieldUnitsToMatrixUnits p n α := by
  letI := RepresentationTheory.FiniteFieldMatrixCharacterValues.quadraticFiniteFieldAlgebra p n
  letI := RepresentationTheory.FiniteFieldMatrixCharacterValues.primeField_finiteField_quadraticExtension_isScalarTower p n
  haveI := RepresentationTheory.FiniteFieldMatrixCharacterValues.quadraticFiniteField_finiteDimensional p n
  haveI : Fintype (GaloisField p (2 * n)) := Fintype.ofFinite _
  haveI : Algebra.IsAlgebraic (GaloisField p n) (GaloisField p (2 * n)) :=
    Algebra.IsAlgebraic.of_finite _ _
  set b := Module.finBasisOfFinrankEq (R := GaloisField p n)
    (M := GaloisField p (2 * n)) (RepresentationTheory.FiniteFieldMatrixCharacterValues.quadraticFiniteField_finrank p n hn)
  have hembed : ∀ (u : (GaloisField p (2 * n))ˣ),
      (RepresentationTheory.FiniteFieldMatrixCharacterValues.quadraticFieldUnitsToMatrixUnits p n u).val =
      Algebra.leftMulMatrix b (u : GaloisField p (2 * n)) := by
    intro u; simp only [RepresentationTheory.FiniteFieldMatrixCharacterValues.quadraticFieldUnitsToMatrixUnits, dif_neg hn]; congr 1
  
  obtain ⟨α₀, hα₀_ns⟩ := GL2.exists_nonscalar_elliptic p n hn
  
  have hconj := hg (RepresentationTheory.FiniteFieldMatrixCharacterValues.quadraticFieldUnitsToMatrixUnits p n α₀) ⟨α₀, rfl⟩
  obtain ⟨β, hβ⟩ := hconj
  
  set P := (Algebra.leftMulMatrix b (α₀ : GaloisField p (2 * n))).charpoly
  have hcharpoly_eq : (Algebra.leftMulMatrix b (β : GaloisField p (2 * n))).charpoly = P := by
    
    
    
    have hval : Algebra.leftMulMatrix b (β : GaloisField p (2 * n)) =
        (g.val)⁻¹ * Algebra.leftMulMatrix b (α₀ : GaloisField p (2 * n)) * g.val := by
      have h1 := hembed β; have h2 := hembed α₀
      rw [← h1, ← h2, hβ, ← Matrix.coe_units_inv]; simp [Units.val_mul]
    rw [hval]
    exact Matrix.charpoly_units_conj' g _
  
  have hα₀_root : Polynomial.aeval (α₀ : GaloisField p (2 * n)) P = 0 :=
    GL2.isRoot_charpoly_leftMulMatrix p n hn ↑α₀
  have hβ_root : Polynomial.aeval (β : GaloisField p (2 * n)) P = 0 := by
    rw [show P = (Algebra.leftMulMatrix b (β : GaloisField p (2 * n))).charpoly from
      hcharpoly_eq.symm]
    exact GL2.isRoot_charpoly_leftMulMatrix p n hn ↑β
  set q := Fintype.card (GaloisField p n)
  have hαq_root : Polynomial.aeval ((α₀ : GaloisField p (2 * n)) ^ q) P = 0 :=
    GL2.frobenius_root_of_basefield_poly p n hn ↑α₀ P hα₀_root
  
  have hdeg : P.natDegree = 2 := by
    change (Algebra.leftMulMatrix b (↑α₀ : GaloisField p (2 * n))).charpoly.natDegree = 2
    rw [Matrix.charpoly_natDegree_eq_dim]; simp [Fintype.card_fin]
  
  have hne : (α₀ : GaloisField p (2 * n)) ≠ (α₀ : GaloisField p (2 * n)) ^ q := by
    
    intro heq
    apply hα₀_ns
    
    let φ := FiniteField.frobeniusAlgEquivOfAlgebraic
        (GaloisField p n) (GaloisField p (2 * n))
    have hφ_fix : φ (↑α₀) = ↑α₀ := by
      rw [show (φ : GaloisField p (2 * n) → GaloisField p (2 * n)) (↑α₀) = (↑α₀) ^ q from
        congrFun (FiniteField.coe_frobeniusAlgEquivOfAlgebraic _ _) _]
      exact heq.symm
    
    have hφ_ne_one : φ ≠ 1 := by
      intro h
      
      
      have hbij := FiniteField.bijective_frobeniusAlgEquivOfAlgebraic_pow
        (GaloisField p n) (GaloisField p (2 * n))
      rw [RepresentationTheory.FiniteFieldMatrixCharacterValues.quadraticFiniteField_finrank p n hn] at hbij
      exact absurd (hbij.1 (show φ ^ (0 : Fin 2).1 = φ ^ (1 : Fin 2).1 by simp [h]))
        (by decide)
    
    have hcard_gal : Nat.card (GaloisField p (2 * n) ≃ₐ[GaloisField p n]
        GaloisField p (2 * n)) = 2 :=
      (IsGalois.card_aut_eq_finrank (GaloisField p n) (GaloisField p (2 * n))).trans
        (RepresentationTheory.FiniteFieldMatrixCharacterValues.quadraticFiniteField_finrank p n hn)
    have hall_fix : ∀ f : (GaloisField p (2 * n) ≃ₐ[GaloisField p n] GaloisField p (2 * n)),
        f (↑α₀ : GaloisField p (2 * n)) = ↑α₀ := by
      intro f
      
      obtain ⟨y, hy_ne, hy_unique⟩ :=
        (Nat.card_eq_two_iff' (1 : GaloisField p (2 * n) ≃ₐ[GaloisField p n]
          GaloisField p (2 * n))).mp hcard_gal
      by_cases hf : f = 1
      · rw [hf]; simp
      · 
        have hfy : f = y := hy_unique f hf
        have hφy : φ = y := hy_unique φ hφ_ne_one
        rw [hfy, ← hφy]; exact hφ_fix
    
    have h_in_range : (↑α₀ : GaloisField p (2 * n)) ∈
        Set.range (algebraMap (GaloisField p n) (GaloisField p (2 * n))) :=
      (IsGalois.mem_range_algebraMap_iff_fixed
        (F := GaloisField p n) (E := GaloisField p (2 * n)) (↑α₀)).mpr hall_fix
    
    obtain ⟨c, hc⟩ := h_in_range
    rw [RepresentationTheory.FiniteFieldUnitClassDecomposition.classPredicateGamma_iff_matrixEntries]
    have hscalar : Algebra.leftMulMatrix b (↑α₀ : GaloisField p (2 * n)) =
        (algebraMap (GaloisField p n) (Matrix (Fin 2) (Fin 2) (GaloisField p n))) c := by
      rw [← hc]; exact (Algebra.leftMulMatrix b).commutes c
    rw [hembed α₀, hscalar, Matrix.algebraMap_eq_diagonal]
    exact ⟨Matrix.diagonal_apply_ne _ (by decide : (0 : Fin 2) ≠ 1),
           Matrix.diagonal_apply_ne _ (by decide : (1 : Fin 2) ≠ 0),
           by simp [Matrix.diagonal_apply_eq]⟩
  
  have hβ_dichotomy : (β : GaloisField p (2 * n)) = ↑α₀ ∨
      (β : GaloisField p (2 * n)) = (↑α₀ : GaloisField p (2 * n)) ^ q :=
    GL2.root_dichotomy_of_deg_two (F := GaloisField p (2 * n))
      P hdeg (↑α₀) ((↑α₀) ^ q) (↑β) hα₀_root hαq_root hβ_root hne
  
  rcases hβ_dichotomy with hβ_eq_α | hβ_eq_αq
  · 
    left
    have hβα : β = α₀ := Units.val_injective hβ_eq_α
    rw [hβα] at hβ
    
    have hcomm : g * RepresentationTheory.FiniteFieldMatrixCharacterValues.quadraticFieldUnitsToMatrixUnits p n α₀ =
        RepresentationTheory.FiniteFieldMatrixCharacterValues.quadraticFieldUnitsToMatrixUnits p n α₀ * g := by
      
      calc g * RepresentationTheory.FiniteFieldMatrixCharacterValues.quadraticFieldUnitsToMatrixUnits p n α₀
          = g * (g⁻¹ * RepresentationTheory.FiniteFieldMatrixCharacterValues.quadraticFieldUnitsToMatrixUnits p n α₀ * g) :=
            congr_arg (g * ·) hβ
        _ = RepresentationTheory.FiniteFieldMatrixCharacterValues.quadraticFieldUnitsToMatrixUnits p n α₀ * g := by group
    exact mem_auxiliarySet_of_commutes_with_nonAuxiliaryCondition_mem p n hn
      (RepresentationTheory.FiniteFieldMatrixCharacterValues.quadraticFieldUnitsToMatrixUnits p n α₀) ⟨α₀, rfl⟩ hα₀_ns g hcomm
  · 
    right
    
    
    
    
    set σ := auxiliaryElement p n
    
    set α₀q_unit : (GaloisField p (2 * n))ˣ :=
      ⟨(↑α₀ : GaloisField p (2 * n)) ^ q,
       (↑α₀⁻¹ : GaloisField p (2 * n)) ^ q,
       by rw [← mul_pow]; simp [Units.val_inv_eq_inv_val],
       by rw [← mul_pow]; simp [Units.val_inv_eq_inv_val]⟩
    have hβ_eq_αq_unit : β = α₀q_unit := Units.val_injective hβ_eq_αq
    
    have hfrob_conj := conjugate_auxiliaryFunctionValue_eq_auxiliaryFunctionValue_cardPowerUnit p n hn α₀
    
    have hconj_eq : g⁻¹ * RepresentationTheory.FiniteFieldMatrixCharacterValues.quadraticFieldUnitsToMatrixUnits p n α₀ * g =
        σ⁻¹ * RepresentationTheory.FiniteFieldMatrixCharacterValues.quadraticFieldUnitsToMatrixUnits p n α₀ * σ := by
      have hfrob := conjugate_auxiliaryFunctionValue_eq_auxiliaryFunctionValue_cardPowerUnit p n hn α₀
      
      calc g⁻¹ * RepresentationTheory.FiniteFieldMatrixCharacterValues.quadraticFieldUnitsToMatrixUnits p n α₀ * g
          = RepresentationTheory.FiniteFieldMatrixCharacterValues.quadraticFieldUnitsToMatrixUnits p n β := hβ.symm
        _ = RepresentationTheory.FiniteFieldMatrixCharacterValues.quadraticFieldUnitsToMatrixUnits p n α₀q_unit :=
            congr_arg _ hβ_eq_αq_unit
        _ = (auxiliaryElement p n)⁻¹ * RepresentationTheory.FiniteFieldMatrixCharacterValues.quadraticFieldUnitsToMatrixUnits p n α₀ *
            auxiliaryElement p n := by
          convert hfrob.symm using 2; exact Units.ext rfl
    
    have hcomm : g * σ⁻¹ * RepresentationTheory.FiniteFieldMatrixCharacterValues.quadraticFieldUnitsToMatrixUnits p n α₀ =
        RepresentationTheory.FiniteFieldMatrixCharacterValues.quadraticFieldUnitsToMatrixUnits p n α₀ * (g * σ⁻¹) := by
      
      
      
      have := congr_arg (g * · * σ⁻¹) hconj_eq
      
      beta_reduce at this
      rw [show g * (g⁻¹ * RepresentationTheory.FiniteFieldMatrixCharacterValues.quadraticFieldUnitsToMatrixUnits p n α₀ * g) * σ⁻¹ =
          RepresentationTheory.FiniteFieldMatrixCharacterValues.quadraticFieldUnitsToMatrixUnits p n α₀ * (g * σ⁻¹) from by group,
        show g * (σ⁻¹ * RepresentationTheory.FiniteFieldMatrixCharacterValues.quadraticFieldUnitsToMatrixUnits p n α₀ * σ) * σ⁻¹ =
          g * σ⁻¹ * RepresentationTheory.FiniteFieldMatrixCharacterValues.quadraticFieldUnitsToMatrixUnits p n α₀ from by group] at this
      exact this.symm
    
    have hgσ_inv_mem : g * σ⁻¹ ∈ RepresentationTheory.FiniteFieldMatrixCharacterValues.distinguishedMatrixSubgroup p n :=
      mem_auxiliarySet_of_commutes_with_nonAuxiliaryCondition_mem p n hn
        (RepresentationTheory.FiniteFieldMatrixCharacterValues.quadraticFieldUnitsToMatrixUnits p n α₀) ⟨α₀, rfl⟩ hα₀_ns (g * σ⁻¹) hcomm
    
    obtain ⟨γ, hγ⟩ := hgσ_inv_mem
    
    have hg_eq : g = RepresentationTheory.FiniteFieldMatrixCharacterValues.quadraticFieldUnitsToMatrixUnits p n γ * σ := by
      calc g = g * σ⁻¹ * σ := by group
        _ = RepresentationTheory.FiniteFieldMatrixCharacterValues.quadraticFieldUnitsToMatrixUnits p n γ * σ := by rw [hγ]
    
    
    
    set γq_unit : (GaloisField p (2 * n))ˣ :=
      ⟨(↑γ : GaloisField p (2 * n)) ^ q,
       (↑γ⁻¹ : GaloisField p (2 * n)) ^ q,
       by rw [← mul_pow]; simp [Units.val_inv_eq_inv_val],
       by rw [← mul_pow]; simp [Units.val_inv_eq_inv_val]⟩
    refine ⟨γq_unit, ?_⟩
    rw [hg_eq]
    
    have hfrob_γ := conjugate_auxiliaryFunctionValue_eq_auxiliaryFunctionValue_cardPowerUnit p n hn γ
    
    
    change RepresentationTheory.FiniteFieldMatrixCharacterValues.quadraticFieldUnitsToMatrixUnits p n γ * auxiliaryElement p n =
      auxiliaryElement p n * RepresentationTheory.FiniteFieldMatrixCharacterValues.quadraticFieldUnitsToMatrixUnits p n γq_unit
    calc RepresentationTheory.FiniteFieldMatrixCharacterValues.quadraticFieldUnitsToMatrixUnits p n γ * auxiliaryElement p n
        = auxiliaryElement p n *
          ((auxiliaryElement p n)⁻¹ * RepresentationTheory.FiniteFieldMatrixCharacterValues.quadraticFieldUnitsToMatrixUnits p n γ *
           auxiliaryElement p n) := by group
      _ = auxiliaryElement p n * RepresentationTheory.FiniteFieldMatrixCharacterValues.quadraticFieldUnitsToMatrixUnits p n γq_unit := by
          congr 1; convert hfrob_γ using 2; exact Units.ext rfl





/-- The filtered cardinality of the auxiliary predicate is twice the auxiliary-set cardinality. -/
lemma card_auxiliaryPredicate_eq_two_mul_card_auxiliarySet (hn : n ≠ 0) (hp2 : p ≠ 2)
    [Fintype (GL2 p n)] [Fintype (RepresentationTheory.FiniteFieldMatrixCharacterValues.distinguishedMatrixSubgroup p n)]
    [DecidablePred (auxiliaryPredicate p n)] :
    (Finset.univ.filter (fun g : GL2 p n =>
      auxiliaryPredicate p n g)).card =
    2 * Fintype.card ↥(RepresentationTheory.FiniteFieldMatrixCharacterValues.distinguishedMatrixSubgroup p n) := by
  classical
  haveI : Fintype (GaloisField p n) := Fintype.ofFinite _
  
  set N := Finset.univ.filter (fun g : GL2 p n => auxiliaryPredicate p n g)
  set K := Finset.univ.filter (fun g : GL2 p n => g ∈ RepresentationTheory.FiniteFieldMatrixCharacterValues.distinguishedMatrixSubgroup p n)
  set σK := Finset.univ.filter (fun g : GL2 p n =>
    ∃ α : (GaloisField p (2 * n))ˣ,
      g = auxiliaryElement p n * RepresentationTheory.FiniteFieldMatrixCharacterValues.quadraticFieldUnitsToMatrixUnits p n α)
  
  have hN_eq : N = K ∪ σK := by
    ext g; simp only [Finset.mem_union, Finset.mem_filter, Finset.mem_univ, true_and, N, K, σK]
    constructor
    · intro hg
      exact mem_auxiliarySet_or_exists_auxiliaryElement_mul_of_auxiliaryPredicate p n hn hp2 g hg
    · rintro (hk | ⟨α, rfl⟩)
      · exact auxiliaryPredicate_of_mem p n g hk
      · exact auxiliaryPredicate_auxiliaryElement_mul_of_mem p n hn
          (RepresentationTheory.FiniteFieldMatrixCharacterValues.quadraticFieldUnitsToMatrixUnits p n α) ⟨α, rfl⟩
  
  have hKσK_disj : Disjoint K σK := by
    rw [Finset.disjoint_filter]
    intro g _ hgK ⟨α, hgα⟩
    have : auxiliaryElement p n ∈ RepresentationTheory.FiniteFieldMatrixCharacterValues.distinguishedMatrixSubgroup p n := by
      obtain ⟨β, hβ⟩ := hgK
      rw [hgα] at hβ
      have : auxiliaryElement p n =
          RepresentationTheory.FiniteFieldMatrixCharacterValues.quadraticFieldUnitsToMatrixUnits p n β * (RepresentationTheory.FiniteFieldMatrixCharacterValues.quadraticFieldUnitsToMatrixUnits p n α)⁻¹ := by
        rw [hβ]; group
      rw [this]; exact ⟨β * α⁻¹, by rw [map_mul, map_inv]⟩
    exact auxiliaryElement_not_mem_auxiliarySet p n hn this
  
  have hK_card : K.card = Fintype.card ↥(RepresentationTheory.FiniteFieldMatrixCharacterValues.distinguishedMatrixSubgroup p n) := by
    simp only [K, ← Fintype.card_subtype]
  
  have hσK_card : σK.card = Fintype.card ↥(RepresentationTheory.FiniteFieldMatrixCharacterValues.distinguishedMatrixSubgroup p n) := by
    
    set σ := auxiliaryElement p n
    have hσK_eq : σK = K.map ⟨(σ * ·), mul_right_injective σ⟩ := by
      ext g; simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_map,
        Function.Embedding.coeFn_mk, σK, K]
      constructor
      · rintro ⟨α, rfl⟩
        exact ⟨RepresentationTheory.FiniteFieldMatrixCharacterValues.quadraticFieldUnitsToMatrixUnits p n α, ⟨α, rfl⟩, rfl⟩
      · rintro ⟨k, ⟨α, rfl⟩, rfl⟩
        exact ⟨α, rfl⟩
    rw [hσK_eq, Finset.card_map, hK_card]
  
  rw [hN_eq, Finset.card_union_of_disjoint hKσK_disj, hK_card, hσK_card, two_mul]

end Normalizer

end RepresentationTheory.GaloisFieldAuxiliary

