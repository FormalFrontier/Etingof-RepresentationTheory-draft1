/-
Copyright (c) 2026 mathlib-initiative. All rights reserved.
Released under Apache 2.0 license as described in the file LICENCE.
Authors: mathlib-initiative
-/

import RepresentationTheory.GeneralLinear.AuxiliaryRepresentations
import RepresentationTheory.Representation.DualCompatibility
import RepresentationTheory.AuxiliaryWeightSpaces.Duality
import RepresentationTheory.Determinants.FiniteNatFamilyTransforms
import RepresentationTheory.GeneralLinear.AuxiliaryDecomposition

noncomputable section

namespace RepresentationTheory.GeneralLinearGroup.PolynomialTransforms

open RepresentationTheory.Auxiliary.GeneralLinearPolynomialRealization
open RepresentationTheory.AuxiliaryModuleData
open RepresentationTheory.AuxiliaryWeightSpaces.Duality
open RepresentationTheory.Determinants.FiniteNatFamilyTransforms
open RepresentationTheory.GeneralLinear.AuxiliaryDecomposition
open RepresentationTheory.GeneralLinear.AuxiliaryRepresentations
open RepresentationTheory.GeneralLinearGroup.PolynomialQuotientRepresentation
open RepresentationTheory.GeneralLinearGroup.WeightCharacter
open RepresentationTheory.Representation.DualCompatibility
open RepresentationTheory.SymmetricPolynomials.Alternant

attribute [local instance]
  RepresentationTheory.GeneralLinearGroup.WeightCharacter.schurSubmoduleAddCommGroup

section TwistShift

variable {k : Type*} [Field k] {N : ℕ} {V : Type*} [AddCommGroup V] [Module k V]

/-- If the homomorphism has the prescribed values on the displayed indexed elements, the displayed family for the transformed representation at an index equals the original family at the coordinatewise shifted index. -/
theorem indexed_family_transformed_representation_eq_shift
    (c : Matrix.GeneralLinearGroup (Fin N) k →* kˣ)
    (ρ : Representation k (Matrix.GeneralLinearGroup (Fin N) k) V)
    (sh : Fin N → ℤ)
    (hc : ∀ (i : Fin N) (t : kˣ), c (diagonalUnit k N i t) = t ^ sh i)
    (w : Fin N → ℤ) :
    integerTupleSubmodule k N (twistByCharacter c ρ) w
      = integerTupleSubmodule k N ρ (fun i => w i - sh i) := by
  simp only [integerTupleSubmodule]
  refine iInf_congr fun i => iInf_congr fun t => ?_
  have hCT : (twistByCharacter c ρ) (diagonalUnit k N i t)
      = ((c (diagonalUnit k N i t) : kˣ) : k) • ρ (diagonalUnit k N i t) := rfl
  have hexp : sh i + (w i - sh i) = w i := by omega
  have hsc : (((t ^ sh i : kˣ) : k)) * (((t ^ (w i - sh i) : kˣ) : k))
      = ((t ^ w i : kˣ) : k) := by
    rw [← Units.val_mul, ← zpow_add, hexp]
  have factored : (twistByCharacter c ρ) (diagonalUnit k N i t)
        - (((t ^ w i : kˣ) : k)) • LinearMap.id
      = ((t ^ sh i : kˣ) : k) •
          (ρ (diagonalUnit k N i t) - (((t ^ (w i - sh i) : kˣ) : k)) • LinearMap.id) := by
    rw [hCT, hc i t, smul_sub, smul_smul, hsc]
  rw [factored, LinearMap.ker_smul _ _ (Units.ne_zero (t ^ sh i))]

end TwistShift

/-- Evaluating the indicated integer power of the displayed homomorphism on the element indexed by a coordinate and a unit gives the corresponding power of that unit. -/
theorem pow_apply_indexed_element_eq_pow (k : Type*) [Field k] (N : ℕ) (z : ℤ) (i : Fin N) (t : kˣ) :
    (generalLinearGroupToUnits k N ^ z) (diagonalUnit k N i t) = t ^ z := by
  rw [MonoidHom.zpow_apply]
  congr 1

  apply Units.ext
  change Matrix.det (diagonalUnit k N i t).val = (t : k)
  simp only [diagonalUnit, Matrix.det_diagonal, Finset.prod_update_of_mem (Finset.mem_univ i),
    Pi.one_apply]
  simp [Finset.prod_eq_one (fun j _ => rfl)]

/-- Multiplying the given power of the displayed object by the inverse of its negative-shift power yields its power at the sum with the shift. -/
theorem pow_mul_inv_pow_neg_shift_eq_pow_add_shift (n : ℕ) (lam : auxiliaryIndex n) (k : Type*)
    [Field k] [IsAlgClosed k] (s : ℕ) :
    (generalLinearGroupToUnits k n ^ s) * (generalLinearGroupToUnits k n ^ (-(lam.toNat : ℤ)))⁻¹
      = generalLinearGroupToUnits k n ^ ((s + lam.toNat : ℕ) : ℤ) := by
  rw [show (generalLinearGroupToUnits k n ^ (-(lam.toNat : ℤ)))⁻¹ = generalLinearGroupToUnits k n ^ (lam.toNat : ℤ) from by
        ext g
        simp only [MonoidHom.inv_apply, MonoidHom.zpow_apply, zpow_neg, inv_inv],
    ← zpow_natCast (generalLinearGroupToUnits k n) s, ← zpow_add, Nat.cast_add]

/-- The coefficient at the given exponent of the polynomial attached to the displayed transformation of the dual equals the scalar cast of the finrank of the displayed subtype. -/
theorem coeff_polynomial_of_transformed_dual_eq_finrank (n : ℕ) (lam : auxiliaryIndex n)
    (k : Type) [Field k] [IsAlgClosed k] [CharZero k] (s : ℕ) (μ : Fin n →₀ ℕ) :
    (weightCharacter k n
        (FDRep.of (twistByCharacter (generalLinearGroupToUnits k n ^ s)
          ((generalLinearRepresentationOnAuxiliarySpaceAlt n lam k).dual)))).coeff μ
      = (Module.finrank k (integerTupleSubmodule (V := schurSubmodule k n lam.toNatAt) k n
          (schurSubmoduleRepresentation k n lam.toNatAt)
          (fun i => ((s + lam.toNat : ℕ) : ℤ) - (μ i : ℤ))) : ℚ) := by
  change (weightCharacter k n
      (FDRep.of (twistByCharacter (generalLinearGroupToUnits k n ^ s)
        (Representation.dual (twistByCharacter (generalLinearGroupToUnits k n ^ (-(lam.toNat : ℤ)))
          (schurSubmoduleRepresentation k n lam.toNatAt)))))).coeff μ = _

  obtain ⟨d, v, wt, hv⟩ := exists_auxiliary_weight_vector_data
    (schurRepresentation k n lam.toNatAt)
    (auxiliarySup_eq_top_for_auxiliaryRepresentation k n lam.toNatAt)

  have hvℤ : ∀ (c : Fin d) (i : Fin n) (t : kˣ),
      (schurSubmoduleRepresentation k n lam.toNatAt) (diagonalUnit k n i t) (v c)
        = ((t ^ (wt c i : ℤ) : kˣ) : k) • v c := by
    intro c i t
    rw [Units.val_zpow_eq_zpow_val, zpow_natCast]
    exact hv c i t
  rw [coeff_weightCharacter,
    natAuxiliaryWeightSpace_eq_intAuxiliaryWeightSpace k n _ (fun i => μ i),
    FDRep.of_ρ', dual_construction_eq_construction_inv_dual, twistByCharacter_mul,
    pow_mul_inv_pow_neg_shift_eq_pow_add_shift,
    indexed_family_transformed_representation_eq_shift _ _ (fun _ => ((s + lam.toNat : ℕ) : ℤ))
      (fun i t => pow_apply_indexed_element_eq_pow k n _ i t),
    finrank_dualAuxiliaryWeightSpace k n d (schurSubmoduleRepresentation k n lam.toNatAt) v
      (fun c i => (wt c i : ℤ)) hvℤ (fun i => (μ i : ℤ) - ((s + lam.toNat : ℕ) : ℤ))]

  rw [show (fun i => -((μ i : ℤ) - ((s + lam.toNat : ℕ) : ℤ)))
        = (fun i : Fin n => ((s + lam.toNat : ℕ) : ℤ) - (μ i : ℤ)) from by funext i; omega]

/-- For an antitone natural-valued family, the scalar cast of the finrank of the displayed subtype equals the coefficient at the corresponding finitely supported exponent. -/
theorem finrank_displayed_subtype_eq_polynomial_coeff (k : Type) [Field k] [IsAlgClosed k]
    [CharZero k] (n : ℕ) (lz : Fin n → ℕ) (hlz : Antitone lz) (w' : Fin n → ℕ) :
    (Module.finrank k (integerTupleSubmodule (V := schurSubmodule k n lz) k n
        (schurSubmoduleRepresentation k n lz)
        (fun i => (w' i : ℤ))) : ℚ)
      = (partitionPolynomial n lz).coeff (Finsupp.equivFunOnFinite.symm w') := by
  have h := finrank_weightSpace_schurRepresentation k n lz hlz (Finsupp.equivFunOnFinite.symm w')
  rw [natAuxiliaryWeightSpace_eq_intAuxiliaryWeightSpace k n (schurRepresentation k n lz)
      (Finsupp.equivFunOnFinite.symm w')] at h
  simp only [schurRepresentation, FDRep.of_ρ'] at h
  rw [← h]
  rfl

/-- If one coordinate of the integer-valued index is negative, the displayed subtype has finrank zero. -/
theorem finrank_subtype_eq_zero_of_neg_coordinate (k : Type) [Field k] [IsAlgClosed k]
    [CharZero k] (n : ℕ) (lz : Fin n → ℕ) (w : Fin n → ℤ) (i₀ : Fin n) (hi₀ : w i₀ < 0) :
    Module.finrank k (integerTupleSubmodule (V := schurSubmodule k n lz) k n
      (schurSubmoduleRepresentation k n lz) w) = 0 := by
  obtain ⟨d, v, wt, hv⟩ := exists_auxiliary_weight_vector_data (schurRepresentation k n lz)
    (auxiliarySup_eq_top_for_auxiliaryRepresentation k n lz)
  have hvℤ : ∀ (c : Fin d) (i : Fin n) (t : kˣ),
      (schurSubmoduleRepresentation k n lz) (diagonalUnit k n i t) (v c)
        = ((t ^ (wt c i : ℤ) : kˣ) : k) • v c := by
    intro c i t
    rw [Units.val_zpow_eq_zpow_val, zpow_natCast]
    exact hv c i t
  rw [finrank_auxiliaryWeightSpace_eq_card k n d (schurSubmoduleRepresentation k n lz) v
      (fun c i => (wt c i : ℤ)) hvℤ w, Finset.card_eq_zero, Finset.filter_eq_empty_iff]
  intro c _ hc
  have h : ((wt c i₀ : ℤ)) = w i₀ := congrFun hc i₀
  omega

section DegreeBound

open _root_.MvPolynomial

private lemma degreeOf_alternant_le (N : ℕ) (e : Fin N → ℕ) (B : ℕ)
    (hB : ∀ j, e j ≤ B) (t : Fin N) :
    (alternantMatrix N e).det.degreeOf t ≤ B := by
  rw [Matrix.det_apply]
  refine le_trans (MvPolynomial.degreeOf_sum_le t _ _) (Finset.sup_le ?_)
  intro σ _
  have hprod : (∏ i, alternantMatrix N e (σ i) i)
      = monomial (Finsupp.equivFunOnFinite.symm (e ∘ ⇑σ.symm)) (1 : ℚ) := by
    rw [show (∏ i, alternantMatrix N e (σ i) i)
          = ∏ i, (X (σ i) : MvPolynomial (Fin N) ℚ) ^ e i from rfl,
      show (∏ i, (X (σ i) : MvPolynomial (Fin N) ℚ) ^ e i)
          = ∏ i, X i ^ (e (σ.symm i)) from Fintype.prod_equiv σ _ _ (fun _ => by simp)]
    exact prod_X_pow_eq_monomial _
  rw [hprod, Units.smul_def, ← Int.cast_smul_eq_zsmul ℚ, smul_eq_C_mul]
  refine le_trans (degreeOf_C_mul_le _ t _) ?_
  rw [degreeOf_monomial_eq _ t one_ne_zero]
  have : (Finsupp.equivFunOnFinite.symm (e ∘ ⇑σ.symm)) t = e (σ.symm t) := by
    simp [Finsupp.equivFunOnFinite]
  rw [this]; exact hB _

private lemma vandermondeExps_strictAnti (N : ℕ) : StrictAnti (staircaseExponents N) := by
  intro i j hij
  simp only [staircaseExponents]
  have hj := j.isLt
  have : (i : ℕ) < (j : ℕ) := hij
  omega

private lemma vandermonde_degreeOf_ge (N : ℕ) (t : Fin N) :
    N - 1 ≤ (alternantMatrix N (staircaseExponents N)).det.degreeOf t := by
  have hN : 0 < N := lt_of_le_of_lt (Nat.zero_le _) t.isLt
  set i0 : Fin N := ⟨0, hN⟩ with hi0
  set σ : Equiv.Perm (Fin N) := Equiv.swap i0 t with hσ
  have hcoeff1 : MvPolynomial.coeff
      (Finsupp.equivFunOnFinite.symm (staircaseExponents N))
        (alternantMatrix N (staircaseExponents N)).det = 1 := by
    rw [coeff_det_alternantMatrix_of_strictAnti (vandermondeExps_strictAnti N) (vandermondeExps_strictAnti N),
      if_pos rfl]
  set d : Fin N →₀ ℕ :=
    Finsupp.mapDomain σ (Finsupp.equivFunOnFinite.symm (staircaseExponents N)) with hd
  have hrename : MvPolynomial.coeff d
      (MvPolynomial.rename σ (alternantMatrix N (staircaseExponents N)).det) = 1 := by
    rw [hd, MvPolynomial.coeff_rename_mapDomain σ σ.injective _ _, hcoeff1]
  rw [rename_det_alternantMatrix, MvPolynomial.coeff_smul] at hrename
  have hne : MvPolynomial.coeff d (alternantMatrix N (staircaseExponents N)).det ≠ 0 := by
    intro hzero; rw [hzero, smul_zero] at hrename; exact one_ne_zero hrename.symm
  have hsymm : σ.symm t = i0 := by rw [hσ, Equiv.symm_swap, Equiv.swap_apply_right]
  have hdt : d t = N - 1 := by
    have h1 : d t = staircaseExponents N i0 := by
      rw [hd, Finsupp.mapDomain_equiv_apply, hsymm, Finsupp.coe_equivFunOnFinite_symm]
    rw [h1]; simp only [staircaseExponents, hi0, Fin.val_mk, Nat.sub_zero]
  calc N - 1 = d t := hdt.symm
    _ ≤ (alternantMatrix N (staircaseExponents N)).det.degreeOf t :=
        MvPolynomial.monomial_le_degreeOf t (MvPolynomial.mem_support_iff.mpr hne)

/-- A coordinatewise bound on the indexing family bounds the degree of the displayed polynomial in every variable. -/
theorem degree_of_polynomial_le_of_index_le (N : ℕ) (lz : Fin N → ℕ) (m : ℕ)
    (hs : ∀ j, lz j ≤ m) (t : Fin N) :
    (partitionPolynomial N lz).degreeOf t ≤ m := by
  by_cases hsp : partitionPolynomial N lz = 0
  · rw [hsp, MvPolynomial.degreeOf_zero]; exact Nat.zero_le _
  · have hΔ := Auxiliary.det_ne_zero N
    have hmul : (partitionPolynomial N lz).degreeOf t
          + (alternantMatrix N (staircaseExponents N)).det.degreeOf t
        = (alternantMatrix N (addStaircase N lz)).det.degreeOf t := by
      rw [← MvPolynomial.degreeOf_mul_eq hsp hΔ, partitionPolynomial_mul_det_staircase]
    have ha : (alternantMatrix N (addStaircase N lz)).det.degreeOf t ≤ m + (N - 1) := by
      refine degreeOf_alternant_le N _ _ (fun j => ?_) t
      simp only [addStaircase]; have := hs j; have : N - 1 - (j : ℕ) ≤ N - 1 := Nat.sub_le _ _
      omega
    have hΔge : N - 1 ≤ (alternantMatrix N (staircaseExponents N)).det.degreeOf t :=
      vandermonde_degreeOf_ge N t
    have hN : 0 < N := lt_of_le_of_lt (Nat.zero_le _) t.isLt
    omega

/-- If every entry of the indexing family is at most a bound, each coordinate of an exponent with nonzero coefficient in the displayed polynomial is at most that bound. -/
theorem exponent_le_of_polynomial_coeff_ne_zero (N : ℕ) (lz : Fin N → ℕ) (m : ℕ)
    (hs : ∀ j, lz j ≤ m) {c : Fin N →₀ ℕ}
    (hc : (partitionPolynomial N lz).coeff c ≠ 0) (i : Fin N) : c i ≤ m :=
  le_trans (MvPolynomial.monomial_le_degreeOf i (MvPolynomial.mem_support_iff.mpr hc))
    (degree_of_polynomial_le_of_index_le N lz m hs i)

end DegreeBound

section BoxReversal

open _root_.MvPolynomial

/-- A map on finitely supported natural exponent vectors, parameterized by the dimension and a natural number. -/
def exponent_index_map (N D : ℕ) (c : Fin N →₀ ℕ) : Fin N →₀ ℕ :=
  Finsupp.equivFunOnFinite.symm (fun i => D - c i)

/-- At each coordinate, the exponent index map is the truncated difference of the parameter and the input exponent. -/
@[simp] lemma exponent_index_map_apply (N D : ℕ) (c : Fin N →₀ ℕ) (i : Fin N) :
    exponent_index_map N D c i = D - c i := rfl

/-- A rational linear self-map of multivariate polynomials, parameterized by the number of variables and a natural number. -/
noncomputable def polynomial_index_map (N D : ℕ) :
    MvPolynomial (Fin N) ℚ →ₗ[ℚ] MvPolynomial (Fin N) ℚ :=
  (Finsupp.lsum ℚ (fun e => monomial (exponent_index_map N D e))).comp
    (AddMonoidAlgebra.coeffLinearEquiv ℚ).toLinearMap

/-- The polynomial index map sends a monomial to the monomial with mapped exponent vector and unchanged rational coefficient. -/
@[simp] lemma polynomial_index_map_monomial (N D : ℕ) (c : Fin N →₀ ℕ) (a : ℚ) :
    polynomial_index_map N D (monomial c a) = monomial (exponent_index_map N D c) a := by
  simp [polynomial_index_map, MvPolynomial.monomial, AddMonoidAlgebra.coeffLinearEquiv_apply]

/-- The polynomial index map is the sum over the original support of monomials at the mapped exponent vectors with the original coefficients. -/
lemma polynomial_index_map_eq_support_sum (N D : ℕ) (P : MvPolynomial (Fin N) ℚ) :
    polynomial_index_map N D P = ∑ c ∈ P.support, monomial (exponent_index_map N D c) (P.coeff c) := by
  conv_lhs => rw [P.as_sum]
  rw [map_sum]
  exact Finset.sum_congr rfl (fun c _ => polynomial_index_map_monomial N D c _)

/-- For exponent vectors bounded by their respective parameters, mapping their sum at the sum of the parameters equals the sum of the separately mapped vectors. -/
lemma exponent_index_map_add (N D E : ℕ) (c d : Fin N →₀ ℕ)
    (hc : ∀ i, c i ≤ D) (hd : ∀ i, d i ≤ E) :
    exponent_index_map N (D + E) (c + d) = exponent_index_map N D c + exponent_index_map N E d := by
  apply Finsupp.ext; intro i
  rw [Finsupp.add_apply, exponent_index_map_apply, exponent_index_map_apply, exponent_index_map_apply, Finsupp.add_apply]
  have := hc i; have := hd i; omega

/-- For polynomials with coordinatewise bounded supports, the map at the sum of the bounds sends their product to the product of their respective mapped polynomials. -/
lemma polynomial_index_map_mul (N D E : ℕ) (P Q : MvPolynomial (Fin N) ℚ)
    (hP : ∀ c ∈ P.support, ∀ i, c i ≤ D) (hQ : ∀ d ∈ Q.support, ∀ i, d i ≤ E) :
    polynomial_index_map N (D + E) (P * Q) = polynomial_index_map N D P * polynomial_index_map N E Q := by
  have key : polynomial_index_map N (D + E) (P * Q)
      = ∑ c ∈ P.support, ∑ d ∈ Q.support,
          monomial (exponent_index_map N D c) (P.coeff c) * monomial (exponent_index_map N E d) (Q.coeff d) := by
    conv_lhs => rw [P.as_sum, Q.as_sum]
    rw [Finset.sum_mul_sum, map_sum]
    refine Finset.sum_congr rfl (fun c hc => ?_)
    rw [map_sum]
    refine Finset.sum_congr rfl (fun d hd => ?_)
    rw [monomial_mul, polynomial_index_map_monomial, exponent_index_map_add N D E c d (hP c hc) (hQ d hd), ← monomial_mul]
  rw [key, polynomial_index_map_eq_support_sum, polynomial_index_map_eq_support_sum, Finset.sum_mul_sum]

/-- The determinant of the displayed matrix is the sum over permutations of monomials with permuted exponent data and coefficients given by the permutation signs. -/
lemma det_matrix_eq_sum_signed_monomials (N : ℕ) (e : Fin N → ℕ) :
    (alternantMatrix N e).det
      = ∑ σ : Equiv.Perm (Fin N),
          monomial (Finsupp.equivFunOnFinite.symm (e ∘ ⇑σ.symm))
            (((Equiv.Perm.sign σ : ℤ) : ℚ)) := by
  rw [Matrix.det_apply]
  refine Finset.sum_congr rfl (fun σ _ => ?_)
  rw [show (∏ i, alternantMatrix N e (σ i) i)
        = monomial (Finsupp.equivFunOnFinite.symm (e ∘ ⇑σ.symm)) (1 : ℚ) from by
      rw [show (∏ i, alternantMatrix N e (σ i) i)
            = ∏ i, (X (σ i) : MvPolynomial (Fin N) ℚ) ^ e i from rfl,
        show (∏ i, (X (σ i) : MvPolynomial (Fin N) ℚ) ^ e i)
            = ∏ i, X i ^ (e (σ.symm i)) from Fintype.prod_equiv σ _ _ (fun _ => by simp)]
      exact prod_X_pow_eq_monomial _]
  rw [Units.smul_def, ← Int.cast_smul_eq_zsmul ℚ, smul_eq_C_mul, C_mul_monomial, mul_one]

/-- Applying the polynomial index map to the determinant of the displayed matrix replaces each entry of its exponent family by its truncated difference from the parameter. -/
lemma polynomial_index_map_apply_det (N D : ℕ) (e : Fin N → ℕ) :
    polynomial_index_map N D (alternantMatrix N e).det = (alternantMatrix N (fun j => D - e j)).det := by
  rw [det_matrix_eq_sum_signed_monomials, map_sum, det_matrix_eq_sum_signed_monomials]
  refine Finset.sum_congr rfl (fun σ _ => ?_)
  rw [polynomial_index_map_monomial]
  congr 1

/-- At the displayed parameter and exponent family, the polynomial index map sends the determinant to the same determinant multiplied by the sign of the reversing permutation. -/
lemma polynomial_index_map_apply_special_det (N : ℕ) :
    polynomial_index_map N (N - 1) (alternantMatrix N (staircaseExponents N)).det
      = (↑↑(Fin.revPerm (n := N)).sign : MvPolynomial (Fin N) ℚ)
          * (alternantMatrix N (staircaseExponents N)).det := by
  rw [polynomial_index_map_apply_det]
  have hexp : (fun j => (N - 1) - staircaseExponents N j)
      = (fun j => staircaseExponents N (Fin.rev j)) := by
    funext j; simp only [staircaseExponents, Fin.val_rev]; have := j.isLt; omega
  rw [hexp]
  have hmat : alternantMatrix N (fun j => staircaseExponents N (Fin.rev j))
      = (alternantMatrix N (staircaseExponents N)).submatrix id Fin.revPerm := by
    ext i j
    simp only [alternantMatrix, Matrix.of_apply, Matrix.submatrix_apply, id_eq, Fin.revPerm_apply]
  rw [hmat, Matrix.det_permute']

/-- When every supported exponent is coordinatewise bounded by the parameter, a coefficient after applying the polynomial index map is the corresponding reindexed coefficient inside the bound and zero outside it. -/
lemma coeff_polynomial_index_map_of_support_le (N D : ℕ) (P : MvPolynomial (Fin N) ℚ)
    (hP : ∀ c ∈ P.support, ∀ i, c i ≤ D) (μ : Fin N →₀ ℕ) :
    (polynomial_index_map N D P).coeff μ
      = if (∀ i, μ i ≤ D) then P.coeff (exponent_index_map N D μ) else 0 := by
  rw [polynomial_index_map_eq_support_sum, MvPolynomial.coeff_sum]
  simp only [MvPolynomial.coeff_monomial]
  by_cases hμ : ∀ i, μ i ≤ D
  · rw [if_pos hμ, Finset.sum_eq_single (exponent_index_map N D μ)]
    · have hinv : exponent_index_map N D (exponent_index_map N D μ) = μ := by
        apply Finsupp.ext; intro i; rw [exponent_index_map_apply, exponent_index_map_apply]; have := hμ i; omega
      rw [if_pos hinv]
    · intro c hc hcne
      rw [if_neg]
      intro heq
      apply hcne
      apply Finsupp.ext; intro i
      rw [exponent_index_map_apply]
      have h2 : (exponent_index_map N D c) i = μ i := by rw [heq]
      rw [exponent_index_map_apply] at h2
      have := hP c hc i
      omega
    · intro hnotin
      rw [MvPolynomial.notMem_support_iff.mp hnotin]
      simp
  · rw [if_neg hμ]
    apply Finset.sum_eq_zero
    intro c hc
    rw [if_neg]
    intro heq
    apply hμ
    intro i
    have h2 : (exponent_index_map N D c) i = μ i := by rw [heq]
    rw [exponent_index_map_apply] at h2
    omega

end BoxReversal

/-- A result whose formal statement could not be displayed in the evidence packet. -/
theorem auxiliary_result (n : ℕ) (lz : Fin n → ℕ) (hlz : Antitone lz) (m : ℕ)
    (hs : ∀ j, lz j ≤ m) (μ : Fin n →₀ ℕ) :
    (partitionPolynomial n (finiteNatFamilyTransform n lz m)).coeff μ
      = if _h : ∀ i, μ i ≤ m
        then (partitionPolynomial n lz).coeff (Finsupp.equivFunOnFinite.symm (fun i => m - μ i))
        else 0 := by
  have hΔ : (alternantMatrix n (staircaseExponents n)).det ≠ 0 :=
    Auxiliary.det_ne_zero n
  have hc2 : (↑↑(Fin.revPerm (n := n)).sign : MvPolynomial (Fin n) ℚ)
      * ↑↑(Fin.revPerm (n := n)).sign = 1 := by
    rcases Int.units_eq_one_or (Fin.revPerm (n := n)).sign with h | h <;> simp [h]
  have hboundS : ∀ d ∈ (partitionPolynomial n lz).support, ∀ i, d i ≤ m :=
    fun d hd i => exponent_le_of_polynomial_coeff_ne_zero n lz m hs (MvPolynomial.mem_support_iff.mp hd) i
  have hboundD : ∀ d ∈ (alternantMatrix n (staircaseExponents n)).det.support, ∀ i, d i ≤ n - 1 :=
    fun d hd i => le_trans (MvPolynomial.monomial_le_degreeOf i hd)
      (degreeOf_alternant_le n (staircaseExponents n) (n - 1)
        (fun j => by simp only [staircaseExponents]; omega) i)

  have hΔrev : (alternantMatrix n (staircaseExponents n)).det
      = (↑↑(Fin.revPerm (n := n)).sign : MvPolynomial (Fin n) ℚ)
          * polynomial_index_map n (n - 1) (alternantMatrix n (staircaseExponents n)).det := by
    rw [polynomial_index_map_apply_special_det, ← mul_assoc, hc2, one_mul]

  have hRHS : polynomial_index_map n m (partitionPolynomial n lz) * (alternantMatrix n (staircaseExponents n)).det
      = (↑↑(Fin.revPerm (n := n)).sign : MvPolynomial (Fin n) ℚ)
          * (alternantMatrix n (fun j => (m + n - 1) - addStaircase n lz j)).det := by
    have step1 : polynomial_index_map n m (partitionPolynomial n lz)
          * polynomial_index_map n (n - 1) (alternantMatrix n (staircaseExponents n)).det
        = (alternantMatrix n (fun j => (m + n - 1) - addStaircase n lz j)).det := by
      rw [← polynomial_index_map_mul n m (n - 1) (partitionPolynomial n lz)
            (alternantMatrix n (staircaseExponents n)).det hboundS hboundD,
        partitionPolynomial_mul_det_staircase, polynomial_index_map_apply_det]
      have hfe : (fun j => (m + (n - 1)) - addStaircase n lz j)
          = (fun j : Fin n => (m + n - 1) - addStaircase n lz j) := by
        funext j; have := j.isLt; omega
      rw [hfe]
    calc polynomial_index_map n m (partitionPolynomial n lz) * (alternantMatrix n (staircaseExponents n)).det
        = polynomial_index_map n m (partitionPolynomial n lz)
            * (↑↑(Fin.revPerm (n := n)).sign
                * polynomial_index_map n (n - 1) (alternantMatrix n (staircaseExponents n)).det) := by
              rw [← hΔrev]
      _ = (↑↑(Fin.revPerm (n := n)).sign : MvPolynomial (Fin n) ℚ)
            * (polynomial_index_map n m (partitionPolynomial n lz)
                * polynomial_index_map n (n - 1) (alternantMatrix n (staircaseExponents n)).det) := by ring
      _ = _ := by rw [step1]

  have hid : partitionPolynomial n (finiteNatFamilyTransform n lz m) = polynomial_index_map n m (partitionPolynomial n lz) := by
    have hIS := det_eq_reversePermSign_mul n lz m hs
    apply mul_right_cancel₀ hΔ
    rw [hRHS, hIS, ← mul_assoc, hc2, one_mul]
  rw [hid, coeff_polynomial_index_map_of_support_le n m (partitionPolynomial n lz) hboundS μ]
  by_cases hμ : ∀ i, μ i ≤ m
  · rw [dif_pos hμ, if_pos hμ]; rfl
  · rw [dif_neg hμ, if_neg hμ]

/-- Under the componentwise bound, the polynomial attached to the displayed transformation of the dual equals the displayed polynomial at the resulting natural-valued index. -/
theorem polynomial_of_transformed_dual_eq_indexed_polynomial (n : ℕ) (lam : auxiliaryIndex n)
    (k : Type) [Field k] [IsAlgClosed k] [CharZero k] (s : ℕ)
    (hs : ∀ i, lam.toNatAt i ≤ s + lam.toNat) :
    weightCharacter k n
        (FDRep.of (twistByCharacter (generalLinearGroupToUnits k n ^ s) ((generalLinearRepresentationOnAuxiliarySpaceAlt n lam k).dual)))
      = partitionPolynomial n (finiteNatFamilyTransform n lam.toNatAt (s + lam.toNat)) := by
  apply MvPolynomial.ext
  intro μ
  rw [coeff_polynomial_of_transformed_dual_eq_finrank n lam k s μ]
  set lz := lam.toNatAt with hlz_def
  set m := s + lam.toNat with hm_def
  have hlz : Antitone lz := lam.toNatWeight_antitone
  rw [auxiliary_result n lz hlz m hs μ]
  by_cases hμ : ∀ i, μ i ≤ m
  · rw [dif_pos hμ,
       show (fun i => (m : ℤ) - (μ i : ℤ)) = (fun i => ((m - μ i : ℕ) : ℤ)) from by
         funext i; have := hμ i; omega,
       finrank_displayed_subtype_eq_polynomial_coeff k n lz hlz (fun i => m - μ i)]
  · rw [dif_neg hμ]
    push Not at hμ
    obtain ⟨i₀, hi₀⟩ := hμ
    rw [finrank_subtype_eq_zero_of_neg_coordinate k n lz (fun i => (m : ℤ) - (μ i : ℤ)) i₀
      (by omega)]
    simp

end RepresentationTheory.GeneralLinearGroup.PolynomialTransforms
