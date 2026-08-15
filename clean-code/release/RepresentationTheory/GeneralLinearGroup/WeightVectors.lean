/-
Copyright (c) 2026 mathlib-initiative. All rights reserved.
Released under Apache 2.0 license as described in the file LICENCE.
Authors: mathlib-initiative
-/

import RepresentationTheory.GeneralLinearGroup.PolynomialTransforms
import RepresentationTheory.LinearEquivCompatibility
import RepresentationTheory.Auxiliary.GeneralLinearGroupPolynomialEvaluation
import RepresentationTheory.Auxiliary.GeneralLinearPolynomialRealization

/-!
# Weight vectors for general linear group representations
-/

noncomputable section

namespace RepresentationTheory.GeneralLinearGroup.WeightVectors

open RepresentationTheory.Auxiliary.GeneralLinearPolynomialRealization
open RepresentationTheory.Auxiliary.GeneralLinearGroupPolynomialEvaluation
open RepresentationTheory.AuxiliaryCharacter
open RepresentationTheory.AuxiliaryModuleData
open RepresentationTheory.AuxiliaryWeightSpaces.Duality
open RepresentationTheory.Determinants.FiniteNatFamilyTransforms
open RepresentationTheory.GeneralLinear.AuxiliaryDecomposition
open RepresentationTheory.GeneralLinear.AuxiliaryRepresentations
open RepresentationTheory.GeneralLinearGroup.Auxiliary
open RepresentationTheory.GeneralLinearGroup.PolynomialQuotientRepresentation
open RepresentationTheory.GeneralLinearGroup.PolynomialTransforms
open RepresentationTheory.GeneralLinearGroup.WeightCharacter
open RepresentationTheory.LinearEquivCompatibility
open RepresentationTheory.Representation.DualCompatibility
open RepresentationTheory.SymmetricPolynomials.Alternant

attribute [local instance]
  RepresentationTheory.GeneralLinearGroup.WeightCharacter.schurSubmoduleAddCommGroup

variable {k : Type} [Field k] [IsAlgClosed k] [CharZero k]

omit [CharZero k] in

/-- If the displayed basis vectors scale by the prescribed coordinate exponents, the supremum of the displayed indexed family is top. -/
theorem supremum_indexed_family_eq_top_of_diagonal_basis (n d : ℕ)
    (M : FDRep k (Matrix.GeneralLinearGroup (Fin n) k))
    (b : Module.Basis (Fin d) k M) (wt : Fin d → Fin n → ℕ)
    (hb : ∀ (c : Fin d) (i : Fin n) (t : kˣ),
        M.ρ (diagonalUnit k n i t) (b c) = ((t : k) ^ wt c i) • b c) :
    ⨆ (μ : Fin n →₀ ℕ), weightSpace k n M (fun i => μ i) = ⊤ := by
  classical
  rw [eq_top_iff, ← b.span_eq, Submodule.span_le]
  rintro _ ⟨c, rfl⟩
  set μc : Fin n →₀ ℕ := Finsupp.equivFunOnFinite.symm (wt c) with hμc
  have hμc_apply : ∀ i, μc i = wt c i := fun i => rfl
  have hmem : b c ∈ weightSpace k n M (fun i => μc i) := by
    simp only [weightSpace, Submodule.mem_iInf, LinearMap.mem_ker, LinearMap.sub_apply,
      LinearMap.smul_apply, LinearMap.id_coe, id_eq, sub_eq_zero]
    intro i t
    rw [hb c i t, hμc_apply]
  exact SetLike.mem_coe.mpr (Submodule.mem_iSup_of_mem μc hmem)

omit [IsAlgClosed k] [CharZero k] in

/-- The given representation property is preserved by the displayed representation transformation. -/
theorem property_preserved_by_representation_transformation {Y : Type} [AddCommGroup Y] [Module k Y]
    [Module.Finite k Y] (n m : ℕ)
    (ρ : Representation k (Matrix.GeneralLinearGroup (Fin n) k) Y)
    (h : HasAuxiliaryMapProperty n ρ) :
    HasAuxiliaryMapProperty n
      (twistByCharacter (generalLinearGroupToUnits k n ^ ((m : ℕ) : ℤ)) ρ) := by
  induction m with
  | zero =>
    have heq : twistByCharacter (generalLinearGroupToUnits k n ^ ((0 : ℕ) : ℤ)) ρ = ρ := by
      ext g v
      change (((generalLinearGroupToUnits k n ^ (0 : ℤ)) g : kˣ) : k) • ρ g v = ρ g v
      rw [MonoidHom.zpow_apply, zpow_zero, Units.val_one, one_smul]
    rw [heq]; exact h
  | succ m ih =>
    have hfun : (twistByCharacter (generalLinearGroupToUnits k n ^ (((m + 1 : ℕ)) : ℤ)) ρ :
          Matrix.GeneralLinearGroup (Fin n) k → Y →ₗ[k] Y)
        = fun g => ((generalLinearGroupToUnits k n) g : k)
            • (twistByCharacter (generalLinearGroupToUnits k n ^ ((m : ℕ) : ℤ)) ρ) g := by
      funext g
      ext v
      simp only [twistByCharacter_apply, LinearMap.smul_apply, MonoidHom.zpow_apply]
      rw [show (((m + 1 : ℕ)) : ℤ) = ((m : ℕ) : ℤ) + 1 by push_cast; ring,
        zpow_add_one, Units.val_mul, mul_comm, mul_smul]
    rw [hfun]
    exact ih.auxiliary_det_smul

set_option synthInstance.maxHeartbeats 80000 in

/-- Under the displayed componentwise bound, there exists a map from the displayed transformation of the dual satisfying the shown commuting equation for every group element and dual vector. -/
theorem nonempty_intertwining_map_from_transformed_dual (n : ℕ) (lam : auxiliaryIndex n)
    (k : Type) [Field k] [IsAlgClosed k] [CharZero k] (s : ℕ)
    (hs : ∀ i, lam.toNatAt i ≤ s + lam.toNat) :
    Nonempty
      { e : Module.Dual k (auxiliaryFamily n lam k) ≃ₗ[k]
            schurSubmodule k n (finiteNatFamilyTransform n lam.toNatAt (s + lam.toNat)) //
        ∀ (g : Matrix.GeneralLinearGroup (Fin n) k) (v : Module.Dual k (auxiliaryFamily n lam k)),
          e (twistByCharacter (generalLinearGroupToUnits k n ^ s) ((generalLinearRepresentationOnAuxiliarySpaceAlt n lam k).dual) g v)
            = schurSubmoduleRepresentation k n (finiteNatFamilyTransform n lam.toNatAt (s + lam.toNat)) g (e v) } := by
  classical
  set lz := lam.toNatAt with hlz_def
  have hlz : Antitone lz := lam.toNatWeight_antitone
  set m : ℕ := s + lam.toNat with hm_def
  set ν : Fin n → ℕ := finiteNatFamilyTransform n lz m with hν_def
  have hν : Antitone ν := finiteNatFamilyTransform_antitone n lz hlz m

  set M : FDRep k (Matrix.GeneralLinearGroup (Fin n) k) :=
    FDRep.of (twistByCharacter (generalLinearGroupToUnits k n ^ s) ((generalLinearRepresentationOnAuxiliarySpaceAlt n lam k).dual)) with hM_def

  obtain ⟨d, v, wt, hv⟩ := exists_auxiliary_weight_vector_data
    (schurRepresentation k n lz) (auxiliarySup_eq_top_for_auxiliaryRepresentation k n lz)

  have hvℤ : ∀ (c : Fin d) (i : Fin n) (t : kˣ),
      ((schurRepresentation k n lz).ρ) (diagonalUnit k n i t) (v c)
        = ((t ^ (wt c i : ℤ) : kˣ) : k) • v c := by
    intro c i t
    rw [Units.val_zpow_eq_zpow_val, zpow_natCast]
    exact hv c i t

  have hbound : ∀ (c : Fin d) (i : Fin n), wt c i ≤ m := by
    intro c i
    set μc : Fin n →₀ ℕ := Finsupp.equivFunOnFinite.symm (wt c) with hμc
    have hμc_apply : ∀ j, μc j = wt c j := fun j => rfl
    have hmem : v c ∈ weightSpace k n (schurRepresentation k n lz) (fun j => μc j) := by
      simp only [weightSpace, Submodule.mem_iInf, LinearMap.mem_ker, LinearMap.sub_apply,
        LinearMap.smul_apply, LinearMap.id_coe, id_eq, sub_eq_zero]
      intro j t
      rw [hv c j t, hμc_apply]
    have hne : weightSpace k n (schurRepresentation k n lz) (fun j => μc j) ≠ ⊥ := by
      intro hbot
      rw [hbot] at hmem
      exact v.ne_zero c (by rwa [Submodule.mem_bot] at hmem)
    have hfr : 0 < Module.finrank k
        (weightSpace k n (schurRepresentation k n lz) (fun j => μc j)) :=
      Module.finrank_pos_iff.mpr (Submodule.nontrivial_iff_ne_bot.mpr hne)
    have hcoeff : (partitionPolynomial n lz).coeff μc ≠ 0 := by
      rw [← finrank_weightSpace_schurRepresentation k n lz hlz μc]
      exact_mod_cast hfr.ne'
    have hle := exponent_le_of_polynomial_coeff_ne_zero n lz m hs hcoeff i
    rwa [hμc_apply] at hle

  have hMeigen : ∀ (c : Fin d) (i : Fin n) (t : kˣ),
      M.ρ (diagonalUnit k n i t) (v.dualBasis c)
        = ((t : k) ^ (m - wt c i)) • v.dualBasis c := by
    intro c i t

    change (twistByCharacter (generalLinearGroupToUnits k n ^ s)
        (Representation.dual (twistByCharacter (generalLinearGroupToUnits k n ^ (-(lam.toNat : ℤ)))
          ((schurRepresentation k n lz).ρ)))) (diagonalUnit k n i t) (v.dualBasis c)
      = ((t : k) ^ (m - wt c i)) • v.dualBasis c
    rw [dual_construction_eq_construction_inv_dual, twistByCharacter_mul, pow_mul_inv_pow_neg_shift_eq_pow_add_shift,
      twistByCharacter_apply, pow_apply_indexed_element_eq_pow k n _ i t,
      dualBasis_hasNegatedAuxiliaryWeight k n d ((schurRepresentation k n lz).ρ) v (fun c i => (wt c i : ℤ)) hvℤ c i t,
      smul_smul, ← Units.val_mul, ← zpow_add]
    congr 1
    rw [show ((m : ℕ) : ℤ) + -(wt c i : ℤ) = (((m - wt c i : ℕ)) : ℤ) by
          have := hbound c i; omega,
      Units.val_zpow_eq_zpow_val, zpow_natCast]

  have h_span : ⨆ (μ : Fin n →₀ ℕ), weightSpace k n M (fun i => μ i) = ⊤ :=
    supremum_indexed_family_eq_top_of_diagonal_basis n d M v.dualBasis
      (fun c i => m - wt c i) hMeigen

  have hσalg : HasAuxiliaryMapProperty n (schurSubmoduleRepresentation k n lz) :=
    auxiliaryFDRep_property (k := k) n lz
  have halg : HasAuxiliaryMapProperty n M.ρ := by

    change HasAuxiliaryMapProperty n
      (twistByCharacter (generalLinearGroupToUnits k n ^ s)
        (Representation.dual (twistByCharacter (generalLinearGroupToUnits k n ^ (-(lam.toNat : ℤ)))
          (schurSubmoduleRepresentation k n lz))))
    rw [dual_construction_eq_construction_inv_dual, twistByCharacter_mul, pow_mul_inv_pow_neg_shift_eq_pow_add_shift]
    exact property_preserved_by_representation_transformation n m _
      (HasAuxiliaryMapProperty.auxiliary_dual (schurSubmoduleRepresentation k n lz) hσalg)

  have h_char : weightCharacter k n M = partitionPolynomial n ν := by
    rw [hM_def]
    exact polynomial_of_transformed_dual_eq_indexed_polynomial n lam k s hs

  have h_dim : Module.finrank k M = Module.finrank k (schurRepresentation k n ν) := by
    have h₂_top : ⨆ (μ : Fin n →₀ ℕ),
        weightSpace k n (schurRepresentation k n ν) (fun i => μ i) = ⊤ :=
      auxiliarySup_eq_top_for_auxiliaryRepresentation k n ν
    have h_char_eq : weightCharacter k n M = weightCharacter k n (schurRepresentation k n ν) :=
      h_char.trans (weightCharacter_schurRepresentation_eq k n ν hν).symm
    exact finrank_eq_of_auxiliaryPolynomial_eq k n M (schurRepresentation k n ν) h_span h₂_top h_char_eq

  obtain ⟨iso⟩ := iso_of_auxiliaryConditions_and_finrank_eq k n ν hν M halg h_span h_char h_dim

  exact ⟨FDRep.isoToLinearEquiv iso,
    isCompatible_isoToLinearEquiv (twistByCharacter (generalLinearGroupToUnits k n ^ s) ((generalLinearRepresentationOnAuxiliarySpaceAlt n lam k).dual))
      (schurSubmoduleRepresentation k n ν) iso⟩

end RepresentationTheory.GeneralLinearGroup.WeightVectors
