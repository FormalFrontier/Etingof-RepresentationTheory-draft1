/-
Copyright (c) 2026 mathlib-initiative. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: mathlib-initiative
-/

import Mathlib
import RepresentationTheory.Auxiliary.GeneralLinearPolynomialSubrepresentations
import RepresentationTheory.GeneralLinear.AuxiliaryRepresentationFamilies
import RepresentationTheory.GeneralLinear.AuxiliaryPolynomialQuotient
import RepresentationTheory.GeneralLinear.AuxiliaryPolynomialIdentities
import RepresentationTheory.LinearAlgebra.GeneralLinearGroup.PolynomialCoefficients
import RepresentationTheory.SimpleDirectSumAndWeightDegree
import RepresentationTheory.GeneralLinear.AuxiliaryDecomposition
import RepresentationTheory.LinearEquivCompatibility
import RepresentationTheory.GeneralLinearGroup.DiagonalAction
import RepresentationTheory.GeneralLinearGroup.AuxiliaryDecomposition

open scoped TensorProduct

noncomputable section

namespace RepresentationTheory.Auxiliary.EquivariantMaps

open MvPolynomial RepresentationTheory.Matrix.MvPolynomialRightMul RepresentationTheory.Auxiliary.GeneralLinearCoordinateLocalization
  RepresentationTheory.LinearAlgebra.Matrix.GeneralLinearGroup.LocalizationAction RepresentationTheory.MatrixPolynomialHomogeneity RepresentationTheory.GeneralLinearGroup.PolynomialQuotientRepresentation
  RepresentationTheory.Auxiliary.GeneralLinearPolynomialSubrepresentations RepresentationTheory.GeneralLinear.AuxiliaryRepresentationFamilies
  RepresentationTheory.GeneralLinear.AuxiliaryPolynomialQuotient RepresentationTheory.GeneralLinear.HomogeneousPolynomialsAndAuxiliaryRepresentations
  RepresentationTheory.GeneralLinear.AuxiliaryPolynomialIdentities

/-- A value attached to each natural-number-indexed representation can be expressed as a finite sum of family terms with natural-number coefficients. -/
theorem auxiliary_indexed_representation_value_eq_finite_weighted_sum
    (k : Type) [Field k] [IsAlgClosed k] [CharZero k] (N d : ℕ) :
    ∃ (S : Finset {l : Fin N → ℕ // Antitone l}) (c : {l : Fin N → ℕ // Antitone l} → ℕ),
      _root_.RepresentationTheory.GeneralLinearGroup.WeightCharacter.weightCharacter k N (_root_.RepresentationTheory.GeneralLinear.HomogeneousPolynomialsAndAuxiliaryRepresentations.auxiliaryIndexedGeneralLinearFDRep k N d)
        = ∑ ν ∈ S, (c ν : ℚ) • _root_.RepresentationTheory.SymmetricPolynomials.Alternant.partitionPolynomial N ν.val := by
  classical
  have hc : ∀ ν : {l : Fin N → ℕ // Antitone l},
      ((_root_.RepresentationTheory.GeneralLinear.AuxiliaryRepresentationFamilies.auxiliaryPolynomial_eval_one_eq_natCast k ν.val ν.property).choose : ℚ)
        = MvPolynomial.eval (fun _ => (1 : ℚ)) (_root_.RepresentationTheory.SymmetricPolynomials.Alternant.partitionPolynomial N ν.val) :=
    fun ν => ((_root_.RepresentationTheory.GeneralLinear.AuxiliaryRepresentationFamilies.auxiliaryPolynomial_eval_one_eq_natCast k ν.val ν.property).choose_spec).symm
  refine ⟨(Finset.univ : Finset (_root_.RepresentationTheory.SymmetricPolynomials.Alternant.FinPartition N d)).image _root_.RepresentationTheory.GeneralLinear.AuxiliaryRepresentationFamilies.auxiliaryAntitoneMap,
    fun ν => (_root_.RepresentationTheory.GeneralLinear.AuxiliaryRepresentationFamilies.auxiliaryPolynomial_eval_one_eq_natCast k ν.val ν.property).choose, ?_⟩
  rw [_root_.RepresentationTheory.GeneralLinear.AuxiliaryPolynomialIdentities.auxiliaryIndexedGeneralLinearFDRep_auxiliaryPolynomial_eq_weightedSum k N d,
    Finset.sum_image (fun x _ y _ h => _root_.RepresentationTheory.GeneralLinear.AuxiliaryRepresentationFamilies.auxiliaryAntitoneMap_injective h)]
  refine Finset.sum_congr rfl (fun ν _ => ?_)
  have hval : (_root_.RepresentationTheory.GeneralLinear.AuxiliaryRepresentationFamilies.auxiliaryAntitoneMap ν).val = ν.parts := rfl
  rw [hc (_root_.RepresentationTheory.GeneralLinear.AuxiliaryRepresentationFamilies.auxiliaryAntitoneMap ν), hval]

/-- If the natural-number values associated with a finite basis are bounded, the corresponding indexed representation satisfies the given predicate and admits an injective equivariant map. -/
theorem auxiliary_subrepresentation_has_injective_equivariant_map_of_basis_bound
    (n : ℕ) (k : Type) [Field k] [IsAlgClosed k] [CharZero k]
    (S : Subrepresentation (_root_.RepresentationTheory.LinearAlgebra.Matrix.GeneralLinearGroup.LocalizationAction.generalLinearGroupLocalizationRepresentation k n))
    [FiniteDimensional k S.toSubmodule]
    {m : ℕ} (B : Module.Basis (Fin m) k S.toSubmodule) (r : ℕ)
    (hr_ge : ∀ i, _root_.RepresentationTheory.Auxiliary.GeneralLinearCoordinateLocalization.localization_denominator_order ((S.toSubmodule.subtype (B i)) : Localization.Away (_root_.RepresentationTheory.Auxiliary.GeneralLinearCoordinateLocalization.auxiliary_matrix_polynomial k n)) ≤ r) :
      _root_.RepresentationTheory.GeneralLinearGroup.Auxiliary.HasAuxiliaryMapProperty n
        ⇑(_root_.RepresentationTheory.GeneralLinearGroup.PolynomialQuotientRepresentation.twistByCharacter (_root_.RepresentationTheory.GeneralLinearGroup.PolynomialQuotientRepresentation.generalLinearGroupToUnits k n ^ r) S.toRepresentation) ∧
      ∃ φ : S.toSubmodule →ₗ[k] MvPolynomial (Fin n × Fin n) k,
        Function.Injective φ ∧
        ∀ (g : Matrix.GeneralLinearGroup (Fin n) k) (v : S.toSubmodule),
          φ (_root_.RepresentationTheory.GeneralLinearGroup.PolynomialQuotientRepresentation.twistByCharacter (_root_.RepresentationTheory.GeneralLinearGroup.PolynomialQuotientRepresentation.generalLinearGroupToUnits k n ^ r) S.toRepresentation g v) = _root_.RepresentationTheory.Matrix.MvPolynomialRightMul.Matrix.generalLinearGroupMvPolynomialRightMul k n g (φ v) := by
  classical

  have hclear : ∀ i, ∃ P : MvPolynomial (Fin n × Fin n) k,
      (S.toSubmodule.subtype (B i) : Localization.Away (_root_.RepresentationTheory.Auxiliary.GeneralLinearCoordinateLocalization.auxiliary_matrix_polynomial k n)) = _root_.RepresentationTheory.GeneralLinearGroup.Localization.localizationDenominatorPower r P := by
    intro i
    obtain ⟨Q, hQ⟩ :=
      _root_.RepresentationTheory.Auxiliary.GeneralLinearCoordinateLocalization.exists_numerator_at_denominator_order (S.toSubmodule.subtype (B i) : Localization.Away (_root_.RepresentationTheory.Auxiliary.GeneralLinearCoordinateLocalization.auxiliary_matrix_polynomial k n))
    refine ⟨Q * _root_.RepresentationTheory.Auxiliary.GeneralLinearCoordinateLocalization.auxiliary_matrix_polynomial k n ^ (r - _root_.RepresentationTheory.Auxiliary.GeneralLinearCoordinateLocalization.localization_denominator_order (S.toSubmodule.subtype (B i))), ?_⟩
    conv_lhs => rw [hQ]
    rw [_root_.RepresentationTheory.GeneralLinearGroup.Localization.localizationDenominatorPower_apply, map_mul, map_pow, mul_assoc]
    congr 1

    rw [show (IsLocalization.Away.invSelf (_root_.RepresentationTheory.Auxiliary.GeneralLinearCoordinateLocalization.auxiliary_matrix_polynomial k n) : Localization.Away (_root_.RepresentationTheory.Auxiliary.GeneralLinearCoordinateLocalization.auxiliary_matrix_polynomial k n)) ^ r
          = IsLocalization.Away.invSelf (_root_.RepresentationTheory.Auxiliary.GeneralLinearCoordinateLocalization.auxiliary_matrix_polynomial k n)
              ^ (r - _root_.RepresentationTheory.Auxiliary.GeneralLinearCoordinateLocalization.localization_denominator_order (S.toSubmodule.subtype (B i)))
            * IsLocalization.Away.invSelf (_root_.RepresentationTheory.Auxiliary.GeneralLinearCoordinateLocalization.auxiliary_matrix_polynomial k n)
              ^ (_root_.RepresentationTheory.Auxiliary.GeneralLinearCoordinateLocalization.localization_denominator_order (S.toSubmodule.subtype (B i))) from by
        rw [← pow_add, Nat.sub_add_cancel (hr_ge i)],
      ← mul_assoc, _root_.RepresentationTheory.Auxiliary.GeneralLinearCoordinateLocalization.algebraMap_pow_mul_invSelf_pow, one_mul]
  choose P hP using hclear

  set d : ℕ := Finset.univ.sup (fun i => (P i).totalDegree) with hd

  set ι : (_root_.RepresentationTheory.Auxiliary.GeneralLinearPolynomialSubrepresentations.auxiliarySubrepresentation k n d).toSubmodule →ₗ[k] Localization.Away (_root_.RepresentationTheory.Auxiliary.GeneralLinearCoordinateLocalization.auxiliary_matrix_polynomial k n) :=
    (_root_.RepresentationTheory.GeneralLinearGroup.Localization.localizationDenominatorPower r).comp (_root_.RepresentationTheory.Auxiliary.GeneralLinearPolynomialSubrepresentations.auxiliarySubrepresentation k n d).toSubmodule.subtype with hι
  have hι_apply : ∀ w : (_root_.RepresentationTheory.Auxiliary.GeneralLinearPolynomialSubrepresentations.auxiliarySubrepresentation k n d).toSubmodule,
      ι w = _root_.RepresentationTheory.GeneralLinearGroup.Localization.localizationDenominatorPower r (w : MvPolynomial (Fin n × Fin n) k) := fun _ => rfl
  have hι_inj : Function.Injective ι :=
    (_root_.RepresentationTheory.Auxiliary.GeneralLinearPolynomialSubrepresentations.auxiliaryMap_injective r).comp (Submodule.injective_subtype _)

  have hinter : ∀ (g : Matrix.GeneralLinearGroup (Fin n) k) (w : (_root_.RepresentationTheory.Auxiliary.GeneralLinearPolynomialSubrepresentations.auxiliarySubrepresentation k n d).toSubmodule),
      ι ((_root_.RepresentationTheory.Auxiliary.GeneralLinearPolynomialSubrepresentations.auxiliarySubrepresentation k n d).toRepresentation g w)
        = _root_.RepresentationTheory.GeneralLinearGroup.PolynomialQuotientRepresentation.twistByCharacter (_root_.RepresentationTheory.GeneralLinearGroup.PolynomialQuotientRepresentation.generalLinearGroupToUnits k n ^ r) (_root_.RepresentationTheory.LinearAlgebra.Matrix.GeneralLinearGroup.LocalizationAction.generalLinearGroupLocalizationRepresentation k n) g (ι w) := by
    intro g w
    rw [hι_apply, _root_.RepresentationTheory.Auxiliary.GeneralLinearPolynomialSubrepresentations.auxiliarySubrepresentation_apply_coe, hι_apply, _root_.RepresentationTheory.Auxiliary.GeneralLinearPolynomialSubrepresentations.auxiliaryMap_action]

  have hIII : S.toSubmodule ≤ LinearMap.range ι := by
    have hspan : S.toSubmodule
        = Submodule.span k (Set.range (fun i =>
            (S.toSubmodule.subtype (B i) : Localization.Away (_root_.RepresentationTheory.Auxiliary.GeneralLinearCoordinateLocalization.auxiliary_matrix_polynomial k n)))) := by
      conv_lhs => rw [← Submodule.map_subtype_top S.toSubmodule, ← B.span_eq,
        Submodule.map_span]
      rw [← Set.range_comp]
      rfl
    rw [hspan, Submodule.span_le]
    rintro _ ⟨i, rfl⟩
    rw [SetLike.mem_coe, LinearMap.mem_range]
    refine ⟨⟨P i, ?_⟩, ?_⟩
    · change P i ∈ (_root_.RepresentationTheory.Auxiliary.GeneralLinearPolynomialSubrepresentations.auxiliarySubrepresentation k n d).toSubmodule
      exact (MvPolynomial.mem_restrictTotalDegree _ _ _).mpr
        (Finset.le_sup (f := fun i => (P i).totalDegree) (Finset.mem_univ i))
    · rw [hι_apply]; exact (hP i).symm

  set U : Submodule k (_root_.RepresentationTheory.Auxiliary.GeneralLinearPolynomialSubrepresentations.auxiliarySubrepresentation k n d).toSubmodule :=
    Submodule.comap ι S.toSubmodule with hU
  have hU_inv : ∀ g, ∀ v ∈ U, (_root_.RepresentationTheory.Auxiliary.GeneralLinearPolynomialSubrepresentations.auxiliarySubrepresentation k n d).toRepresentation g v ∈ U := by
    intro g v hv
    rw [hU, Submodule.mem_comap] at hv ⊢
    rw [hinter, _root_.RepresentationTheory.GeneralLinearGroup.PolynomialQuotientRepresentation.twistByCharacter_apply]
    exact Submodule.smul_mem _ _ (S.apply_mem_toSubmodule g hv)
  haveI : Module.Finite k U := inferInstance

  have hmap : U.map ι = S.toSubmodule := by
    rw [hU, Submodule.map_comap_eq, inf_eq_right.mpr hIII]
  let e : U ≃ₗ[k] S.toSubmodule :=
    (Submodule.equivMapOfInjective ι hι_inj U).trans (LinearEquiv.ofEq _ _ hmap)
  have he_coe : ∀ y : U,
      (e y : Localization.Away (_root_.RepresentationTheory.Auxiliary.GeneralLinearCoordinateLocalization.auxiliary_matrix_polynomial k n)) = ι (y : (_root_.RepresentationTheory.Auxiliary.GeneralLinearPolynomialSubrepresentations.auxiliarySubrepresentation k n d).toSubmodule) := by
    intro y
    change ((LinearEquiv.ofEq _ _ hmap) (Submodule.equivMapOfInjective ι hι_inj U y) :
        Localization.Away (_root_.RepresentationTheory.Auxiliary.GeneralLinearCoordinateLocalization.auxiliary_matrix_polynomial k n)) = _
    rw [LinearEquiv.coe_ofEq_apply, Submodule.coe_equivMapOfInjective_apply]
  have hS_coe : ∀ (g : Matrix.GeneralLinearGroup (Fin n) k) (z : S.toSubmodule),
      ((S.toRepresentation g z : Localization.Away (_root_.RepresentationTheory.Auxiliary.GeneralLinearCoordinateLocalization.auxiliary_matrix_polynomial k n)))
        = _root_.RepresentationTheory.LinearAlgebra.Matrix.GeneralLinearGroup.LocalizationAction.generalLinearGroupLocalizationRepresentation k n g (z : Localization.Away (_root_.RepresentationTheory.Auxiliary.GeneralLinearCoordinateLocalization.auxiliary_matrix_polynomial k n)) :=
    fun g z => LinearMap.coe_restrict_apply (S.apply_mem_toSubmodule g) z

  have hcomm : ∀ (g : Matrix.GeneralLinearGroup (Fin n) k) (y : U),
      e (((_root_.RepresentationTheory.Auxiliary.GeneralLinearPolynomialSubrepresentations.auxiliarySubrepresentation k n d).toRepresentation g).restrict (hU_inv g) y)
        = _root_.RepresentationTheory.GeneralLinearGroup.PolynomialQuotientRepresentation.twistByCharacter (_root_.RepresentationTheory.GeneralLinearGroup.PolynomialQuotientRepresentation.generalLinearGroupToUnits k n ^ r) S.toRepresentation g (e y) := by
    intro g y
    apply Subtype.ext
    have hL : (↑(e (((_root_.RepresentationTheory.Auxiliary.GeneralLinearPolynomialSubrepresentations.auxiliarySubrepresentation k n d).toRepresentation g).restrict (hU_inv g) y)) :
        Localization.Away (_root_.RepresentationTheory.Auxiliary.GeneralLinearCoordinateLocalization.auxiliary_matrix_polynomial k n))
        = _root_.RepresentationTheory.GeneralLinearGroup.PolynomialQuotientRepresentation.twistByCharacter (_root_.RepresentationTheory.GeneralLinearGroup.PolynomialQuotientRepresentation.generalLinearGroupToUnits k n ^ r) (_root_.RepresentationTheory.LinearAlgebra.Matrix.GeneralLinearGroup.LocalizationAction.generalLinearGroupLocalizationRepresentation k n) g (ι (y : _)) := by
      rw [he_coe, LinearMap.coe_restrict_apply, hinter]
    have hR : (↑(_root_.RepresentationTheory.GeneralLinearGroup.PolynomialQuotientRepresentation.twistByCharacter (_root_.RepresentationTheory.GeneralLinearGroup.PolynomialQuotientRepresentation.generalLinearGroupToUnits k n ^ r) S.toRepresentation g (e y)) :
        Localization.Away (_root_.RepresentationTheory.Auxiliary.GeneralLinearCoordinateLocalization.auxiliary_matrix_polynomial k n))
        = _root_.RepresentationTheory.GeneralLinearGroup.PolynomialQuotientRepresentation.twistByCharacter (_root_.RepresentationTheory.GeneralLinearGroup.PolynomialQuotientRepresentation.generalLinearGroupToUnits k n ^ r) (_root_.RepresentationTheory.LinearAlgebra.Matrix.GeneralLinearGroup.LocalizationAction.generalLinearGroupLocalizationRepresentation k n) g (ι (y : _)) := by
      rw [_root_.RepresentationTheory.GeneralLinearGroup.PolynomialQuotientRepresentation.twistByCharacter_apply, Submodule.coe_smul, hS_coe, he_coe, _root_.RepresentationTheory.GeneralLinearGroup.PolynomialQuotientRepresentation.twistByCharacter_apply]
    rw [hL, hR]

  have hMalg : _root_.RepresentationTheory.GeneralLinearGroup.Auxiliary.HasAuxiliaryMapProperty n
      ⇑(_root_.RepresentationTheory.GeneralLinearGroup.PolynomialQuotientRepresentation.twistByCharacter (_root_.RepresentationTheory.GeneralLinearGroup.PolynomialQuotientRepresentation.generalLinearGroupToUnits k n ^ r) S.toRepresentation) :=
    ((_root_.RepresentationTheory.Auxiliary.GeneralLinearPolynomialSubrepresentations.auxiliarySubrepresentation_property k n d).auxiliary_restrict U hU_inv).auxiliary_of_linearEquiv e hcomm

  refine ⟨hMalg,
    (_root_.RepresentationTheory.Auxiliary.GeneralLinearPolynomialSubrepresentations.auxiliarySubrepresentation k n d).toSubmodule.subtype ∘ₗ U.subtype ∘ₗ e.symm.toLinearMap, ?_, ?_⟩
  ·
    exact (Submodule.injective_subtype _).comp
      ((Submodule.injective_subtype U).comp e.symm.injective)
  ·
    intro g v
    change (_root_.RepresentationTheory.Auxiliary.GeneralLinearPolynomialSubrepresentations.auxiliarySubrepresentation k n d).toSubmodule.subtype (U.subtype (e.symm
        (_root_.RepresentationTheory.GeneralLinearGroup.PolynomialQuotientRepresentation.twistByCharacter (_root_.RepresentationTheory.GeneralLinearGroup.PolynomialQuotientRepresentation.generalLinearGroupToUnits k n ^ r) S.toRepresentation g v)))
      = _root_.RepresentationTheory.Matrix.MvPolynomialRightMul.Matrix.generalLinearGroupMvPolynomialRightMul k n g ((_root_.RepresentationTheory.Auxiliary.GeneralLinearPolynomialSubrepresentations.auxiliarySubrepresentation k n d).toSubmodule.subtype (U.subtype (e.symm v)))
    have hsymm : e.symm (_root_.RepresentationTheory.GeneralLinearGroup.PolynomialQuotientRepresentation.twistByCharacter (_root_.RepresentationTheory.GeneralLinearGroup.PolynomialQuotientRepresentation.generalLinearGroupToUnits k n ^ r) S.toRepresentation g v)
        = ((_root_.RepresentationTheory.Auxiliary.GeneralLinearPolynomialSubrepresentations.auxiliarySubrepresentation k n d).toRepresentation g).restrict (hU_inv g) (e.symm v) := by
      apply e.injective
      rw [e.apply_symm_apply, hcomm, e.apply_symm_apply]
    rw [hsymm,
      show U.subtype ((((_root_.RepresentationTheory.Auxiliary.GeneralLinearPolynomialSubrepresentations.auxiliarySubrepresentation k n d).toRepresentation g).restrict (hU_inv g)) (e.symm v))
          = (_root_.RepresentationTheory.Auxiliary.GeneralLinearPolynomialSubrepresentations.auxiliarySubrepresentation k n d).toRepresentation g (U.subtype (e.symm v)) from
        LinearMap.coe_restrict_apply (hU_inv g) (e.symm v)]
    exact _root_.RepresentationTheory.Auxiliary.GeneralLinearPolynomialSubrepresentations.auxiliarySubrepresentation_apply_coe d g (U.subtype (e.symm v))

/-- For a finite-dimensional subrepresentation, some natural power gives the stated predicate, an associated indexed supremum equal to top, and an injective equivariant map. -/
theorem auxiliary_subrepresentation_has_equivariant_embedding_with_supremum_eq_top
    (n : ℕ) (k : Type) [Field k] [IsAlgClosed k] [CharZero k]
    (S : Subrepresentation (_root_.RepresentationTheory.LinearAlgebra.Matrix.GeneralLinearGroup.LocalizationAction.generalLinearGroupLocalizationRepresentation k n))
    [FiniteDimensional k S.toSubmodule] :
    ∃ r : ℕ,
      _root_.RepresentationTheory.GeneralLinearGroup.Auxiliary.HasAuxiliaryMapProperty n
        ⇑(_root_.RepresentationTheory.GeneralLinearGroup.PolynomialQuotientRepresentation.twistByCharacter (_root_.RepresentationTheory.GeneralLinearGroup.PolynomialQuotientRepresentation.generalLinearGroupToUnits k n ^ r) S.toRepresentation) ∧
      (⨆ μ : Fin n →₀ ℕ,
        _root_.RepresentationTheory.GeneralLinearGroup.WeightCharacter.weightSpace k n
          (FDRep.of (_root_.RepresentationTheory.GeneralLinearGroup.PolynomialQuotientRepresentation.twistByCharacter (_root_.RepresentationTheory.GeneralLinearGroup.PolynomialQuotientRepresentation.generalLinearGroupToUnits k n ^ r) S.toRepresentation)) (fun i => μ i) = ⊤) ∧
      ∃ φ : S.toSubmodule →ₗ[k] MvPolynomial (Fin n × Fin n) k,
        Function.Injective φ ∧
        ∀ (g : Matrix.GeneralLinearGroup (Fin n) k) (v : S.toSubmodule),
          φ (_root_.RepresentationTheory.GeneralLinearGroup.PolynomialQuotientRepresentation.twistByCharacter (_root_.RepresentationTheory.GeneralLinearGroup.PolynomialQuotientRepresentation.generalLinearGroupToUnits k n ^ r) S.toRepresentation g v) = _root_.RepresentationTheory.Matrix.MvPolynomialRightMul.Matrix.generalLinearGroupMvPolynomialRightMul k n g (φ v) := by
  classical
  haveI : Module.Finite k S.toSubmodule := ‹FiniteDimensional k S.toSubmodule›
  let B : Module.Basis (Fin (Module.finrank k S.toSubmodule)) k S.toSubmodule :=
    Module.finBasis k S.toSubmodule

  set r₀ : ℕ := Finset.univ.sup
    (fun i => _root_.RepresentationTheory.Auxiliary.GeneralLinearCoordinateLocalization.localization_denominator_order ((S.toSubmodule.subtype (B i)) : Localization.Away (_root_.RepresentationTheory.Auxiliary.GeneralLinearCoordinateLocalization.auxiliary_matrix_polynomial k n))) with hr₀def
  have hr₀ : ∀ i, _root_.RepresentationTheory.Auxiliary.GeneralLinearCoordinateLocalization.localization_denominator_order ((S.toSubmodule.subtype (B i)) : Localization.Away (_root_.RepresentationTheory.Auxiliary.GeneralLinearCoordinateLocalization.auxiliary_matrix_polynomial k n)) ≤ r₀ :=
    fun i => Finset.le_sup
      (f := fun i => _root_.RepresentationTheory.Auxiliary.GeneralLinearCoordinateLocalization.localization_denominator_order ((S.toSubmodule.subtype (B i)) : Localization.Away (_root_.RepresentationTheory.Auxiliary.GeneralLinearCoordinateLocalization.auxiliary_matrix_polynomial k n)))
      (Finset.mem_univ i)

  obtain ⟨hMalg₀, -⟩ := auxiliary_subrepresentation_has_injective_equivariant_map_of_basis_bound n k S B r₀ hr₀
  obtain ⟨s, hPoly₀⟩ := hMalg₀.exists_det_twist

  have hr : ∀ i, _root_.RepresentationTheory.Auxiliary.GeneralLinearCoordinateLocalization.localization_denominator_order ((S.toSubmodule.subtype (B i)) : Localization.Away (_root_.RepresentationTheory.Auxiliary.GeneralLinearCoordinateLocalization.auxiliary_matrix_polynomial k n)) ≤ r₀ + s :=
    fun i => le_trans (hr₀ i) (Nat.le_add_right r₀ s)
  obtain ⟨hMalg, φ, hφ_inj, hφ_equiv⟩ := auxiliary_subrepresentation_has_injective_equivariant_map_of_basis_bound n k S B (r₀ + s) hr
  refine ⟨r₀ + s, hMalg, ?_, φ, hφ_inj, hφ_equiv⟩

  have hfun : (fun g => (Matrix.GeneralLinearGroup.det g : k) ^ s •
        (_root_.RepresentationTheory.GeneralLinearGroup.PolynomialQuotientRepresentation.twistByCharacter (_root_.RepresentationTheory.GeneralLinearGroup.PolynomialQuotientRepresentation.generalLinearGroupToUnits k n ^ r₀) S.toRepresentation) g)
      = ⇑(_root_.RepresentationTheory.GeneralLinearGroup.PolynomialQuotientRepresentation.twistByCharacter (_root_.RepresentationTheory.GeneralLinearGroup.PolynomialQuotientRepresentation.generalLinearGroupToUnits k n ^ (r₀ + s)) S.toRepresentation) := by
    funext g
    ext x
    rw [LinearMap.smul_apply, _root_.RepresentationTheory.GeneralLinearGroup.PolynomialQuotientRepresentation.twistByCharacter_apply, _root_.RepresentationTheory.GeneralLinearGroup.PolynomialQuotientRepresentation.twistByCharacter_apply, smul_smul]
    congr 1
    have hd : (Matrix.GeneralLinearGroup.det g : k) = (_root_.RepresentationTheory.GeneralLinearGroup.PolynomialQuotientRepresentation.generalLinearGroupToUnits k n g : k) := rfl
    rw [hd, MonoidHom.pow_apply, MonoidHom.pow_apply, Units.val_pow_eq_pow_val,
      Units.val_pow_eq_pow_val, pow_add]
    ring
  have hPoly : _root_.RepresentationTheory.GeneralLinearGroup.DiagonalAction.IsAuxiliaryEndomorphismFamily n
      ⇑(_root_.RepresentationTheory.GeneralLinearGroup.PolynomialQuotientRepresentation.twistByCharacter (_root_.RepresentationTheory.GeneralLinearGroup.PolynomialQuotientRepresentation.generalLinearGroupToUnits k n ^ (r₀ + s)) S.toRepresentation) := hfun ▸ hPoly₀
  exact _root_.RepresentationTheory.GeneralLinearGroup.DiagonalAction.iSup_indexedFamily_eq_top_of_isAuxiliaryEndomorphismFamily
    (FDRep.of (_root_.RepresentationTheory.GeneralLinearGroup.PolynomialQuotientRepresentation.twistByCharacter (_root_.RepresentationTheory.GeneralLinearGroup.PolynomialQuotientRepresentation.generalLinearGroupToUnits k n ^ (r₀ + s)) S.toRepresentation)) hPoly

/-- If a simple finite-dimensional representation maps injectively and equivariantly into a multivariate polynomial ring, then it maps injectively and equivariantly into some member of a natural-number-indexed representation family. -/
theorem auxiliary_simple_representation_embeds_in_indexed_representation_of_polynomial_embedding
    (k : Type) [Field k] [IsAlgClosed k] [CharZero k] (N : ℕ)
    (L : FDRep k (Matrix.GeneralLinearGroup (Fin N) k))
    (hLsimp : IsSimpleModule (MonoidAlgebra k (Matrix.GeneralLinearGroup (Fin N) k))
      (Representation.asModule L.ρ))
    (φ : L →ₗ[k] MvPolynomial (Fin N × Fin N) k)
    (hφ_inj : Function.Injective φ)
    (hφ_equiv : ∀ (g : Matrix.GeneralLinearGroup (Fin N) k) (v : L),
      φ (L.ρ g v) = _root_.RepresentationTheory.Matrix.MvPolynomialRightMul.Matrix.generalLinearGroupMvPolynomialRightMul k N g (φ v)) :
    ∃ (d : ℕ) (ψ : L →ₗ[k] _root_.RepresentationTheory.GeneralLinear.HomogeneousPolynomialsAndAuxiliaryRepresentations.auxiliaryIndexedGeneralLinearFDRep k N d),
      Function.Injective ψ ∧
      (∀ (g : Matrix.GeneralLinearGroup (Fin N) k) (v : L),
        ψ (L.ρ g v) = (_root_.RepresentationTheory.GeneralLinear.HomogeneousPolynomialsAndAuxiliaryRepresentations.auxiliaryIndexedGeneralLinearFDRep k N d).ρ g (ψ v)) := by
  classical
  haveI := hLsimp

  let ψ : ∀ d, L →ₗ[k] _root_.RepresentationTheory.GeneralLinear.HomogeneousPolynomialsAndAuxiliaryRepresentations.auxiliaryIndexedGeneralLinearFDRep k N d := fun d =>
    LinearMap.codRestrict (_root_.RepresentationTheory.MatrixPolynomialHomogeneity.homogeneousSubrepresentation k N d).toSubmodule
      ((MvPolynomial.homogeneousComponent d).comp φ)
      (fun v => MvPolynomial.homogeneousComponent_mem d (φ v))

  have hψ_val : ∀ d (v : L),
      (_root_.RepresentationTheory.MatrixPolynomialHomogeneity.homogeneousSubrepresentation k N d).toSubmodule.subtype (ψ d v)
        = MvPolynomial.homogeneousComponent d (φ v) := fun _ _ => rfl

  have hρ_coe : ∀ d (g : Matrix.GeneralLinearGroup (Fin N) k)
      (z : _root_.RepresentationTheory.GeneralLinear.HomogeneousPolynomialsAndAuxiliaryRepresentations.auxiliaryIndexedGeneralLinearFDRep k N d),
      (_root_.RepresentationTheory.MatrixPolynomialHomogeneity.homogeneousSubrepresentation k N d).toSubmodule.subtype ((_root_.RepresentationTheory.GeneralLinear.HomogeneousPolynomialsAndAuxiliaryRepresentations.auxiliaryIndexedGeneralLinearFDRep k N d).ρ g z)
        = _root_.RepresentationTheory.Matrix.MvPolynomialRightMul.Matrix.generalLinearGroupMvPolynomialRightMul k N g ((_root_.RepresentationTheory.MatrixPolynomialHomogeneity.homogeneousSubrepresentation k N d).toSubmodule.subtype z) :=
    fun d g z =>
      LinearMap.coe_restrict_apply ((_root_.RepresentationTheory.MatrixPolynomialHomogeneity.homogeneousSubrepresentation k N d).apply_mem_toSubmodule g) z

  have hψ_equiv : ∀ d (g : Matrix.GeneralLinearGroup (Fin N) k) (v : L),
      ψ d (L.ρ g v) = (_root_.RepresentationTheory.GeneralLinear.HomogeneousPolynomialsAndAuxiliaryRepresentations.auxiliaryIndexedGeneralLinearFDRep k N d).ρ g (ψ d v) := by
    intro d g v
    apply Submodule.injective_subtype (_root_.RepresentationTheory.MatrixPolynomialHomogeneity.homogeneousSubrepresentation k N d).toSubmodule
    rw [hψ_val, hρ_coe, hψ_val, hφ_equiv, _root_.RepresentationTheory.GeneralLinear.AuxiliaryPolynomialQuotient.homogeneousComponent_auxiliaryAction]

  have hschur : ∀ d, Function.Injective (ψ d) ∨ ψ d = 0 := by
    intro d
    let Ψ : Representation.asModule L.ρ
        →ₗ[MonoidAlgebra k (Matrix.GeneralLinearGroup (Fin N) k)]
          Representation.asModule (_root_.RepresentationTheory.GeneralLinear.HomogeneousPolynomialsAndAuxiliaryRepresentations.auxiliaryIndexedGeneralLinearFDRep k N d).ρ :=
      _root_.RepresentationTheory.AsModuleEquivalences.linearMapAsModule (ψ d) (hψ_equiv d)
    rcases eq_bot_or_eq_top (LinearMap.ker Ψ) with hker | hker
    · exact Or.inl fun a b h => LinearMap.ker_eq_bot.1 hker h
    · refine Or.inr ?_
      have hΨ0 : Ψ = 0 := LinearMap.ker_eq_top.1 hker
      ext v
      change Ψ v = 0
      rw [hΨ0, LinearMap.zero_apply]

  haveI : Nontrivial L :=
    IsSimpleModule.nontrivial (R := MonoidAlgebra k (Matrix.GeneralLinearGroup (Fin N) k))
      (M := Representation.asModule L.ρ)
  obtain ⟨v, hv0⟩ := exists_ne (0 : L)
  have hexists : ∃ d, Function.Injective (ψ d) := by
    by_contra hcon
    push Not at hcon
    have hzero : ∀ d, ψ d = 0 := fun d => (hschur d).resolve_left (hcon d)

    have hdecomp : (∑ d ∈ Finset.range ((φ v).totalDegree + 1),
        MvPolynomial.homogeneousComponent d (φ v)) = φ v :=
      MvPolynomial.sum_homogeneousComponent (φ v)
    have hzeroterm : ∀ d, MvPolynomial.homogeneousComponent d (φ v) = 0 := by
      intro d
      rw [← hψ_val d v, hzero d, LinearMap.zero_apply]
      rfl
    have hφv0 : φ v = 0 := by
      rw [← hdecomp]; exact Finset.sum_eq_zero fun d _ => hzeroterm d
    exact hv0 (hφ_inj (by rw [hφv0, map_zero]))
  obtain ⟨d, hd⟩ := hexists
  exact ⟨d, ψ d, hd, hψ_equiv d⟩

/-- A simple finite-dimensional subrepresentation admits an equivariant map whose source action is formed using the negation of a natural-number exponent. -/
theorem auxiliary_simple_subrepresentation_has_equivariant_map_after_negated_nat_power
    (n : ℕ) (k : Type) [Field k] [IsAlgClosed k] [CharZero k]
    (S : Subrepresentation (_root_.RepresentationTheory.LinearAlgebra.Matrix.GeneralLinearGroup.LocalizationAction.generalLinearGroupLocalizationRepresentation k n))
    [FiniteDimensional k S.toSubmodule]
    (hSsimple : IsSimpleModule (MonoidAlgebra k (Matrix.GeneralLinearGroup (Fin n) k))
      (Subrepresentation.asSubmodule S)) :
    ∃ (r : ℕ) (ν : Fin n → ℕ) (_hν : Antitone ν),
      Nonempty { f : _root_.RepresentationTheory.GeneralLinearGroup.WeightCharacter.schurSubmodule k n ν ≃ₗ[k] S.toSubmodule //
        ∀ (g : Matrix.GeneralLinearGroup (Fin n) k) (v : _root_.RepresentationTheory.GeneralLinearGroup.WeightCharacter.schurSubmodule k n ν),
          f (_root_.RepresentationTheory.GeneralLinearGroup.PolynomialQuotientRepresentation.twistByCharacter (_root_.RepresentationTheory.GeneralLinearGroup.PolynomialQuotientRepresentation.generalLinearGroupToUnits k n ^ (-(r : ℤ))) (_root_.RepresentationTheory.GeneralLinearGroup.WeightCharacter.schurSubmoduleRepresentation k n ν) g v)
            = S.toRepresentation g (f v) } := by
  classical

  haveI hSsimp' : IsSimpleModule (MonoidAlgebra k (Matrix.GeneralLinearGroup (Fin n) k))
      (Representation.asModule S.toRepresentation) :=
    _root_.RepresentationTheory.Submodules.isSimpleModule_toRepresentation_of_asSubmodule S hSsimple

  obtain ⟨r, hMalg, hMtop, φ, hφ_inj, hφ_equiv⟩ :=
    auxiliary_subrepresentation_has_equivariant_embedding_with_supremum_eq_top n k S

  set Mrep : Representation k (Matrix.GeneralLinearGroup (Fin n) k) S.toSubmodule :=
    _root_.RepresentationTheory.GeneralLinearGroup.PolynomialQuotientRepresentation.twistByCharacter (_root_.RepresentationTheory.GeneralLinearGroup.PolynomialQuotientRepresentation.generalLinearGroupToUnits k n ^ r) S.toRepresentation with hMrep
  set L : FDRep k (Matrix.GeneralLinearGroup (Fin n) k) := FDRep.of Mrep with hL

  haveI hLsimp : IsSimpleModule (MonoidAlgebra k (Matrix.GeneralLinearGroup (Fin n) k))
      (Representation.asModule L.ρ) := by
    have := _root_.RepresentationTheory.GeneralLinear.AuxiliaryRepresentations.isSimpleModule_auxiliaryRepresentationConstruction (_root_.RepresentationTheory.GeneralLinearGroup.PolynomialQuotientRepresentation.generalLinearGroupToUnits k n ^ r) S.toRepresentation
    exact this

  obtain ⟨d, ψ, hψ_inj, hψ_equiv⟩ :=
    auxiliary_simple_representation_embeds_in_indexed_representation_of_polynomial_embedding k n L hLsimp φ hφ_inj hφ_equiv

  obtain ⟨Sset, c, hchar⟩ := auxiliary_indexed_representation_value_eq_finite_weighted_sum k n d

  obtain ⟨ν, _hνS, _hcpos, hcharL⟩ :=
    _root_.RepresentationTheory.SimpleDirectSumAndWeightDegree.GeneralLinearRepresentation.exists_positive_polynomial_term_of_simple_subrepresentation_of_weightSum k n d
      (_root_.RepresentationTheory.GeneralLinear.HomogeneousPolynomialsAndAuxiliaryRepresentations.auxiliaryIndexedGeneralLinearFDRep k n d)
      (_root_.RepresentationTheory.LinearAlgebra.GeneralLinearGroup.PolynomialCoefficients.fdRep_rho_satisfies_property k n d)
      (_root_.RepresentationTheory.GeneralLinear.AuxiliaryRepresentationFamilies.iSup_auxiliarySubmodule_eq_top d)
      (fun μ hμ => _root_.RepresentationTheory.GeneralLinear.AuxiliaryRepresentationFamilies.sum_eq_degree_of_auxiliarySubmodule_ne_bot d μ hμ)
      Sset c hchar L hLsimp ψ hψ_inj hψ_equiv

  obtain ⟨e⟩ := _root_.RepresentationTheory.GeneralLinear.AuxiliaryDecomposition.iso_auxiliaryRepresentation_of_auxiliaryValue_eq k n ν.val ν.property
    L hLsimp hMtop hMalg hcharL

  refine ⟨r, ν.val, ν.property, ⟨⟨(FDRep.isoToLinearEquiv e).symm, ?_⟩⟩⟩
  intro g v

  have hInt : _root_.RepresentationTheory.LinearEquivCompatibility.RepresentationLinearEquiv.IsCompatible Mrep (_root_.RepresentationTheory.GeneralLinearGroup.WeightCharacter.schurSubmoduleRepresentation k n ν.val) (FDRep.isoToLinearEquiv e) :=
    _root_.RepresentationTheory.LinearEquivCompatibility.isCompatible_isoToLinearEquiv Mrep (_root_.RepresentationTheory.GeneralLinearGroup.WeightCharacter.schurSubmoduleRepresentation k n ν.val) e
  have hsymm : _root_.RepresentationTheory.LinearEquivCompatibility.RepresentationLinearEquiv.IsCompatible (_root_.RepresentationTheory.GeneralLinearGroup.WeightCharacter.schurSubmoduleRepresentation k n ν.val) Mrep (FDRep.isoToLinearEquiv e).symm :=
    hInt.symm
  have htw := hsymm.map_both (_root_.RepresentationTheory.GeneralLinearGroup.PolynomialQuotientRepresentation.generalLinearGroupToUnits k n ^ r)⁻¹

  have hchar_inv : ((_root_.RepresentationTheory.GeneralLinearGroup.PolynomialQuotientRepresentation.generalLinearGroupToUnits k n ^ r)⁻¹ : Matrix.GeneralLinearGroup (Fin n) k →* kˣ)
      = _root_.RepresentationTheory.GeneralLinearGroup.PolynomialQuotientRepresentation.generalLinearGroupToUnits k n ^ (-(r : ℤ)) := by
    rw [zpow_neg, zpow_natCast]
  have huntwist : _root_.RepresentationTheory.GeneralLinearGroup.PolynomialQuotientRepresentation.twistByCharacter (_root_.RepresentationTheory.GeneralLinearGroup.PolynomialQuotientRepresentation.generalLinearGroupToUnits k n ^ r)⁻¹ Mrep = S.toRepresentation := by
    rw [hMrep]
    ext g' x
    rw [_root_.RepresentationTheory.GeneralLinearGroup.PolynomialQuotientRepresentation.twistByCharacter_apply, _root_.RepresentationTheory.GeneralLinearGroup.PolynomialQuotientRepresentation.twistByCharacter_apply, smul_smul, ← Units.val_mul,
      ← MonoidHom.mul_apply, inv_mul_cancel, MonoidHom.one_apply, Units.val_one, one_smul]
  rw [huntwist, hchar_inv] at htw
  exact htw g v

end RepresentationTheory.Auxiliary.EquivariantMaps
