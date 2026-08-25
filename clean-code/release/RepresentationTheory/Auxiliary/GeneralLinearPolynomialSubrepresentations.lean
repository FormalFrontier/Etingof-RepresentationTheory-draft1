/-
Copyright (c) 2026 mathlib-initiative. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: mathlib-initiative
-/

import Mathlib
import RepresentationTheory.GeneralLinearGroup.Localization
import RepresentationTheory.LinearAlgebra.GeneralLinearGroup.PolynomialCoefficients
import RepresentationTheory.AuxiliarySemisimpleDecomposition

open scoped TensorProduct

noncomputable section

namespace RepresentationTheory.Auxiliary.GeneralLinearPolynomialSubrepresentations

open MvPolynomial RepresentationTheory.Matrix.MvPolynomialRightMul RepresentationTheory.Auxiliary.GeneralLinearCoordinateLocalization
  RepresentationTheory.LinearAlgebra.Matrix.GeneralLinearGroup.LocalizationAction RepresentationTheory.MatrixPolynomialHomogeneity RepresentationTheory.GeneralLinearGroup.PolynomialQuotientRepresentation

variable {k : Type*} [Field k] {N : ℕ}

/-- The auxiliary map commutes with the displayed group action. -/
theorem auxiliaryMap_action (r : ℕ) (g : Matrix.GeneralLinearGroup (Fin N) k)
    (p : MvPolynomial (Fin N × Fin N) k) :
    _root_.RepresentationTheory.GeneralLinearGroup.PolynomialQuotientRepresentation.twistByCharacter (_root_.RepresentationTheory.GeneralLinearGroup.PolynomialQuotientRepresentation.generalLinearGroupToUnits k N ^ r) (_root_.RepresentationTheory.LinearAlgebra.Matrix.GeneralLinearGroup.LocalizationAction.generalLinearGroupLocalizationRepresentation k N) g (_root_.RepresentationTheory.GeneralLinearGroup.Localization.localizationDenominatorPower r p)
      = _root_.RepresentationTheory.GeneralLinearGroup.Localization.localizationDenominatorPower r (_root_.RepresentationTheory.Matrix.MvPolynomialRightMul.Matrix.generalLinearGroupMvPolynomialRightMul k N g p) := by
  have hdet : ((_root_.RepresentationTheory.GeneralLinearGroup.PolynomialQuotientRepresentation.generalLinearGroupToUnits k N) g : k) = (g : Matrix (Fin N) (Fin N) k).det :=
    Matrix.GeneralLinearGroup.val_det_apply g
  rw [_root_.RepresentationTheory.GeneralLinearGroup.PolynomialQuotientRepresentation.twistByCharacter_apply, _root_.RepresentationTheory.GeneralLinearGroup.Localization.localizationDenominatorPower_apply, _root_.RepresentationTheory.GeneralLinearGroup.Localization.action_map_mul_invSelf_pow, ← _root_.RepresentationTheory.GeneralLinearGroup.Localization.localizationDenominatorPower_apply, smul_smul]
  have hscal : ((_root_.RepresentationTheory.GeneralLinearGroup.PolynomialQuotientRepresentation.generalLinearGroupToUnits k N ^ r) g : k) * ((g : Matrix (Fin N) (Fin N) k).det)⁻¹ ^ r = 1 := by
    rw [MonoidHom.pow_apply, Units.val_pow_eq_pow_val, hdet, ← mul_pow,
      mul_inv_cancel₀ (by rw [← hdet]; exact (_root_.RepresentationTheory.GeneralLinearGroup.PolynomialQuotientRepresentation.generalLinearGroupToUnits k N g).ne_zero), one_pow]
  rw [hscal, one_smul]

/-- The auxiliary subrepresentation indexed by a natural-number parameter. -/
def auxiliarySubrepresentation (k : Type*) [Field k] (N d : ℕ) :
    Subrepresentation (_root_.RepresentationTheory.Matrix.MvPolynomialRightMul.Matrix.generalLinearGroupMvPolynomialRightMul k N) where
  toSubmodule := MvPolynomial.restrictTotalDegree (Fin N × Fin N) k d
  apply_mem_toSubmodule g f hf := by
    rw [MvPolynomial.mem_restrictTotalDegree, _root_.RepresentationTheory.Matrix.MvPolynomialRightMul.Matrix.generalLinearGroupMvPolynomialRightMul_apply]
    exact (_root_.RepresentationTheory.GeneralLinearGroup.Localization.totalDegree_substitute_le _ _).trans
      ((MvPolynomial.mem_restrictTotalDegree _ _ _).mp hf)

/-- The module underlying the auxiliary subrepresentation is finite. -/
instance auxiliarySubrepresentation_finite (k : Type*) [Field k] (N d : ℕ) :
    Module.Finite k (auxiliarySubrepresentation k N d).toSubmodule :=
  inferInstanceAs
    (Module.Finite k (MvPolynomial.restrictTotalDegree (Fin N × Fin N) k d))

/-- The restricted action on the auxiliary subrepresentation agrees with the ambient action after coercion. -/
theorem auxiliarySubrepresentation_apply_coe (d : ℕ)
    (g : Matrix.GeneralLinearGroup (Fin N) k) (w : (auxiliarySubrepresentation k N d).toSubmodule) :
    ((auxiliarySubrepresentation k N d).toRepresentation g w : MvPolynomial (Fin N × Fin N) k)
      = _root_.RepresentationTheory.Matrix.MvPolynomialRightMul.Matrix.generalLinearGroupMvPolynomialRightMul k N g (w : MvPolynomial (Fin N × Fin N) k) :=
  LinearMap.coe_restrict_apply ((auxiliarySubrepresentation k N d).apply_mem_toSubmodule g) w

set_option maxHeartbeats 6400000 in

/-- Records the displayed property of the representation associated with the auxiliary subrepresentation. -/
theorem auxiliarySubrepresentation_property (k : Type*) [Field k] (N d : ℕ) :
    RepresentationTheory.GeneralLinearGroup.Auxiliary.HasAuxiliaryMapProperty N
      ⇑(auxiliarySubrepresentation k N d).toRepresentation := by
  classical
  set W := (auxiliarySubrepresentation k N d).toSubmodule with hW

  let val : W →ₗ[k] MvPolynomial (Fin N × Fin N) k := W.subtype
  have hval_inj : Function.Injective val := Submodule.injective_subtype W
  have hval_rho : ∀ (g : Matrix.GeneralLinearGroup (Fin N) k) (w : W),
      val ((auxiliarySubrepresentation k N d).toRepresentation g w) = _root_.RepresentationTheory.Matrix.MvPolynomialRightMul.Matrix.generalLinearGroupMvPolynomialRightMul k N g (val w) :=
    fun g w => auxiliarySubrepresentation_apply_coe d g w

  set S : Finset ((Fin N × Fin N) →₀ ℕ) :=
    (Finset.range (d + 1)).biUnion (fun e => Finset.univ.finsuppAntidiag e) with hS
  have hmemS : ∀ μ : (Fin N × Fin N) →₀ ℕ, μ ∈ S ↔ (μ.sum fun _ e => e) ≤ d := by
    intro μ
    have hbridge : (μ.sum fun _ e => e) = Finset.univ.sum ⇑μ :=
      Finsupp.sum_fintype μ (fun _ n => n) (fun _ => rfl)
    rw [hS]
    simp only [Finset.mem_biUnion, Finset.mem_range, Finset.mem_finsuppAntidiag,
      Finset.subset_univ, and_true]
    constructor
    · rintro ⟨e, he, heq⟩; omega
    · intro h; exact ⟨Finset.univ.sum ⇑μ, by omega, rfl⟩

  have hmem : ∀ s : {s // s ∈ S},
      (MvPolynomial.monomial (↑s : (Fin N × Fin N) →₀ ℕ) (1 : k)) ∈ W := by
    intro s
    refine (MvPolynomial.mem_restrictTotalDegree _ _ _).mpr ?_
    rw [MvPolynomial.totalDegree_monomial _ (one_ne_zero)]
    exact (hmemS _).mp s.2
  let v : {s // s ∈ S} → W :=
    fun s => ⟨MvPolynomial.monomial (↑s) 1, hmem s⟩
  have hvval : ∀ s, val (v s) = MvPolynomial.monomial (↑s) 1 := fun _ => rfl

  have hli : LinearIndependent k v := by
    have hb : LinearIndependent k
        (fun s : {s // s ∈ S} => MvPolynomial.monomial (↑s : (Fin N × Fin N) →₀ ℕ) (1 : k)) := by
      have hcomp := (MvPolynomial.basisMonomials (Fin N × Fin N) k).linearIndependent.comp
        (fun s : {s // s ∈ S} => (↑s : (Fin N × Fin N) →₀ ℕ)) Subtype.val_injective
      simpa only [Function.comp_def, MvPolynomial.coe_basisMonomials] using hcomp
    exact hb.of_comp val

  have hsp : ⊤ ≤ Submodule.span k (Set.range v) := by
    rintro w -
    rw [Submodule.mem_span_range_iff_exists_fun]
    refine ⟨fun s => MvPolynomial.coeff (↑s) (val w), hval_inj ?_⟩
    have hsupp : ∀ p ∈ (val w).support, p ∈ S := by
      intro p hp
      rw [hmemS]
      exact (MvPolynomial.le_totalDegree hp).trans
        ((MvPolynomial.mem_restrictTotalDegree _ _ _).mp w.2)
    rw [map_sum]
    simp_rw [map_smul, hvval]
    rw [Finset.sum_coe_sort_eq_attach, Finset.sum_attach S
      (fun p => MvPolynomial.coeff p (val w) • MvPolynomial.monomial p (1 : k))]
    simp_rw [MvPolynomial.smul_eq_C_mul, MvPolynomial.C_mul_monomial, mul_one]
    conv_rhs => rw [(val w).as_sum]
    refine (Finset.sum_subset hsupp ?_).symm
    intro p _ hp
    rw [MvPolynomial.notMem_support_iff.mp hp]
    exact MvPolynomial.monomial_zero

  let b : Module.Basis {s // s ∈ S} k W :=
    Module.Basis.mk hli hsp
  have hbv : ∀ s, val (b s) = MvPolynomial.monomial (↑s) 1 := by
    intro s; rw [show b s = v s from Module.Basis.mk_apply hli hsp s]; exact hvval s

  have hrepr : ∀ (w : W) (a : {s // s ∈ S}),
      b.repr w a = MvPolynomial.coeff (↑a) (val w) := by
    intro w a
    have hexp : val w
        = ∑ s : {s // s ∈ S}, b.repr w s •
            MvPolynomial.monomial (↑s : (Fin N × Fin N) →₀ ℕ) (1 : k) := by
      conv_lhs => rw [← b.sum_repr w]
      rw [map_sum]
      exact Finset.sum_congr rfl fun s _ => by rw [map_smul, hbv s]
    rw [hexp, MvPolynomial.coeff_sum]
    simp only [MvPolynomial.coeff_smul, smul_eq_mul, MvPolynomial.coeff_monomial]
    rw [Finset.sum_eq_single a
      (fun s _ hsa => by rw [if_neg (fun h => hsa (Subtype.ext h)), mul_zero])
      (fun ha => absurd (Finset.mem_univ a) ha)]
    rw [if_pos rfl, mul_one]

  refine ⟨Fintype.card {s // s ∈ S}, b.reindex (Fintype.equivFin {s // s ∈ S}),
    fun a c => _root_.RepresentationTheory.LinearAlgebra.GeneralLinearGroup.PolynomialCoefficients.multiIndexPolynomial k N
      (↑((Fintype.equivFin {s // s ∈ S}).symm c))
      (↑((Fintype.equivFin {s // s ∈ S}).symm a)), fun g a c => ?_⟩
  rw [Module.Basis.repr_reindex_apply, Module.Basis.reindex_apply, hrepr, hval_rho, hbv,
    _root_.RepresentationTheory.LinearAlgebra.GeneralLinearGroup.PolynomialCoefficients.coeff_apply_monomial]

/-- The auxiliary map indexed by a natural number is injective. -/
theorem auxiliaryMap_injective (r : ℕ) :
    Function.Injective
      (_root_.RepresentationTheory.GeneralLinearGroup.Localization.localizationDenominatorPower r : MvPolynomial (Fin N × Fin N) k →ₗ[k] Localization.Away (_root_.RepresentationTheory.Auxiliary.GeneralLinearCoordinateLocalization.auxiliary_matrix_polynomial k N)) := by
  intro p q hpq
  rw [_root_.RepresentationTheory.GeneralLinearGroup.Localization.localizationDenominatorPower_apply, _root_.RepresentationTheory.GeneralLinearGroup.Localization.localizationDenominatorPower_apply] at hpq
  have hu : IsUnit (IsLocalization.Away.invSelf (_root_.RepresentationTheory.Auxiliary.GeneralLinearCoordinateLocalization.auxiliary_matrix_polynomial k N) ^ r) :=
    IsUnit.of_mul_eq_one
      ((algebraMap (MvPolynomial (Fin N × Fin N) k) (Localization.Away (_root_.RepresentationTheory.Auxiliary.GeneralLinearCoordinateLocalization.auxiliary_matrix_polynomial k N))
        (_root_.RepresentationTheory.Auxiliary.GeneralLinearCoordinateLocalization.auxiliary_matrix_polynomial k N)) ^ r)
      (by rw [mul_comm]; exact _root_.RepresentationTheory.Auxiliary.GeneralLinearCoordinateLocalization.algebraMap_pow_mul_invSelf_pow r)
  exact _root_.RepresentationTheory.Auxiliary.GeneralLinearCoordinateLocalization.matrix_polynomial_algebraMap_injective (hu.mul_right_cancel hpq)

/-- The representation arising from the displayed auxiliary subrepresentation is semisimple. -/
theorem auxiliarySubrepresentation_isSemisimple (k : Type) [Field k] [IsAlgClosed k] [CharZero k] {N : ℕ}
    (φ : Localization.Away (_root_.RepresentationTheory.Auxiliary.GeneralLinearCoordinateLocalization.auxiliary_matrix_polynomial k N)) :
    IsSemisimpleModule (MonoidAlgebra k (Matrix.GeneralLinearGroup (Fin N) k))
      (Representation.asModule (_root_.RepresentationTheory.GeneralLinearGroup.Localization.Auxiliary.subrepresentation φ).toRepresentation) := by
  classical
  obtain ⟨r, Q, hQ⟩ := _root_.RepresentationTheory.Auxiliary.GeneralLinearCoordinateLocalization.exists_localization_presentation φ
  set d := Q.totalDegree with hd
  haveI : Module.Finite k (_root_.RepresentationTheory.GeneralLinearGroup.Localization.Auxiliary φ) := _root_.RepresentationTheory.GeneralLinearGroup.Localization.Auxiliary.finiteDimensional φ
  haveI : Module.Finite k (_root_.RepresentationTheory.GeneralLinearGroup.Localization.Auxiliary.subrepresentation φ).toSubmodule :=
    inferInstanceAs (Module.Finite k (_root_.RepresentationTheory.GeneralLinearGroup.Localization.Auxiliary φ))

  set ι : (auxiliarySubrepresentation k N d).toSubmodule →ₗ[k] Localization.Away (_root_.RepresentationTheory.Auxiliary.GeneralLinearCoordinateLocalization.auxiliary_matrix_polynomial k N) :=
    (_root_.RepresentationTheory.GeneralLinearGroup.Localization.localizationDenominatorPower r).comp (auxiliarySubrepresentation k N d).toSubmodule.subtype with hι
  have hι_apply : ∀ w : (auxiliarySubrepresentation k N d).toSubmodule,
      ι w = _root_.RepresentationTheory.GeneralLinearGroup.Localization.localizationDenominatorPower r (w : MvPolynomial (Fin N × Fin N) k) := fun _ => rfl
  have hι_inj : Function.Injective ι :=
    (auxiliaryMap_injective r).comp (Submodule.injective_subtype _)

  have hinter : ∀ (g : Matrix.GeneralLinearGroup (Fin N) k) (w : (auxiliarySubrepresentation k N d).toSubmodule),
      ι ((auxiliarySubrepresentation k N d).toRepresentation g w)
        = _root_.RepresentationTheory.GeneralLinearGroup.PolynomialQuotientRepresentation.twistByCharacter (_root_.RepresentationTheory.GeneralLinearGroup.PolynomialQuotientRepresentation.generalLinearGroupToUnits k N ^ r) (_root_.RepresentationTheory.LinearAlgebra.Matrix.GeneralLinearGroup.LocalizationAction.generalLinearGroupLocalizationRepresentation k N) g (ι w) := by
    intro g w
    rw [hι_apply, auxiliarySubrepresentation_apply_coe, hι_apply, auxiliaryMap_action]

  have hIII : _root_.RepresentationTheory.GeneralLinearGroup.Localization.Auxiliary φ ≤ LinearMap.range ι := by
    rw [_root_.RepresentationTheory.GeneralLinearGroup.Localization.Auxiliary, Submodule.span_le]
    rintro _ ⟨g, rfl⟩
    rw [SetLike.mem_coe, LinearMap.mem_range]
    refine ⟨⟨((g : Matrix (Fin N) (Fin N) k).det)⁻¹ ^ r • _root_.RepresentationTheory.Matrix.MvPolynomialRightMul.Matrix.generalLinearGroupMvPolynomialRightMul k N g Q, ?_⟩, ?_⟩
    · refine (MvPolynomial.mem_restrictTotalDegree _ _ _).mpr ?_
      refine (MvPolynomial.totalDegree_smul_le _ _).trans ?_
      rw [_root_.RepresentationTheory.Matrix.MvPolynomialRightMul.Matrix.generalLinearGroupMvPolynomialRightMul_apply]
      exact _root_.RepresentationTheory.GeneralLinearGroup.Localization.totalDegree_substitute_le _ _
    · change _ = _root_.RepresentationTheory.LinearAlgebra.Matrix.GeneralLinearGroup.LocalizationAction.generalLinearGroupLocalizationRepresentation k N g φ
      rw [hι_apply, map_smul, _root_.RepresentationTheory.GeneralLinearGroup.Localization.localizationDenominatorPower_apply, hQ, _root_.RepresentationTheory.GeneralLinearGroup.Localization.action_map_mul_invSelf_pow]

  set U : Submodule k (auxiliarySubrepresentation k N d).toSubmodule :=
    Submodule.comap ι (_root_.RepresentationTheory.GeneralLinearGroup.Localization.Auxiliary φ) with hU
  have hU_inv : ∀ g, ∀ v ∈ U, (auxiliarySubrepresentation k N d).toRepresentation g v ∈ U := by
    intro g v hv
    rw [hU, Submodule.mem_comap] at hv ⊢
    rw [hinter, _root_.RepresentationTheory.GeneralLinearGroup.PolynomialQuotientRepresentation.twistByCharacter_apply]
    exact Submodule.smul_mem _ _ (_root_.RepresentationTheory.GeneralLinearGroup.Localization.auxiliary_action_mem φ g hv)
  haveI : Module.Finite k U := inferInstance

  have hmap : U.map ι = (_root_.RepresentationTheory.GeneralLinearGroup.Localization.Auxiliary.subrepresentation φ).toSubmodule := by
    change U.map ι = _root_.RepresentationTheory.GeneralLinearGroup.Localization.Auxiliary φ
    rw [hU, Submodule.map_comap_eq, inf_eq_right.mpr hIII]
  let e : U ≃ₗ[k] (_root_.RepresentationTheory.GeneralLinearGroup.Localization.Auxiliary.subrepresentation φ).toSubmodule :=
    (Submodule.equivMapOfInjective ι hι_inj U).trans (LinearEquiv.ofEq _ _ hmap)
  have he_coe : ∀ y : U,
      (e y : Localization.Away (_root_.RepresentationTheory.Auxiliary.GeneralLinearCoordinateLocalization.auxiliary_matrix_polynomial k N)) = ι (y : (auxiliarySubrepresentation k N d).toSubmodule) := by
    intro y
    change ((LinearEquiv.ofEq _ _ hmap) (Submodule.equivMapOfInjective ι hι_inj U y) :
        Localization.Away (_root_.RepresentationTheory.Auxiliary.GeneralLinearCoordinateLocalization.auxiliary_matrix_polynomial k N)) = _
    rw [LinearEquiv.coe_ofEq_apply, Submodule.coe_equivMapOfInjective_apply]
  have hrh_coe : ∀ (g : Matrix.GeneralLinearGroup (Fin N) k) (z : (_root_.RepresentationTheory.GeneralLinearGroup.Localization.Auxiliary.subrepresentation φ).toSubmodule),
      ((_root_.RepresentationTheory.GeneralLinearGroup.Localization.Auxiliary.subrepresentation φ).toRepresentation g z : Localization.Away (_root_.RepresentationTheory.Auxiliary.GeneralLinearCoordinateLocalization.auxiliary_matrix_polynomial k N))
        = _root_.RepresentationTheory.LinearAlgebra.Matrix.GeneralLinearGroup.LocalizationAction.generalLinearGroupLocalizationRepresentation k N g (z : Localization.Away (_root_.RepresentationTheory.Auxiliary.GeneralLinearCoordinateLocalization.auxiliary_matrix_polynomial k N)) :=
    fun g z => LinearMap.coe_restrict_apply ((_root_.RepresentationTheory.GeneralLinearGroup.Localization.Auxiliary.subrepresentation φ).apply_mem_toSubmodule g) z

  have hcomm : ∀ (g : Matrix.GeneralLinearGroup (Fin N) k) (y : U),
      e (((auxiliarySubrepresentation k N d).toRepresentation g).restrict (hU_inv g) y)
        = _root_.RepresentationTheory.GeneralLinearGroup.PolynomialQuotientRepresentation.twistByCharacter (_root_.RepresentationTheory.GeneralLinearGroup.PolynomialQuotientRepresentation.generalLinearGroupToUnits k N ^ r) (_root_.RepresentationTheory.GeneralLinearGroup.Localization.Auxiliary.subrepresentation φ).toRepresentation g (e y) := by
    intro g y
    apply Subtype.ext
    have hL : (↑(e (((auxiliarySubrepresentation k N d).toRepresentation g).restrict (hU_inv g) y)) :
        Localization.Away (_root_.RepresentationTheory.Auxiliary.GeneralLinearCoordinateLocalization.auxiliary_matrix_polynomial k N))
        = _root_.RepresentationTheory.GeneralLinearGroup.PolynomialQuotientRepresentation.twistByCharacter (_root_.RepresentationTheory.GeneralLinearGroup.PolynomialQuotientRepresentation.generalLinearGroupToUnits k N ^ r) (_root_.RepresentationTheory.LinearAlgebra.Matrix.GeneralLinearGroup.LocalizationAction.generalLinearGroupLocalizationRepresentation k N) g (ι (y : _)) := by
      rw [he_coe, LinearMap.coe_restrict_apply, hinter]
    have hR : (↑(_root_.RepresentationTheory.GeneralLinearGroup.PolynomialQuotientRepresentation.twistByCharacter (_root_.RepresentationTheory.GeneralLinearGroup.PolynomialQuotientRepresentation.generalLinearGroupToUnits k N ^ r) (_root_.RepresentationTheory.GeneralLinearGroup.Localization.Auxiliary.subrepresentation φ).toRepresentation g (e y)) :
        Localization.Away (_root_.RepresentationTheory.Auxiliary.GeneralLinearCoordinateLocalization.auxiliary_matrix_polynomial k N))
        = _root_.RepresentationTheory.GeneralLinearGroup.PolynomialQuotientRepresentation.twistByCharacter (_root_.RepresentationTheory.GeneralLinearGroup.PolynomialQuotientRepresentation.generalLinearGroupToUnits k N ^ r) (_root_.RepresentationTheory.LinearAlgebra.Matrix.GeneralLinearGroup.LocalizationAction.generalLinearGroupLocalizationRepresentation k N) g (ι (y : _)) := by
      rw [_root_.RepresentationTheory.GeneralLinearGroup.PolynomialQuotientRepresentation.twistByCharacter_apply, Submodule.coe_smul, hrh_coe, he_coe, _root_.RepresentationTheory.GeneralLinearGroup.PolynomialQuotientRepresentation.twistByCharacter_apply]
    rw [hL, hR]

  have htwAlg : RepresentationTheory.GeneralLinearGroup.Auxiliary.HasAuxiliaryMapProperty N
      ⇑(_root_.RepresentationTheory.GeneralLinearGroup.PolynomialQuotientRepresentation.twistByCharacter (_root_.RepresentationTheory.GeneralLinearGroup.PolynomialQuotientRepresentation.generalLinearGroupToUnits k N ^ r) (_root_.RepresentationTheory.GeneralLinearGroup.Localization.Auxiliary.subrepresentation φ).toRepresentation) :=
    ((auxiliarySubrepresentation_property k N d).auxiliary_restrict U hU_inv).auxiliary_of_linearEquiv e hcomm

  haveI hss_tw : IsSemisimpleModule (MonoidAlgebra k (Matrix.GeneralLinearGroup (Fin N) k))
      (_root_.RepresentationTheory.GeneralLinearGroup.PolynomialQuotientRepresentation.twistByCharacter (_root_.RepresentationTheory.GeneralLinearGroup.PolynomialQuotientRepresentation.generalLinearGroupToUnits k N ^ r) (_root_.RepresentationTheory.GeneralLinearGroup.Localization.Auxiliary.subrepresentation φ).toRepresentation).asModule :=
    _root_.RepresentationTheory.AuxiliarySemisimpleDecomposition.isSemisimpleModule_of_auxiliary N
      (_root_.RepresentationTheory.GeneralLinearGroup.PolynomialQuotientRepresentation.twistByCharacter (_root_.RepresentationTheory.GeneralLinearGroup.PolynomialQuotientRepresentation.generalLinearGroupToUnits k N ^ r) (_root_.RepresentationTheory.GeneralLinearGroup.Localization.Auxiliary.subrepresentation φ).toRepresentation) htwAlg
  have huntwist : _root_.RepresentationTheory.GeneralLinearGroup.PolynomialQuotientRepresentation.twistByCharacter (_root_.RepresentationTheory.GeneralLinearGroup.PolynomialQuotientRepresentation.generalLinearGroupToUnits k N ^ r)⁻¹
      (_root_.RepresentationTheory.GeneralLinearGroup.PolynomialQuotientRepresentation.twistByCharacter (_root_.RepresentationTheory.GeneralLinearGroup.PolynomialQuotientRepresentation.generalLinearGroupToUnits k N ^ r) (_root_.RepresentationTheory.GeneralLinearGroup.Localization.Auxiliary.subrepresentation φ).toRepresentation)
      = (_root_.RepresentationTheory.GeneralLinearGroup.Localization.Auxiliary.subrepresentation φ).toRepresentation := by
    ext g v
    rw [_root_.RepresentationTheory.GeneralLinearGroup.PolynomialQuotientRepresentation.twistByCharacter_apply, _root_.RepresentationTheory.GeneralLinearGroup.PolynomialQuotientRepresentation.twistByCharacter_apply, smul_smul, ← Units.val_mul,
      ← MonoidHom.mul_apply, inv_mul_cancel, MonoidHom.one_apply, Units.val_one, one_smul]
  have hfin := _root_.RepresentationTheory.GeneralLinear.AuxiliaryRepresentations.isSemisimpleModule_auxiliaryRepresentationConstruction (_root_.RepresentationTheory.GeneralLinearGroup.PolynomialQuotientRepresentation.generalLinearGroupToUnits k N ^ r)⁻¹
    (_root_.RepresentationTheory.GeneralLinearGroup.PolynomialQuotientRepresentation.twistByCharacter (_root_.RepresentationTheory.GeneralLinearGroup.PolynomialQuotientRepresentation.generalLinearGroupToUnits k N ^ r) (_root_.RepresentationTheory.GeneralLinearGroup.Localization.Auxiliary.subrepresentation φ).toRepresentation)
  rwa [huntwist] at hfin

end RepresentationTheory.Auxiliary.GeneralLinearPolynomialSubrepresentations
