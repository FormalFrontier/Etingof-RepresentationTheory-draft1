/-
Copyright (c) 2026 mathlib-initiative. All rights reserved.
Released under Apache 2.0 license as described in the file LICENCE.
Authors: mathlib-initiative
-/

import Mathlib
import RepresentationTheory.AuxiliaryEquivariantDecomposition
import RepresentationTheory.AsModuleEquivalences
import RepresentationTheory.Alignment.Attribute

set_option maxSynthPendingDepth 3
set_option backward.isDefEq.respectTransparency false

noncomputable section

namespace RepresentationTheory.AuxiliaryRepresentationDecompositions

open RepresentationTheory.Auxiliary.GeneralLinearCoordinateLocalization RepresentationTheory.LinearAlgebra.Matrix.GeneralLinearGroup.LocalizationAction RepresentationTheory.Auxiliary.GeneralLinearPolynomialRealization
  RepresentationTheory.GeneralLinearGroup.PolynomialQuotientRepresentation

/-- Given the displayed auxiliary condition and a linear functional, there exists an auxiliary map satisfying the displayed pointwise identity. -/
theorem auxiliary_exists_map_satisfying_identity
    {n : ℕ} {k : Type} [Field k] {Y : Type} [AddCommGroup Y] [Module k Y] [Module.Finite k Y]
    (ρ : Matrix.GeneralLinearGroup (Fin n) k → Y →ₗ[k] Y)
    (halg : _root_.RepresentationTheory.GeneralLinearGroup.Auxiliary.HasAuxiliaryMapProperty n ρ) (u : Y →ₗ[k] k) :
    ∃ mc : Y →ₗ[k] Localization.Away (_root_.RepresentationTheory.Auxiliary.GeneralLinearCoordinateLocalization.auxiliary_matrix_polynomial k n),
      ∀ (v : Y) (g : Matrix.GeneralLinearGroup (Fin n) k),
        _root_.RepresentationTheory.Auxiliary.GeneralLinearCoordinateLocalization.localization_evaluation_ringHom (mc v) g = u (ρ g v) := by
  classical
  obtain ⟨d, b, P, hP⟩ := halg
  refine ⟨∑ a, ∑ c, LinearMap.smulRight (b.coord c) (u (b a) • _root_.RepresentationTheory.Auxiliary.GeneralLinearCoordinateLocalization.auxiliary_localization_ringHom (P a c)), ?_⟩
  intro v g

  have hmc : (∑ a, ∑ c,
        LinearMap.smulRight (b.coord c) (u (b a) • _root_.RepresentationTheory.Auxiliary.GeneralLinearCoordinateLocalization.auxiliary_localization_ringHom (P a c))) v
      = ∑ a, ∑ c, (b.repr v c * u (b a)) • _root_.RepresentationTheory.Auxiliary.GeneralLinearCoordinateLocalization.auxiliary_localization_ringHom (P a c) := by
    simp only [LinearMap.sum_apply, LinearMap.smulRight_apply, Module.Basis.coord_apply,
      smul_smul]
  rw [hmc, map_sum, Finset.sum_apply]
  have hLHS : ∀ a : Fin d, _root_.RepresentationTheory.Auxiliary.GeneralLinearCoordinateLocalization.localization_evaluation_ringHom (∑ c, (b.repr v c * u (b a)) • _root_.RepresentationTheory.Auxiliary.GeneralLinearCoordinateLocalization.auxiliary_localization_ringHom (P a c)) g
      = ∑ c, (b.repr v c * u (b a)) * _root_.RepresentationTheory.GeneralLinearGroup.Auxiliary.auxiliaryPolynomialEvaluation g (P a c) := by
    intro a
    rw [map_sum, Finset.sum_apply]
    refine Finset.sum_congr rfl fun c _ => ?_
    rw [_root_.RepresentationTheory.Auxiliary.GeneralLinearPolynomialRealization.localization_evaluation_smul, Pi.smul_apply, smul_eq_mul, ← _root_.RepresentationTheory.Auxiliary.GeneralLinearCoordinateLocalization.auxiliary_localization_ringHom_action_apply]
  rw [Finset.sum_congr rfl fun a _ => hLHS a]

  have hexp : u (ρ g v) = ∑ c, b.repr v c * ∑ a, _root_.RepresentationTheory.GeneralLinearGroup.Auxiliary.auxiliaryPolynomialEvaluation g (P a c) * u (b a) := by
    conv_lhs => rw [← b.sum_repr v]
    rw [map_sum, map_sum]
    refine Finset.sum_congr rfl fun c _ => ?_
    rw [map_smul, map_smul, smul_eq_mul]
    congr 1
    conv_lhs => rw [← b.sum_repr (ρ g (b c))]
    rw [map_sum]
    exact Finset.sum_congr rfl fun a _ => by rw [map_smul, smul_eq_mul, hP g a c]
  rw [hexp, Finset.sum_comm]
  refine Finset.sum_congr rfl fun c _ => ?_
  rw [Finset.mul_sum]
  exact Finset.sum_congr rfl fun a _ => by ring

/-- An auxiliary map satisfying the displayed identity sends each image under the representation to the image under the corresponding displayed target map. -/
theorem auxiliaryMap_apply_representation_of_identity
    {n : ℕ} {k : Type} [Field k] [CharZero k]
    {Y : Type} [AddCommGroup Y] [Module k Y]
    (ρ : Representation k (Matrix.GeneralLinearGroup (Fin n) k) Y)
    (u : Y →ₗ[k] k) (mc : Y →ₗ[k] Localization.Away (_root_.RepresentationTheory.Auxiliary.GeneralLinearCoordinateLocalization.auxiliary_matrix_polynomial k n))
    (hmc : ∀ (v : Y) (g : Matrix.GeneralLinearGroup (Fin n) k),
      _root_.RepresentationTheory.Auxiliary.GeneralLinearCoordinateLocalization.localization_evaluation_ringHom (mc v) g = u (ρ g v))
    (g : Matrix.GeneralLinearGroup (Fin n) k) (v : Y) :
    mc (ρ g v) = _root_.RepresentationTheory.LinearAlgebra.Matrix.GeneralLinearGroup.LocalizationAction.generalLinearGroupLocalizationRepresentation k n g (mc v) := by
  apply _root_.RepresentationTheory.Auxiliary.GeneralLinearCoordinateLocalization.localization_evaluation_injective
  funext y
  rw [hmc, _root_.RepresentationTheory.Auxiliary.GeneralLinearPolynomialRealization.localization_evaluation_action_apply, hmc]
  congr 1
  rw [← Module.End.mul_apply, ← map_mul]

private theorem injective_of_isSimpleModule_of_ne_zero
    {n : ℕ} {k : Type} [Field k]
    {Y : Type} [AddCommGroup Y] [Module k Y]
    (ρ : Representation k (Matrix.GeneralLinearGroup (Fin n) k) Y)
    [hsimp : IsSimpleModule (MonoidAlgebra k (Matrix.GeneralLinearGroup (Fin n) k)) ρ.asModule]
    {W : Type} [AddCommGroup W] [Module k W]
    (σ : Representation k (Matrix.GeneralLinearGroup (Fin n) k) W)
    (f : Y →ₗ[k] W)
    (hf : ∀ (g : Matrix.GeneralLinearGroup (Fin n) k) (v : Y), f (ρ g v) = σ g (f v))
    (hne : f ≠ 0) :
    Function.Injective f := by
  have hstable : ∀ (g : Matrix.GeneralLinearGroup (Fin n) k),
      ∀ x ∈ LinearMap.ker f, ρ g (ρ.asModuleEquiv x) ∈ LinearMap.ker f := by
    intro g x hx
    rw [LinearMap.mem_ker] at hx ⊢
    rw [show ρ.asModuleEquiv x = x from rfl, hf, hx, map_zero]
  rcases hsimp.eq_bot_or_eq_top
      (_root_.RepresentationTheory.Algebra.ModuleActions.RingActionStructure.invariantSubmodule ρ (LinearMap.ker f) hstable) with h | h
  · rw [← LinearMap.ker_eq_bot, eq_bot_iff]
    intro x hx
    rw [Submodule.eq_bot_iff] at h
    exact h x ((_root_.RepresentationTheory.Algebra.ModuleActions.RingActionStructure.mem_invariantSubmodule_iff ρ _ hstable x).mpr hx)
  · exfalso
    apply hne
    ext x
    rw [Submodule.eq_top_iff'] at h
    exact (LinearMap.mem_ker).mp
      ((_root_.RepresentationTheory.Algebra.ModuleActions.RingActionStructure.mem_invariantSubmodule_iff ρ _ hstable x).mp (h x))

/-- A simple finite-dimensional general linear group representation satisfying the displayed auxiliary condition is equivalent to a displayed representation for some parameter. -/
theorem auxiliary_exists_representationParameter_of_simple
    (n : ℕ) (k : Type) [Field k] [IsAlgClosed k] [CharZero k]
    {Y : Type} [AddCommGroup Y] [Module k Y] [Module.Finite k Y]
    (ρ : Representation k (Matrix.GeneralLinearGroup (Fin n) k) Y)
    (halg : _root_.RepresentationTheory.GeneralLinearGroup.Auxiliary.HasAuxiliaryMapProperty n ⇑ρ)
    [hsimp : IsSimpleModule (MonoidAlgebra k (Matrix.GeneralLinearGroup (Fin n) k)) ρ.asModule] :
    ∃ lam : _root_.RepresentationTheory.AuxiliaryModuleData.auxiliaryIndex n,
      Nonempty (ρ.asModule ≃ₗ[MonoidAlgebra k (Matrix.GeneralLinearGroup (Fin n) k)]
        (_root_.RepresentationTheory.GeneralLinear.AuxiliaryRepresentations.generalLinearRepresentationOnAuxiliarySpaceAlt n lam k).asModule) := by
  classical

  haveI hnt : Nontrivial Y := by
    have h := (Submodule.nontrivial_iff
      (MonoidAlgebra k (Matrix.GeneralLinearGroup (Fin n) k))).mp hsimp.toNontrivial
    exact (show Nontrivial ρ.asModule from h)

  obtain ⟨d, b, P, hP⟩ := halg
  obtain ⟨v₀, hv₀⟩ := exists_ne (0 : Y)
  have hrepr : b.repr v₀ ≠ 0 := fun h => hv₀ (by simpa using congrArg b.repr.symm h)
  obtain ⟨c₀, hc₀⟩ : ∃ c₀, b.repr v₀ c₀ ≠ 0 := by
    by_contra hcon
    exact hrepr (by ext c; simpa using not_not.mp (not_exists.mp hcon c))
  set u : Y →ₗ[k] k := b.coord c₀ with hu
  have huv₀ : u v₀ ≠ 0 := hc₀

  obtain ⟨mc, hmc⟩ := auxiliary_exists_map_satisfying_identity (n := n) (k := k) ⇑ρ ⟨d, b, P, hP⟩ u
  have hmc_equiv : ∀ (g : Matrix.GeneralLinearGroup (Fin n) k) (v : Y),
      mc (ρ g v) = _root_.RepresentationTheory.LinearAlgebra.Matrix.GeneralLinearGroup.LocalizationAction.generalLinearGroupLocalizationRepresentation k n g (mc v) :=
    fun g v => auxiliaryMap_apply_representation_of_identity ρ u mc hmc g v
  have hmc_ne : mc ≠ 0 := by
    intro h
    apply huv₀
    have := hmc v₀ 1
    rw [h] at this
    simpa using this.symm
  have hmc_inj : Function.Injective mc :=
    injective_of_isSimpleModule_of_ne_zero ρ (_root_.RepresentationTheory.LinearAlgebra.Matrix.GeneralLinearGroup.LocalizationAction.generalLinearGroupLocalizationRepresentation k n) mc hmc_equiv hmc_ne

  set mcKG : ρ.asModule →ₗ[MonoidAlgebra k (Matrix.GeneralLinearGroup (Fin n) k)]
      (_root_.RepresentationTheory.LinearAlgebra.Matrix.GeneralLinearGroup.LocalizationAction.generalLinearGroupLocalizationRepresentation k n).asModule :=
    _root_.RepresentationTheory.AsModuleEquivalences.linearMapAsModule mc hmc_equiv with hmcKG
  have hmcKG_inj : Function.Injective mcKG := hmc_inj
  set S : Subrepresentation (_root_.RepresentationTheory.LinearAlgebra.Matrix.GeneralLinearGroup.LocalizationAction.generalLinearGroupLocalizationRepresentation k n) :=
    Subrepresentation.ofSubmodule' (LinearMap.range mcKG) with hS
  have hS_toSubmodule : S.toSubmodule = LinearMap.range mc := by
    apply SetLike.ext; intro x
    constructor
    · rintro ⟨y, rfl⟩; exact ⟨y, rfl⟩
    · rintro ⟨y, rfl⟩; exact ⟨y, rfl⟩
  haveI hSfin : FiniteDimensional k S.toSubmodule := by
    rw [hS_toSubmodule]; infer_instance
  have hSsimple : IsSimpleModule (MonoidAlgebra k (Matrix.GeneralLinearGroup (Fin n) k))
      (Subrepresentation.asSubmodule S) :=
    (LinearEquiv.isSimpleModule_iff (LinearEquiv.ofInjective mcKG hmcKG_inj)).mp hsimp

  obtain ⟨lam, ι, hι_equiv, hι_range⟩ :=
    _root_.RepresentationTheory.AuxiliaryEquivariantDecomposition.auxiliary_exists_range_eq_of_isSimpleModule n k S hSsimple
  rw [hS_toSubmodule] at hι_range

  haveI := _root_.RepresentationTheory.AuxiliaryEquivariantDecomposition.auxiliary_isSimpleModule n k lam
  have hι_ne : ι ≠ 0 := by
    intro h
    apply hmc_ne
    have hrange0 : LinearMap.range mc = ⊥ := by rw [← hι_range, h, LinearMap.range_zero]
    ext v
    exact (Submodule.eq_bot_iff _).mp hrange0 (mc v) ⟨v, rfl⟩
  have hι_inj : Function.Injective ι :=
    injective_of_isSimpleModule_of_ne_zero (_root_.RepresentationTheory.GeneralLinear.AuxiliaryRepresentations.generalLinearRepresentationOnAuxiliarySpaceAlt n lam k) (_root_.RepresentationTheory.LinearAlgebra.Matrix.GeneralLinearGroup.LocalizationAction.generalLinearGroupLocalizationRepresentation k n) ι
      hι_equiv hι_ne

  set e : _root_.RepresentationTheory.AuxiliaryModuleData.auxiliaryFamily n lam k ≃ₗ[k] Y :=
    (LinearEquiv.ofInjective ι hι_inj).trans
      ((LinearEquiv.ofEq _ _ hι_range).trans (LinearEquiv.ofInjective mc hmc_inj).symm) with he
  have he_spec : ∀ w : _root_.RepresentationTheory.AuxiliaryModuleData.auxiliaryFamily n lam k, mc (e w) = ι w := by
    intro w
    have h2 : (LinearEquiv.ofInjective mc hmc_inj) (e w)
        = (LinearEquiv.ofEq _ _ hι_range) ((LinearEquiv.ofInjective ι hι_inj) w) := by
      rw [he]
      simp only [LinearEquiv.trans_apply, LinearEquiv.apply_symm_apply]
    have h3 : ((LinearEquiv.ofEq _ _ hι_range)
        ((LinearEquiv.ofInjective ι hι_inj) w) : Localization.Away (_root_.RepresentationTheory.Auxiliary.GeneralLinearCoordinateLocalization.auxiliary_matrix_polynomial k n)) = ι w := rfl
    rw [← h3, ← h2]
    rfl
  have he_int : ∀ (g : Matrix.GeneralLinearGroup (Fin n) k) (w : _root_.RepresentationTheory.AuxiliaryModuleData.auxiliaryFamily n lam k),
      e (_root_.RepresentationTheory.GeneralLinear.AuxiliaryRepresentations.generalLinearRepresentationOnAuxiliarySpaceAlt n lam k g w) = ρ g (e w) := by
    intro g w
    apply hmc_inj
    rw [he_spec, hι_equiv, ← he_spec, hmc_equiv]
  exact ⟨lam, ⟨(_root_.RepresentationTheory.AsModuleEquivalences.linearEquivAsModule e he_int).symm⟩⟩

/-- A simple finite-dimensional general linear group representation satisfying the displayed auxiliary condition is equivalent to a uniquely parameterized displayed representation. -/
@[source_ref "Chapter5/Discussion_after_Definition5.23.1" (role := primary)]
theorem auxiliary_existsUnique_representationParameter_of_simple
    (n : ℕ) (k : Type) [Field k] [IsAlgClosed k] [CharZero k]
    {Y : Type} [AddCommGroup Y] [Module k Y] [Module.Finite k Y]
    (ρ : Representation k (Matrix.GeneralLinearGroup (Fin n) k) Y)
    (halg : _root_.RepresentationTheory.GeneralLinearGroup.Auxiliary.HasAuxiliaryMapProperty n ⇑ρ)
    [IsSimpleModule (MonoidAlgebra k (Matrix.GeneralLinearGroup (Fin n) k)) ρ.asModule] :
    ∃! lam : _root_.RepresentationTheory.AuxiliaryModuleData.auxiliaryIndex n,
      Nonempty (ρ.asModule ≃ₗ[MonoidAlgebra k (Matrix.GeneralLinearGroup (Fin n) k)]
        (_root_.RepresentationTheory.GeneralLinear.AuxiliaryRepresentations.generalLinearRepresentationOnAuxiliarySpaceAlt n lam k).asModule) := by
  obtain ⟨lam, ⟨e⟩⟩ := auxiliary_exists_representationParameter_of_simple n k ρ halg
  refine ⟨lam, ⟨e⟩, fun mu ⟨f⟩ => ?_⟩
  exact (_root_.RepresentationTheory.AuxiliaryRepresentationParameters.auxiliaryRepresentation_linearEquiv_iff_parameters_eq n k).mp ⟨f.symm.trans e⟩

/-- A simple submodule of a representation satisfying the displayed auxiliary condition is equivalent to a displayed representation for some parameter. -/
theorem auxiliary_simpleSubmodule_exists_representationParameter
    (n : ℕ) (k : Type) [Field k] [IsAlgClosed k] [CharZero k]
    {Y : Type} [AddCommGroup Y] [Module k Y] [Module.Finite k Y]
    (ρ : Representation k (Matrix.GeneralLinearGroup (Fin n) k) Y)
    (halg : _root_.RepresentationTheory.GeneralLinearGroup.Auxiliary.HasAuxiliaryMapProperty n ⇑ρ)
    (S : Submodule (MonoidAlgebra k (Matrix.GeneralLinearGroup (Fin n) k)) ρ.asModule)
    (hS : IsSimpleModule (MonoidAlgebra k (Matrix.GeneralLinearGroup (Fin n) k)) S) :
    ∃ lam : _root_.RepresentationTheory.AuxiliaryModuleData.auxiliaryIndex n,
      Nonempty (S ≃ₗ[MonoidAlgebra k (Matrix.GeneralLinearGroup (Fin n) k)]
        (_root_.RepresentationTheory.GeneralLinear.AuxiliaryRepresentations.generalLinearRepresentationOnAuxiliarySpaceAlt n lam k).asModule) := by
  classical

  set T : Subrepresentation ρ := Subrepresentation.ofSubmodule' S with hT
  set σ : Representation k (Matrix.GeneralLinearGroup (Fin n) k) T.toSubmodule :=
    T.toRepresentation with hσ
  haveI : Module.Finite k T.toSubmodule := Module.Finite.of_injective T.toSubmodule.subtype
    Subtype.coe_injective

  have hsub : ∀ (g : Matrix.GeneralLinearGroup (Fin n) k) (x : T.toSubmodule),
      T.toSubmodule.subtype (σ g x) = ρ g (T.toSubmodule.subtype x) :=
    fun g x => LinearMap.coe_restrict_apply (T.apply_mem_toSubmodule g) x
  set incl : Representation.asModule σ →ₗ[MonoidAlgebra k
      (Matrix.GeneralLinearGroup (Fin n) k)] ρ.asModule :=
    _root_.RepresentationTheory.AsModuleEquivalences.linearMapAsModule T.toSubmodule.subtype hsub with hincl
  have hincl_inj : Function.Injective incl := by
    intro a b hab
    apply σ.asModuleEquiv.injective
    apply Subtype.coe_injective
    exact hab
  have hrange : LinearMap.range incl = S := by
    apply SetLike.ext; intro x
    rw [LinearMap.mem_range]
    constructor
    · rintro ⟨y, rfl⟩; exact y.2
    · intro hx; exact ⟨⟨x, hx⟩, rfl⟩
  set eS : Representation.asModule σ ≃ₗ[MonoidAlgebra k
      (Matrix.GeneralLinearGroup (Fin n) k)] S :=
    (LinearEquiv.ofInjective incl hincl_inj).trans (LinearEquiv.ofEq _ _ hrange) with heS

  haveI : IsSimpleModule (MonoidAlgebra k (Matrix.GeneralLinearGroup (Fin n) k))
      (Representation.asModule σ) := (LinearEquiv.isSimpleModule_iff eS).mpr hS
  have halgσ : _root_.RepresentationTheory.GeneralLinearGroup.Auxiliary.HasAuxiliaryMapProperty n ⇑σ :=
    halg.auxiliary_restrict T.toSubmodule (fun g _ hv => T.apply_mem_toSubmodule g hv)
  obtain ⟨lam, ⟨f⟩⟩ := auxiliary_exists_representationParameter_of_simple n k σ halgσ
  exact ⟨lam, ⟨eS.symm.trans f⟩⟩

/-- A finite-dimensional general linear group representation satisfying the displayed auxiliary condition is equivalent to a finite direct sum of displayed representations. -/
@[source_ref "Chapter5/Theorem5.23.2" (role := supporting)]
theorem auxiliary_exists_directSum_representation_decomposition
    (n : ℕ) (k : Type) [Field k] [IsAlgClosed k] [CharZero k]
    {Y : Type} [AddCommGroup Y] [Module k Y] [Module.Finite k Y]
    (ρ : Representation k (Matrix.GeneralLinearGroup (Fin n) k) Y)
    (halg : _root_.RepresentationTheory.GeneralLinearGroup.Auxiliary.HasAuxiliaryMapProperty n ⇑ρ) :
    ∃ (p : ℕ) (lam : Fin p → _root_.RepresentationTheory.AuxiliaryModuleData.auxiliaryIndex n),
      Nonempty (ρ.asModule ≃ₗ[MonoidAlgebra k (Matrix.GeneralLinearGroup (Fin n) k)]
        DirectSum (Fin p) fun j => (_root_.RepresentationTheory.GeneralLinear.AuxiliaryRepresentations.generalLinearRepresentationOnAuxiliarySpaceAlt n (lam j) k).asModule) := by
  classical
  haveI hss : IsSemisimpleModule (MonoidAlgebra k (Matrix.GeneralLinearGroup (Fin n) k))
      ρ.asModule := _root_.RepresentationTheory.AuxiliarySemisimpleDecomposition.isSemisimpleModule_of_auxiliary n ρ halg
  haveI : Module.Finite (MonoidAlgebra k (Matrix.GeneralLinearGroup (Fin n) k))
      ρ.asModule :=
    Module.Finite.of_restrictScalars_finite k
      (MonoidAlgebra k (Matrix.GeneralLinearGroup (Fin n) k)) ρ.asModule
  obtain ⟨p, S, e, hSsimple⟩ := IsSemisimpleModule.exists_linearEquiv_fin_dfinsupp
    (MonoidAlgebra k (Matrix.GeneralLinearGroup (Fin n) k)) ρ.asModule
  choose lam hlam using fun j : Fin p =>
    auxiliary_simpleSubmodule_exists_representationParameter n k ρ halg (S j) (hSsimple j)
  refine ⟨p, lam, ⟨e.trans (DFinsupp.mapRange.linearEquiv fun j => (hlam j).some)⟩⟩

end RepresentationTheory.AuxiliaryRepresentationDecompositions
