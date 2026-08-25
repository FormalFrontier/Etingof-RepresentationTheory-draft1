/-
Copyright (c) 2026 mathlib-initiative. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: mathlib-initiative
-/

import RepresentationTheory.GeneralLinear.WeightedPolynomialIndexShift
import RepresentationTheory.GeneralLinear.AuxiliaryPolynomialIdentities
import RepresentationTheory.MatrixPolynomialHomogeneity

open MvPolynomial

namespace RepresentationTheory.GeneralLinear.AuxiliaryRepresentationFamilies

open RepresentationTheory.Auxiliary.AuxiliaryPolynomialSubrepresentation
open RepresentationTheory.Auxiliary.GeneralLinearCoordinateLocalization
open RepresentationTheory.AuxiliaryCharacter
open RepresentationTheory.GeneralLinear.AuxiliaryPolynomialEmbedding
open RepresentationTheory.GeneralLinear.AuxiliaryPolynomialIdentities
open RepresentationTheory.GeneralLinear.HomogeneousPolynomialsAndAuxiliaryRepresentations
open RepresentationTheory.GeneralLinear.WeightedPolynomialIndexShift
open RepresentationTheory.GeneralLinearGroup.PolynomialQuotientRepresentation
open RepresentationTheory.GeneralLinearGroup.WeightCharacter
open RepresentationTheory.Matrix.MvPolynomialRightMul.Matrix
open RepresentationTheory.MatrixPolynomialHomogeneity
open RepresentationTheory.SymmetricPolynomials.Alternant

variable {k : Type*} [Field k] [IsAlgClosed k] [CharZero k]

omit [CharZero k] in
/-- Membership in the auxiliary submodule is equivalent to the displayed coordinate-indexed group
elements acting by the prescribed powers. -/
theorem mem_auxiliarySubmodule_iff_action_eq_smul (N : ℕ)
    (M : FDRep k (Matrix.GeneralLinearGroup (Fin N) k)) (μ : Fin N → ℕ) (v : M) :
    v ∈ weightSpace k N M μ ↔
      ∀ (i : Fin N) (t : kˣ), M.ρ (diagonalUnit k N i t) v = (t : k) ^ μ i • v := by
  simp only [weightSpace, Submodule.mem_iInf, LinearMap.mem_ker, LinearMap.sub_apply,
    LinearMap.smul_apply, LinearMap.id_apply, sub_eq_zero]

omit [CharZero k] in
/-- An equivariant linear map sends each displayed auxiliary submodule into the corresponding
target auxiliary submodule. -/
theorem map_auxiliarySubmodule_le (N : ℕ)
    (V W : FDRep k (Matrix.GeneralLinearGroup (Fin N) k))
    (f : V →ₗ[k] W) (hf : ∀ g v, f (V.ρ g v) = W.ρ g (f v)) (μ : Fin N → ℕ) :
    (weightSpace k N V μ).map f ≤ weightSpace k N W μ := by
  rintro _ ⟨v, hv, rfl⟩
  simp only [SetLike.mem_coe, mem_auxiliarySubmodule_iff_action_eq_smul] at hv ⊢
  intro i t
  rw [← hf, hv i t, map_smul]

omit [CharZero k] in
/-- For an injective equivariant linear map, the target auxiliary submodule intersected with the
range equals the image of the corresponding source auxiliary submodule. -/
theorem auxiliarySubmodule_inf_range_eq_map (N : ℕ)
    (U V : FDRep k (Matrix.GeneralLinearGroup (Fin N) k))
    (ι : U →ₗ[k] V) (hι : ∀ g u, ι (U.ρ g u) = V.ρ g (ι u))
    (hι_inj : Function.Injective ι) (μ : Fin N → ℕ) :
    weightSpace k N V μ ⊓ LinearMap.range ι = (weightSpace k N U μ).map ι := by
  apply le_antisymm
  · rintro x ⟨hxV, u, rfl⟩
    refine ⟨u, ?_, rfl⟩
    simp only [SetLike.mem_coe, mem_auxiliarySubmodule_iff_action_eq_smul] at hxV ⊢
    intro i t
    apply hι_inj
    rw [hι, map_smul, hxV i t]
  · refine le_inf (map_auxiliarySubmodule_le N U V ι hι μ) ?_
    rintro _ ⟨u, _, rfl⟩
    exact ⟨u, rfl⟩

/-- For the displayed equivariant exact pair, if the indicated auxiliary submodules span, the
middle auxiliary polynomial is the sum of the other two. -/
theorem auxiliaryPolynomial_eq_add_of_exact (N : ℕ)
    (U V W : FDRep k (Matrix.GeneralLinearGroup (Fin N) k))
    (ι : U →ₗ[k] V) (π : V →ₗ[k] W)
    (hι : ∀ g u, ι (U.ρ g u) = V.ρ g (ι u))
    (hπ : ∀ g v, π (V.ρ g v) = W.ρ g (π v))
    (hι_inj : Function.Injective ι)
    (hπ_surj : Function.Surjective π)
    (hexact : LinearMap.range ι = LinearMap.ker π)
    (hUtop : ⨆ μ : Fin N →₀ ℕ, weightSpace k N U (fun i => μ i) = ⊤)
    (hVtop : ⨆ μ : Fin N →₀ ℕ, weightSpace k N V (fun i => μ i) = ⊤) :
    weightCharacter k N V = weightCharacter k N U + weightCharacter k N W := by
  classical
  have hWtop : ⨆ μ : Fin N →₀ ℕ, weightSpace k N W (fun i => μ i) = ⊤ := by
    have h1 : (⨆ μ : Fin N →₀ ℕ, weightSpace k N V (fun i => μ i)).map π
        = ⨆ μ : Fin N →₀ ℕ, (weightSpace k N V (fun i => μ i)).map π :=
      Submodule.map_iSup _ _
    rw [hVtop, Submodule.map_top, LinearMap.range_eq_top.mpr hπ_surj] at h1
    have h2 : (⨆ μ : Fin N →₀ ℕ, (weightSpace k N V (fun i => μ i)).map π)
        ≤ ⨆ μ : Fin N →₀ ℕ, weightSpace k N W (fun i => μ i) :=
      iSup_mono fun μ => map_auxiliarySubmodule_le N V W π hπ _
    exact top_le_iff.mp (h1 ▸ h2)
  have hsplit : ∀ μ : Fin N →₀ ℕ,
      Module.finrank k (weightSpace k N V (fun i => μ i))
        = Module.finrank k ((weightSpace k N V (fun i => μ i)).map π)
          + Module.finrank k (weightSpace k N U (fun i => μ i)) := by
    intro μ
    have hrn := LinearMap.finrank_range_add_finrank_ker
      (π ∘ₗ (weightSpace k N V (fun i => μ i)).subtype)
    rw [LinearMap.range_comp, Submodule.range_subtype] at hrn
    have hk : Module.finrank k
          (LinearMap.ker (π ∘ₗ (weightSpace k N V (fun i => μ i)).subtype))
        = Module.finrank k (weightSpace k N U (fun i => μ i)) := by
      rw [LinearMap.ker_comp,
        (Submodule.equivMapOfInjective _
          (Submodule.injective_subtype (weightSpace k N V (fun i => μ i)))
          (Submodule.comap (weightSpace k N V (fun i => μ i)).subtype
            (LinearMap.ker π))).finrank_eq,
        Submodule.map_comap_subtype, ← hexact,
        auxiliarySubmodule_inf_range_eq_map N U V ι hι hι_inj (fun i => μ i),
        ← (Submodule.equivMapOfInjective ι hι_inj
            (weightSpace k N U (fun i => μ i))).finrank_eq]
    rw [hk] at hrn
    omega
  have hle : ∀ μ : Fin N →₀ ℕ,
      Module.finrank k (weightSpace k N V (fun i => μ i))
        ≤ Module.finrank k (weightSpace k N U (fun i => μ i))
          + Module.finrank k (weightSpace k N W (fun i => μ i)) := by
    intro μ
    rw [hsplit μ, add_comm]
    exact Nat.add_le_add_left
      (Submodule.finrank_mono (map_auxiliarySubmodule_le N V W π hπ (fun i => μ i))) _
  set S : Finset (Fin N →₀ ℕ) :=
    (finite_support_weightSpace k N U).toFinset
      ∪ (finite_support_weightSpace k N V).toFinset
      ∪ (finite_support_weightSpace k N W).toFinset with hS
  have zero_of : ∀ (M : FDRep k (Matrix.GeneralLinearGroup (Fin N) k)) (μ : Fin N →₀ ℕ),
      μ ∉ (finite_support_weightSpace k N M).toFinset →
      Module.finrank k (weightSpace k N M (fun i => μ i)) = 0 := by
    intro M μ hμ
    have : weightSpace k N M (fun i => μ i) = ⊥ := by
      by_contra h; exact hμ ((finite_support_weightSpace k N M).mem_toFinset.mpr h)
    rw [this, finrank_bot]
  have hsumV : ∑ μ ∈ S, Module.finrank k (weightSpace k N V (fun i => μ i))
      = Module.finrank k V := by
    rw [finrank_eq_sum_finrank_auxiliaryWeightSpace k N V hVtop]
    refine (Finset.sum_subset ?_ (fun μ _ hμ => zero_of V μ hμ)).symm
    rw [hS]; exact Finset.subset_union_right.trans Finset.subset_union_left
  have hsumU : ∑ μ ∈ S, Module.finrank k (weightSpace k N U (fun i => μ i))
      = Module.finrank k U := by
    rw [finrank_eq_sum_finrank_auxiliaryWeightSpace k N U hUtop]
    refine (Finset.sum_subset ?_ (fun μ _ hμ => zero_of U μ hμ)).symm
    rw [hS]; exact Finset.subset_union_left.trans Finset.subset_union_left
  have hsumW : ∑ μ ∈ S, Module.finrank k (weightSpace k N W (fun i => μ i))
      = Module.finrank k W := by
    rw [finrank_eq_sum_finrank_auxiliaryWeightSpace k N W hWtop]
    refine (Finset.sum_subset ?_ (fun μ _ hμ => zero_of W μ hμ)).symm
    rw [hS]; exact Finset.subset_union_right
  have hrnπ := LinearMap.finrank_range_add_finrank_ker π
  rw [LinearMap.range_eq_top.mpr hπ_surj, finrank_top, ← hexact,
    ← (LinearEquiv.ofInjective ι hι_inj).finrank_eq] at hrnπ
  have hsumeq : ∑ μ ∈ S, Module.finrank k (weightSpace k N V (fun i => μ i))
      = ∑ μ ∈ S, (Module.finrank k (weightSpace k N U (fun i => μ i))
          + Module.finrank k (weightSpace k N W (fun i => μ i))) := by
    rw [Finset.sum_add_distrib, hsumU, hsumW, hsumV]; omega
  have hterm := (Finset.sum_eq_sum_iff_of_le (fun μ _ => hle μ)).mp hsumeq
  have hdim : ∀ μ : Fin N →₀ ℕ,
      Module.finrank k (weightSpace k N V (fun i => μ i))
        = Module.finrank k (weightSpace k N U (fun i => μ i))
          + Module.finrank k (weightSpace k N W (fun i => μ i)) := by
    intro μ
    by_cases hμS : μ ∈ S
    · exact hterm μ hμS
    · have hVμ := zero_of V μ (fun h => hμS (by
        rw [hS]; exact Finset.mem_union_left _ (Finset.mem_union_right _ h)))
      have hUμ := zero_of U μ (fun h => hμS (by
        rw [hS]; exact Finset.mem_union_left _ (Finset.mem_union_left _ h)))
      have hWμ := zero_of W μ (fun h => hμS (by rw [hS]; exact Finset.mem_union_right _ h))
      rw [hVμ, hUμ, hWμ]
  ext μ
  rw [MvPolynomial.coeff_add, coeff_weightCharacter, coeff_weightCharacter,
    coeff_weightCharacter]
  rw [hdim μ]; push_cast; ring

omit [IsAlgClosed k] [CharZero k] in
/-- The displayed units-valued map sends the auxiliary element indexed by a coordinate and a unit
to a unit with the same value. -/
theorem auxiliaryUnitsMap_apply_auxiliaryElement (N : ℕ) (i : Fin N) (t : kˣ) :
    ((generalLinearGroupToUnits k N (diagonalUnit k N i t) : kˣ) : k) = (t : k) := by
  rw [generalLinearGroupToUnits, Matrix.GeneralLinearGroup.val_det_apply]
  change (Matrix.diagonal (Function.update (1 : Fin N → k) i (t : k))).det = (t : k)
  rw [Matrix.det_diagonal, Finset.prod_update_of_mem (Finset.mem_univ i)]
  simp

omit [CharZero k] in
/-- The supremum of the displayed auxiliary submodules is top. -/
theorem iSup_auxiliarySubmodule_eq_top {N : ℕ} (d : ℕ) :
    ⨆ μ : Fin N →₀ ℕ,
      weightSpace k N (auxiliaryIndexedGeneralLinearFDRep k N d) (fun i => μ i) = ⊤ := by
  classical
  refine Submodule.map_injective_of_injective (auxiliaryPolynomialEmbedding_injective d) ?_
  rw [Submodule.map_iSup, Submodule.map_top]
  have hrange : LinearMap.range (auxiliaryPolynomialEmbedding d)
      = MvPolynomial.homogeneousSubmodule (Fin N × Fin N) k d :=
    Submodule.range_subtype _
  rw [hrange]
  simp_rw [map_auxiliarySubmodule_auxiliaryPolynomialEmbedding, ← Submodule.span_iUnion]
  have hunion : (⋃ μ : Fin N →₀ ℕ,
        (fun s => MvPolynomial.monomial s (1 : k)) ''
          (auxiliaryMatrixExponentFinset N d μ : Set _))
      = (fun s => MvPolynomial.monomial s (1 : k)) ''
          { s : (Fin N × Fin N) →₀ ℕ | ∑ p, s p = d } := by
    ext x
    simp only [Set.mem_iUnion, Set.mem_image, Finset.mem_coe,
      mem_auxiliaryMatrixExponentFinset_iff, Set.mem_setOf_eq]
    constructor
    · rintro ⟨μ, s, ⟨hsum, _⟩, rfl⟩; exact ⟨s, hsum, rfl⟩
    · rintro ⟨s, hsum, rfl⟩
      exact ⟨Finsupp.equivFunOnFinite.symm (fun j => ∑ i, s (i, j)), s,
        ⟨hsum, fun j => by simp⟩, rfl⟩
  rw [hunion]
  apply le_antisymm
  · rw [Submodule.span_le]
    rintro _ ⟨s, hs, rfl⟩
    exact (MvPolynomial.mem_homogeneousSubmodule d _).2
      (MvPolynomial.isHomogeneous_monomial _ (by rw [Finsupp.degree_eq_sum]; exact hs))
  · intro f hf
    rw [(f).as_sum]
    refine Submodule.sum_mem _ fun s hs => ?_
    have hdeg : ∑ p, s p = d := by
      have hH : f.IsHomogeneous d := (MvPolynomial.mem_homogeneousSubmodule d _).1 hf
      have := hH (MvPolynomial.mem_support_iff.mp hs)
      rwa [← Finsupp.degree_eq_sum, Finsupp.degree_eq_weight_one]
    rw [show (MvPolynomial.monomial s (MvPolynomial.coeff s f)
          : MvPolynomial (Fin N × Fin N) k)
        = MvPolynomial.coeff s f • MvPolynomial.monomial s 1 by
        rw [MvPolynomial.smul_monomial, smul_eq_mul, mul_one]]
    exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨s, hdeg, rfl⟩)

omit [CharZero k] in
/-- If the displayed auxiliary submodule is not bottom, the sum of its indices equals the degree. -/
theorem sum_eq_degree_of_auxiliarySubmodule_ne_bot {N : ℕ} (d : ℕ) (μ : Fin N → ℕ)
    (h : weightSpace k N (auxiliaryIndexedGeneralLinearFDRep k N d) μ ≠ ⊥) :
    ∑ i, μ i = d := by
  classical
  by_contra hne
  apply h
  have hExponentSet : auxiliaryMatrixExponentFinset N d μ = ∅ := by
    rw [Finset.eq_empty_iff_forall_notMem]
    intro s hs
    rw [mem_auxiliaryMatrixExponentFinset_iff] at hs
    obtain ⟨hsum, hcol⟩ := hs
    apply hne
    calc ∑ i, μ i = ∑ j, ∑ i, s (i, j) := Finset.sum_congr rfl (fun j _ => (hcol j).symm)
      _ = ∑ p, s p := by rw [Fintype.sum_prod_type]; exact Finset.sum_comm.symm
      _ = d := hsum
  apply Submodule.map_injective_of_injective (auxiliaryPolynomialEmbedding_injective d)
  rw [Submodule.map_bot, map_auxiliarySubmodule_auxiliaryPolynomialEmbedding, hExponentSet]
  simp

/-- An auxiliary natural-number-indexed family of subrepresentations of the displayed
representation. -/
noncomputable def auxiliarySubrepresentationFamily (k : Type*) [Field k] (N d : ℕ) :
    Subrepresentation (matrixPolynomialQuotientRepresentation k N) where
  toSubmodule :=
    (MvPolynomial.homogeneousSubmodule (Fin N × Fin N) k d).map
      (Submodule.mkQ (matrixIndexedPolynomialSubmodule k N))
  apply_mem_toSubmodule g x hx := by
    obtain ⟨f, hf, rfl⟩ := hx
    refine ⟨generalLinearGroupMvPolynomialRightMul k N g f, ?_, ?_⟩
    · exact (MvPolynomial.mem_homogeneousSubmodule d _).2
        (generalLinearAction_preserves_isHomogeneous g
          ((MvPolynomial.mem_homogeneousSubmodule d _).1 hf))
    · rw [Submodule.mkQ_apply, Submodule.mkQ_apply,
        matrixPolynomialQuotientRepresentation_apply_mk]

/-- An auxiliary natural-number-indexed family of finite-dimensional general linear group
representations. -/
noncomputable def auxiliaryRepresentationFamilyOne (k : Type*) [Field k] (N d : ℕ) :
    FDRep k (Matrix.GeneralLinearGroup (Fin N) k) :=
  haveI : FiniteDimensional k (MvPolynomial.homogeneousSubmodule (Fin N × Fin N) k d) :=
    finiteDimensional_homogeneousSubmodule d
  haveI : FiniteDimensional k (auxiliarySubrepresentationFamily k N d).toSubmodule :=
    inferInstanceAs (FiniteDimensional k
      ((MvPolynomial.homogeneousSubmodule (Fin N × Fin N) k d).map
        (Submodule.mkQ (matrixIndexedPolynomialSubmodule k N))))
  FDRep.of (auxiliarySubrepresentationFamily k N d).toRepresentation

/-- An auxiliary linear map from the displayed source representation to the first auxiliary
representation family. -/
noncomputable def auxiliaryLinearMapToFamilyOne (k : Type*) [Field k] (N d : ℕ) :
    auxiliaryIndexedGeneralLinearFDRep k N d →ₗ[k] auxiliaryRepresentationFamilyOne k N d :=
  (Submodule.mkQ (matrixIndexedPolynomialSubmodule k N)).restrict
    (fun _ (hx : _ ∈ MvPolynomial.homogeneousSubmodule (Fin N × Fin N) k d) =>
      Submodule.mem_map_of_mem hx)

omit [IsAlgClosed k] [CharZero k] in
/-- The auxiliary linear map onto the first representation family is surjective. -/
theorem auxiliaryLinearMapToFamilyOne_surjective {N : ℕ} (d : ℕ) :
    Function.Surjective (auxiliaryLinearMapToFamilyOne k N d) := by
  rintro ⟨_, f, hf, rfl⟩
  exact ⟨⟨f, hf⟩, rfl⟩

omit [IsAlgClosed k] [CharZero k] in
/-- The auxiliary linear map to the first family commutes with the general linear group action. -/
theorem auxiliaryLinearMapToFamilyOne_equivariant {N : ℕ} (d : ℕ)
    (g : Matrix.GeneralLinearGroup (Fin N) k) (v : auxiliaryIndexedGeneralLinearFDRep k N d) :
    auxiliaryLinearMapToFamilyOne k N d ((auxiliaryIndexedGeneralLinearFDRep k N d).ρ g v)
      = (auxiliaryRepresentationFamilyOne k N d).ρ g (auxiliaryLinearMapToFamilyOne k N d v) := by
  let eV : auxiliaryIndexedGeneralLinearFDRep k N d →ₗ[k]
      MvPolynomial (Fin N × Fin N) k := auxiliaryPolynomialEmbedding d
  let eW : auxiliaryRepresentationFamilyOne k N d →ₗ[k]
      (MvPolynomial (Fin N × Fin N) k ⧸ matrixIndexedPolynomialSubmodule k N) :=
    (auxiliarySubrepresentationFamily k N d).toSubmodule.subtype
  have eW_inj : Function.Injective eW := Subtype.coe_injective
  have eV_rho : ∀ (g : Matrix.GeneralLinearGroup (Fin N) k)
      (v : auxiliaryIndexedGeneralLinearFDRep k N d),
      eV ((auxiliaryIndexedGeneralLinearFDRep k N d).ρ g v) =
        generalLinearGroupMvPolynomialRightMul k N g (eV v) := fun _ _ => rfl
  have eW_rho : ∀ (g : Matrix.GeneralLinearGroup (Fin N) k)
      (w : auxiliaryRepresentationFamilyOne k N d),
      eW ((auxiliaryRepresentationFamilyOne k N d).ρ g w) =
        matrixPolynomialQuotientRepresentation k N g (eW w) := fun _ _ => rfl
  have eW_π : ∀ v, eW (auxiliaryLinearMapToFamilyOne k N d v) =
      Submodule.mkQ (matrixIndexedPolynomialSubmodule k N) (eV v) :=
    fun _ => rfl
  apply eW_inj
  rw [eW_π, eW_rho, eW_π, eV_rho]
  simp only [Submodule.mkQ_apply, matrixPolynomialQuotientRepresentation_apply_mk]

omit [CharZero k] in
/-- The supremum of the indicated auxiliary submodules for the first family is top. -/
theorem iSup_familyOneAuxiliarySubmodule_eq_top {N : ℕ} (d : ℕ) :
    ⨆ μ : Fin N →₀ ℕ,
        weightSpace k N (auxiliaryRepresentationFamilyOne k N d) (fun i => μ i) = ⊤ := by
  have h1 : (⨆ μ : Fin N →₀ ℕ,
        weightSpace k N (auxiliaryIndexedGeneralLinearFDRep k N d) (fun i => μ i)).map
          (auxiliaryLinearMapToFamilyOne k N d)
      = ⨆ μ : Fin N →₀ ℕ,
          (weightSpace k N (auxiliaryIndexedGeneralLinearFDRep k N d) (fun i => μ i)).map
            (auxiliaryLinearMapToFamilyOne k N d) :=
    Submodule.map_iSup _ _
  rw [iSup_auxiliarySubmodule_eq_top, Submodule.map_top,
    LinearMap.range_eq_top.mpr (auxiliaryLinearMapToFamilyOne_surjective d)] at h1
  have h2 : (⨆ μ : Fin N →₀ ℕ,
        (weightSpace k N (auxiliaryIndexedGeneralLinearFDRep k N d) (fun i => μ i)).map
          (auxiliaryLinearMapToFamilyOne k N d))
      ≤ ⨆ μ : Fin N →₀ ℕ,
        weightSpace k N (auxiliaryRepresentationFamilyOne k N d) (fun i => μ i) :=
    iSup_mono fun μ => map_auxiliarySubmodule_le N _ _ (auxiliaryLinearMapToFamilyOne k N d)
      (auxiliaryLinearMapToFamilyOne_equivariant d) _
  exact top_le_iff.mp (h1 ▸ h2)

/-- If an indicated auxiliary submodule for the first family is not bottom, its coordinate sum
equals the degree. -/
theorem sum_eq_degree_of_familyOneAuxiliarySubmodule_ne_bot {N : ℕ} (d : ℕ) (μ : Fin N → ℕ)
    (h : weightSpace k N (auxiliaryRepresentationFamilyOne k N d) μ ≠ ⊥) :
    ∑ i, μ i = d := by
  classical
  by_contra hne
  set μ₀ : Fin N →₀ ℕ := Finsupp.equivFunOnFinite.symm μ with hμ₀
  have hμ₀μ : (fun i => μ₀ i) = μ := by funext i; rw [hμ₀]; simp
  have hindep := iSupIndep_auxiliaryWeightSpace k N (auxiliaryRepresentationFamilyOne k N d)
  have hdisj := hindep μ₀
  have hsup : (⊤ : Submodule k (auxiliaryRepresentationFamilyOne k N d))
      ≤ ⨆ (ν : Fin N →₀ ℕ) (_ : ν ≠ μ₀),
          weightSpace k N (auxiliaryRepresentationFamilyOne k N d) (fun i => ν i) := by
    have hrange : (⨆ ν : Fin N →₀ ℕ,
          (weightSpace k N (auxiliaryIndexedGeneralLinearFDRep k N d) (fun i => ν i)).map
            (auxiliaryLinearMapToFamilyOne k N d)) = ⊤ := by
      rw [← Submodule.map_iSup, iSup_auxiliarySubmodule_eq_top, Submodule.map_top,
        LinearMap.range_eq_top.mpr (auxiliaryLinearMapToFamilyOne_surjective d)]
    rw [← hrange]
    refine iSup_le fun ν => ?_
    by_cases hν : ν = μ₀
    · rw [hν]
      have hVbot :
          weightSpace k N (auxiliaryIndexedGeneralLinearFDRep k N d) (fun i => μ₀ i) = ⊥ := by
        by_contra hVne
        have hsum : ∑ i, μ₀ i = d :=
          sum_eq_degree_of_auxiliarySubmodule_ne_bot d (fun i => μ₀ i) hVne
        exact hne (by simpa only [hμ₀μ] using hsum)
      rw [hVbot, Submodule.map_bot]
      exact bot_le
    · exact le_iSup₂_of_le ν hν
        (map_auxiliarySubmodule_le N _ _ (auxiliaryLinearMapToFamilyOne k N d)
          (auxiliaryLinearMapToFamilyOne_equivariant d) _)
  rw [top_le_iff] at hsup
  rw [hsup] at hdisj
  have hbot := hdisj.eq_bot_of_le le_top
  simp only [hμ₀μ] at hbot
  exact h hbot

/-- A second auxiliary natural-number-indexed family of finite-dimensional general linear group
representations. -/
noncomputable def auxiliaryRepresentationFamilyTwo (k : Type*) [Field k] (N e : ℕ) :
    FDRep k (Matrix.GeneralLinearGroup (Fin N) k) :=
  haveI : FiniteDimensional k (homogeneousSubrepresentation k N e).toSubmodule :=
    finiteDimensional_homogeneousSubmodule e
  FDRep.of (twistByCharacter (generalLinearGroupToUnits k N)
    (homogeneousSubrepresentation k N e).toRepresentation)

omit [IsAlgClosed k] [CharZero k] in
/-- The action on the second auxiliary family equals the displayed representation action scaled by
the value of the indicated units-valued map. -/
theorem auxiliaryRepresentationFamilyTwo_action_eq_unitsVal_smul
    (e : ℕ) (g : Matrix.GeneralLinearGroup (Fin N) k)
    (v : auxiliaryRepresentationFamilyTwo k N e) :
    (auxiliaryRepresentationFamilyTwo k N e).ρ g v
      = (generalLinearGroupToUnits k N g : k) •
        (auxiliaryIndexedGeneralLinearFDRep k N e).ρ g v := by
  change (twistByCharacter (generalLinearGroupToUnits k N)
      (homogeneousSubrepresentation k N e).toRepresentation) g v =
    (generalLinearGroupToUnits k N g : k) •
      (homogeneousSubrepresentation k N e).toRepresentation g v
  rw [twistByCharacter_apply]

omit [CharZero k] in
/-- When every coordinate is positive, the auxiliary submodule for the second family equals that
for the displayed source representation at the coordinatewise predecessor. -/
theorem auxiliarySubmodule_familyTwo_eq_source_shift
    (e : ℕ) (μ : Fin N → ℕ) (hμ : ∀ i, 1 ≤ μ i) :
    weightSpace k N (auxiliaryRepresentationFamilyTwo k N e) μ
      = weightSpace k N (auxiliaryIndexedGeneralLinearFDRep k N e) (fun i => μ i - 1) := by
  letI : FiniteDimensional k (homogeneousSubrepresentation k N e).toSubmodule :=
    finiteDimensional_homogeneousSubmodule e
  change weightSpace k N
      (FDRep.of (twistByCharacter (generalLinearGroupToUnits k N)
        (homogeneousSubrepresentation k N e).toRepresentation)) μ =
    weightSpace k N
      (FDRep.of (homogeneousSubrepresentation k N e).toRepresentation)
        (fun i => μ i - 1)
  ext v
  rw [mem_auxiliarySubmodule_iff_action_eq_smul, mem_auxiliarySubmodule_iff_action_eq_smul]
  refine forall_congr' fun i => forall_congr' fun t => ?_
  rw [FDRep.of_ρ', twistByCharacter_apply,
    auxiliaryUnitsMap_apply_auxiliaryElement]
  constructor
  · intro h
    refine smul_right_injective _ (Units.ne_zero t) ?_
    change (t : k) • (homogeneousSubrepresentation k N e).toRepresentation
        (diagonalUnit k N i t) v
        = (t : k) • ((t : k) ^ (μ i - 1) • v)
    rw [h, smul_smul, ← pow_succ', Nat.sub_add_cancel (hμ i)]
  · intro h
    change (homogeneousSubrepresentation k N e).toRepresentation
      (diagonalUnit k N i t) v = (t : k) ^ (μ i - 1) • v at h
    rw [h, smul_smul, ← pow_succ', Nat.sub_add_cancel (hμ i)]

omit [CharZero k] in
/-- A zero coordinate makes the indicated auxiliary submodule for the second family equal to
bottom. -/
theorem auxiliarySubmodule_familyTwo_eq_bot_of_coord_eq_zero
    (e : ℕ) (μ : Fin N → ℕ) (j : Fin N) (hj : μ j = 0) :
    weightSpace k N (auxiliaryRepresentationFamilyTwo k N e) μ = ⊥ := by
  letI : FiniteDimensional k (homogeneousSubrepresentation k N e).toSubmodule :=
    finiteDimensional_homogeneousSubmodule e
  change weightSpace k N
    (FDRep.of (twistByCharacter (generalLinearGroupToUnits k N)
      (homogeneousSubrepresentation k N e).toRepresentation)) μ = ⊥
  rw [eq_bot_iff]
  intro v hv
  rw [Submodule.mem_bot]
  rw [mem_auxiliarySubmodule_iff_action_eq_smul] at hv
  apply Subtype.ext
  change (v : MvPolynomial (Fin N × Fin N) k) = 0
  ext s
  rw [MvPolynomial.coeff_zero]
  by_contra hcoeff
  obtain ⟨t, ht⟩ := exists_unit_pow_ne_one k ((∑ l, s (l, j)) + 1) (by omega)
  have hkey :
      (t : k) • (homogeneousSubrepresentation k N e).toRepresentation
        (diagonalUnit k N j t) v = v := by
    have := hv j t
    rwa [FDRep.of_ρ', twistByCharacter_apply,
      auxiliaryUnitsMap_apply_auxiliaryElement, hj, pow_zero, one_smul] at this
  have hpoly := congrArg
    (fun w : (homogeneousSubrepresentation k N e).toSubmodule =>
      (w : MvPolynomial (Fin N × Fin N) k)) hkey
  change (t : k) • generalLinearGroupMvPolynomialRightMul k N
    (diagonalUnit k N j t) (v : MvPolynomial (Fin N × Fin N) k) =
      (v : MvPolynomial (Fin N × Fin N) k) at hpoly
  have hc := congrArg (MvPolynomial.coeff s) hpoly
  rw [MvPolynomial.coeff_smul, coeff_auxiliaryAction, smul_eq_mul,
    ← mul_assoc, ← pow_succ'] at hc
  exact ht (mul_right_cancel₀ hcoeff (by rw [hc, one_mul]))

/-- All-ones exponent vector. -/
private noncomputable def allOnes (N : ℕ) : Fin N →₀ ℕ :=
  ∑ i : Fin N, Finsupp.single i 1

private theorem allOnes_apply (N : ℕ) (i : Fin N) : allOnes N i = 1 := by
  classical
  simp only [allOnes, Finsupp.finsetSum_apply, Finsupp.single_apply,
    Finset.sum_ite_eq', Finset.mem_univ, if_true]

private theorem prod_X_eq_monomial_allOnes (N : ℕ) :
    (∏ i : Fin N, (MvPolynomial.X i : MvPolynomial (Fin N) ℚ))
      = MvPolynomial.monomial (allOnes N) 1 := by
  classical
  have hsupp : (allOnes N).support = Finset.univ := by
    ext i; simp only [Finsupp.mem_support_iff, allOnes_apply, Finset.mem_univ, ne_eq,
      one_ne_zero, not_false_eq_true]
  rw [← MvPolynomial.prod_X_pow_eq_monomial, hsupp]
  exact Finset.prod_congr rfl fun i _ => by rw [allOnes_apply, pow_one]

set_option maxHeartbeats 800000 in
-- The coefficientwise argument performs several expensive representation-theoretic rewrites.
omit [CharZero k] in
/-- The auxiliary polynomial for the second family is the product of all variables times the
auxiliary polynomial for the displayed source representation. -/
theorem auxiliaryPolynomial_familyTwo_eq_variables_mul_source (e : ℕ) :
    weightCharacter k N (auxiliaryRepresentationFamilyTwo k N e)
      = (∏ i : Fin N, (MvPolynomial.X i : MvPolynomial (Fin N) ℚ))
          * weightCharacter k N (auxiliaryIndexedGeneralLinearFDRep k N e) := by
  classical
  rw [prod_X_eq_monomial_allOnes]
  ext μ
  rw [coeff_weightCharacter, MvPolynomial.coeff_monomial_mul']
  by_cases hμ : allOnes N ≤ μ
  · have hμ1 : ∀ i, 1 ≤ μ i := fun i => by
      have := (Finsupp.le_def.mp hμ) i; rwa [allOnes_apply] at this
    have harg : (fun i => μ i - 1) = (fun i => (μ - allOnes N) i) := by
      funext i; rw [Finsupp.tsub_apply, allOnes_apply]
    rw [if_pos hμ, one_mul, coeff_weightCharacter]
    refine Nat.cast_inj.mpr ?_
    rw [auxiliarySubmodule_familyTwo_eq_source_shift e (fun i => μ i) hμ1]
    exact congrArg
      (fun w => Module.finrank k
        (weightSpace k N (auxiliaryIndexedGeneralLinearFDRep k N e) w)) harg
  · rw [if_neg hμ]
    have hj : ∃ j, μ j = 0 := by
      by_contra h; push Not at h
      exact hμ (Finsupp.le_def.mpr fun i => by rw [allOnes_apply]; have := h i; omega)
    obtain ⟨j, hj0⟩ := hj
    rw [auxiliarySubmodule_familyTwo_eq_bot_of_coord_eq_zero e (fun i => μ i) j hj0, finrank_bot,
      Nat.cast_zero]

set_option maxHeartbeats 3200000 in
-- The exact-sequence and filtered-sum calculation requires additional elaboration time.
/-- When the degree is at least the displayed natural number, the polynomial of the first
auxiliary family is a filtered finite sum of the displayed auxiliary polynomials. -/
theorem auxiliaryPolynomial_familyOne_eq_filtered_sum (d : ℕ) (hd : N ≤ d) :
    weightCharacter k N (auxiliaryRepresentationFamilyOne k N d)
      = ∑ ν ∈ Finset.univ.filter
            (fun ν : FinPartition N d => (0 : ℕ) ∈ Set.range ν.parts),
          (MvPolynomial.eval (fun _ => (1 : ℚ)) (partitionPolynomial N ν.parts)) •
            partitionPolynomial N ν.parts := by
  classical
  have hmem_ι : ∀ x ∈ MvPolynomial.homogeneousSubmodule (Fin N × Fin N) k (d - N),
      mul_auxiliary_polynomial_linearMap k N x ∈
        MvPolynomial.homogeneousSubmodule (Fin N × Fin N) k d := by
    intro x hx
    have h := degreeShiftMap_homogeneousSubmodule_le (k := k) (N := N) (d - N)
      (Submodule.mem_map_of_mem hx)
    rwa [show N + (d - N) = d from by omega] at h
  let ι : auxiliaryRepresentationFamilyTwo k N (d - N) →ₗ[k]
      auxiliaryIndexedGeneralLinearFDRep k N d :=
    (mul_auxiliary_polynomial_linearMap k N).restrict hmem_ι
  have hmem_π : ∀ x ∈ MvPolynomial.homogeneousSubmodule (Fin N × Fin N) k d,
      Submodule.mkQ (matrixIndexedPolynomialSubmodule k N) x
        ∈ (MvPolynomial.homogeneousSubmodule (Fin N × Fin N) k d).map
            (Submodule.mkQ (matrixIndexedPolynomialSubmodule k N)) :=
    fun x hx => Submodule.mem_map_of_mem hx
  let π : auxiliaryIndexedGeneralLinearFDRep k N d →ₗ[k]
      auxiliaryRepresentationFamilyOne k N d :=
    (Submodule.mkQ (matrixIndexedPolynomialSubmodule k N)).restrict hmem_π
  let eU : auxiliaryRepresentationFamilyTwo k N (d - N) →ₗ[k] MvPolynomial (Fin N × Fin N) k :=
    (MvPolynomial.homogeneousSubmodule (Fin N × Fin N) k (d - N)).subtype
  let eV : auxiliaryIndexedGeneralLinearFDRep k N d →ₗ[k]
      MvPolynomial (Fin N × Fin N) k := auxiliaryPolynomialEmbedding d
  let eW : auxiliaryRepresentationFamilyOne k N d →ₗ[k]
      (MvPolynomial (Fin N × Fin N) k ⧸ matrixIndexedPolynomialSubmodule k N) :=
    (auxiliarySubrepresentationFamily k N d).toSubmodule.subtype
  have eU_inj : Function.Injective eU := Subtype.coe_injective
  have eV_inj : Function.Injective eV := Subtype.coe_injective
  have eW_inj : Function.Injective eW := Subtype.coe_injective
  have eU_rho : ∀ (g : Matrix.GeneralLinearGroup (Fin N) k)
      (u : auxiliaryRepresentationFamilyTwo k N (d - N)),
      eU ((auxiliaryRepresentationFamilyTwo k N (d - N)).ρ g u)
        = twistByCharacter (generalLinearGroupToUnits k N)
          (generalLinearGroupMvPolynomialRightMul k N) g (eU u) := fun _ _ => rfl
  have eV_rho : ∀ (g : Matrix.GeneralLinearGroup (Fin N) k)
      (v : auxiliaryIndexedGeneralLinearFDRep k N d),
      eV ((auxiliaryIndexedGeneralLinearFDRep k N d).ρ g v) =
        generalLinearGroupMvPolynomialRightMul k N g (eV v) := fun _ _ => rfl
  have eW_rho : ∀ (g : Matrix.GeneralLinearGroup (Fin N) k)
      (w : auxiliaryRepresentationFamilyOne k N d),
      eW ((auxiliaryRepresentationFamilyOne k N d).ρ g w) =
        matrixPolynomialQuotientRepresentation k N g (eW w) := fun _ _ => rfl
  have eV_ι : ∀ u, eV (ι u) = mul_auxiliary_polynomial_linearMap k N (eU u) := fun _ => rfl
  have eW_π : ∀ v,
      eW (π v) = Submodule.mkQ (matrixIndexedPolynomialSubmodule k N) (eV v) :=
    fun _ => rfl
  have hι : ∀ (g : Matrix.GeneralLinearGroup (Fin N) k)
      (u : auxiliaryRepresentationFamilyTwo k N (d - N)),
      ι ((auxiliaryRepresentationFamilyTwo k N (d - N)).ρ g u) =
        (auxiliaryIndexedGeneralLinearFDRep k N d).ρ g (ι u) := by
    intro g u
    apply eV_inj
    rw [eV_ι, eV_rho, eV_ι, eU_rho, mul_auxiliary_polynomial_linearMap_equivariant]
  have hπ : ∀ (g : Matrix.GeneralLinearGroup (Fin N) k)
      (v : auxiliaryIndexedGeneralLinearFDRep k N d),
      π ((auxiliaryIndexedGeneralLinearFDRep k N d).ρ g v) =
        (auxiliaryRepresentationFamilyOne k N d).ρ g (π v) := by
    intro g v
    apply eW_inj
    rw [eW_π, eW_rho, eW_π, eV_rho]
    simp only [Submodule.mkQ_apply, matrixPolynomialQuotientRepresentation_apply_mk]
  have hι_inj : Function.Injective ι := by
    intro a b hab
    apply eU_inj
    apply mul_auxiliary_polynomial_linearMap_injective
    rw [← eV_ι, ← eV_ι, hab]
  have hπ_surj : Function.Surjective π := by
    rintro ⟨_, f, hf, rfl⟩
    exact ⟨⟨f, hf⟩, rfl⟩
  have hexact : LinearMap.range ι = LinearMap.ker π := by
    apply Submodule.ext
    intro x
    rw [LinearMap.mem_range, LinearMap.mem_ker]
    constructor
    · rintro ⟨u, rfl⟩
      apply eW_inj
      rw [eW_π, eV_ι, map_zero, Submodule.mkQ_apply,
        Submodule.Quotient.mk_eq_zero, ← range_mul_auxiliary_polynomial_linearMap]
      exact ⟨eU u, rfl⟩
    · intro hx
      have hxdet : eV x ∈ matrixIndexedPolynomialSubmodule k N := by
        have hxv : eW (π x) = 0 := by rw [hx, map_zero]
        rw [eW_π, Submodule.mkQ_apply] at hxv
        exact (Submodule.Quotient.mk_eq_zero _).1 hxv
      have hxhom : eV x ∈ MvPolynomial.homogeneousSubmodule (Fin N × Fin N) k d := x.2
      have hmem : eV x
          ∈ (MvPolynomial.homogeneousSubmodule (Fin N × Fin N) k (d - N)).map
            (mul_auxiliary_polynomial_linearMap k N) := by
        rw [← inf_homogeneousSubmodule_eq_map_homogeneousSubmodule d hd]; exact ⟨hxdet, hxhom⟩
      obtain ⟨Q, hQ, hQx⟩ := hmem
      refine ⟨⟨Q, hQ⟩, eV_inj ?_⟩
      rw [eV_ι]; exact hQx
  have hVtop : ⨆ μ : Fin N →₀ ℕ,
      weightSpace k N (auxiliaryIndexedGeneralLinearFDRep k N d) (fun i => μ i) = ⊤ :=
    iSup_auxiliarySubmodule_eq_top d
  have hUtop : ⨆ μ : Fin N →₀ ℕ,
      weightSpace k N (auxiliaryRepresentationFamilyTwo k N (d - N)) (fun i => μ i) = ⊤ := by
    letI : FiniteDimensional k
        (homogeneousSubrepresentation k N (d - N)).toSubmodule :=
      finiteDimensional_homogeneousSubmodule (d - N)
    change (⨆ μ : Fin N →₀ ℕ,
      weightSpace k N
        (FDRep.of (twistByCharacter (generalLinearGroupToUnits k N)
          (homogeneousSubrepresentation k N (d - N)).toRepresentation))
        (fun i => μ i)) = ⊤
    have hSource := iSup_auxiliarySubmodule_eq_top (k := k) (N := N) (d - N)
    change (⨆ μ : Fin N →₀ ℕ,
      weightSpace k N
        (FDRep.of (homogeneousSubrepresentation k N (d - N)).toRepresentation)
        (fun i => μ i)) = ⊤ at hSource
    rw [eq_top_iff, ← hSource]
    refine iSup_le fun ν => le_iSup_of_le (ν + allOnes N) (le_of_eq ?_)
    have hμ : ∀ i, 1 ≤ (ν + allOnes N) i := fun i => by
      rw [Finsupp.add_apply, allOnes_apply]; omega
    have hShift := auxiliarySubmodule_familyTwo_eq_source_shift
      (k := k) (N := N) (d - N) (fun i => (ν + allOnes N) i) hμ
    change weightSpace k N
        (FDRep.of (twistByCharacter (generalLinearGroupToUnits k N)
          (homogeneousSubrepresentation k N (d - N)).toRepresentation))
          (fun i => (ν + allOnes N) i) =
      weightSpace k N
        (FDRep.of (homogeneousSubrepresentation k N (d - N)).toRepresentation)
          (fun i => (ν + allOnes N) i - 1) at hShift
    rw [hShift]
    congr 1
    funext i
    simp only [Finsupp.add_apply, allOnes_apply]
    omega
  have htwist : weightCharacter k N (auxiliaryRepresentationFamilyTwo k N (d - N))
      = ∑ ν ∈ Finset.univ.filter
            (fun ν : FinPartition N d => (0 : ℕ) ∉ Set.range ν.parts),
          (MvPolynomial.eval (fun _ => (1 : ℚ)) (partitionPolynomial N ν.parts)) •
            partitionPolynomial N ν.parts := by
    rw [auxiliaryPolynomial_familyTwo_eq_variables_mul_source (d - N),
      auxiliaryIndexedGeneralLinearFDRep_auxiliaryPolynomial_eq_weightedSum k N (d - N),
      mul_comm, weightedPolynomialSum_mul_prod_variables hd]
  have hSES := auxiliaryPolynomial_eq_add_of_exact N (auxiliaryRepresentationFamilyTwo k N (d - N))
    (auxiliaryIndexedGeneralLinearFDRep k N d) (auxiliaryRepresentationFamilyOne k N d)
    ι π hι hπ hι_inj hπ_surj hexact
    hUtop hVtop
  rw [auxiliaryIndexedGeneralLinearFDRep_auxiliaryPolynomial_eq_weightedSum k N d, htwist] at hSES
  have hW : weightCharacter k N (auxiliaryRepresentationFamilyOne k N d)
      = (∑ ν : FinPartition N d,
            (MvPolynomial.eval (fun _ => (1 : ℚ)) (partitionPolynomial N ν.parts)) •
              partitionPolynomial N ν.parts)
        - ∑ ν ∈ Finset.univ.filter
              (fun ν : FinPartition N d => (0 : ℕ) ∉ Set.range ν.parts),
            (MvPolynomial.eval (fun _ => (1 : ℚ)) (partitionPolynomial N ν.parts)) •
              partitionPolynomial N ν.parts := by
    rw [hSES]; ring
  rw [hW, sub_eq_iff_eq_add]
  exact (Finset.sum_filter_add_sum_filter_not Finset.univ _ _).symm

/-- Evaluating the auxiliary polynomial of an antitone sequence at one produces a natural-number
value in the field. -/
theorem auxiliaryPolynomial_eval_one_eq_natCast (k : Type*) [Field k] [IsAlgClosed k] [CharZero k]
    {N : ℕ} (l : Fin N → ℕ) (hl : Antitone l) :
    ∃ m : ℕ, MvPolynomial.eval (fun _ => (1 : ℚ)) (partitionPolynomial N l) = (m : ℚ) := by
  classical
  refine ⟨∑ d ∈ (partitionPolynomial N l).support,
      Module.finrank k (weightSpace k N (schurRepresentation k N l) (fun i => d i)), ?_⟩
  rw [MvPolynomial.eval_eq', Nat.cast_sum]
  refine Finset.sum_congr rfl (fun d _ => ?_)
  rw [finrank_weightSpace_schurRepresentation k N l hl d]
  simp

/-- An auxiliary map from the displayed indexing type to antitone functions. -/
def auxiliaryAntitoneMap {N d : ℕ} (ν : FinPartition N d) :
    {l : Fin N → ℕ // Antitone l} :=
  ⟨ν.parts, ν.parts_antitone⟩

/-- The auxiliary map to antitone functions is injective. -/
theorem auxiliaryAntitoneMap_injective {N d : ℕ} :
    Function.Injective (auxiliaryAntitoneMap (N := N) (d := d)) := by
  intro ν₁ ν₂ h
  obtain ⟨p₁, d₁, s₁⟩ := ν₁
  obtain ⟨p₂, d₂, s₂⟩ := ν₂
  have hp : p₁ = p₂ := congrArg Subtype.val h
  subst hp; rfl

omit [IsAlgClosed k] [CharZero k] in
/-- When the degree is less than the displayed natural number, the auxiliary submodule has trivial
intersection with the corresponding homogeneous component. -/
theorem auxiliarySubmodule_inf_homogeneousSubmodule_eq_bot {N : ℕ} (d : ℕ) (hd : d < N) :
    matrixIndexedPolynomialSubmodule k N ⊓
      MvPolynomial.homogeneousSubmodule (Fin N × Fin N) k d = ⊥ := by
  rw [eq_bot_iff]
  rintro x ⟨hxdet, hxhom⟩
  rw [Submodule.mem_bot]
  rw [← range_mul_auxiliary_polynomial_linearMap] at hxdet
  obtain ⟨g, hg⟩ := LinearMap.mem_range.1 hxdet
  have hx0 : MvPolynomial.homogeneousComponent d x = 0 := by
    rw [← hg, mul_auxiliary_polynomial_linearMap_apply]
    conv_lhs => rw [← MvPolynomial.sum_homogeneousComponent g, Finset.mul_sum, map_sum]
    refine Finset.sum_eq_zero (fun j _ => ?_)
    rw [MvPolynomial.homogeneousComponent_of_mem
        ((MvPolynomial.mem_homogeneousSubmodule (N + j) _).2
          (polynomial_isHomogeneous_of_degree_matrixSize.mul
            (MvPolynomial.homogeneousComponent_isHomogeneous j g))),
      if_neg (by omega)]
  have hxeq : MvPolynomial.homogeneousComponent d x = x := by
    rw [MvPolynomial.homogeneousComponent_of_mem hxhom, if_pos rfl]
  rw [← hxeq]; exact hx0

omit [CharZero k] in
/-- When the degree is less than the displayed natural number, the first auxiliary family and the
displayed source representation have the same auxiliary polynomial. -/
theorem auxiliaryPolynomial_familyOne_eq_source_of_degree_lt {N : ℕ} (d : ℕ) (hd : d < N) :
    weightCharacter k N (auxiliaryRepresentationFamilyOne k N d)
      = weightCharacter k N (auxiliaryIndexedGeneralLinearFDRep k N d) := by
  have hinj : Function.Injective (auxiliaryLinearMapToFamilyOne k N d) := by
    rw [injective_iff_map_eq_zero]
    intro v hv
    have hco :
        Submodule.mkQ (matrixIndexedPolynomialSubmodule k N)
          (auxiliaryPolynomialEmbedding d v) = 0 := by
      have h := Subtype.ext_iff.mp hv
      exact h
    rw [Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero] at hco
    have hv0 : auxiliaryPolynomialEmbedding d v = 0 := by
      have hmem : auxiliaryPolynomialEmbedding d v ∈
          (⊥ : Submodule k (MvPolynomial (Fin N × Fin N) k)) := by
        rw [← auxiliarySubmodule_inf_homogeneousSubmodule_eq_bot d hd]
        exact ⟨hco, auxiliaryPolynomialEmbedding_mem_homogeneousSubmodule d v⟩
      simpa using hmem
    exact auxiliaryPolynomialEmbedding_injective d (by simpa using hv0)
  haveI : Module.Finite k (homogeneousSubrepresentation k N d).toSubmodule :=
    inferInstanceAs (Module.Finite k (auxiliaryIndexedGeneralLinearFDRep k N d))
  haveI : Module.Finite k (auxiliarySubrepresentationFamily k N d).toSubmodule :=
    inferInstanceAs (Module.Finite k (auxiliaryRepresentationFamilyOne k N d))
  exact (auxiliaryPolynomial_eq_of_linearEquiv k N
    (homogeneousSubrepresentation k N d).toRepresentation
    (auxiliarySubrepresentationFamily k N d).toRepresentation
    (LinearEquiv.ofBijective (auxiliaryLinearMapToFamilyOne k N d)
      ⟨hinj, auxiliaryLinearMapToFamilyOne_surjective d⟩)
    (fun g v => auxiliaryLinearMapToFamilyOne_equivariant d g v)).symm

/-- The polynomial of the first auxiliary family admits a finite expansion by auxiliary
polynomials indexed by antitone sequences that attain zero. -/
theorem exists_auxiliaryPolynomial_familyOne_expansion (N d : ℕ) :
    ∃ (S : Finset {l : Fin N → ℕ // Antitone l})
      (c : {l : Fin N → ℕ // Antitone l} → ℕ),
      (∀ ν ∈ S, (0 : ℕ) ∈ Set.range ν.val) ∧
      weightCharacter k N (auxiliaryRepresentationFamilyOne k N d)
        = ∑ ν ∈ S, (c ν : ℚ) • partitionPolynomial N ν.val := by
  classical
  have hc : ∀ ν : {l : Fin N → ℕ // Antitone l},
      ((auxiliaryPolynomial_eval_one_eq_natCast k ν.val ν.property).choose : ℚ)
        = MvPolynomial.eval (fun _ => (1 : ℚ)) (partitionPolynomial N ν.val) :=
    fun ν => ((auxiliaryPolynomial_eval_one_eq_natCast k ν.val ν.property).choose_spec).symm
  rcases Nat.lt_or_ge d N with hd | hd
  · -- `d < N`: `(A/det)_d ≅ A_d`, the full degree-`d` Cauchy character; every bounded
    refine ⟨(Finset.univ : Finset (FinPartition N d)).image auxiliaryAntitoneMap,
      fun ν => (auxiliaryPolynomial_eval_one_eq_natCast k ν.val ν.property).choose, ?_, ?_⟩
    · intro ν' hν'
      rw [Finset.mem_image] at hν'
      obtain ⟨ν, _, rfl⟩ := hν'
      change (0 : ℕ) ∈ Set.range ν.parts
      by_contra h
      have hpos : ∀ i, 1 ≤ ν.parts i := fun i => by
        rcases Nat.eq_zero_or_pos (ν.parts i) with h0 | h1
        · exact absurd ⟨i, h0⟩ h
        · exact h1
      have hge : N ≤ ∑ i, ν.parts i := by
        calc N = ∑ _i : Fin N, 1 := by simp
          _ ≤ ∑ i, ν.parts i := Finset.sum_le_sum (fun i _ => hpos i)
      rw [ν.sum_parts] at hge; omega
    · rw [auxiliaryPolynomial_familyOne_eq_source_of_degree_lt d hd,
        auxiliaryIndexedGeneralLinearFDRep_auxiliaryPolynomial_eq_weightedSum k N d,
        Finset.sum_image (fun x _ y _ h => auxiliaryAntitoneMap_injective h)]
      refine Finset.sum_congr rfl (fun ν _ => ?_)
      have hval : (auxiliaryAntitoneMap ν).val = ν.parts := rfl
      rw [hc (auxiliaryAntitoneMap ν), hval]
  · -- `d ≥ N`: translate the formula along `auxiliaryAntitoneMap`.
    refine ⟨(Finset.univ.filter
        (fun ν : FinPartition N d => (0 : ℕ) ∈ Set.range ν.parts)).image auxiliaryAntitoneMap,
      fun ν => (auxiliaryPolynomial_eval_one_eq_natCast k ν.val ν.property).choose, ?_, ?_⟩
    · intro ν' hν'
      rw [Finset.mem_image] at hν'
      obtain ⟨ν, hν, rfl⟩ := hν'
      exact (Finset.mem_filter.mp hν).2
    · rw [auxiliaryPolynomial_familyOne_eq_filtered_sum d hd,
        Finset.sum_image (fun x _ y _ h => auxiliaryAntitoneMap_injective h)]
      refine Finset.sum_congr rfl (fun ν _ => ?_)
      have hval : (auxiliaryAntitoneMap ν).val = ν.parts := rfl
      rw [hc (auxiliaryAntitoneMap ν), hval]

end RepresentationTheory.GeneralLinear.AuxiliaryRepresentationFamilies
