/-
Copyright (c) 2026 mathlib-initiative. All rights reserved.
Released under Apache 2.0 license as described in the file LICENCE.
Authors: mathlib-initiative
-/

import RepresentationTheory.Representation.ModuleEquivAndTraceSeparation
import RepresentationTheory.GeneralLinearRepresentation.SubrepresentationQuotient
import RepresentationTheory.GeneralLinearRepresentation.WeightSpaceEigenspaces
import RepresentationTheory.Submodules
import RepresentationTheory.GeneralLinearGroup.WeightCharacter

open CategoryTheory MvPolynomial
open scoped MonoidAlgebra

noncomputable section

set_option linter.dupNamespace false
set_option linter.style.longLine false

namespace RepresentationTheory.GeneralLinearRepresentation.WeightPolynomialDecomposition

namespace GeneralLinearRepresentation

open RepresentationTheory.AuxiliaryCharacter
open RepresentationTheory.GeneralLinearGroup.WeightCharacter
open RepresentationTheory.GeneralLinearRepresentation.SubrepresentationQuotient.GeneralLinearRepresentation
open RepresentationTheory.GeneralLinearRepresentation.WeightSpaceEigenspaces.GeneralLinearRepresentation
open RepresentationTheory.GeneralLinearRepresentation.WeightSpaceMorphisms.GeneralLinearRepresentation
open RepresentationTheory.Representation.ModuleEquivAndTraceSeparation
open RepresentationTheory.Submodules
open RepresentationTheory.UnitTupleActions
open RepresentationTheory.Auxiliary.GeneralLinearGroupPolynomialEvaluation

variable (k : Type) [Field k] [IsAlgClosed k] [CharZero k]

/-- The representation carried by a subrepresentation has weight spaces spanning the whole space whenever the ambient representation does. -/
theorem iSup_weightSpaces_subrepresentation_eq_top (N : ℕ)
    (M : FDRep k (Matrix.GeneralLinearGroup (Fin N) k)) (σ : Subrepresentation M.ρ)
    (hM : ⨆ μ : Fin N →₀ ℕ, weightSpace k N M (fun i => μ i) = ⊤) :
    ⨆ μ : Fin N →₀ ℕ, weightSpace k N (ofSubrepresentation M σ) (fun i => μ i) = ⊤ := by
  classical
  set ι : ofSubrepresentation M σ →ₗ[k] M := σ.toSubmodule.subtype with hιdef
  have hι : ∀ g v, ι ((ofSubrepresentation M σ).ρ g v) = M.ρ g (ι v) := subrepresentationSubtype_equivariant M σ
  have hι_inj : Function.Injective ι := subrepresentationSubtype_injective M σ
  have hrange : LinearMap.range ι = σ.toSubmodule := Submodule.range_subtype _
  have hinv : ∀ (g : Matrix.GeneralLinearGroup (Fin N) k), ∀ v ∈ σ.toSubmodule,
      M.ρ g v ∈ σ.toSubmodule := fun g v hv => σ.apply_mem_toSubmodule g hv
  have htor := iSup_weightSpace_inf_invariantSubmodule_eq (k := k) N M σ.toSubmodule hinv hM
  -- Rewrite the torus-invariant decomposition in terms of `ofSubrepresentation` weight spaces.
  have hkey : (fun μ : Fin N →₀ ℕ => weightSpace k N M (fun i => μ i) ⊓ σ.toSubmodule)
      = (fun μ : Fin N →₀ ℕ => (weightSpace k N (ofSubrepresentation M σ) (fun i => μ i)).map ι) := by
    funext μ
    rw [← hrange]
    exact weightSpace_inf_range_eq_map_of_injective_equivariant N (ofSubrepresentation M σ) M ι hι hι_inj (fun i => μ i)
  rw [hkey, ← Submodule.map_iSup] at htor
  -- `(⨆ ...).map ι = σ.toSubmodule = range ι = (⊤).map ι`, and `ι` is injective.
  have hmaptop : (⨆ μ : Fin N →₀ ℕ, weightSpace k N (ofSubrepresentation M σ) (fun i => μ i)).map ι
      = (⊤ : Submodule k (ofSubrepresentation M σ)).map ι := by
    rw [Submodule.map_top, hrange]; exact htor
  exact Submodule.map_injective_of_injective hι_inj hmaptop

omit [IsAlgClosed k] [CharZero k] in
/-- The stated auxiliary condition on a general linear group action passes to the representation carried by a subrepresentation. -/
theorem auxiliaryCondition_subrepresentation (N : ℕ)
    (M : FDRep k (Matrix.GeneralLinearGroup (Fin N) k)) (σ : Subrepresentation M.ρ)
    (hM : GeneralLinearGroup.Auxiliary.HasAuxiliaryMapProperty N M.ρ) :
    GeneralLinearGroup.Auxiliary.HasAuxiliaryMapProperty N (ofSubrepresentation M σ).ρ := by
  have hrestrict := hM.auxiliary_restrict σ.toSubmodule
    (fun g v hv => σ.apply_mem_toSubmodule g hv)
  -- `simpa only [ofSubrepresentation, FDRep.of_ρ']` over-unfolds the carrier/action;
  -- `(ofSubrepresentation M σ).ρ` is defeq to the restricted action `σ.toRepresentation`,
  -- so `exact hrestrict` closes the goal directly.
  exact hrestrict

/-- A representation satisfying the stated auxiliary and weight-space spanning conditions has a finite decomposition of its polynomial invariant into those of simple representations with the same conditions. -/
theorem exists_simple_weightPolynomial_decomposition (N : ℕ)
    (M : FDRep k (Matrix.GeneralLinearGroup (Fin N) k))
    (halg : GeneralLinearGroup.Auxiliary.HasAuxiliaryMapProperty N M.ρ)
    (hM : ⨆ μ : Fin N →₀ ℕ, weightSpace k N M (fun i => μ i) = ⊤) :
    ∃ (p : ℕ) (W : Fin p → FDRep k (Matrix.GeneralLinearGroup (Fin N) k)),
      (∀ j, IsSimpleModule (MonoidAlgebra k (Matrix.GeneralLinearGroup (Fin N) k))
          (Representation.asModule (W j).ρ)) ∧
      (∀ j, GeneralLinearGroup.Auxiliary.HasAuxiliaryMapProperty N (W j).ρ) ∧
      (∀ j, ⨆ μ : Fin N →₀ ℕ, weightSpace k N (W j) (fun i => μ i) = ⊤) ∧
      weightCharacter k N M = ∑ j, weightCharacter k N (W j) := by
  classical
  -- Strong induction on `finrank k M`.
  suffices H : ∀ n (M : FDRep k (Matrix.GeneralLinearGroup (Fin N) k)),
      Module.finrank k M = n →
      GeneralLinearGroup.Auxiliary.HasAuxiliaryMapProperty N M.ρ →
      (⨆ μ : Fin N →₀ ℕ, weightSpace k N M (fun i => μ i) = ⊤) →
      ∃ (p : ℕ) (W : Fin p → FDRep k (Matrix.GeneralLinearGroup (Fin N) k)),
        (∀ j, IsSimpleModule (MonoidAlgebra k (Matrix.GeneralLinearGroup (Fin N) k))
            (Representation.asModule (W j).ρ)) ∧
        (∀ j, GeneralLinearGroup.Auxiliary.HasAuxiliaryMapProperty N (W j).ρ) ∧
        (∀ j, ⨆ μ : Fin N →₀ ℕ, weightSpace k N (W j) (fun i => μ i) = ⊤) ∧
        weightCharacter k N M = ∑ j, weightCharacter k N (W j) by
    exact H _ M rfl halg hM
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro M hn halg hM
    rcases Nat.eq_zero_or_pos n with hn0 | hnpos
    · -- Base case: `finrank M = 0`, so every weight space is trivial and `char M = 0`.
      refine ⟨0, Fin.elim0, fun j => j.elim0, fun j => j.elim0, fun j => j.elim0, ?_⟩
      simp only [Finset.univ_eq_empty, Finset.sum_empty]
      apply MvPolynomial.ext
      intro μ
      rw [coeff_weightCharacter, MvPolynomial.coeff_zero]
      have hz : Module.finrank k (weightSpace k N M (fun i => μ i)) = 0 := by
        have hle := Submodule.finrank_le (weightSpace k N M (fun i => μ i))
        omega
      rw [hz]; norm_num
    · -- Inductive step: peel a simple submodule.
      haveI hMnt : Nontrivial M :=
        Module.nontrivial_of_finrank_pos (R := k) (by rw [hn]; exact hnpos)
      haveI : Nontrivial (Representation.asModule M.ρ) := by
        obtain ⟨a, b, hab⟩ := exists_pair_ne M
        exact ⟨(Representation.asModuleEquiv M.ρ).symm a, (Representation.asModuleEquiv M.ρ).symm b,
          fun h => hab ((Representation.asModuleEquiv M.ρ).symm.injective h)⟩
      have htop_ne : (⊤ : Submodule (MonoidAlgebra k (Matrix.GeneralLinearGroup (Fin N) k))
          (Representation.asModule M.ρ)) ≠ ⊥ := by
        intro h
        rw [Submodule.eq_bot_iff] at h
        obtain ⟨a, ha⟩ := exists_ne (0 : Representation.asModule M.ρ)
        exact ha (h a Submodule.mem_top)
      obtain ⟨S, hSsimple, _hSle⟩ := exists_isSimpleModule_submodule_le_of_finite M.ρ ⊤ htop_ne
      set σ : Subrepresentation M.ρ := Subrepresentation.ofSubmodule' S with hσdef
      have hσasSub : σ.asSubmodule = S := rfl
      -- `ofSubrepresentation M σ` is simple, algebraic, weight-spanning.
      have hsubsimple : IsSimpleModule (MonoidAlgebra k (Matrix.GeneralLinearGroup (Fin N) k))
          (Representation.asModule (ofSubrepresentation M σ).ρ) := by
        have h1 : IsSimpleModule (MonoidAlgebra k (Matrix.GeneralLinearGroup (Fin N) k))
            σ.asSubmodule := hσasSub ▸ hSsimple
        have h2 := isSimpleModule_toRepresentation_of_asSubmodule σ h1
        change IsSimpleModule (MonoidAlgebra k (Matrix.GeneralLinearGroup (Fin N) k))
          σ.toRepresentation.asModule
        exact h2
      have hsubalg : GeneralLinearGroup.Auxiliary.HasAuxiliaryMapProperty N (ofSubrepresentation M σ).ρ :=
        auxiliaryCondition_subrepresentation k N M σ halg
      have hsubspan : ⨆ μ : Fin N →₀ ℕ, weightSpace k N (ofSubrepresentation M σ) (fun i => μ i) = ⊤ :=
        iSup_weightSpaces_subrepresentation_eq_top k N M σ hM
      -- `σ.toSubmodule ≠ ⊥`, so the quotient has strictly smaller `finrank`.
      have hSne : S ≠ ⊥ := by
        haveI := hSsimple
        exact Submodule.nontrivial_iff_ne_bot.mp
          (IsSimpleModule.nontrivial (MonoidAlgebra k (Matrix.GeneralLinearGroup (Fin N) k)) S)
      have hStne : σ.toSubmodule ≠ ⊥ := by
        rw [Submodule.ne_bot_iff] at hSne ⊢
        obtain ⟨x, hxS, hx0⟩ := hSne
        have hxσ : x ∈ σ.asSubmodule := hσasSub ▸ hxS
        exact ⟨x, hxσ, hx0⟩
      have hquot_alg : GeneralLinearGroup.Auxiliary.HasAuxiliaryMapProperty N (quotientBySubrepresentation M σ).ρ :=
        auxiliaryCondition_quotient M σ halg
      have hquot_span :
          ⨆ μ : Fin N →₀ ℕ, weightSpace k N (quotientBySubrepresentation M σ) (fun i => μ i) = ⊤ :=
        iSup_weightSpaces_quotient_eq_top M σ hM
      have hquot_finrank : Module.finrank k (quotientBySubrepresentation M σ) < n := by
        have hadd := Submodule.finrank_quotient_add_finrank σ.toSubmodule
        haveI : Nontrivial σ.toSubmodule := Submodule.nontrivial_iff_ne_bot.mpr hStne
        have hpos : 0 < Module.finrank k σ.toSubmodule := Module.finrank_pos
        have hq : Module.finrank k (quotientBySubrepresentation M σ) = Module.finrank k (M ⧸ σ.toSubmodule) :=
          rfl
        rw [hq]; omega
      obtain ⟨p, W, hWsimple, hWalg, hWspan, hWchar⟩ :=
        ih _ hquot_finrank (quotientBySubrepresentation M σ) rfl hquot_alg hquot_span
      -- Assemble: `ofSubrepresentation M σ` followed by the factors of the quotient.
      refine ⟨p + 1, Fin.cons (ofSubrepresentation M σ) W, ?_, ?_, ?_, ?_⟩
      · intro j; refine Fin.cases ?_ ?_ j
        · exact hsubsimple
        · exact hWsimple
      · intro j; refine Fin.cases ?_ ?_ j
        · exact hsubalg
        · exact hWalg
      · intro j; refine Fin.cases ?_ ?_ j
        · exact hsubspan
        · exact hWspan
      · rw [Fin.sum_univ_succ]
        simp only [Fin.cons_zero, Fin.cons_succ]
        rw [← hWchar]
        exact weightPolynomial_eq_subrepresentation_add_quotient M σ hsubspan hM

omit [CharZero k] in
/-- The supremum of all weight spaces of the representation indexed by a natural-valued weight is the whole space. -/
theorem iSup_weightSpaces_canonical_eq_top (N : ℕ) (lam : Fin N → ℕ) :
    ⨆ (μ : Fin N →₀ ℕ), weightSpace k N (schurRepresentation k N lam) (fun i => μ i) = ⊤ := by
  refine iSup_weightSpaces_eq_top_of_surjective_equivariant N
    (FDRep.of (tensorPowerRepresentation k N (∑ i, lam i))) (schurRepresentation k N lam)
    (LinearMap.rangeRestrict (symmetrizerEndomorphism k N lam)) ?_
    (LinearMap.surjective_rangeRestrict _)
    (auxiliaryRepresentation_iSupWeightSpace_eq_top k N (∑ i, lam i))
  intro g v
  apply Subtype.ext
  change symmetrizerEndomorphism k N lam ((FDRep.of (tensorPowerRepresentation k N (∑ i, lam i))).ρ g v)
     = (tensorPowerRepresentation k N (∑ i, lam i) g) (symmetrizerEndomorphism k N lam v)
  rw [FDRep.of_ρ']
  exact (LinearMap.ext_iff.mp (tensorPowerRepresentation_comp_symmetrizerEndomorphism k N lam g) v).symm

omit [CharZero k] in
/-- Isomorphic finite-dimensional representations have equal polynomial invariants. -/
theorem weightPolynomial_eq_of_iso (N : ℕ)
    (X Y : FDRep k (Matrix.GeneralLinearGroup (Fin N) k)) (e : X ≅ Y) :
    weightCharacter k N X = weightCharacter k N Y := by
  have hint : ∀ (g : Matrix.GeneralLinearGroup (Fin N) k) (v : X),
      (FDRep.isoToLinearEquiv e) (X.ρ g v) = Y.ρ g ((FDRep.isoToLinearEquiv e) v) := by
    intro g v
    have h := FDRep.Iso.conj_ρ e g
    have hconj : (FDRep.isoToLinearEquiv e).conj (X.ρ g) ((FDRep.isoToLinearEquiv e) v)
        = (FDRep.isoToLinearEquiv e) (X.ρ g v) := by
      simp only [LinearEquiv.conj_apply, LinearMap.comp_apply, LinearEquiv.coe_coe]
      rw [(FDRep.isoToLinearEquiv e).symm_apply_apply]
    rw [h, hconj]
  have h0 := auxiliaryPolynomial_eq_of_linearEquiv k N X.ρ Y.ρ (FDRep.isoToLinearEquiv e) hint
  rwa [auxiliary_fdRep_value_of_representation_eq, auxiliary_fdRep_value_of_representation_eq] at h0

/-- The polynomial invariants of a finite pairwise nonisomorphic family of simple representations are linearly independent over the rationals. -/
theorem linearIndependent_weightPolynomials_of_pairwise_nonisomorphic (N : ℕ) {ι : Type} [Fintype ι]
    (R : ι → FDRep k (Matrix.GeneralLinearGroup (Fin N) k))
    (hRalg : ∀ i, GeneralLinearGroup.Auxiliary.HasAuxiliaryMapProperty N (R i).ρ)
    (hRsimp : ∀ i, IsSimpleModule (MonoidAlgebra k (Matrix.GeneralLinearGroup (Fin N) k))
        (Representation.asModule (R i).ρ))
    (hRspan : ∀ i, ⨆ μ : Fin N →₀ ℕ, weightSpace k N (R i) (fun j => μ j) = ⊤)
    (hRdist : Pairwise (fun i j => ¬ Nonempty ((R i) ≅ (R j))))
    (a : ι → ℚ)
    (hcomb : ∑ i, a i • weightCharacter k N (R i) = 0) :
    ∀ i, a i = 0 := by
  classical
  refine trace_coefficients_eq_zero_of_diagonal_sum_eq_zero
    (k := k) N R hRalg hRsimp hRdist a (fun t => ?_)
  have hchar0 : ∑ i ∈ Finset.univ, a i • weightCharacter k N (R i) = 0 := by simpa using hcomb
  have h := sum_trace_unitTupleAction_eq_zero_of_auxiliaryPolynomialRelation
    (k := k) (N := N) Finset.univ a R (fun i _ => hRspan i) hchar0 t
  simpa using h

/-- In a vanishing rational combination of polynomial invariants, the coefficients indexed by any fixed invariant sum to zero. -/
theorem sum_coefficients_eq_zero_on_weightPolynomial_fiber (N : ℕ) {ι : Type} [Fintype ι]
    (R : ι → FDRep k (Matrix.GeneralLinearGroup (Fin N) k))
    (hRalg : ∀ i, GeneralLinearGroup.Auxiliary.HasAuxiliaryMapProperty N (R i).ρ)
    (hRsimp : ∀ i, IsSimpleModule (MonoidAlgebra k (Matrix.GeneralLinearGroup (Fin N) k))
        (Representation.asModule (R i).ρ))
    (hRspan : ∀ i, ⨆ μ : Fin N →₀ ℕ, weightSpace k N (R i) (fun j => μ j) = ⊤)
    (a : ι → ℚ)
    (hcomb : ∑ i, a i • weightCharacter k N (R i) = 0)
    (w : MvPolynomial (Fin N) ℚ) :
    ∑ i ∈ Finset.univ.filter (fun i => weightCharacter k N (R i) = w), a i = 0 := by
  classical
  let χ : ι → MvPolynomial (Fin N) ℚ := fun i => weightCharacter k N (R i)
  let reps : Finset (MvPolynomial (Fin N) ℚ) := Finset.image χ Finset.univ
  by_cases hw : w ∈ reps
  · have hpickex : ∀ w : {w // w ∈ reps}, ∃ i, χ i = w.1 := by
      intro w
      have hw := w.2
      simp only [reps, Finset.mem_image, Finset.mem_univ, true_and] at hw
      obtain ⟨i, hi⟩ := hw
      exact ⟨i, hi⟩
    choose pick hpick using hpickex
    let Rep : {w // w ∈ reps} → FDRep k (Matrix.GeneralLinearGroup (Fin N) k) :=
      fun w => R (pick w)
    let b : {w // w ∈ reps} → ℚ :=
      fun w => ∑ i ∈ Finset.univ.filter (fun i => χ i = w.1), a i
    have hRepchar : ∀ w, weightCharacter k N (Rep w) = w.1 := fun w => hpick w
    have hzero : ∑ w ∈ reps, (∑ i ∈ Finset.univ.filter (fun i => χ i = w), a i) • w = 0 := by
      have h1 : ∑ w ∈ reps, (∑ i ∈ Finset.univ.filter (fun i => χ i = w), a i) • w
          = ∑ w ∈ reps, ∑ i ∈ Finset.univ.filter (fun i => χ i = w), a i • χ i := by
        refine Finset.sum_congr rfl (fun w _ => ?_)
        rw [Finset.sum_smul]
        refine Finset.sum_congr rfl (fun i hi => ?_)
        rw [Finset.mem_filter] at hi
        rw [hi.2]
      rw [h1, Finset.sum_fiberwise_of_maps_to
        (fun i _ => Finset.mem_image_of_mem χ (Finset.mem_univ i)) (fun i => a i • χ i)]
      exact hcomb
    have hRepcomb : ∑ w : {w // w ∈ reps}, b w • weightCharacter k N (Rep w) = 0 := by
      have hstep : ∀ w : {w // w ∈ reps}, b w • weightCharacter k N (Rep w)
          = (fun w0 => (∑ i ∈ Finset.univ.filter (fun i => χ i = w0), a i) • w0) w.1 := by
        intro w; rw [hRepchar w]
      rw [Finset.sum_congr rfl (fun w _ => hstep w),
        Finset.sum_coe_sort reps
          (fun w0 => (∑ i ∈ Finset.univ.filter (fun i => χ i = w0), a i) • w0)]
      exact hzero
    have hRepdist :
        Pairwise (fun w w' : {w // w ∈ reps} => ¬ Nonempty ((Rep w) ≅ (Rep w'))) := by
      intro w w' hww'
      rintro ⟨e⟩
      apply hww'
      apply Subtype.ext
      have h3 := weightPolynomial_eq_of_iso k N (Rep w) (Rep w') e
      rw [hRepchar w, hRepchar w'] at h3
      exact h3
    have hb0 := linearIndependent_weightPolynomials_of_pairwise_nonisomorphic k N Rep
      (fun w => hRalg (pick w)) (fun w => hRsimp (pick w)) (fun w => hRspan (pick w))
      hRepdist b hRepcomb
    exact hb0 ⟨w, hw⟩
  · have hempty : Finset.univ.filter (fun i => weightCharacter k N (R i) = w) = ∅ := by
      rw [Finset.filter_eq_empty_iff]
      intro i _ hi
      have hmem : weightCharacter k N (R i) ∈ reps :=
        Finset.mem_image_of_mem χ (Finset.mem_univ i)
      rw [hi] at hmem
      exact hw hmem
    rw [hempty, Finset.sum_empty]

/-- An injectively embedded simple representation has polynomial invariant equal to a term occurring with positive coefficient in any specified finite expansion. -/
theorem exists_positive_polynomial_term_of_simple_subrepresentation (N : ℕ)
    (M : FDRep k (Matrix.GeneralLinearGroup (Fin N) k))
    (halg : GeneralLinearGroup.Auxiliary.HasAuxiliaryMapProperty N M.ρ)
    (h_span : ⨆ (μ : Fin N →₀ ℕ), weightSpace k N M (fun i => μ i) = ⊤)
    (S : Finset {l : Fin N → ℕ // Antitone l})
    (c : {l : Fin N → ℕ // Antitone l} → ℕ)
    (hchar : weightCharacter k N M = ∑ ν ∈ S, (c ν : ℚ) • RepresentationTheory.SymmetricPolynomials.Alternant.partitionPolynomial N ν.val)
    (L : FDRep k (Matrix.GeneralLinearGroup (Fin N) k))
    (hLsimp : IsSimpleModule (MonoidAlgebra k (Matrix.GeneralLinearGroup (Fin N) k))
      (Representation.asModule L.ρ))
    (φ : L →ₗ[k] M)
    (hφ_inj : Function.Injective φ)
    (hφ_equiv : ∀ (g : Matrix.GeneralLinearGroup (Fin N) k) (v : L),
      φ (L.ρ g v) = M.ρ g (φ v)) :
    ∃ ν ∈ S, 0 < c ν ∧ weightCharacter k N L = RepresentationTheory.SymmetricPolynomials.Alternant.partitionPolynomial N ν.val := by
  classical
  -- ### Step A: the image subrepresentation `σL ≅ L` (algebraic, weight-spanning).
  let σL : Subrepresentation M.ρ :=
    ⟨LinearMap.range φ, by
      rintro g v ⟨w, rfl⟩
      exact ⟨L.ρ g w, hφ_equiv g w⟩⟩
  let e' : L ≃ₗ[k] (ofSubrepresentation M σL) := LinearEquiv.ofInjective φ hφ_inj
  have he' : ∀ (g : Matrix.GeneralLinearGroup (Fin N) k) (v : L),
      e' (L.ρ g v) = (ofSubrepresentation M σL).ρ g (e' v) := by
    intro g v
    apply subrepresentationSubtype_injective M σL
    rw [subrepresentationSubtype_equivariant]
    exact hφ_equiv g v
  have he'symm : ∀ (g : Matrix.GeneralLinearGroup (Fin N) k) (v : ofSubrepresentation M σL),
      e'.symm ((ofSubrepresentation M σL).ρ g v) = L.ρ g (e'.symm v) := by
    intro g v
    apply e'.injective
    rw [e'.apply_symm_apply, he', e'.apply_symm_apply]
  have hsubalg : GeneralLinearGroup.Auxiliary.HasAuxiliaryMapProperty N (ofSubrepresentation M σL).ρ :=
    auxiliaryCondition_subrepresentation k N M σL halg
  have hsubspan : ⨆ μ : Fin N →₀ ℕ, weightSpace k N (ofSubrepresentation M σL) (fun i => μ i) = ⊤ :=
    iSup_weightSpaces_subrepresentation_eq_top k N M σL h_span
  have hcharL : weightCharacter k N L = weightCharacter k N (ofSubrepresentation M σL) := by
    have h0 := auxiliaryPolynomial_eq_of_linearEquiv k N L.ρ (ofSubrepresentation M σL).ρ e' he'
    rwa [auxiliary_fdRep_value_of_representation_eq, auxiliary_fdRep_value_of_representation_eq] at h0
  -- ### Step B: short-exact-sequence split `char M = char L + ∑_j char (W j)`.
  have hquotalg : GeneralLinearGroup.Auxiliary.HasAuxiliaryMapProperty N (quotientBySubrepresentation M σL).ρ :=
    auxiliaryCondition_quotient M σL halg
  have hquotspan :
      ⨆ μ : Fin N →₀ ℕ, weightSpace k N (quotientBySubrepresentation M σL) (fun i => μ i) = ⊤ :=
    iSup_weightSpaces_quotient_eq_top M σL h_span
  obtain ⟨p, W, hWsimp, hWalg, hWspan, hWchar⟩ :=
    exists_simple_weightPolynomial_decomposition k N (quotientBySubrepresentation M σL) hquotalg hquotspan
  have hMdecomp : weightCharacter k N M
      = weightCharacter k N L + ∑ j, weightCharacter k N (W j) := by
    rw [weightPolynomial_eq_subrepresentation_add_quotient M σL hsubspan h_span, ← hcharL, hWchar]
  -- ### Step C: assemble the raw family `{L} ∪ {W j} ∪ {schurRepresentation ν}ᵥ` with coefficients.
  let R : Unit ⊕ Fin p ⊕ {ν // ν ∈ S} → FDRep k (Matrix.GeneralLinearGroup (Fin N) k) :=
    Sum.elim (fun _ => L) (Sum.elim W (fun ν => schurRepresentation k N ν.1.val))
  let a : Unit ⊕ Fin p ⊕ {ν // ν ∈ S} → ℚ :=
    Sum.elim (fun _ => 1) (Sum.elim (fun _ => 1) (fun ν => -(c ν.1 : ℚ)))
  have hRsimp : ∀ i, IsSimpleModule (MonoidAlgebra k (Matrix.GeneralLinearGroup (Fin N) k))
      (Representation.asModule (R i).ρ) := by
    rintro (_ | j | ν)
    · exact hLsimp
    · exact hWsimp j
    · exact isSimpleModule_fdRep_of_antitone k N ν.1.val ν.1.property
  have hRalg : ∀ i, GeneralLinearGroup.Auxiliary.HasAuxiliaryMapProperty N (R i).ρ := by
    rintro (_ | j | ν)
    · exact GeneralLinearGroup.Auxiliary.HasAuxiliaryMapProperty.auxiliary_of_linearEquiv e'.symm he'symm hsubalg
    · exact hWalg j
    · exact auxiliaryFDRep_property (k := k) N ν.1.val
  have hRspan : ∀ i, ⨆ μ : Fin N →₀ ℕ, weightSpace k N (R i) (fun j => μ j) = ⊤ := by
    rintro (_ | j | ν)
    · exact iSup_weightSpaces_eq_top_of_surjective_equivariant N (ofSubrepresentation M σL) L
        e'.symm.toLinearMap he'symm e'.symm.surjective hsubspan
    · exact hWspan j
    · exact iSup_weightSpaces_canonical_eq_top k N ν.1.val
  -- The vanishing character combination `char L + ∑_j char (W j) - ∑_{ν∈S} c_ν S_ν = char M - char M`.
  have hcomb : ∑ i, a i • weightCharacter k N (R i) = 0 := by
    have hsplit : ∑ i, a i • weightCharacter k N (R i)
        = (weightCharacter k N L + ∑ j, weightCharacter k N (W j))
          + (-∑ ν ∈ S, (c ν : ℚ) • RepresentationTheory.SymmetricPolynomials.Alternant.partitionPolynomial N ν.val) := by
      rw [Fintype.sum_sum_type, Fintype.sum_sum_type]
      have hUnit : ∑ _x : Unit, a (Sum.inl _x) • weightCharacter k N (R (Sum.inl _x))
          = weightCharacter k N L := by
        simp only [Finset.univ_unique, Finset.sum_singleton]
        change (1 : ℚ) • weightCharacter k N L = weightCharacter k N L
        rw [one_smul]
      have hW : ∑ j : Fin p, a (Sum.inr (Sum.inl j)) • weightCharacter k N (R (Sum.inr (Sum.inl j)))
          = ∑ j, weightCharacter k N (W j) := by
        refine Finset.sum_congr rfl (fun j _ => ?_)
        change (1 : ℚ) • weightCharacter k N (W j) = weightCharacter k N (W j)
        rw [one_smul]
      have hV : ∑ ν : {ν // ν ∈ S},
            a (Sum.inr (Sum.inr ν)) • weightCharacter k N (R (Sum.inr (Sum.inr ν)))
          = -∑ ν ∈ S, (c ν : ℚ) • RepresentationTheory.SymmetricPolynomials.Alternant.partitionPolynomial N ν.val := by
        rw [← Finset.sum_neg_distrib,
          ← Finset.sum_coe_sort S (fun ν => -((c ν : ℚ) • RepresentationTheory.SymmetricPolynomials.Alternant.partitionPolynomial N ν.val))]
        refine Finset.sum_congr rfl (fun ν _ => ?_)
        change (-(c ν.1 : ℚ)) • weightCharacter k N (schurRepresentation k N ν.1.val)
            = -((c ν.1 : ℚ) • RepresentationTheory.SymmetricPolynomials.Alternant.partitionPolynomial N ν.1.val)
        rw [weightCharacter_schurRepresentation_eq k N ν.1.val ν.1.property, neg_smul]
      rw [hUnit, hW, hV, ← add_assoc]
    rw [hsplit, ← hMdecomp, ← hchar, add_neg_cancel]
  -- ### Step D: the net coefficient at every character value vanishes (grouping by character value).
  have hnet := sum_coefficients_eq_zero_on_weightPolynomial_fiber k N R hRalg hRsimp
    hRspan a hcomb
  -- ### Step E: read off the conclusion from the net coefficient at `char L`.
  by_contra hcon
  push Not at hcon
  -- `hcon : ∀ ν ∈ S, 0 < c ν → weightCharacter k N L ≠ RepresentationTheory.SymmetricPolynomials.Alternant.partitionPolynomial N ν.val`
  have hcν0 : ∀ ν ∈ S, RepresentationTheory.SymmetricPolynomials.Alternant.partitionPolynomial N ν.val = weightCharacter k N L → c ν = 0 := by
    intro ν hν heq
    by_contra hc
    exact hcon ν hν (Nat.pos_of_ne_zero hc) heq.symm
  have hbw0 := hnet (weightCharacter k N L)
  -- Every term in the net coefficient at `char L` is nonnegative, and `L` itself contributes `1`.
  have hnonneg : ∀ i ∈ Finset.univ.filter (fun i => weightCharacter k N (R i) = weightCharacter k N L),
      0 ≤ a i := by
    intro i hi
    rw [Finset.mem_filter] at hi
    obtain ⟨_, hχi⟩ := hi
    match i with
    | Sum.inl () => change (0 : ℚ) ≤ 1; norm_num
    | Sum.inr (Sum.inl j) => change (0 : ℚ) ≤ 1; norm_num
    | Sum.inr (Sum.inr ν) =>
        have hchareq : weightCharacter k N (schurRepresentation k N ν.1.val) = RepresentationTheory.SymmetricPolynomials.Alternant.partitionPolynomial N ν.1.val :=
          weightCharacter_schurRepresentation_eq k N ν.1.val ν.1.property
        rw [show weightCharacter k N (R (Sum.inr (Sum.inr ν)))
            = weightCharacter k N (schurRepresentation k N ν.1.val) from rfl, hchareq] at hχi
        have hc0 : c ν.1 = 0 := hcν0 ν.1 ν.2 hχi
        change (0 : ℚ) ≤ -(c ν.1 : ℚ)
        rw [hc0]; norm_num
  have hmem0 : (Sum.inl () : Unit ⊕ Fin p ⊕ {ν // ν ∈ S})
      ∈ Finset.univ.filter (fun i => weightCharacter k N (R i) = weightCharacter k N L) := by
    rw [Finset.mem_filter]
    exact ⟨Finset.mem_univ _, rfl⟩
  have hone : (1 : ℚ)
      ≤ ∑ i ∈ Finset.univ.filter (fun i => weightCharacter k N (R i) = weightCharacter k N L), a i := by
    have hle := Finset.single_le_sum hnonneg hmem0
    -- `a (Sum.inl ())` is defeq to `1`
    -- (`Sum.elim (fun _ => 1) _ (Sum.inl ()) = 1`), so `exact hle` closes the goal.
    exact hle
  rw [hbw0] at hone
  exact absurd hone (by norm_num)

end GeneralLinearRepresentation

end RepresentationTheory.GeneralLinearRepresentation.WeightPolynomialDecomposition

end
