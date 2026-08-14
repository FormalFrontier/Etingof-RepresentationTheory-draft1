/-
Copyright (c) 2026 FormalFrontier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENCE.
Authors: FormalFrontier
-/

import RepresentationTheory.GeneralLinear.AuxiliaryRepresentationFamilies
import RepresentationTheory.AsModuleEquivalences

open MvPolynomial

namespace RepresentationTheory.GeneralLinear.AuxiliaryPolynomialQuotient

open RepresentationTheory.AsModuleEquivalences
open RepresentationTheory.Auxiliary.AuxiliaryPolynomialSubrepresentation
open RepresentationTheory.Auxiliary.GeneralLinearCoordinateLocalization
open RepresentationTheory.GeneralLinear.AuxiliaryRepresentationFamilies
open RepresentationTheory.GeneralLinearGroup.PolynomialQuotientRepresentation
open RepresentationTheory.Matrix.MvPolynomialRightMul.Matrix
open RepresentationTheory.MatrixPolynomialHomogeneity

variable {k : Type*} [Field k] {N : ℕ}

/-- Taking a homogeneous component commutes with the displayed general linear group action on
multivariate polynomials. -/
theorem homogeneousComponent_auxiliaryAction (g : Matrix.GeneralLinearGroup (Fin N) k)
    (d : ℕ) (f : MvPolynomial (Fin N × Fin N) k) :
    MvPolynomial.homogeneousComponent d (generalLinearGroupMvPolynomialRightMul k N g f) =
      generalLinearGroupMvPolynomialRightMul k N g
        (MvPolynomial.homogeneousComponent d f) := by
  have key : generalLinearGroupMvPolynomialRightMul k N g f =
      ∑ e ∈ Finset.range (f.totalDegree + 1),
        generalLinearGroupMvPolynomialRightMul k N g
          (MvPolynomial.homogeneousComponent e f) := by
    rw [← map_sum, MvPolynomial.sum_homogeneousComponent]
  rw [key, map_sum]
  rw [Finset.sum_congr rfl fun e _ =>
    MvPolynomial.homogeneousComponent_of_mem (m := d) (n := e)
      ((MvPolynomial.mem_homogeneousSubmodule e _).2
        (generalLinearAction_preserves_isHomogeneous g
          (MvPolynomial.homogeneousComponent_isHomogeneous e f)))]
  rw [Finset.sum_ite_eq]
  split
  · rfl
  · next h =>
    rw [Finset.mem_range, not_lt] at h
    rw [MvPolynomial.homogeneousComponent_eq_zero d f (by omega), map_zero]

/-- Every homogeneous component of an element of the auxiliary polynomial submodule remains in
that submodule. -/
theorem homogeneousComponent_mem_auxiliarySubmodule (d : ℕ)
    {f : MvPolynomial (Fin N × Fin N) k}
    (hf : f ∈ matrixIndexedPolynomialSubmodule k N) :
    MvPolynomial.homogeneousComponent d f ∈ matrixIndexedPolynomialSubmodule k N := by
  rw [← range_mul_auxiliary_polynomial_linearMap, LinearMap.mem_range] at hf
  obtain ⟨Q, rfl⟩ := hf
  rw [mul_auxiliary_polynomial_linearMap_apply]
  have hexp : MvPolynomial.homogeneousComponent d (auxiliary_matrix_polynomial k N * Q) =
      ∑ e ∈ Finset.range (Q.totalDegree + 1),
        MvPolynomial.homogeneousComponent d
          (auxiliary_matrix_polynomial k N * MvPolynomial.homogeneousComponent e Q) := by
    conv_lhs => rw [← MvPolynomial.sum_homogeneousComponent Q, Finset.mul_sum, map_sum]
  rw [hexp]
  refine Submodule.sum_mem _ fun e _ => ?_
  have hhom :
      (auxiliary_matrix_polynomial k N * MvPolynomial.homogeneousComponent e Q).IsHomogeneous
        (N + e) :=
    polynomial_isHomogeneous_of_degree_matrixSize.mul
      (MvPolynomial.homogeneousComponent_isHomogeneous e Q)
  rw [MvPolynomial.homogeneousComponent_of_mem
    ((MvPolynomial.mem_homogeneousSubmodule _ _).2 hhom)]
  split
  · rw [← range_mul_auxiliary_polynomial_linearMap, LinearMap.mem_range]
    exact ⟨MvPolynomial.homogeneousComponent e Q, by
      rw [mul_auxiliary_polynomial_linearMap_apply]⟩
  · exact Submodule.zero_mem _

/-- An auxiliary natural-number-indexed linear endomorphism of the displayed polynomial quotient. -/
noncomputable def auxiliaryLinearEndomorphism (k : Type*) [Field k] (N d : ℕ) :
    (MvPolynomial (Fin N × Fin N) k ⧸ matrixIndexedPolynomialSubmodule k N) →ₗ[k]
      (MvPolynomial (Fin N × Fin N) k ⧸ matrixIndexedPolynomialSubmodule k N) :=
  Submodule.mapQ (matrixIndexedPolynomialSubmodule k N)
    (matrixIndexedPolynomialSubmodule k N) (MvPolynomial.homogeneousComponent d)
    (fun _ hx => Submodule.mem_comap.2 (homogeneousComponent_mem_auxiliarySubmodule d hx))

/-- On a quotient class, the auxiliary linear endomorphism is represented by the correspondingly
indexed homogeneous component. -/
@[simp] theorem auxiliaryLinearEndomorphism_mk
    (d : ℕ) (f : MvPolynomial (Fin N × Fin N) k) :
    auxiliaryLinearEndomorphism k N d (Submodule.Quotient.mk f) =
      Submodule.Quotient.mk (MvPolynomial.homogeneousComponent d f) :=
  rfl

/-- The image of the auxiliary linear endomorphism belongs to the correspondingly indexed
auxiliary subrepresentation. -/
theorem auxiliaryLinearEndomorphism_mem (d : ℕ)
    (x : MvPolynomial (Fin N × Fin N) k ⧸ matrixIndexedPolynomialSubmodule k N) :
    auxiliaryLinearEndomorphism k N d x ∈
      (auxiliarySubrepresentationFamily k N d).toSubmodule := by
  obtain ⟨f, rfl⟩ := Submodule.Quotient.mk_surjective _ x
  rw [auxiliaryLinearEndomorphism_mk]
  exact ⟨MvPolynomial.homogeneousComponent d f,
    MvPolynomial.homogeneousComponent_mem d f, rfl⟩

/-- The auxiliary linear endomorphism commutes with the displayed general linear group action on
the quotient. -/
theorem auxiliaryLinearEndomorphism_commutes_action
    (d : ℕ) (g : Matrix.GeneralLinearGroup (Fin N) k)
    (x : MvPolynomial (Fin N × Fin N) k ⧸ matrixIndexedPolynomialSubmodule k N) :
    auxiliaryLinearEndomorphism k N d (matrixPolynomialQuotientRepresentation k N g x) =
      matrixPolynomialQuotientRepresentation k N g (auxiliaryLinearEndomorphism k N d x) := by
  obtain ⟨f, rfl⟩ := Submodule.Quotient.mk_surjective _ x
  rw [matrixPolynomialQuotientRepresentation_apply_mk, auxiliaryLinearEndomorphism_mk,
    auxiliaryLinearEndomorphism_mk, matrixPolynomialQuotientRepresentation_apply_mk,
    homogeneousComponent_auxiliaryAction]

/-- The auxiliary linear endomorphism fixes each element of the correspondingly indexed auxiliary
subrepresentation. -/
theorem auxiliaryLinearEndomorphism_eq_self_of_mem (d : ℕ)
    {x : MvPolynomial (Fin N × Fin N) k ⧸ matrixIndexedPolynomialSubmodule k N}
    (hx : x ∈ (auxiliarySubrepresentationFamily k N d).toSubmodule) :
    auxiliaryLinearEndomorphism k N d x = x := by
  obtain ⟨f, hf, rfl⟩ := hx
  rw [Submodule.mkQ_apply, auxiliaryLinearEndomorphism_mk,
    MvPolynomial.homogeneousComponent_of_mem hf, if_pos rfl]

/-- The auxiliary linear endomorphism at one index vanishes on an auxiliary subrepresentation at a
distinct index. -/
theorem auxiliaryLinearEndomorphism_eq_zero_of_mem_ne (d e : ℕ) (hde : d ≠ e)
    {x : MvPolynomial (Fin N × Fin N) k ⧸ matrixIndexedPolynomialSubmodule k N}
    (hx : x ∈ (auxiliarySubrepresentationFamily k N e).toSubmodule) :
    auxiliaryLinearEndomorphism k N d x = 0 := by
  obtain ⟨f, hf, rfl⟩ := hx
  rw [Submodule.mkQ_apply, auxiliaryLinearEndomorphism_mk,
    MvPolynomial.homogeneousComponent_of_mem hf, if_neg hde, Submodule.Quotient.mk_zero]

/-- The underlying submodules of the auxiliary subrepresentation family span the entire quotient
representation. -/
theorem iSup_auxiliarySubrepresentationFamily_eq_top :
    ⨆ d, (auxiliarySubrepresentationFamily k N d).toSubmodule = ⊤ := by
  have hA : ⨆ d, MvPolynomial.homogeneousSubmodule (Fin N × Fin N) k d = ⊤ := by
    rw [eq_top_iff]
    intro f _
    rw [← MvPolynomial.sum_homogeneousComponent f]
    exact Submodule.sum_mem _ fun d _ =>
      Submodule.mem_iSup_of_mem d (MvPolynomial.homogeneousComponent_mem d f)
  have hfun : (fun d => (auxiliarySubrepresentationFamily k N d).toSubmodule) =
      (fun d => (MvPolynomial.homogeneousSubmodule (Fin N × Fin N) k d).map
        (Submodule.mkQ (matrixIndexedPolynomialSubmodule k N))) := rfl
  rw [hfun, ← Submodule.map_iSup, hA, Submodule.map_top, Submodule.range_mkQ]

/-- The underlying submodules of the auxiliary subrepresentation family are independent. -/
theorem iSupIndep_auxiliarySubrepresentationFamily :
    iSupIndep (fun d => (auxiliarySubrepresentationFamily k N d).toSubmodule) := by
  rw [iSupIndep_def]
  intro d
  rw [Submodule.disjoint_def]
  intro x hxd hxsup
  have h1 : auxiliaryLinearEndomorphism k N d x = x :=
    auxiliaryLinearEndomorphism_eq_self_of_mem d hxd
  have h2 : auxiliaryLinearEndomorphism k N d x = 0 := by
    have hle : (⨆ (e) (_ : e ≠ d), (auxiliarySubrepresentationFamily k N e).toSubmodule) ≤
        LinearMap.ker (auxiliaryLinearEndomorphism k N d) := by
      refine iSup_le fun e => iSup_le fun hed => ?_
      intro y hy
      rw [LinearMap.mem_ker]
      exact auxiliaryLinearEndomorphism_eq_zero_of_mem_ne d e (Ne.symm hed) hy
    exact (LinearMap.mem_ker).1 (hle hxsup)
  rw [← h1, h2]

/-- A simple representation embedded equivariantly in the polynomial quotient embeds equivariantly
in some member of the auxiliary representation family. -/
theorem exists_equivariantEmbedding_auxiliaryRepresentationFamily
    (k : Type*) [Field k] (N : ℕ)
    (L : FDRep k (Matrix.GeneralLinearGroup (Fin N) k))
    (hLsimp : IsSimpleModule (MonoidAlgebra k (Matrix.GeneralLinearGroup (Fin N) k))
      (Representation.asModule L.ρ))
    (φ : L →ₗ[k]
      (MvPolynomial (Fin N × Fin N) k ⧸ matrixIndexedPolynomialSubmodule k N))
    (hφ_inj : Function.Injective φ)
    (hφ_equiv : ∀ (g : Matrix.GeneralLinearGroup (Fin N) k) (v : L),
      φ (L.ρ g v) = matrixPolynomialQuotientRepresentation k N g (φ v)) :
    ∃ (d : ℕ) (ψ : L →ₗ[k] auxiliaryRepresentationFamilyOne k N d),
      Function.Injective ψ ∧
      (∀ (g : Matrix.GeneralLinearGroup (Fin N) k) (v : L),
        ψ (L.ρ g v) = (auxiliaryRepresentationFamilyOne k N d).ρ g (ψ v)) := by
  classical
  haveI := hLsimp
  let ψ : ∀ d, L →ₗ[k] auxiliaryRepresentationFamilyOne k N d := fun d =>
    LinearMap.codRestrict (auxiliarySubrepresentationFamily k N d).toSubmodule
      (auxiliaryLinearEndomorphism k N d ∘ₗ φ)
      (fun v => auxiliaryLinearEndomorphism_mem d (φ v))
  have hψ_val : ∀ d (v : L),
      (auxiliarySubrepresentationFamily k N d).toSubmodule.subtype (ψ d v) =
        auxiliaryLinearEndomorphism k N d (φ v) := fun _ _ => rfl
  have hψ_equiv : ∀ d (g : Matrix.GeneralLinearGroup (Fin N) k) (v : L),
      ψ d (L.ρ g v) = (auxiliaryRepresentationFamilyOne k N d).ρ g (ψ d v) := by
    intro d g v
    apply Subtype.val_injective
    change auxiliaryLinearEndomorphism k N d (φ (L.ρ g v)) =
      matrixPolynomialQuotientRepresentation k N g
        (auxiliaryLinearEndomorphism k N d (φ v))
    rw [hφ_equiv, auxiliaryLinearEndomorphism_commutes_action]
  have hschur : ∀ d, Function.Injective (ψ d) ∨ ψ d = 0 := by
    intro d
    let Ψ : Representation.asModule L.ρ →ₗ[MonoidAlgebra k
        (Matrix.GeneralLinearGroup (Fin N) k)]
        Representation.asModule (auxiliaryRepresentationFamilyOne k N d).ρ :=
      linearMapAsModule (ψ d) (hψ_equiv d)
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
    obtain ⟨p, hp⟩ :=
      Submodule.Quotient.mk_surjective (matrixIndexedPolynomialSubmodule k N) (φ v)
    have hdecomp :
        (∑ d ∈ Finset.range (p.totalDegree + 1),
          auxiliaryLinearEndomorphism k N d (φ v)) = φ v := by
      have hstep : ∀ d, auxiliaryLinearEndomorphism k N d (φ v) =
          (matrixIndexedPolynomialSubmodule k N).mkQ
            (MvPolynomial.homogeneousComponent d p) := by
        intro d
        rw [← hp, Submodule.mkQ_apply, auxiliaryLinearEndomorphism_mk]
      simp_rw [hstep]
      rw [← map_sum, MvPolynomial.sum_homogeneousComponent, Submodule.mkQ_apply, hp]
    have hzeroterm : ∀ d, auxiliaryLinearEndomorphism k N d (φ v) = 0 := by
      intro d
      rw [← hψ_val d v]
      calc
        (auxiliarySubrepresentationFamily k N d).toSubmodule.subtype (ψ d v) =
            (auxiliarySubrepresentationFamily k N d).toSubmodule.subtype (ψ d 0) := by
          congr 1
          rw [hzero d, LinearMap.zero_apply, LinearMap.zero_apply]
        _ = auxiliaryLinearEndomorphism k N d (φ 0) := hψ_val d 0
        _ = 0 := by rw [map_zero, map_zero]
    have hφv0 : φ v = 0 := by
      rw [← hdecomp]; exact Finset.sum_eq_zero fun d _ => hzeroterm d
    exact hv0 (hφ_inj (by rw [hφv0, map_zero]))
  obtain ⟨d, hd⟩ := hexists
  exact ⟨d, ψ d, hd, hψ_equiv d⟩

end RepresentationTheory.GeneralLinear.AuxiliaryPolynomialQuotient
