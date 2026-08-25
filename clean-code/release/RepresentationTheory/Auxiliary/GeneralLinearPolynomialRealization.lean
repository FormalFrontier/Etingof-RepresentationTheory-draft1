/-
Copyright (c) 2026 mathlib-initiative. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: mathlib-initiative
-/

import RepresentationTheory.GeneralLinearGroup.Auxiliary
import RepresentationTheory.AuxiliaryCharacter
import RepresentationTheory.GL.Weights
import RepresentationTheory.GeneralLinearGroup.WeightCharacter

namespace RepresentationTheory.Auxiliary.GeneralLinearPolynomialRealization

open MvPolynomial
open RepresentationTheory.Auxiliary.GeneralLinearCoordinateLocalization
open RepresentationTheory.AuxiliaryCharacter
open RepresentationTheory.GeneralLinearGroup.Auxiliary
open RepresentationTheory.GeneralLinearGroup.PolynomialQuotientRepresentation
open RepresentationTheory.GeneralLinearGroup.WeightCharacter
open RepresentationTheory.GL.Weights
open RepresentationTheory.LinearAlgebra.Matrix.GeneralLinearGroup.LocalizationAction
open RepresentationTheory.Matrix.MvPolynomialRightMul.Matrix

variable {k : Type} [Field k] {N : ℕ}

/-- Evaluating a polynomial after the matrix substitution associated with a matrix equals
evaluating the original polynomial on the matrix product. -/
lemma eval_matrix_substitution (M g : Matrix (Fin N) (Fin N) k)
    (p : MvPolynomial (Fin N × Fin N) k) :
    MvPolynomial.eval (fun ij : Fin N × Fin N => g ij.1 ij.2) (mvPolynomialRightMul M p)
      = MvPolynomial.eval (fun ij : Fin N × Fin N => (g * M) ij.1 ij.2) p := by
  classical
  suffices halgs :
      (MvPolynomial.aeval (fun ij : Fin N × Fin N => g ij.1 ij.2)).comp
          (mvPolynomialRightMul M) =
        (MvPolynomial.aeval (fun ij : Fin N × Fin N => (g * M) ij.1 ij.2) :
          MvPolynomial (Fin N × Fin N) k →ₐ[k] k) by
    have := AlgHom.congr_fun halgs p
    simpa [AlgHom.comp_apply, MvPolynomial.aeval_eq_eval] using this
  apply MvPolynomial.algHom_ext
  rintro ⟨i, j⟩
  rw [AlgHom.comp_apply, mvPolynomialRightMul_apply_X, map_sum, MvPolynomial.aeval_X,
    Matrix.mul_apply]
  refine Finset.sum_congr rfl fun l _ => ?_
  rw [map_smul, MvPolynomial.aeval_X, smul_eq_mul, mul_comm]

/-- Evaluating the action of one general linear matrix on a localized element at another matrix
agrees with evaluation at their product in the displayed order. -/
lemma localization_evaluation_action_apply
    (h g : Matrix.GeneralLinearGroup (Fin N) k)
    (x : Localization.Away (auxiliary_matrix_polynomial k N)) :
    localization_evaluation_ringHom
        (generalLinearGroupLocalizationRepresentation k N h x) g =
      localization_evaluation_ringHom x (g * h) := by
  have key : ∀ a : MvPolynomial (Fin N × Fin N) k,
      localization_evaluation_ringHom
          (generalLinearGroupLocalizationRepresentation k N h
            (algebraMap (MvPolynomial (Fin N × Fin N) k) _ a)) g =
        localization_evaluation_ringHom (algebraMap _ _ a) (g * h) := by
    intro a
    rw [generalLinearGroupLocalizationRepresentation_algebraMap_apply,
      localization_evaluation_algebraMap, localization_evaluation_algebraMap,
      matrix_polynomial_evaluation_apply, matrix_polynomial_evaluation_apply]
    change MvPolynomial.eval
        (fun ij : Fin N × Fin N => (g : Matrix (Fin N) (Fin N) k) ij.1 ij.2)
        (mvPolynomialRightMul (h : Matrix (Fin N) (Fin N) k) a) = _
    rw [eval_matrix_substitution]
    rfl
  let F : Localization.Away (auxiliary_matrix_polynomial k N) →+* k :=
    (Pi.evalRingHom (fun _ : Matrix.GeneralLinearGroup (Fin N) k => k) g).comp
      (localization_evaluation_ringHom.comp
        (generalLinearGroupLocalizationMap h).toRingHom)
  let G : Localization.Away (auxiliary_matrix_polynomial k N) →+* k :=
    (Pi.evalRingHom (fun _ : Matrix.GeneralLinearGroup (Fin N) k => k) (g * h)).comp
      localization_evaluation_ringHom
  have hFG : F = G := by
    apply IsLocalization.ringHom_ext (Submonoid.powers (auxiliary_matrix_polynomial k N))
    apply RingHom.ext
    intro a
    simp only [F, G, RingHom.comp_apply, Pi.evalRingHom_apply, AlgHom.toRingHom_eq_coe,
      AlgHom.coe_toRingHom]
    rw [← generalLinearGroupLocalizationRepresentation_apply_eq_map]
    exact key a
  have hx := RingHom.congr_fun hFG x
  simpa only [F, G, RingHom.comp_apply, Pi.evalRingHom_apply, AlgHom.toRingHom_eq_coe,
    AlgHom.coe_toRingHom, ← generalLinearGroupLocalizationRepresentation_apply_eq_map] using hx

/-- Evaluation of a scalar multiple in the localization is the corresponding scalar multiple of
its evaluation function. -/
lemma localization_evaluation_smul (c : k)
    (x : Localization.Away (auxiliary_matrix_polynomial k N)) :
    localization_evaluation_ringHom (c • x) =
      c • localization_evaluation_ringHom x := by
  rw [Algebra.smul_def, map_mul]
  have hc : localization_evaluation_ringHom
      (algebraMap k (Localization.Away (auxiliary_matrix_polynomial k N)) c) =
      Function.const _ c := by
    rw [IsScalarTower.algebraMap_apply k (MvPolynomial (Fin N × Fin N) k)
        (Localization.Away (auxiliary_matrix_polynomial k N)),
      localization_evaluation_algebraMap]
    funext g
    rw [matrix_polynomial_evaluation_apply, MvPolynomial.algebraMap_eq,
      MvPolynomial.eval_C]
    rfl
  rw [hc]
  funext g
  simp [Function.const_apply, smul_eq_mul]

/-- Under the displayed supremum hypothesis, there are finitely indexed vectors and auxiliary
weights such that each displayed general linear element scales each vector by the corresponding
power of the chosen unit. -/
theorem exists_auxiliary_weight_vector_data [IsAlgClosed k] [CharZero k]
    (M : FDRep k (Matrix.GeneralLinearGroup (Fin N) k))
    (h_span : ⨆ (μ : Fin N →₀ ℕ), weightSpace k N M (fun i => μ i) = ⊤) :
    ∃ (d : ℕ) (v : Module.Basis (Fin d) k M) (wt : Fin d → (Fin N → ℕ)),
      ∀ (c : Fin d) (i : Fin N) (t : kˣ),
        M.ρ (diagonalUnit k N i t) (v c) = ((t : k) ^ wt c i) • v c := by
  classical
  set p : (Fin N →₀ ℕ) → Submodule k M :=
    fun μ => weightSpace k N M (fun i => μ i) with hp_def
  have h_indep : iSupIndep p := iSupIndep_auxiliaryWeightSpace k N M
  have hs_fin : {μ | p μ ≠ ⊥}.Finite := finite_support_weightSpace k N M
  haveI : Fintype {μ // p μ ≠ ⊥} := hs_fin.fintype
  have h_internal : DirectSum.IsInternal (fun μ : {μ // p μ ≠ ⊥} => p μ.val) := by
    rw [DirectSum.isInternal_ne_bot_iff]
    exact (DirectSum.isInternal_submodule_iff_iSupIndep_and_iSup_eq_top _).mpr
      ⟨h_indep, h_span⟩
  let bb := h_internal.collectedBasis (fun μ => Module.finBasis k (p μ.val))
  let e := Fintype.equivFin
    (Σ μ : {μ // p μ ≠ ⊥}, Fin (Module.finrank k (p μ.val)))
  refine ⟨Fintype.card
      (Σ μ : {μ // p μ ≠ ⊥}, Fin (Module.finrank k (p μ.val))),
    bb.reindex e, fun c i => (e.symm c).1.val i, ?_⟩
  intro c i t
  have hmem : (bb.reindex e) c ∈
      weightSpace k N M (fun j => (e.symm c).1.val j) := by
    rw [Module.Basis.reindex_apply]
    have hcb := h_internal.collectedBasis_mem
      (fun μ => Module.finBasis k (p μ.val)) (e.symm c)
    simpa only [hp_def] using hcb
  simp only [weightSpace, Submodule.mem_iInf, LinearMap.mem_ker, LinearMap.sub_apply,
    LinearMap.smul_apply, LinearMap.id_coe, id_eq, sub_eq_zero] at hmem
  exact hmem i t

/-- Under the stated spanning and representation hypotheses, there is a finite basis whose matrix
coefficients are evaluations of multivariable polynomials in the entries of a general linear
matrix. -/
theorem exists_basis_with_polynomial_matrix_coefficients [CharZero k] [IsAlgClosed k]
    (_n : ℕ) (M : FDRep k (Matrix.GeneralLinearGroup (Fin N) k))
    (halg : HasAuxiliaryMapProperty N M.ρ)
    (h_span : ⨆ (μ : Fin N →₀ ℕ), weightSpace k N M (fun i => μ i) = ⊤) :
    ∃ (d : ℕ) (b : Module.Basis (Fin d) k M)
       (Q : Fin d → Fin d → MvPolynomial (Fin N × Fin N) k),
         ∀ (g : Matrix.GeneralLinearGroup (Fin N) k) a c,
           b.repr (M.ρ g (b c)) a =
             MvPolynomial.eval
               (fun ij : Fin N × Fin N =>
                 (g : Matrix (Fin N) (Fin N) k) ij.1 ij.2)
               (Q a c) := by
  classical
  obtain ⟨d, v, wt, hv⟩ := exists_auxiliary_weight_vector_data M h_span
  obtain ⟨m, b₀, P₀, hP₀⟩ := halg
  set R : Fin d → Fin d → MvPolynomial (AuxiliaryIndex N) k :=
    fun a c => ∑ a₀ : Fin m, ∑ c₀ : Fin m,
      (v.repr (b₀ a₀) a * b₀.repr (v c) c₀) • P₀ a₀ c₀ with hR
  have hReval : ∀ (g : Matrix.GeneralLinearGroup (Fin N) k) (a c : Fin d),
      auxiliaryPolynomialEvaluation g (R a c) = v.repr (M.ρ g (v c)) a := by
    intro g a c
    have hP₀' : ∀ a₀ c₀,
        auxiliaryPolynomialEvaluation g (P₀ a₀ c₀) =
          b₀.repr (M.ρ g (b₀ c₀)) a₀ :=
      fun a₀ c₀ => (hP₀ g a₀ c₀).symm
    have hlin : auxiliaryPolynomialEvaluation g (R a c) =
        ∑ a₀ : Fin m, ∑ c₀ : Fin m,
          (v.repr (b₀ a₀) a * b₀.repr (v c) c₀) *
            auxiliaryPolynomialEvaluation g (P₀ a₀ c₀) := by
      rw [hR]
      simp only [auxiliaryPolynomialEvaluation, map_sum, MvPolynomial.smul_eval]
    rw [hlin]
    simp_rw [hP₀']
    have expand_col : M.ρ g (v c) =
        ∑ c₀ : Fin m, b₀.repr (v c) c₀ • M.ρ g (b₀ c₀) := by
      conv_lhs =>
        rw [show v c = ∑ c₀, b₀.repr (v c) c₀ • b₀ c₀ from
          (b₀.sum_repr (v c)).symm]
      rw [map_sum]; simp_rw [map_smul]
    rw [expand_col, map_sum]
    simp only [map_smul, Finsupp.coe_finsetSum, Finset.sum_apply, Finsupp.coe_smul,
      Pi.smul_apply, smul_eq_mul]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun c₀ _ => ?_
    have hrow : v.repr (M.ρ g (b₀ c₀)) a =
        ∑ a₀ : Fin m,
          b₀.repr (M.ρ g (b₀ c₀)) a₀ * v.repr (b₀ a₀) a := by
      conv_lhs =>
        rw [show M.ρ g (b₀ c₀) =
          ∑ a₀, b₀.repr (M.ρ g (b₀ c₀)) a₀ • b₀ a₀ from
            (b₀.sum_repr _).symm]
      rw [map_sum]
      simp only [map_smul, Finsupp.coe_finsetSum, Finset.sum_apply, Finsupp.coe_smul,
        Pi.smul_apply, smul_eq_mul]
    rw [hrow, Finset.mul_sum]
    refine Finset.sum_congr rfl fun a₀ _ => ?_
    ring
  have hcoeff : ∀ (g : Matrix.GeneralLinearGroup (Fin N) k) (a c : Fin d),
      localization_evaluation_ringHom (auxiliary_localization_ringHom (R a c)) g =
        v.repr (M.ρ g (v c)) a :=
    fun g a c => by rw [← auxiliary_localization_ringHom_action_apply, hReval]
  have hRweight : ∀ a c, auxiliary_localization_ringHom (R a c) ∈
      integerTupleSubmodule k N (generalLinearGroupLocalizationRepresentation k N)
        (fun j => (wt c j : ℤ)) := by
    intro a c
    rw [mem_weightSpace_iff_forall_apply_eq_smul]
    intro i s
    apply localization_evaluation_injective
    funext g
    have hscal : ((s ^ (wt c i : ℤ) : kˣ) : k) = (s : k) ^ wt c i := by
      rw [zpow_natCast, Units.val_pow_eq_pow_val]
    rw [hscal, localization_evaluation_action_apply,
      hcoeff (g * diagonalUnit k N i s) a c, map_mul, Module.End.mul_apply,
      hv c i s, map_smul, map_smul, Finsupp.smul_apply, smul_eq_mul,
      localization_evaluation_smul, Pi.smul_apply, hcoeff g a c, smul_eq_mul]
  have hstable : ∀ (g : Matrix.GeneralLinearGroup (Fin N) k),
      ∀ x ∈ Submodule.span k
          (Set.range fun j : Fin d × Fin d => auxiliary_localization_ringHom (R j.1 j.2)),
        generalLinearGroupLocalizationRepresentation k N g x ∈
          Submodule.span k
            (Set.range fun j : Fin d × Fin d => auxiliary_localization_ringHom (R j.1 j.2)) := by
    intro g x hx
    induction hx using Submodule.span_induction with
    | mem y hy =>
        obtain ⟨⟨a, c⟩, rfl⟩ := hy
        have hexp : generalLinearGroupLocalizationRepresentation k N g
              (auxiliary_localization_ringHom (R a c)) =
            ∑ c' : Fin d, (v.repr (M.ρ g (v c)) c') •
              auxiliary_localization_ringHom (R a c') := by
          apply localization_evaluation_injective
          funext hh
          have hLHS : localization_evaluation_ringHom
                (generalLinearGroupLocalizationRepresentation k N g
                  (auxiliary_localization_ringHom (R a c))) hh =
              ∑ c' : Fin d,
                v.repr (M.ρ g (v c)) c' * v.repr (M.ρ hh (v c')) a := by
            rw [localization_evaluation_action_apply, hcoeff (hh * g) a c,
              map_mul, Module.End.mul_apply]
            conv_lhs =>
              rw [show M.ρ g (v c) =
                ∑ c' : Fin d, (v.repr (M.ρ g (v c)) c') • v c' from
                  (v.sum_repr _).symm]
            rw [map_sum, map_sum]
            simp only [map_smul, Finsupp.coe_finsetSum, Finset.sum_apply,
              Finsupp.coe_smul, Pi.smul_apply, smul_eq_mul]
          have hRHS : localization_evaluation_ringHom
                (∑ c' : Fin d, (v.repr (M.ρ g (v c)) c') •
                  auxiliary_localization_ringHom (R a c')) hh =
              ∑ c' : Fin d,
                v.repr (M.ρ g (v c)) c' * v.repr (M.ρ hh (v c')) a := by
            rw [map_sum, Finset.sum_apply]
            refine Finset.sum_congr rfl fun c' _ => ?_
            rw [localization_evaluation_smul, Pi.smul_apply, hcoeff hh a c',
              smul_eq_mul]
          rw [hLHS, hRHS]
        rw [hexp]
        exact Submodule.sum_mem _ fun c' _ =>
          Submodule.smul_mem _ _ (Submodule.subset_span ⟨(a, c'), rfl⟩)
    | zero => rw [map_zero]; exact Submodule.zero_mem _
    | add a b _ _ iha ihb => rw [map_add]; exact Submodule.add_mem _ iha ihb
    | smul c a _ iha => rw [map_smul]; exact Submodule.smul_mem _ _ iha
  have hQex : ∀ j : Fin d × Fin d, ∃ Q : MvPolynomial (Fin N × Fin N) k,
      ∀ g : Matrix.GeneralLinearGroup (Fin N) k,
        auxiliaryPolynomialEvaluation g (R j.1 j.2) =
          MvPolynomial.eval
            (fun ij : Fin N × Fin N =>
              (g : Matrix (Fin N) (Fin N) k) ij.1 ij.2) Q :=
    fun j => exists_polynomial_eval_matrixEntries_of_weight_and_span_stable
      (fun j : Fin d × Fin d => R j.1 j.2) (fun j => wt j.2)
      (fun j => hRweight j.1 j.2) hstable j
  choose Qf hQf using hQex
  refine ⟨d, v, fun a c => Qf (a, c), ?_⟩
  intro g a c
  rw [← hReval g a c]
  exact hQf (a, c) g

end RepresentationTheory.Auxiliary.GeneralLinearPolynomialRealization
