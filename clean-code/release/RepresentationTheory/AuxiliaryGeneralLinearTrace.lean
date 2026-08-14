/-
Copyright (c) 2026 FormalFrontier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENCE.
Authors: FormalFrontier
-/

import Mathlib
import RepresentationTheory.GeneralLinearGroup.Auxiliary
import RepresentationTheory.Auxiliary.GeneralLinearCoordinateLocalization
import RepresentationTheory.Matrix.CharpolyDiscriminant
import RepresentationTheory.LinearAlgebra.GeneralLinearGroup.Auxiliary
import RepresentationTheory.UnitTupleActions

open Matrix MvPolynomial
open RepresentationTheory.Auxiliary.GeneralLinearCoordinateLocalization
open RepresentationTheory.LinearAlgebra.GeneralLinearGroup.Auxiliary
open RepresentationTheory.Matrix.CharpolyDiscriminant

namespace RepresentationTheory.AuxiliaryGeneralLinearTrace

set_option linter.unusedDecidableInType false

variable {N : ℕ} {k : Type*} [Field k] [IsAlgClosed k] [CharZero k] [DecidableEq k]

set_option linter.unusedSectionVars false in
/-- An auxiliary representation admits a parameter expressing each of its trace values by the
displayed function. -/
theorem auxiliary_exists_trace_formula
    (M : FDRep k (Matrix.GeneralLinearGroup (Fin N) k))
    (hM : RepresentationTheory.GeneralLinearGroup.Auxiliary.HasAuxiliaryMapProperty N M.ρ) :
    ∃ T : MvPolynomial (RepresentationTheory.GeneralLinearGroup.Auxiliary.AuxiliaryIndex N) k,
      ∀ g, LinearMap.trace k M (M.ρ g) =
        RepresentationTheory.GeneralLinearGroup.Auxiliary.auxiliaryPolynomialEvaluation g T := by
  obtain ⟨m, b, P, hP⟩ := hM
  refine ⟨∑ a, P a a, fun g => ?_⟩
  rw [LinearMap.trace_eq_matrix_trace k b (M.ρ g)]
  have hsum :
      RepresentationTheory.GeneralLinearGroup.Auxiliary.auxiliaryPolynomialEvaluation g
          (∑ a, P a a) =
        ∑ a, RepresentationTheory.GeneralLinearGroup.Auxiliary.auxiliaryPolynomialEvaluation g
          (P a a) := by
    simp only [RepresentationTheory.GeneralLinearGroup.Auxiliary.auxiliaryPolynomialEvaluation,
      map_sum]
  rw [hsum, Matrix.trace]
  refine Finset.sum_congr rfl (fun a _ => ?_)
  rw [Matrix.diag_apply, LinearMap.toMatrix_apply, hP g a a]

/-- Under the auxiliary representation hypotheses, a linear combination of traces that vanishes on
the displayed elements indexed by tuples of units vanishes on every group element. -/
theorem auxiliary_trace_sum_eq_zero_of_unit_tuple
    (N : ℕ) {ι : Type} [Fintype ι]
    (L : ι → FDRep k (Matrix.GeneralLinearGroup (Fin N) k))
    (hLalg : ∀ i,
      RepresentationTheory.GeneralLinearGroup.Auxiliary.HasAuxiliaryMapProperty N (L i).ρ)
    (c : ι → k)
    (htorus : ∀ t : Fin N → kˣ,
        ∑ i, c i • LinearMap.trace k (L i)
          ((L i).ρ (RepresentationTheory.UnitTupleActions.unitTupleElement k N t)) = 0)
    (g : Matrix.GeneralLinearGroup (Fin N) k) :
    ∑ i, c i • LinearMap.trace k (L i) ((L i).ρ g) = 0 := by
  classical
  set χ : Matrix.GeneralLinearGroup (Fin N) k → k :=
    fun g => ∑ i, c i • LinearMap.trace k (L i) ((L i).ρ g) with hχdef
  rcases Nat.eq_zero_or_pos N with hN0 | hN
  · subst hN0
    have hg : g = RepresentationTheory.UnitTupleActions.unitTupleElement k 0 (fun _ => 1) := by
      apply Units.ext; ext i; exact i.elim0
    rw [hg]; exact htorus (fun _ => 1)
  have hconj : ∀ (i : ι) (h gg : Matrix.GeneralLinearGroup (Fin N) k),
      LinearMap.trace k (L i) ((L i).ρ (h * gg * h⁻¹))
        = LinearMap.trace k (L i) ((L i).ρ gg) := by
    intro i h gg
    have hρ : (L i).ρ (h * gg * h⁻¹) = (L i).ρ h * (L i).ρ gg * (L i).ρ h⁻¹ := by
      rw [map_mul, map_mul]
    have hinv : (L i).ρ h⁻¹ * (L i).ρ h = 1 := by
      rw [← map_mul, inv_mul_cancel, map_one]
    rw [hρ, LinearMap.trace_mul_comm, ← mul_assoc, hinv, one_mul]
  have hχconj : ∀ (h gg : Matrix.GeneralLinearGroup (Fin N) k),
      χ (h * gg * h⁻¹) = χ gg := by
    intro h gg
    simp only [hχdef]
    exact Finset.sum_congr rfl (fun i _ => by rw [hconj i h gg])
  choose T hT using fun i => auxiliary_exists_trace_formula (L i) (hLalg i)
  set Tsum : MvPolynomial (RepresentationTheory.GeneralLinearGroup.Auxiliary.AuxiliaryIndex N) k :=
    ∑ i, c i • T i with hTsum
  have hχeval : ∀ gg,
      χ gg =
        RepresentationTheory.GeneralLinearGroup.Auxiliary.auxiliaryPolynomialEvaluation
          gg Tsum := by
    intro gg
    simp only [hχdef, hTsum,
      RepresentationTheory.GeneralLinearGroup.Auxiliary.auxiliaryPolynomialEvaluation, map_sum]
    refine Finset.sum_congr rfl (fun i _ => ?_)
    rw [MvPolynomial.smul_eq_C_mul, map_mul, MvPolynomial.eval_C, smul_eq_mul,
      ← RepresentationTheory.GeneralLinearGroup.Auxiliary.auxiliaryPolynomialEvaluation,
      ← hT i gg]
  set F : Localization.Away (auxiliary_matrix_polynomial k N) :=
    auxiliary_localization_ringHom Tsum with hF
  have hχF : ∀ gg, χ gg = localization_evaluation_ringHom F gg := by
    intro gg
    rw [hχeval gg, hF, auxiliary_localization_ringHom_action_apply]
  obtain ⟨r, Q, hQ⟩ := exists_localization_presentation F
  have hnum : (algebraMap _ (Localization.Away (auxiliary_matrix_polynomial k N)) Q)
      = F * (algebraMap _ (Localization.Away (auxiliary_matrix_polynomial k N))
        (auxiliary_matrix_polynomial k N)) ^ r :=
    algebraMap_eq_mul_pow_of_eq_mul_invSelf_pow hQ
  have hstar : ∀ gg : Matrix.GeneralLinearGroup (Fin N) k,
      MvPolynomial.eval
          (fun ij : Fin N × Fin N => (gg : Matrix (Fin N) (Fin N) k) ij.1 ij.2) Q
        = χ gg * (gg : Matrix (Fin N) (Fin N) k).det ^ r := by
    intro gg
    have hfun := congrArg localization_evaluation_ringHom hnum
    rw [map_mul, map_pow] at hfun
    have hpt := congrFun hfun gg
    simp only [Pi.mul_apply, Pi.pow_apply, localization_evaluation_algebraMap,
      matrix_polynomial_evaluation_apply] at hpt
    rw [hpt, hχF gg, ← matrix_polynomial_evaluation_apply,
      matrix_polynomial_evaluation_auxiliary_apply]
  have eval_detPoly : ∀ x : Fin N × Fin N → k,
      MvPolynomial.eval x (auxiliary_matrix_polynomial k N) =
        (Matrix.of fun i j => x (i, j)).det := by
    intro x
    rw [auxiliary_matrix_polynomial, (MvPolynomial.eval x).map_det]
    congr 1
    ext i j
    simp [Matrix.mvPolynomialX]
  have hQ0 : Q = 0 := by
    refine RepresentationTheory.MvPolynomial.Vanishing.eq_zero_of_eval_eq_zero_off_zero_locus
      (Q := auxiliary_matrix_polynomial k N *
        RepresentationTheory.Matrix.CharpolyDiscriminant.genericMatrixDiscriminant k N)
      (mul_ne_zero auxiliary_matrix_polynomial_ne_zero
        (RepresentationTheory.Matrix.CharpolyDiscriminant.genericMatrixDiscriminant_ne_zero
          N hN)) ?_
    intro x hx
    rw [map_mul, mul_ne_zero_iff] at hx
    obtain ⟨hdet, hdiscr⟩ := hx
    rw [eval_detPoly] at hdet
    set Mx : Matrix (Fin N) (Fin N) k := Matrix.of fun i j => x (i, j) with hMx
    set g : Matrix.GeneralLinearGroup (Fin N) k :=
      Matrix.GeneralLinearGroup.mkOfDetNeZero Mx hdet with hg
    have hgcoe : (g : Matrix (Fin N) (Fin N) k) = Mx := by
      rw [hg]; rfl
    have hentries :
        (fun ij : Fin N × Fin N => (g : Matrix (Fin N) (Fin N) k) ij.1 ij.2) = x := by
      funext ij; rw [hgcoe, hMx]; simp
    rw [RepresentationTheory.Matrix.CharpolyDiscriminant.eval_genericMatrixDiscriminant]
      at hdiscr
    have hcard : (g : Matrix (Fin N) (Fin N) k).charpoly.roots.toFinset.card = N := by
      rw [hgcoe]
      exact charpoly_rootFinset_card_eq_of_discr_ne_zero Mx hN hdiscr
    obtain ⟨t, h, hgconj⟩ :=
      exists_eq_conjugate_auxiliary_of_card_roots_eq N g hcard
    have hχg : χ g = 0 := by
      rw [hgconj,
        hχconj h (RepresentationTheory.UnitTupleActions.unitTupleElement k N t)]
      simp only [hχdef]; exact htorus t
    rw [← hentries, hstar g, hχg, zero_mul]
  have hgdet : (g : Matrix (Fin N) (Fin N) k).det ≠ 0 :=
    ((Matrix.isUnit_iff_isUnit_det _).mp (Units.isUnit g)).ne_zero
  have hfinal := hstar g
  rw [hQ0, map_zero] at hfinal
  have hzero : χ g * (g : Matrix (Fin N) (Fin N) k).det ^ r = 0 := hfinal.symm
  have hχg0 : χ g = 0 :=
    (mul_eq_zero.mp hzero).resolve_right (pow_ne_zero r hgdet)
  simpa only [hχdef] using hχg0

end RepresentationTheory.AuxiliaryGeneralLinearTrace
