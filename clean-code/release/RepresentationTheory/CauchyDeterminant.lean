/-
Copyright (c) 2026 mathlib-initiative. All rights reserved.
Released under Apache 2.0 license as described in the file LICENCE.
Authors: mathlib-initiative
-/

import Mathlib
import RepresentationTheory.Alignment.Attribute

open Matrix Finset

set_option maxHeartbeats 800000

namespace RepresentationTheory.CauchyDeterminant

/-- Evaluates the determinant of the matrix of pairwise reciprocal differences. -/
@[source_ref "Chapter5/Lemma5.15.3" (role := primary),
  source_ref "Chapter5/Discussion_proof_of_Lemma5.15.3" (role := supporting)]
theorem cauchy_det
    (N : ℕ) (z y : Fin N → ℂ)
    (hzy : ∀ i j, z i ≠ y j) :
    (∏ i : Fin N, ∏ j : Fin N, (z i - y j)) *
      (Matrix.of (fun i j : Fin N => (z i - y j)⁻¹)).det =
    (∏ i : Fin N, ∏ j ∈ Ioi i, (z j - z i)) *
    (∏ i : Fin N, ∏ j ∈ Ioi i, (y i - y j)) := by
  have h_cauchy : Matrix.det (Matrix.of (fun i j => 1 / ((z i) - (y j)))) = (∏ i, ∏ j ∈ Finset.Ioi i, ((z j) - (z i))) * (∏ i, ∏ j ∈ Finset.Ioi i, ((y i) - (y j))) / (∏ i, ∏ j, ((z i) - (y j))) := by
    have h_cauchy_det : ∀ (N : ℕ) (z y : Fin N → ℂ), (∀ i j, z i ≠ y j) → Matrix.det (Matrix.of (fun i j => 1 / ((z i) - (y j)))) = (∏ i, ∏ j ∈ Finset.Ioi i, ((z j) - (z i))) * (∏ i, ∏ j ∈ Finset.Ioi i, ((y i) - (y j))) / (∏ i, ∏ j, ((z i) - (y j))) := by
      intro N z y hzy;
      induction' N with N ih <;> simp +decide [ Fin.prod_univ_succ, Finset.prod_mul_distrib ] at *;
      have h_factor : Matrix.det (Matrix.of (fun i j => (z i - y j)⁻¹)) = (z 0 - y 0)⁻¹ * Matrix.det (Matrix.of (fun i j => (z (Fin.succ i) - y (Fin.succ j))⁻¹ - (z (Fin.succ i) - y 0)⁻¹ * (z 0 - y (Fin.succ j))⁻¹ * (z 0 - y 0))) := by
        have h_factor : Matrix.det (Matrix.of (fun i j => (z i - y j)⁻¹)) = Matrix.det (Matrix.of (fun i j => if i = 0 then (z 0 - y j)⁻¹ else if j = 0 then 0 else (z i - y j)⁻¹ - (z i - y 0)⁻¹ * (z 0 - y j)⁻¹ * (z 0 - y 0))) := by
          have h_row_ops : ∃ P : Matrix (Fin (N + 1)) (Fin (N + 1)) ℂ, P.det = 1 ∧ P * Matrix.of (fun i j => (z i - y j)⁻¹) = Matrix.of (fun i j => if i = 0 then (z 0 - y j)⁻¹ else if j = 0 then 0 else (z i - y j)⁻¹ - (z i - y 0)⁻¹ * (z 0 - y j)⁻¹ * (z 0 - y 0)) := by
            refine ⟨ Matrix.of ( fun i j => if i = 0 then if j = 0 then 1 else 0 else if j = 0 then - ( z i - y 0 ) ⁻¹ * ( z 0 - y 0 ) else if i = j then 1 else 0 ), ?_, ?_ ⟩ <;> simp +decide [ Matrix.det_succ_row_zero ];
            · erw [ Matrix.det_of_upperTriangular ] <;> norm_num [ Matrix.submatrix ];
              intro i j hij; aesop;
            · ext i j; simp +decide [ Matrix.mul_apply ] ; split_ifs <;> simp_all +decide [ sub_eq_iff_eq_add ] <;> ring_nf;
              · simp +decide [ Finset.sum_ite, Finset.filter_eq', Finset.filter_ne', * ] ; ring_nf;
              · simp +decide [ Finset.sum_ite, Finset.filter_eq', Finset.filter_ne', * ] ; ring_nf;
          obtain ⟨ P, hP₁, hP₂ ⟩ := h_row_ops; rw [ ← hP₂, Matrix.det_mul, hP₁, one_mul ] ;
        rw [ h_factor, Matrix.det_succ_column_zero ];
        simp +decide [ Matrix.submatrix ];
      have h_simplify : Matrix.det (Matrix.of (fun i j => (z (Fin.succ i) - y (Fin.succ j))⁻¹ - (z (Fin.succ i) - y 0)⁻¹ * (z 0 - y (Fin.succ j))⁻¹ * (z 0 - y 0))) = Matrix.det (Matrix.of (fun i j => (z (Fin.succ i) - y (Fin.succ j))⁻¹ * ((z (Fin.succ i) - z 0) * (y 0 - y (Fin.succ j))) / ((z (Fin.succ i) - y 0) * (z 0 - y (Fin.succ j))))) := by
        refine congr_arg Matrix.det ( funext fun i => funext fun j => ?_ );
        simp +decide [ sub_eq_iff_eq_add ];
        field_simp;
        rw [ div_add', div_div, div_eq_div_iff ] <;> simp +decide [ sub_eq_iff_eq_add, hzy ] ; ring_nf;
      have h_ind : Matrix.det (Matrix.of (fun i j => (z (Fin.succ i) - y (Fin.succ j))⁻¹ * ((z (Fin.succ i) - z 0) * (y 0 - y (Fin.succ j))) / ((z (Fin.succ i) - y 0) * (z 0 - y (Fin.succ j))))) = (∏ i : Fin N, (z (Fin.succ i) - z 0)) * (∏ i : Fin N, (y 0 - y (Fin.succ i))) / ((∏ i : Fin N, (z (Fin.succ i) - y 0)) * (∏ i : Fin N, (z 0 - y (Fin.succ i)))) * Matrix.det (Matrix.of (fun i j => (z (Fin.succ i) - y (Fin.succ j))⁻¹)) := by
        have h_ind : Matrix.det (Matrix.of (fun i j => (z (Fin.succ i) - y (Fin.succ j))⁻¹ * ((z (Fin.succ i) - z 0) * (y 0 - y (Fin.succ j))) / ((z (Fin.succ i) - y 0) * (z 0 - y (Fin.succ j))))) = Matrix.det (Matrix.diagonal (fun i => (z (Fin.succ i) - z 0) / (z (Fin.succ i) - y 0)) * Matrix.of (fun i j => (z (Fin.succ i) - y (Fin.succ j))⁻¹) * Matrix.diagonal (fun j => (y 0 - y (Fin.succ j)) / (z 0 - y (Fin.succ j)))) := by
          congr with i j ; simp +decide [ div_eq_mul_inv, mul_assoc, mul_comm, mul_left_comm ];
        rw [ h_ind, Matrix.det_mul, Matrix.det_mul ] ; norm_num [ Finset.prod_mul_distrib, Finset.prod_div_distrib ] ; ring;
      rw [ h_factor, h_simplify, h_ind ];
      rw [ ih ( fun i => z i.succ ) ( fun i => y i.succ ) ( fun i j => hzy _ _ ) ] ; ring_nf;
      grind;
    exact h_cauchy_det N z y hzy;
  simp +zetaDelta at *;
  rw [ h_cauchy, mul_div_cancel₀ _ ( Finset.prod_ne_zero_iff.mpr fun i hi => Finset.prod_ne_zero_iff.mpr fun j hj => sub_ne_zero.mpr ( hzy i j ) ) ]

end RepresentationTheory.CauchyDeterminant
