/-
Copyright (c) 2026 mathlib-initiative. All rights reserved.
Released under Apache 2.0 license as described in the file LICENCE.
Authors: mathlib-initiative
-/

import Mathlib
import RepresentationTheory.Alignment.Attribute

/-! # Quaternion Rotation Maps -/

open scoped Quaternion
open Matrix

namespace RepresentationTheory.QuaternionRotationMaps





/-- A matrix identity for the displayed action or transformation. -/
@[source_ref "Chapter4/Problem4.12.7" (role := primary)]
theorem matrixAction_011564
    (W : Submodule ℝ (Fin 2 → ℂ))
    (hW : ∀ A : Matrix.specialUnitaryGroup (Fin 2) ℂ, ∀ v : Fin 2 → ℂ,
      v ∈ W → (A : Matrix (Fin 2) (Fin 2) ℂ).mulVec v ∈ W) :
    W = ⊥ ∨ W = ⊤ := by
  rw [or_iff_not_imp_left]
  intro hne
  obtain ⟨v, hvW, hv0⟩ := (Submodule.ne_bot_iff W).mp hne
  
  have hD : (!![Complex.I, 0; 0, -Complex.I] : Matrix (Fin 2) (Fin 2) ℂ) ∈
      Matrix.specialUnitaryGroup (Fin 2) ℂ := by
    rw [Matrix.mem_specialUnitaryGroup_iff]
    refine ⟨?_, ?_⟩
    · rw [Matrix.mem_unitaryGroup_iff, Matrix.star_eq_conjTranspose]
      ext i j
      fin_cases i <;> fin_cases j <;>
        simp [Matrix.mul_apply, Fin.sum_univ_two, Matrix.conjTranspose_apply]
    · simp [Matrix.det_fin_two]
  have hJ : (!![(0 : ℂ), -1; 1, 0] : Matrix (Fin 2) (Fin 2) ℂ) ∈
      Matrix.specialUnitaryGroup (Fin 2) ℂ := by
    rw [Matrix.mem_specialUnitaryGroup_iff]
    refine ⟨?_, ?_⟩
    · rw [Matrix.mem_unitaryGroup_iff, Matrix.star_eq_conjTranspose]
      ext i j
      fin_cases i <;> fin_cases j <;>
        simp [Matrix.mul_apply, Fin.sum_univ_two, Matrix.conjTranspose_apply]
    · simp [Matrix.det_fin_two]
  
  have eDv : (!![Complex.I, 0; 0, -Complex.I] : Matrix (Fin 2) (Fin 2) ℂ).mulVec v
      = ![Complex.I * v 0, -Complex.I * v 1] := by
    funext i; fin_cases i <;>
      simp [Matrix.mulVec, dotProduct, Matrix.cons_val_zero, Matrix.cons_val_one]
  have eJv : (!![(0 : ℂ), -1; 1, 0] : Matrix (Fin 2) (Fin 2) ℂ).mulVec v
      = ![-(v 1), v 0] := by
    funext i; fin_cases i <;>
      simp [Matrix.mulVec, dotProduct, Matrix.cons_val_zero, Matrix.cons_val_one]
  have eDJv : (!![Complex.I, 0; 0, -Complex.I] : Matrix (Fin 2) (Fin 2) ℂ).mulVec
      ![-(v 1), v 0] = ![-Complex.I * v 1, -Complex.I * v 0] := by
    funext i; fin_cases i <;>
      simp [Matrix.mulVec, dotProduct, Matrix.cons_val_zero, Matrix.cons_val_one]
  have hDv : ![Complex.I * v 0, -Complex.I * v 1] ∈ W := eDv ▸ hW ⟨_, hD⟩ v hvW
  have hJv : ![-(v 1), v 0] ∈ W := eJv ▸ hW ⟨_, hJ⟩ v hvW
  have hDJv : ![-Complex.I * v 1, -Complex.I * v 0] ∈ W := eDJv ▸ hW ⟨_, hD⟩ _ hJv
  
  set f : Fin 4 → (Fin 2 → ℂ) :=
    ![v, ![Complex.I * v 0, -Complex.I * v 1], ![-(v 1), v 0],
      ![-Complex.I * v 1, -Complex.I * v 0]] with hf
  
  set Nr : ℝ := Complex.normSq (v 0) + Complex.normSq (v 1) with hNr_def
  have hNr : Nr ≠ 0 := by
    intro h
    apply hv0
    have h0 : Complex.normSq (v 0) = 0 := by
      nlinarith [Complex.normSq_nonneg (v 0), Complex.normSq_nonneg (v 1)]
    have h1 : Complex.normSq (v 1) = 0 := by
      nlinarith [Complex.normSq_nonneg (v 0), Complex.normSq_nonneg (v 1)]
    funext i
    fin_cases i
    · exact Complex.normSq_eq_zero.mp h0
    · exact Complex.normSq_eq_zero.mp h1
  have hli : LinearIndependent ℝ f := by
    rw [Fintype.linearIndependent_iff]
    intro g hg
    have h0 := congrFun hg 0
    have h1 := congrFun hg 1
    simp only [hf, Finset.sum_apply, Fin.sum_univ_four, Pi.smul_apply,
      Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.cons_val_three,
      Matrix.head_cons, Matrix.tail_cons, Pi.zero_apply,
      Complex.real_smul] at h0 h1
    
    
    
    set α : ℂ := (g 0 : ℂ) + Complex.I * (g 1 : ℂ) with hα_def
    set β : ℂ := (g 2 : ℂ) + Complex.I * (g 3 : ℂ) with hβ_def
    have eqI : v 0 * α - v 1 * β = 0 := by linear_combination h0
    have h1c := congrArg (starRingEnd ℂ) h1
    simp only [map_add, map_mul, map_neg, Complex.conj_ofReal, map_zero,
      Complex.conj_I] at h1c
    have eqII : (starRingEnd ℂ) (v 1) * α + (starRingEnd ℂ) (v 0) * β = 0 := by
      linear_combination h1c
    
    have hNc : (Nr : ℂ) = v 0 * (starRingEnd ℂ) (v 0) + v 1 * (starRingEnd ℂ) (v 1) := by
      rw [Complex.mul_conj, Complex.mul_conj, hNr_def]; push_cast; ring
    have hαz : (Nr : ℂ) * α = 0 := by
      rw [hNc]
      linear_combination (starRingEnd ℂ) (v 0) * eqI + v 1 * eqII
    have hβz : (Nr : ℂ) * β = 0 := by
      rw [hNc]
      linear_combination (-(starRingEnd ℂ) (v 1)) * eqI + v 0 * eqII
    have hα0 : α = 0 := by
      rcases mul_eq_zero.mp hαz with h | h
      · exact absurd (Complex.ofReal_eq_zero.mp h) hNr
      · exact h
    have hβ0 : β = 0 := by
      rcases mul_eq_zero.mp hβz with h | h
      · exact absurd (Complex.ofReal_eq_zero.mp h) hNr
      · exact h
    
    have hg0 : g 0 = 0 := by
      have := congrArg Complex.re hα0
      simpa [hα_def, Complex.add_re, Complex.mul_re] using this
    have hg1 : g 1 = 0 := by
      have := congrArg Complex.im hα0
      simpa [hα_def, Complex.add_im, Complex.mul_im] using this
    have hg2 : g 2 = 0 := by
      have := congrArg Complex.re hβ0
      simpa [hβ_def, Complex.add_re, Complex.mul_re] using this
    have hg3 : g 3 = 0 := by
      have := congrArg Complex.im hβ0
      simpa [hβ_def, Complex.add_im, Complex.mul_im] using this
    intro i
    fin_cases i
    · exact hg0
    · exact hg1
    · exact hg2
    · exact hg3
  have hcard : Fintype.card (Fin 4) = Module.finrank ℝ (Fin 2 → ℂ) := by
    simp [Module.finrank_pi_fintype, Complex.finrank_real_complex]
  have hspan : Submodule.span ℝ (Set.range f) = ⊤ :=
    hli.span_eq_top_of_card_eq_finrank hcard
  have hsub : Submodule.span ℝ (Set.range f) ≤ W := by
    rw [Submodule.span_le]
    rintro x ⟨i, rfl⟩
    fin_cases i
    · exact hvW
    · exact hDv
    · exact hJv
    · exact hDJv
  exact le_antisymm le_top (hspan ▸ hsub)



/-- The equality displayed in the formal statement. -/
@[source_ref "Chapter4/Problem4.12.7" (role := primary)]
theorem valueFormula_011596 (q₁ q₂ : ℍ[ℝ]) :
    star (q₁ * q₂) = star q₂ * star q₁ :=
  star_mul q₁ q₂



/-- A norm-square identity for the displayed quaternion expression. -/
@[source_ref "Chapter4/Problem4.12.7" (role := primary)]
theorem quaternionNorm_011503 (q₁ q₂ : ℍ[ℝ]) :
    Quaternion.normSq (q₁ * q₂) = Quaternion.normSq q₁ * Quaternion.normSq q₂ :=
  map_mul Quaternion.normSq q₁ q₂




/-- The matrix-valued construction specified by the displayed formal signature. -/
noncomputable def quaternionToMatrix (q : ℍ[ℝ]) : Matrix (Fin 2) (Fin 2) ℂ :=
  !![(q.re : ℂ) + q.imI * Complex.I, (q.imJ : ℂ) + q.imK * Complex.I;
     -(q.imJ : ℂ) + q.imK * Complex.I, (q.re : ℂ) - q.imI * Complex.I]

/-- A coordinate identity for the displayed quaternion. -/
@[simp] lemma quaternionCoordinate_011552 (q : ℍ[ℝ]) :
    quaternionToMatrix q 0 0 = (q.re : ℂ) + q.imI * Complex.I := rfl
/-- A coordinate identity for the displayed quaternion. -/
@[simp] lemma quaternionCoordinate_011551 (q : ℍ[ℝ]) :
    quaternionToMatrix q 0 1 = (q.imJ : ℂ) + q.imK * Complex.I := rfl
/-- A coordinate identity for the displayed quaternion. -/
@[simp] lemma quaternionCoordinate_011550 (q : ℍ[ℝ]) :
    quaternionToMatrix q 1 0 = -(q.imJ : ℂ) + q.imK * Complex.I := rfl
/-- A coordinate identity for the displayed quaternion. -/
@[simp] lemma quaternionCoordinate_011549 (q : ℍ[ℝ]) :
    quaternionToMatrix q 1 1 = (q.re : ℂ) - q.imI * Complex.I := rfl


/-- The equality displayed in the formal statement. -/
lemma valueFormula_011558 : quaternionToMatrix 1 = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp


/-- The equality displayed in the formal statement. -/
lemma valueFormula_011556 (q₁ q₂ : ℍ[ℝ]) : quaternionToMatrix (q₁ * q₂) = quaternionToMatrix q₁ * quaternionToMatrix q₂ := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    (simp only [quaternionToMatrix, Matrix.mul_apply, Fin.sum_univ_two, Fin.isValue, Fin.mk_zero, Fin.mk_one,
        Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.of_apply,
        Matrix.cons_val', Matrix.empty_val', Matrix.cons_val_fin_one,
        Quaternion.re_mul, Quaternion.imI_mul, Quaternion.imJ_mul, Quaternion.imK_mul] ;
      apply Complex.ext <;>
      simp only [Complex.add_re, Complex.add_im, Complex.mul_re, Complex.mul_im, Complex.sub_re,
        Complex.sub_im, Complex.neg_re, Complex.neg_im, Complex.ofReal_re, Complex.ofReal_im,
        Complex.I_re, Complex.I_im, mul_zero, mul_one, neg_zero, sub_zero,
        zero_sub, add_zero, zero_add] <;> ring)


/-- A matrix identity for the displayed action or transformation. -/
lemma matrixAction_011553 (q : ℍ[ℝ]) : quaternionToMatrix (star q) = (quaternionToMatrix q)ᴴ := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    (simp only [quaternionToMatrix, Matrix.conjTranspose_apply, Fin.isValue, Fin.mk_zero, Fin.mk_one,
        Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.of_apply,
        Matrix.cons_val', Matrix.empty_val', Matrix.cons_val_fin_one,
        Quaternion.re_star, Quaternion.imI_star, Quaternion.imJ_star, Quaternion.imK_star] ;
      apply Complex.ext <;> simp)


/-- A norm-square identity for the displayed quaternion expression. -/
lemma quaternionNorm_011554 (q : ℍ[ℝ]) : (quaternionToMatrix q).det = ((Quaternion.normSq q : ℝ) : ℂ) := by
  rw [Matrix.det_fin_two, Quaternion.normSq_def']
  simp only [quaternionCoordinate_011552, quaternionCoordinate_011551, quaternionCoordinate_011550, quaternionCoordinate_011549]
  apply Complex.ext <;>
    simp only [Complex.add_re, Complex.add_im, Complex.mul_re, Complex.mul_im, Complex.sub_re,
      Complex.sub_im, Complex.neg_re, Complex.neg_im, Complex.ofReal_re, Complex.ofReal_im,
      Complex.I_re, Complex.I_im, mul_zero, mul_one, neg_zero, sub_zero,
      zero_sub, add_zero, zero_add] <;> ring


/-- A norm-square identity for the displayed quaternion expression. -/
lemma quaternionNorm_011502 {q : ℍ[ℝ]} : q ∈ unitary ℍ[ℝ] ↔ Quaternion.normSq q = 1 := by
  rw [Unitary.mem_iff]
  constructor
  · rintro ⟨h, -⟩
    rw [Quaternion.star_mul_self, ← Quaternion.coe_one, Quaternion.coe_inj] at h
    exact h
  · intro h
    have hc : ((Quaternion.normSq q : ℝ) : ℍ[ℝ]) = 1 := by rw [h, Quaternion.coe_one]
    exact ⟨by rw [Quaternion.star_mul_self]; exact hc, by rw [Quaternion.self_mul_star]; exact hc⟩


/-- The monoid homomorphism specified by the displayed formal signature. -/
@[source_ref "Chapter4/Problem4.12.7" (role := supporting)]
noncomputable def unitQuaternionToSpecialUnitary : unitary ℍ[ℝ] →* Matrix.specialUnitaryGroup (Fin 2) ℂ where
  toFun q := ⟨quaternionToMatrix (q : ℍ[ℝ]), by
    have hq : Quaternion.normSq (q : ℍ[ℝ]) = 1 := quaternionNorm_011502.mp q.2
    rw [Matrix.mem_specialUnitaryGroup_iff]
    refine ⟨?_, ?_⟩
    · rw [Matrix.mem_unitaryGroup_iff', Matrix.star_eq_conjTranspose, ← matrixAction_011553,
        ← valueFormula_011556, Quaternion.star_mul_self, hq, Quaternion.coe_one, valueFormula_011558]
    · rw [quaternionNorm_011554, hq]; norm_num⟩
  map_one' := Subtype.ext (by simpa using valueFormula_011558)
  map_mul' a b := Subtype.ext (by simpa using valueFormula_011556 (a : ℍ[ℝ]) (b : ℍ[ℝ]))

/-- Injectivity of the map displayed in the formal statement. -/
@[source_ref "Chapter4/Problem4.12.7" (role := supporting)]
lemma injective_011546 : Function.Injective unitQuaternionToSpecialUnitary := by
  intro a b h
  have hm : quaternionToMatrix (a : ℍ[ℝ]) = quaternionToMatrix (b : ℍ[ℝ]) := congrArg Subtype.val h
  have e00 := congrFun (congrFun hm 0) 0
  have e01 := congrFun (congrFun hm 0) 1
  simp only [quaternionCoordinate_011552, quaternionCoordinate_011551] at e00 e01
  apply Subtype.ext
  apply Quaternion.ext
  · simpa using congrArg Complex.re e00
  · simpa using congrArg Complex.im e00
  · simpa using congrArg Complex.re e01
  · simpa using congrArg Complex.im e01

/-- Surjectivity of the map displayed in the formal statement. -/
@[source_ref "Chapter4/Problem4.12.7" (role := supporting)]
lemma surjective_011547 : Function.Surjective unitQuaternionToSpecialUnitary := by
  intro A
  set M : Matrix (Fin 2) (Fin 2) ℂ := (A : Matrix (Fin 2) (Fin 2) ℂ) with hM
  have hmem := A.2
  rw [Matrix.mem_specialUnitaryGroup_iff] at hmem
  obtain ⟨hu, hdet⟩ := hmem
  have huc : Mᴴ * M = 1 := by
    rw [← Matrix.star_eq_conjTranspose]; exact Matrix.mem_unitaryGroup_iff'.mp hu
  have hinvL : M⁻¹ = Mᴴ := Matrix.inv_eq_left_inv huc
  have hinvR : M⁻¹ = M.adjugate := by
    apply Matrix.inv_eq_right_inv; rw [Matrix.mul_adjugate, hdet, one_smul]
  have hadj : Mᴴ = M.adjugate := by rw [← hinvL, hinvR]
  rw [Matrix.adjugate_fin_two] at hadj
  have h11 : M 1 1 = star (M 0 0) := by
    have h := congrFun (congrFun hadj 0) 0
    simp only [Matrix.conjTranspose_apply, Matrix.cons_val_zero,
      Matrix.of_apply, Matrix.cons_val', Matrix.empty_val',
      Matrix.cons_val_fin_one] at h
    exact h.symm
  have h10 : M 1 0 = -star (M 0 1) := by
    have h := congrFun (congrFun hadj 1) 0
    simp only [Matrix.conjTranspose_apply, Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.of_apply, Matrix.cons_val', Matrix.empty_val',
      Matrix.cons_val_fin_one] at h
    rw [h]; ring
  set q : ℍ[ℝ] := ⟨(M 0 0).re, (M 0 0).im, (M 0 1).re, (M 0 1).im⟩ with hq
  have key : (Complex.normSq (M 0 0) + Complex.normSq (M 0 1) : ℝ) = 1 := by
    have hdet2 : M.det = M 0 0 * M 1 1 - M 0 1 * M 1 0 := Matrix.det_fin_two M
    rw [h11, h10, mul_neg, sub_neg_eq_add] at hdet2
    have e0 : M 0 0 * star (M 0 0) = (Complex.normSq (M 0 0) : ℂ) := Complex.mul_conj (M 0 0)
    have e1 : M 0 1 * star (M 0 1) = (Complex.normSq (M 0 1) : ℂ) := Complex.mul_conj (M 0 1)
    rw [e0, e1, hdet] at hdet2
    exact_mod_cast hdet2.symm
  have hnorm : Quaternion.normSq q = 1 := by
    rw [Quaternion.normSq_def']
    simp only [hq, Complex.normSq_apply] at key ⊢
    nlinarith [key]
  refine ⟨⟨q, quaternionNorm_011502.mpr hnorm⟩, ?_⟩
  apply Subtype.ext
  change quaternionToMatrix q = M
  rw [Matrix.eta_fin_two M, h11, h10]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [quaternionToMatrix, hq, Complex.ext_iff]



/-- Existence of the displayed multiplicative equivalence under the stated hypotheses. -/
@[source_ref "Chapter4/Problem4.12.7" (role := primary)]
theorem multiplicativeEquivalence_011606 :
    Nonempty (unitary ℍ[ℝ] ≃* Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  ⟨MulEquiv.ofBijective unitQuaternionToSpecialUnitary ⟨injective_011546, surjective_011547⟩⟩



/-- Injectivity of the map displayed in the formal statement. -/
lemma injective_011555 : Function.Injective quaternionToMatrix := by
  intro a b h
  have e00 := congrFun (congrFun h 0) 0
  have e01 := congrFun (congrFun h 0) 1
  simp only [quaternionCoordinate_011552, quaternionCoordinate_011551] at e00 e01
  apply Quaternion.ext
  · simpa using congrArg Complex.re e00
  · simpa using congrArg Complex.im e00
  · simpa using congrArg Complex.re e01
  · simpa using congrArg Complex.im e01


/-- Auxiliary result whose proposition is not displayed in the packet. -/
lemma Auxiliary011557 : quaternionToMatrix (-1 : ℍ[ℝ]) = -1 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [quaternionToMatrix]









section PartF


/-- The quaternion-valued construction specified by the displayed formal signature. -/
noncomputable def quaternionI : ℍ[ℝ] := ⟨0, 1, 0, 0⟩

/-- The quaternion-valued construction specified by the displayed formal signature. -/
noncomputable def quaternionJ : ℍ[ℝ] := ⟨0, 0, 1, 0⟩

/-- The quaternion-valued construction specified by the displayed formal signature. -/
noncomputable def quaternionK : ℍ[ℝ] := ⟨0, 0, 0, 1⟩

/-- A coordinate identity for the displayed quaternion. -/
@[simp] lemma quaternionCoordinate_011517 : quaternionI.re = 0 := rfl
/-- A coordinate identity for the displayed quaternion. -/
@[simp] lemma quaternionCoordinate_011510 : quaternionI.imI = 1 := rfl
/-- A coordinate identity for the displayed quaternion. -/
@[simp] lemma quaternionCoordinate_011511 : quaternionI.imJ = 0 := rfl
/-- A coordinate identity for the displayed quaternion. -/
@[simp] lemma quaternionCoordinate_011512 : quaternionI.imK = 0 := rfl
/-- A coordinate identity for the displayed quaternion. -/
@[simp] lemma quaternionCoordinate_011527 : quaternionJ.re = 0 := rfl
/-- A coordinate identity for the displayed quaternion. -/
@[simp] lemma quaternionCoordinate_011520 : quaternionJ.imI = 0 := rfl
/-- A coordinate identity for the displayed quaternion. -/
@[simp] lemma quaternionCoordinate_011521 : quaternionJ.imJ = 1 := rfl
/-- A coordinate identity for the displayed quaternion. -/
@[simp] lemma quaternionCoordinate_011522 : quaternionJ.imK = 0 := rfl
/-- A coordinate identity for the displayed quaternion. -/
@[simp] lemma quaternionCoordinate_011537 : quaternionK.re = 0 := rfl
/-- A coordinate identity for the displayed quaternion. -/
@[simp] lemma quaternionCoordinate_011530 : quaternionK.imI = 0 := rfl
/-- A coordinate identity for the displayed quaternion. -/
@[simp] lemma quaternionCoordinate_011531 : quaternionK.imJ = 0 := rfl
/-- A coordinate identity for the displayed quaternion. -/
@[simp] lemma quaternionCoordinate_011532 : quaternionK.imK = 1 := rfl










/-- Auxiliary result whose proposition is not displayed in the packet. -/
@[source_ref "Chapter4/Problem4.12.7" (role := supporting), simp] lemma Auxiliary011514 : quaternionI * quaternionI = -1 := by ext <;> simp [quaternionI]
/-- Auxiliary result whose proposition is not displayed in the packet. -/
@[source_ref "Chapter4/Problem4.12.7" (role := supporting), simp] lemma Auxiliary011525 : quaternionJ * quaternionJ = -1 := by ext <;> simp [quaternionJ]
/-- Auxiliary result whose proposition is not displayed in the packet. -/
@[source_ref "Chapter4/Problem4.12.7" (role := supporting), simp] lemma Auxiliary011536 : quaternionK * quaternionK = -1 := by ext <;> simp [quaternionK]

/-- The equality displayed in the formal statement. -/
@[source_ref "Chapter4/Problem4.12.7" (role := primary), simp] lemma valueFormula_011515 : quaternionI * quaternionJ = quaternionK := by ext <;> simp [quaternionI, quaternionJ, quaternionK]
/-- The equality displayed in the formal statement. -/
@[source_ref "Chapter4/Problem4.12.7" (role := primary), simp] lemma valueFormula_011524 : quaternionJ * quaternionI = -quaternionK := by ext <;> simp [quaternionI, quaternionJ, quaternionK]
/-- The equality displayed in the formal statement. -/
@[source_ref "Chapter4/Problem4.12.7" (role := primary), simp] lemma valueFormula_011526 : quaternionJ * quaternionK = quaternionI := by ext <;> simp [quaternionI, quaternionJ, quaternionK]
/-- The equality displayed in the formal statement. -/
@[source_ref "Chapter4/Problem4.12.7" (role := primary), simp] lemma valueFormula_011535 : quaternionK * quaternionJ = -quaternionI := by ext <;> simp [quaternionI, quaternionJ, quaternionK]
/-- The equality displayed in the formal statement. -/
@[source_ref "Chapter4/Problem4.12.7" (role := primary), simp] lemma valueFormula_011534 : quaternionK * quaternionI = quaternionJ := by ext <;> simp [quaternionI, quaternionJ, quaternionK]
/-- The equality displayed in the formal statement. -/
@[source_ref "Chapter4/Problem4.12.7" (role := primary), simp] lemma valueFormula_011516 : quaternionI * quaternionK = -quaternionJ := by ext <;> simp [quaternionI, quaternionJ, quaternionK]



/-- The quaternion-valued construction specified by the displayed formal signature. -/
@[source_ref "Chapter4/Problem4.12.7" (role := primary)]
noncomputable def quaternionBasis : Module.Basis (Fin 4) ℝ ℍ[ℝ] :=
  QuaternionAlgebra.basisOneIJK _ _ _

/-- The equality displayed in the formal statement. -/
@[simp] lemma valueFormula_011563 : quaternionBasis 0 = 1 := by
  change QuaternionAlgebra.basisOneIJK (-1) 0 (-1) 0 = 1
  apply Module.Basis.apply_eq_iff.mpr; ext i
  fin_cases i <;> simp [QuaternionAlgebra.coe_basisOneIJK_repr]
/-- The equality displayed in the formal statement. -/
@[simp] lemma valueFormula_011560 : quaternionBasis 1 = quaternionI := by
  change QuaternionAlgebra.basisOneIJK (-1) 0 (-1) 1 = quaternionI
  apply Module.Basis.apply_eq_iff.mpr; ext i
  fin_cases i <;> simp [QuaternionAlgebra.coe_basisOneIJK_repr, quaternionI]
/-- The equality displayed in the formal statement. -/
@[simp] lemma valueFormula_011562 : quaternionBasis 2 = quaternionJ := by
  change QuaternionAlgebra.basisOneIJK (-1) 0 (-1) 2 = quaternionJ
  apply Module.Basis.apply_eq_iff.mpr; ext i
  fin_cases i <;> simp [QuaternionAlgebra.coe_basisOneIJK_repr, quaternionJ]
/-- The equality displayed in the formal statement. -/
@[simp] lemma valueFormula_011561 : quaternionBasis 3 = quaternionK := by
  change QuaternionAlgebra.basisOneIJK (-1) 0 (-1) 3 = quaternionK
  apply Module.Basis.apply_eq_iff.mpr; ext i
  fin_cases i <;> simp [QuaternionAlgebra.coe_basisOneIJK_repr, quaternionK]


/-- A cardinality or dimension identity for the displayed finite object. -/
@[source_ref "Chapter4/Problem4.12.7" (role := supporting)]
theorem cardinalityFormula_011489 : Module.finrank ℝ ℍ[ℝ] = 4 :=
  Quaternion.finrank_eq_four



/-- The equality displayed in the formal statement. -/
@[simp] lemma valueFormula_011597 : star quaternionI = -quaternionI := by ext <;> simp [quaternionI]
/-- The equality displayed in the formal statement. -/
@[simp] lemma valueFormula_011598 : star quaternionJ = -quaternionJ := by ext <;> simp [quaternionJ]
/-- The equality displayed in the formal statement. -/
@[simp] lemma valueFormula_011599 : star quaternionK = -quaternionK := by ext <;> simp [quaternionK]



/-- A norm-square identity for the displayed quaternion expression. -/
lemma quaternionNorm_011504 : Quaternion.normSq quaternionI = 1 := by rw [Quaternion.normSq_def']; simp [quaternionI]
/-- A norm-square identity for the displayed quaternion expression. -/
lemma quaternionNorm_011505 : Quaternion.normSq quaternionJ = 1 := by rw [Quaternion.normSq_def']; simp [quaternionJ]
/-- A norm-square identity for the displayed quaternion expression. -/
lemma quaternionNorm_011506 : Quaternion.normSq quaternionK = 1 := by rw [Quaternion.normSq_def']; simp [quaternionK]

/-- A membership statement for the displayed set, submodule, or subgroup. -/
lemma membershipCharacterization_011513 : quaternionI ∈ unitary ℍ[ℝ] := quaternionNorm_011502.mpr quaternionNorm_011504
/-- A membership statement for the displayed set, submodule, or subgroup. -/
lemma membershipCharacterization_011523 : quaternionJ ∈ unitary ℍ[ℝ] := quaternionNorm_011502.mpr quaternionNorm_011505
/-- A membership statement for the displayed set, submodule, or subgroup. -/
lemma membershipCharacterization_011533 : quaternionK ∈ unitary ℍ[ℝ] := quaternionNorm_011502.mpr quaternionNorm_011506


/-- The quaternion-valued construction specified by the displayed formal signature. -/
@[source_ref "Chapter4/Problem4.12.7" (role := supporting)]
def realUnitQuaternions : Set ℍ[ℝ] := {1, -1, quaternionI, -quaternionI, quaternionJ, -quaternionJ, quaternionK, -quaternionK}



/-- A membership statement for the displayed set, submodule, or subgroup. -/
@[source_ref "Chapter4/Problem4.12.7" (role := supporting)]
lemma membershipCharacterization_011466 : ∀ x ∈ realUnitQuaternions, x ∈ unitary ℍ[ℝ] := by
  intro x hx
  simp only [realUnitQuaternions, Set.mem_insert_iff, Set.mem_singleton_iff] at hx
  rcases hx with h | h | h | h | h | h | h | h <;> subst h <;>
    rw [quaternionNorm_011502] <;>
    simp [Quaternion.normSq_neg, quaternionNorm_011504, quaternionNorm_011505, quaternionNorm_011506]


/-- A membership statement for the displayed set, submodule, or subgroup. -/
lemma membershipCharacterization_011507 : (1 : ℍ[ℝ]) ∈ realUnitQuaternions := by simp [realUnitQuaternions]



/-- A membership statement for the displayed set, submodule, or subgroup. -/
@[source_ref "Chapter4/Problem4.12.7" (role := supporting)]
lemma membershipCharacterization_011460 : ∀ x ∈ realUnitQuaternions, ∀ y ∈ realUnitQuaternions, x * y ∈ realUnitQuaternions := by
  intro x hx y hy
  simp only [realUnitQuaternions, Set.mem_insert_iff, Set.mem_singleton_iff] at hx hy
  rcases hx with h | h | h | h | h | h | h | h <;> subst h <;>
    rcases hy with h | h | h | h | h | h | h | h <;> subst h <;>
    simp [realUnitQuaternions]



/-- A membership statement for the displayed set, submodule, or subgroup. -/
@[source_ref "Chapter4/Problem4.12.7" (role := supporting)]
lemma membershipCharacterization_011463 : ∀ x ∈ realUnitQuaternions, star x ∈ realUnitQuaternions := by
  intro x hx
  simp only [realUnitQuaternions, Set.mem_insert_iff, Set.mem_singleton_iff] at hx
  rcases hx with h | h | h | h | h | h | h | h <;> subst h <;> simp [realUnitQuaternions]




/-- The matrix-valued construction specified by the displayed formal signature. -/
noncomputable def quaternionRotationMatrix (q : ℍ[ℝ]) : Matrix (Fin 3) (Fin 3) ℝ :=
  !![ (q * quaternionI * star q).imI, (q * quaternionJ * star q).imI, (q * quaternionK * star q).imI;
      (q * quaternionI * star q).imJ, (q * quaternionJ * star q).imJ, (q * quaternionK * star q).imJ;
      (q * quaternionI * star q).imK, (q * quaternionJ * star q).imK, (q * quaternionK * star q).imK ]

attribute [local simp] Quaternion.re_mul Quaternion.imI_mul Quaternion.imJ_mul Quaternion.imK_mul
  Quaternion.re_star Quaternion.imI_star Quaternion.imJ_star Quaternion.imK_star



/-- The equality displayed in the formal statement. -/
lemma valueFormula_011580 (q : ℍ[ℝ]) : quaternionRotationMatrix (-q) = quaternionRotationMatrix q := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp only [quaternionRotationMatrix, star_neg, neg_mul, mul_neg, neg_neg,
      Matrix.cons_val', Matrix.empty_val',
      Matrix.cons_val_fin_one, Matrix.of_apply]


/-- The equality displayed in the formal statement. -/
lemma valueFormula_011582 : quaternionRotationMatrix (1 : ℍ[ℝ]) = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp only [quaternionRotationMatrix, star_one, one_mul, mul_one,
      Matrix.cons_val', Matrix.empty_val', Matrix.cons_val_fin_one,
      Matrix.of_apply, quaternionCoordinate_011510, quaternionCoordinate_011511, quaternionCoordinate_011512, quaternionCoordinate_011520, quaternionCoordinate_011521, quaternionCoordinate_011522,
      quaternionCoordinate_011530, quaternionCoordinate_011531, quaternionCoordinate_011532, Matrix.one_apply] <;> norm_num


/-- Auxiliary result whose proposition is not displayed in the packet. -/
lemma Auxiliary011581 : quaternionRotationMatrix (-1 : ℍ[ℝ]) = 1 := by
  rw [valueFormula_011580, valueFormula_011582]




/-- The equality displayed in the formal statement. -/
lemma valueFormula_011579 (q₁ q₂ : ℍ[ℝ]) : quaternionRotationMatrix (q₁ * q₂) = quaternionRotationMatrix q₁ * quaternionRotationMatrix q₂ := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp only [quaternionRotationMatrix, Matrix.mul_apply, Fin.sum_univ_three, Matrix.cons_val_zero,
      Matrix.cons_val_one, Matrix.cons_val', Matrix.empty_val',
      Matrix.cons_val_fin_one, Matrix.of_apply, Fin.isValue] <;>
    simp <;> ring


/-- A coordinate identity for the displayed quaternion. -/
lemma quaternionCoordinate_011575 (q : ℍ[ℝ]) :
    quaternionRotationMatrix q 0 0 = q.re ^ 2 + q.imI ^ 2 - q.imJ ^ 2 - q.imK ^ 2 := by
  simp only [quaternionRotationMatrix, Matrix.cons_val_zero, Matrix.cons_val', Matrix.empty_val',
    Matrix.cons_val_fin_one, Matrix.of_apply]
  simp ; ring


/-- A coordinate identity for the displayed quaternion. -/
lemma quaternionCoordinate_011576 (q : ℍ[ℝ]) :
    quaternionRotationMatrix q 1 1 = q.re ^ 2 - q.imI ^ 2 + q.imJ ^ 2 - q.imK ^ 2 := by
  simp only [quaternionRotationMatrix, Matrix.cons_val_one, Matrix.cons_val', Matrix.empty_val',
    Matrix.cons_val_fin_one, Matrix.of_apply, Fin.isValue]
  simp ; ring



/-- A norm-square identity for the displayed quaternion expression. -/
lemma quaternionNorm_011578 (q : ℍ[ℝ]) (hq : Quaternion.normSq q = 1) :
    quaternionRotationMatrix q ∈ Matrix.specialOrthogonalGroup (Fin 3) ℝ := by
  have h4 : q.re ^ 2 + q.imI ^ 2 + q.imJ ^ 2 + q.imK ^ 2 = 1 := by
    rw [Quaternion.normSq_def'] at hq; linarith
  rw [Matrix.mem_specialOrthogonalGroup_iff]
  refine ⟨?_, ?_⟩
  · rw [Matrix.mem_orthogonalGroup_iff]
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp only [quaternionRotationMatrix, Matrix.mul_apply, Matrix.transpose_apply, Fin.sum_univ_three,
        Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
        Matrix.cons_val', Matrix.empty_val', Matrix.cons_val_fin_one, Matrix.of_apply,
        Matrix.one_apply, Fin.isValue] <;>
      simp <;>
      · first
        | linear_combination (q.re ^ 2 + q.imI ^ 2 + q.imJ ^ 2 + q.imK ^ 2 + 1) * h4
        | linear_combination (0 : ℝ)
  · rw [Matrix.det_fin_three]
    simp only [quaternionRotationMatrix, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
      Matrix.cons_val', Matrix.empty_val', Matrix.cons_val_fin_one,
      Matrix.of_apply, Fin.isValue]
    simp
    linear_combination
      ((q.re ^ 2 + q.imI ^ 2 + q.imJ ^ 2 + q.imK ^ 2) ^ 2 +
        (q.re ^ 2 + q.imI ^ 2 + q.imJ ^ 2 + q.imK ^ 2) + 1) * h4




/-- Auxiliary result whose proposition is not displayed in the packet. -/
@[source_ref "Chapter4/Problem4.12.7" (role := supporting)]
lemma Auxiliary011577 (q : ℍ[ℝ]) (hq : Quaternion.normSq q = 1) :
    quaternionRotationMatrix q = 1 ↔ q = 1 ∨ q = -1 := by
  constructor
  · intro h
    have h4 : q.re ^ 2 + q.imI ^ 2 + q.imJ ^ 2 + q.imK ^ 2 = 1 := by
      rw [Quaternion.normSq_def'] at hq; linarith
    have e00 : quaternionRotationMatrix q 0 0 = 1 := by rw [h]; simp
    have e11 : quaternionRotationMatrix q 1 1 = 1 := by rw [h]; simp
    rw [quaternionCoordinate_011575] at e00
    rw [quaternionCoordinate_011576] at e11
    have hb : q.imI = 0 := by nlinarith [sq_nonneg q.imI, sq_nonneg q.imJ, sq_nonneg q.imK]
    have hc : q.imJ = 0 := by nlinarith [sq_nonneg q.imI, sq_nonneg q.imJ, sq_nonneg q.imK]
    have hd : q.imK = 0 := by nlinarith [sq_nonneg q.imI, sq_nonneg q.imJ, sq_nonneg q.imK]
    have ha : q.re = 1 ∨ q.re = -1 := mul_self_eq_one_iff.mp (by nlinarith)
    rcases ha with ha | ha
    · left; ext <;> simp [ha, hb, hc, hd]
    · right; ext <;> simp [ha, hb, hc, hd]
  · rintro (rfl | rfl)
    · exact valueFormula_011582
    · exact Auxiliary011581



/-- The monoid homomorphism specified by the displayed formal signature. -/
@[source_ref "Chapter4/Problem4.12.7" (role := supporting)]
noncomputable def unitQuaternionToRotation : unitary ℍ[ℝ] →* Matrix.specialOrthogonalGroup (Fin 3) ℝ where
  toFun q := ⟨quaternionRotationMatrix (q : ℍ[ℝ]), quaternionNorm_011578 _ (quaternionNorm_011502.mp q.2)⟩
  map_one' := Subtype.ext (by simpa using valueFormula_011582)
  map_mul' a b := Subtype.ext (by simpa using valueFormula_011579 (a : ℍ[ℝ]) (b : ℍ[ℝ]))

/-- A membership statement for the displayed set, submodule, or subgroup. -/
@[simp] lemma membershipCharacterization_011571 (q : unitary ℍ[ℝ]) :
    (unitQuaternionToRotation q : Matrix (Fin 3) (Fin 3) ℝ) = quaternionRotationMatrix (q : ℍ[ℝ]) := rfl










/-- A matrix identity for the displayed action or transformation. -/
lemma matrixAction_011583 (c s : ℝ) :
    quaternionRotationMatrix (⟨c, s, 0, 0⟩ : ℍ[ℝ]) =
      !![c ^ 2 + s ^ 2, 0, 0;
         0, c ^ 2 - s ^ 2, -(2 * c * s);
         0, 2 * c * s, c ^ 2 - s ^ 2] := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [quaternionRotationMatrix, quaternionI, quaternionJ, quaternionK] <;> ring



/-- A matrix identity for the displayed action or transformation. -/
lemma matrixAction_011584 (c s : ℝ) :
    quaternionRotationMatrix (⟨c, 0, s, 0⟩ : ℍ[ℝ]) =
      !![c ^ 2 - s ^ 2, 0, 2 * c * s;
         0, c ^ 2 + s ^ 2, 0;
         -(2 * c * s), 0, c ^ 2 - s ^ 2] := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [quaternionRotationMatrix, quaternionI, quaternionJ, quaternionK] <;> ring



/-- A matrix identity for the displayed action or transformation. -/
lemma matrixAction_011586 (c s : ℝ) :
    quaternionRotationMatrix (⟨c, 0, 0, s⟩ : ℍ[ℝ]) =
      !![c ^ 2 - s ^ 2, -(2 * c * s), 0;
         2 * c * s, c ^ 2 - s ^ 2, 0;
         0, 0, c ^ 2 + s ^ 2] := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [quaternionRotationMatrix, quaternionI, quaternionJ, quaternionK] <;> ring



/-- The matrix-valued construction specified by the displayed formal signature. -/
noncomputable def rotationAboutThirdAxis (θ : ℝ) : Matrix (Fin 3) (Fin 3) ℝ :=
  !![Real.cos θ, -Real.sin θ, 0; Real.sin θ, Real.cos θ, 0; 0, 0, 1]



/-- The matrix-valued construction specified by the displayed formal signature. -/
noncomputable def rotationAboutSecondAxis (θ : ℝ) : Matrix (Fin 3) (Fin 3) ℝ :=
  !![Real.cos θ, 0, Real.sin θ; 0, 1, 0; -Real.sin θ, 0, Real.cos θ]




/-- The equality displayed in the formal statement. -/
lemma valueFormula_011587 (θ : ℝ) :
    quaternionRotationMatrix (⟨Real.cos (θ / 2), 0, 0, Real.sin (θ / 2)⟩ : ℍ[ℝ]) = rotationAboutThirdAxis θ := by
  have hθ : (2 : ℝ) * (θ / 2) = θ := by ring
  have hcos : Real.cos (θ / 2) ^ 2 - Real.sin (θ / 2) ^ 2 = Real.cos θ := by
    have h := Real.cos_two_mul' (θ / 2); rw [hθ] at h; exact h.symm
  have hsin : 2 * Real.cos (θ / 2) * Real.sin (θ / 2) = Real.sin θ := by
    have h := Real.sin_two_mul (θ / 2); rw [hθ] at h; rw [h]; ring
  have hone : Real.cos (θ / 2) ^ 2 + Real.sin (θ / 2) ^ 2 = 1 := Real.cos_sq_add_sin_sq _
  rw [matrixAction_011586, rotationAboutThirdAxis, hcos, hsin, hone]



/-- The equality displayed in the formal statement. -/
lemma valueFormula_011585 (θ : ℝ) :
    quaternionRotationMatrix (⟨Real.cos (θ / 2), 0, Real.sin (θ / 2), 0⟩ : ℍ[ℝ]) = rotationAboutSecondAxis θ := by
  have hθ : (2 : ℝ) * (θ / 2) = θ := by ring
  have hcos : Real.cos (θ / 2) ^ 2 - Real.sin (θ / 2) ^ 2 = Real.cos θ := by
    have h := Real.cos_two_mul' (θ / 2); rw [hθ] at h; exact h.symm
  have hsin : 2 * Real.cos (θ / 2) * Real.sin (θ / 2) = Real.sin θ := by
    have h := Real.sin_two_mul (θ / 2); rw [hθ] at h; rw [h]; ring
  have hone : Real.cos (θ / 2) ^ 2 + Real.sin (θ / 2) ^ 2 = 1 := Real.cos_sq_add_sin_sq _
  rw [matrixAction_011584, rotationAboutSecondAxis, hcos, hsin, hone]


private lemma exists_cos_sin_eq {x y : ℝ} (h : x ^ 2 + y ^ 2 = 1) :
    ∃ θ : ℝ, Real.cos θ = x ∧ Real.sin θ = y := by
  set z : ℂ := (x : ℂ) + (y : ℂ) * Complex.I with hz_def
  have hns : Complex.normSq z = 1 := by rw [hz_def, Complex.normSq_add_mul_I, h]
  have hnorm : ‖z‖ = 1 := by rw [Complex.norm_def, hns, Real.sqrt_one]
  have hz0 : z ≠ 0 := by
    intro h0; rw [h0] at hnorm; simp at hnorm
  have hre : z.re = x := by rw [hz_def]; simp
  have him : z.im = y := by rw [hz_def]; simp
  refine ⟨Complex.arg z, ?_, ?_⟩
  · rw [Complex.cos_arg hz0, hre, hnorm, div_one]
  · rw [Complex.sin_arg, him, hnorm, div_one]


private lemma sq_add_sq_eq_zero {a b : ℝ} (h : a ^ 2 + b ^ 2 = 0) : a = 0 ∧ b = 0 :=
  ⟨sq_eq_zero_iff.mp (le_antisymm (by nlinarith [sq_nonneg b]) (sq_nonneg a)),
   sq_eq_zero_iff.mp (le_antisymm (by nlinarith [sq_nonneg a]) (sq_nonneg b))⟩

set_option maxHeartbeats 1000000 in











/-- A membership statement for the displayed set, submodule, or subgroup. -/
theorem membershipCharacterization_011588 (R : Matrix (Fin 3) (Fin 3) ℝ)
    (hR : R ∈ Matrix.specialOrthogonalGroup (Fin 3) ℝ) :
    ∃ α β γ : ℝ, R = rotationAboutThirdAxis α * rotationAboutSecondAxis β * rotationAboutThirdAxis γ := by
  
  rw [mem_specialOrthogonalGroup_iff] at hR
  obtain ⟨hOrthMem, hdet⟩ := hR
  have hRRt : R * Rᵀ = 1 := by have h := hOrthMem; rwa [mem_orthogonalGroup_iff] at h
  have hRtR : Rᵀ * R = 1 := by have h := hOrthMem; rwa [mem_orthogonalGroup_iff'] at h
  
  have hadj : Rᵀ = adjugate R := by
    calc Rᵀ = Rᵀ * (R * adjugate R) := by rw [mul_adjugate, hdet, one_smul, mul_one]
      _ = Rᵀ * R * adjugate R := by rw [Matrix.mul_assoc]
      _ = adjugate R := by rw [hRtR, Matrix.one_mul]
  rw [adjugate_fin_three] at hadj
  have hC00 : R 0 0 = R 1 1 * R 2 2 - R 1 2 * R 2 1 := by
    have h := congrFun (congrFun hadj 0) 0; simpa [Matrix.transpose_apply] using h
  have hC01 : R 0 1 = -(R 1 0 * R 2 2) + R 1 2 * R 2 0 := by
    have h := congrFun (congrFun hadj 1) 0; simpa [Matrix.transpose_apply] using h
  have hC02 : R 0 2 = R 1 0 * R 2 1 - R 1 1 * R 2 0 := by
    have h := congrFun (congrFun hadj 2) 0; simpa [Matrix.transpose_apply] using h
  have hC12 : R 1 2 = -(R 0 0 * R 2 1) + R 0 1 * R 2 0 := by
    have h := congrFun (congrFun hadj 2) 1; simpa [Matrix.transpose_apply] using h
  
  have hO02 : R 0 0 * R 2 0 + R 0 1 * R 2 1 + R 0 2 * R 2 2 = 0 := by
    have h := congrFun (congrFun hRRt 0) 2
    simpa [mul_apply, Fin.sum_univ_three, Matrix.transpose_apply, Matrix.one_apply] using h
  have hO12 : R 1 0 * R 2 0 + R 1 1 * R 2 1 + R 1 2 * R 2 2 = 0 := by
    have h := congrFun (congrFun hRRt 1) 2
    simpa [mul_apply, Fin.sum_univ_three, Matrix.transpose_apply, Matrix.one_apply] using h
  have hcol2 : R 0 2 ^ 2 + R 1 2 ^ 2 + R 2 2 ^ 2 = 1 := by
    have h := congrFun (congrFun hRtR 2) 2
    simp only [mul_apply, Fin.sum_univ_three, Matrix.transpose_apply, Matrix.one_apply_eq] at h
    linear_combination h
  have hrow2 : R 2 0 ^ 2 + R 2 1 ^ 2 + R 2 2 ^ 2 = 1 := by
    have h := congrFun (congrFun hRRt 2) 2
    simp only [mul_apply, Fin.sum_univ_three, Matrix.transpose_apply, Matrix.one_apply_eq] at h
    linear_combination h
  have hcol0 : R 0 0 ^ 2 + R 1 0 ^ 2 + R 2 0 ^ 2 = 1 := by
    have h := congrFun (congrFun hRtR 0) 0
    simp only [mul_apply, Fin.sum_univ_three, Matrix.transpose_apply, Matrix.one_apply_eq] at h
    linear_combination h
  have hrow0 : R 0 0 ^ 2 + R 0 1 ^ 2 + R 0 2 ^ 2 = 1 := by
    have h := congrFun (congrFun hRRt 0) 0
    simp only [mul_apply, Fin.sum_univ_three, Matrix.transpose_apply, Matrix.one_apply_eq] at h
    linear_combination h
  
  have key00 : R 0 0 * (R 2 0 ^ 2 + R 2 1 ^ 2) = -(R 0 2 * R 2 2 * R 2 0) - R 1 2 * R 2 1 := by
    linear_combination R 2 0 * hO02 + R 2 1 * hC12
  have key01 : R 0 1 * (R 2 0 ^ 2 + R 2 1 ^ 2) = R 1 2 * R 2 0 - R 0 2 * R 2 1 * R 2 2 := by
    linear_combination R 2 1 * hO02 - R 2 0 * hC12
  have key10 : R 1 0 * (R 2 0 ^ 2 + R 2 1 ^ 2) = R 0 2 * R 2 1 - R 1 2 * R 2 0 * R 2 2 := by
    linear_combination R 2 0 * hO12 - R 2 1 * hC02
  have key11 : R 1 1 * (R 2 0 ^ 2 + R 2 1 ^ 2) = -(R 0 2 * R 2 0) - R 1 2 * R 2 1 * R 2 2 := by
    linear_combination R 2 1 * hO12 + R 2 0 * hC02
  
  have hb1 : -1 ≤ R 2 2 := by
    nlinarith [hcol2, sq_nonneg (R 0 2), sq_nonneg (R 1 2), sq_nonneg (R 2 2 + 1)]
  have hb2 : R 2 2 ≤ 1 := by
    nlinarith [hcol2, sq_nonneg (R 0 2), sq_nonneg (R 1 2), sq_nonneg (R 2 2 - 1)]
  set β : ℝ := Real.arccos (R 2 2) with hβ_def
  have hcb : Real.cos β = R 2 2 := by rw [hβ_def]; exact Real.cos_arccos hb1 hb2
  have hsb2 : Real.sin β ^ 2 = 1 - R 2 2 ^ 2 := by
    have h := Real.sin_sq_add_cos_sq β; rw [hcb] at h; linarith
  rcases eq_or_ne (Real.sin β) 0 with hs0 | hsne
  · 
    have h22sq : R 2 2 ^ 2 = 1 := by
      have : Real.sin β ^ 2 = 0 := by rw [hs0]; ring
      linarith [hsb2]
    obtain ⟨hz02, hz12⟩ :=
      sq_add_sq_eq_zero (show R 0 2 ^ 2 + R 1 2 ^ 2 = 0 by linarith [hcol2, h22sq])
    obtain ⟨hz20, hz21⟩ :=
      sq_add_sq_eq_zero (show R 2 0 ^ 2 + R 2 1 ^ 2 = 0 by linarith [hrow2, h22sq])
    have h22 : R 2 2 = 1 ∨ R 2 2 = -1 := by
      have h := h22sq; rw [pow_two] at h; exact mul_self_eq_one_iff.mp h
    rcases h22 with h22 | h22
    · 
      have hcol0' : R 0 0 ^ 2 + R 1 0 ^ 2 = 1 := by
        have h := hcol0; rw [hz20] at h; simpa using h
      obtain ⟨α, hca, hsa⟩ := exists_cos_sin_eq hcol0'
      have e11 : R 0 0 = R 1 1 := by have h := hC00; rw [h22, hz12, hz21] at h; linear_combination h
      have e01 : R 0 1 = -R 1 0 := by have h := hC01; rw [h22, hz20] at h; linear_combination h
      refine ⟨α, β, 0, ?_⟩
      ext i j
      fin_cases i <;> fin_cases j <;>
        simp only [rotationAboutThirdAxis, rotationAboutSecondAxis, mul_apply, Fin.sum_univ_three] <;>
        simp <;>
        (try simp only [hca, hsa, hcb, hs0, h22, hz02, hz12, hz20, hz21,
          Real.cos_zero])
      all_goals
        first
          | linear_combination e01
          | linear_combination -e01
          | linear_combination e11
          | linear_combination -e11
          | linear_combination (0 : ℝ)
    · 
      have hrow0' : R 0 0 ^ 2 + R 0 1 ^ 2 = 1 := by
        have h := hrow0; rw [hz02] at h; simpa using h
      obtain ⟨α, hca, hsa⟩ :=
        exists_cos_sin_eq (show (-R 0 0) ^ 2 + (-R 0 1) ^ 2 = 1 by linear_combination hrow0')
      have e11 : R 1 1 = -R 0 0 := by
        have h := hC00; rw [h22, hz12, hz21] at h; linear_combination h
      have e01 : R 0 1 = R 1 0 := by have h := hC01; rw [h22, hz20] at h; linear_combination h
      refine ⟨α, β, 0, ?_⟩
      ext i j
      fin_cases i <;> fin_cases j <;>
        simp only [rotationAboutThirdAxis, rotationAboutSecondAxis, mul_apply, Fin.sum_univ_three] <;>
        simp <;>
        (try simp only [hca, hsa, hcb, hs0, h22, hz02, hz12, hz20, hz21,
          Real.cos_zero])
      all_goals
        first
          | linear_combination e01
          | linear_combination -e01
          | linear_combination e11
          | linear_combination -e11
          | linear_combination (0 : ℝ)
  · 
    have hsb2col : Real.sin β ^ 2 = R 0 2 ^ 2 + R 1 2 ^ 2 := by rw [hsb2]; linarith [hcol2]
    have hsb2row : Real.sin β ^ 2 = R 2 0 ^ 2 + R 2 1 ^ 2 := by rw [hsb2]; linarith [hrow2]
    have hunitα : (R 0 2 / Real.sin β) ^ 2 + (R 1 2 / Real.sin β) ^ 2 = 1 := by
      field_simp
      first | linear_combination hsb2col | linear_combination -hsb2col
    have hunitγ : (-(R 2 0) / Real.sin β) ^ 2 + (R 2 1 / Real.sin β) ^ 2 = 1 := by
      field_simp
      first | linear_combination hsb2row | linear_combination -hsb2row
    obtain ⟨α, hca, hsa⟩ := exists_cos_sin_eq hunitα
    obtain ⟨γ, hcg, hsg⟩ := exists_cos_sin_eq hunitγ
    refine ⟨α, β, γ, ?_⟩
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp only [rotationAboutThirdAxis, rotationAboutSecondAxis, mul_apply, Fin.sum_univ_three] <;>
      simp <;>
      (try simp only [hca, hsa, hcb, hcg, hsg]) <;>
      (try field_simp)
    all_goals
      first
        | linear_combination key00 + R 0 0 * hsb2row
        | linear_combination key01 + R 0 1 * hsb2row
        | linear_combination key10 + R 1 0 * hsb2row
        | linear_combination key11 + R 1 1 * hsb2row








/-- Surjectivity of the map displayed in the formal statement. -/
@[source_ref "Chapter4/Problem4.12.7" (role := supporting)]
theorem surjective_011572 : Function.Surjective unitQuaternionToRotation := by
  intro R
  obtain ⟨α, β, γ, hR⟩ := membershipCharacterization_011588 (R : Matrix (Fin 3) (Fin 3) ℝ) R.2
  set qz1 : ℍ[ℝ] := ⟨Real.cos (α / 2), 0, 0, Real.sin (α / 2)⟩ with hqz1
  set qy : ℍ[ℝ] := ⟨Real.cos (β / 2), 0, Real.sin (β / 2), 0⟩ with hqy
  set qz2 : ℍ[ℝ] := ⟨Real.cos (γ / 2), 0, 0, Real.sin (γ / 2)⟩ with hqz2
  have hnz1 : Quaternion.normSq qz1 = 1 := by
    rw [hqz1, Quaternion.normSq_def']; simpa using Real.cos_sq_add_sin_sq (α / 2)
  have hny : Quaternion.normSq qy = 1 := by
    rw [hqy, Quaternion.normSq_def']; simpa using Real.cos_sq_add_sin_sq (β / 2)
  have hnz2 : Quaternion.normSq qz2 = 1 := by
    rw [hqz2, Quaternion.normSq_def']; simpa using Real.cos_sq_add_sin_sq (γ / 2)
  set q : ℍ[ℝ] := qz1 * qy * qz2 with hq
  have hnq : Quaternion.normSq q = 1 := by
    rw [hq, quaternionNorm_011503, quaternionNorm_011503, hnz1, hny, hnz2]; ring
  refine ⟨⟨q, quaternionNorm_011502.mpr hnq⟩, ?_⟩
  apply Subtype.ext
  rw [membershipCharacterization_011571]
  change quaternionRotationMatrix q = (R : Matrix (Fin 3) (Fin 3) ℝ)
  rw [hq, valueFormula_011579, valueFormula_011579, hqz1, hqy, hqz2, valueFormula_011587, valueFormula_011585,
    valueFormula_011587]
  exact hR.symm

end PartF



/-- Auxiliary result whose proposition is not displayed in the packet. -/
@[source_ref "Chapter4/Problem4.12.7" (role := supporting)]
theorem Auxiliary011486 :
    ∃ h : Matrix.specialUnitaryGroup (Fin 2) ℂ →*
        Matrix.specialOrthogonalGroup (Fin 3) ℝ,
      Function.Surjective h ∧
      ∀ A : Matrix.specialUnitaryGroup (Fin 2) ℂ,
        A ∈ h.ker ↔
          ((A : Matrix (Fin 2) (Fin 2) ℂ) = 1 ∨
           (A : Matrix (Fin 2) (Fin 2) ℂ) = -1) := by
  
  let e : unitary ℍ[ℝ] ≃* Matrix.specialUnitaryGroup (Fin 2) ℂ :=
    MulEquiv.ofBijective unitQuaternionToSpecialUnitary ⟨injective_011546, surjective_011547⟩
  
  refine ⟨unitQuaternionToRotation.comp e.symm.toMonoidHom, ?_, ?_⟩
  · 
    intro M
    obtain ⟨q, hq⟩ := surjective_011572 M
    refine ⟨e q, ?_⟩
    simp only [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, MulEquiv.symm_apply_apply]
    exact hq
  · 
    intro A
    have hnorm : Quaternion.normSq ((e.symm A : unitary ℍ[ℝ]) : ℍ[ℝ]) = 1 :=
      quaternionNorm_011502.mp (e.symm A).2
    have hAq : (A : Matrix (Fin 2) (Fin 2) ℂ) = quaternionToMatrix ((e.symm A : unitary ℍ[ℝ]) : ℍ[ℝ]) := by
      have h1 : unitQuaternionToSpecialUnitary (e.symm A) = A := e.apply_symm_apply A
      calc (A : Matrix (Fin 2) (Fin 2) ℂ)
            = ((unitQuaternionToSpecialUnitary (e.symm A) : Matrix.specialUnitaryGroup (Fin 2) ℂ) :
                Matrix (Fin 2) (Fin 2) ℂ) := by rw [h1]
        _ = quaternionToMatrix ((e.symm A : unitary ℍ[ℝ]) : ℍ[ℝ]) := rfl
    have hker : A ∈ (unitQuaternionToRotation.comp e.symm.toMonoidHom).ker ↔
        quaternionRotationMatrix ((e.symm A : unitary ℍ[ℝ]) : ℍ[ℝ]) = 1 := by
      rw [MonoidHom.mem_ker]
      simp only [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, Subtype.ext_iff, membershipCharacterization_011571,
        Submonoid.coe_one]
    rw [hker, Auxiliary011577 _ hnorm, hAq]
    constructor
    · rintro (h | h)
      · left; rw [h, valueFormula_011558]
      · right; rw [h, Auxiliary011557]
    · rintro (h | h)
      · left; exact injective_011555 (by rw [valueFormula_011558]; exact h)
      · right; exact injective_011555 (by rw [Auxiliary011557]; exact h)




















section PartB


private def e0 : Fin 2 → ℂ := ![1, 0]

private lemma e0_ne_zero : e0 ≠ 0 := by
  intro h
  have h0 := congrFun h 0
  simp [e0] at h0


/-- The matrix-valued construction specified by the displayed formal signature. -/
noncomputable def specialUnitaryEndomorphism (A : Matrix.specialUnitaryGroup (Fin 2) ℂ) :
    Module.End ℝ (Fin 2 → ℂ) :=
  (Matrix.mulVecLin (A : Matrix (Fin 2) (Fin 2) ℂ)).restrictScalars ℝ

/-- A matrix identity for the displayed action or transformation. -/
@[simp] lemma matrixAction_011603 (A : Matrix.specialUnitaryGroup (Fin 2) ℂ) (v : Fin 2 → ℂ) :
    specialUnitaryEndomorphism A v = (A : Matrix (Fin 2) (Fin 2) ℂ).mulVec v := by
  simp [specialUnitaryEndomorphism]





/-- The construction specified by the displayed formal type. -/
@[source_ref "Chapter4/Problem4.12.7" (role := supporting)]
noncomputable def equivariantEndomorphismAlgebra : Subalgebra ℝ (Module.End ℝ (Fin 2 → ℂ)) :=
  Subalgebra.centralizer ℝ (Set.range specialUnitaryEndomorphism)

/-- A matrix identity for the displayed action or transformation. -/
@[source_ref "Chapter4/Problem4.12.7" (role := primary)]
lemma matrixAction_011500 {f : Module.End ℝ (Fin 2 → ℂ)} :
    f ∈ equivariantEndomorphismAlgebra ↔
      ∀ (A : Matrix.specialUnitaryGroup (Fin 2) ℂ) (v : Fin 2 → ℂ),
        f ((A : Matrix (Fin 2) (Fin 2) ℂ).mulVec v)
          = (A : Matrix (Fin 2) (Fin 2) ℂ).mulVec (f v) := by
  rw [equivariantEndomorphismAlgebra, Subalgebra.mem_centralizer_iff, Set.forall_mem_range]
  simp only [DFunLike.ext_iff, Module.End.mul_apply, matrixAction_011603]
  exact ⟨fun h A v => (h A v).symm, fun h A v => (h A v).symm⟩


/-- A matrix identity for the displayed action or transformation. -/
lemma matrixAction_011478 {f : Module.End ℝ (Fin 2 → ℂ)} (hf : f ∈ equivariantEndomorphismAlgebra)
    (A : Matrix.specialUnitaryGroup (Fin 2) ℂ) (v : Fin 2 → ℂ) (hv : v ∈ LinearMap.ker f) :
    (A : Matrix (Fin 2) (Fin 2) ℂ).mulVec v ∈ LinearMap.ker f := by
  rw [LinearMap.mem_ker] at hv ⊢
  rw [(matrixAction_011500.mp hf) A v, hv, Matrix.mulVec_zero]


/-- A membership statement for the displayed set, submodule, or subgroup. -/
lemma membershipCharacterization_011479 {f : Module.End ℝ (Fin 2 → ℂ)} (hf : f ∈ equivariantEndomorphismAlgebra)
    (h0 : f e0 = 0) : f = 0 := by
  rcases matrixAction_011564 (LinearMap.ker f)
      (fun A v hv => matrixAction_011478 hf A v hv) with h | h
  · exfalso
    have hmem : e0 ∈ LinearMap.ker f := LinearMap.mem_ker.mpr h0
    rw [h, Submodule.mem_bot] at hmem
    exact e0_ne_zero hmem
  · exact LinearMap.ker_eq_top.mp h





/-- A membership statement for the displayed set, submodule, or subgroup. -/
@[source_ref "Chapter4/Problem4.12.7" (role := primary)]
theorem membershipCharacterization_011477 (x : equivariantEndomorphismAlgebra) (hx : x ≠ 0) : IsUnit x := by
  set f : Module.End ℝ (Fin 2 → ℂ) := (x : Module.End ℝ (Fin 2 → ℂ)) with hfdef
  have hf : f ∈ equivariantEndomorphismAlgebra := x.2
  have hf0 : f ≠ 0 := by
    intro h
    apply hx
    apply Subtype.ext
    rw [ZeroMemClass.coe_zero, ← hfdef]
    exact h
  obtain ⟨w, hw⟩ := DFunLike.ne_iff.mp hf0
  have hw0 : f w ≠ 0 := by simpa using hw
  have hinj : Function.Injective f := by
    rw [← LinearMap.ker_eq_bot]
    rcases matrixAction_011564 (LinearMap.ker f)
        (fun A v hv => matrixAction_011478 hf A v hv) with h | h
    · exact h
    · exfalso
      have : w ∈ LinearMap.ker f := h.symm ▸ Submodule.mem_top
      exact hw0 (LinearMap.mem_ker.mp this)
  have hsurj : Function.Surjective f := by
    rw [← LinearMap.range_eq_top]
    have hinv : ∀ (A : Matrix.specialUnitaryGroup (Fin 2) ℂ) (v : Fin 2 → ℂ),
        v ∈ LinearMap.range f →
          (A : Matrix (Fin 2) (Fin 2) ℂ).mulVec v ∈ LinearMap.range f := by
      intro A v hv
      obtain ⟨u, rfl⟩ := LinearMap.mem_range.mp hv
      exact LinearMap.mem_range.mpr ⟨(A : Matrix (Fin 2) (Fin 2) ℂ).mulVec u,
        (matrixAction_011500.mp hf) A u⟩
    rcases matrixAction_011564 (LinearMap.range f) hinv with h | h
    · exfalso
      have hmem : f w ∈ LinearMap.range f := LinearMap.mem_range.mpr ⟨w, rfl⟩
      rw [h, Submodule.mem_bot] at hmem
      exact hw0 hmem
    · exact h
  let e := LinearEquiv.ofBijective f ⟨hinj, hsurj⟩
  let g : Module.End ℝ (Fin 2 → ℂ) := e.symm.toLinearMap
  have hg : g ∈ equivariantEndomorphismAlgebra := by
    rw [matrixAction_011500]
    intro A v
    apply hinj
    rw [(matrixAction_011500.mp hf) A (g v)]
    rw [show f (g ((A : Matrix (Fin 2) (Fin 2) ℂ).mulVec v))
          = (A : Matrix (Fin 2) (Fin 2) ℂ).mulVec v from e.apply_symm_apply _,
        show f (g v) = v from e.apply_symm_apply v]
  refine ⟨⟨x, ⟨g, hg⟩, ?_, ?_⟩, rfl⟩
  · apply Subtype.ext
    change f * g = 1
    refine LinearMap.ext fun v => ?_
    exact e.apply_symm_apply v
  · apply Subtype.ext
    change g * f = 1
    refine LinearMap.ext fun v => ?_
    exact e.symm_apply_apply v




private lemma star_realSmul (r : ℝ) (z : ℂ) : star (r • z) = r • star z := by
  rw [Complex.real_smul, Complex.real_smul, Complex.star_def, map_mul, Complex.conj_ofReal]


/-- The construction specified by the displayed formal type. -/
noncomputable def complexStructureEndomorphism : Module.End ℝ (Fin 2 → ℂ) where
  toFun v := Complex.I • v
  map_add' _ _ := smul_add _ _ _
  map_smul' r v := smul_comm Complex.I r v

/-- The equality displayed in the formal statement. -/
@[simp] lemma valueFormula_011493 (v : Fin 2 → ℂ) : complexStructureEndomorphism v = Complex.I • v := rfl

/-- A membership statement for the displayed set, submodule, or subgroup. -/
lemma membershipCharacterization_011494 : complexStructureEndomorphism ∈ equivariantEndomorphismAlgebra := by
  rw [matrixAction_011500]
  intro A v
  simp only [valueFormula_011493, Matrix.mulVec_smul]


/-- The matrix-valued construction specified by the displayed formal signature. -/
noncomputable def quaternionComplexMatrix : Matrix (Fin 2) (Fin 2) ℂ := !![0, -1; 1, 0]


/-- The construction specified by the displayed formal type. -/
noncomputable def conjugateMatrixEndomorphism : Module.End ℝ (Fin 2 → ℂ) where
  toFun v := quaternionComplexMatrix.mulVec (star v)
  map_add' _ _ := by rw [star_add, Matrix.mulVec_add]
  map_smul' r v := by
    change quaternionComplexMatrix.mulVec (star (r • v)) = r • quaternionComplexMatrix.mulVec (star v)
    have hs : star (r • v) = r • star v := by
      funext i
      simp only [Pi.star_apply, Pi.smul_apply]
      exact star_realSmul r (v i)
    rw [hs, Matrix.mulVec_smul]

/-- A matrix identity for the displayed action or transformation. -/
@[simp] lemma matrixAction_011498 (v : Fin 2 → ℂ) : conjugateMatrixEndomorphism v = quaternionComplexMatrix.mulVec (star v) := rfl



/-- A membership statement for the displayed set, submodule, or subgroup. -/
lemma membershipCharacterization_011605 (A : Matrix.specialUnitaryGroup (Fin 2) ℂ) :
    (A : Matrix (Fin 2) (Fin 2) ℂ) 1 1 = star ((A : Matrix (Fin 2) (Fin 2) ℂ) 0 0) ∧
    (A : Matrix (Fin 2) (Fin 2) ℂ) 1 0 = -star ((A : Matrix (Fin 2) (Fin 2) ℂ) 0 1) := by
  set M : Matrix (Fin 2) (Fin 2) ℂ := (A : Matrix (Fin 2) (Fin 2) ℂ) with hM
  have hmem := A.2
  rw [Matrix.mem_specialUnitaryGroup_iff] at hmem
  obtain ⟨hu, hdet⟩ := hmem
  have huc : Mᴴ * M = 1 := by
    rw [← Matrix.star_eq_conjTranspose]; exact Matrix.mem_unitaryGroup_iff'.mp hu
  have hinvL : M⁻¹ = Mᴴ := Matrix.inv_eq_left_inv huc
  have hinvR : M⁻¹ = M.adjugate := by
    apply Matrix.inv_eq_right_inv; rw [Matrix.mul_adjugate, hdet, one_smul]
  have hadj : Mᴴ = M.adjugate := by rw [← hinvL, hinvR]
  rw [Matrix.adjugate_fin_two] at hadj
  refine ⟨?_, ?_⟩
  · have h := congrFun (congrFun hadj 0) 0
    simp only [Matrix.conjTranspose_apply, Matrix.cons_val_zero, Matrix.of_apply,
      Matrix.cons_val', Matrix.empty_val', Matrix.cons_val_fin_one] at h
    exact h.symm
  · have h := congrFun (congrFun hadj 1) 0
    simp only [Matrix.conjTranspose_apply, Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.of_apply, Matrix.cons_val', Matrix.empty_val', Matrix.cons_val_fin_one] at h
    rw [h]; ring


private lemma star_mulVec_eq (A : Matrix (Fin 2) (Fin 2) ℂ) (v : Fin 2 → ℂ) :
    star (A.mulVec v) = (A.map (starRingEnd ℂ)).mulVec (star v) := by
  funext i
  simp only [Pi.star_apply, Matrix.mulVec, dotProduct, Fin.sum_univ_two, Matrix.map_apply,
    star_add, star_mul', starRingEnd_apply]


/-- A membership statement for the displayed set, submodule, or subgroup. -/
lemma membershipCharacterization_011604 (A : Matrix.specialUnitaryGroup (Fin 2) ℂ) :
    quaternionComplexMatrix * (A : Matrix (Fin 2) (Fin 2) ℂ).map (starRingEnd ℂ)
      = (A : Matrix (Fin 2) (Fin 2) ℂ) * quaternionComplexMatrix := by
  obtain ⟨h11, h10⟩ := membershipCharacterization_011605 A
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp only [quaternionComplexMatrix, Matrix.mul_apply, Fin.sum_univ_two, Matrix.map_apply, Matrix.cons_val_zero,
      Matrix.cons_val_one, Matrix.of_apply, Matrix.cons_val', Matrix.empty_val',
      Matrix.cons_val_fin_one, Fin.isValue, starRingEnd_apply] <;>
    simp [h11, h10]

/-- A membership statement for the displayed set, submodule, or subgroup. -/
lemma membershipCharacterization_011499 : conjugateMatrixEndomorphism ∈ equivariantEndomorphismAlgebra := by
  rw [matrixAction_011500]
  intro A v
  change quaternionComplexMatrix.mulVec (star ((A : Matrix (Fin 2) (Fin 2) ℂ).mulVec v))
      = (A : Matrix (Fin 2) (Fin 2) ℂ).mulVec (quaternionComplexMatrix.mulVec (star v))
  rw [star_mulVec_eq, Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, membershipCharacterization_011604]


/-- The linear map specified by the displayed formal signature. -/
noncomputable def evaluationLinearMap : equivariantEndomorphismAlgebra →ₗ[ℝ] (Fin 2 → ℂ) where
  toFun x := (x : Module.End ℝ (Fin 2 → ℂ)) e0
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

/-- A membership statement for the displayed set, submodule, or subgroup. -/
@[simp] lemma membershipCharacterization_011483 (x : equivariantEndomorphismAlgebra) : evaluationLinearMap x = (x : Module.End ℝ (Fin 2 → ℂ)) e0 := rfl

/-- Injectivity of the map displayed in the formal statement. -/
lemma injective_011484 : Function.Injective evaluationLinearMap := by
  intro x y hxy
  have h0 : ((x : Module.End ℝ (Fin 2 → ℂ)) - y) e0 = 0 := by
    rw [LinearMap.sub_apply, ← membershipCharacterization_011483 x, ← membershipCharacterization_011483 y, hxy, sub_self]
  have hz : (x : Module.End ℝ (Fin 2 → ℂ)) - y = 0 :=
    membershipCharacterization_011479 (sub_mem x.2 y.2) h0
  exact Subtype.ext (sub_eq_zero.mp hz)

/-- Surjectivity of the map displayed in the formal statement. -/
lemma surjective_011485 : Function.Surjective evaluationLinearMap := by
  intro w
  refine ⟨(w 0).re • (1 : equivariantEndomorphismAlgebra) + (w 0).im • ⟨complexStructureEndomorphism, membershipCharacterization_011494⟩
      + (w 1).re • ⟨conjugateMatrixEndomorphism, membershipCharacterization_011499⟩
      + (w 1).im • ⟨complexStructureEndomorphism * conjugateMatrixEndomorphism, mul_mem membershipCharacterization_011494 membershipCharacterization_011499⟩, ?_⟩
  have ev1 : evaluationLinearMap (1 : equivariantEndomorphismAlgebra) = ![1, 0] := rfl
  have evI : evaluationLinearMap ⟨complexStructureEndomorphism, membershipCharacterization_011494⟩ = ![Complex.I, 0] := by
    funext i; fin_cases i <;> simp [membershipCharacterization_011483, valueFormula_011493, e0]
  have evJ : evaluationLinearMap ⟨conjugateMatrixEndomorphism, membershipCharacterization_011499⟩ = ![0, 1] := by
    funext i; fin_cases i <;>
      simp [membershipCharacterization_011483, matrixAction_011498, e0, quaternionComplexMatrix, Matrix.mulVec, dotProduct, Fin.sum_univ_two]
  have evK : evaluationLinearMap ⟨complexStructureEndomorphism * conjugateMatrixEndomorphism, mul_mem membershipCharacterization_011494 membershipCharacterization_011499⟩ = ![0, Complex.I] := by
    funext i; fin_cases i <;>
      simp [membershipCharacterization_011483, Module.End.mul_apply, valueFormula_011493, matrixAction_011498, e0, quaternionComplexMatrix,
        dotProduct, Fin.sum_univ_two]
  rw [map_add, map_add, map_add, map_smul, map_smul, map_smul, map_smul, ev1, evI, evJ, evK]
  funext i
  fin_cases i <;> simp [Complex.real_smul, Complex.re_add_im]



/-- A cardinality or dimension identity for the displayed finite object. -/
@[source_ref "Chapter4/Problem4.12.7" (role := primary)]
theorem cardinalityFormula_011488 : Module.finrank ℝ equivariantEndomorphismAlgebra = 4 := by
  have hbij : Function.Bijective evaluationLinearMap := ⟨injective_011484, surjective_011485⟩
  rw [(LinearEquiv.ofBijective evaluationLinearMap hbij).finrank_eq]
  simp [Module.finrank_pi_fintype, Complex.finrank_real_complex]

end PartB

end RepresentationTheory.QuaternionRotationMaps
