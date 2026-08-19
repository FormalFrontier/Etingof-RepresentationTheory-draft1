/-
Copyright (c) 2026 mathlib-initiative. All rights reserved.
Released under Apache 2.0 license as described in the file LICENCE.
Authors: mathlib-initiative
-/

import Mathlib
import RepresentationTheory.Alignment.Attribute

/-! # Matrix conjugation actions -/


open Matrix

noncomputable section

namespace RepresentationTheory.MatrixConjugationActions


/-- Defines a submonoid of three-by-three real matrices. -/
abbrev realMatrixSubmonoid : Submonoid (Matrix (Fin 3) (Fin 3) ℝ) := specialOrthogonalGroup (Fin 3) ℝ


/-- Defines an auxiliary type. -/
abbrev realMatrixSpace : Type := Matrix (Fin 3) (Fin 3) ℝ


/-- Defines a real representation of the displayed matrix submonoid. -/
def realConjugationRepresentation : Representation ℝ realMatrixSubmonoid realMatrixSpace where
  toFun A := (LinearMap.mulLeft ℝ (A : realMatrixSpace)).comp
    (LinearMap.mulRight ℝ (star (A : realMatrixSpace)))
  map_one' := by
    ext M
    simp
  map_mul' A B := by
    ext M
    simp only [Submonoid.coe_mul, star_mul, LinearMap.comp_apply, LinearMap.mulLeft_apply,
      LinearMap.mulRight_apply, Module.End.mul_apply]
    simp [mul_assoc]

/-- Computes the displayed real representation action. -/
@[simp]
theorem realConjugationRepresentation_apply (A : realMatrixSubmonoid) (M : realMatrixSpace) :
    realConjugationRepresentation A M = (A : realMatrixSpace) * M * star (A : realMatrixSpace) := by
  simp [realConjugationRepresentation, mul_assoc]


/-- Defines an auxiliary real submodule of the displayed matrix space. -/
def auxiliaryRealSubmoduleA : Submodule ℝ realMatrixSpace := Submodule.span ℝ {(1 : realMatrixSpace)}


/-- Defines an auxiliary real submodule of the displayed matrix space. -/
def auxiliaryRealSubmoduleB : Submodule ℝ realMatrixSpace where
  carrier := {M | Mᵀ = -M}
  add_mem' {a b} ha hb := by
    simp only [Set.mem_setOf_eq] at ha hb ⊢; rw [transpose_add, ha, hb]; abel
  zero_mem' := by simp
  smul_mem' c a ha := by
    simp only [Set.mem_setOf_eq] at ha ⊢; rw [transpose_smul, ha, smul_neg]


/-- Defines an auxiliary real submodule of the displayed matrix space. -/
def auxiliaryRealSubmoduleC : Submodule ℝ realMatrixSpace where
  carrier := {M | Mᵀ = M}
  add_mem' {a b} ha hb := by
    simp only [Set.mem_setOf_eq] at ha hb ⊢; rw [transpose_add, ha, hb]
  zero_mem' := by simp
  smul_mem' c a ha := by
    simp only [Set.mem_setOf_eq] at ha ⊢; rw [transpose_smul, ha]


/-- Defines an auxiliary real submodule of the displayed matrix space. -/
def auxiliaryRealSubmoduleD : Submodule ℝ realMatrixSpace where
  carrier := {M | Mᵀ = M ∧ M.trace = 0}
  add_mem' {a b} ha hb := by
    simp only [Set.mem_setOf_eq] at ha hb ⊢
    exact ⟨by rw [transpose_add, ha.1, hb.1], by rw [trace_add, ha.2, hb.2, add_zero]⟩
  zero_mem' := by simp only [Set.mem_setOf_eq]; exact ⟨by simp, by simp⟩
  smul_mem' c a ha := by
    simp only [Set.mem_setOf_eq] at ha ⊢
    exact ⟨by rw [transpose_smul, ha.1], by rw [trace_smul, ha.2, smul_zero]⟩

/-- States containment between the two displayed real submodules. -/
theorem auxiliaryRealSubmoduleA_le_auxiliaryRealSubmodule : auxiliaryRealSubmoduleA ≤ auxiliaryRealSubmoduleC := by
  intro M hM
  rw [auxiliaryRealSubmoduleA, Submodule.mem_span_singleton] at hM
  obtain ⟨c, rfl⟩ := hM
  change (c • (1 : realMatrixSpace))ᵀ = c • 1
  rw [transpose_smul, transpose_one]

/-- States containment between the two displayed real submodules. -/
theorem auxiliaryRealSubmoduleD_le_auxiliaryRealSubmoduleC : auxiliaryRealSubmoduleD ≤ auxiliaryRealSubmoduleC := fun _ hM => hM.1


/-- An auxiliary result about the displayed matrix action. -/
theorem auxiliaryActionResultD (A : realMatrixSubmonoid) : star (A : realMatrixSpace) = (A : realMatrixSpace)ᵀ := by
  ext i j
  simp


/-- Each displayed submonoid element multiplied by its star is the identity. -/
theorem mul_star_eq_one (A : realMatrixSubmonoid) : (A : realMatrixSpace) * star (A : realMatrixSpace) = 1 :=
  mem_unitaryGroup_iff.mp (mem_specialOrthogonalGroup_iff.mp A.2).1


/-- An auxiliary result about the displayed matrix action. -/
theorem auxiliaryActionResultE (A : realMatrixSubmonoid) : star (A : realMatrixSpace) * (A : realMatrixSpace) = 1 :=
  mem_unitaryGroup_iff'.mp (mem_specialOrthogonalGroup_iff.mp A.2).1


/-- The displayed action preserves each listed real submodule. -/
theorem realConjugation_preserves_selected_submodules (S : Submodule ℝ realMatrixSpace)
    (hS : S = auxiliaryRealSubmoduleA ∨ S = auxiliaryRealSubmoduleB ∨ S = auxiliaryRealSubmoduleD)
    (A : realMatrixSubmonoid) (M : realMatrixSpace) (hM : M ∈ S) : realConjugationRepresentation A M ∈ S := by
  have hAstar : (A : realMatrixSpace) * star (A : realMatrixSpace) = 1 := mul_star_eq_one A
  have hstarA : star (A : realMatrixSpace) * (A : realMatrixSpace) = 1 := auxiliaryActionResultE A
  have hstarT : star (A : realMatrixSpace) = (A : realMatrixSpace)ᵀ := auxiliaryActionResultD A
  rw [realConjugationRepresentation_apply]
  rcases hS with h | h | h
  ·
    subst h
    rw [auxiliaryRealSubmoduleA, Submodule.mem_span_singleton] at hM ⊢
    obtain ⟨c, rfl⟩ := hM
    exact ⟨c, by rw [Matrix.mul_smul, Matrix.smul_mul, mul_one, hAstar]⟩
  ·
    subst h
    simp only [auxiliaryRealSubmoduleB, Submodule.mem_mk, AddSubmonoid.mem_mk, AddSubsemigroup.mem_mk,
      Set.mem_setOf_eq] at hM ⊢
    rw [hstarT]
    simp only [Matrix.transpose_mul, Matrix.transpose_transpose, hM, Matrix.mul_neg,
      Matrix.neg_mul, mul_assoc]
  ·
    subst h
    simp only [auxiliaryRealSubmoduleD, Submodule.mem_mk, AddSubmonoid.mem_mk, AddSubsemigroup.mem_mk,
      Set.mem_setOf_eq] at hM ⊢
    obtain ⟨hsym, htr⟩ := hM
    refine ⟨?_, ?_⟩
    · rw [hstarT]
      simp only [Matrix.transpose_mul, Matrix.transpose_transpose, hsym, mul_assoc]
    · rw [Matrix.trace_mul_comm, ← mul_assoc, hstarA, Matrix.one_mul, htr]

/-- An auxiliary result about the displayed real matrix space. -/
theorem auxiliaryRealMatrixResultD {M : realMatrixSpace} : M ∈ auxiliaryRealSubmoduleB ↔ Mᵀ = -M := Iff.rfl
/-- An auxiliary result about the displayed real matrix space. -/
theorem auxiliaryRealMatrixResultE {M : realMatrixSpace} : M ∈ auxiliaryRealSubmoduleC ↔ Mᵀ = M := Iff.rfl
/-- An auxiliary result about the displayed real matrix space. -/
theorem auxiliaryRealMatrixResultF {M : realMatrixSpace} :
    M ∈ auxiliaryRealSubmoduleD ↔ Mᵀ = M ∧ M.trace = 0 := Iff.rfl


/-- An auxiliary result about the displayed real matrix space. -/
theorem auxiliaryRealMatrixResultK {M : realMatrixSpace} (hM : M ∈ auxiliaryRealSubmoduleB) : M.trace = 0 := by
  have h : Mᵀ = -M := hM
  have h2 := congr_arg Matrix.trace h
  rw [Matrix.trace_transpose, Matrix.trace_neg] at h2
  linarith


/-- A scalar multiple of the identity with zero trace has zero scalar. -/
theorem smul_one_eq_zero_of_trace_eq_zero {c : ℝ} (h : (c • (1 : realMatrixSpace)).trace = 0) : c = 0 := by
  rw [Matrix.trace_smul, Matrix.trace_one, Fintype.card_fin, Nat.cast_ofNat, smul_eq_mul] at h
  rcases mul_eq_zero.mp h with h' | h'
  · exact h'
  · norm_num at h'


/-- An auxiliary internal direct-sum assertion. -/
@[source_ref "Chapter4/Problem4.12.11" (role := supporting)]
theorem auxiliaryInternalDirectSum :
    DirectSum.IsInternal ![auxiliaryRealSubmoduleA, auxiliaryRealSubmoduleB, auxiliaryRealSubmoduleD] := by
  refine DirectSum.isInternal_submodule_of_iSupIndep_of_iSup_eq_top ?_ ?_
  · rw [iSupIndep_fin_three]
    refine ⟨?_, ?_, ?_⟩
    ·
      change Disjoint auxiliaryRealSubmoduleA (auxiliaryRealSubmoduleB ⊔ auxiliaryRealSubmoduleD)
      rw [Submodule.disjoint_def]
      intro M hMs hMst
      rw [auxiliaryRealSubmoduleA, Submodule.mem_span_singleton] at hMs
      obtain ⟨c, rfl⟩ := hMs
      rw [Submodule.mem_sup] at hMst
      obtain ⟨y, hy, z, hz, hyz⟩ := hMst
      have htr : (c • (1 : realMatrixSpace)).trace = 0 := by
        rw [← hyz, Matrix.trace_add, auxiliaryRealMatrixResultK hy,
          (auxiliaryRealMatrixResultF.mp hz).2, add_zero]
      rw [smul_one_eq_zero_of_trace_eq_zero htr, zero_smul]
    ·
      change Disjoint auxiliaryRealSubmoduleB (auxiliaryRealSubmoduleD ⊔ auxiliaryRealSubmoduleA)
      rw [Submodule.disjoint_def]
      intro M hM hMts
      have hMskew : Mᵀ = -M := hM
      rw [Submodule.mem_sup] at hMts
      obtain ⟨z, hz, a, ha, hza⟩ := hMts
      have hsym : Mᵀ = M := by
        rw [← hza, Matrix.transpose_add, (auxiliaryRealMatrixResultF.mp hz).1,
          auxiliaryRealMatrixResultE.mp (auxiliaryRealSubmoduleA_le_auxiliaryRealSubmodule ha)]
      have hMM : M = -M := hsym.symm.trans hMskew
      have h2 : (2 : ℝ) • M = 0 := by rw [two_smul ℝ]; nth_rewrite 2 [hMM]; rw [add_neg_cancel]
      exact (smul_eq_zero.mp h2).resolve_left (by norm_num)
    ·

      change Disjoint auxiliaryRealSubmoduleD (auxiliaryRealSubmoduleA ⊔ auxiliaryRealSubmoduleB)
      rw [Submodule.disjoint_def]
      intro M hM hMsk
      obtain ⟨hMsym, hMtr⟩ := auxiliaryRealMatrixResultF.mp hM
      rw [Submodule.mem_sup] at hMsk
      obtain ⟨a, ha, y, hy, hay⟩ := hMsk
      have haa : aᵀ = a := auxiliaryRealMatrixResultE.mp (auxiliaryRealSubmoduleA_le_auxiliaryRealSubmodule ha)
      have hya : yᵀ = -y := hy
      have hMt : Mᵀ = a - y := by
        rw [← hay, Matrix.transpose_add, haa, hya, sub_eq_add_neg]
      have key : a - y = a + y := by rw [← hMt, hMsym, hay]
      have hyy : -y = y := by
        rw [sub_eq_add_neg] at key; exact add_right_injective a key
      have hy0 : y = 0 := by
        have h2 : (2 : ℝ) • y = 0 := by rw [two_smul ℝ]; nth_rewrite 2 [← hyy]; rw [add_neg_cancel]
        exact (smul_eq_zero.mp h2).resolve_left (by norm_num)
      have hMa : M = a := by rw [← hay, hy0, add_zero]
      rw [auxiliaryRealSubmoduleA, Submodule.mem_span_singleton] at ha
      obtain ⟨c, rfl⟩ := ha
      rw [hMa] at hMtr ⊢
      rw [smul_one_eq_zero_of_trace_eq_zero hMtr, zero_smul]
  ·
    rw [eq_top_iff]
    rintro M -
    have hdecomp : M ∈ auxiliaryRealSubmoduleA ⊔ auxiliaryRealSubmoduleB ⊔ auxiliaryRealSubmoduleD := by
      rw [Submodule.mem_sup]
      refine ⟨(M.trace / 3) • (1 : realMatrixSpace) + (1 / 2 : ℝ) • (M - Mᵀ), ?_,
          (1 / 2 : ℝ) • (M + Mᵀ) - (M.trace / 3) • (1 : realMatrixSpace), ?_, by module⟩
      · rw [Submodule.mem_sup]
        refine ⟨(M.trace / 3) • (1 : realMatrixSpace), ?_, (1 / 2 : ℝ) • (M - Mᵀ), ?_, rfl⟩
        · rw [auxiliaryRealSubmoduleA]; exact Submodule.smul_mem _ _ (Submodule.mem_span_singleton_self _)
        · rw [auxiliaryRealMatrixResultD, Matrix.transpose_smul, Matrix.transpose_sub,
            Matrix.transpose_transpose]
          module
      · rw [auxiliaryRealMatrixResultF]
        refine ⟨?_, ?_⟩
        · simp only [Matrix.transpose_sub, Matrix.transpose_smul, Matrix.transpose_add,
            Matrix.transpose_transpose, Matrix.transpose_one]
          module
        · simp only [Matrix.trace_sub, Matrix.trace_smul, Matrix.trace_add,
            Matrix.trace_transpose, Matrix.trace_one, Fintype.card_fin, Nat.cast_ofNat,
            smul_eq_mul]
          ring
    refine SetLike.le_def.mp ?_ hdecomp
    exact sup_le
      (sup_le (le_iSup ![auxiliaryRealSubmoduleA, auxiliaryRealSubmoduleB, auxiliaryRealSubmoduleD] 0)
        (le_iSup ![auxiliaryRealSubmoduleA, auxiliaryRealSubmoduleB, auxiliaryRealSubmoduleD] 1))
      (le_iSup ![auxiliaryRealSubmoduleA, auxiliaryRealSubmoduleB, auxiliaryRealSubmoduleD] 2)


/-- An auxiliary conjunction of displayed propositions. -/
@[source_ref "Chapter4/Problem4.12.11" (role := primary)]
theorem auxiliaryConjunction :
    auxiliaryRealSubmoduleA ⊔ auxiliaryRealSubmoduleD = auxiliaryRealSubmoduleC ∧ auxiliaryRealSubmoduleA ⊓ auxiliaryRealSubmoduleD = ⊥ := by
  refine ⟨le_antisymm (sup_le auxiliaryRealSubmoduleA_le_auxiliaryRealSubmodule auxiliaryRealSubmoduleD_le_auxiliaryRealSubmoduleC) ?_, ?_⟩
  ·
    intro M hM
    have hMsym : Mᵀ = M := hM
    rw [Submodule.mem_sup]
    refine ⟨(M.trace / 3) • (1 : realMatrixSpace), ?_, M - (M.trace / 3) • (1 : realMatrixSpace), ?_, by module⟩
    · rw [auxiliaryRealSubmoduleA]; exact Submodule.smul_mem _ _ (Submodule.mem_span_singleton_self _)
    · rw [auxiliaryRealMatrixResultF]
      refine ⟨?_, ?_⟩
      · rw [Matrix.transpose_sub, hMsym, Matrix.transpose_smul, Matrix.transpose_one]
      · simp only [Matrix.trace_sub, Matrix.trace_smul, Matrix.trace_one, Fintype.card_fin,
          Nat.cast_ofNat, smul_eq_mul]
        ring
  ·
    rw [Submodule.eq_bot_iff]
    intro M hM
    rw [Submodule.mem_inf] at hM
    obtain ⟨hs, htsym⟩ := hM
    rw [auxiliaryRealSubmoduleA, Submodule.mem_span_singleton] at hs
    obtain ⟨c, rfl⟩ := hs
    rw [smul_one_eq_zero_of_trace_eq_zero (auxiliaryRealMatrixResultF.mp htsym).2, zero_smul]

/-- Computes the dimension of the displayed real submodule. -/
@[source_ref "Chapter4/Problem4.12.11" (role := supporting)]
theorem auxiliaryRealSubmoduleA_finrank : Module.finrank ℝ auxiliaryRealSubmoduleA = 1 := by
  rw [auxiliaryRealSubmoduleA, finrank_span_singleton (one_ne_zero)]

/-- Computes the dimension of the displayed real submodule. -/
@[source_ref "Chapter4/Problem4.12.11" (role := supporting)]
theorem auxiliaryRealSubmoduleB_finrank : Module.finrank ℝ auxiliaryRealSubmoduleB = 3 := by
  classical
  set v : Fin 3 → realMatrixSpace :=
    ![!![(0 : ℝ), 1, 0; -1, 0, 0; 0, 0, (0 : ℝ)],
      !![(0 : ℝ), 0, 1; 0, 0, 0; -1, 0, (0 : ℝ)],
      !![(0 : ℝ), 0, 0; 0, 0, 1; 0, -1, (0 : ℝ)]] with hv
  have hindep : LinearIndependent ℝ v := by
    rw [Fintype.linearIndependent_iff]
    intro g hg
    have e01 := congr_fun (congr_fun hg 0) 1
    have e02 := congr_fun (congr_fun hg 0) 2
    have e12 := congr_fun (congr_fun hg 1) 2
    simp [hv, Fin.sum_univ_three, Matrix.add_apply] at e01 e02 e12
    intro i; fin_cases i <;> simp_all
  have hspan : auxiliaryRealSubmoduleB = Submodule.span ℝ (Set.range v) := by
    apply le_antisymm
    · intro M hM
      have hM' : Mᵀ = -M := hM
      have hd : ∀ i, M i i = 0 := fun i => by
        have h := congr_fun (congr_fun hM' i) i
        simp only [Matrix.transpose_apply, Matrix.neg_apply] at h; linarith
      have ho : ∀ i j, M j i = -M i j := fun i j => by
        have h := congr_fun (congr_fun hM' i) j
        simpa only [Matrix.transpose_apply, Matrix.neg_apply] using h
      have key : M = M 0 1 • v 0 + M 0 2 • v 1 + M 1 2 • v 2 := by
        ext i j
        fin_cases i <;> fin_cases j <;>
          simp [hv, Matrix.add_apply] <;>
          linarith [hd 0, hd 1, hd 2, ho 0 1, ho 0 2, ho 1 2]
      rw [key]
      exact Submodule.add_mem _
        (Submodule.add_mem _
          (Submodule.smul_mem _ _ (Submodule.subset_span ⟨0, rfl⟩))
          (Submodule.smul_mem _ _ (Submodule.subset_span ⟨1, rfl⟩)))
        (Submodule.smul_mem _ _ (Submodule.subset_span ⟨2, rfl⟩))
    · rw [Submodule.span_le]
      rintro _ ⟨i, rfl⟩
      change (v i)ᵀ = -(v i)
      fin_cases i <;> · ext a b; fin_cases a <;> fin_cases b <;> simp [hv]
  rw [hspan, finrank_span_eq_card hindep, Fintype.card_fin]

/-- The displayed real submodule has dimension five. -/
@[source_ref "Chapter4/Problem4.12.11" (role := supporting)]
theorem auxiliaryRealSubmoduleD_finrank : Module.finrank ℝ auxiliaryRealSubmoduleD = 5 := by
  classical
  set v : Fin 5 → realMatrixSpace :=
    ![!![(0 : ℝ), 1, 0; 1, 0, 0; 0, 0, (0 : ℝ)],
      !![(0 : ℝ), 0, 1; 0, 0, 0; 1, 0, (0 : ℝ)],
      !![(0 : ℝ), 0, 0; 0, 0, 1; 0, 1, (0 : ℝ)],
      !![(1 : ℝ), 0, 0; 0, -1, 0; 0, 0, (0 : ℝ)],
      !![(0 : ℝ), 0, 0; 0, 1, 0; 0, 0, (-1 : ℝ)]] with hv
  have hindep : LinearIndependent ℝ v := by
    rw [Fintype.linearIndependent_iff]
    intro g hg
    have e01 := congr_fun (congr_fun hg 0) 1
    have e02 := congr_fun (congr_fun hg 0) 2
    have e12 := congr_fun (congr_fun hg 1) 2
    have e00 := congr_fun (congr_fun hg 0) 0
    have e11 := congr_fun (congr_fun hg 1) 1
    simp [hv, Fin.sum_univ_five, Matrix.add_apply] at e01 e02 e12 e00 e11
    intro i; fin_cases i <;> simp_all
  have hspan : auxiliaryRealSubmoduleD = Submodule.span ℝ (Set.range v) := by
    apply le_antisymm
    · intro M hM
      obtain ⟨hsym, htr⟩ := hM
      have hs : ∀ i j, M j i = M i j := fun i j => by
        have h := congr_fun (congr_fun hsym i) j
        simpa only [Matrix.transpose_apply] using h
      have htrace : M 2 2 = -M 0 0 - M 1 1 := by
        rw [Matrix.trace_fin_three] at htr; linarith
      have key : M = M 0 1 • v 0 + M 0 2 • v 1 + M 1 2 • v 2 + M 0 0 • v 3
          + (M 0 0 + M 1 1) • v 4 := by
        ext i j
        fin_cases i <;> fin_cases j <;>
          simp [hv, Matrix.add_apply] <;>
          linarith [hs 0 1, hs 0 2, hs 1 2, htrace]
      rw [key]
      refine Submodule.add_mem _ (Submodule.add_mem _ (Submodule.add_mem _
        (Submodule.add_mem _
          (Submodule.smul_mem _ _ (Submodule.subset_span ⟨0, rfl⟩))
          (Submodule.smul_mem _ _ (Submodule.subset_span ⟨1, rfl⟩)))
        (Submodule.smul_mem _ _ (Submodule.subset_span ⟨2, rfl⟩)))
        (Submodule.smul_mem _ _ (Submodule.subset_span ⟨3, rfl⟩)))
        (Submodule.smul_mem _ _ (Submodule.subset_span ⟨4, rfl⟩))
    · rw [Submodule.span_le]
      rintro _ ⟨i, rfl⟩
      refine ⟨?_, ?_⟩
      · show (v i)ᵀ = v i
        fin_cases i <;> · ext a b; fin_cases a <;> fin_cases b <;> simp [hv]
      · show (v i).trace = 0
        fin_cases i <;> simp [hv, Matrix.trace_fin_three]
  rw [hspan, finrank_span_eq_card hindep, Fintype.card_fin]


/-- Defines a real representation on functions over a three-element finite type. -/
def coordinateRepresentation : Representation ℝ realMatrixSubmonoid (Fin 3 → ℝ) where
  toFun A := Matrix.mulVecLin (A : realMatrixSpace)
  map_one' := by rw [Submonoid.coe_one, Matrix.mulVecLin_one]; rfl
  map_mul' A B := by rw [Submonoid.coe_mul, Matrix.mulVecLin_mul]; rfl

/-- Computes the displayed coordinate representation action. -/
@[simp]
theorem coordinateRepresentation_apply (A : realMatrixSubmonoid) (v : Fin 3 → ℝ) : coordinateRepresentation A v = (A : realMatrixSpace) *ᵥ v := rfl


/-- Defines a linear map from three coordinates to the displayed real matrix space. -/
def coordinateLinearMap : (Fin 3 → ℝ) →ₗ[ℝ] realMatrixSpace where
  toFun v := !![0, -v 2, v 1; v 2, 0, -v 0; -v 1, v 0, 0]
  map_add' u v := by ext i j; fin_cases i <;> fin_cases j <;> simp <;> ring
  map_smul' c v := by ext i j; fin_cases i <;> fin_cases j <;> simp

/-- Computes the displayed coordinate linear map. -/
@[simp]
theorem coordinateLinearMap_apply (v : Fin 3 → ℝ) :
    coordinateLinearMap v = !![0, -v 2, v 1; v 2, 0, -v 0; -v 1, v 0, 0] := rfl

/-- The coordinate linear map sends every vector into the displayed real submodule. -/
theorem coordinateLinearMap_mem_auxiliaryRealSubmoduleB (v : Fin 3 → ℝ) : coordinateLinearMap v ∈ auxiliaryRealSubmoduleB := by
  change (coordinateLinearMap v)ᵀ = -coordinateLinearMap v
  ext i j; fin_cases i <;> fin_cases j <;> simp


/-- An auxiliary result involving a real matrix and three coordinates. -/
theorem auxiliaryCoordinateResult (A : realMatrixSpace) (v : Fin 3 → ℝ) :
    Aᵀ * coordinateLinearMap (A *ᵥ v) * A = A.det • coordinateLinearMap v := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_apply, Fin.sum_univ_three, Matrix.mulVec, dotProduct,
      Matrix.det_fin_three] <;> ring


/-- Relates the coordinate linear map to the displayed action. -/
theorem coordinateLinearMap_action (A : realMatrixSubmonoid) (v : Fin 3 → ℝ) :
    coordinateLinearMap ((A : realMatrixSpace) *ᵥ v) = realConjugationRepresentation A (coordinateLinearMap v) := by
  have hdet : (A : realMatrixSpace).det = 1 := (mem_specialOrthogonalGroup_iff.mp A.2).2
  have hAAt : (A : realMatrixSpace) * (A : realMatrixSpace)ᵀ = 1 := by
    simpa [auxiliaryActionResultD] using mul_star_eq_one A
  have key := auxiliaryCoordinateResult (A : realMatrixSpace) v
  rw [hdet, one_smul] at key
  calc coordinateLinearMap ((A : realMatrixSpace) *ᵥ v)
      = (A : realMatrixSpace) * (A : realMatrixSpace)ᵀ * coordinateLinearMap ((A : realMatrixSpace) *ᵥ v) * ((A : realMatrixSpace) * (A : realMatrixSpace)ᵀ) := by
        rw [hAAt, one_mul, mul_one]
    _ = (A : realMatrixSpace) * ((A : realMatrixSpace)ᵀ * coordinateLinearMap ((A : realMatrixSpace) *ᵥ v) * (A : realMatrixSpace)) * (A : realMatrixSpace)ᵀ := by
        simp only [Matrix.mul_assoc]
    _ = (A : realMatrixSpace) * coordinateLinearMap v * (A : realMatrixSpace)ᵀ := by rw [key]
    _ = realConjugationRepresentation A (coordinateLinearMap v) := by rw [realConjugationRepresentation_apply, auxiliaryActionResultD]


/-- Defines a linear map from the displayed real matrix space to three coordinates. -/
def matrixToCoordinateLinearMap : realMatrixSpace →ₗ[ℝ] (Fin 3 → ℝ) where
  toFun M := ![M 2 1, M 0 2, M 1 0]
  map_add' M N := by ext i; fin_cases i <;> simp
  map_smul' c M := by ext i; fin_cases i <;> simp

/-- An auxiliary result about the displayed real matrix space. -/
@[simp]
theorem auxiliaryRealMatrixResultP (M : realMatrixSpace) : matrixToCoordinateLinearMap M = ![M 2 1, M 0 2, M 1 0] := rfl

/-- An auxiliary result involving three coordinates. -/
@[simp]
theorem auxiliaryCoordinateResultB (v : Fin 3 → ℝ) : matrixToCoordinateLinearMap (coordinateLinearMap v) = v := by
  ext i; fin_cases i <;> simp

/-- An auxiliary result about the displayed real matrix space. -/
theorem auxiliaryMatrixResultB {M : realMatrixSpace} (hM : M ∈ auxiliaryRealSubmoduleB) : coordinateLinearMap (matrixToCoordinateLinearMap M) = M := by
  have hM' : Mᵀ = -M := hM
  have hd : ∀ i, M i i = 0 := fun i => by
    have h := congr_fun (congr_fun hM' i) i
    simp only [Matrix.transpose_apply, Matrix.neg_apply] at h; linarith
  have ho : ∀ i j, M j i = -M i j := fun i j => by
    have h := congr_fun (congr_fun hM' i) j
    simpa only [Matrix.transpose_apply, Matrix.neg_apply] using h
  ext i j
  fin_cases i <;> fin_cases j <;> simp <;>
    linarith [hd 0, hd 1, hd 2, ho 0 1, ho 0 2, ho 1 2]


/-- Defines an auxiliary real representation of the displayed matrix submonoid. -/
def auxiliaryRealRepresentation : Representation ℝ realMatrixSubmonoid auxiliaryRealSubmoduleB where
  toFun A := (realConjugationRepresentation A).restrict
    (fun M hM => realConjugation_preserves_selected_submodules auxiliaryRealSubmoduleB (Or.inr (Or.inl rfl)) A M hM)
  map_one' := by ext M; simp
  map_mul' A B := by ext M; simp

/-- An auxiliary result about the displayed matrix action. -/
@[simp]
theorem auxiliaryActionResultC (A : realMatrixSubmonoid) (M : auxiliaryRealSubmoduleB) :
    (auxiliaryRealRepresentation A M : realMatrixSpace) = realConjugationRepresentation A (M : realMatrixSpace) := rfl


/-- Defines a linear equivalence with functions on a three-element finite type. -/
def coordinateLinearEquiv : (Fin 3 → ℝ) ≃ₗ[ℝ] auxiliaryRealSubmoduleB where
  toFun v := ⟨coordinateLinearMap v, coordinateLinearMap_mem_auxiliaryRealSubmoduleB v⟩
  map_add' u v := by ext : 1; exact coordinateLinearMap.map_add u v
  map_smul' c v := by ext : 1; exact coordinateLinearMap.map_smul c v
  invFun M := matrixToCoordinateLinearMap (M : realMatrixSpace)
  left_inv v := auxiliaryCoordinateResultB v
  right_inv M := by ext : 1; exact auxiliaryMatrixResultB M.2

/-- Computes the displayed coordinate equivalence. -/
@[simp]
theorem coordinateLinearEquiv_apply (v : Fin 3 → ℝ) : (coordinateLinearEquiv v : realMatrixSpace) = coordinateLinearMap v := rfl


/-- Relates the coordinate equivalence to the displayed matrix action. -/
theorem coordinateLinearEquiv_action (A : realMatrixSubmonoid) (v : Fin 3 → ℝ) :
    coordinateLinearEquiv (coordinateRepresentation A v) = auxiliaryRealRepresentation A (coordinateLinearEquiv v) := by
  ext : 1
  rw [coordinateLinearEquiv_apply, auxiliaryActionResultC, coordinateLinearEquiv_apply, coordinateRepresentation_apply, coordinateLinearMap_action]


/-- Defines a family of three elements of the displayed real matrix space. -/
def threeMatrixFamily : Fin 3 → realMatrixSpace :=
  ![!![(0 : ℝ), 1, 0; -1, 0, 0; 0, 0, (0 : ℝ)],
    !![(0 : ℝ), 0, 1; 0, 0, 0; -1, 0, (0 : ℝ)],
    !![(0 : ℝ), 0, 0; 0, 0, 1; 0, -1, (0 : ℝ)]]

/-- Each element of the displayed family belongs to the specified submodule. -/
theorem threeMatrixFamily_mem_auxiliarySubmodule (i : Fin 3) : threeMatrixFamily i ∈ auxiliaryRealSubmoduleB := by
  fin_cases i <;> · change (_ : realMatrixSpace)ᵀ = -_; ext a b; fin_cases a <;> fin_cases b <;> simp [threeMatrixFamily]


/-- An auxiliary result about the displayed real matrix space. -/
theorem auxiliaryRealMatrixResultJ (M : realMatrixSpace) (hM : Mᵀ = -M) :
    M = (M 0 1) • threeMatrixFamily 0 + (M 0 2) • threeMatrixFamily 1 + (M 1 2) • threeMatrixFamily 2 := by
  have hd : ∀ i, M i i = 0 := fun i => by
    have h := congr_fun (congr_fun hM i) i
    simp only [Matrix.transpose_apply, Matrix.neg_apply] at h; linarith
  have ho : ∀ i j, M j i = -M i j := fun i j => by
    have h := congr_fun (congr_fun hM i) j
    simpa only [Matrix.transpose_apply, Matrix.neg_apply] using h
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [threeMatrixFamily, Matrix.add_apply] <;>
    linarith [hd 0, hd 1, hd 2, ho 0 1, ho 0 2, ho 1 2]


/-- Defines an auxiliary element subtype of the displayed matrix submonoid. -/
def matrixSubmonoidElementC : realMatrixSubmonoid := ⟨!![(-1:ℝ), 0, 0; 0, -1, 0; 0, 0, 1], by
  rw [mem_specialOrthogonalGroup_iff]
  refine ⟨?_, ?_⟩
  · rw [mem_orthogonalGroup_iff]; ext i j
    fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_three]
  · simp [Matrix.det_fin_three]⟩


/-- Defines an auxiliary element subtype of the displayed matrix submonoid. -/
def matrixSubmonoidElementB : realMatrixSubmonoid := ⟨!![(-1:ℝ), 0, 0; 0, 1, 0; 0, 0, -1], by
  rw [mem_specialOrthogonalGroup_iff]
  refine ⟨?_, ?_⟩
  · rw [mem_orthogonalGroup_iff]; ext i j
    fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_three]
  · simp [Matrix.det_fin_three]⟩


/-- Defines an auxiliary element subtype of the displayed matrix submonoid. -/
def matrixSubmonoidElementA : realMatrixSubmonoid := ⟨!![(1:ℝ), 0, 0; 0, -1, 0; 0, 0, -1], by
  rw [mem_specialOrthogonalGroup_iff]
  refine ⟨?_, ?_⟩
  · rw [mem_orthogonalGroup_iff]; ext i j
    fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_three]
  · simp [Matrix.det_fin_three]⟩


/-- Defines an auxiliary element subtype of the displayed matrix submonoid. -/
def matrixSubmonoidElementD : realMatrixSubmonoid := ⟨!![(0:ℝ), 0, 1; 1, 0, 0; 0, 1, 0], by
  rw [mem_specialOrthogonalGroup_iff]
  refine ⟨?_, ?_⟩
  · rw [mem_orthogonalGroup_iff]; ext i j
    fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_three]
  · simp [Matrix.det_fin_three]⟩


private theorem conjRep_Dz0 : realConjugationRepresentation matrixSubmonoidElementC (threeMatrixFamily 0) = threeMatrixFamily 0 := by
  ext i j; fin_cases i <;> fin_cases j <;>
    simp [realConjugationRepresentation_apply, matrixSubmonoidElementC, threeMatrixFamily, Matrix.mul_apply, Fin.sum_univ_three]
private theorem conjRep_Dz1 : realConjugationRepresentation matrixSubmonoidElementC (threeMatrixFamily 1) = -threeMatrixFamily 1 := by
  ext i j; fin_cases i <;> fin_cases j <;>
    simp [realConjugationRepresentation_apply, matrixSubmonoidElementC, threeMatrixFamily, Matrix.mul_apply, Fin.sum_univ_three]
private theorem conjRep_Dz2 : realConjugationRepresentation matrixSubmonoidElementC (threeMatrixFamily 2) = -threeMatrixFamily 2 := by
  ext i j; fin_cases i <;> fin_cases j <;>
    simp [realConjugationRepresentation_apply, matrixSubmonoidElementC, threeMatrixFamily, Matrix.mul_apply, Fin.sum_univ_three]
private theorem conjRep_Dy0 : realConjugationRepresentation matrixSubmonoidElementB (threeMatrixFamily 0) = -threeMatrixFamily 0 := by
  ext i j; fin_cases i <;> fin_cases j <;>
    simp [realConjugationRepresentation_apply, matrixSubmonoidElementB, threeMatrixFamily, Matrix.mul_apply, Fin.sum_univ_three]
private theorem conjRep_Dy1 : realConjugationRepresentation matrixSubmonoidElementB (threeMatrixFamily 1) = threeMatrixFamily 1 := by
  ext i j; fin_cases i <;> fin_cases j <;>
    simp [realConjugationRepresentation_apply, matrixSubmonoidElementB, threeMatrixFamily, Matrix.mul_apply, Fin.sum_univ_three]
private theorem conjRep_Dy2 : realConjugationRepresentation matrixSubmonoidElementB (threeMatrixFamily 2) = -threeMatrixFamily 2 := by
  ext i j; fin_cases i <;> fin_cases j <;>
    simp [realConjugationRepresentation_apply, matrixSubmonoidElementB, threeMatrixFamily, Matrix.mul_apply, Fin.sum_univ_three]
private theorem conjRep_Dx0 : realConjugationRepresentation matrixSubmonoidElementA (threeMatrixFamily 0) = -threeMatrixFamily 0 := by
  ext i j; fin_cases i <;> fin_cases j <;>
    simp [realConjugationRepresentation_apply, matrixSubmonoidElementA, threeMatrixFamily, Matrix.mul_apply, Fin.sum_univ_three]
private theorem conjRep_Dx1 : realConjugationRepresentation matrixSubmonoidElementA (threeMatrixFamily 1) = -threeMatrixFamily 1 := by
  ext i j; fin_cases i <;> fin_cases j <;>
    simp [realConjugationRepresentation_apply, matrixSubmonoidElementA, threeMatrixFamily, Matrix.mul_apply, Fin.sum_univ_three]
private theorem conjRep_Dx2 : realConjugationRepresentation matrixSubmonoidElementA (threeMatrixFamily 2) = threeMatrixFamily 2 := by
  ext i j; fin_cases i <;> fin_cases j <;>
    simp [realConjugationRepresentation_apply, matrixSubmonoidElementA, threeMatrixFamily, Matrix.mul_apply, Fin.sum_univ_three]
private theorem conjRep_Pc0 : realConjugationRepresentation matrixSubmonoidElementD (threeMatrixFamily 0) = threeMatrixFamily 2 := by
  ext i j; fin_cases i <;> fin_cases j <;>
    simp [realConjugationRepresentation_apply, matrixSubmonoidElementD, threeMatrixFamily, Matrix.mul_apply, Fin.sum_univ_three]
private theorem conjRep_Pc1 : realConjugationRepresentation matrixSubmonoidElementD (threeMatrixFamily 1) = -threeMatrixFamily 0 := by
  ext i j; fin_cases i <;> fin_cases j <;>
    simp [realConjugationRepresentation_apply, matrixSubmonoidElementD, threeMatrixFamily, Matrix.mul_apply, Fin.sum_univ_three]
private theorem conjRep_Pc2 : realConjugationRepresentation matrixSubmonoidElementD (threeMatrixFamily 2) = -threeMatrixFamily 1 := by
  ext i j; fin_cases i <;> fin_cases j <;>
    simp [realConjugationRepresentation_apply, matrixSubmonoidElementD, threeMatrixFamily, Matrix.mul_apply, Fin.sum_univ_three]


/-- Defines a family of five elements of the displayed real matrix space. -/
def fiveMatrixFamily : Fin 5 → realMatrixSpace :=
  ![!![(0 : ℝ), 1, 0; 1, 0, 0; 0, 0, (0 : ℝ)],
    !![(0 : ℝ), 0, 1; 0, 0, 0; 1, 0, (0 : ℝ)],
    !![(0 : ℝ), 0, 0; 0, 0, 1; 0, 1, (0 : ℝ)],
    !![(1 : ℝ), 0, 0; 0, -1, 0; 0, 0, (0 : ℝ)],
    !![(0 : ℝ), 0, 0; 0, 1, 0; 0, 0, (-1 : ℝ)]]

/-- Each element of the displayed family belongs to the specified submodule. -/
theorem fiveMatrixFamily_mem_auxiliarySubmodule (i : Fin 5) : fiveMatrixFamily i ∈ auxiliaryRealSubmoduleD := by
  rw [auxiliaryRealMatrixResultF]
  refine ⟨?_, ?_⟩
  · fin_cases i <;> · ext a b; fin_cases a <;> fin_cases b <;> simp [fiveMatrixFamily]
  · fin_cases i <;> simp [fiveMatrixFamily, Matrix.trace_fin_three]


/-- An auxiliary result about the displayed real matrix space. -/
theorem auxiliaryRealMatrixResultO (M : realMatrixSpace) (hsym : Mᵀ = M) (htr : M.trace = 0) :
    M = M 0 1 • fiveMatrixFamily 0 + M 0 2 • fiveMatrixFamily 1 + M 1 2 • fiveMatrixFamily 2 + M 0 0 • fiveMatrixFamily 3
      + (M 0 0 + M 1 1) • fiveMatrixFamily 4 := by
  have hs : ∀ i j, M j i = M i j := fun i j => by
    have h := congr_fun (congr_fun hsym i) j
    simpa only [Matrix.transpose_apply] using h
  have htrace : M 2 2 = -M 0 0 - M 1 1 := by
    rw [Matrix.trace_fin_three] at htr; linarith
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [fiveMatrixFamily, Matrix.add_apply] <;>
    linarith [hs 0 1, hs 0 2, hs 1 2, htrace]


/-- Defines an auxiliary real value. -/
noncomputable def auxiliaryRealParameter : ℝ := Real.sqrt 2 / 2

/-- An auxiliary assertion with unavailable formal rendering. -/
theorem auxiliaryMatrixAssertionA : auxiliaryRealParameter * auxiliaryRealParameter = 1 / 2 := by
  rw [auxiliaryRealParameter, div_mul_div_comm, Real.mul_self_sqrt (by norm_num)]; norm_num


/-- Defines an auxiliary element subtype of the displayed matrix submonoid. -/
def matrixSubmonoidElementF : realMatrixSubmonoid := ⟨!![auxiliaryRealParameter, -auxiliaryRealParameter, 0; auxiliaryRealParameter, auxiliaryRealParameter, 0; 0, 0, 1], by
  rw [mem_specialOrthogonalGroup_iff]
  refine ⟨?_, ?_⟩
  · rw [mem_orthogonalGroup_iff]; ext i j
    fin_cases i <;> fin_cases j <;>
      simp [Matrix.mul_apply, Fin.sum_univ_three] <;> nlinarith [auxiliaryMatrixAssertionA]
  · simp [Matrix.det_fin_three]
    nlinarith [auxiliaryMatrixAssertionA]⟩


/-- Defines an auxiliary element subtype of the displayed matrix submonoid. -/
def matrixSubmonoidElementE : realMatrixSubmonoid := ⟨!![auxiliaryRealParameter, 0, auxiliaryRealParameter; 0, 1, 0; -auxiliaryRealParameter, 0, auxiliaryRealParameter], by
  rw [mem_specialOrthogonalGroup_iff]
  refine ⟨?_, ?_⟩
  · rw [mem_orthogonalGroup_iff]; ext i j
    fin_cases i <;> fin_cases j <;>
      simp [Matrix.mul_apply, Fin.sum_univ_three] <;> nlinarith [auxiliaryMatrixAssertionA]
  · simp [Matrix.det_fin_three]
    nlinarith [auxiliaryMatrixAssertionA]⟩


/-- An auxiliary equality concerning the displayed real representation. -/
theorem auxiliaryRealActionValue : realConjugationRepresentation matrixSubmonoidElementF (fiveMatrixFamily 0) = -fiveMatrixFamily 3 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [realConjugationRepresentation_apply, matrixSubmonoidElementF, fiveMatrixFamily, Matrix.mul_apply, Fin.sum_univ_three,
      Matrix.neg_apply] <;> nlinarith [auxiliaryMatrixAssertionA]


private theorem conjRep_Rz45_w3 : realConjugationRepresentation matrixSubmonoidElementF (fiveMatrixFamily 3) = fiveMatrixFamily 0 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [realConjugationRepresentation_apply, matrixSubmonoidElementF, fiveMatrixFamily, Matrix.mul_apply, Fin.sum_univ_three] <;>
    nlinarith [auxiliaryMatrixAssertionA]


private theorem conjRep_Rz45_w4 :
    realConjugationRepresentation matrixSubmonoidElementF (fiveMatrixFamily 4)
      = (-2⁻¹ : ℝ) • fiveMatrixFamily 0 + (2⁻¹ : ℝ) • fiveMatrixFamily 3 + fiveMatrixFamily 4 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [realConjugationRepresentation_apply, matrixSubmonoidElementF, fiveMatrixFamily, Matrix.mul_apply, Fin.sum_univ_three,
      Matrix.add_apply] <;>
    nlinarith [auxiliaryMatrixAssertionA]


private theorem conjRep_Ry45_w3 :
    realConjugationRepresentation matrixSubmonoidElementE (fiveMatrixFamily 3)
      = (-2⁻¹ : ℝ) • fiveMatrixFamily 1 + (2⁻¹ : ℝ) • fiveMatrixFamily 3 + (-2⁻¹ : ℝ) • fiveMatrixFamily 4 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [realConjugationRepresentation_apply, matrixSubmonoidElementE, fiveMatrixFamily, Matrix.mul_apply, Fin.sum_univ_three,
      Matrix.add_apply] <;>
    nlinarith [auxiliaryMatrixAssertionA]


private theorem conjRep_Ry45_w4 :
    realConjugationRepresentation matrixSubmonoidElementE (fiveMatrixFamily 4)
      = (-2⁻¹ : ℝ) • fiveMatrixFamily 1 + (-2⁻¹ : ℝ) • fiveMatrixFamily 3 + (2⁻¹ : ℝ) • fiveMatrixFamily 4 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [realConjugationRepresentation_apply, matrixSubmonoidElementE, fiveMatrixFamily, Matrix.mul_apply, Fin.sum_univ_three,
      Matrix.add_apply] <;>
    nlinarith [auxiliaryMatrixAssertionA]


private theorem conjRep_Pc_w0 : realConjugationRepresentation matrixSubmonoidElementD (fiveMatrixFamily 0) = fiveMatrixFamily 2 := by
  ext i j; fin_cases i <;> fin_cases j <;>
    simp [realConjugationRepresentation_apply, matrixSubmonoidElementD, fiveMatrixFamily, Matrix.mul_apply, Fin.sum_univ_three]
private theorem conjRep_Pc_w1 : realConjugationRepresentation matrixSubmonoidElementD (fiveMatrixFamily 1) = fiveMatrixFamily 0 := by
  ext i j; fin_cases i <;> fin_cases j <;>
    simp [realConjugationRepresentation_apply, matrixSubmonoidElementD, fiveMatrixFamily, Matrix.mul_apply, Fin.sum_univ_three]
private theorem conjRep_Pc_w2 : realConjugationRepresentation matrixSubmonoidElementD (fiveMatrixFamily 2) = fiveMatrixFamily 1 := by
  ext i j; fin_cases i <;> fin_cases j <;>
    simp [realConjugationRepresentation_apply, matrixSubmonoidElementD, fiveMatrixFamily, Matrix.mul_apply, Fin.sum_univ_three]
private theorem conjRep_Pc_w3 : realConjugationRepresentation matrixSubmonoidElementD (fiveMatrixFamily 3) = fiveMatrixFamily 4 := by
  ext i j; fin_cases i <;> fin_cases j <;>
    simp [realConjugationRepresentation_apply, matrixSubmonoidElementD, fiveMatrixFamily, Matrix.mul_apply, Fin.sum_univ_three]


private theorem conjRep_Dx_w0 : realConjugationRepresentation matrixSubmonoidElementA (fiveMatrixFamily 0) = -fiveMatrixFamily 0 := by
  ext i j; fin_cases i <;> fin_cases j <;>
    simp [realConjugationRepresentation_apply, matrixSubmonoidElementA, fiveMatrixFamily, Matrix.mul_apply, Fin.sum_univ_three]
private theorem conjRep_Dx_w1 : realConjugationRepresentation matrixSubmonoidElementA (fiveMatrixFamily 1) = -fiveMatrixFamily 1 := by
  ext i j; fin_cases i <;> fin_cases j <;>
    simp [realConjugationRepresentation_apply, matrixSubmonoidElementA, fiveMatrixFamily, Matrix.mul_apply, Fin.sum_univ_three]
private theorem conjRep_Dx_w2 : realConjugationRepresentation matrixSubmonoidElementA (fiveMatrixFamily 2) = fiveMatrixFamily 2 := by
  ext i j; fin_cases i <;> fin_cases j <;>
    simp [realConjugationRepresentation_apply, matrixSubmonoidElementA, fiveMatrixFamily, Matrix.mul_apply, Fin.sum_univ_three]
private theorem conjRep_Dx_w3 : realConjugationRepresentation matrixSubmonoidElementA (fiveMatrixFamily 3) = fiveMatrixFamily 3 := by
  ext i j; fin_cases i <;> fin_cases j <;>
    simp [realConjugationRepresentation_apply, matrixSubmonoidElementA, fiveMatrixFamily, Matrix.mul_apply, Fin.sum_univ_three]
private theorem conjRep_Dx_w4 : realConjugationRepresentation matrixSubmonoidElementA (fiveMatrixFamily 4) = fiveMatrixFamily 4 := by
  ext i j; fin_cases i <;> fin_cases j <;>
    simp [realConjugationRepresentation_apply, matrixSubmonoidElementA, fiveMatrixFamily, Matrix.mul_apply, Fin.sum_univ_three]
private theorem conjRep_Dy_w0 : realConjugationRepresentation matrixSubmonoidElementB (fiveMatrixFamily 0) = -fiveMatrixFamily 0 := by
  ext i j; fin_cases i <;> fin_cases j <;>
    simp [realConjugationRepresentation_apply, matrixSubmonoidElementB, fiveMatrixFamily, Matrix.mul_apply, Fin.sum_univ_three]
private theorem conjRep_Dy_w1 : realConjugationRepresentation matrixSubmonoidElementB (fiveMatrixFamily 1) = fiveMatrixFamily 1 := by
  ext i j; fin_cases i <;> fin_cases j <;>
    simp [realConjugationRepresentation_apply, matrixSubmonoidElementB, fiveMatrixFamily, Matrix.mul_apply, Fin.sum_univ_three]
private theorem conjRep_Dy_w2 : realConjugationRepresentation matrixSubmonoidElementB (fiveMatrixFamily 2) = -fiveMatrixFamily 2 := by
  ext i j; fin_cases i <;> fin_cases j <;>
    simp [realConjugationRepresentation_apply, matrixSubmonoidElementB, fiveMatrixFamily, Matrix.mul_apply, Fin.sum_univ_three]
private theorem conjRep_Dy_w3 : realConjugationRepresentation matrixSubmonoidElementB (fiveMatrixFamily 3) = fiveMatrixFamily 3 := by
  ext i j; fin_cases i <;> fin_cases j <;>
    simp [realConjugationRepresentation_apply, matrixSubmonoidElementB, fiveMatrixFamily, Matrix.mul_apply, Fin.sum_univ_three]
private theorem conjRep_Dy_w4 : realConjugationRepresentation matrixSubmonoidElementB (fiveMatrixFamily 4) = fiveMatrixFamily 4 := by
  ext i j; fin_cases i <;> fin_cases j <;>
    simp [realConjugationRepresentation_apply, matrixSubmonoidElementB, fiveMatrixFamily, Matrix.mul_apply, Fin.sum_univ_three]
private theorem conjRep_Dz_w0 : realConjugationRepresentation matrixSubmonoidElementC (fiveMatrixFamily 0) = fiveMatrixFamily 0 := by
  ext i j; fin_cases i <;> fin_cases j <;>
    simp [realConjugationRepresentation_apply, matrixSubmonoidElementC, fiveMatrixFamily, Matrix.mul_apply, Fin.sum_univ_three]
private theorem conjRep_Dz_w1 : realConjugationRepresentation matrixSubmonoidElementC (fiveMatrixFamily 1) = -fiveMatrixFamily 1 := by
  ext i j; fin_cases i <;> fin_cases j <;>
    simp [realConjugationRepresentation_apply, matrixSubmonoidElementC, fiveMatrixFamily, Matrix.mul_apply, Fin.sum_univ_three]
private theorem conjRep_Dz_w2 : realConjugationRepresentation matrixSubmonoidElementC (fiveMatrixFamily 2) = -fiveMatrixFamily 2 := by
  ext i j; fin_cases i <;> fin_cases j <;>
    simp [realConjugationRepresentation_apply, matrixSubmonoidElementC, fiveMatrixFamily, Matrix.mul_apply, Fin.sum_univ_three]
private theorem conjRep_Dz_w3 : realConjugationRepresentation matrixSubmonoidElementC (fiveMatrixFamily 3) = fiveMatrixFamily 3 := by
  ext i j; fin_cases i <;> fin_cases j <;>
    simp [realConjugationRepresentation_apply, matrixSubmonoidElementC, fiveMatrixFamily, Matrix.mul_apply, Fin.sum_univ_three]
private theorem conjRep_Dz_w4 : realConjugationRepresentation matrixSubmonoidElementC (fiveMatrixFamily 4) = fiveMatrixFamily 4 := by
  ext i j; fin_cases i <;> fin_cases j <;>
    simp [realConjugationRepresentation_apply, matrixSubmonoidElementC, fiveMatrixFamily, Matrix.mul_apply, Fin.sum_univ_three]


/-- An auxiliary statement about real submodules of the displayed matrix space. -/
@[source_ref "Chapter4/Problem4.12.11" (role := supporting)]
theorem auxiliaryRealSubmoduleClassification (U : Submodule ℝ realMatrixSpace) (hUle : U ≤ auxiliaryRealSubmoduleB)
    (hUinv : ∀ (A : realMatrixSubmonoid), ∀ M ∈ U, realConjugationRepresentation A M ∈ U) :
    U = ⊥ ∨ U = auxiliaryRealSubmoduleB := by
  rcases eq_or_ne U ⊥ with h | h
  · exact Or.inl h
  refine Or.inr (le_antisymm hUle ?_)

  obtain ⟨M, hMU, hMne⟩ := U.ne_bot_iff.mp h
  have hMsk : Mᵀ = -M := auxiliaryRealMatrixResultD.mp (hUle hMU)
  have hMdec : M = (M 0 1) • threeMatrixFamily 0 + (M 0 2) • threeMatrixFamily 1 + (M 1 2) • threeMatrixFamily 2 :=
    auxiliaryRealMatrixResultJ M hMsk
  have hDzM : realConjugationRepresentation matrixSubmonoidElementC M ∈ U := hUinv matrixSubmonoidElementC M hMU
  have hDyM : realConjugationRepresentation matrixSubmonoidElementB M ∈ U := hUinv matrixSubmonoidElementB M hMU
  have hDxM : realConjugationRepresentation matrixSubmonoidElementA M ∈ U := hUinv matrixSubmonoidElementA M hMU

  have hav0 : (M 0 1) • threeMatrixFamily 0 ∈ U := by
    have key : (M 0 1) • threeMatrixFamily 0 = (2⁻¹ : ℝ) • (M + realConjugationRepresentation matrixSubmonoidElementC M) := by
      conv_rhs => rw [hMdec]
      simp only [map_add, map_smul, conjRep_Dz0, conjRep_Dz1, conjRep_Dz2]
      module
    rw [key]; exact U.smul_mem _ (U.add_mem hMU hDzM)
  have hbv1 : (M 0 2) • threeMatrixFamily 1 ∈ U := by
    have key : (M 0 2) • threeMatrixFamily 1 = (2⁻¹ : ℝ) • (M + realConjugationRepresentation matrixSubmonoidElementB M) := by
      conv_rhs => rw [hMdec]
      simp only [map_add, map_smul, conjRep_Dy0, conjRep_Dy1, conjRep_Dy2]
      module
    rw [key]; exact U.smul_mem _ (U.add_mem hMU hDyM)
  have hcv2 : (M 1 2) • threeMatrixFamily 2 ∈ U := by
    have key : (M 1 2) • threeMatrixFamily 2 = (2⁻¹ : ℝ) • (M + realConjugationRepresentation matrixSubmonoidElementA M) := by
      conv_rhs => rw [hMdec]
      simp only [map_add, map_smul, conjRep_Dx0, conjRep_Dx1, conjRep_Dx2]
      module
    rw [key]; exact U.smul_mem _ (U.add_mem hMU hDxM)

  have hav2 : (M 0 1) • threeMatrixFamily 2 ∈ U := by
    have t := hUinv matrixSubmonoidElementD _ hav0; rwa [map_smul, conjRep_Pc0] at t
  have hav1 : (M 0 1) • threeMatrixFamily 1 ∈ U := by
    have t := hUinv matrixSubmonoidElementD _ hav2; rw [map_smul, conjRep_Pc2, smul_neg] at t
    exact neg_mem_iff.mp t
  have hbv0 : (M 0 2) • threeMatrixFamily 0 ∈ U := by
    have t := hUinv matrixSubmonoidElementD _ hbv1; rw [map_smul, conjRep_Pc1, smul_neg] at t
    exact neg_mem_iff.mp t
  have hbv2 : (M 0 2) • threeMatrixFamily 2 ∈ U := by
    have t := hUinv matrixSubmonoidElementD _ hbv0; rwa [map_smul, conjRep_Pc0] at t
  have hcv1 : (M 1 2) • threeMatrixFamily 1 ∈ U := by
    have t := hUinv matrixSubmonoidElementD _ hcv2; rw [map_smul, conjRep_Pc2, smul_neg] at t
    exact neg_mem_iff.mp t
  have hcv0 : (M 1 2) • threeMatrixFamily 0 ∈ U := by
    have t := hUinv matrixSubmonoidElementD _ hcv1; rw [map_smul, conjRep_Pc1, smul_neg] at t
    exact neg_mem_iff.mp t

  have hne3 : M 0 1 ≠ 0 ∨ M 0 2 ≠ 0 ∨ M 1 2 ≠ 0 := by
    by_contra hcon
    push Not at hcon
    exact hMne (by rw [hMdec, hcon.1, hcon.2.1, hcon.2.2]; simp)
  have extract : ∀ w : realMatrixSpace,
      (M 0 1) • w ∈ U → (M 0 2) • w ∈ U → (M 1 2) • w ∈ U → w ∈ U := by
    intro w h1 h2 h3
    rcases hne3 with hh | hh | hh
    · rw [← one_smul ℝ w, ← inv_mul_cancel₀ hh, mul_smul]; exact U.smul_mem _ h1
    · rw [← one_smul ℝ w, ← inv_mul_cancel₀ hh, mul_smul]; exact U.smul_mem _ h2
    · rw [← one_smul ℝ w, ← inv_mul_cancel₀ hh, mul_smul]; exact U.smul_mem _ h3
  have hs0 : threeMatrixFamily 0 ∈ U := extract _ hav0 hbv0 hcv0
  have hs1 : threeMatrixFamily 1 ∈ U := extract _ hav1 hbv1 hcv1
  have hs2 : threeMatrixFamily 2 ∈ U := extract _ hav2 hbv2 hcv2

  intro N hN
  rw [auxiliaryRealMatrixResultJ N (auxiliaryRealMatrixResultD.mp hN)]
  exact U.add_mem (U.add_mem (U.smul_mem _ hs0) (U.smul_mem _ hs1)) (U.smul_mem _ hs2)


/-- An auxiliary statement about real submodules of the displayed matrix space. -/
@[source_ref "Chapter4/Problem4.12.11" (role := supporting)]
theorem auxiliaryRealSubmoduleResult (U : Submodule ℝ realMatrixSpace) (hUle : U ≤ auxiliaryRealSubmoduleD)
    (hUinv : ∀ (A : realMatrixSubmonoid), ∀ M ∈ U, realConjugationRepresentation A M ∈ U) :
    U = ⊥ ∨ U = auxiliaryRealSubmoduleD := by
  rcases eq_or_ne U ⊥ with h | h
  · exact Or.inl h
  refine Or.inr (le_antisymm hUle ?_)

  have hUsym : ∀ N ∈ U, Nᵀ = N := fun N hN => (auxiliaryRealMatrixResultF.mp (hUle hN)).1

  have projA : ∀ N ∈ U, (N 0 1) • fiveMatrixFamily 0 ∈ U := by
    intro N hN
    obtain ⟨hsym, htr⟩ := auxiliaryRealMatrixResultF.mp (hUle hN)
    have key : (N 0 1) • fiveMatrixFamily 0
        = (4⁻¹ : ℝ) • (N - realConjugationRepresentation matrixSubmonoidElementA N - realConjugationRepresentation matrixSubmonoidElementB N + realConjugationRepresentation matrixSubmonoidElementC N) := by
      conv_rhs => rw [auxiliaryRealMatrixResultO N hsym htr]
      simp only [map_add, map_smul, conjRep_Dx_w0, conjRep_Dx_w1, conjRep_Dx_w2, conjRep_Dx_w3,
        conjRep_Dx_w4, conjRep_Dy_w0, conjRep_Dy_w1, conjRep_Dy_w2, conjRep_Dy_w3, conjRep_Dy_w4,
        conjRep_Dz_w0, conjRep_Dz_w1, conjRep_Dz_w2, conjRep_Dz_w3, conjRep_Dz_w4]
      module
    rw [key]
    exact U.smul_mem _ (U.add_mem (U.sub_mem (U.sub_mem hN (hUinv matrixSubmonoidElementA N hN))
      (hUinv matrixSubmonoidElementB N hN)) (hUinv matrixSubmonoidElementC N hN))
  have projB : ∀ N ∈ U, (N 0 2) • fiveMatrixFamily 1 ∈ U := by
    intro N hN
    obtain ⟨hsym, htr⟩ := auxiliaryRealMatrixResultF.mp (hUle hN)
    have key : (N 0 2) • fiveMatrixFamily 1
        = (4⁻¹ : ℝ) • (N - realConjugationRepresentation matrixSubmonoidElementA N + realConjugationRepresentation matrixSubmonoidElementB N - realConjugationRepresentation matrixSubmonoidElementC N) := by
      conv_rhs => rw [auxiliaryRealMatrixResultO N hsym htr]
      simp only [map_add, map_smul, conjRep_Dx_w0, conjRep_Dx_w1, conjRep_Dx_w2, conjRep_Dx_w3,
        conjRep_Dx_w4, conjRep_Dy_w0, conjRep_Dy_w1, conjRep_Dy_w2, conjRep_Dy_w3, conjRep_Dy_w4,
        conjRep_Dz_w0, conjRep_Dz_w1, conjRep_Dz_w2, conjRep_Dz_w3, conjRep_Dz_w4]
      module
    rw [key]
    exact U.smul_mem _ (U.sub_mem (U.add_mem (U.sub_mem hN (hUinv matrixSubmonoidElementA N hN))
      (hUinv matrixSubmonoidElementB N hN)) (hUinv matrixSubmonoidElementC N hN))
  have projC : ∀ N ∈ U, (N 1 2) • fiveMatrixFamily 2 ∈ U := by
    intro N hN
    obtain ⟨hsym, htr⟩ := auxiliaryRealMatrixResultF.mp (hUle hN)
    have key : (N 1 2) • fiveMatrixFamily 2
        = (4⁻¹ : ℝ) • (N + realConjugationRepresentation matrixSubmonoidElementA N - realConjugationRepresentation matrixSubmonoidElementB N - realConjugationRepresentation matrixSubmonoidElementC N) := by
      conv_rhs => rw [auxiliaryRealMatrixResultO N hsym htr]
      simp only [map_add, map_smul, conjRep_Dx_w0, conjRep_Dx_w1, conjRep_Dx_w2, conjRep_Dx_w3,
        conjRep_Dx_w4, conjRep_Dy_w0, conjRep_Dy_w1, conjRep_Dy_w2, conjRep_Dy_w3, conjRep_Dy_w4,
        conjRep_Dz_w0, conjRep_Dz_w1, conjRep_Dz_w2, conjRep_Dz_w3, conjRep_Dz_w4]
      module
    rw [key]
    exact U.smul_mem _ (U.sub_mem (U.sub_mem (U.add_mem hN (hUinv matrixSubmonoidElementA N hN))
      (hUinv matrixSubmonoidElementB N hN)) (hUinv matrixSubmonoidElementC N hN))

  have hbootstrap : fiveMatrixFamily 0 ∈ U → auxiliaryRealSubmoduleD ≤ U := by
    intro hw0
    have hw2 : fiveMatrixFamily 2 ∈ U := by
      have t := hUinv matrixSubmonoidElementD _ hw0; rwa [conjRep_Pc_w0] at t
    have hw1 : fiveMatrixFamily 1 ∈ U := by
      have t := hUinv matrixSubmonoidElementD _ hw2; rwa [conjRep_Pc_w2] at t
    have hw3 : fiveMatrixFamily 3 ∈ U := by
      have t := hUinv matrixSubmonoidElementF _ hw0; rw [auxiliaryRealActionValue] at t
      exact (Submodule.neg_mem_iff U).mp t
    have hw4 : fiveMatrixFamily 4 ∈ U := by
      have t := hUinv matrixSubmonoidElementD _ hw3; rwa [conjRep_Pc_w3] at t
    intro N hN
    obtain ⟨hNsym, hNtr⟩ := auxiliaryRealMatrixResultF.mp hN
    rw [auxiliaryRealMatrixResultO N hNsym hNtr]
    exact U.add_mem (U.add_mem (U.add_mem (U.add_mem
      (U.smul_mem _ hw0) (U.smul_mem _ hw1)) (U.smul_mem _ hw2))
      (U.smul_mem _ hw3)) (U.smul_mem _ hw4)

  have smul_extract : ∀ {c : ℝ} {w : realMatrixSpace}, c ≠ 0 → c • w ∈ U → w ∈ U := by
    intro c w hc hcw
    rw [← one_smul ℝ w, ← inv_mul_cancel₀ hc, mul_smul]; exact U.smul_mem _ hcw

  have w1_to_w0 : fiveMatrixFamily 1 ∈ U → fiveMatrixFamily 0 ∈ U := fun hw1 => by
    have t := hUinv matrixSubmonoidElementD _ hw1; rwa [conjRep_Pc_w1] at t
  have w2_to_w0 : fiveMatrixFamily 2 ∈ U → fiveMatrixFamily 0 ∈ U := fun hw2 => by
    have t := hUinv matrixSubmonoidElementD _ hw2; rw [conjRep_Pc_w2] at t; exact w1_to_w0 t

  obtain ⟨M, hMU, hMne⟩ := U.ne_bot_iff.mp h
  obtain ⟨hMsym, hMtr⟩ := auxiliaryRealMatrixResultF.mp (hUle hMU)
  rcases eq_or_ne (M 0 1) 0 with h01 | h01
  · rcases eq_or_ne (M 0 2) 0 with h02 | h02
    · rcases eq_or_ne (M 1 2) 0 with h12 | h12
      ·

        have hMdec : M = M 0 0 • fiveMatrixFamily 3 + (M 0 0 + M 1 1) • fiveMatrixFamily 4 := by
          have hd := auxiliaryRealMatrixResultO M hMsym hMtr
          rw [h01, h02, h12] at hd
          simpa only [zero_smul, zero_add] using hd
        set a := M 0 0 with ha
        set b := M 1 1 with hb
        rcases eq_or_ne a b with hab | hab
        ·
          have hM00 : a ≠ 0 := by
            intro hz
            have hb0 : b = 0 := by rw [← hab]; exact hz
            apply hMne
            conv_lhs => rw [hMdec]
            rw [hz, hb0]; simp
          have hform : realConjugationRepresentation matrixSubmonoidElementE M
              = (-(2 * a + b) / 2) • fiveMatrixFamily 1 + (-b / 2) • fiveMatrixFamily 3 + (b / 2) • fiveMatrixFamily 4 := by
            conv_lhs => rw [hMdec]
            rw [map_add, map_smul, map_smul, conjRep_Ry45_w3, conjRep_Ry45_w4]
            module
          have hentry : (realConjugationRepresentation matrixSubmonoidElementE M) 0 2 = -(2 * a + b) / 2 := by
            rw [hform]; simp [fiveMatrixFamily, Matrix.add_apply]
          have hne : 2 * a + b ≠ 0 := by rw [← hab]; intro hc; exact hM00 (by linarith)
          have hcoef : (realConjugationRepresentation matrixSubmonoidElementE M) 0 2 ≠ 0 := by
            rw [hentry, neg_div]; exact neg_ne_zero.mpr (div_ne_zero hne (by norm_num))
          exact hbootstrap (w1_to_w0 (smul_extract hcoef (projB _ (hUinv matrixSubmonoidElementE M hMU))))
        ·
          have hform : realConjugationRepresentation matrixSubmonoidElementF M
              = ((a - b) / 2) • fiveMatrixFamily 0 + ((a + b) / 2) • fiveMatrixFamily 3 + (a + b) • fiveMatrixFamily 4 := by
            conv_lhs => rw [hMdec]
            rw [map_add, map_smul, map_smul, conjRep_Rz45_w3, conjRep_Rz45_w4]
            module
          have hentry : (realConjugationRepresentation matrixSubmonoidElementF M) 0 1 = (a - b) / 2 := by
            rw [hform]; simp [fiveMatrixFamily, Matrix.add_apply]
          have hcoef : (realConjugationRepresentation matrixSubmonoidElementF M) 0 1 ≠ 0 :=
            hentry ▸ div_ne_zero (sub_ne_zero.mpr hab) (by norm_num)
          exact hbootstrap (smul_extract hcoef (projA _ (hUinv matrixSubmonoidElementF M hMU)))
      ·
        exact hbootstrap (w2_to_w0 (smul_extract h12 (projC M hMU)))
    ·
      exact hbootstrap (w1_to_w0 (smul_extract h02 (projB M hMU)))
  ·
    exact hbootstrap (smul_extract h01 (projA M hMU))


/-- Defines an auxiliary type. -/
abbrev complexMatrixSpace : Type := Matrix (Fin 3) (Fin 3) ℂ


/-- Defines a ring homomorphism from the displayed real matrix space to the complex matrix space. -/
def complexificationMap : realMatrixSpace →+* complexMatrixSpace := (algebraMap ℝ ℂ).mapMatrix

/-- Computes an entry of the displayed complexification map. -/
@[simp] theorem complexificationMap_apply (M : realMatrixSpace) (i j : Fin 3) : complexificationMap M i j = ((M i j : ℝ) : ℂ) := rfl


/-- An auxiliary result about the displayed real matrix space. -/
theorem auxiliaryMatrixResultA (M : realMatrixSpace) : complexificationMap Mᵀ = (complexificationMap M)ᵀ := by
  ext i j; simp [Matrix.transpose_apply]


/-- Defines a complex representation of the displayed matrix submonoid. -/
def complexConjugationRepresentation : Representation ℂ realMatrixSubmonoid complexMatrixSpace where
  toFun A := (LinearMap.mulLeft ℂ (complexificationMap (A : realMatrixSpace))).comp
    (LinearMap.mulRight ℂ ((complexificationMap (A : realMatrixSpace))ᵀ))
  map_one' := by
    ext M
    simp
  map_mul' A B := by
    ext M
    simp only [Submonoid.coe_mul, map_mul, Matrix.transpose_mul, LinearMap.comp_apply,
      LinearMap.mulLeft_apply, LinearMap.mulRight_apply, Module.End.mul_apply]
    simp [mul_assoc]

/-- Computes the displayed complex representation action. -/
@[simp]
theorem complexConjugationRepresentation_apply (A : realMatrixSubmonoid) (M : complexMatrixSpace) :
    complexConjugationRepresentation A M = complexificationMap (A : realMatrixSpace) * M * (complexificationMap (A : realMatrixSpace))ᵀ := by
  simp [complexConjugationRepresentation, mul_assoc]


/-- The displayed complexification map commutes with the two actions. -/
theorem complexification_conjugation_commutes (A : realMatrixSubmonoid) (M : realMatrixSpace) : complexificationMap (realConjugationRepresentation A M) = complexConjugationRepresentation A (complexificationMap M) := by
  rw [realConjugationRepresentation_apply, complexConjugationRepresentation_apply, auxiliaryActionResultD, map_mul, map_mul, auxiliaryMatrixResultA]


/-- Defines an auxiliary complex submodule of the displayed matrix space. -/
def auxiliaryComplexSubmoduleA : Submodule ℂ complexMatrixSpace where
  carrier := {M | Mᵀ = -M}
  add_mem' {a b} ha hb := by
    simp only [Set.mem_setOf_eq] at ha hb ⊢; rw [transpose_add, ha, hb]; abel
  zero_mem' := by simp
  smul_mem' c a ha := by
    simp only [Set.mem_setOf_eq] at ha ⊢; rw [transpose_smul, ha, smul_neg]


/-- Defines an auxiliary complex submodule of the displayed matrix space. -/
def auxiliaryComplexSubmoduleB : Submodule ℂ complexMatrixSpace where
  carrier := {M | Mᵀ = M ∧ M.trace = 0}
  add_mem' {a b} ha hb := by
    simp only [Set.mem_setOf_eq] at ha hb ⊢
    exact ⟨by rw [transpose_add, ha.1, hb.1], by rw [trace_add, ha.2, hb.2, add_zero]⟩
  zero_mem' := by simp only [Set.mem_setOf_eq]; exact ⟨by simp, by simp⟩
  smul_mem' c a ha := by
    simp only [Set.mem_setOf_eq] at ha ⊢
    exact ⟨by rw [transpose_smul, ha.1], by rw [trace_smul, ha.2, smul_zero]⟩

/-- An auxiliary result about the displayed complex matrix space. -/
theorem auxiliaryComplexMatrixResultA {M : complexMatrixSpace} : M ∈ auxiliaryComplexSubmoduleA ↔ Mᵀ = -M := Iff.rfl
/-- An auxiliary result about the displayed complex matrix space. -/
theorem auxiliaryComplexMatrixResultB {M : complexMatrixSpace} :
    M ∈ auxiliaryComplexSubmoduleB ↔ Mᵀ = M ∧ M.trace = 0 := Iff.rfl


/-- The displayed complexification map respects real scalar multiplication. -/
theorem complexification_smul (r : ℝ) (N : realMatrixSpace) : complexificationMap (r • N) = (r : ℂ) • complexificationMap N := by
  ext i j; simp [Matrix.smul_apply, Complex.ofReal_mul]


/-- An auxiliary result about the displayed complex matrix space. -/
theorem auxiliaryComplexMatrixResultC (M : complexMatrixSpace) (hM : Mᵀ = -M) :
    M = M 0 1 • complexificationMap (threeMatrixFamily 0) + M 0 2 • complexificationMap (threeMatrixFamily 1) + M 1 2 • complexificationMap (threeMatrixFamily 2) := by
  have hd : ∀ i, M i i = 0 := fun i => by
    have h := congr_fun (congr_fun hM i) i
    simp only [Matrix.transpose_apply, Matrix.neg_apply] at h; linear_combination (2⁻¹ : ℂ) * h
  have ho : ∀ i j, M j i = -M i j := fun i j => by
    have h := congr_fun (congr_fun hM i) j
    simpa only [Matrix.transpose_apply, Matrix.neg_apply] using h
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [threeMatrixFamily, Matrix.add_apply] <;>
    (first | rfl | exact hd 0 | exact hd 1 | exact hd 2 |
      exact ho 0 1 | exact ho 0 2 | exact ho 1 2)


/-- An auxiliary result about the displayed complex matrix space. -/
theorem auxiliaryComplexMatrixResultD (M : complexMatrixSpace) (hsym : Mᵀ = M) (htr : M.trace = 0) :
    M = M 0 1 • complexificationMap (fiveMatrixFamily 0) + M 0 2 • complexificationMap (fiveMatrixFamily 1) + M 1 2 • complexificationMap (fiveMatrixFamily 2) + M 0 0 • complexificationMap (fiveMatrixFamily 3)
      + (M 0 0 + M 1 1) • complexificationMap (fiveMatrixFamily 4) := by
  have hs : ∀ i j, M j i = M i j := fun i j => by
    have h := congr_fun (congr_fun hsym i) j
    simpa only [Matrix.transpose_apply] using h
  have htrace : M 2 2 = -M 1 1 - M 0 0 := by
    rw [Matrix.trace_fin_three] at htr; linear_combination htr
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [fiveMatrixFamily, Matrix.add_apply] <;>
    (first | rfl | exact hs 0 1 | exact hs 0 2 | exact hs 1 2 | exact htrace)


private theorem conjRepc_Dz0 : complexConjugationRepresentation matrixSubmonoidElementC (complexificationMap (threeMatrixFamily 0)) = complexificationMap (threeMatrixFamily 0) := by
  rw [← complexification_conjugation_commutes, conjRep_Dz0]
private theorem conjRepc_Dz1 : complexConjugationRepresentation matrixSubmonoidElementC (complexificationMap (threeMatrixFamily 1)) = -complexificationMap (threeMatrixFamily 1) := by
  rw [← complexification_conjugation_commutes, conjRep_Dz1, map_neg]
private theorem conjRepc_Dz2 : complexConjugationRepresentation matrixSubmonoidElementC (complexificationMap (threeMatrixFamily 2)) = -complexificationMap (threeMatrixFamily 2) := by
  rw [← complexification_conjugation_commutes, conjRep_Dz2, map_neg]
private theorem conjRepc_Dy0 : complexConjugationRepresentation matrixSubmonoidElementB (complexificationMap (threeMatrixFamily 0)) = -complexificationMap (threeMatrixFamily 0) := by
  rw [← complexification_conjugation_commutes, conjRep_Dy0, map_neg]
private theorem conjRepc_Dy1 : complexConjugationRepresentation matrixSubmonoidElementB (complexificationMap (threeMatrixFamily 1)) = complexificationMap (threeMatrixFamily 1) := by
  rw [← complexification_conjugation_commutes, conjRep_Dy1]
private theorem conjRepc_Dy2 : complexConjugationRepresentation matrixSubmonoidElementB (complexificationMap (threeMatrixFamily 2)) = -complexificationMap (threeMatrixFamily 2) := by
  rw [← complexification_conjugation_commutes, conjRep_Dy2, map_neg]
private theorem conjRepc_Dx0 : complexConjugationRepresentation matrixSubmonoidElementA (complexificationMap (threeMatrixFamily 0)) = -complexificationMap (threeMatrixFamily 0) := by
  rw [← complexification_conjugation_commutes, conjRep_Dx0, map_neg]
private theorem conjRepc_Dx1 : complexConjugationRepresentation matrixSubmonoidElementA (complexificationMap (threeMatrixFamily 1)) = -complexificationMap (threeMatrixFamily 1) := by
  rw [← complexification_conjugation_commutes, conjRep_Dx1, map_neg]
private theorem conjRepc_Dx2 : complexConjugationRepresentation matrixSubmonoidElementA (complexificationMap (threeMatrixFamily 2)) = complexificationMap (threeMatrixFamily 2) := by
  rw [← complexification_conjugation_commutes, conjRep_Dx2]
private theorem conjRepc_Pc0 : complexConjugationRepresentation matrixSubmonoidElementD (complexificationMap (threeMatrixFamily 0)) = complexificationMap (threeMatrixFamily 2) := by
  rw [← complexification_conjugation_commutes, conjRep_Pc0]
private theorem conjRepc_Pc1 : complexConjugationRepresentation matrixSubmonoidElementD (complexificationMap (threeMatrixFamily 1)) = -complexificationMap (threeMatrixFamily 0) := by
  rw [← complexification_conjugation_commutes, conjRep_Pc1, map_neg]
private theorem conjRepc_Pc2 : complexConjugationRepresentation matrixSubmonoidElementD (complexificationMap (threeMatrixFamily 2)) = -complexificationMap (threeMatrixFamily 1) := by
  rw [← complexification_conjugation_commutes, conjRep_Pc2, map_neg]

private theorem conjRepc_Pc_w0 : complexConjugationRepresentation matrixSubmonoidElementD (complexificationMap (fiveMatrixFamily 0)) = complexificationMap (fiveMatrixFamily 2) := by
  rw [← complexification_conjugation_commutes, conjRep_Pc_w0]
private theorem conjRepc_Pc_w1 : complexConjugationRepresentation matrixSubmonoidElementD (complexificationMap (fiveMatrixFamily 1)) = complexificationMap (fiveMatrixFamily 0) := by
  rw [← complexification_conjugation_commutes, conjRep_Pc_w1]
private theorem conjRepc_Pc_w2 : complexConjugationRepresentation matrixSubmonoidElementD (complexificationMap (fiveMatrixFamily 2)) = complexificationMap (fiveMatrixFamily 1) := by
  rw [← complexification_conjugation_commutes, conjRep_Pc_w2]
private theorem conjRepc_Pc_w3 : complexConjugationRepresentation matrixSubmonoidElementD (complexificationMap (fiveMatrixFamily 3)) = complexificationMap (fiveMatrixFamily 4) := by
  rw [← complexification_conjugation_commutes, conjRep_Pc_w3]
private theorem conjRepc_Rz45_w0 : complexConjugationRepresentation matrixSubmonoidElementF (complexificationMap (fiveMatrixFamily 0)) = -complexificationMap (fiveMatrixFamily 3) := by
  rw [← complexification_conjugation_commutes, auxiliaryRealActionValue, map_neg]
private theorem conjRepc_Rz45_w3 : complexConjugationRepresentation matrixSubmonoidElementF (complexificationMap (fiveMatrixFamily 3)) = complexificationMap (fiveMatrixFamily 0) := by
  rw [← complexification_conjugation_commutes, conjRep_Rz45_w3]
private theorem conjRepc_Rz45_w4 : complexConjugationRepresentation matrixSubmonoidElementF (complexificationMap (fiveMatrixFamily 4))
    = (-2⁻¹ : ℂ) • complexificationMap (fiveMatrixFamily 0) + (2⁻¹ : ℂ) • complexificationMap (fiveMatrixFamily 3) + complexificationMap (fiveMatrixFamily 4) := by
  rw [← complexification_conjugation_commutes, conjRep_Rz45_w4]; simp only [map_add, complexification_smul]; push_cast; module
private theorem conjRepc_Ry45_w3 : complexConjugationRepresentation matrixSubmonoidElementE (complexificationMap (fiveMatrixFamily 3))
    = (-2⁻¹ : ℂ) • complexificationMap (fiveMatrixFamily 1) + (2⁻¹ : ℂ) • complexificationMap (fiveMatrixFamily 3) + (-2⁻¹ : ℂ) • complexificationMap (fiveMatrixFamily 4) := by
  rw [← complexification_conjugation_commutes, conjRep_Ry45_w3]; simp only [map_add, complexification_smul]; push_cast; module
private theorem conjRepc_Ry45_w4 : complexConjugationRepresentation matrixSubmonoidElementE (complexificationMap (fiveMatrixFamily 4))
    = (-2⁻¹ : ℂ) • complexificationMap (fiveMatrixFamily 1) + (-2⁻¹ : ℂ) • complexificationMap (fiveMatrixFamily 3) + (2⁻¹ : ℂ) • complexificationMap (fiveMatrixFamily 4) := by
  rw [← complexification_conjugation_commutes, conjRep_Ry45_w4]; simp only [map_add, complexification_smul]; push_cast; module
private theorem conjRepc_Dx_w0 : complexConjugationRepresentation matrixSubmonoidElementA (complexificationMap (fiveMatrixFamily 0)) = -complexificationMap (fiveMatrixFamily 0) := by
  rw [← complexification_conjugation_commutes, conjRep_Dx_w0, map_neg]
private theorem conjRepc_Dx_w1 : complexConjugationRepresentation matrixSubmonoidElementA (complexificationMap (fiveMatrixFamily 1)) = -complexificationMap (fiveMatrixFamily 1) := by
  rw [← complexification_conjugation_commutes, conjRep_Dx_w1, map_neg]
private theorem conjRepc_Dx_w2 : complexConjugationRepresentation matrixSubmonoidElementA (complexificationMap (fiveMatrixFamily 2)) = complexificationMap (fiveMatrixFamily 2) := by
  rw [← complexification_conjugation_commutes, conjRep_Dx_w2]
private theorem conjRepc_Dx_w3 : complexConjugationRepresentation matrixSubmonoidElementA (complexificationMap (fiveMatrixFamily 3)) = complexificationMap (fiveMatrixFamily 3) := by
  rw [← complexification_conjugation_commutes, conjRep_Dx_w3]
private theorem conjRepc_Dx_w4 : complexConjugationRepresentation matrixSubmonoidElementA (complexificationMap (fiveMatrixFamily 4)) = complexificationMap (fiveMatrixFamily 4) := by
  rw [← complexification_conjugation_commutes, conjRep_Dx_w4]
private theorem conjRepc_Dy_w0 : complexConjugationRepresentation matrixSubmonoidElementB (complexificationMap (fiveMatrixFamily 0)) = -complexificationMap (fiveMatrixFamily 0) := by
  rw [← complexification_conjugation_commutes, conjRep_Dy_w0, map_neg]
private theorem conjRepc_Dy_w1 : complexConjugationRepresentation matrixSubmonoidElementB (complexificationMap (fiveMatrixFamily 1)) = complexificationMap (fiveMatrixFamily 1) := by
  rw [← complexification_conjugation_commutes, conjRep_Dy_w1]
private theorem conjRepc_Dy_w2 : complexConjugationRepresentation matrixSubmonoidElementB (complexificationMap (fiveMatrixFamily 2)) = -complexificationMap (fiveMatrixFamily 2) := by
  rw [← complexification_conjugation_commutes, conjRep_Dy_w2, map_neg]
private theorem conjRepc_Dy_w3 : complexConjugationRepresentation matrixSubmonoidElementB (complexificationMap (fiveMatrixFamily 3)) = complexificationMap (fiveMatrixFamily 3) := by
  rw [← complexification_conjugation_commutes, conjRep_Dy_w3]
private theorem conjRepc_Dy_w4 : complexConjugationRepresentation matrixSubmonoidElementB (complexificationMap (fiveMatrixFamily 4)) = complexificationMap (fiveMatrixFamily 4) := by
  rw [← complexification_conjugation_commutes, conjRep_Dy_w4]
private theorem conjRepc_Dz_w0 : complexConjugationRepresentation matrixSubmonoidElementC (complexificationMap (fiveMatrixFamily 0)) = complexificationMap (fiveMatrixFamily 0) := by
  rw [← complexification_conjugation_commutes, conjRep_Dz_w0]
private theorem conjRepc_Dz_w1 : complexConjugationRepresentation matrixSubmonoidElementC (complexificationMap (fiveMatrixFamily 1)) = -complexificationMap (fiveMatrixFamily 1) := by
  rw [← complexification_conjugation_commutes, conjRep_Dz_w1, map_neg]
private theorem conjRepc_Dz_w2 : complexConjugationRepresentation matrixSubmonoidElementC (complexificationMap (fiveMatrixFamily 2)) = -complexificationMap (fiveMatrixFamily 2) := by
  rw [← complexification_conjugation_commutes, conjRep_Dz_w2, map_neg]
private theorem conjRepc_Dz_w3 : complexConjugationRepresentation matrixSubmonoidElementC (complexificationMap (fiveMatrixFamily 3)) = complexificationMap (fiveMatrixFamily 3) := by
  rw [← complexification_conjugation_commutes, conjRep_Dz_w3]
private theorem conjRepc_Dz_w4 : complexConjugationRepresentation matrixSubmonoidElementC (complexificationMap (fiveMatrixFamily 4)) = complexificationMap (fiveMatrixFamily 4) := by
  rw [← complexification_conjugation_commutes, conjRep_Dz_w4]


/-- An auxiliary statement about complex submodules of the displayed matrix space. -/
@[source_ref "Chapter4/Problem4.12.11" (role := supporting)]
theorem auxiliaryComplexSubmoduleClassification (U : Submodule ℂ complexMatrixSpace) (hUle : U ≤ auxiliaryComplexSubmoduleA)
    (hUinv : ∀ (A : realMatrixSubmonoid), ∀ M ∈ U, complexConjugationRepresentation A M ∈ U) :
    U = ⊥ ∨ U = auxiliaryComplexSubmoduleA := by

  rcases eq_or_ne U ⊥ with h | h
  · exact Or.inl h
  refine Or.inr (le_antisymm hUle ?_)
  obtain ⟨M, hMU, hMne⟩ := U.ne_bot_iff.mp h
  have hMsk : Mᵀ = -M := auxiliaryComplexMatrixResultA.mp (hUle hMU)
  have hMdec : M = M 0 1 • complexificationMap (threeMatrixFamily 0) + M 0 2 • complexificationMap (threeMatrixFamily 1) + M 1 2 • complexificationMap (threeMatrixFamily 2) :=
    auxiliaryComplexMatrixResultC M hMsk
  have hDzM : complexConjugationRepresentation matrixSubmonoidElementC M ∈ U := hUinv matrixSubmonoidElementC M hMU
  have hDyM : complexConjugationRepresentation matrixSubmonoidElementB M ∈ U := hUinv matrixSubmonoidElementB M hMU
  have hDxM : complexConjugationRepresentation matrixSubmonoidElementA M ∈ U := hUinv matrixSubmonoidElementA M hMU
  have hav0 : M 0 1 • complexificationMap (threeMatrixFamily 0) ∈ U := by
    have key : M 0 1 • complexificationMap (threeMatrixFamily 0) = (2⁻¹ : ℂ) • (M + complexConjugationRepresentation matrixSubmonoidElementC M) := by
      conv_rhs => rw [hMdec]
      simp only [map_add, map_smul, conjRepc_Dz0, conjRepc_Dz1, conjRepc_Dz2]
      module
    rw [key]; exact U.smul_mem _ (U.add_mem hMU hDzM)
  have hbv1 : M 0 2 • complexificationMap (threeMatrixFamily 1) ∈ U := by
    have key : M 0 2 • complexificationMap (threeMatrixFamily 1) = (2⁻¹ : ℂ) • (M + complexConjugationRepresentation matrixSubmonoidElementB M) := by
      conv_rhs => rw [hMdec]
      simp only [map_add, map_smul, conjRepc_Dy0, conjRepc_Dy1, conjRepc_Dy2]
      module
    rw [key]; exact U.smul_mem _ (U.add_mem hMU hDyM)
  have hcv2 : M 1 2 • complexificationMap (threeMatrixFamily 2) ∈ U := by
    have key : M 1 2 • complexificationMap (threeMatrixFamily 2) = (2⁻¹ : ℂ) • (M + complexConjugationRepresentation matrixSubmonoidElementA M) := by
      conv_rhs => rw [hMdec]
      simp only [map_add, map_smul, conjRepc_Dx0, conjRepc_Dx1, conjRepc_Dx2]
      module
    rw [key]; exact U.smul_mem _ (U.add_mem hMU hDxM)
  have hav2 : M 0 1 • complexificationMap (threeMatrixFamily 2) ∈ U := by
    have t := hUinv matrixSubmonoidElementD _ hav0; rwa [map_smul, conjRepc_Pc0] at t
  have hav1 : M 0 1 • complexificationMap (threeMatrixFamily 1) ∈ U := by
    have t := hUinv matrixSubmonoidElementD _ hav2; rw [map_smul, conjRepc_Pc2, smul_neg] at t
    exact neg_mem_iff.mp t
  have hbv0 : M 0 2 • complexificationMap (threeMatrixFamily 0) ∈ U := by
    have t := hUinv matrixSubmonoidElementD _ hbv1; rw [map_smul, conjRepc_Pc1, smul_neg] at t
    exact neg_mem_iff.mp t
  have hbv2 : M 0 2 • complexificationMap (threeMatrixFamily 2) ∈ U := by
    have t := hUinv matrixSubmonoidElementD _ hbv0; rwa [map_smul, conjRepc_Pc0] at t
  have hcv1 : M 1 2 • complexificationMap (threeMatrixFamily 1) ∈ U := by
    have t := hUinv matrixSubmonoidElementD _ hcv2; rw [map_smul, conjRepc_Pc2, smul_neg] at t
    exact neg_mem_iff.mp t
  have hcv0 : M 1 2 • complexificationMap (threeMatrixFamily 0) ∈ U := by
    have t := hUinv matrixSubmonoidElementD _ hcv1; rw [map_smul, conjRepc_Pc1, smul_neg] at t
    exact neg_mem_iff.mp t
  have hne3 : M 0 1 ≠ 0 ∨ M 0 2 ≠ 0 ∨ M 1 2 ≠ 0 := by
    by_contra hcon
    push Not at hcon
    exact hMne (by rw [hMdec, hcon.1, hcon.2.1, hcon.2.2]; simp)
  have extract : ∀ w : complexMatrixSpace,
      M 0 1 • w ∈ U → M 0 2 • w ∈ U → M 1 2 • w ∈ U → w ∈ U := by
    intro w h1 h2 h3
    rcases hne3 with hh | hh | hh
    · rw [← one_smul ℂ w, ← inv_mul_cancel₀ hh, mul_smul]; exact U.smul_mem _ h1
    · rw [← one_smul ℂ w, ← inv_mul_cancel₀ hh, mul_smul]; exact U.smul_mem _ h2
    · rw [← one_smul ℂ w, ← inv_mul_cancel₀ hh, mul_smul]; exact U.smul_mem _ h3
  have hs0 : complexificationMap (threeMatrixFamily 0) ∈ U := extract _ hav0 hbv0 hcv0
  have hs1 : complexificationMap (threeMatrixFamily 1) ∈ U := extract _ hav1 hbv1 hcv1
  have hs2 : complexificationMap (threeMatrixFamily 2) ∈ U := extract _ hav2 hbv2 hcv2
  intro N hN
  rw [auxiliaryComplexMatrixResultC N (auxiliaryComplexMatrixResultA.mp hN)]
  exact U.add_mem (U.add_mem (U.smul_mem _ hs0) (U.smul_mem _ hs1)) (U.smul_mem _ hs2)


/-- An auxiliary statement about complex submodules of the displayed matrix space. -/
@[source_ref "Chapter4/Problem4.12.11" (role := supporting)]
theorem auxiliaryComplexSubmoduleResult (U : Submodule ℂ complexMatrixSpace)
    (hUle : U ≤ auxiliaryComplexSubmoduleB)
    (hUinv : ∀ (A : realMatrixSubmonoid), ∀ M ∈ U, complexConjugationRepresentation A M ∈ U) :
    U = ⊥ ∨ U = auxiliaryComplexSubmoduleB := by

  rcases eq_or_ne U ⊥ with h | h
  · exact Or.inl h
  refine Or.inr (le_antisymm hUle ?_)
  have projA : ∀ N ∈ U, N 0 1 • complexificationMap (fiveMatrixFamily 0) ∈ U := by
    intro N hN
    obtain ⟨hsym, htr⟩ := auxiliaryComplexMatrixResultB.mp (hUle hN)
    have key : N 0 1 • complexificationMap (fiveMatrixFamily 0)
        = (4⁻¹ : ℂ) • (N - complexConjugationRepresentation matrixSubmonoidElementA N - complexConjugationRepresentation matrixSubmonoidElementB N + complexConjugationRepresentation matrixSubmonoidElementC N) := by
      conv_rhs => rw [auxiliaryComplexMatrixResultD N hsym htr]
      simp only [map_add, map_smul, conjRepc_Dx_w0, conjRepc_Dx_w1, conjRepc_Dx_w2, conjRepc_Dx_w3,
        conjRepc_Dx_w4, conjRepc_Dy_w0, conjRepc_Dy_w1, conjRepc_Dy_w2, conjRepc_Dy_w3,
        conjRepc_Dy_w4, conjRepc_Dz_w0, conjRepc_Dz_w1, conjRepc_Dz_w2, conjRepc_Dz_w3,
        conjRepc_Dz_w4]
      module
    rw [key]
    exact U.smul_mem _ (U.add_mem (U.sub_mem (U.sub_mem hN (hUinv matrixSubmonoidElementA N hN))
      (hUinv matrixSubmonoidElementB N hN)) (hUinv matrixSubmonoidElementC N hN))
  have projB : ∀ N ∈ U, N 0 2 • complexificationMap (fiveMatrixFamily 1) ∈ U := by
    intro N hN
    obtain ⟨hsym, htr⟩ := auxiliaryComplexMatrixResultB.mp (hUle hN)
    have key : N 0 2 • complexificationMap (fiveMatrixFamily 1)
        = (4⁻¹ : ℂ) • (N - complexConjugationRepresentation matrixSubmonoidElementA N + complexConjugationRepresentation matrixSubmonoidElementB N - complexConjugationRepresentation matrixSubmonoidElementC N) := by
      conv_rhs => rw [auxiliaryComplexMatrixResultD N hsym htr]
      simp only [map_add, map_smul, conjRepc_Dx_w0, conjRepc_Dx_w1, conjRepc_Dx_w2, conjRepc_Dx_w3,
        conjRepc_Dx_w4, conjRepc_Dy_w0, conjRepc_Dy_w1, conjRepc_Dy_w2, conjRepc_Dy_w3,
        conjRepc_Dy_w4, conjRepc_Dz_w0, conjRepc_Dz_w1, conjRepc_Dz_w2, conjRepc_Dz_w3,
        conjRepc_Dz_w4]
      module
    rw [key]
    exact U.smul_mem _ (U.sub_mem (U.add_mem (U.sub_mem hN (hUinv matrixSubmonoidElementA N hN))
      (hUinv matrixSubmonoidElementB N hN)) (hUinv matrixSubmonoidElementC N hN))
  have projC : ∀ N ∈ U, N 1 2 • complexificationMap (fiveMatrixFamily 2) ∈ U := by
    intro N hN
    obtain ⟨hsym, htr⟩ := auxiliaryComplexMatrixResultB.mp (hUle hN)
    have key : N 1 2 • complexificationMap (fiveMatrixFamily 2)
        = (4⁻¹ : ℂ) • (N + complexConjugationRepresentation matrixSubmonoidElementA N - complexConjugationRepresentation matrixSubmonoidElementB N - complexConjugationRepresentation matrixSubmonoidElementC N) := by
      conv_rhs => rw [auxiliaryComplexMatrixResultD N hsym htr]
      simp only [map_add, map_smul, conjRepc_Dx_w0, conjRepc_Dx_w1, conjRepc_Dx_w2, conjRepc_Dx_w3,
        conjRepc_Dx_w4, conjRepc_Dy_w0, conjRepc_Dy_w1, conjRepc_Dy_w2, conjRepc_Dy_w3,
        conjRepc_Dy_w4, conjRepc_Dz_w0, conjRepc_Dz_w1, conjRepc_Dz_w2, conjRepc_Dz_w3,
        conjRepc_Dz_w4]
      module
    rw [key]
    exact U.smul_mem _ (U.sub_mem (U.sub_mem (U.add_mem hN (hUinv matrixSubmonoidElementA N hN))
      (hUinv matrixSubmonoidElementB N hN)) (hUinv matrixSubmonoidElementC N hN))
  have hbootstrap : complexificationMap (fiveMatrixFamily 0) ∈ U → auxiliaryComplexSubmoduleB ≤ U := by
    intro hw0
    have hw2 : complexificationMap (fiveMatrixFamily 2) ∈ U := by
      have t := hUinv matrixSubmonoidElementD _ hw0; rwa [conjRepc_Pc_w0] at t
    have hw1 : complexificationMap (fiveMatrixFamily 1) ∈ U := by
      have t := hUinv matrixSubmonoidElementD _ hw2; rwa [conjRepc_Pc_w2] at t
    have hw3 : complexificationMap (fiveMatrixFamily 3) ∈ U := by
      have t := hUinv matrixSubmonoidElementF _ hw0; rw [conjRepc_Rz45_w0] at t
      exact (Submodule.neg_mem_iff U).mp t
    have hw4 : complexificationMap (fiveMatrixFamily 4) ∈ U := by
      have t := hUinv matrixSubmonoidElementD _ hw3; rwa [conjRepc_Pc_w3] at t
    intro N hN
    obtain ⟨hNsym, hNtr⟩ := auxiliaryComplexMatrixResultB.mp hN
    rw [auxiliaryComplexMatrixResultD N hNsym hNtr]
    exact U.add_mem (U.add_mem (U.add_mem (U.add_mem
      (U.smul_mem _ hw0) (U.smul_mem _ hw1)) (U.smul_mem _ hw2))
      (U.smul_mem _ hw3)) (U.smul_mem _ hw4)
  have smul_extract : ∀ {c : ℂ} {w : complexMatrixSpace}, c ≠ 0 → c • w ∈ U → w ∈ U := by
    intro c w hc hcw
    rw [← one_smul ℂ w, ← inv_mul_cancel₀ hc, mul_smul]; exact U.smul_mem _ hcw
  have w1_to_w0 : complexificationMap (fiveMatrixFamily 1) ∈ U → complexificationMap (fiveMatrixFamily 0) ∈ U := fun hw1 => by
    have t := hUinv matrixSubmonoidElementD _ hw1; rwa [conjRepc_Pc_w1] at t
  have w2_to_w0 : complexificationMap (fiveMatrixFamily 2) ∈ U → complexificationMap (fiveMatrixFamily 0) ∈ U := fun hw2 => by
    have t := hUinv matrixSubmonoidElementD _ hw2; rw [conjRepc_Pc_w2] at t; exact w1_to_w0 t
  obtain ⟨M, hMU, hMne⟩ := U.ne_bot_iff.mp h
  obtain ⟨hMsym, hMtr⟩ := auxiliaryComplexMatrixResultB.mp (hUle hMU)
  rcases eq_or_ne (M 0 1) 0 with h01 | h01
  · rcases eq_or_ne (M 0 2) 0 with h02 | h02
    · rcases eq_or_ne (M 1 2) 0 with h12 | h12
      · have hMdec : M = M 0 0 • complexificationMap (fiveMatrixFamily 3) + (M 0 0 + M 1 1) • complexificationMap (fiveMatrixFamily 4) := by
          have hd := auxiliaryComplexMatrixResultD M hMsym hMtr
          rw [h01, h02, h12] at hd
          simpa only [zero_smul, zero_add] using hd
        set a := M 0 0 with ha
        set b := M 1 1 with hb
        rcases eq_or_ne a b with hab | hab
        · have hM00 : a ≠ 0 := by
            intro hz
            have hb0 : b = 0 := by rw [← hab]; exact hz
            apply hMne
            conv_lhs => rw [hMdec]
            rw [hz, hb0]; simp
          have hform : complexConjugationRepresentation matrixSubmonoidElementE M
              = (-(2 * a + b) / 2) • complexificationMap (fiveMatrixFamily 1) + (-b / 2) • complexificationMap (fiveMatrixFamily 3)
                + (b / 2) • complexificationMap (fiveMatrixFamily 4) := by
            conv_lhs => rw [hMdec]
            rw [map_add, map_smul, map_smul, conjRepc_Ry45_w3, conjRepc_Ry45_w4]
            module
          have hentry : (complexConjugationRepresentation matrixSubmonoidElementE M) 0 2 = -(2 * a + b) / 2 := by
            rw [hform]; simp [fiveMatrixFamily, Matrix.add_apply]
          have hne : 2 * a + b ≠ 0 := by
            rw [← hab]; intro hc; exact hM00 (by linear_combination (3⁻¹ : ℂ) * hc)
          have hcoef : (complexConjugationRepresentation matrixSubmonoidElementE M) 0 2 ≠ 0 := by
            rw [hentry, neg_div]; exact neg_ne_zero.mpr (div_ne_zero hne (by norm_num))
          exact hbootstrap (w1_to_w0 (smul_extract hcoef (projB _ (hUinv matrixSubmonoidElementE M hMU))))
        · have hform : complexConjugationRepresentation matrixSubmonoidElementF M
              = ((a - b) / 2) • complexificationMap (fiveMatrixFamily 0) + ((a + b) / 2) • complexificationMap (fiveMatrixFamily 3)
                + (a + b) • complexificationMap (fiveMatrixFamily 4) := by
            conv_lhs => rw [hMdec]
            rw [map_add, map_smul, map_smul, conjRepc_Rz45_w3, conjRepc_Rz45_w4]
            module
          have hentry : (complexConjugationRepresentation matrixSubmonoidElementF M) 0 1 = (a - b) / 2 := by
            rw [hform]; simp [fiveMatrixFamily, Matrix.add_apply]
          have hcoef : (complexConjugationRepresentation matrixSubmonoidElementF M) 0 1 ≠ 0 :=
            hentry ▸ div_ne_zero (sub_ne_zero.mpr hab) (by norm_num)
          exact hbootstrap (smul_extract hcoef (projA _ (hUinv matrixSubmonoidElementF M hMU)))
      · exact hbootstrap (w2_to_w0 (smul_extract h12 (projC M hMU)))
    · exact hbootstrap (w1_to_w0 (smul_extract h02 (projB M hMU)))
  · exact hbootstrap (smul_extract h01 (projA M hMU))


/-- The displayed action fixes the identity matrix. -/
theorem realConjugation_map_one (A : realMatrixSubmonoid) : realConjugationRepresentation A (1 : realMatrixSpace) = 1 := by
  rw [realConjugationRepresentation_apply, Matrix.mul_one, mul_star_eq_one]


/-- The displayed action commutes with transpose. -/
theorem realConjugation_transpose (A : realMatrixSubmonoid) (M : realMatrixSpace) :
    realConjugationRepresentation A Mᵀ = (realConjugationRepresentation A M)ᵀ := by
  simp only [realConjugationRepresentation_apply, auxiliaryActionResultD, Matrix.transpose_mul,
    Matrix.transpose_transpose, Matrix.mul_assoc]


/-- The displayed action preserves matrix trace. -/
theorem realConjugation_trace (A : realMatrixSubmonoid) (M : realMatrixSpace) : (realConjugationRepresentation A M).trace = M.trace := by
  rw [realConjugationRepresentation_apply, Matrix.trace_mul_comm ((A : realMatrixSpace) * M) (star (A : realMatrixSpace)),
    ← Matrix.mul_assoc, auxiliaryActionResultE, Matrix.one_mul]


/-- Defines an auxiliary linear endomorphism of the displayed real matrix space. -/
def auxiliaryRealEndomorphismA : realMatrixSpace →ₗ[ℝ] realMatrixSpace where
  toFun M := (M.trace / 3) • (1 : realMatrixSpace)
  map_add' M N := by rw [Matrix.trace_add]; module
  map_smul' c M := by rw [Matrix.trace_smul]; simp only [RingHom.id_apply, smul_eq_mul]; module

/-- An auxiliary result about the displayed real matrix space. -/
@[simp] theorem auxiliaryMatrixResultG (M : realMatrixSpace) : auxiliaryRealEndomorphismA M = (M.trace / 3) • (1 : realMatrixSpace) := rfl


/-- An auxiliary result about the displayed matrix action. -/
theorem auxiliaryActionResultA (A : realMatrixSubmonoid) (M : realMatrixSpace) :
    auxiliaryRealEndomorphismA (realConjugationRepresentation A M) = realConjugationRepresentation A (auxiliaryRealEndomorphismA M) := by
  rw [auxiliaryMatrixResultG, auxiliaryMatrixResultG, realConjugation_trace, map_smul, realConjugation_map_one]


/-- Defines an auxiliary linear endomorphism of the displayed real matrix space. -/
def auxiliaryRealEndomorphismB : realMatrixSpace →ₗ[ℝ] realMatrixSpace where
  toFun M := (1 / 2 : ℝ) • (M - Mᵀ)
  map_add' M N := by rw [Matrix.transpose_add]; module
  map_smul' c M := by rw [Matrix.transpose_smul]; simp only [RingHom.id_apply]; module

/-- An auxiliary assertion with unavailable formal rendering. -/
@[simp] theorem auxiliaryMatrixAssertionB (M : realMatrixSpace) : auxiliaryRealEndomorphismB M = (1 / 2 : ℝ) • (M - Mᵀ) := rfl


/-- An auxiliary result about the displayed matrix action. -/
theorem auxiliaryActionResultB (A : realMatrixSubmonoid) (M : realMatrixSpace) :
    auxiliaryRealEndomorphismB (realConjugationRepresentation A M) = realConjugationRepresentation A (auxiliaryRealEndomorphismB M) := by
  rw [auxiliaryMatrixAssertionB, auxiliaryMatrixAssertionB, map_smul, map_sub, realConjugation_transpose]


/-- An auxiliary result about the displayed real matrix space. -/
theorem auxiliaryMatrixResultH (M : realMatrixSpace) : auxiliaryRealEndomorphismA M ∈ auxiliaryRealSubmoduleA := by
  rw [auxiliaryMatrixResultG, auxiliaryRealSubmoduleA]
  exact Submodule.smul_mem _ _ (Submodule.mem_span_singleton_self _)


/-- An auxiliary result about the displayed real matrix space. -/
theorem auxiliaryMatrixResultI (M : realMatrixSpace) : auxiliaryRealEndomorphismB M ∈ auxiliaryRealSubmoduleB := by
  rw [auxiliaryMatrixAssertionB, auxiliaryRealMatrixResultD, Matrix.transpose_smul, Matrix.transpose_sub,
    Matrix.transpose_transpose]
  module


/-- An auxiliary result about a linear endomorphism of the displayed real matrix space. -/
theorem auxiliaryLinearMapResult (φ : realMatrixSpace →ₗ[ℝ] realMatrixSpace)
    (hφ : ∀ (A : realMatrixSubmonoid) (M : realMatrixSpace), φ (realConjugationRepresentation A M) = realConjugationRepresentation A (φ M))
    (W Wsmall : Submodule ℝ realMatrixSpace)
    (hWirr : ∀ (U : Submodule ℝ realMatrixSpace), U ≤ W →
      (∀ (A : realMatrixSubmonoid), ∀ M ∈ U, realConjugationRepresentation A M ∈ U) → U = ⊥ ∨ U = W)
    (hWinv : ∀ (A : realMatrixSubmonoid), ∀ M ∈ W, realConjugationRepresentation A M ∈ W)
    (hmaps : ∀ w ∈ W, φ w ∈ Wsmall)
    (hlt : Module.finrank ℝ Wsmall < Module.finrank ℝ W) :
    ∀ w ∈ W, φ w = 0 := by
  have hkerinv : ∀ (A : realMatrixSubmonoid), ∀ M ∈ LinearMap.ker φ, realConjugationRepresentation A M ∈ LinearMap.ker φ := by
    intro A M hM
    rw [LinearMap.mem_ker] at hM ⊢
    rw [hφ A M, hM, map_zero]
  set K := W ⊓ LinearMap.ker φ with hK
  have hKinv : ∀ (A : realMatrixSubmonoid), ∀ M ∈ K, realConjugationRepresentation A M ∈ K := by
    intro A M hM
    rw [hK, Submodule.mem_inf] at hM ⊢
    exact ⟨hWinv A M hM.1, hkerinv A M hM.2⟩
  rcases hWirr K inf_le_left hKinv with hbot | htop
  · exfalso
    have hψinj : Function.Injective (φ.restrict hmaps) := by
      rw [injective_iff_map_eq_zero]
      rintro ⟨x, hx⟩ hψ0
      have hfx : φ x = 0 := by
        have := congrArg (Subtype.val) hψ0
        rwa [LinearMap.coe_restrict_apply, ZeroMemClass.coe_zero] at this
      have hxK : x ∈ K := by rw [hK]; exact ⟨hx, LinearMap.mem_ker.mpr hfx⟩
      rw [hbot, Submodule.mem_bot] at hxK
      exact Subtype.ext hxK
    have := LinearMap.finrank_le_finrank_of_injective hψinj
    omega
  · intro w hw
    have : w ∈ K := by rw [htop]; exact hw
    rw [hK, Submodule.mem_inf] at this
    exact LinearMap.mem_ker.mp this.2


/-- An auxiliary result about the displayed real matrix space. -/
theorem auxiliaryMatrixResultC (N : realMatrixSpace)
    (hz : realConjugationRepresentation matrixSubmonoidElementC N = N) (hy : realConjugationRepresentation matrixSubmonoidElementB N = N) (hp : realConjugationRepresentation matrixSubmonoidElementD N = N) :
    N = N 0 0 • (1 : realMatrixSpace) := by
  rw [realConjugationRepresentation_apply] at hz hy hp

  have z02 := congr_fun (congr_fun hz 0) 2
  have z20 := congr_fun (congr_fun hz 2) 0
  have z12 := congr_fun (congr_fun hz 1) 2
  have z21 := congr_fun (congr_fun hz 2) 1
  have y01 := congr_fun (congr_fun hy 0) 1
  have y10 := congr_fun (congr_fun hy 1) 0

  have p00 := congr_fun (congr_fun hp 0) 0
  have p11 := congr_fun (congr_fun hp 1) 1
  have p22 := congr_fun (congr_fun hp 2) 2
  simp only [matrixSubmonoidElementC, matrixSubmonoidElementB, matrixSubmonoidElementD, Matrix.mul_apply, Fin.sum_univ_three, star, Matrix.conjTranspose,
    Matrix.transpose, Matrix.of_apply, Matrix.map_apply, Matrix.cons_val', Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two, Matrix.tail_cons,
    id_eq] at z02 z20 z12 z21 y01 y10 p00 p11 p22
  have h01 : N 0 1 = 0 := by linarith
  have h10 : N 1 0 = 0 := by linarith
  have h02 : N 0 2 = 0 := by linarith
  have h20 : N 2 0 = 0 := by linarith
  have h12 : N 1 2 = 0 := by linarith
  have h21 : N 2 1 = 0 := by linarith
  have h11 : N 1 1 = N 0 0 := by linarith
  have h22 : N 2 2 = N 0 0 := by linarith
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.smul_apply, smul_eq_mul, h01, h10, h02, h20, h12, h21, h11, h22]

open Polynomial Filter Topology in

/-- A real polynomial of odd degree has a root. -/
theorem exists_root_of_odd_natDegree {p : ℝ[X]} (hodd : Odd p.natDegree) :
    ∃ x : ℝ, p.IsRoot x := by
  have hpne : p ≠ 0 := by rintro rfl; simp at hodd
  have hlc : p.leadingCoeff ≠ 0 := leadingCoeff_ne_zero.mpr hpne
  set c := p.leadingCoeff⁻¹ with hc
  have hcne : c ≠ 0 := inv_ne_zero hlc
  set q := C c * p with hq
  have hqdeg : q.natDegree = p.natDegree := by rw [hq, natDegree_C_mul hcne]
  have hqodd : Odd q.natDegree := hqdeg ▸ hodd
  have hqlc : q.leadingCoeff = 1 := by
    rw [hq, leadingCoeff_mul, leadingCoeff_C, hc, inv_mul_cancel₀ hlc]
  have hqnd : q.natDegree ≠ 0 := by
    rintro h; rw [h] at hqodd; simp at hqodd
  have hdeg : 0 < q.degree := natDegree_pos_iff_degree_pos.mp (Nat.pos_of_ne_zero hqnd)

  suffices h : ∃ x, q.IsRoot x by
    obtain ⟨x, hx⟩ := h
    refine ⟨x, ?_⟩
    have : eval x q = 0 := hx
    rw [hq, eval_mul, eval_C] at this
    exact (mul_eq_zero.mp this).resolve_left hcne

  have hpos : Tendsto (fun x => eval x q) atTop atTop :=
    q.tendsto_atTop_of_leadingCoeff_nonneg hdeg (by rw [hqlc]; norm_num)
  obtain ⟨b, hb⟩ := (hpos.eventually_gt_atTop 0).exists

  set r := q.comp (-X) with hr
  have hrnd : r.natDegree = q.natDegree := by rw [hr, natDegree_comp]; simp
  have hrdeg : 0 < r.degree :=
    natDegree_pos_iff_degree_pos.mp (by rw [hrnd]; exact Nat.pos_of_ne_zero hqnd)
  have hrlc : r.leadingCoeff ≤ 0 := by
    rw [hr, leadingCoeff_comp (by simp), hqlc, one_mul, leadingCoeff_neg, leadingCoeff_X,
      Odd.neg_one_pow hqodd]
    norm_num
  have hneg : Tendsto (fun x => eval x r) atTop atBot :=
    r.tendsto_atBot_of_leadingCoeff_nonpos hrdeg hrlc
  obtain ⟨a, ha⟩ := (hneg.eventually_lt_atBot 0).exists
  have ha' : eval (-a) q < 0 := by rw [hr, eval_comp, eval_neg, eval_X] at ha; exact ha
  have hmem : (0 : ℝ) ∈ Set.Icc (eval (-a) q) (eval b q) := ⟨ha'.le, hb.le⟩
  rcases le_total (-a) b with hab | hab
  · obtain ⟨x, _, hx⟩ := intermediate_value_Icc hab q.continuous.continuousOn hmem
    exact ⟨x, hx⟩
  · obtain ⟨x, _, hx⟩ := intermediate_value_Icc' hab q.continuous.continuousOn hmem
    exact ⟨x, hx⟩


/-- An auxiliary result about a displayed linear endomorphism. -/
theorem auxiliaryEndomorphismResultA (f : realMatrixSpace →ₗ[ℝ] realMatrixSpace)
    (hf : ∀ A : realMatrixSubmonoid, f.comp (realConjugationRepresentation A) = (realConjugationRepresentation A).comp f) :
    ∃ K μ : ℝ,
      (∀ x ∈ auxiliaryRealSubmoduleA, f x = K • x) ∧
      (∀ y ∈ auxiliaryRealSubmoduleD, f y = μ • y) ∧
      (∀ x ∈ auxiliaryRealSubmoduleC, f x ∈ auxiliaryRealSubmoduleC) := by
  have hf_pt : ∀ (A : realMatrixSubmonoid) (M : realMatrixSpace), f (realConjugationRepresentation A M) = realConjugationRepresentation A (f M) :=
    fun A M => LinearMap.congr_fun (hf A) M

  have hinv1 : ∀ A : realMatrixSubmonoid, realConjugationRepresentation A (f 1) = f 1 := fun A => by rw [← hf_pt A 1, realConjugation_map_one]
  set K := (f 1) 0 0 with hKdef
  have hf1 : f 1 = K • (1 : realMatrixSpace) :=
    auxiliaryMatrixResultC (f 1) (hinv1 matrixSubmonoidElementC) (hinv1 matrixSubmonoidElementB) (hinv1 matrixSubmonoidElementD)
  have hscalar : ∀ x ∈ auxiliaryRealSubmoduleA, f x = K • x := by
    intro x hx
    rw [auxiliaryRealSubmoduleA, Submodule.mem_span_singleton] at hx
    obtain ⟨c, rfl⟩ := hx
    rw [map_smul, hf1, smul_comm]

  have hWinv : ∀ (A : realMatrixSubmonoid), ∀ M ∈ auxiliaryRealSubmoduleD, realConjugationRepresentation A M ∈ auxiliaryRealSubmoduleD :=
    fun A M hM => realConjugation_preserves_selected_submodules auxiliaryRealSubmoduleD (Or.inr (Or.inr rfl)) A M hM
  have hsc0 : ∀ w ∈ auxiliaryRealSubmoduleD, auxiliaryRealEndomorphismA (f w) = 0 := by
    refine auxiliaryLinearMapResult (auxiliaryRealEndomorphismA.comp f) ?_ auxiliaryRealSubmoduleD auxiliaryRealSubmoduleA
      auxiliaryRealSubmoduleResult hWinv ?_ ?_
    · intro A M; simp only [LinearMap.comp_apply]; rw [hf_pt, auxiliaryActionResultA]
    · intro w _; simp only [LinearMap.comp_apply]; exact auxiliaryMatrixResultH _
    · rw [auxiliaryRealSubmoduleA_finrank, auxiliaryRealSubmoduleD_finrank]; norm_num
  have hsk0 : ∀ w ∈ auxiliaryRealSubmoduleD, auxiliaryRealEndomorphismB (f w) = 0 := by
    refine auxiliaryLinearMapResult (auxiliaryRealEndomorphismB.comp f) ?_ auxiliaryRealSubmoduleD auxiliaryRealSubmoduleB
      auxiliaryRealSubmoduleResult hWinv ?_ ?_
    · intro A M; simp only [LinearMap.comp_apply]; rw [hf_pt, auxiliaryActionResultB]
    · intro w _; simp only [LinearMap.comp_apply]; exact auxiliaryMatrixResultI _
    · rw [auxiliaryRealSubmoduleB_finrank, auxiliaryRealSubmoduleD_finrank]; norm_num
  have hmapsW : ∀ w ∈ auxiliaryRealSubmoduleD, f w ∈ auxiliaryRealSubmoduleD := by
    intro w hw
    have hs := hsc0 w hw
    have hk := hsk0 w hw
    rw [auxiliaryMatrixResultG, smul_eq_zero] at hs
    rw [auxiliaryMatrixAssertionB, smul_eq_zero] at hk
    rw [auxiliaryRealMatrixResultF]
    refine ⟨?_, ?_⟩
    · rcases hk with h | h
      · norm_num at h
      · rw [sub_eq_zero] at h; exact h.symm
    · rcases hs with h | h
      · exact (div_eq_zero_iff.mp h).resolve_right (by norm_num)
      · exact absurd h one_ne_zero


  set g : Module.End ℝ auxiliaryRealSubmoduleD := f.restrict hmapsW with hg
  have hgnd : g.charpoly.natDegree = 5 := by
    rw [LinearMap.charpoly_natDegree, auxiliaryRealSubmoduleD_finrank]
  obtain ⟨μ, hμ⟩ := exists_root_of_odd_natDegree (p := g.charpoly) (by rw [hgnd]; decide)
  have hev : g.HasEigenvalue μ := (Module.End.hasEigenvalue_iff_isRoot_charpoly g μ).mpr hμ
  obtain ⟨v, hvec⟩ := hev.exists_hasEigenvector
  have hvsmul : g v = μ • v := hvec.apply_eq_smul
  have hvne : (v : realMatrixSpace) ≠ 0 :=
    fun h => (Module.End.hasEigenvector_iff.mp hvec).2 (Subtype.ext (by simpa using h))
  have hfv : f (v : realMatrixSpace) = μ • (v : realMatrixSpace) := by
    have := congrArg (Subtype.val) hvsmul
    rwa [LinearMap.coe_restrict_apply, Submodule.coe_smul] at this
  set E := auxiliaryRealSubmoduleD ⊓ LinearMap.ker (f - μ • LinearMap.id) with hE
  have hEinv : ∀ (A : realMatrixSubmonoid), ∀ M ∈ E, realConjugationRepresentation A M ∈ E := by
    intro A M hM
    rw [hE, Submodule.mem_inf] at hM
    obtain ⟨hM1, hM2⟩ := hM
    rw [LinearMap.mem_ker, LinearMap.sub_apply, LinearMap.smul_apply, LinearMap.id_apply,
      sub_eq_zero] at hM2
    rw [hE, Submodule.mem_inf]
    refine ⟨hWinv A M hM1, ?_⟩
    rw [LinearMap.mem_ker, LinearMap.sub_apply, LinearMap.smul_apply, LinearMap.id_apply,
      sub_eq_zero, hf_pt, hM2, map_smul]
  have hEne : E ≠ ⊥ := by
    rw [Submodule.ne_bot_iff]
    refine ⟨v, ?_, hvne⟩
    rw [hE, Submodule.mem_inf]
    refine ⟨v.2, ?_⟩
    rw [LinearMap.mem_ker, LinearMap.sub_apply, LinearMap.smul_apply, LinearMap.id_apply,
      sub_eq_zero, hfv]
  have hEtop : E = auxiliaryRealSubmoduleD :=
    (auxiliaryRealSubmoduleResult E inf_le_left hEinv).resolve_left hEne
  have hmu : ∀ y ∈ auxiliaryRealSubmoduleD, f y = μ • y := by
    intro y hy
    have hyE : y ∈ E := by rw [hEtop]; exact hy
    rw [hE, Submodule.mem_inf, LinearMap.mem_ker, LinearMap.sub_apply, LinearMap.smul_apply,
      LinearMap.id_apply, sub_eq_zero] at hyE
    exact hyE.2

  refine ⟨K, μ, hscalar, hmu, ?_⟩
  intro x hx
  rw [← auxiliaryConjunction.1] at hx
  rw [Submodule.mem_sup] at hx
  obtain ⟨s, hs, w, hw, rfl⟩ := hx
  rw [map_add, hscalar s hs, hmu w hw]
  exact Submodule.add_mem _ (Submodule.smul_mem auxiliaryRealSubmoduleC K (auxiliaryRealSubmoduleA_le_auxiliaryRealSubmodule hs))
    (Submodule.smul_mem auxiliaryRealSubmoduleC μ (auxiliaryRealSubmoduleD_le_auxiliaryRealSubmoduleC hw))


/-- An auxiliary result about a displayed linear endomorphism. -/
theorem auxiliaryEndomorphismResultB (f : realMatrixSpace →ₗ[ℝ] realMatrixSpace)
    (hf : ∀ A : realMatrixSubmonoid, f.comp (realConjugationRepresentation A) = (realConjugationRepresentation A).comp f) :
    ∃ K μ : ℝ, ∀ x ∈ auxiliaryRealSubmoduleA, ∀ y ∈ auxiliaryRealSubmoduleD, f (x + y) = K • x + μ • y := by
  obtain ⟨K, μ, hK, hμ, -⟩ := auxiliaryEndomorphismResultA f hf
  exact ⟨K, μ, fun x hx y hy => by rw [map_add, hK x hx, hμ y hy]⟩


/-- The displayed action preserves the specified real submodule. -/
theorem realConjugation_preserves_auxiliarySubmodule (A : realMatrixSubmonoid) {M : realMatrixSpace} (hM : M ∈ auxiliaryRealSubmoduleC) : realConjugationRepresentation A M ∈ auxiliaryRealSubmoduleC := by
  have h : Mᵀ = M := hM
  change (realConjugationRepresentation A M)ᵀ = realConjugationRepresentation A M
  rw [← realConjugation_transpose, h]


/-- Defines an auxiliary real representation of the displayed matrix submonoid. -/
def auxiliaryRealRepresentationB : Representation ℝ realMatrixSubmonoid auxiliaryRealSubmoduleC where
  toFun A := (realConjugationRepresentation A).restrict (fun _ hM => realConjugation_preserves_auxiliarySubmodule A hM)
  map_one' := by
    refine LinearMap.ext fun x => Subtype.ext ?_
    simp
  map_mul' A B := by
    refine LinearMap.ext fun x => Subtype.ext ?_
    simp [mul_assoc]

/-- An auxiliary result about the displayed matrix action. -/
@[simp] theorem auxiliaryActionResultH (A : realMatrixSubmonoid) (x : auxiliaryRealSubmoduleC) :
    (auxiliaryRealRepresentationB A x : realMatrixSpace) = realConjugationRepresentation A (x : realMatrixSpace) := rfl


/-- An auxiliary result about the displayed matrix action. -/
theorem auxiliaryActionResultI (A : realMatrixSubmonoid) :
    auxiliaryRealSubmoduleC.subtype.comp (auxiliaryRealRepresentationB A) = (realConjugationRepresentation A).comp auxiliaryRealSubmoduleC.subtype :=
  LinearMap.ext fun _ => rfl


/-- Defines an auxiliary linear endomorphism of the displayed real matrix space. -/
def auxiliaryRealEndomorphismC : realMatrixSpace →ₗ[ℝ] realMatrixSpace where
  toFun M := (1 / 2 : ℝ) • (M + Mᵀ)
  map_add' M N := by rw [Matrix.transpose_add]; module
  map_smul' c M := by rw [Matrix.transpose_smul]; simp only [RingHom.id_apply]; module

/-- An auxiliary assertion with unavailable formal rendering. -/
@[simp] theorem auxiliaryMatrixAssertionC (M : realMatrixSpace) : auxiliaryRealEndomorphismC M = (1 / 2 : ℝ) • (M + Mᵀ) := rfl


/-- An auxiliary result about the displayed real matrix space. -/
theorem auxiliaryRealMatrixResultN (M : realMatrixSpace) : auxiliaryRealEndomorphismC M ∈ auxiliaryRealSubmoduleC := by
  rw [auxiliaryMatrixAssertionC, auxiliaryRealMatrixResultE, Matrix.transpose_smul, Matrix.transpose_add,
    Matrix.transpose_transpose]
  module


/-- An auxiliary result about the displayed matrix action. -/
theorem auxiliaryActionResultG (A : realMatrixSubmonoid) (M : realMatrixSpace) :
    auxiliaryRealEndomorphismC (realConjugationRepresentation A M) = realConjugationRepresentation A (auxiliaryRealEndomorphismC M) := by
  rw [auxiliaryMatrixAssertionC, auxiliaryMatrixAssertionC, map_smul, map_add, realConjugation_transpose]


/-- An auxiliary result about the displayed real matrix space. -/
theorem auxiliaryRealMatrixResultM {M : realMatrixSpace} (hM : M ∈ auxiliaryRealSubmoduleC) : auxiliaryRealEndomorphismC M = M := by
  have h : Mᵀ = M := hM
  rw [auxiliaryMatrixAssertionC, h]
  module


/-- Defines an auxiliary linear map from the real matrix space into the displayed real submodule. -/
def auxiliaryRealSubmoduleLinearMap : realMatrixSpace →ₗ[ℝ] auxiliaryRealSubmoduleC := LinearMap.codRestrict auxiliaryRealSubmoduleC auxiliaryRealEndomorphismC auxiliaryRealMatrixResultN

/-- An auxiliary result about the displayed real matrix space. -/
@[simp] theorem auxiliaryRealMatrixResultL (M : realMatrixSpace) : (auxiliaryRealSubmoduleLinearMap M : realMatrixSpace) = auxiliaryRealEndomorphismC M := rfl

/-- An auxiliary result about an element of the displayed real submodule. -/
theorem auxiliaryRealSubmoduleElementResult (x : auxiliaryRealSubmoduleC) : auxiliaryRealSubmoduleLinearMap (x : realMatrixSpace) = x :=
  Subtype.ext (by rw [auxiliaryRealMatrixResultL, auxiliaryRealMatrixResultM x.2])

/-- An auxiliary result about the displayed matrix action. -/
theorem auxiliaryActionResultF (A : realMatrixSubmonoid) (M : realMatrixSpace) :
    auxiliaryRealSubmoduleLinearMap (realConjugationRepresentation A M) = auxiliaryRealRepresentationB A (auxiliaryRealSubmoduleLinearMap M) :=
  Subtype.ext (by rw [auxiliaryRealMatrixResultL, auxiliaryActionResultH, auxiliaryRealMatrixResultL, auxiliaryActionResultG])


/-- Defines an auxiliary linear map involving the displayed coordinate space. -/
def auxiliaryCoordinateLinearMap (f : auxiliaryRealSubmoduleC →ₗ[ℝ] realMatrixSpace) : realMatrixSpace →ₗ[ℝ] realMatrixSpace := f.comp auxiliaryRealSubmoduleLinearMap

/-- An auxiliary universally quantified assertion. -/
theorem auxiliaryUniversalResultD (f : auxiliaryRealSubmoduleC →ₗ[ℝ] realMatrixSpace) (x : auxiliaryRealSubmoduleC) :
    auxiliaryCoordinateLinearMap f (x : realMatrixSpace) = f x := by
  rw [auxiliaryCoordinateLinearMap, LinearMap.comp_apply, auxiliaryRealSubmoduleElementResult]


/-- An auxiliary universally quantified assertion. -/
theorem auxiliaryUniversalResultE (f : auxiliaryRealSubmoduleC →ₗ[ℝ] realMatrixSpace)
    (hf : ∀ A : realMatrixSubmonoid, f.comp (auxiliaryRealRepresentationB A) = (realConjugationRepresentation A).comp f) (A : realMatrixSubmonoid) :
    (auxiliaryCoordinateLinearMap f).comp (realConjugationRepresentation A) = (realConjugationRepresentation A).comp (auxiliaryCoordinateLinearMap f) := by
  refine LinearMap.ext fun M => ?_
  have hpt := LinearMap.congr_fun (hf A) (auxiliaryRealSubmoduleLinearMap M)
  simp only [LinearMap.comp_apply] at hpt
  simp only [auxiliaryCoordinateLinearMap, LinearMap.comp_apply]
  rw [auxiliaryActionResultF, hpt]


/-- An auxiliary universally quantified assertion. -/
@[source_ref "Chapter4/Problem4.12.11" (role := supporting)]
theorem auxiliaryUniversalResultA (f : auxiliaryRealSubmoduleC →ₗ[ℝ] realMatrixSpace)
    (hf : ∀ A : realMatrixSubmonoid, f.comp (auxiliaryRealRepresentationB A) = (realConjugationRepresentation A).comp f) :
    ∃ K μ : ℝ,
      (∀ x : auxiliaryRealSubmoduleC, (x : realMatrixSpace) ∈ auxiliaryRealSubmoduleA → f x = K • (x : realMatrixSpace)) ∧
      (∀ y : auxiliaryRealSubmoduleC, (y : realMatrixSpace) ∈ auxiliaryRealSubmoduleD → f y = μ • (y : realMatrixSpace)) ∧
      (∀ x : auxiliaryRealSubmoduleC, f x ∈ auxiliaryRealSubmoduleC) := by
  obtain ⟨K, μ, hK, hμ, hsym⟩ := auxiliaryEndomorphismResultA (auxiliaryCoordinateLinearMap f) (auxiliaryUniversalResultE f hf)
  refine ⟨K, μ, fun x hx => ?_, fun y hy => ?_, fun x => ?_⟩
  · rw [← auxiliaryUniversalResultD f x]; exact hK _ hx
  · rw [← auxiliaryUniversalResultD f y]; exact hμ _ hy
  · rw [← auxiliaryUniversalResultD f x]; exact hsym _ x.2


/-- An auxiliary universally quantified assertion. -/
@[source_ref "Chapter4/Problem4.12.11" (role := supporting)]
theorem auxiliaryUniversalResultB (f : auxiliaryRealSubmoduleC →ₗ[ℝ] realMatrixSpace)
    (hf : ∀ A : realMatrixSubmonoid, f.comp (auxiliaryRealRepresentationB A) = (realConjugationRepresentation A).comp f) :
    ∃ K μ : ℝ, ∀ x y : auxiliaryRealSubmoduleC, (x : realMatrixSpace) ∈ auxiliaryRealSubmoduleA → (y : realMatrixSpace) ∈ auxiliaryRealSubmoduleD →
      f (x + y) = K • (x : realMatrixSpace) + μ • (y : realMatrixSpace) := by
  obtain ⟨K, μ, hK, hμ, -⟩ := auxiliaryUniversalResultA f hf
  exact ⟨K, μ, fun x y hx hy => by rw [map_add, hK x hx, hμ y hy]⟩


/-- An auxiliary universally quantified assertion. -/
@[source_ref "Chapter4/Problem4.12.11" (role := supporting)]
theorem auxiliaryUniversalResultC (f : auxiliaryRealSubmoduleC →ₗ[ℝ] realMatrixSpace)
    (hf : ∀ A : realMatrixSubmonoid, f.comp (auxiliaryRealRepresentationB A) = (realConjugationRepresentation A).comp f) :
    ∃ K μ : ℝ, ∀ d : auxiliaryRealSubmoduleC, ∃ x ∈ auxiliaryRealSubmoduleA, ∃ y ∈ auxiliaryRealSubmoduleD,
      (d : realMatrixSpace) = x + y ∧ f d = K • x + μ • y := by
  obtain ⟨K, μ, hK, hμ, -⟩ := auxiliaryUniversalResultA f hf
  refine ⟨K, μ, fun d => ?_⟩
  have hd : (d : realMatrixSpace) ∈ auxiliaryRealSubmoduleA ⊔ auxiliaryRealSubmoduleD := by
    rw [auxiliaryConjunction.1]; exact d.2
  rw [Submodule.mem_sup] at hd
  obtain ⟨x, hx, y, hy, hxy⟩ := hd
  refine ⟨x, hx, y, hy, hxy.symm, ?_⟩
  have hdxy : d = (⟨x, auxiliaryRealSubmoduleA_le_auxiliaryRealSubmodule hx⟩ : auxiliaryRealSubmoduleC) + ⟨y, auxiliaryRealSubmoduleD_le_auxiliaryRealSubmoduleC hy⟩ :=
    Subtype.ext (by simpa using hxy.symm)
  rw [hdxy, map_add, hK _ hx, hμ _ hy]

end RepresentationTheory.MatrixConjugationActions

/-- An auxiliary type whose internal description is not exposed by the displayed formal type. -/
alias _root_.RepresentationTheory.MatrixConjugationActions.AuxiliaryType010680 := _root_.RepresentationTheory.MatrixConjugationActions.realMatrixSpace

/-- An auxiliary type whose internal description is not exposed by the displayed formal type. -/
alias _root_.RepresentationTheory.MatrixConjugationActions.AuxiliaryType010681 := _root_.RepresentationTheory.MatrixConjugationActions.complexMatrixSpace

/-- An auxiliary statement whose formal type was unavailable. -/
alias _root_.RepresentationTheory.MatrixConjugationActions.auxiliaryUnavailableStatementOne := _root_.RepresentationTheory.MatrixConjugationActions.auxiliaryMatrixAssertionA

/-- An auxiliary statement whose formal type was unavailable. -/
alias _root_.RepresentationTheory.MatrixConjugationActions.auxiliaryUnavailableStatementThree := _root_.RepresentationTheory.MatrixConjugationActions.auxiliaryMatrixAssertionC

/-- An auxiliary statement whose formal type was unavailable. -/
alias _root_.RepresentationTheory.MatrixConjugationActions.auxiliaryUnavailableStatementTwo := _root_.RepresentationTheory.MatrixConjugationActions.auxiliaryMatrixAssertionB
