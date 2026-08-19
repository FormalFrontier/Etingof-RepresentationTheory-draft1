/-
Copyright (c) 2026 mathlib-initiative. All rights reserved.
Released under Apache 2.0 license as described in the file LICENCE.
Authors: mathlib-initiative
-/

import RepresentationTheory.AuxiliaryIntegerMatrixProperty
import RepresentationTheory.AuxiliaryIntegerMatrixTransform
import RepresentationTheory.AuxiliaryFiniteIndexIntegerFunction
import RepresentationTheory.AuxiliaryIntegerVectorTransforms
import RepresentationTheory.AuxiliaryFiniteDimensionalFamily
import RepresentationTheory.QuiverRepresentation.Auxiliary
import RepresentationTheory.Alignment.Attribute

/-- Evaluate the integer vector obtained by successively applying coordinate reflections indexed by a list. -/
def RepresentationTheory.LinearAlgebra.IntegerMatrixReflections.iteratedCoordinateReflection (n : ℕ) (A : Matrix (Fin n) (Fin n) ℤ)
    (vertices : List (Fin n)) (v : Fin n → ℤ) : Fin n → ℤ :=
  vertices.foldl (fun d i => RepresentationTheory.AuxiliaryIntegerVectorTransforms.auxiliaryCoordinateTransform n A i d) v

namespace RepresentationTheory.LinearAlgebra.IntegerMatrixReflections

open Finset Matrix

variable {n : ℕ} {adj : Matrix (Fin n) (Fin n) ℤ}

/-- The matrix obtained from a symmetric integer matrix by the specified transform is symmetric. -/
lemma matrixTransform_isSymm (hadj : adj.IsSymm) :
    (RepresentationTheory.AuxiliaryIntegerMatrixTransform.auxiliaryTransform n adj).IsSymm := by
  change (RepresentationTheory.AuxiliaryIntegerMatrixTransform.auxiliaryTransform n adj)ᵀ = RepresentationTheory.AuxiliaryIntegerMatrixTransform.auxiliaryTransform n adj
  unfold RepresentationTheory.AuxiliaryIntegerMatrixTransform.auxiliaryTransform
  rw [Matrix.transpose_sub, Matrix.transpose_smul, Matrix.transpose_one]
  rw [show adjᵀ = adj from hadj]

/-- A coordinate reflection leaves every coordinate other than the reflected coordinate unchanged. -/
lemma coordinateReflection_apply_of_ne {A : Matrix (Fin n) (Fin n) ℤ}
    (v : Fin n → ℤ) (i j : Fin n) (hij : j ≠ i) :
    RepresentationTheory.AuxiliaryIntegerVectorTransforms.auxiliaryCoordinateTransform n A i v j = v j := by
  simp [RepresentationTheory.AuxiliaryIntegerVectorTransforms.auxiliaryCoordinateTransform, RepresentationTheory.AuxiliaryIntegerVectorTransforms.auxiliaryVectorTransform, Pi.sub_apply,
    hij]

/-- For a symmetric matrix, the reflected coordinate equals its original value minus the corresponding coordinate of the matrix-vector product. -/
lemma coordinateReflection_apply_self {A : Matrix (Fin n) (Fin n) ℤ}
    (hA : A.IsSymm) (v : Fin n → ℤ) (i : Fin n) :
    RepresentationTheory.AuxiliaryIntegerVectorTransforms.auxiliaryCoordinateTransform n A i v i = v i - (A.mulVec v) i := by

  have symm : ∀ j, A j i = A i j := fun j => congr_fun (congr_fun hA i) j
  have key : dotProduct v (A.mulVec (Pi.single i 1)) = (A.mulVec v) i := by
    simp only [dotProduct, mulVec, Pi.single_apply,
      mul_ite, mul_one, mul_zero, Finset.sum_ite_eq', Finset.mem_univ, ite_true]
    exact Finset.sum_congr rfl fun j _ => by rw [symm j]; ring
  simp only [RepresentationTheory.AuxiliaryIntegerVectorTransforms.auxiliaryCoordinateTransform, RepresentationTheory.AuxiliaryIntegerVectorTransforms.auxiliaryVectorTransform, Pi.sub_apply, Pi.smul_apply,
    Pi.single_apply, mul_one, key, ite_true, smul_eq_mul]

/-- For a symmetric matrix, the coordinate sum after reflection is the original coordinate sum minus the selected coordinate of the matrix-vector product. -/
lemma sum_coordinateReflection {A : Matrix (Fin n) (Fin n) ℤ}
    (hA : A.IsSymm) (v : Fin n → ℤ) (i : Fin n) :
    ∑ j : Fin n, RepresentationTheory.AuxiliaryIntegerVectorTransforms.auxiliaryCoordinateTransform n A i v j = (∑ j : Fin n, v j) - (A.mulVec v) i := by
  have : ∀ j, RepresentationTheory.AuxiliaryIntegerVectorTransforms.auxiliaryCoordinateTransform n A i v j =
      v j + (if j = i then -(A.mulVec v) i else 0) := by
    intro j
    by_cases h : j = i
    · subst h; rw [coordinateReflection_apply_self hA]; simp; ring
    · rw [coordinateReflection_apply_of_ne v i j h]; simp [h]
  simp_rw [this, Finset.sum_add_distrib, Finset.sum_ite_eq', Finset.mem_univ, if_true]
  ring

/-- Under the stated matrix condition, a coordinate reflection preserves the quadratic form defined by the matrix. -/
lemma quadraticForm_coordinateReflection
    (hDynkin : RepresentationTheory.AuxiliaryIntegerMatrixProperty.IsAuxiliaryMatrix n adj) (v : Fin n → ℤ) (i : Fin n) :
    dotProduct (RepresentationTheory.AuxiliaryIntegerVectorTransforms.auxiliaryCoordinateTransform n (RepresentationTheory.AuxiliaryIntegerMatrixTransform.auxiliaryTransform n adj) i v)
      ((RepresentationTheory.AuxiliaryIntegerMatrixTransform.auxiliaryTransform n adj).mulVec (RepresentationTheory.AuxiliaryIntegerVectorTransforms.auxiliaryCoordinateTransform n (RepresentationTheory.AuxiliaryIntegerMatrixTransform.auxiliaryTransform n adj) i v)) =
    dotProduct v ((RepresentationTheory.AuxiliaryIntegerMatrixTransform.auxiliaryTransform n adj).mulVec v) := by
  set A := RepresentationTheory.AuxiliaryIntegerMatrixTransform.auxiliaryTransform n adj with hA_def
  have hAsymm := matrixTransform_isSymm hDynkin.1
  have symm_ij : ∀ j, A j i = A i j := fun j => congr_fun (congr_fun hAsymm i) j
  set c := (A.mulVec v) i

  have hc : dotProduct v (A.mulVec (Pi.single i (1 : ℤ))) = c := by
    simp only [dotProduct, mulVec, Pi.single_apply, mul_ite, mul_one, mul_zero,
      Finset.sum_ite_eq', Finset.mem_univ, ite_true]
    exact Finset.sum_congr rfl fun j _ => by rw [symm_ij j]; ring

  have hs : RepresentationTheory.AuxiliaryIntegerVectorTransforms.auxiliaryCoordinateTransform n A i v = v - c • (Pi.single i (1 : ℤ)) := by
    ext j
    simp only [RepresentationTheory.AuxiliaryIntegerVectorTransforms.auxiliaryCoordinateTransform, RepresentationTheory.AuxiliaryIntegerVectorTransforms.auxiliaryVectorTransform, Pi.sub_apply, Pi.smul_apply, hc]

  have hAii : A i i = 2 := by
    simp only [hA_def, RepresentationTheory.AuxiliaryIntegerMatrixTransform.auxiliaryTransform, Matrix.sub_apply, Matrix.smul_apply,
      Matrix.one_apply]
    have := hDynkin.2.1 i; simp_all

  have hBaa : dotProduct (Pi.single i (1 : ℤ)) (A.mulVec (Pi.single i (1 : ℤ))) = 2 := by
    simp only [dotProduct, mulVec, Pi.single_apply, mul_ite, mul_one, mul_zero,
      ite_mul, one_mul, zero_mul, Finset.sum_ite_eq', Finset.mem_univ, ite_true]
    exact hAii

  rw [hs]
  simp only [Matrix.mulVec_sub, Matrix.mulVec_smul]
  simp only [sub_dotProduct, dotProduct_sub, smul_dotProduct, dotProduct_smul]

  have hBav : dotProduct (Pi.single i (1 : ℤ)) (A.mulVec v) = c := by
    simp only [dotProduct, mulVec, Pi.single_apply, ite_mul, one_mul, zero_mul,
      Finset.sum_ite_eq', Finset.mem_univ, ite_true]; rfl
  rw [hc, hBaa, hBav]
  ring

/-- Reflecting a nonnegative integer vector preserves nonnegativity when the selected matrix-product coordinate is at most the selected vector coordinate. -/
lemma coordinateReflection_nonneg {A : Matrix (Fin n) (Fin n) ℤ}
    (hA : A.IsSymm) (d : Fin n → ℤ) (k : Fin n)
    (hd_pos : ∀ i, 0 ≤ d i) (hk : (A.mulVec d) k ≤ d k) :
    ∀ i, 0 ≤ RepresentationTheory.AuxiliaryIntegerVectorTransforms.auxiliaryCoordinateTransform n A k d i := by
  intro i
  by_cases h : i = k
  · subst h; rw [coordinateReflection_apply_self hA]; linarith
  · rw [coordinateReflection_apply_of_ne d k i h]; exact hd_pos i

/-- Under the stated matrix condition, reflecting a vector of quadratic value two at any coordinate does not produce the zero vector. -/
lemma coordinateReflection_ne_zero_of_quadraticForm_eq_two
    (hDynkin : RepresentationTheory.AuxiliaryIntegerMatrixProperty.IsAuxiliaryMatrix n adj) (v : Fin n → ℤ) (k : Fin n)
    (hv_root : dotProduct v ((RepresentationTheory.AuxiliaryIntegerMatrixTransform.auxiliaryTransform n adj).mulVec v) = 2) :
    RepresentationTheory.AuxiliaryIntegerVectorTransforms.auxiliaryCoordinateTransform n (RepresentationTheory.AuxiliaryIntegerMatrixTransform.auxiliaryTransform n adj) k v ≠ 0 := by
  intro h
  have hB := quadraticForm_coordinateReflection hDynkin v k
  rw [h] at hB

  have : dotProduct (0 : Fin n → ℤ) ((RepresentationTheory.AuxiliaryIntegerMatrixTransform.auxiliaryTransform n adj).mulVec (0 : Fin n → ℤ)) = 0 := by
    simp [dotProduct]
  linarith

/-- The coordinate sum of a nonnegative nonzero integer vector is at least one. -/
lemma one_le_sum_of_nonneg_of_ne_zero
    (d : Fin n → ℤ) (hd_pos : ∀ i, 0 ≤ d i) (hd_nonzero : d ≠ 0) :
    1 ≤ ∑ i : Fin n, d i := by
  by_contra h; push Not at h
  have hsum0 : ∑ i : Fin n, d i = 0 := by
    have := Finset.sum_nonneg (fun i (_ : i ∈ Finset.univ) => hd_pos i); omega
  have : ∀ i, d i = 0 := fun i =>
    (Finset.sum_eq_zero_iff_of_nonneg (fun j _ => hd_pos j)).mp hsum0 i (Finset.mem_univ i)
  exact hd_nonzero (funext this)

/-- A nonnegative nonzero integer vector whose coordinates sum to one is a coordinate vector. -/
lemma eq_single_of_nonneg_of_sum_eq_one
    (d : Fin n → ℤ) (hd_pos : ∀ i, 0 ≤ d i) (hd_nonzero : d ≠ 0)
    (hd_sum : ∑ i : Fin n, d i = 1) :
    ∃ p, d = RepresentationTheory.AuxiliaryFiniteIndexIntegerFunction.auxiliaryValue n p := by
  simp only [RepresentationTheory.AuxiliaryFiniteIndexIntegerFunction.auxiliaryValue]
  have ⟨p, hp⟩ : ∃ p, d p = 1 := by
    by_contra h; push Not at h

    have hne1 : ∀ i, d i ≠ 1 := h
    have ⟨i, hi⟩ : ∃ i, 0 < d i := by
      by_contra h'; push Not at h'
      exact hd_nonzero (funext fun i => le_antisymm (h' i) (hd_pos i))
    have hi2 : 2 ≤ d i := by have := hne1 i; omega
    have : 2 ≤ ∑ j : Fin n, d j :=
      le_trans hi2 (Finset.single_le_sum (fun j _ => hd_pos j) (Finset.mem_univ i))
    linarith
  refine ⟨p, funext fun i => ?_⟩
  by_cases h : i = p
  · simp [h, hp]
  · simp only [Pi.single_apply, if_neg h]

    have h1 : d i + d p ≤ ∑ j : Fin n, d j := by
      calc d i + d p = ∑ j ∈ ({i, p} : Finset (Fin n)), d j := by
            rw [Finset.sum_pair h]
        _ ≤ ∑ j : Fin n, d j :=
            Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _)
              (fun j _ _ => hd_pos j)
    linarith [hd_pos i]

/-- For a nonnegative nonzero integer vector of quadratic value two and total sum at least two, some coordinate of the matrix product is positive and no larger than the corresponding vector coordinate. -/
lemma exists_pos_matrixMulVec_le_of_quadraticForm_eq_two
    (hDynkin : RepresentationTheory.AuxiliaryIntegerMatrixProperty.IsAuxiliaryMatrix n adj) (d : Fin n → ℤ)
    (hd_pos : ∀ i, 0 ≤ d i) (hd_nonzero : d ≠ 0)
    (hd_root : dotProduct d ((RepresentationTheory.AuxiliaryIntegerMatrixTransform.auxiliaryTransform n adj).mulVec d) = 2)
    (hd_sum : 2 ≤ ∑ i : Fin n, d i) :
    ∃ k, 0 < (RepresentationTheory.AuxiliaryIntegerMatrixTransform.auxiliaryTransform n adj).mulVec d k ∧
         (RepresentationTheory.AuxiliaryIntegerMatrixTransform.auxiliaryTransform n adj).mulVec d k ≤ d k := by
  set A := RepresentationTheory.AuxiliaryIntegerMatrixTransform.auxiliaryTransform n adj with hA_def
  set Ad := A.mulVec d
  by_contra hcon; push Not at hcon

  have ⟨k₀, hdk₀, hAdk₀⟩ : ∃ k, 0 < d k ∧ 0 < Ad k := by
    by_contra hall; push Not at hall

    have : ∀ k, d k * Ad k ≤ 0 := fun k => by
      by_cases hdk : 0 < d k
      · exact mul_nonpos_of_nonneg_of_nonpos (le_of_lt hdk) (by linarith [hall k hdk])
      · have : d k = 0 := le_antisymm (by linarith) (hd_pos k)
        simp [this]
    have hle := Finset.sum_nonpos (fun k (_ : k ∈ Finset.univ) => this k)
    simp only [dotProduct] at hd_root
    linarith

  have hAdk₀_big : 2 ≤ Ad k₀ := by
    have := hcon k₀ hAdk₀; omega

  set d' : Fin n → ℤ := d - Pi.single k₀ 1
  have hAsymm := matrixTransform_isSymm hDynkin.1

  have symm_k₀ : ∀ j, A j k₀ = A k₀ j := fun j => congr_fun (congr_fun hAsymm k₀) j
  have hBde : dotProduct d (A.mulVec (Pi.single k₀ (1 : ℤ))) = Ad k₀ := by
    simp only [dotProduct, mulVec, Pi.single_apply, mul_ite, mul_one, mul_zero,
      Finset.sum_ite_eq', Finset.mem_univ, ite_true]
    exact Finset.sum_congr rfl fun j _ => by rw [symm_k₀ j]; ring

  have hBed : dotProduct (Pi.single k₀ (1 : ℤ)) (A.mulVec d) = Ad k₀ := by
    simp only [dotProduct, mulVec, Pi.single_apply, ite_mul, one_mul, zero_mul,
      Finset.sum_ite_eq', Finset.mem_univ, ite_true]; rfl

  have hBee : dotProduct (Pi.single k₀ (1 : ℤ)) (A.mulVec (Pi.single k₀ (1 : ℤ))) = 2 := by
    simp only [dotProduct, mulVec, Pi.single_apply, mul_ite, mul_one, mul_zero,
      ite_mul, one_mul, zero_mul, Finset.sum_ite_eq', Finset.mem_univ, ite_true]
    simp only [hA_def, RepresentationTheory.AuxiliaryIntegerMatrixTransform.auxiliaryTransform, Matrix.sub_apply, Matrix.smul_apply,
      Matrix.one_apply]
    have := hDynkin.2.1 k₀; simp_all

  have hBd' : dotProduct d' (A.mulVec d') = 4 - 2 * Ad k₀ := by
    change dotProduct (d - Pi.single k₀ 1) (A.mulVec (d - Pi.single k₀ 1)) = _
    simp only [Matrix.mulVec_sub]
    simp only [sub_dotProduct, dotProduct_sub]
    rw [hd_root, hBde, hBed, hBee]
    ring
  have hBd'_nonpos : dotProduct d' (A.mulVec d') ≤ 0 := by linarith

  by_cases hd'_zero : d' = 0
  ·
    have : d = Pi.single k₀ 1 := by
      have := sub_eq_zero.mp (funext fun j => by exact congr_fun hd'_zero j)
      exact this
    have : ∑ i : Fin n, d i = 1 := by
      rw [this]; simp
    linarith
  ·
    have hpos_def := hDynkin.2.2.2.2
    have hpos := hpos_def d' hd'_zero
    rw [show (2 • (1 : Matrix (Fin n) (Fin n) ℤ) - adj) = A from rfl] at hpos
    linarith

/-- Iteration along a list with a new head is iteration along the tail after reflecting at the head coordinate. -/
lemma iteratedCoordinateReflection_cons (A : Matrix (Fin n) (Fin n) ℤ)
    (k : Fin n) (vertices : List (Fin n)) (v : Fin n → ℤ) :
    iteratedCoordinateReflection n A (k :: vertices) v =
    iteratedCoordinateReflection n A vertices (RepresentationTheory.AuxiliaryIntegerVectorTransforms.auxiliaryCoordinateTransform n A k v) := by
  simp [iteratedCoordinateReflection]

end RepresentationTheory.LinearAlgebra.IntegerMatrixReflections

/-- A nonnegative nonzero integer vector of quadratic value two can be carried to a coordinate vector by a finite sequence of coordinate reflections. -/
@[source_ref "Chapter6/Theorem6.8.1" (role := supporting)]
theorem RepresentationTheory.LinearAlgebra.IntegerMatrixReflections.exists_iteratedCoordinateReflection_eq_single_of_quadraticForm_eq_two
    {n : ℕ} {adj : Matrix (Fin n) (Fin n) ℤ}
    (hDynkin : RepresentationTheory.AuxiliaryIntegerMatrixProperty.IsAuxiliaryMatrix n adj)
    (d : Fin n → ℤ)
    (hd_pos : ∀ i, 0 ≤ d i)
    (hd_nonzero : d ≠ 0)
    (hd_root : dotProduct d ((RepresentationTheory.AuxiliaryIntegerMatrixTransform.auxiliaryTransform n adj).mulVec d) = 2) :
    ∃ (vertices : List (Fin n)) (p : Fin n),
      RepresentationTheory.LinearAlgebra.IntegerMatrixReflections.iteratedCoordinateReflection n (RepresentationTheory.AuxiliaryIntegerMatrixTransform.auxiliaryTransform n adj) vertices d =
        RepresentationTheory.AuxiliaryFiniteIndexIntegerFunction.auxiliaryValue n p := by
  set A := RepresentationTheory.AuxiliaryIntegerMatrixTransform.auxiliaryTransform n adj with hA_def
  have hAsymm : A.IsSymm := RepresentationTheory.LinearAlgebra.IntegerMatrixReflections.matrixTransform_isSymm hDynkin.1

  suffices h : ∀ (m : ℕ) (d : Fin n → ℤ),
      (∑ i, d i).toNat = m →
      (∀ i, 0 ≤ d i) → d ≠ 0 →
      dotProduct d (A.mulVec d) = 2 →
      ∃ (vertices : List (Fin n)) (p : Fin n),
        RepresentationTheory.LinearAlgebra.IntegerMatrixReflections.iteratedCoordinateReflection n A vertices d = RepresentationTheory.AuxiliaryFiniteIndexIntegerFunction.auxiliaryValue n p from
    h _ d rfl hd_pos hd_nonzero hd_root
  intro m
  induction m using Nat.strongRecOn with
  | ind m ih =>
    intro d hm hd_pos hd_nonzero hd_root
    have hsum_nonneg : 0 ≤ ∑ i, d i := Finset.sum_nonneg fun i _ => hd_pos i
    have hsum_pos := RepresentationTheory.LinearAlgebra.IntegerMatrixReflections.one_le_sum_of_nonneg_of_ne_zero d hd_pos hd_nonzero
    by_cases hle : ∑ i : Fin n, d i ≤ 1
    ·
      have hd_sum : ∑ i : Fin n, d i = 1 := by omega
      obtain ⟨p, hp⟩ := RepresentationTheory.LinearAlgebra.IntegerMatrixReflections.eq_single_of_nonneg_of_sum_eq_one d hd_pos hd_nonzero hd_sum
      exact ⟨[], p, by simp [RepresentationTheory.LinearAlgebra.IntegerMatrixReflections.iteratedCoordinateReflection, hp]⟩
    ·
      push Not at hle
      have hd_sum2 : 2 ≤ ∑ i : Fin n, d i := by omega
      obtain ⟨k, hk_pos, hk_le⟩ :=
        RepresentationTheory.LinearAlgebra.IntegerMatrixReflections.exists_pos_matrixMulVec_le_of_quadraticForm_eq_two hDynkin d hd_pos hd_nonzero hd_root hd_sum2
      set d' := RepresentationTheory.AuxiliaryIntegerVectorTransforms.auxiliaryCoordinateTransform n A k d with hd'_def
      have hd'_pos := RepresentationTheory.LinearAlgebra.IntegerMatrixReflections.coordinateReflection_nonneg hAsymm d k hd_pos hk_le
      have hd'_nonzero := RepresentationTheory.LinearAlgebra.IntegerMatrixReflections.coordinateReflection_ne_zero_of_quadraticForm_eq_two hDynkin d k hd_root
      have hd'_root : dotProduct d' (A.mulVec d') = 2 :=
        RepresentationTheory.LinearAlgebra.IntegerMatrixReflections.quadraticForm_coordinateReflection hDynkin d k ▸ hd_root
      have hd'_sum : ∑ j, d' j = (∑ j, d j) - (A.mulVec d) k :=
        RepresentationTheory.LinearAlgebra.IntegerMatrixReflections.sum_coordinateReflection hAsymm d k
      have hd'_sum_lt : (∑ j, d' j).toNat < m := by
        have h1 : ∑ j, d' j < ∑ j, d j := by linarith
        have h2 : 0 ≤ ∑ j, d' j := Finset.sum_nonneg fun i _ => hd'_pos i
        omega
      obtain ⟨vertices', p, hp⟩ := ih _ hd'_sum_lt d' rfl hd'_pos hd'_nonzero hd'_root
      exact ⟨k :: vertices', p, by
        rw [RepresentationTheory.LinearAlgebra.IntegerMatrixReflections.iteratedCoordinateReflection_cons]; exact hp⟩
