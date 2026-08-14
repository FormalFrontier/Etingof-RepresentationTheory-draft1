/-
Copyright (c) 2026 FormalFrontier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENCE.
Authors: FormalFrontier
-/

import Mathlib
import RepresentationTheory.FDRep.GroupAlgebraDecomposition



open Representation CategoryTheory

universe u

variable {k G : Type u} [Field k] [Group G]




/-- The trace of multiplication by the identity on the group algebra is the field cast of the group cardinality. -/
theorem RepresentationTheory.FDRep.RegularRepresentationCharacter.trace_ofMulAction_one [Fintype G] :
    LinearMap.trace k (MonoidAlgebra k G) ((Representation.ofMulAction k G G) 1) =
      (Fintype.card G : k) := by
  rw [map_one, LinearMap.trace_one]
  norm_num [RepresentationTheory.FDRep.GroupAlgebraDecomposition.finrank_monoidAlgebra (k := k) (G := G)]


/-- Multiplication by a nonidentity element has zero trace on the group algebra. -/
theorem RepresentationTheory.FDRep.RegularRepresentationCharacter.trace_ofMulAction_eq_zero_of_ne_one [Finite G] (g : G) (hg : g ≠ 1) :
    LinearMap.trace k (MonoidAlgebra k G) ((Representation.ofMulAction k G G) g) = 0 := by
  classical
  cases nonempty_fintype G
  have key : ∀ h : G, (ofMulAction k G G g (MonoidAlgebra.single h 1)).coeff h = 0 := by
    intro h
    rw [Representation.coeff_ofMulAction]
    change (Finsupp.single h 1) (g⁻¹ • h) = 0
    rw [Finsupp.single_apply, if_neg]
    intro heq
    rw [smul_eq_mul] at heq

    exact hg (inv_eq_one.mp (mul_right_cancel (show g⁻¹ * h = 1 * h by rw [one_mul, ← heq])))
  rw [LinearMap.trace_eq_matrix_trace k (MonoidAlgebra.basis G k)]
  simp only [Matrix.trace, Matrix.diag_apply, LinearMap.toMatrix_apply]
  apply Finset.sum_eq_zero
  intro h _
  change (ofMulAction k G G g (MonoidAlgebra.single h 1)).coeff h = 0
  exact key h

open scoped Classical in

/-- The trace of multiplication by a group element on the group algebra is the group cardinality at the identity and zero otherwise. -/
theorem RepresentationTheory.FDRep.RegularRepresentationCharacter.trace_ofMulAction_eq_ite [Fintype G] (g : G) :
    LinearMap.trace k (MonoidAlgebra k G) ((Representation.ofMulAction k G G) g) =
      if g = 1 then (Fintype.card G : k) else 0 := by
  split
  · subst_vars; exact RepresentationTheory.FDRep.RegularRepresentationCharacter.trace_ofMulAction_one
  · exact RepresentationTheory.FDRep.RegularRepresentationCharacter.trace_ofMulAction_eq_zero_of_ne_one g ‹_›





private lemma stdBasis_repr_apply' [IsAlgClosed k] {n : ℕ}
    (A : Matrix (Fin n) (Fin n) k) (ij : Fin n × Fin n) :
    (Matrix.stdBasis k (Fin n) (Fin n)).repr A ij = A ij.1 ij.2 := by
  simp [Matrix.stdBasis]


private lemma ofMulAction_eq_mulLeft (g : G) :
    (Representation.ofMulAction k G G g : MonoidAlgebra k G →ₗ[k] MonoidAlgebra k G) =
      LinearMap.mulLeft k (MonoidAlgebra.of k G g) := by
  apply (MonoidAlgebra.basis G k).ext
  intro h
  simp [LinearMap.mulLeft_apply, MonoidAlgebra.basis_apply]


private lemma trace_mulLeft_algEquiv [IsAlgClosed k]
    {A B : Type u} [Ring A] [Ring B] [Algebra k A] [Algebra k B]
    [Module.Free k A] [Module.Finite k A] [Module.Free k B] [Module.Finite k B]
    (φ : A ≃ₐ[k] B) (a : A) :
    LinearMap.trace k A (LinearMap.mulLeft k a) =
      LinearMap.trace k B (LinearMap.mulLeft k (φ a)) := by
  have h : φ.toLinearEquiv.conj (LinearMap.mulLeft k a) = LinearMap.mulLeft k (φ a) := by
    ext x; simp [LinearEquiv.conj_apply, LinearMap.mulLeft_apply, map_mul]
  rw [← h]; exact (LinearMap.trace_conj' (LinearMap.mulLeft k a) φ.toLinearEquiv).symm


private lemma trace_mulLeft_matrix [IsAlgClosed k] {n : ℕ}
    (M : Matrix (Fin n) (Fin n) k) :
    LinearMap.trace k (Matrix (Fin n) (Fin n) k) (LinearMap.mulLeft k M) =
      (n : k) * Matrix.trace M := by
  rw [LinearMap.trace_eq_matrix_trace k (Matrix.stdBasis k (Fin n) (Fin n))]
  simp only [Matrix.trace, Matrix.diag_apply, LinearMap.toMatrix_apply,
    LinearMap.mulLeft_apply, stdBasis_repr_apply']
  have key : ∀ x : Fin n × Fin n,
      (M * (Matrix.stdBasis k (Fin n) (Fin n)) x) x.1 x.2 = M x.1 x.1 := by
    intro ⟨a, b⟩; rw [Matrix.stdBasis_eq_single, Matrix.mul_single_apply_same, mul_one]
  simp_rw [key]
  rw [show ∑ x : Fin n × Fin n, M x.1 x.1 = ∑ a : Fin n, ∑ _ : Fin n, M a a from by
    rw [← Finset.sum_product']; rfl]
  simp [Finset.sum_const, Finset.mul_sum]


private lemma trace_mulLeft_pi [IsAlgClosed k] {N : ℕ} {d : Fin N → ℕ}
    (a : ∀ i : Fin N, Matrix (Fin (d i)) (Fin (d i)) k) :
    LinearMap.trace k _ (LinearMap.mulLeft k a) =
      ∑ i, (d i : k) * Matrix.trace (a i) := by
  let B := Pi.basis (fun i => Matrix.stdBasis k (Fin (d i)) (Fin (d i)))
  rw [LinearMap.trace_eq_matrix_trace k B]
  simp only [Matrix.trace, Matrix.diag_apply, LinearMap.toMatrix_apply,
    LinearMap.mulLeft_apply]
  have key : ∀ x : Σ i, Fin (d i) × Fin (d i),
      B.repr (a * B x) x = a x.1 x.2.1 x.2.1 := by
    intro ⟨i, a', b'⟩
    rw [Pi.basis_repr, stdBasis_repr_apply', Pi.basis_apply]
    simp [Pi.mul_apply, Matrix.stdBasis_eq_single,
      Matrix.mul_single_apply_same, mul_one]
  simp_rw [key]
  simp only [Fintype.sum_sigma]
  congr 1; ext i
  rw [show ∑ x : Fin (d i) × Fin (d i), a i x.1 x.1 =
    ∑ a' : Fin (d i), ∑ _ : Fin (d i), a i a' a' from by
    rw [← Finset.sum_product']; rfl]
  simp [Finset.sum_const, Finset.mul_sum]


private lemma representation_character_eq [Fintype G] [IsAlgClosed k] [NeZero (Nat.card G : k)]
    (D : RepresentationTheory.FDRep.GroupAlgebraDecomposition.DecompositionData k G) (i : Fin D.count) (g : G) :
    (D.representation i).character g =
      Matrix.trace (D.matrixBlockHom i (MonoidAlgebra.of k G g)) := by
  change LinearMap.trace k (Fin (D.dimension i) → k) (Matrix.mulVecLin _) = _
  rw [← Matrix.toLin'_apply']; exact Matrix.trace_toLin'_eq _




/-- For an indexed pairwise nonisomorphic simple family, the dimension-weighted sum of character values vanishes at every nonidentity group element. -/
theorem RepresentationTheory.FDRep.RegularRepresentationCharacter.sum_finrank_mul_character_eq_zero_of_ne_one [Fintype G] [IsAlgClosed k] [NeZero (Nat.card G : k)]
    (D : RepresentationTheory.FDRep.GroupAlgebraDecomposition.DecompositionData k G) (V : Fin D.count → FDRep k G)
    (hV : ∀ i, Simple (V i))
    (hinj : ∀ i j, Nonempty ((V i) ≅ (V j)) → i = j)
    (g : G) (hg : g ≠ 1) :
    ∑ i, (Module.finrank k (V i) : k) * (V i).character g = 0 := by

  choose τ hτ using fun j => D.exists_iso_representation_of_simple (V j) (hV j)
  have hτ_inj : Function.Injective τ := by
    intro j₁ j₂ h
    exact hinj j₁ j₂ ⟨(hτ j₁).some ≪≫ (h ▸ (hτ j₂).some.symm)⟩
  have hτ_bij : Function.Bijective τ := Finite.injective_iff_bijective.mp hτ_inj

  have h_col : ∑ i, (D.dimension i : k) * (D.representation i).character g = 0 := by
    simp_rw [representation_character_eq D _ g]
    have h1 : LinearMap.trace k (MonoidAlgebra k G) (LinearMap.mulLeft k (MonoidAlgebra.of k G g)) = 0 := by
      have := RepresentationTheory.FDRep.RegularRepresentationCharacter.trace_ofMulAction_eq_zero_of_ne_one (k := k) g hg
      rwa [ofMulAction_eq_mulLeft] at this
    rw [trace_mulLeft_algEquiv D.groupAlgebraEquivMatrix, trace_mulLeft_pi] at h1
    exact h1

  have hfr : ∀ j, Module.finrank k (V j) = D.dimension (τ j) := by
    intro j; rw [← D.finrank_representation (τ j)]
    exact LinearEquiv.finrank_eq (FDRep.isoToLinearEquiv (hτ j).some)
  have hchar : ∀ j, (V j).character g = (D.representation (τ j)).character g := by
    intro j; exact congr_fun (FDRep.char_iso (hτ j).some) g

  conv_lhs => arg 2; ext j; rw [hfr j, hchar j]
  let τ_equiv := Equiv.ofBijective τ hτ_bij
  rw [show ∑ j, (D.dimension (τ j) : k) * (D.representation (τ j)).character g =
    ∑ i, (D.dimension i : k) * (D.representation i).character g from
    Finset.sum_equiv τ_equiv (fun _ => by simp) (fun _ _ => rfl)]
  exact h_col




private theorem regTrace_eq_card_mul [Fintype G]
    (γ : MonoidAlgebra k G) :
    LinearMap.trace k (MonoidAlgebra k G) (LinearMap.mulLeft k γ) =
      (Fintype.card G : k) * γ.coeff 1 := by
  classical





  suffices h_eq :
      (LinearMap.trace k (MonoidAlgebra k G)).comp
        (Algebra.lmul k (MonoidAlgebra k G)).toLinearMap =
      (Fintype.card G : k) •
        ((Finsupp.lapply (1 : G)).comp (MonoidAlgebra.coeffLinearEquiv k).toLinearMap) by
    exact LinearMap.ext_iff.mp h_eq γ
  apply (MonoidAlgebra.basis G k).ext
  intro g
  simp only [LinearMap.comp_apply, AlgHom.toLinearMap_apply,
    LinearMap.smul_apply, smul_eq_mul, Finsupp.lapply_apply]

  change LinearMap.trace k (MonoidAlgebra k G) (LinearMap.mulLeft k _) = _
  have := RepresentationTheory.FDRep.RegularRepresentationCharacter.trace_ofMulAction_eq_ite (k := k) g
  rw [ofMulAction_eq_mulLeft] at this
  simp only [MonoidAlgebra.basis_apply]
  change LinearMap.trace k (MonoidAlgebra k G)
      (LinearMap.mulLeft k (MonoidAlgebra.single g 1)) =
    (Fintype.card G : k) * (MonoidAlgebra.single g 1).coeff 1
  rw [MonoidAlgebra.coeff_single]
  convert this using 1
  · rfl
  · split_ifs with h <;> simp [Finsupp.single_apply, h]


/-- The field cast of each indexed natural number supplied by the data is nonzero. -/
theorem RepresentationTheory.FDRep.GroupAlgebraDecomposition.DecompositionData.cast_indexedNat_ne_zero [Fintype G] [IsAlgClosed k]
    [Invertible (Fintype.card G : k)] [NeZero (Nat.card G : k)]
    (D : RepresentationTheory.FDRep.GroupAlgebraDecomposition.DecompositionData k G) (i : Fin D.count) :
    (D.dimension i : k) ≠ 0 := by
  classical
  intro hd_zero

  set e : MonoidAlgebra k G := D.groupAlgebraEquivMatrix.symm (Pi.single i 1) with he_def

  have he_ne : e ≠ 0 := by
    intro h
    have h1 : Pi.single i (1 : Matrix (Fin (D.dimension i)) (Fin (D.dimension i)) k) = 0 :=
      D.groupAlgebraEquivMatrix.symm.injective (h.trans (map_zero _).symm)
    haveI := D.dimension_neZero i
    haveI : Nonempty (Fin (D.dimension i)) := ⟨⟨0, Nat.pos_of_ne_zero (NeZero.ne _)⟩⟩
    exact one_ne_zero ((Pi.single_eq_same i 1).symm.trans (congr_fun h1 i))

  have he_ann : ∀ β : MonoidAlgebra k G, (e * β).coeff 1 = 0 := by
    intro β

    have hiso : D.groupAlgebraEquivMatrix (e * β) = Pi.single i (D.matrixBlockHom i β) := by
      change D.groupAlgebraEquivMatrix (D.groupAlgebraEquivMatrix.symm (Pi.single i 1) * β) = _
      rw [map_mul, AlgEquiv.apply_symm_apply]
      funext j
      simp only [Pi.mul_apply]
      by_cases hj : j = i
      · subst hj
        rw [Pi.single_eq_same, Pi.single_eq_same, one_mul]
        rfl
      · rw [Pi.single_eq_of_ne hj, Pi.single_eq_of_ne hj, zero_mul]
    have hrt_wd : LinearMap.trace k (MonoidAlgebra k G) (LinearMap.mulLeft k (e * β)) =
        (D.dimension i : k) * Matrix.trace (D.matrixBlockHom i β) := by
      conv_lhs => rw [trace_mulLeft_algEquiv D.groupAlgebraEquivMatrix (e * β)]
      rw [trace_mulLeft_pi]

      have h_zero : ∀ j, j ≠ i → (D.groupAlgebraEquivMatrix (e * β)) j = 0 := fun j hj => by
        rw [hiso]; exact Pi.single_eq_of_ne hj _
      have h_same : (D.groupAlgebraEquivMatrix (e * β)) i = D.matrixBlockHom i β := by
        rw [hiso]; exact Pi.single_eq_same i _
      rw [Finset.sum_eq_single i
        (fun j _ hj => by rw [h_zero j hj]; simp)
        (fun h => absurd (Finset.mem_univ i) h), h_same]

    have hrt_reg := regTrace_eq_card_mul (e * β)

    rw [hrt_wd, hd_zero, zero_mul] at hrt_reg
    exact (mul_eq_zero.mp hrt_reg.symm).resolve_left (Invertible.ne_zero _)

  have hecoeff : e.coeff ≠ 0 := by
    intro h
    apply he_ne
    apply MonoidAlgebra.coeff_inj.mp
    simpa using h
  obtain ⟨g, hg⟩ := Finsupp.support_nonempty_iff.mpr hecoeff
  rw [Finsupp.mem_support_iff] at hg

  have : (e * MonoidAlgebra.single g⁻¹ (1 : k)).coeff (1 : G) = e.coeff g := by
    rw [MonoidAlgebra.coeff_mul_single_apply, inv_inv, one_mul, mul_one]
  exact hg (this ▸ he_ann _)
