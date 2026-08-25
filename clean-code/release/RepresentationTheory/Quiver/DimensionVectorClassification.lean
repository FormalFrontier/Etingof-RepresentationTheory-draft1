/-
Copyright (c) 2026 mathlib-initiative. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: mathlib-initiative
-/

import RepresentationTheory.AuxiliaryIntegerMatrixProperty
import RepresentationTheory.AuxiliaryIntegerMatrixTransform
import RepresentationTheory.AuxiliaryIntegerMatrixVectorProperty
import RepresentationTheory.IntegerMatrixVectorPredicates
import RepresentationTheory.AuxiliaryFiniteDimensionalFamily
import RepresentationTheory.QuiverRepresentation.Auxiliary
import RepresentationTheory.Quiver.LinearAlgebra.Auxiliary
import RepresentationTheory.LinearAlgebra.Matrix.TwoIdentitySub
import RepresentationTheory.Quiver.MatrixOrientation
import RepresentationTheory.AuxiliaryQuiverRepresentationRelations
import RepresentationTheory.AuxiliaryQuiverRepresentationDimensions
import RepresentationTheory.Alignment.Attribute






















namespace RepresentationTheory.Quiver.DimensionVectorClassification

section Finiteness



/-- For a nonzero integer vector, its dot product with the image under twice the identity matrix minus the adjacency matrix is at least two. -/
theorem two_le_dot_mulVec_two_smul_one_sub_adj_of_ne_zero
    {n : ℕ} {adj : Matrix (Fin n) (Fin n) ℤ}
    (hDynkin : RepresentationTheory.AuxiliaryIntegerMatrixProperty.IsAuxiliaryMatrix n adj)
    (x : Fin n → ℤ) (hx : x ≠ 0) :
    2 ≤ dotProduct x ((2 • (1 : Matrix (Fin n) (Fin n) ℤ) - adj).mulVec x) := by
  have hpos := hDynkin.2.2.2.2 x hx
  have heven := RepresentationTheory.LinearAlgebra.Matrix.TwoIdentitySub.Matrix.even_dotProduct_mulVec_two_smul_one_sub n adj hDynkin.1 hDynkin.2.1 x
  obtain ⟨k, hk⟩ := heven
  rw [hk] at hpos ⊢
  omega




private theorem cartan_mulVec_injective
    {n : ℕ} {adj : Matrix (Fin n) (Fin n) ℤ}
    (hDynkin : RepresentationTheory.AuxiliaryIntegerMatrixProperty.IsAuxiliaryMatrix n adj) :
    Function.Injective (2 • (1 : Matrix (Fin n) (Fin n) ℤ) - adj).mulVec := by
  intro x y hxy
  by_contra hne
  have hne' : x - y ≠ 0 := sub_ne_zero.mpr hne
  have hpos := hDynkin.2.2.2.2 (x - y) hne'
  have hzero : (2 • (1 : Matrix (Fin n) (Fin n) ℤ) - adj).mulVec (x - y) = 0 := by
    rw [Matrix.mulVec_sub]; exact sub_eq_zero.mpr hxy
  simp only [dotProduct, hzero, Pi.zero_apply, mul_zero, Finset.sum_const_zero] at hpos
  omega



private lemma dotProduct_mulVec_comm
    {n : ℕ} (C : Matrix (Fin n) (Fin n) ℤ)
    (hCsymm : C.IsSymm) (x y : Fin n → ℤ) :
    dotProduct y (C.mulVec x) = dotProduct x (C.mulVec y) := by
  simp only [dotProduct, Matrix.mulVec]
  simp_rw [Finset.mul_sum]
  rw [Finset.sum_comm]
  congr 1; ext i; congr 1; ext j
  rw [hCsymm.apply j i]; ring



private lemma bilinear_expand_sub
    {n : ℕ} (C : Matrix (Fin n) (Fin n) ℤ)
    (hCsymm : C.IsSymm) (x y : Fin n → ℤ) :
    dotProduct (x - y) (C.mulVec (x - y)) =
    dotProduct x (C.mulVec x) - 2 * dotProduct x (C.mulVec y) +
    dotProduct y (C.mulVec y) := by
  rw [Matrix.mulVec_sub, sub_dotProduct, dotProduct_sub, dotProduct_sub]
  have hsym := dotProduct_mulVec_comm C hCsymm x y
  linarith



private lemma bilinear_expand_add
    {n : ℕ} (C : Matrix (Fin n) (Fin n) ℤ)
    (hCsymm : C.IsSymm) (x y : Fin n → ℤ) :
    dotProduct (x + y) (C.mulVec (x + y)) =
    dotProduct x (C.mulVec x) + 2 * dotProduct x (C.mulVec y) +
    dotProduct y (C.mulVec y) := by
  rw [Matrix.mulVec_add, add_dotProduct, dotProduct_add, dotProduct_add]
  have hsym := dotProduct_mulVec_comm C hCsymm x y
  linarith




private theorem cartan_mulVec_bounded
    {n : ℕ} {adj : Matrix (Fin n) (Fin n) ℤ}
    (hDynkin : RepresentationTheory.AuxiliaryIntegerMatrixProperty.IsAuxiliaryMatrix n adj)
    (d : Fin n → ℤ) (hd : RepresentationTheory.IntegerMatrixVectorPredicates.integerMatrixVectorCondition n adj d) (i : Fin n) :
    (2 • (1 : Matrix (Fin n) (Fin n) ℤ) - adj).mulVec d i ∈ Set.Icc (-2 : ℤ) 2 := by
  set C := (2 • (1 : Matrix (Fin n) (Fin n) ℤ) - adj)
  have hBdd : dotProduct d (C.mulVec d) = 2 := hd.1.2
  have hCsymm : C.IsSymm := Matrix.IsSymm.ext fun a b => by
    simp only [C, Matrix.sub_apply, Matrix.smul_apply, Matrix.one_apply]
    rw [hDynkin.1.apply a b]; split_ifs <;> omega

  have hBei : dotProduct (Pi.single i 1) (C.mulVec (Pi.single i 1)) = 2 := by
    simp only [dotProduct, C, Matrix.mulVec, Matrix.sub_apply, Matrix.smul_apply,
      Matrix.one_apply, Pi.single_apply]
    simp [Finset.sum_ite_eq', hDynkin.2.1 i]

  have hBeid : dotProduct (Pi.single i 1) (C.mulVec d) = C.mulVec d i := by
    simp [dotProduct, Pi.single_apply, Finset.sum_ite_eq']

  have hBdei : dotProduct d (C.mulVec (Pi.single i 1)) = C.mulVec d i := by

    simp only [dotProduct, Matrix.mulVec, Pi.single_apply, mul_ite, mul_one, mul_zero,
      Finset.sum_ite_eq', Finset.mem_univ, ite_true]

    congr 1; ext a; rw [hCsymm.apply i a]; ring
  constructor
  ·

    have hne : d + Pi.single i 1 ≠ 0 := by
      intro h; have := congr_fun h i
      simp [Pi.add_apply] at this; linarith [hd.2 i]
    have hB := two_le_dot_mulVec_two_smul_one_sub_adj_of_ne_zero hDynkin _ hne
    have hexp := bilinear_expand_add C hCsymm d (Pi.single i 1)
    rw [hBdd, hBdei, hBei] at hexp; linarith
  ·
    by_cases hdeq : d = Pi.single i 1
    · subst hdeq; rw [← hBeid]; linarith [hBei]
    · have hne : d - Pi.single i 1 ≠ 0 := sub_ne_zero.mpr hdeq
      have hB := two_le_dot_mulVec_two_smul_one_sub_adj_of_ne_zero hDynkin _ hne
      have hexp := bilinear_expand_sub C hCsymm d (Pi.single i 1)
      rw [hBdd, hBdei, hBei] at hexp; linarith







/-- Under the stated matrix hypothesis, only finitely many integer vectors satisfy the specified predicate. -/
@[source_ref "Chapter6/Theorem6.5.2" (role := supporting)]
theorem finite_setOf_vectorPredicate
    {n : ℕ} {adj : Matrix (Fin n) (Fin n) ℤ}
    (hDynkin : RepresentationTheory.AuxiliaryIntegerMatrixProperty.IsAuxiliaryMatrix n adj) :
    Set.Finite {d : Fin n → ℤ | RepresentationTheory.IntegerMatrixVectorPredicates.integerMatrixVectorCondition n adj d} := by
  set C := (2 • (1 : Matrix (Fin n) (Fin n) ℤ) - adj)

  have hC_inj := cartan_mulVec_injective hDynkin

  have hbounded : ∀ d ∈ {d : Fin n → ℤ | RepresentationTheory.IntegerMatrixVectorPredicates.integerMatrixVectorCondition n adj d},
      C.mulVec d ∈ Set.Icc (fun (_ : Fin n) => (-2 : ℤ)) (fun _ => 2) := by
    intro d hd
    simp only [Set.mem_Icc, Pi.le_def]
    exact ⟨fun i => (cartan_mulVec_bounded hDynkin d hd i).1,
           fun i => (cartan_mulVec_bounded hDynkin d hd i).2⟩

  have hfin : Set.Finite (Set.Icc (fun (_ : Fin n) => (-2 : ℤ)) (fun _ => 2)) :=
    Set.finite_Icc _ _

  have himg_fin : Set.Finite (C.mulVec '' {d | RepresentationTheory.IntegerMatrixVectorPredicates.integerMatrixVectorCondition n adj d}) :=
    hfin.subset (Set.image_subset_iff.mpr hbounded)

  exact himg_fin.of_finite_image (hC_inj.injOn.mono (Set.subset_univ _))

end Finiteness







/-- A nonnegative nonzero integer vector satisfies the specified predicate when its dot product with the indicated matrix product is two. -/
@[source_ref "Chapter6/Theorem6.5.2" (role := supporting)]
theorem vectorPredicate_of_nonneg_of_dot_mulVec_eq_two
    {n : ℕ} {adj : Matrix (Fin n) (Fin n) ℤ}
    (_hDynkin : RepresentationTheory.AuxiliaryIntegerMatrixProperty.IsAuxiliaryMatrix n adj)
    (d : Fin n → ℤ)
    (hd_pos : ∀ i, 0 ≤ d i)
    (hd_nonzero : d ≠ 0)
    (hd_root : dotProduct d ((RepresentationTheory.AuxiliaryIntegerMatrixTransform.auxiliaryTransform n adj).mulVec d) = 2) :
    RepresentationTheory.IntegerMatrixVectorPredicates.integerMatrixVectorCondition n adj d :=
  ⟨⟨hd_nonzero, by rwa [RepresentationTheory.AuxiliaryIntegerMatrixTransform.auxiliaryTransform] at hd_root⟩, hd_pos⟩

universe u in







/-- Under the given matrix and quiver hypotheses, a vector satisfying the specified predicate is realized as the componentwise finrank vector of an object with the stated property, and any two such objects with that finrank vector are related. -/
@[source_ref "Chapter6/Theorem6.5.2" (role := primary)]
theorem Quiver.exists_finrankVector_and_related_of_vectorPredicate
    {n : ℕ} {adj : Matrix (Fin n) (Fin n) ℤ}
    (hDynkin : RepresentationTheory.AuxiliaryIntegerMatrixProperty.IsAuxiliaryMatrix n adj)
    (k : Type u) [Field k]
    {Q : @Quiver.{0, 0} (Fin n)}
    (hQ : RepresentationTheory.Quiver.MatrixOrientation.IsMatrixOrientation Q adj)
    [∀ (a b : Fin n), Subsingleton (@Quiver.Hom (Fin n) Q a b)]
    (α : Fin n → ℤ) (hα : RepresentationTheory.IntegerMatrixVectorPredicates.integerMatrixVectorCondition n adj α) :

    (∃ (ρ : @RepresentationTheory.CategoryTheory.QuiverLinearDiagrams.AuxiliaryQuiverModuleData.{u, 0, u, _} k (Fin n) _ Q)
      (_ : ∀ v, Module.Free k (ρ.obj v)) (_ : ∀ v, Module.Finite k (ρ.obj v)),
      ρ.AuxiliaryCondition ∧ ∀ v, (α v : ℤ) = ↑(Module.finrank k (ρ.obj v))) ∧

    (∀ (ρ₁ ρ₂ : @RepresentationTheory.CategoryTheory.QuiverLinearDiagrams.AuxiliaryQuiverModuleData.{u, 0, 0, 0} k (Fin n) _ Q)
      [∀ v, Module.Free k (ρ₁.obj v)] [∀ v, Module.Finite k (ρ₁.obj v)]
      [∀ v, Module.Free k (ρ₂.obj v)] [∀ v, Module.Finite k (ρ₂.obj v)],
      ρ₁.AuxiliaryCondition → ρ₂.AuxiliaryCondition →
      (∀ v, (α v : ℤ) = ↑(Module.finrank k (ρ₁.obj v))) →
      (∀ v, (α v : ℤ) = ↑(Module.finrank k (ρ₂.obj v))) →
      Nonempty (RepresentationTheory.CategoryTheory.QuiverLinearDiagrams.AuxiliaryQuiverModuleData.AuxiliaryData ρ₁ ρ₂)) := by
  constructor
  ·
    exact RepresentationTheory.AuxiliaryQuiverRepresentationDimensions.auxiliary_exists_representation_finrank_eq hDynkin α hα k hQ
  ·
    intro ρ₁ ρ₂ _ _ _ _ h₁ h₂ hdim₁ hdim₂
    apply RepresentationTheory.AuxiliaryQuiverRepresentationRelations.auxiliary_nonempty_of_finrank_eq hDynkin hQ ρ₁ ρ₂ h₁ h₂
    intro v
    have h1 := hdim₁ v
    have h2 := hdim₂ v
    omega

universe u in
















/-- Under the given matrix and quiver hypotheses, the predicate on integer vectors has finitely many solutions, holds for the componentwise finrank vector of every object with the stated property, and classifies such objects by that vector up to the specified relation. -/
@[source_ref "Chapter6/Discussion_after_Example6.3.1" (role := supporting),
  source_ref "Chapter6/Theorem6.5.2" (role := primary)]
theorem Quiver.finite_and_finrankVector_classification
    {n : ℕ} {adj : Matrix (Fin n) (Fin n) ℤ}
    (hDynkin : RepresentationTheory.AuxiliaryIntegerMatrixProperty.IsAuxiliaryMatrix n adj)
    (k : Type u) [Field k]
    {Q : @Quiver.{0, 0} (Fin n)}
    (hQ : RepresentationTheory.Quiver.MatrixOrientation.IsMatrixOrientation Q adj)
    [∀ (a b : Fin n), Subsingleton (@Quiver.Hom (Fin n) Q a b)] :

    (Set.Finite {d : Fin n → ℤ | RepresentationTheory.IntegerMatrixVectorPredicates.integerMatrixVectorCondition n adj d}) ∧

    (∀ (ρ : @RepresentationTheory.CategoryTheory.QuiverLinearDiagrams.AuxiliaryQuiverModuleData.{u, 0, 0, 0} k (Fin n) _ Q)
      [∀ v, Module.Free k (ρ.obj v)] [∀ v, Module.Finite k (ρ.obj v)],
      ρ.AuxiliaryCondition →
      RepresentationTheory.IntegerMatrixVectorPredicates.integerMatrixVectorCondition n adj (fun v => (Module.finrank k (ρ.obj v) : ℤ))) ∧

    (∀ (α : Fin n → ℤ), RepresentationTheory.IntegerMatrixVectorPredicates.integerMatrixVectorCondition n adj α →
      (∃ (ρ : @RepresentationTheory.CategoryTheory.QuiverLinearDiagrams.AuxiliaryQuiverModuleData.{u, 0, u, _} k (Fin n) _ Q)
        (_ : ∀ v, Module.Free k (ρ.obj v)) (_ : ∀ v, Module.Finite k (ρ.obj v)),
        ρ.AuxiliaryCondition ∧ ∀ v, (α v : ℤ) = ↑(Module.finrank k (ρ.obj v))) ∧
      (∀ (ρ₁ ρ₂ : @RepresentationTheory.CategoryTheory.QuiverLinearDiagrams.AuxiliaryQuiverModuleData.{u, 0, 0, 0} k (Fin n) _ Q)
        [∀ v, Module.Free k (ρ₁.obj v)] [∀ v, Module.Finite k (ρ₁.obj v)]
        [∀ v, Module.Free k (ρ₂.obj v)] [∀ v, Module.Finite k (ρ₂.obj v)],
        ρ₁.AuxiliaryCondition → ρ₂.AuxiliaryCondition →
        (∀ v, (α v : ℤ) = ↑(Module.finrank k (ρ₁.obj v))) →
        (∀ v, (α v : ℤ) = ↑(Module.finrank k (ρ₂.obj v))) →
        Nonempty (RepresentationTheory.CategoryTheory.QuiverLinearDiagrams.AuxiliaryQuiverModuleData.AuxiliaryData ρ₁ ρ₂))) := by
  refine ⟨finite_setOf_vectorPredicate hDynkin, ?_, ?_⟩
  ·
    intro ρ _ _ hρ
    refine vectorPredicate_of_nonneg_of_dot_mulVec_eq_two hDynkin _
      (fun _ => Int.natCast_nonneg _) ?_ ?_
    ·
      obtain ⟨v, hv⟩ := hρ.1
      intro heq
      haveI : Nontrivial (ρ.obj v) := hv
      have hv0 : Module.finrank k (ρ.obj v) = 0 := by
        have h := congr_fun heq v
        simpa using h



      haveI : Nonempty (Module.Free.ChooseBasisIndex k (ρ.obj v)) :=
        (Module.Free.chooseBasis k (ρ.obj v)).index_nonempty
      have hpos : 0 < Module.finrank k (ρ.obj v) := by
        rw [Module.finrank_eq_card_chooseBasisIndex]
        exact Fintype.card_pos
      omega
    ·
      exact RepresentationTheory.AuxiliaryQuiverConstructions.auxiliary_finrank_quadratic_form_eq_two hDynkin hQ ρ hρ
  ·
    intro α hα
    exact Quiver.exists_finrankVector_and_related_of_vectorPredicate hDynkin k hQ α hα

end RepresentationTheory.Quiver.DimensionVectorClassification
