/-
Copyright (c) 2026 mathlib-initiative. All rights reserved.
Released under Apache 2.0 license as described in the file LICENCE.
Authors: mathlib-initiative
-/

import Mathlib.CategoryTheory.Abelian.Projective.Resolution
import Mathlib.Algebra.Homology.HomologicalComplexAbelian
import Mathlib.Algebra.Homology.HomologicalComplexBiprod
import Mathlib.Algebra.Homology.ShortComplex.ShortExact
import Mathlib.Algebra.Homology.HomologySequenceLemmas
import Mathlib.Algebra.Homology.SingleHomology
import Mathlib.CategoryTheory.Abelian.DiagramLemmas.Four
import RepresentationTheory.Alignment.Attribute

set_option backward.isDefEq.respectTransparency false

/-!
# Projective resolutions for short exact complexes

This module constructs compatible projective resolutions for short exact complexes in abelian
categories with enough projectives. It defines the associated middle complex, connecting maps,
augmentation, and short exact sequence of complexes.
-/

universe v u

open CategoryTheory Category Limits

namespace RepresentationTheory.HomologicalAlgebra.ProjectiveResolution.ShortExact

section Augmentation

variable {C : Type u} [Category.{v} C] [Abelian C]
    {S : ShortComplex C} (hS : S.ShortExact)
    (P₁ : ProjectiveResolution S.X₁) (P₃ : ProjectiveResolution S.X₃)

/-- The degree-zero augmentation from the biproduct of the outer resolutions to the middle object. -/
noncomputable def CategoryTheory.ShortComplex.ShortExact.middleAugmentationZero :
    P₁.complex.X 0 ⊞ P₃.complex.X 0 ⟶ S.X₂ :=
  haveI := hS.epi_g
  biprod.desc (P₁.π.f 0 ≫ S.f) (Projective.factorThru (P₃.π.f 0) S.g)

/-- The first biproduct inclusion followed by the middle augmentation is the left augmentation followed by the first short-complex map. -/
@[reassoc (attr := simp)]
lemma CategoryTheory.ShortComplex.ShortExact.inl_comp_middleAugmentationZero :
    biprod.inl ≫ CategoryTheory.ShortComplex.ShortExact.middleAugmentationZero hS P₁ P₃ = P₁.π.f 0 ≫ S.f := by
  simp [CategoryTheory.ShortComplex.ShortExact.middleAugmentationZero]

/-- The second inclusion followed by the middle augmentation and the second short-complex map equals the right augmentation. -/
@[reassoc (attr := simp)]
lemma CategoryTheory.ShortComplex.ShortExact.inr_comp_middleAugmentationZero_comp_g :
    haveI := hS.epi_g
    (biprod.inr ≫ CategoryTheory.ShortComplex.ShortExact.middleAugmentationZero hS P₁ P₃) ≫ S.g = P₃.π.f 0 := by
  haveI := hS.epi_g
  simp [CategoryTheory.ShortComplex.ShortExact.middleAugmentationZero, Projective.factorThru_comp]

/-- The middle augmentation followed by the second short-complex map is the right projection followed by the right augmentation. -/
@[reassoc]
lemma CategoryTheory.ShortComplex.ShortExact.middleAugmentationZero_comp_g :
    CategoryTheory.ShortComplex.ShortExact.middleAugmentationZero hS P₁ P₃ ≫ S.g = biprod.snd ≫ P₃.π.f 0 := by
  haveI := hS.epi_g
  ext
  · simp [CategoryTheory.ShortComplex.ShortExact.middleAugmentationZero]
  · simp [CategoryTheory.ShortComplex.ShortExact.middleAugmentationZero, Projective.factorThru_comp]

/-! ## Connecting morphisms and the middle complex -/

/-- The degree-one differential followed by the degree-zero augmentation forms an exact short complex. -/
lemma CategoryTheory.ProjectiveResolution.exact_d_one_augmentation :
    (ShortComplex.mk (P₁.complex.d 1 0) (P₁.π.f 0) P₁.complex_d_comp_π_f_zero).Exact :=
  ShortComplex.exact_of_g_is_cokernel _ P₁.isColimitCokernelCofork

/-- A morphism from degree one of the right projective resolution to the left object. -/
noncomputable def CategoryTheory.ShortComplex.ShortExact.degreeOneToLeft : P₃.complex.X 1 ⟶ S.X₁ :=
  haveI := hS.epi_g
  haveI := hS.mono_f
  hS.exact.lift (-(P₃.complex.d 1 0) ≫ Projective.factorThru (P₃.π.f 0) S.g) (by
    haveI := hS.epi_g
    simp [Projective.factorThru_comp, P₃.complex_d_comp_π_f_zero])

/-- The degree-one-to-left morphism followed by the first map of the short complex equals the stated negative composite. -/
@[reassoc] lemma CategoryTheory.ShortComplex.ShortExact.degreeOneToLeft_comp_f :
    haveI := hS.epi_g
    CategoryTheory.ShortComplex.ShortExact.degreeOneToLeft hS P₃ ≫ S.f
      = -(P₃.complex.d 1 0) ≫ Projective.factorThru (P₃.π.f 0) S.g := by
  haveI := hS.epi_g
  haveI := hS.mono_f
  exact hS.exact.lift_f _ _

/-- The degree-two differential vanishes after the morphism from degree one to the left object. -/
lemma CategoryTheory.ShortComplex.ShortExact.d_comp_degreeOneToLeft :
    P₃.complex.d 2 1 ≫ CategoryTheory.ShortComplex.ShortExact.degreeOneToLeft hS P₃ = 0 := by
  haveI := hS.mono_f
  rw [← cancel_mono S.f, zero_comp, assoc, CategoryTheory.ShortComplex.ShortExact.degreeOneToLeft_comp_f]
  simp [P₃.complex.d_comp_d_assoc]

/-- The connecting morphism from degree one of the right resolution to degree zero of the left resolution. -/
noncomputable def CategoryTheory.ShortComplex.ShortExact.connectingZero : P₃.complex.X 1 ⟶ P₁.complex.X 0 :=
  Projective.factorThru (CategoryTheory.ShortComplex.ShortExact.degreeOneToLeft hS P₃) (P₁.π.f 0)

/-- The degree-zero connecting morphism followed by the left augmentation equals the morphism to the left object. -/
@[reassoc] lemma CategoryTheory.ShortComplex.ShortExact.connectingZero_comp_augmentation :
    CategoryTheory.ShortComplex.ShortExact.connectingZero hS P₁ P₃ ≫ P₁.π.f 0 = CategoryTheory.ShortComplex.ShortExact.degreeOneToLeft hS P₃ :=
  Projective.factorThru_comp _ _

/-- Auxiliary dependent data used in the construction of connecting morphisms. -/
noncomputable def CategoryTheory.ShortComplex.ShortExact.connectingAux :
    ∀ n, Σ' (a : P₃.complex.X (n + 1) ⟶ P₁.complex.X n)
      (_b : P₃.complex.X (n + 2) ⟶ P₁.complex.X (n + 1)),
        _b ≫ P₁.complex.d (n + 1) n = -(P₃.complex.d (n + 2) (n + 1)) ≫ a
  | 0 =>
      ⟨CategoryTheory.ShortComplex.ShortExact.connectingZero hS P₁ P₃,
        (CategoryTheory.ProjectiveResolution.exact_d_one_augmentation P₁).liftFromProjective
          (-(P₃.complex.d 2 1) ≫ CategoryTheory.ShortComplex.ShortExact.connectingZero hS P₁ P₃) (by
            simp [CategoryTheory.ShortComplex.ShortExact.connectingZero_comp_augmentation, CategoryTheory.ShortComplex.ShortExact.d_comp_degreeOneToLeft]),
        (CategoryTheory.ProjectiveResolution.exact_d_one_augmentation P₁).liftFromProjective_comp _ _⟩
  | n + 1 => by
      set a := (CategoryTheory.ShortComplex.ShortExact.connectingAux n).1 with hadef
      set b := (CategoryTheory.ShortComplex.ShortExact.connectingAux n).2.1 with hbdef
      have hab : b ≫ P₁.complex.d (n + 1) n = -(P₃.complex.d (n + 2) (n + 1)) ≫ a :=
        (CategoryTheory.ShortComplex.ShortExact.connectingAux n).2.2
      have hk : (-(P₃.complex.d (n + 3) (n + 2)) ≫ b) ≫ P₁.complex.d (n + 1) n = 0 := by
        simp [hab, P₃.complex.d_comp_d_assoc]
      exact ⟨b, (P₁.exact_succ n).liftFromProjective (-(P₃.complex.d (n + 3) (n + 2)) ≫ b) hk,
        (P₁.exact_succ n).liftFromProjective_comp _ _⟩

/-- The connecting morphism from degree one higher in the right resolution to the current degree in the left resolution. -/
noncomputable def CategoryTheory.ShortComplex.ShortExact.connecting (n : ℕ) : P₃.complex.X (n + 1) ⟶ P₁.complex.X n :=
  (CategoryTheory.ShortComplex.ShortExact.connectingAux hS P₁ P₃ n).1

/-- The connecting morphism at a successor index is the first component of the auxiliary dependent data. -/
lemma CategoryTheory.ShortComplex.ShortExact.connecting_succ_eq_connectingAux (n : ℕ) :
    CategoryTheory.ShortComplex.ShortExact.connecting hS P₁ P₃ (n + 1) = (CategoryTheory.ShortComplex.ShortExact.connectingAux hS P₁ P₃ n).2.1 := rfl

/-- A connecting morphism followed by the left differential equals the negative right differential followed by the preceding connecting morphism. -/
@[reassoc]
lemma CategoryTheory.ShortComplex.ShortExact.connecting_succ_comp_d (n : ℕ) :
    CategoryTheory.ShortComplex.ShortExact.connecting hS P₁ P₃ (n + 1) ≫ P₁.complex.d (n + 1) n
      = -(P₃.complex.d (n + 2) (n + 1)) ≫ CategoryTheory.ShortComplex.ShortExact.connecting hS P₁ P₃ n := by
  rw [CategoryTheory.ShortComplex.ShortExact.connecting_succ_eq_connectingAux]; exact (CategoryTheory.ShortComplex.ShortExact.connectingAux hS P₁ P₃ n).2.2

/-- The connecting morphism at index zero is the designated degree-zero connecting morphism. -/
lemma CategoryTheory.ShortComplex.ShortExact.connecting_zero_eq : CategoryTheory.ShortComplex.ShortExact.connecting hS P₁ P₃ 0 = CategoryTheory.ShortComplex.ShortExact.connectingZero hS P₁ P₃ := rfl

/-- The degree-zero connecting morphism followed by the left augmentation and first short-complex map equals the stated negative composite. -/
@[reassoc] lemma CategoryTheory.ShortComplex.ShortExact.connecting_zero_comp_augmentation_comp_f :
    haveI := hS.epi_g
    CategoryTheory.ShortComplex.ShortExact.connecting hS P₁ P₃ 0 ≫ P₁.π.f 0 ≫ S.f
      = -(P₃.complex.d 1 0) ≫ Projective.factorThru (P₃.π.f 0) S.g := by
  haveI := hS.epi_g
  rw [CategoryTheory.ShortComplex.ShortExact.connecting_zero_eq, ← assoc, CategoryTheory.ShortComplex.ShortExact.connectingZero_comp_augmentation, CategoryTheory.ShortComplex.ShortExact.degreeOneToLeft_comp_f]

/-- The differential between consecutive biproducts of the two outer projective resolutions. -/
noncomputable def CategoryTheory.ShortComplex.ShortExact.middleDifferential (n : ℕ) :
    P₁.complex.X (n + 1) ⊞ P₃.complex.X (n + 1) ⟶ P₁.complex.X n ⊞ P₃.complex.X n :=
  biprod.lift (biprod.desc (P₁.complex.d (n + 1) n) (CategoryTheory.ShortComplex.ShortExact.connecting hS P₁ P₃ n))
    (biprod.desc 0 (P₃.complex.d (n + 1) n))

/-- Composing the middle differential with the first projection gives the indicated biproduct map. -/
@[reassoc (attr := simp)] lemma CategoryTheory.ShortComplex.ShortExact.middleDifferential_comp_fst (n : ℕ) :
    CategoryTheory.ShortComplex.ShortExact.middleDifferential hS P₁ P₃ n ≫ biprod.fst
      = biprod.desc (P₁.complex.d (n + 1) n) (CategoryTheory.ShortComplex.ShortExact.connecting hS P₁ P₃ n) := by
  simp [CategoryTheory.ShortComplex.ShortExact.middleDifferential]

/-- Composing the middle differential with the second projection gives zero and the second outer differential. -/
@[reassoc (attr := simp)] lemma CategoryTheory.ShortComplex.ShortExact.middleDifferential_comp_snd (n : ℕ) :
    CategoryTheory.ShortComplex.ShortExact.middleDifferential hS P₁ P₃ n ≫ biprod.snd = biprod.desc 0 (P₃.complex.d (n + 1) n) := by
  simp [CategoryTheory.ShortComplex.ShortExact.middleDifferential]

/-- Precomposing the middle differential with the first inclusion gives the first outer differential and zero. -/
@[reassoc (attr := simp)] lemma CategoryTheory.ShortComplex.ShortExact.inl_comp_middleDifferential (n : ℕ) :
    biprod.inl ≫ CategoryTheory.ShortComplex.ShortExact.middleDifferential hS P₁ P₃ n = biprod.lift (P₁.complex.d (n + 1) n) 0 := by
  apply biprod.hom_ext <;> simp

/-- Precomposing the middle differential with the second inclusion gives the connecting map and the second outer differential. -/
@[reassoc (attr := simp)] lemma CategoryTheory.ShortComplex.ShortExact.inr_comp_middleDifferential (n : ℕ) :
    biprod.inr ≫ CategoryTheory.ShortComplex.ShortExact.middleDifferential hS P₁ P₃ n
      = biprod.lift (CategoryTheory.ShortComplex.ShortExact.connecting hS P₁ P₃ n) (P₃.complex.d (n + 1) n) := by
  apply biprod.hom_ext <;> simp

/-- Two consecutive middle differentials compose to zero. -/
lemma CategoryTheory.ShortComplex.ShortExact.middleDifferential_d_squared (n : ℕ) :
    CategoryTheory.ShortComplex.ShortExact.middleDifferential hS P₁ P₃ (n + 1) ≫ CategoryTheory.ShortComplex.ShortExact.middleDifferential hS P₁ P₃ n = 0 := by
  apply biprod.hom_ext' <;> apply biprod.hom_ext <;>
    simp [CategoryTheory.ShortComplex.ShortExact.connecting_succ_comp_d, biprod.lift_desc, P₁.complex.d_comp_d, P₃.complex.d_comp_d]

/-- The chain complex associated to a short exact complex and projective resolutions of its outer objects. -/
noncomputable def CategoryTheory.ShortComplex.ShortExact.middleComplex : ChainComplex C ℕ :=
  ChainComplex.of (fun n => P₁.complex.X n ⊞ P₃.complex.X n) (CategoryTheory.ShortComplex.ShortExact.middleDifferential hS P₁ P₃)
    (CategoryTheory.ShortComplex.ShortExact.middleDifferential_d_squared hS P₁ P₃)

/-- Every object of the associated middle chain complex is projective. -/
instance CategoryTheory.ShortComplex.ShortExact.middleComplex_projective (n : ℕ) :
    Projective ((CategoryTheory.ShortComplex.ShortExact.middleComplex hS P₁ P₃).X n) := by
  dsimp [CategoryTheory.ShortComplex.ShortExact.middleComplex, ChainComplex.of]
  infer_instance

/-- The degree-zero middle differential vanishes after the middle augmentation map. -/
lemma CategoryTheory.ShortComplex.ShortExact.middleDifferential_zero_comp_middleAugmentationZero :
    CategoryTheory.ShortComplex.ShortExact.middleDifferential hS P₁ P₃ 0 ≫ CategoryTheory.ShortComplex.ShortExact.middleAugmentationZero hS P₁ P₃ = 0 := by
  haveI := hS.epi_g
  apply biprod.hom_ext'
  · rw [CategoryTheory.ShortComplex.ShortExact.inl_comp_middleDifferential_assoc, comp_zero]
    simp only [CategoryTheory.ShortComplex.ShortExact.middleAugmentationZero, biprod.lift_desc, zero_comp, add_zero]
    rw [← assoc, P₁.complex_d_comp_π_f_zero, zero_comp]
  · rw [CategoryTheory.ShortComplex.ShortExact.inr_comp_middleDifferential_assoc, comp_zero]
    simp only [CategoryTheory.ShortComplex.ShortExact.middleAugmentationZero, biprod.lift_desc]
    rw [CategoryTheory.ShortComplex.ShortExact.connecting_zero_comp_augmentation_comp_f]
    simp

/-! ## Chain maps and a short exact complex -/

/-- The chain morphism from the left projective resolution into the associated middle complex. -/
noncomputable def CategoryTheory.ShortComplex.ShortExact.inlToMiddleComplex : P₁.complex ⟶ CategoryTheory.ShortComplex.ShortExact.middleComplex hS P₁ P₃ :=
  ChainComplex.ofHom
    (fun i => (biprod.inl : P₁.complex.X i ⟶ P₁.complex.X i ⊞ P₃.complex.X i))
    (fun n => by
      simp only [CategoryTheory.ShortComplex.ShortExact.middleComplex, ChainComplex.of_d, CategoryTheory.ShortComplex.ShortExact.inl_comp_middleDifferential]
      apply biprod.hom_ext <;> simp)

/-- The chain morphism from the associated middle complex to the right projective resolution. -/
noncomputable def CategoryTheory.ShortComplex.ShortExact.sndFromMiddleComplex : CategoryTheory.ShortComplex.ShortExact.middleComplex hS P₁ P₃ ⟶ P₃.complex :=
  ChainComplex.ofHom
    (fun i => (biprod.snd : P₁.complex.X i ⊞ P₃.complex.X i ⟶ P₃.complex.X i))
    (fun n => by
      simp only [CategoryTheory.ShortComplex.ShortExact.middleComplex, ChainComplex.of_d, CategoryTheory.ShortComplex.ShortExact.middleDifferential_comp_snd]
      apply biprod.hom_ext' <;> simp)

/-- Each component of the chain morphism into the middle complex is the first biproduct inclusion. -/
@[simp] lemma CategoryTheory.ShortComplex.ShortExact.inlToMiddleComplex_f (i : ℕ) :
    (CategoryTheory.ShortComplex.ShortExact.inlToMiddleComplex hS P₁ P₃).f i
      = (biprod.inl : P₁.complex.X i ⟶ P₁.complex.X i ⊞ P₃.complex.X i) := rfl

/-- Each component of the chain morphism from the middle complex is the second biproduct projection. -/
@[simp] lemma CategoryTheory.ShortComplex.ShortExact.sndFromMiddleComplex_f (i : ℕ) :
    (CategoryTheory.ShortComplex.ShortExact.sndFromMiddleComplex hS P₁ P₃).f i
      = (biprod.snd : P₁.complex.X i ⊞ P₃.complex.X i ⟶ P₃.complex.X i) := rfl

/-- The inclusion into the middle complex followed by its projection to the right resolution is zero. -/
lemma CategoryTheory.ShortComplex.ShortExact.inlToMiddleComplex_comp_sndFromMiddleComplex :
    CategoryTheory.ShortComplex.ShortExact.inlToMiddleComplex hS P₁ P₃ ≫ CategoryTheory.ShortComplex.ShortExact.sndFromMiddleComplex hS P₁ P₃ = 0 := by
  ext n
  simp

/-- The short complex of chain complexes built from the two outer projective resolutions and their associated middle complex. -/
noncomputable def CategoryTheory.ShortComplex.ShortExact.resolutionShortComplex : ShortComplex (ChainComplex C ℕ) :=
  ShortComplex.mk (CategoryTheory.ShortComplex.ShortExact.inlToMiddleComplex hS P₁ P₃) (CategoryTheory.ShortComplex.ShortExact.sndFromMiddleComplex hS P₁ P₃) (CategoryTheory.ShortComplex.ShortExact.inlToMiddleComplex_comp_sndFromMiddleComplex hS P₁ P₃)

/-- A splitting of the short complex of resolutions after evaluation in any degree. -/
noncomputable def CategoryTheory.ShortComplex.ShortExact.resolutionShortComplex_splitting (i : ℕ) :
    ((CategoryTheory.ShortComplex.ShortExact.resolutionShortComplex hS P₁ P₃).map
      (HomologicalComplex.eval C (ComplexShape.down ℕ) i)).Splitting :=
  ShortComplex.Splitting.ofHasBinaryBiproduct (P₁.complex.X i) (P₃.complex.X i)

/-- The short complex of projective-resolution chain complexes is short exact. -/
@[source_ref "Chapter8/Problem8.2.6" (role := supporting)]
lemma CategoryTheory.ShortComplex.ShortExact.resolutionShortComplex_shortExact :
    (CategoryTheory.ShortComplex.ShortExact.resolutionShortComplex hS P₁ P₃).ShortExact :=
  HomologicalComplex.shortExact_of_degreewise_shortExact _
    (fun i => (CategoryTheory.ShortComplex.ShortExact.resolutionShortComplex_splitting hS P₁ P₃ i).shortExact)

/-! ## Augmentation and projective resolution -/

/-- The chain morphism from the associated middle complex to the middle object concentrated in degree zero. -/
noncomputable def CategoryTheory.ShortComplex.ShortExact.middleAugmentation :
    CategoryTheory.ShortComplex.ShortExact.middleComplex hS P₁ P₃ ⟶ (ChainComplex.single₀ C).obj S.X₂ :=
  (ChainComplex.toSingle₀Equiv _ _).symm
    ⟨CategoryTheory.ShortComplex.ShortExact.middleAugmentationZero hS P₁ P₃, by
      have hd : (CategoryTheory.ShortComplex.ShortExact.middleComplex hS P₁ P₃).d 1 0 = CategoryTheory.ShortComplex.ShortExact.middleDifferential hS P₁ P₃ 0 := by
        simp only [CategoryTheory.ShortComplex.ShortExact.middleComplex]; exact ChainComplex.of_d _ _ 0
      rw [hd, CategoryTheory.ShortComplex.ShortExact.middleDifferential_zero_comp_middleAugmentationZero]⟩

/-- The degree-zero component of the middle augmentation chain morphism is the degree-zero augmentation. -/
@[simp] lemma CategoryTheory.ShortComplex.ShortExact.middleAugmentation_f_zero :
    (CategoryTheory.ShortComplex.ShortExact.middleAugmentation hS P₁ P₃).f 0 = CategoryTheory.ShortComplex.ShortExact.middleAugmentationZero hS P₁ P₃ := by
  simp [CategoryTheory.ShortComplex.ShortExact.middleAugmentation]

/-- Every positive-degree component of the middle augmentation chain morphism is zero. -/
@[simp] lemma CategoryTheory.ShortComplex.ShortExact.middleAugmentation_f_succ (n : ℕ) :
    (CategoryTheory.ShortComplex.ShortExact.middleAugmentation hS P₁ P₃).f (n + 1) = 0 :=
  (HomologicalComplex.isZero_single_obj_X (ComplexShape.down ℕ) 0 S.X₂ (n + 1)
    (by simp)).eq_of_tgt _ _

/-- The short complex of chain complexes concentrated in degree zero associated to a short complex. -/
noncomputable def CategoryTheory.ShortComplex.singleShortComplex : ShortComplex (ChainComplex C ℕ) :=
  S.map (ChainComplex.single₀ C)

include hS in
/-- Degree-zero concentration preserves short exactness of a short complex. -/
lemma CategoryTheory.ShortComplex.singleShortComplex_shortExact : (CategoryTheory.ShortComplex.singleShortComplex (S := S)).ShortExact :=
  ShortComplex.ShortExact.map_of_exact hS (ChainComplex.single₀ C)

/-- A morphism from the short complex of resolutions to the corresponding concentrated short complex. -/
noncomputable def CategoryTheory.ShortComplex.ShortExact.resolutionShortComplexToSingle :
    CategoryTheory.ShortComplex.ShortExact.resolutionShortComplex hS P₁ P₃ ⟶ CategoryTheory.ShortComplex.singleShortComplex (S := S) :=
  ShortComplex.homMk P₁.π (CategoryTheory.ShortComplex.ShortExact.middleAugmentation hS P₁ P₃) P₃.π
    (by
      apply HomologicalComplex.hom_ext; intro n
      obtain _ | n := n <;>
        simp [CategoryTheory.ShortComplex.ShortExact.resolutionShortComplex, CategoryTheory.ShortComplex.singleShortComplex, ShortComplex.map])
    (by
      apply HomologicalComplex.hom_ext; intro n
      obtain _ | n := n <;>
        simp [CategoryTheory.ShortComplex.ShortExact.resolutionShortComplex, CategoryTheory.ShortComplex.singleShortComplex, ShortComplex.map, CategoryTheory.ShortComplex.ShortExact.middleAugmentationZero_comp_g])

/-- The middle augmentation chain morphism is a quasi-isomorphism. -/
instance CategoryTheory.ShortComplex.ShortExact.middleAugmentation_quasiIso : QuasiIso (CategoryTheory.ShortComplex.ShortExact.middleAugmentation hS P₁ P₃) := by
  have hS₁ := CategoryTheory.ShortComplex.ShortExact.resolutionShortComplex_shortExact hS P₁ P₃
  have hS₂ := CategoryTheory.ShortComplex.singleShortComplex_shortExact hS
  rw [quasiIso_iff]
  rintro (_ | n)
  · rw [quasiIsoAt_iff_isIso_homologyMap]
    have hmono : Mono (HomologicalComplex.homologyMap (CategoryTheory.ShortComplex.singleShortComplex (S := S)).f 0) := by
      haveI := hS.mono_f
      refine (hS₂.homology_exact₁ 1 0 (by simp)).mono_g ?_
      exact (HomologicalComplex.isZero_single_obj_homology _ 0 S.X₃ 1 (by norm_num)).eq_of_src _ _
    have hepi : Epi (HomologicalComplex.homologyMap (CategoryTheory.ShortComplex.ShortExact.resolutionShortComplex hS P₁ P₃).g 0) := by
      haveI := hS₁.epi_g
      exact HomologicalComplex.epi_homologyMap_of_epi_of_not_rel _ 0 (by simp)
    haveI : Mono (HomologicalComplex.homologyMap (CategoryTheory.ShortComplex.ShortExact.middleAugmentation hS P₁ P₃) 0) :=
      ShortComplex.mono_of_mono_of_mono_of_mono
        ((HomologicalComplex.homologyFunctor C (ComplexShape.down ℕ) 0).mapShortComplex.map
          (CategoryTheory.ShortComplex.ShortExact.resolutionShortComplexToSingle hS P₁ P₃)) (hS₁.homology_exact₂ 0) hmono
        (inferInstanceAs (Mono (HomologicalComplex.homologyMap P₁.π 0)))
        (inferInstanceAs (Mono (HomologicalComplex.homologyMap P₃.π 0)))
    haveI : Epi (HomologicalComplex.homologyMap (CategoryTheory.ShortComplex.ShortExact.middleAugmentation hS P₁ P₃) 0) :=
      ShortComplex.epi_of_epi_of_epi_of_epi
        ((HomologicalComplex.homologyFunctor C (ComplexShape.down ℕ) 0).mapShortComplex.map
          (CategoryTheory.ShortComplex.ShortExact.resolutionShortComplexToSingle hS P₁ P₃)) (hS₂.homology_exact₂ 0) hepi
        (inferInstanceAs (Epi (HomologicalComplex.homologyMap P₁.π 0)))
        (inferInstanceAs (Epi (HomologicalComplex.homologyMap P₃.π 0)))
    exact isIso_of_mono_of_epi _
  · rw [quasiIsoAt_iff_exactAt' _ _ (ChainComplex.exactAt_succ_single_obj _ _)]
    exact hS₁.exactAt_X₂ (n + 1) (P₁.complex_exactAt_succ n) (P₃.complex_exactAt_succ n)

/-- A projective resolution of the middle object obtained from resolutions of the outer objects. -/
@[source_ref "Chapter8/Problem8.2.6" (role := supporting)]
noncomputable def CategoryTheory.ShortComplex.ShortExact.middleProjectiveResolution : ProjectiveResolution S.X₂ where
  complex := CategoryTheory.ShortComplex.ShortExact.middleComplex hS P₁ P₃
  π := CategoryTheory.ShortComplex.ShortExact.middleAugmentation hS P₁ P₃

end Augmentation

/-- A short exact complex admits compatible projective resolutions once resolutions of its outer objects are fixed. -/
theorem CategoryTheory.ShortComplex.ShortExact.exists_projectiveResolution {C : Type u} [Category.{v} C] [Abelian C] [EnoughProjectives C]
    {S : ShortComplex C} (hS : S.ShortExact)
    (P₁ : ProjectiveResolution S.X₁) (P₃ : ProjectiveResolution S.X₃) :
    ∃ (P₂ : ProjectiveResolution S.X₂)
      (α : P₁.complex ⟶ P₂.complex) (β : P₂.complex ⟶ P₃.complex)
      (w : α ≫ β = 0),
      (ShortComplex.mk α β w).ShortExact ∧
      α.f 0 ≫ P₂.π.f 0 = P₁.π.f 0 ≫ S.f ∧
      β.f 0 ≫ P₃.π.f 0 = P₂.π.f 0 ≫ S.g :=
  ⟨CategoryTheory.ShortComplex.ShortExact.middleProjectiveResolution hS P₁ P₃, CategoryTheory.ShortComplex.ShortExact.inlToMiddleComplex hS P₁ P₃, CategoryTheory.ShortComplex.ShortExact.sndFromMiddleComplex hS P₁ P₃,
    CategoryTheory.ShortComplex.ShortExact.inlToMiddleComplex_comp_sndFromMiddleComplex hS P₁ P₃, CategoryTheory.ShortComplex.ShortExact.resolutionShortComplex_shortExact hS P₁ P₃,
    by simp [CategoryTheory.ShortComplex.ShortExact.middleProjectiveResolution],
    by simp [CategoryTheory.ShortComplex.ShortExact.middleProjectiveResolution, CategoryTheory.ShortComplex.ShortExact.middleAugmentationZero_comp_g]⟩


-- Clean-room documentation for declarations generated by reassoc.
/-- The first-projection formula for the middle differential remains valid after postcomposition. -/
add_decl_doc CategoryTheory.ShortComplex.ShortExact.middleDifferential_comp_fst_assoc

/-- The first-inclusion formula for the middle differential remains valid after postcomposition. -/
add_decl_doc CategoryTheory.ShortComplex.ShortExact.inl_comp_middleDifferential_assoc

/-- The second-inclusion formula for the middle differential remains valid after postcomposition. -/
add_decl_doc CategoryTheory.ShortComplex.ShortExact.inr_comp_middleDifferential_assoc

/-- The second-projection formula for the middle differential remains valid after postcomposition. -/
add_decl_doc CategoryTheory.ShortComplex.ShortExact.middleDifferential_comp_snd_assoc

/-- The formula for the degree-one-to-left morphism followed by the first map persists after postcomposition. -/
add_decl_doc CategoryTheory.ShortComplex.ShortExact.degreeOneToLeft_comp_f_assoc

/-- The degree-zero connecting and augmentation identity remains valid after postcomposition. -/
add_decl_doc CategoryTheory.ShortComplex.ShortExact.connectingZero_comp_augmentation_assoc

/-- The connecting-differential identity remains valid after postcomposition. -/
add_decl_doc CategoryTheory.ShortComplex.ShortExact.connecting_succ_comp_d_assoc

/-- The degree-zero connecting, augmentation, and first-map identity persists after postcomposition. -/
add_decl_doc CategoryTheory.ShortComplex.ShortExact.connecting_zero_comp_augmentation_comp_f_assoc

/-- The middle-augmentation formula for the second short-complex map remains valid after postcomposition. -/
add_decl_doc CategoryTheory.ShortComplex.ShortExact.middleAugmentationZero_comp_g_assoc

/-- The first-inclusion formula for the middle augmentation persists after postcomposition. -/
add_decl_doc CategoryTheory.ShortComplex.ShortExact.inl_comp_middleAugmentationZero_assoc

/-- The second-inclusion formula for the middle augmentation and second map persists after postcomposition. -/
add_decl_doc CategoryTheory.ShortComplex.ShortExact.inr_comp_middleAugmentationZero_comp_g_assoc

end RepresentationTheory.HomologicalAlgebra.ProjectiveResolution.ShortExact

/-- An auxiliary statement whose displayed formal type contains an elided term. -/
alias _root_.RepresentationTheory.HomologicalAlgebra.ProjectiveResolution.ShortExact.Auxiliary.statement020386 := _root_.RepresentationTheory.HomologicalAlgebra.ProjectiveResolution.ShortExact.CategoryTheory.ProjectiveResolution.exact_d_one_augmentation

/-- An auxiliary statement whose displayed formal type is unavailable. -/
alias _root_.RepresentationTheory.HomologicalAlgebra.ProjectiveResolution.ShortExact.Auxiliary.statement020412 := _root_.RepresentationTheory.HomologicalAlgebra.ProjectiveResolution.ShortExact.CategoryTheory.ShortComplex.ShortExact.connectingAux
