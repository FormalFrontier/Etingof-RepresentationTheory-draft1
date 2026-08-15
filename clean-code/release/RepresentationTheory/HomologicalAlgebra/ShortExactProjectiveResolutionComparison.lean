/-
Copyright (c) 2026 mathlib-initiative. All rights reserved.
Released under Apache 2.0 license as described in the file LICENCE.
Authors: mathlib-initiative
-/

import RepresentationTheory.HomologicalAlgebra.ProjectiveResolution.ShortExact

/-!
# Comparison maps between short-exact projective resolutions

This module constructs a strict comparison between the projective-resolution short complexes
associated to a morphism of short exact complexes.
-/

universe v u

open CategoryTheory CategoryTheory.Limits Category
open RepresentationTheory.HomologicalAlgebra.ProjectiveResolution.ShortExact

namespace RepresentationTheory.HomologicalAlgebra.ShortExactProjectiveResolutionComparison
namespace ShortExactProjectiveResolutionComparison

variable {C : Type u} [Category.{v} C] [Abelian C]
    {S T : ShortComplex C} (hS : S.ShortExact) (hT : T.ShortExact) (φ : S ⟶ T)
    (P₁ : ProjectiveResolution S.X₁) (P₃ : ProjectiveResolution S.X₃)
    (Q₁ : ProjectiveResolution T.X₁) (Q₃ : ProjectiveResolution T.X₃)

include hS hT φ P₁ P₃ Q₁ Q₃

/-- Constructs the chain map between projective resolutions of the left objects induced by a
morphism of short complexes. -/
noncomputable abbrev leftResolutionMap : P₁.complex ⟶ Q₁.complex :=
  ProjectiveResolution.lift φ.τ₁ P₁ Q₁

/-- Constructs the chain map between projective resolutions of the right objects induced by a
morphism of short complexes. -/
noncomputable abbrev rightResolutionMap : P₃.complex ⟶ Q₃.complex :=
  ProjectiveResolution.lift φ.τ₃ P₃ Q₃

/-- Constructs a morphism from degree zero of the third-term projective resolution to the middle
object of the target short complex. -/
noncomputable def degreeZeroToMiddle : P₃.complex.X 0 ⟶ T.X₂ :=
  @Projective.factorThru C _ (P₃.complex.X 0) S.X₃ S.X₂ (P₃.projective 0)
      (P₃.π.f 0) S.g hS.epi_g ≫ φ.τ₂ -
    (rightResolutionMap φ P₃ Q₃).f 0 ≫
      @Projective.factorThru C _ (Q₃.complex.X 0) T.X₃ T.X₂ (Q₃.projective 0)
        (Q₃.π.f 0) T.g hT.epi_g

set_option linter.unusedSectionVars false in
/-- The degree-zero morphism to the target middle object vanishes after composition with the
target's second differential. -/
lemma degreeZeroToMiddle_g :
    degreeZeroToMiddle (hS := hS) (hT := hT) (φ := φ) (P₃ := P₃) (Q₃ := Q₃) ≫
      T.g = 0 := by
  rw [degreeZeroToMiddle, Preadditive.sub_comp]
  simp only [Category.assoc]
  rw [φ.comm₂₃]
  simp only [Projective.factorThru_comp_assoc, Projective.factorThru_comp]
  rw [sub_eq_zero]
  exact (ProjectiveResolution.lift_commutes_zero φ.τ₃ P₃ Q₃).symm

/-- Constructs a morphism from degree zero of the source third-term resolution to the left object
of the target short complex. -/
noncomputable def degreeZeroLiftToLeft : P₃.complex.X 0 ⟶ T.X₁ := by
  letI : Mono T.f := hT.mono_f
  exact hT.exact.lift
    (degreeZeroToMiddle (hS := hS) (hT := hT) (φ := φ) (P₃ := P₃) (Q₃ := Q₃))
    (degreeZeroToMiddle_g (hS := hS) (hT := hT) (φ := φ)
      (P₁ := P₁) (P₃ := P₃) (Q₁ := Q₁) (Q₃ := Q₃))

/-- The degree-zero lift followed by the target's first differential equals the induced morphism
to its middle object. -/
@[reassoc]
lemma degreeZeroLiftToLeft_f :
    degreeZeroLiftToLeft (hS := hS) (hT := hT) (φ := φ)
        (P₁ := P₁) (P₃ := P₃) (Q₁ := Q₁) (Q₃ := Q₃) ≫ T.f =
      degreeZeroToMiddle (hS := hS) (hT := hT) (φ := φ)
        (P₃ := P₃) (Q₃ := Q₃) := by
  letI : Mono T.f := hT.mono_f
  exact hT.exact.lift_f _ _

/-- Constructs the degree-zero morphism from the source third-term resolution to the target
first-term resolution. -/
noncomputable def crossTermZero : P₃.complex.X 0 ⟶ Q₁.complex.X 0 := by
  exact @Projective.factorThru C _ (P₃.complex.X 0) T.X₁ (Q₁.complex.X 0)
    (P₃.projective 0) (degreeZeroLiftToLeft (hS := hS) (hT := hT) (φ := φ)
      (P₁ := P₁) (P₃ := P₃) (Q₁ := Q₁) (Q₃ := Q₃))
    (Q₁.π.f 0) (epi_of_isColimit_cofork Q₁.isColimitCokernelCofork)

/-- The initial cross term followed by the target resolution projection equals the degree-zero
lift to the target left object. -/
@[reassoc]
lemma crossTermZero_pi :
    crossTermZero (hS := hS) (hT := hT) (φ := φ)
        (P₁ := P₁) (P₃ := P₃) (Q₁ := Q₁) (Q₃ := Q₃) ≫ Q₁.π.f 0 =
      degreeZeroLiftToLeft (hS := hS) (hT := hT) (φ := φ)
        (P₁ := P₁) (P₃ := P₃) (Q₁ := Q₁) (Q₃ := Q₃) :=
  Projective.factorThru_comp _ _

/-- Given a cross term in one degree, constructs a morphism from the next source degree to the
current target degree. -/
noncomputable def liftCrossTerm (n : ℕ)
    (r : P₃.complex.X n ⟶ Q₁.complex.X n) :
    P₃.complex.X (n + 1) ⟶ Q₁.complex.X n :=
  P₃.complex.d (n + 1) n ≫ r +
    CategoryTheory.ShortComplex.ShortExact.connecting hS P₁ P₃ n ≫
      (leftResolutionMap φ P₁ Q₁).f n -
    (rightResolutionMap φ P₃ Q₃).f (n + 1) ≫
      CategoryTheory.ShortComplex.ShortExact.connecting hT Q₁ Q₃ n

set_option backward.isDefEq.respectTransparency false in
/-- At degree zero, the lifted initial cross term vanishes after composition with the target
resolution projection. -/
lemma liftCrossTerm_zero_pi :
    liftCrossTerm hS hT φ P₁ P₃ Q₁ Q₃ 0
      (crossTermZero (hS := hS) (hT := hT) (φ := φ)
        (P₁ := P₁) (P₃ := P₃) (Q₁ := Q₁) (Q₃ := Q₃)) ≫ Q₁.π.f 0 = 0 := by
  letI : Mono T.f := hT.mono_f
  letI : Epi S.g := hS.epi_g
  letI : Epi T.g := hT.epi_g
  let pπ : P₁.complex.X 0 ⟶ S.X₁ := P₁.π.f 0
  let qπ : Q₁.complex.X 0 ⟶ T.X₁ := Q₁.π.f 0
  let aS : P₃.complex.X 0 ⟶ S.X₂ :=
    @Projective.factorThru C _ (P₃.complex.X 0) S.X₃ S.X₂ (P₃.projective 0)
      (P₃.π.f 0) S.g hS.epi_g
  let aT : Q₃.complex.X 0 ⟶ T.X₂ :=
    @Projective.factorThru C _ (Q₃.complex.X 0) T.X₃ T.X₂ (Q₃.projective 0)
      (Q₃.π.f 0) T.g hT.epi_g
  change liftCrossTerm hS hT φ P₁ P₃ Q₁ Q₃ 0
      (crossTermZero hS hT φ P₁ P₃ Q₁ Q₃) ≫ qπ = 0
  have hzero : crossTermZero hS hT φ P₁ P₃ Q₁ Q₃ ≫ qπ =
      degreeZeroLiftToLeft hS hT φ P₁ P₃ Q₁ Q₃ := by
    dsimp only [qπ]
    exact crossTermZero_pi hS hT φ P₁ P₃ Q₁ Q₃
  have hlift : (leftResolutionMap φ P₁ Q₁).f 0 ≫ qπ = pπ ≫ φ.τ₁ := by
    dsimp only [pπ, qπ]
    exact ProjectiveResolution.lift_commutes_zero φ.τ₁ P₁ Q₁
  have htwS : CategoryTheory.ShortComplex.ShortExact.connecting hS P₁ P₃ 0 ≫ pπ ≫ S.f =
      -(P₃.complex.d 1 0) ≫ aS := by
    dsimp only [pπ, aS]
    exact CategoryTheory.ShortComplex.ShortExact.connecting_zero_comp_augmentation_comp_f
      hS P₁ P₃
  have htwT : CategoryTheory.ShortComplex.ShortExact.connecting hT Q₁ Q₃ 0 ≫ qπ ≫ T.f =
      -(Q₃.complex.d 1 0) ≫ aT := by
    dsimp only [qπ, aT]
    exact CategoryTheory.ShortComplex.ShortExact.connecting_zero_comp_augmentation_comp_f
      hT Q₁ Q₃
  have htwSφ : CategoryTheory.ShortComplex.ShortExact.connecting hS P₁ P₃ 0 ≫
      pπ ≫ S.f ≫ φ.τ₂ = (-(P₃.complex.d 1 0) ≫ aS) ≫ φ.τ₂ := by
    simpa only [Category.assoc] using congrArg (fun k => k ≫ φ.τ₂) htwS
  have htwTcomp :
      (rightResolutionMap φ P₃ Q₃).f (0 + 1) ≫
          CategoryTheory.ShortComplex.ShortExact.connecting hT Q₁ Q₃ 0 ≫ qπ ≫ T.f =
        (rightResolutionMap φ P₃ Q₃).f (0 + 1) ≫
          (-(Q₃.complex.d 1 0) ≫ aT) := by
    simpa only [Category.assoc] using congrArg
      (fun k => (rightResolutionMap φ P₃ Q₃).f (0 + 1) ≫ k) htwT
  have hdefect : degreeZeroToMiddle hS hT φ P₃ Q₃ =
      aS ≫ φ.τ₂ - (rightResolutionMap φ P₃ Q₃).f 0 ≫ aT := rfl
  have hcomm : (rightResolutionMap φ P₃ Q₃).f 1 ≫ Q₃.complex.d 1 0 ≫ aT =
      P₃.complex.d 1 0 ≫ (rightResolutionMap φ P₃ Q₃).f 0 ≫ aT := by
    exact HomologicalComplex.Hom.comm_assoc (rightResolutionMap φ P₃ Q₃) 1 0 aT
  rw [liftCrossTerm, Preadditive.sub_comp, Preadditive.add_comp]
  simp only [Category.assoc, hzero, hlift]
  apply (cancel_mono T.f).1
  rw [zero_comp, Preadditive.sub_comp, Preadditive.add_comp]
  simp only [Category.assoc]
  rw [degreeZeroLiftToLeft_f]
  rw [φ.comm₁₂]
  rw [htwSφ, htwTcomp]
  rw [hdefect]
  simp only [Preadditive.comp_sub, Preadditive.neg_comp,
    Preadditive.comp_neg, Category.assoc]
  rw [hcomm]
  abel

/-- An auxiliary definition whose formal type is unavailable in the displayed signature. -/
noncomputable def auxiliaryConstruction :
    ∀ n, Σ' (r : P₃.complex.X n ⟶ Q₁.complex.X n)
      (_r' : P₃.complex.X (n + 1) ⟶ Q₁.complex.X (n + 1)),
        _r' ≫ Q₁.complex.d (n + 1) n = liftCrossTerm hS hT φ P₁ P₃ Q₁ Q₃ n r
  | 0 =>
      let r := crossTermZero (hS := hS) (hT := hT) (φ := φ)
        (P₁ := P₁) (P₃ := P₃) (Q₁ := Q₁) (Q₃ := Q₃)
      let r' := Q₁.exact₀.liftFromProjective
        (liftCrossTerm hS hT φ P₁ P₃ Q₁ Q₃ 0 r)
        (liftCrossTerm_zero_pi hS hT φ P₁ P₃ Q₁ Q₃)
      ⟨r, r', Q₁.exact₀.liftFromProjective_comp _ _⟩
  | n + 1 => by
      let r := (auxiliaryConstruction n).1
      let r' := (auxiliaryConstruction n).2.1
      have hr' : r' ≫ Q₁.complex.d (n + 1) n =
          liftCrossTerm hS hT φ P₁ P₃ Q₁ Q₃ n r :=
        (auxiliaryConstruction n).2.2
      have hz : liftCrossTerm hS hT φ P₁ P₃ Q₁ Q₃ (n + 1) r' ≫
          Q₁.complex.d (n + 1) n = 0 := by
        simp only [liftCrossTerm, Preadditive.sub_comp, Preadditive.add_comp,
          Category.assoc]
        rw [hr']
        simp only [liftCrossTerm, Preadditive.comp_sub, Preadditive.comp_add,
          P₃.complex.d_comp_d_assoc, zero_comp, zero_add]
        rw [HomologicalComplex.Hom.comm]
        rw [CategoryTheory.ShortComplex.ShortExact.connecting_succ_comp_d_assoc]
        rw [← HomologicalComplex.Hom.comm_assoc]
        rw [CategoryTheory.ShortComplex.ShortExact.connecting_succ_comp_d]
        simp only [Preadditive.neg_comp, Preadditive.comp_neg]
        rw [show n + 1 + 1 = n + 2 by omega]
        abel_nf
        rw [neg_one_smul ℤ]
        rw [Category.assoc]
        abel
      let r'' := (Q₁.exact_succ n).liftFromProjective
        (liftCrossTerm hS hT φ P₁ P₃ Q₁ Q₃ (n + 1) r') hz
      exact ⟨r', r'', (Q₁.exact_succ n).liftFromProjective_comp _ _⟩

/-- Defines at each degree a morphism from the source third-term resolution to the target
first-term resolution. -/
noncomputable def crossTerm (n : ℕ) : P₃.complex.X n ⟶ Q₁.complex.X n :=
  (auxiliaryConstruction hS hT φ P₁ P₃ Q₁ Q₃ n).1

/-- The cross term in the successor degree is the first component extracted from the auxiliary
dependent data. -/
lemma crossTerm_succ (n : ℕ) :
    crossTerm hS hT φ P₁ P₃ Q₁ Q₃ (n + 1) =
      (auxiliaryConstruction hS hT φ P₁ P₃ Q₁ Q₃ n).2.1 := rfl

/-- The successor cross term followed by the target differential equals the lifting operation
applied to the current cross term. -/
lemma crossTerm_succ_d (n : ℕ) :
    crossTerm hS hT φ P₁ P₃ Q₁ Q₃ (n + 1) ≫ Q₁.complex.d (n + 1) n =
      liftCrossTerm hS hT φ P₁ P₃ Q₁ Q₃ n
        (crossTerm hS hT φ P₁ P₃ Q₁ Q₃ n) := by
  rw [crossTerm_succ]
  exact (auxiliaryConstruction hS hT φ P₁ P₃ Q₁ Q₃ n).2.2

/-- Defines the degreewise morphism between biproducts of the first- and third-term projective
resolutions. -/
noncomputable def component (n : ℕ) :
    (P₁.complex.X n ⊞ P₃.complex.X n) ⟶ (Q₁.complex.X n ⊞ Q₃.complex.X n) :=
  biprod.map ((leftResolutionMap φ P₁ Q₁).f n) ((rightResolutionMap φ P₃ Q₃).f n) +
    biprod.snd ≫ crossTerm hS hT φ P₁ P₃ Q₁ Q₃ n ≫ biprod.inl

/-- Precomposing the degreewise biproduct comparison with the first inclusion yields the left
resolution map followed by the first inclusion. -/
@[reassoc (attr := simp)]
lemma inl_comp_component (n : ℕ) :
    biprod.inl ≫ component hS hT φ P₁ P₃ Q₁ Q₃ n =
      (leftResolutionMap φ P₁ Q₁).f n ≫ biprod.inl := by
  rw [component, Preadditive.comp_add, biprod.inl_map]
  simp

/-- Precomposing the degreewise biproduct comparison with the second inclusion is the sum of the
right resolution map into the second summand and the cross term into the first. -/
@[reassoc (attr := simp)]
lemma inr_comp_component (n : ℕ) :
    biprod.inr ≫ component hS hT φ P₁ P₃ Q₁ Q₃ n =
      (rightResolutionMap φ P₃ Q₃).f n ≫ biprod.inr +
        crossTerm hS hT φ P₁ P₃ Q₁ Q₃ n ≫ biprod.inl := by
  rw [component, Preadditive.comp_add, biprod.inr_map]
  simp

/-- Postcomposing the degreewise comparison with the first projection gives the sum of the left
resolution component and the cross term on the two source summands. -/
@[reassoc (attr := simp)]
lemma component_fst (n : ℕ) :
    component hS hT φ P₁ P₃ Q₁ Q₃ n ≫ biprod.fst =
      biprod.fst ≫ (leftResolutionMap φ P₁ Q₁).f n +
        biprod.snd ≫ crossTerm hS hT φ P₁ P₃ Q₁ Q₃ n := by
  rw [component, Preadditive.add_comp, biprod.map_fst]
  simp [Category.assoc]

/-- Postcomposing the degreewise comparison with the second projection gives the right resolution
component on the second source summand. -/
@[reassoc (attr := simp)]
lemma component_snd (n : ℕ) :
    component hS hT φ P₁ P₃ Q₁ Q₃ n ≫ biprod.snd =
      biprod.snd ≫ (rightResolutionMap φ P₃ Q₃).f n := by
  rw [component, Preadditive.add_comp, biprod.map_snd]
  simp [Category.assoc]

/-- Successive degreewise comparison morphisms commute with the differentials of the assembled
complexes. -/
lemma component_d (n : ℕ) :
    component hS hT φ P₁ P₃ Q₁ Q₃ (n + 1) ≫
        (CategoryTheory.ShortComplex.ShortExact.middleComplex hT Q₁ Q₃).d (n + 1) n =
      (CategoryTheory.ShortComplex.ShortExact.middleComplex hS P₁ P₃).d (n + 1) n ≫
        component hS hT φ P₁ P₃ Q₁ Q₃ n := by
  simp only [CategoryTheory.ShortComplex.ShortExact.middleComplex, ChainComplex.of_d]
  apply biprod.hom_ext <;> apply biprod.hom_ext'
  all_goals
    simp [crossTerm_succ_d, liftCrossTerm, HomologicalComplex.Hom.comm, Category.assoc,
      Preadditive.add_comp, Preadditive.comp_add]
  all_goals abel

/-- Constructs a morphism between the complexes assembled from the endpoint projective
resolutions of two short exact complexes. -/
noncomputable def complexMap :
    CategoryTheory.ShortComplex.ShortExact.middleComplex hS P₁ P₃ ⟶
      CategoryTheory.ShortComplex.ShortExact.middleComplex hT Q₁ Q₃ :=
  ChainComplex.ofHom (component hS hT φ P₁ P₃ Q₁ Q₃)
    (component_d hS hT φ P₁ P₃ Q₁ Q₃)

/-- Constructs a morphism between the objects associated to short exact complexes with chosen
projective resolutions of their first and third terms. -/
noncomputable def middleResolutionMap :
    CategoryTheory.ShortComplex.ShortExact.resolutionShortComplex hS P₁ P₃ ⟶
      CategoryTheory.ShortComplex.ShortExact.resolutionShortComplex hT Q₁ Q₃ :=
  ShortComplex.homMk
    (leftResolutionMap φ P₁ Q₁)
    (complexMap hS hT φ P₁ P₃ Q₁ Q₃)
    (rightResolutionMap φ P₃ Q₃)
    (by
      apply HomologicalComplex.hom_ext
      intro n
      dsimp [CategoryTheory.ShortComplex.ShortExact.resolutionShortComplex, complexMap,
        CategoryTheory.ShortComplex.ShortExact.inlToMiddleComplex]
      exact (inl_comp_component hS hT φ P₁ P₃ Q₁ Q₃ n).symm)
    (by
      apply HomologicalComplex.hom_ext
      intro n
      dsimp [CategoryTheory.ShortComplex.ShortExact.resolutionShortComplex, complexMap,
        CategoryTheory.ShortComplex.ShortExact.sndFromMiddleComplex]
      exact component_snd hS hT φ P₁ P₃ Q₁ Q₃ n)

-- Clean-room documentation for declarations generated by reassoc.

/-- The factorization of the degree-zero middle morphism through the target's first differential
persists after postcomposition. -/
add_decl_doc degreeZeroLiftToLeft_f_assoc

/-- The projection formula for the initial cross term persists after postcomposition with any
morphism. -/
add_decl_doc crossTermZero_pi_assoc

/-- The first-inclusion formula for the degreewise comparison remains valid after postcomposition
with any morphism. -/
add_decl_doc inl_comp_component_assoc

/-- The second-inclusion formula for the degreewise comparison remains valid after postcomposition
with any morphism. -/
add_decl_doc inr_comp_component_assoc

/-- The formula for the first projection of the degreewise comparison persists after
postcomposition. -/
add_decl_doc component_fst_assoc

/-- The formula for the second projection of the degreewise comparison persists after
postcomposition. -/
add_decl_doc component_snd_assoc

end ShortExactProjectiveResolutionComparison
end RepresentationTheory.HomologicalAlgebra.ShortExactProjectiveResolutionComparison
