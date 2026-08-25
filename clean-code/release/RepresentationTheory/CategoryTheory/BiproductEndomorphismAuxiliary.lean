/-
Copyright (c) 2026 mathlib-initiative. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: mathlib-initiative
-/

import RepresentationTheory.Algebra.QuotientMatrixDecomposition
import RepresentationTheory.MoritaEquivalence
import RepresentationTheory.CategoryTheory.Indecomposable
import RepresentationTheory.FGModuleCat.SimpleModules

universe u v w

/-! # Biproduct endomorphism auxiliary results -/

open CategoryTheory CategoryTheory.Limits Module

namespace RepresentationTheory.CategoryTheory.BiproductEndomorphismAuxiliary

private lemma simple_of_functor_obj' {C : Type u} {D : Type v}
    [Category C] [Category D] [HasZeroMorphisms C] [HasZeroMorphisms D]
    (F : C ⥤ D) [F.Full] [F.Faithful] [F.PreservesMonomorphisms]
    (X : C) [Simple (F.obj X)] : Simple X where
  mono_isIso_iff_nonzero {Y} f _ := by
    constructor
    · intro _ h
      haveI : IsIso (F.map f) := Functor.map_isIso F f
      exact (Simple.mono_isIso_iff_nonzero (F.map f)).mp inferInstance (by rw [h]; simp)
    · intro hne
      haveI : Mono (F.map f) := inferInstance
      haveI : IsIso (F.map f) := (Simple.mono_isIso_iff_nonzero (F.map f)).mpr
        (fun h => hne (F.map_injective (by rwa [F.map_zero])))
      exact isIso_of_fully_faithful F f

private lemma simple_of_equivalence' {C : Type u} {D : Type v}
    [Category C] [Category D] [HasZeroMorphisms C] [HasZeroMorphisms D]
    (E : C ≌ D) (X : C) [Simple X] : Simple (E.functor.obj X) := by
  haveI : Simple ((𝟭 C).obj X) := inferInstanceAs (Simple X)
  haveI : Simple (E.inverse.obj (E.functor.obj X)) := Simple.of_iso (E.unitIso.app X).symm
  exact simple_of_functor_obj' E.inverse (E.functor.obj X)

section LinearBiproduct

variable {k : Type w} [Field k]
variable {C : Type u} [Category.{v} C] [Preadditive C] [Linear k C]
  [HasFiniteBiproducts C]
variable {J : Type*} [Fintype J] (f : J → C) (Y : C)

/-- Identifies morphisms from a finite biproduct with their component morphisms to the target. -/
noncomputable def biproductHomToComponentsLinearEquiv :
    (⨁ f ⟶ Y) ≃ₗ[k] ∀ j, (f j ⟶ Y) where
  toFun g j := biproduct.ι f j ≫ g
  invFun g := biproduct.desc g
  map_add' g h := by
    funext j
    simp [Preadditive.comp_add]
  map_smul' r g := by
    funext j
    simp [Linear.comp_smul]
  left_inv g := by
    apply biproduct.hom_ext'
    intro j
    simp
  right_inv g := by
    funext j
    simp

end LinearBiproduct

section CartanSizes

variable {k : Type w} [Field k] [IsAlgClosed k]
variable {C : Type u} [Category.{v} C]
  [RepresentationTheory.CategoryTheory.SubobjectFiniteDimensional.SubobjectFiniteDimensional C]
  [Linear k C]
  [RepresentationTheory.CategoryTheory.Abelian.FiniteLength.SchurFiniteLengthCategory k C]
  [HasFiniteBiproducts C]
variable {ι : Type v} [Fintype ι] [DecidableEq ι]

omit [IsAlgClosed k] in
/-- Under the displayed Hom-dimension condition, the dimension of maps to each member of the target family equals the corresponding value of the natural-number family. -/
theorem auxiliaryFinrankHomEqNatFamilyValue (P S : ι → C) (n : ι → ℕ)
    (hdelta : ∀ i j, finrank k (P i ⟶ S j) = if i = j then 1 else 0) (j : ι) :
    finrank k
      (RepresentationTheory.CategoryTheory.Preadditive.ProjectiveDecomposition.biproductOfMultiplicities
        P n ⟶ S j) = n j := by
  haveI : ∀ p : Σ i, Fin (n i), FiniteDimensional k (P p.1 ⟶ S j) := fun p =>
    RepresentationTheory.CategoryTheory.Abelian.FiniteLength.SchurFiniteLengthCategory.finiteDimensional_hom
      (P p.1) (S j)
  unfold RepresentationTheory.CategoryTheory.Preadditive.ProjectiveDecomposition.biproductOfMultiplicities
  rw [(biproductHomToComponentsLinearEquiv (fun p : Σ i, Fin (n i) => P p.1) (S j)
    (k := k)).finrank_eq, Module.finrank_pi_fintype k]
  simp_rw [hdelta]
  rw [← Finset.univ_sigma_univ, Finset.sum_sigma]
  rw [Finset.sum_eq_single j]
  · simp
  · intro i _ hij
    simp [hij]
  · simp

/-- Under the stated projective and simple family assumptions, constructs the corresponding algebra equivalence to square matrix algebras. -/
theorem auxiliaryQuotientEndomorphismAlgEquivPiMatrixOfSimpleFamily (P S : ι → C)
    (hproj : ∀ i, Projective (P i))
    [RepresentationTheory.CategoryTheory.ProjectiveEpiProperties.HasProjectiveEpiWitnesses
      (⨁ P)]
    (hsimple : ∀ i, Simple (S i))
    (hdistinct : ∀ i j, Nonempty (S i ≅ S j) → i = j)
    (hcomplete : ∀ X : C, Simple X → ∃ i, Nonempty (X ≅ S i))
    (hdelta : ∀ i j, finrank k (P i ⟶ S j) = if i = j then 1 else 0)
    (n : ι → ℕ) (hn : ∀ i, 1 ≤ n i) :
    Nonempty ((((End
      (RepresentationTheory.CategoryTheory.Preadditive.ProjectiveDecomposition.biproductOfMultiplicities
        P n))ᵐᵒᵖ) ⧸
        RepresentationTheory.RingTheory.SimpleModuleAnnihilator.simpleModuleAnnihilator
          ((End
            (RepresentationTheory.CategoryTheory.Preadditive.ProjectiveDecomposition.biproductOfMultiplicities
              P n))ᵐᵒᵖ)) ≃ₐ[k]
      ∀ i, Matrix (Fin (n i)) (Fin (n i)) k) := by
  classical
  let Q :=
    RepresentationTheory.CategoryTheory.Preadditive.ProjectiveDecomposition.biproductOfMultiplicities
      P n
  let B := (End Q)ᵐᵒᵖ
  haveI : ∀ i, Projective (P i) := hproj
  letI : RepresentationTheory.CategoryTheory.ProjectiveEpiProperties.HasProjectiveEpiWitnesses
      Q :=
    RepresentationTheory.CategoryTheory.Preadditive.ProjectiveDecomposition.ofPositiveMultiplicities
      P n hn
  haveI : FiniteDimensional k B :=
    RepresentationTheory.Algebra.QuotientMatrixDecomposition.finiteDimensional_op_end Q
  haveI : IsNoetherianRing B :=
    RepresentationTheory.CategoryTheory.Preadditive.FGModuleEquivalence.opEnd_isNoetherian
      (k := k) Q
  letI :=
    RepresentationTheory.CategoryTheory.Preadditive.FGModuleEquivalence.fgModuleFunctor_isEquivalence
      (k := k) (P := Q)
  let E : C ≌ FGModuleCat.{v} B :=
    RepresentationTheory.CategoryTheory.ProjectiveEpiProperties.HasProjectiveEpiWitnesses.fgModuleFunctor.asEquivalence
  let V : ι → Type v := fun i => Q ⟶ S i
  haveI hVfiniteB : ∀ i, Module.Finite B (V i) := fun i =>
    (inferInstance :
      RepresentationTheory.CategoryTheory.ProjectiveEpiProperties.HasProjectiveEpiWitnesses Q).hom_finite
        (S i)
  haveI hVfiniteK : ∀ i, FiniteDimensional k (V i) := fun i =>
    RepresentationTheory.CategoryTheory.Abelian.FiniteLength.SchurFiniteLengthCategory.finiteDimensional_hom
      Q (S i)
  haveI hVsimple : ∀ i, IsSimpleModule B (V i) := by
    intro i
    haveI : Simple (S i) := hsimple i
    haveI : Simple (E.functor.obj (S i)) := simple_of_equivalence' E (S i)
    change IsSimpleModule B (E.functor.obj (S i))
    exact
      RepresentationTheory.FGModuleCat.SimpleModules.isSimpleModule_carrier_of_simple
        (E.functor.obj (S i))
  have hnoniso : ∀ i j, i ≠ j → IsEmpty (V i ≃ₗ[B] V j) := by
    intro i j hij
    refine ⟨fun e => hij (hdistinct i j ?_)⟩
    have eFG : E.functor.obj (S i) ≅ E.functor.obj (S j) := by
      exact e.toFGModuleCatIso
    exact ⟨E.unitIso.app (S i) ≪≫ E.inverse.mapIso eFG ≪≫
      (E.unitIso.app (S j)).symm⟩
  have hcompleteV : ∀ (W : Type v) [AddCommGroup W] [Module k W] [Module B W]
      [IsScalarTower k B W] [FiniteDimensional k W] [IsSimpleModule B W],
      ∃ i, Nonempty (W ≃ₗ[B] V i) := by
    intro W _ _ _ _ _ _
    letI : Module.Finite B W := Module.Finite.of_restrictScalars_finite k B W
    let X : FGModuleCat.{v} B := FGModuleCat.of B W
    haveI : Simple X := RepresentationTheory.FGModuleCat.SimpleModules.simple_of_isSimpleModule W
    haveI : Simple (E.inverse.obj X) := simple_of_equivalence' E.symm X
    obtain ⟨i, ⟨e⟩⟩ := hcomplete (E.inverse.obj X) inferInstance
    refine ⟨i, ⟨?_⟩⟩
    exact FGModuleCat.isoToLinearEquiv ((E.counitIso.app X).symm ≪≫ E.functor.mapIso e)
  letI : ∀ i, IsScalarTower k B (V i) := fun i => by
    dsimp [V, E]
    set_option backward.isDefEq.respectTransparency false in
      constructor
      intro c b f
      change ((c • b).unop ≫ f) = c • (b.unop ≫ f)
      rw [Algebra.smul_def, MulOpposite.unop_mul, End.mul_def]
      change (((c • 𝟙 Q) ≫ b.unop) ≫ f) = c • (b.unop ≫ f)
      simp
  obtain ⟨e⟩ :=
    RepresentationTheory.Algebra.Semisimplicity.EndomorphismProduct.nonempty_algEquiv_quotient_endProduct
      k B ι V hnoniso hcompleteV
  have hdim : ∀ i, finrank k (V i) = n i := by
    intro i
    change finrank k (Q ⟶ S i) = n i
    exact auxiliaryFinrankHomEqNatFamilyValue P S n hdelta i
  let b : ∀ i, Module.Basis (Fin (n i)) k (V i) := fun i =>
    (Module.finBasis k (V i)).reindex
      (Fintype.equivOfCardEq (by simpa using hdim i))
  let toMat : ∀ i, Module.End k (V i) ≃ₐ[k]
      Matrix (Fin (n i)) (Fin (n i)) k := fun i =>
    LinearMap.toMatrixAlgEquiv (b i)
  exact ⟨e.trans (AlgEquiv.piCongrRight toMat)⟩

/-- Under the stated projective and simple family assumptions, the displayed algebra predicate holds exactly when every value of the natural-number family is one. -/
theorem auxiliaryEndomorphismPropertyIffForallEqOneOfSimpleFamily (P S : ι → C)
    (hproj : ∀ i, Projective (P i))
    [RepresentationTheory.CategoryTheory.ProjectiveEpiProperties.HasProjectiveEpiWitnesses
      (⨁ P)]
    (hsimple : ∀ i, Simple (S i))
    (hdistinct : ∀ i j, Nonempty (S i ≅ S j) → i = j)
    (hcomplete : ∀ X : C, Simple X → ∃ i, Nonempty (X ≅ S i))
    (hdelta : ∀ i j, finrank k (P i ⟶ S j) = if i = j then 1 else 0)
    (n : ι → ℕ) (hn : ∀ i, 1 ≤ n i) :
    RepresentationTheory.FieldAlgebraProperties.fieldAlgebraProperty k
      ((End
        (RepresentationTheory.CategoryTheory.Preadditive.ProjectiveDecomposition.biproductOfMultiplicities
          P n))ᵐᵒᵖ) ↔ ∀ i, n i = 1 := by
  obtain ⟨e⟩ := auxiliaryQuotientEndomorphismAlgEquivPiMatrixOfSimpleFamily
    P S hproj hsimple hdistinct hcomplete hdelta n hn
  exact
    RepresentationTheory.Algebra.QuotientMatrixDecomposition.property_iff_matrix_block_sizes_eq_one
      k
      ((End
        (RepresentationTheory.CategoryTheory.Preadditive.ProjectiveDecomposition.biproductOfMultiplicities
          P n))ᵐᵒᵖ) n hn e

omit [DecidableEq ι] in
/-- Constructs an algebra equivalence from the displayed endomorphism quotient to a family of square matrix algebras. -/
theorem auxiliaryQuotientEndomorphismAlgEquivPiMatrix (P : ι → C)
    (hproj : ∀ i, Projective (P i))
    (hindec : ∀ i, Indecomposable (P i))
    (hdistinct : ∀ i j, Nonempty (P i ≅ P j) → i = j)
    [RepresentationTheory.CategoryTheory.ProjectiveEpiProperties.HasProjectiveEpiWitnesses
      (⨁ P)]
    (n : ι → ℕ) (hn : ∀ i, 1 ≤ n i) :
    Nonempty ((((End
      (RepresentationTheory.CategoryTheory.Preadditive.ProjectiveDecomposition.biproductOfMultiplicities
        P n))ᵐᵒᵖ) ⧸
        RepresentationTheory.RingTheory.SimpleModuleAnnihilator.simpleModuleAnnihilator
          ((End
            (RepresentationTheory.CategoryTheory.Preadditive.ProjectiveDecomposition.biproductOfMultiplicities
              P n))ᵐᵒᵖ)) ≃ₐ[k]
      ∀ i, Matrix (Fin (n i)) (Fin (n i)) k) := by
  classical
  obtain ⟨S, hsimple, hSdistinct, hcomplete, hdelta⟩ :=
    RepresentationTheory.CategoryTheory.Indecomposable.exists_simple_family_with_finrank_hom
      (k := k) P hproj hindec hdistinct
  exact auxiliaryQuotientEndomorphismAlgEquivPiMatrixOfSimpleFamily
    P S hproj hsimple hSdistinct hcomplete hdelta n hn

omit [DecidableEq ι] in
/-- For the stated projective indecomposable family, the displayed algebra predicate holds exactly when every value of the natural-number family is one. -/
theorem auxiliaryEndomorphismPropertyIffForallEqOne (P : ι → C)
    (hproj : ∀ i, Projective (P i))
    (hindec : ∀ i, Indecomposable (P i))
    (hdistinct : ∀ i j, Nonempty (P i ≅ P j) → i = j)
    [RepresentationTheory.CategoryTheory.ProjectiveEpiProperties.HasProjectiveEpiWitnesses
      (⨁ P)]
    (n : ι → ℕ) (hn : ∀ i, 1 ≤ n i) :
    RepresentationTheory.FieldAlgebraProperties.fieldAlgebraProperty k
      ((End
        (RepresentationTheory.CategoryTheory.Preadditive.ProjectiveDecomposition.biproductOfMultiplicities
          P n))ᵐᵒᵖ) ↔ ∀ i, n i = 1 := by
  classical
  obtain ⟨e⟩ := auxiliaryQuotientEndomorphismAlgEquivPiMatrix
    (k := k) P hproj hindec hdistinct n hn
  exact
    RepresentationTheory.Algebra.QuotientMatrixDecomposition.property_iff_matrix_block_sizes_eq_one
      k
      ((End
        (RepresentationTheory.CategoryTheory.Preadditive.ProjectiveDecomposition.biproductOfMultiplicities
          P n))ᵐᵒᵖ) n hn e

end CartanSizes

end RepresentationTheory.CategoryTheory.BiproductEndomorphismAuxiliary
