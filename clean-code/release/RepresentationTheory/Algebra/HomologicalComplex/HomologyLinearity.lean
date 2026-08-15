/-
Copyright (c) 2026 mathlib-initiative. All rights reserved.
Released under Apache 2.0 license as described in the file LICENCE.
Authors: mathlib-initiative
-/
import RepresentationTheory.HomologicalAlgebra.ProjectiveResolution.LinearYonedaComparison
import RepresentationTheory.CategoryTheory.Abelian.ExtensionClasses
import Mathlib.CategoryTheory.Abelian.Projective.Ext
import Mathlib.Algebra.Category.ModuleCat.Ext.HasExt
import Mathlib.Algebra.Homology.DerivedCategory.Ext.Linear
import Mathlib.Algebra.Homology.Linear
import Mathlib.Algebra.Homology.ShortComplex.Linear

open CategoryTheory Limits CochainComplex CochainComplex.HomComplex
open RepresentationTheory.CategoryTheory.Abelian.ExtensionClasses
open RepresentationTheory.Algebra.Homology.LinearYoneda
open RepresentationTheory.HomologicalAlgebra.ProjectiveResolution.LinearYonedaComparison

namespace RepresentationTheory.Algebra.HomologicalComplex.HomologyLinearity

variable {R : Type*} [Semiring R] {C : Type*} [Category C] [Preadditive C]
  [CategoryTheory.Linear R C] {ι : Type*} {c : ComplexShape ι}
  {K L : HomologicalComplex C c}

set_option backward.isDefEq.respectTransparency false in
/-- The homology map of a scalar multiple of a morphism is the corresponding scalar multiple of
its homology map. -/
lemma homologyMap_smul (r : R) (φ : K ⟶ L) (i : ι) [K.HasHomology i] [L.HasHomology i] :
    HomologicalComplex.homologyMap (r • φ) i = r • HomologicalComplex.homologyMap φ i := by
  dsimp [HomologicalComplex.homologyMap]
  rw [← ShortComplex.homologyMap_smul]
  rfl

universe u

variable (k : Type u) [Field k]
variable {A : Type u} [Ring A] [Algebra k A]
variable {M : ModuleCat.{u} A} (N : ModuleCat.{u} A) (P : ProjectiveResolution M)

/-- An additive equivalence at a natural-number degree in the setting of a projective resolution
over an algebra. -/
noncomputable def projectiveResolutionDegreeAddEquiv (n : ℕ) :
    CategoryTheory.ExtensionClasses M N n ≃+ ModuleCat.linearYonedaHomology k A M N n :=
  (P.extAddEquivCohomologyClass.trans
    (CochainComplex.HomComplex.homologyAddEquiv P.cochainComplex
      ((CochainComplex.singleFunctor (ModuleCat.{u} A) 0).obj N) (n : ℤ)).symm).trans
    ((CategoryTheory.ProjectiveResolution.homCochainComplexHomologyAddEquiv k N P n).trans
      (ModuleCat.linearYonedaHomologyIsoOfProjectiveResolution
        k A M N P n).symm.toLinearEquiv.toAddEquiv)

/-- Scalar multiplication on a homology class is induced by the scalar multiple of the identity
map. -/
lemma smul_homology_eq_homologyMap_smul_id (r : k) (n : ℕ)
    (v : (P.complex.linearYonedaObj k N).homology n) :
    r • v =
      (HomologicalComplex.homologyMap (r • 𝟙 (P.complex.linearYonedaObj k N)) n).hom v := by
  rw [homologyMap_smul, HomologicalComplex.homologyMap_id, ← ModuleCat.lsmul_eq_smul_id]
  rfl

/-- A linear equivalence over the base field at a natural-number degree in the setting of a
projective resolution over an algebra. -/
noncomputable def projectiveResolutionDegreeLinearEquiv (n : ℕ) :
    CategoryTheory.ExtensionClasses M N n ≃ₗ[k] ModuleCat.linearYonedaHomology k A M N n where
  __ := projectiveResolutionDegreeAddEquiv k N P n
  map_smul' := by
    intro r x
    set e123 : CategoryTheory.ExtensionClasses M N n ≃+
        (P.complex.linearYonedaObj k N).homology n :=
      (P.extAddEquivCohomologyClass.trans
        (CochainComplex.HomComplex.homologyAddEquiv P.cochainComplex
          ((CochainComplex.singleFunctor (ModuleCat.{u} A) 0).obj N)
            (n : ℤ)).symm).trans
        (CategoryTheory.ProjectiveResolution.homCochainComplexHomologyAddEquiv k N P n) with he123
    set step4 : (P.complex.linearYonedaObj k N).homology n ≃ₗ[k]
        ModuleCat.linearYonedaHomology k A M N n :=
      (ModuleCat.linearYonedaHomologyIsoOfProjectiveResolution k A M N P n).symm.toLinearEquiv
        with hstep4
    have crux : ∀ (f : P.complex.X n ⟶ N) (hf : P.complex.d (n + 1) n ≫ f = 0),
        e123 (P.extMk (r • f) (n + 1) rfl
              (by rw [Linear.comp_smul, hf, smul_zero]))
          = r • e123 (P.extMk f (n + 1) rfl hf) := by
      intro f hf
      have hfg : P.complex.d (n + 1) n ≫ (f ≫ (r • 𝟙 N)) = 0 := by
        rw [← Category.assoc, hf, zero_comp]
      have hExtRw : P.extMk (r • f) (n + 1) rfl
          (by rw [Linear.comp_smul, hf, smul_zero]) =
          P.extMk (f ≫ (r • 𝟙 N)) (n + 1) rfl hfg := by
        congr 1
      have step : P.extAddEquivCohomologyClass (P.extMk (f ≫ (r • 𝟙 N)) (n + 1) rfl hfg)
          = CategoryTheory.ProjectiveResolution.homCohomologyClassMap N P (r • 𝟙 N) (↑n)
              (P.extAddEquivCohomologyClass (P.extMk f (n + 1) rfl hf)) := by
        rw [ProjectiveResolution.extAddEquivCohomologyClass_apply,
            ProjectiveResolution.extEquivCohomologyClass_extMk,
            ProjectiveResolution.extAddEquivCohomologyClass_apply,
            ProjectiveResolution.extEquivCohomologyClass_extMk,
            CategoryTheory.ProjectiveResolution.homCohomologyClassMap_mk]
        congr 1
        rw [← Cocycle.toSingleMk_postcomp]
        congr 1
      simp only [he123, AddEquiv.trans_apply]
      rw [hExtRw, step,
        show (CochainComplex.HomComplex.homologyAddEquiv P.cochainComplex
              ((CochainComplex.singleFunctor (ModuleCat.{u} A) 0).obj N) (↑n : ℤ)).symm
              (CategoryTheory.ProjectiveResolution.homCohomologyClassMap N P (r • 𝟙 N) (↑n)
                (P.extAddEquivCohomologyClass (P.extMk f (n + 1) rfl hf)))
            = HomologicalComplex.homologyMap
                (CategoryTheory.ProjectiveResolution.homCochainComplexMap N P (r • 𝟙 N)) (↑n)
                ((CochainComplex.HomComplex.homologyAddEquiv P.cochainComplex
                  ((CochainComplex.singleFunctor (ModuleCat.{u} A) 0).obj N) (↑n : ℤ)).symm
                  (P.extAddEquivCohomologyClass (P.extMk f (n + 1) rfl hf)))
          from by rw [AddEquiv.symm_apply_eq,
            CategoryTheory.ProjectiveResolution.homComplex_homologyAddEquiv_naturality,
            AddEquiv.apply_symm_apply],
        CategoryTheory.ProjectiveResolution.homCochainComplexHomologyAddEquiv_map_smul,
        ← smul_homology_eq_homologyMap_smul_id]
    have hnat : ∀ y, e123 (r • y)
        = (HomologicalComplex.homologyMap (r • 𝟙 (P.complex.linearYonedaObj k N)) n).hom
            (e123 y) := by
      intro y
      obtain ⟨f, hf, rfl⟩ := P.extMk_surjective y (n + 1) rfl
      have hrf : P.complex.d (n + 1) n ≫ (r • f) = 0 := by
        rw [Linear.comp_smul, hf, smul_zero]
      have hsmul : r • P.extMk f (n + 1) rfl hf =
          P.extMk (r • f) (n + 1) rfl hrf := by
        rw [Abelian.Ext.smul_eq_comp_mk₀, ProjectiveResolution.extMk_comp_mk₀]
        congr 1
      rw [hsmul,
        ← smul_homology_eq_homologyMap_smul_id k N P r n
          (e123 (P.extMk f (n + 1) rfl hf)), crux f hf]
    have key123 : ∀ y, e123 (r • y) = r • e123 y := fun y => by
      rw [hnat y, smul_homology_eq_homologyMap_smul_id k N P r n (e123 y)]
    have hfactor : ∀ y,
        projectiveResolutionDegreeAddEquiv k N P n y = step4 (e123 y) := fun _ => rfl
    change projectiveResolutionDegreeAddEquiv k N P n (r • x) =
      r • projectiveResolutionDegreeAddEquiv k N P n x
    rw [hfactor, hfactor, key123, map_smul]

end RepresentationTheory.Algebra.HomologicalComplex.HomologyLinearity
