/-
Copyright (c) 2026 mathlib-initiative. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: mathlib-initiative
-/

import RepresentationTheory.HomologicalAlgebra.ProjectiveResolution.TensorProduct
import RepresentationTheory.Algebra.TensorProduct.Free
import RepresentationTheory.HomologicalAlgebra.ProjectiveResolution.TensorProductComparison
import RepresentationTheory.Algebra.Homology.TensorResolution
import RepresentationTheory.HomologicalComplex.TensorProduct.Reindexing
import Mathlib.Algebra.Category.ModuleCat.ChangeOfRingsExact

set_option backward.isDefEq.respectTransparency false

/-!
# The external tensor of two projective resolutions is a projective resolution (left modules)

Left-module twin of `TensorResolution.lean`. Assembling
`RepresentationTheory.HomologicalAlgebra.ProjectiveResolution.TensorProduct.tensorProduct` /
`RepresentationTheory.HomologicalAlgebra.ProjectiveResolution.TensorProduct.auxiliaryToSingle`
(`ProjectiveResolution/TensorProduct.lean`), the degreewise projectivity
`RepresentationTheory.Algebra.TensorProduct.Free.ModuleCat.projective_tensorProduct`
(`Algebra/TensorProduct/Free.lean`), and the restriction-of-scalars commutation
`RepresentationTheory.HomologicalAlgebra.ProjectiveResolution.TensorProductComparison.ProjectiveResolution.restrictScalarsTensorProductComplexIso`
(`ProjectiveResolution/TensorProductComparison.lean`), this file
constructs the `ProjectiveResolution` of `M₁ ⊗[k] M₂` over `A₁ ⊗[k] A₂` for **left** modules `M₁`,
`M₂`:

* `RepresentationTheory.HomologicalAlgebra.TensorProduct.X_projective`: each degree of the external tensor complex is
  projective over `A₁ ⊗[k] A₂`;
* `RepresentationTheory.HomologicalAlgebra.TensorProduct.tensorProduct`: the `ProjectiveResolution`, complex
  `RepresentationTheory.HomologicalAlgebra.ProjectiveResolution.TensorProduct.tensorProduct P₁ P₂`, augmentation
  `RepresentationTheory.HomologicalAlgebra.ProjectiveResolution.TensorProduct.auxiliaryToSingle P₁ P₂`, with the `quasiIso` obligation
  proved in full.

This is what the `Ext` half of Problem 8.2.8
(`RepresentationTheory.Auxiliary.TensorProductGradedComparisons.Auxiliary.nonempty_tensorProductGradedPieceLinearEquivDirectSum`)
resolves against, mirroring how the `Tor` half uses the right-module
`RepresentationTheory.Algebra.Homology.TensorResolution.tensorProjectiveResolution`.

## The base ring must be a field

As in the right-module case the `quasiIso` obligation is the vanishing of higher `Tor` over `k`,
false over a general commutative ring but true over a field where every module is flat. The section
variable is `[Field k]`.

## The `quasiIso` obligation

Restriction of scalars to `k` reflects `QuasiIso`
(`RepresentationTheory.Algebra.Homology.TensorResolution.restrictScalars_preservesHomology`), so it
suffices to check the restricted augmentation, which
`RepresentationTheory.HomologicalAlgebra.ProjectiveResolution.TensorProductComparison.ProjectiveResolution.restrictScalarsTensorProductComplexIso`
identifies with the augmentation of the `k`-tensor total complex
`RepresentationTheory.HomologicalAlgebra.ProjectiveResolution.TensorProductComparison.ProjectiveResolution.restrictScalarsComplexLeft P₁ ⊗ RepresentationTheory.HomologicalAlgebra.ProjectiveResolution.TensorProductComparison.ProjectiveResolution.restrictScalarsComplexRight P₂`. That map
is a quasi-isomorphism degreewise: positive degrees by
`RepresentationTheory.HomologicalAlgebra.TensorProduct.tensorObj_homology_succ_isZero`
(via the Chapter 7 Künneth formula), degree 0 by the tensor-cokernel isomorphism. The generic
homological lemmas (`RepresentationTheory.Algebra.Homology.TensorResolution.restrictScalars_preservesHomology`,
`RepresentationTheory.Algebra.Homology.TensorResolution.isZero_homology_mapProjectiveResolution_succ`,
`RepresentationTheory.Algebra.Homology.TensorResolution.quasiIsoAt_zero_of_isColimitCokernel`,
`RepresentationTheory.Algebra.Homology.TensorResolution.isColimit_cokernelCofork_tensor`) are
polymorphic and reused directly from `TensorResolution.lean`.
-/

open CategoryTheory Limits MonoidalCategory HomologicalComplex TensorProduct

namespace RepresentationTheory.HomologicalAlgebra.TensorProduct

universe u

variable {k : Type u} [Field k]
variable {A₁ A₂ : Type u} [Ring A₁] [Ring A₂] [Algebra k A₁] [Algebra k A₂]
variable {M₁ : ModuleCat.{u} A₁} {M₂ : ModuleCat.{u} A₂}

attribute [local instance] RepresentationTheory.Algebra.TensorProduct.ModuleCat.moduleCarrier RepresentationTheory.Algebra.TensorProduct.ModuleCat.moduleCarrierAux RepresentationTheory.Algebra.TensorProduct.ModuleCat.isScalarTower RepresentationTheory.Algebra.TensorProduct.ModuleCat.isScalarTowerAux RepresentationTheory.Algebra.TensorProduct.ModuleCat.tensorProductModule

/-- The degree `.X n` of the external tensor complex, unfolded to the coproduct `mapObj` of its
bidegree summands. -/
private theorem extTensorComplexLeft_X_eq (P₁ : ProjectiveResolution M₁)
    (P₂ : ProjectiveResolution M₂) (n : ℕ) :
    (RepresentationTheory.HomologicalAlgebra.ProjectiveResolution.TensorProduct.tensorProduct (k := k) P₁ P₂).X n
      = (((((RepresentationTheory.Algebra.TensorProduct.ModuleCat.tensorProductFunctor k A₁ A₂).mapBifunctorHomologicalComplex
          (ComplexShape.down ℕ) (ComplexShape.down ℕ)).obj P₁.complex).obj
          P₂.complex).toGradedObject.mapObj
          (ComplexShape.π (ComplexShape.down ℕ) (ComplexShape.down ℕ) (ComplexShape.down ℕ))) n :=
  rfl

/-- The degree `n` object selected by `X` from the displayed complex is projective. -/
theorem X_projective (P₁ : ProjectiveResolution M₁)
    (P₂ : ProjectiveResolution M₂) (n : ℕ) :
    Projective ((RepresentationTheory.HomologicalAlgebra.ProjectiveResolution.TensorProduct.tensorProduct (k := k) P₁ P₂).X n) := by
  rw [extTensorComplexLeft_X_eq]
  set g := ((((RepresentationTheory.Algebra.TensorProduct.ModuleCat.tensorProductFunctor k A₁ A₂).mapBifunctorHomologicalComplex
    (ComplexShape.down ℕ) (ComplexShape.down ℕ)).obj P₁.complex).obj
    P₂.complex).toGradedObject.mapObjFun
    (ComplexShape.π (ComplexShape.down ℕ) (ComplexShape.down ℕ) (ComplexShape.down ℕ)) n with hg
  haveI hsummand : ∀ i, Projective (g i) := by
    rw [hg]; rintro ⟨⟨i₁, i₂⟩, h⟩
    exact RepresentationTheory.Algebra.TensorProduct.Free.ModuleCat.projective_tensorProduct k A₁ A₂ (P₁.complex.X i₁) (P₂.complex.X i₂)
  haveI hcop : HasCoproduct g := by rw [hg]; infer_instance
  change Projective (∐ g)
  refine ⟨fun {E X} f e he => ⟨Sigma.desc fun b => Projective.factorThru (Sigma.ι g b ≫ f) e, ?_⟩⟩
  apply Sigma.hom_ext
  intro b
  rw [Sigma.ι_desc_assoc]
  exact Projective.factorThru_comp _ e

/-- The homology in degree `n + 1` of the displayed tensor-product complex is a zero object. -/
theorem tensorObj_homology_succ_isZero
    (P₁ : ProjectiveResolution M₁) (P₂ : ProjectiveResolution M₂) (n : ℕ) :
    IsZero ((HomologicalComplex.tensorObj (RepresentationTheory.HomologicalAlgebra.ProjectiveResolution.TensorProductComparison.ProjectiveResolution.restrictScalarsComplexLeft (k := k) P₁)
      (RepresentationTheory.HomologicalAlgebra.ProjectiveResolution.TensorProductComparison.ProjectiveResolution.restrictScalarsComplexRight (k := k) P₂)).homology (n + 1)) := by
  haveI : (RepresentationTheory.HomologicalAlgebra.ProjectiveResolution.TensorProductComparison.ModuleCat.restrictScalarsLeft k A₁).PreservesHomology := RepresentationTheory.Algebra.Homology.TensorResolution.restrictScalars_preservesHomology _
  haveI : (RepresentationTheory.HomologicalAlgebra.ProjectiveResolution.TensorProductComparison.ModuleCat.restrictScalarsRight k A₂).PreservesHomology := RepresentationTheory.Algebra.Homology.TensorResolution.restrictScalars_preservesHomology _
  refine IsZero.of_iso ?_
    (RepresentationTheory.HomologicalComplex.TensorProduct.Reindexing.homologyTensorIsoSigma (RepresentationTheory.HomologicalAlgebra.ProjectiveResolution.TensorProductComparison.ProjectiveResolution.restrictScalarsComplexLeft (k := k) P₁) (RepresentationTheory.HomologicalAlgebra.ProjectiveResolution.TensorProductComparison.ProjectiveResolution.restrictScalarsComplexRight (k := k) P₂) (n + 1))
  rw [IsZero.iff_id_eq_zero]
  apply Limits.Sigma.hom_ext
  intro a
  rw [Category.comp_id, comp_zero]
  obtain ⟨⟨p, q⟩, hpq⟩ := a
  have hpq' : p + q = n + 1 := hpq
  refine IsZero.eq_zero_of_src ?_ _
  rcases p with _ | p'
  · have hq : q = n + 1 := by omega
    subst hq
    exact RepresentationTheory.HomologicalComplex.TensorProduct.Reindexing.tensorObj_isZero_of_right
      (RepresentationTheory.Algebra.Homology.TensorResolution.isZero_homology_mapProjectiveResolution_succ P₂ (RepresentationTheory.HomologicalAlgebra.ProjectiveResolution.TensorProductComparison.ModuleCat.restrictScalarsRight k A₂) n)
  · exact RepresentationTheory.HomologicalComplex.TensorProduct.Reindexing.tensorObj_isZero_of_left
      (RepresentationTheory.Algebra.Homology.TensorResolution.isZero_homology_mapProjectiveResolution_succ P₁ (RepresentationTheory.HomologicalAlgebra.ProjectiveResolution.TensorProductComparison.ModuleCat.restrictScalarsLeft k A₁) p')

/-- Forms an object over the tensor product algebra from the two given objects. -/
noncomputable def tensorProduct
    (P₁ : ProjectiveResolution M₁) (P₂ : ProjectiveResolution M₂) :
    ProjectiveResolution (ModuleCat.of (A₁ ⊗[k] A₂) (M₁ ⊗[k] M₂)) where
  complex := RepresentationTheory.HomologicalAlgebra.ProjectiveResolution.TensorProduct.tensorProduct P₁ P₂
  projective := X_projective P₁ P₂
  π := RepresentationTheory.HomologicalAlgebra.ProjectiveResolution.TensorProduct.auxiliaryToSingle P₁ P₂
  quasiIso := by
    haveI : (RepresentationTheory.HomologicalAlgebra.ProjectiveResolution.TensorProductComparison.ModuleCat.restrictScalarsFromTensorProduct k A₁ A₂).PreservesHomology :=
      RepresentationTheory.Algebra.Homology.TensorResolution.restrictScalars_preservesHomology (algebraMap k (A₁ ⊗[k] A₂))
    rw [← HomologicalComplex.quasiIso_map_iff_of_preservesHomology (RepresentationTheory.HomologicalAlgebra.ProjectiveResolution.TensorProduct.auxiliaryToSingle P₁ P₂)
      (RepresentationTheory.HomologicalAlgebra.ProjectiveResolution.TensorProductComparison.ModuleCat.restrictScalarsFromTensorProduct k A₁ A₂)]
    set sIso := RepresentationTheory.HomologicalAlgebra.ProjectiveResolution.TensorProductComparison.ProjectiveResolution.restrictScalarsTensorProductComplexIso (k := k) P₁ P₂ with hsIso
    set tIso := (HomologicalComplex.singleMapHomologicalComplex (RepresentationTheory.HomologicalAlgebra.ProjectiveResolution.TensorProductComparison.ModuleCat.restrictScalarsFromTensorProduct k A₁ A₂)
        (ComplexShape.down ℕ) 0).app (RepresentationTheory.Algebra.TensorProduct.ModuleCat.tensorProduct k A₁ A₂ M₁ M₂) ≪≫
      (ChainComplex.single₀ (ModuleCat.{u} k)).mapIso
        (RepresentationTheory.HomologicalAlgebra.ProjectiveResolution.TensorProductComparison.ModuleCat.restrictScalarsTensorProductIso (k := k) M₁ M₂) with htIso
    set Φ := sIso.inv ≫ ((RepresentationTheory.HomologicalAlgebra.ProjectiveResolution.TensorProductComparison.ModuleCat.restrictScalarsFromTensorProduct k A₁ A₂).mapHomologicalComplex (ComplexShape.down ℕ)).map
      (RepresentationTheory.HomologicalAlgebra.ProjectiveResolution.TensorProduct.auxiliaryToSingle P₁ P₂) ≫ tIso.hom with hΦ
    suffices hQ : QuasiIso Φ by
      have heq : ((RepresentationTheory.HomologicalAlgebra.ProjectiveResolution.TensorProductComparison.ModuleCat.restrictScalarsFromTensorProduct k A₁ A₂).mapHomologicalComplex (ComplexShape.down ℕ)).map
          (RepresentationTheory.HomologicalAlgebra.ProjectiveResolution.TensorProduct.auxiliaryToSingle P₁ P₂) = sIso.hom ≫ Φ ≫ tIso.inv := by
        rw [hΦ]; simp
      rw [heq]; infer_instance
    rw [quasiIso_iff]
    rintro (_ | n)
    · -- degree `0`: the tensor-cokernel augmentation isomorphism.
      refine RepresentationTheory.Algebra.Homology.TensorResolution.quasiIsoAt_zero_of_isColimitCokernel Φ ?_
      set p₁ : (RepresentationTheory.HomologicalAlgebra.ProjectiveResolution.TensorProductComparison.ProjectiveResolution.restrictScalarsComplexLeft P₁).X 0 ⟶ (RepresentationTheory.HomologicalAlgebra.ProjectiveResolution.TensorProductComparison.ModuleCat.restrictScalarsLeft k A₁).obj M₁ :=
        (RepresentationTheory.HomologicalAlgebra.ProjectiveResolution.TensorProductComparison.ModuleCat.restrictScalarsLeft k A₁).map ((ChainComplex.toSingle₀Equiv P₁.complex M₁) P₁.π).1 with hp₁def
      set p₂ : (RepresentationTheory.HomologicalAlgebra.ProjectiveResolution.TensorProductComparison.ProjectiveResolution.restrictScalarsComplexRight P₂).X 0 ⟶ (RepresentationTheory.HomologicalAlgebra.ProjectiveResolution.TensorProductComparison.ModuleCat.restrictScalarsRight k A₂).obj M₂ :=
        (RepresentationTheory.HomologicalAlgebra.ProjectiveResolution.TensorProductComparison.ModuleCat.restrictScalarsRight k A₂).map ((ChainComplex.toSingle₀Equiv P₂.complex M₂) P₂.π).1 with hp₂def
      haveI : Limits.PreservesColimits (RepresentationTheory.HomologicalAlgebra.ProjectiveResolution.TensorProductComparison.ModuleCat.restrictScalarsLeft k A₁) :=
        (ModuleCat.restrictCoextendScalarsAdj (algebraMap k A₁)).leftAdjoint_preservesColimits
      haveI : Limits.PreservesColimits (RepresentationTheory.HomologicalAlgebra.ProjectiveResolution.TensorProductComparison.ModuleCat.restrictScalarsRight k A₂) :=
        (ModuleCat.restrictCoextendScalarsAdj (algebraMap k A₂)).leftAdjoint_preservesColimits
      have hp₁comm : (RepresentationTheory.HomologicalAlgebra.ProjectiveResolution.TensorProductComparison.ProjectiveResolution.restrictScalarsComplexLeft P₁).d 1 0 ≫ p₁ = 0 := by
        have h : (RepresentationTheory.HomologicalAlgebra.ProjectiveResolution.TensorProductComparison.ProjectiveResolution.restrictScalarsComplexLeft P₁).d 1 0 ≫ p₁ = (RepresentationTheory.HomologicalAlgebra.ProjectiveResolution.TensorProductComparison.ModuleCat.restrictScalarsLeft k A₁).map (P₁.complex.d 1 0 ≫ P₁.π.f 0) := by
          rw [Functor.map_comp]; rfl
        rw [h, ProjectiveResolution.complex_d_comp_π_f_zero, Functor.map_zero]
      have hp₂comm : (RepresentationTheory.HomologicalAlgebra.ProjectiveResolution.TensorProductComparison.ProjectiveResolution.restrictScalarsComplexRight P₂).d 1 0 ≫ p₂ = 0 := by
        have h : (RepresentationTheory.HomologicalAlgebra.ProjectiveResolution.TensorProductComparison.ProjectiveResolution.restrictScalarsComplexRight P₂).d 1 0 ≫ p₂ = (RepresentationTheory.HomologicalAlgebra.ProjectiveResolution.TensorProductComparison.ModuleCat.restrictScalarsRight k A₂).map (P₂.complex.d 1 0 ≫ P₂.π.f 0) := by
          rw [Functor.map_comp]; rfl
        rw [h, ProjectiveResolution.complex_d_comp_π_f_zero, Functor.map_zero]
      have hc₁ : IsColimit (CokernelCofork.ofπ p₁ hp₁comm) :=
        P₁.cokernelCofork.mapIsColimit P₁.isColimitCokernelCofork (RepresentationTheory.HomologicalAlgebra.ProjectiveResolution.TensorProductComparison.ModuleCat.restrictScalarsLeft k A₁)
      have hc₂ : IsColimit (CokernelCofork.ofπ p₂ hp₂comm) :=
        P₂.cokernelCofork.mapIsColimit P₂.isColimitCokernelCofork (RepresentationTheory.HomologicalAlgebra.ProjectiveResolution.TensorProductComparison.ModuleCat.restrictScalarsRight k A₂)
      have h₀ : ComplexShape.π (ComplexShape.down ℕ) (ComplexShape.down ℕ)
          (ComplexShape.down ℕ) (0, 0) = 0 := rfl
      have hgapA : HomologicalComplex.ιTensorObj (RepresentationTheory.HomologicalAlgebra.ProjectiveResolution.TensorProductComparison.ProjectiveResolution.restrictScalarsComplexLeft P₁) (RepresentationTheory.HomologicalAlgebra.ProjectiveResolution.TensorProductComparison.ProjectiveResolution.restrictScalarsComplexRight P₂) 0 0 0 rfl ≫
          Φ.f 0 = MonoidalCategory.tensorHom p₁ p₂ := by
        have hs0 : sIso.inv.f 0 = (RepresentationTheory.HomologicalAlgebra.ProjectiveResolution.TensorProductComparison.ProjectiveResolution.restrictScalarsTensorProductXIso P₁ P₂ 0).inv := by rw [hsIso]; rfl
        have hmid0 : (((RepresentationTheory.HomologicalAlgebra.ProjectiveResolution.TensorProductComparison.ModuleCat.restrictScalarsFromTensorProduct k A₁ A₂).mapHomologicalComplex (ComplexShape.down ℕ)).map
            (RepresentationTheory.HomologicalAlgebra.ProjectiveResolution.TensorProduct.auxiliaryToSingle P₁ P₂)).f 0 = (RepresentationTheory.HomologicalAlgebra.ProjectiveResolution.TensorProductComparison.ModuleCat.restrictScalarsFromTensorProduct k A₁ A₂).map (RepresentationTheory.HomologicalAlgebra.ProjectiveResolution.TensorProduct.auxiliaryMap P₁ P₂) := by
          change (RepresentationTheory.HomologicalAlgebra.ProjectiveResolution.TensorProductComparison.ModuleCat.restrictScalarsFromTensorProduct k A₁ A₂).map ((RepresentationTheory.HomologicalAlgebra.ProjectiveResolution.TensorProduct.auxiliaryToSingle P₁ P₂).f 0) = _
          congr 1
        have ht0 : tIso.hom.f 0 = (RepresentationTheory.HomologicalAlgebra.ProjectiveResolution.TensorProductComparison.ModuleCat.restrictScalarsTensorProductIso M₁ M₂).hom := by
          rw [htIso, Iso.trans_hom, HomologicalComplex.comp_f, Iso.app_hom,
            HomologicalComplex.singleMapHomologicalComplex_hom_app_self]
          simp only [ChainComplex.single₀ObjXSelf, Iso.refl_hom, CategoryTheory.Functor.map_id,
            Iso.refl_inv, Category.id_comp,
            CategoryTheory.Functor.mapIso_hom, ChainComplex.single₀_map_f_zero]
          exact Category.id_comp _
        rw [hΦ]
        simp only [HomologicalComplex.comp_f]
        rw [hs0, hmid0, ht0, ← Category.assoc,
          RepresentationTheory.HomologicalAlgebra.ProjectiveResolution.TensorProductComparison.ProjectiveResolution.restrictScalarsTensorProductXIso_inv_iota (k := k) P₁ P₂ 0 0 0 h₀, Category.assoc,
          RepresentationTheory.HomologicalAlgebra.ProjectiveResolution.TensorProductComparison.ProjectiveResolution.restrictScalarsTensorProductIso_augmentation (k := k) P₁ P₂ h₀, Iso.inv_hom_id_assoc]
      have hΦcomm : (HomologicalComplex.tensorObj (RepresentationTheory.HomologicalAlgebra.ProjectiveResolution.TensorProductComparison.ProjectiveResolution.restrictScalarsComplexLeft P₁) (RepresentationTheory.HomologicalAlgebra.ProjectiveResolution.TensorProductComparison.ProjectiveResolution.restrictScalarsComplexRight P₂)).d 1 0 ≫
          Φ.f 0 = 0 := by
        rw [← Φ.comm 1 0, HomologicalComplex.single_obj_d, comp_zero]
      exact RepresentationTheory.Algebra.Homology.TensorResolution.isColimit_cokernelCofork_tensor hp₁comm hp₂comm hc₁ hc₂ hΦcomm hgapA
    · -- positive degrees: source is acyclic, target is `single₀`.
      rw [quasiIsoAt_iff_exactAt' _ _ (ChainComplex.exactAt_succ_single_obj _ _),
        HomologicalComplex.exactAt_iff_isZero_homology]
      exact tensorObj_homology_succ_isZero P₁ P₂ n

end RepresentationTheory.HomologicalAlgebra.TensorProduct
