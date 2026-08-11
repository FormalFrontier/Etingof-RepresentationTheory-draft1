import EtingofRepresentationTheory.Chapter8.ExternalTensorComplexLeft
import EtingofRepresentationTheory.Chapter8.ExternalTensorProjectiveLeft
import EtingofRepresentationTheory.Chapter8.ExternalTensorRestrictionLeft
import EtingofRepresentationTheory.Chapter8.ExternalTensorResolution
import EtingofRepresentationTheory.Chapter7.KunnethChainComplexNat
import Mathlib.Algebra.Category.ModuleCat.ChangeOfRingsExact

set_option backward.isDefEq.respectTransparency false

/-!
# The external tensor of two projective resolutions is a projective resolution (left modules)

Left-module twin of `ExternalTensorResolution.lean`. Assembling `extTensorComplexLeft` /
`extTensorπL` (`ExternalTensorComplexLeft.lean`), the degreewise projectivity
`extTensor_projectiveLeft` (`ExternalTensorProjectiveLeft.lean`), and the restriction-of-scalars
commutation `extTensorComplexLeft_restrictIso` (`ExternalTensorRestrictionLeft.lean`), this file
constructs the `ProjectiveResolution` of `M₁ ⊗[k] M₂` over `A₁ ⊗[k] A₂` for **left** modules `M₁`,
`M₂`:

* `Etingof.extTensorComplexLeft_projective`: each degree of the external tensor complex is
  projective over `A₁ ⊗[k] A₂`;
* `Etingof.extTensorProjectiveResolutionLeft`: the `ProjectiveResolution`, complex
  `extTensorComplexLeft P₁ P₂`, augmentation `extTensorπL P₁ P₂`, with the `quasiIso` obligation
  proved in full.

This is what the `Ext` half of Problem 8.2.8 (`Problem_8_2_8_ext`) resolves against, mirroring how
the `Tor` half uses the right-module `extTensorProjectiveResolution`.

## The base ring must be a field

As in the right-module case the `quasiIso` obligation is the vanishing of higher `Tor` over `k`,
false over a general commutative ring but true over a field where every module is flat. The section
variable is `[Field k]`.

## The `quasiIso` obligation

Restriction of scalars to `k` reflects `QuasiIso` (`restrictScalars_preservesHomology`), so it
suffices to check the restricted augmentation, which `extTensorComplexLeft_restrictIso` identifies
with the augmentation of the `k`-tensor total complex `res₁ComplexL P₁ ⊗ res₂ComplexL P₂`. That map
is a quasi-isomorphism degreewise: positive degrees by `homology_tensorObj_resL_isZero_succ`
(via the Chapter 7 Künneth formula), degree 0 by the tensor-cokernel isomorphism. The generic
homological lemmas (`restrictScalars_preservesHomology`,
`homology_mapHomologicalComplex_projective_isZero_succ`,
`quasiIsoAt_zero_of_isColimitCokernelCofork`, `isColimitCokernelCofork_tensorObj_augmentation`) are
polymorphic and reused directly from `ExternalTensorResolution.lean`.
-/

open CategoryTheory Limits MonoidalCategory HomologicalComplex TensorProduct

namespace Etingof

universe u

variable {k : Type u} [Field k]
variable {A₁ A₂ : Type u} [Ring A₁] [Ring A₂] [Algebra k A₁] [Algebra k A₂]
variable {M₁ : ModuleCat.{u} A₁} {M₂ : ModuleCat.{u} A₂}

attribute [local instance] restrictModule₁L restrictModule₂L tower₁L tower₂L extModuleL

/-- The degree `.X n` of the external tensor complex, unfolded to the coproduct `mapObj` of its
bidegree summands. -/
private theorem extTensorComplexLeft_X_eq (P₁ : ProjectiveResolution M₁)
    (P₂ : ProjectiveResolution M₂) (n : ℕ) :
    (extTensorComplexLeft (k := k) P₁ P₂).X n
      = (((((extTensorFunctorLeft k A₁ A₂).mapBifunctorHomologicalComplex
          (ComplexShape.down ℕ) (ComplexShape.down ℕ)).obj P₁.complex).obj
          P₂.complex).toGradedObject.mapObj
          (ComplexShape.π (ComplexShape.down ℕ) (ComplexShape.down ℕ) (ComplexShape.down ℕ))) n :=
  rfl

/-- Each degree of the external tensor complex is projective over `A₁ ⊗[k] A₂`. -/
theorem extTensorComplexLeft_projective (P₁ : ProjectiveResolution M₁)
    (P₂ : ProjectiveResolution M₂) (n : ℕ) :
    Projective ((extTensorComplexLeft (k := k) P₁ P₂).X n) := by
  rw [extTensorComplexLeft_X_eq]
  set g := ((((extTensorFunctorLeft k A₁ A₂).mapBifunctorHomologicalComplex
    (ComplexShape.down ℕ) (ComplexShape.down ℕ)).obj P₁.complex).obj
    P₂.complex).toGradedObject.mapObjFun
    (ComplexShape.π (ComplexShape.down ℕ) (ComplexShape.down ℕ) (ComplexShape.down ℕ)) n with hg
  haveI hsummand : ∀ i, Projective (g i) := by
    rw [hg]; rintro ⟨⟨i₁, i₂⟩, h⟩
    exact extTensor_projectiveLeft k A₁ A₂ (P₁.complex.X i₁) (P₂.complex.X i₂)
  haveI hcop : HasCoproduct g := by rw [hg]; infer_instance
  change Projective (∐ g)
  refine ⟨fun {E X} f e he => ⟨Sigma.desc fun b => Projective.factorThru (Sigma.ι g b ≫ f) e, ?_⟩⟩
  apply Sigma.hom_ext
  intro b
  rw [Sigma.ι_desc_assoc]
  exact Projective.factorThru_comp _ e

/-- **Positive-degree acyclicity** of the `k`-tensor of the two restricted resolutions (left
version). By the Chapter 7 Künneth formula every summand of `H_{n+1}(C₁ ⊗ C₂)` vanishes because one
index is positive and the restricted resolution is acyclic there. -/
theorem homology_tensorObj_resL_isZero_succ
    (P₁ : ProjectiveResolution M₁) (P₂ : ProjectiveResolution M₂) (n : ℕ) :
    IsZero ((HomologicalComplex.tensorObj (res₁ComplexL (k := k) P₁)
      (res₂ComplexL (k := k) P₂)).homology (n + 1)) := by
  haveI : (res₁L k A₁).PreservesHomology := restrictScalars_preservesHomology _
  haveI : (res₂L k A₂).PreservesHomology := restrictScalars_preservesHomology _
  refine IsZero.of_iso ?_
    (kunnethChainComplexNatIso (res₁ComplexL (k := k) P₁) (res₂ComplexL (k := k) P₂) (n + 1))
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
    exact TensorExtend.isZero_tensorObj_right
      (homology_mapHomologicalComplex_projective_isZero_succ P₂ (res₂L k A₂) n)
  · exact TensorExtend.isZero_tensorObj_left
      (homology_mapHomologicalComplex_projective_isZero_succ P₁ (res₁L k A₁) p')

/-- The **external tensor product of two projective resolutions** `P•₁ ⊗_k P•₂` is a projective
resolution of `M₁ ⊗[k] M₂` over `A₁ ⊗[k] A₂` (left modules). Left-module twin of
`extTensorProjectiveResolution`, resolving left modules for the `Ext` half of Problem 8.2.8. -/
noncomputable def extTensorProjectiveResolutionLeft
    (P₁ : ProjectiveResolution M₁) (P₂ : ProjectiveResolution M₂) :
    ProjectiveResolution (ModuleCat.of (A₁ ⊗[k] A₂) (M₁ ⊗[k] M₂)) where
  complex := extTensorComplexLeft P₁ P₂
  projective := extTensorComplexLeft_projective P₁ P₂
  π := extTensorπL P₁ P₂
  quasiIso := by
    haveI : (resExtL k A₁ A₂).PreservesHomology :=
      restrictScalars_preservesHomology (algebraMap k (A₁ ⊗[k] A₂))
    rw [← HomologicalComplex.quasiIso_map_iff_of_preservesHomology (extTensorπL P₁ P₂)
      (resExtL k A₁ A₂)]
    set sIso := extTensorComplexLeft_restrictIso (k := k) P₁ P₂ with hsIso
    set tIso := (HomologicalComplex.singleMapHomologicalComplex (resExtL k A₁ A₂)
        (ComplexShape.down ℕ) 0).app (extTensorFunctorLeftObj k A₁ A₂ M₁ M₂) ≪≫
      (ChainComplex.single₀ (ModuleCat.{u} k)).mapIso
        (extRestrictObjIsoL (k := k) M₁ M₂) with htIso
    set Φ := sIso.inv ≫ ((resExtL k A₁ A₂).mapHomologicalComplex (ComplexShape.down ℕ)).map
      (extTensorπL P₁ P₂) ≫ tIso.hom with hΦ
    suffices hQ : QuasiIso Φ by
      have heq : ((resExtL k A₁ A₂).mapHomologicalComplex (ComplexShape.down ℕ)).map
          (extTensorπL P₁ P₂) = sIso.hom ≫ Φ ≫ tIso.inv := by
        rw [hΦ]; simp
      rw [heq]; infer_instance
    rw [quasiIso_iff]
    rintro (_ | n)
    · -- degree `0`: the tensor-cokernel augmentation isomorphism.
      refine quasiIsoAt_zero_of_isColimitCokernelCofork Φ ?_
      set p₁ : (res₁ComplexL P₁).X 0 ⟶ (res₁L k A₁).obj M₁ :=
        (res₁L k A₁).map ((ChainComplex.toSingle₀Equiv P₁.complex M₁) P₁.π).1 with hp₁def
      set p₂ : (res₂ComplexL P₂).X 0 ⟶ (res₂L k A₂).obj M₂ :=
        (res₂L k A₂).map ((ChainComplex.toSingle₀Equiv P₂.complex M₂) P₂.π).1 with hp₂def
      haveI : Limits.PreservesColimits (res₁L k A₁) :=
        (ModuleCat.restrictCoextendScalarsAdj (algebraMap k A₁)).leftAdjoint_preservesColimits
      haveI : Limits.PreservesColimits (res₂L k A₂) :=
        (ModuleCat.restrictCoextendScalarsAdj (algebraMap k A₂)).leftAdjoint_preservesColimits
      have hp₁comm : (res₁ComplexL P₁).d 1 0 ≫ p₁ = 0 := by
        have h : (res₁ComplexL P₁).d 1 0 ≫ p₁ = (res₁L k A₁).map (P₁.complex.d 1 0 ≫ P₁.π.f 0) := by
          rw [Functor.map_comp]; rfl
        rw [h, ProjectiveResolution.complex_d_comp_π_f_zero, Functor.map_zero]
      have hp₂comm : (res₂ComplexL P₂).d 1 0 ≫ p₂ = 0 := by
        have h : (res₂ComplexL P₂).d 1 0 ≫ p₂ = (res₂L k A₂).map (P₂.complex.d 1 0 ≫ P₂.π.f 0) := by
          rw [Functor.map_comp]; rfl
        rw [h, ProjectiveResolution.complex_d_comp_π_f_zero, Functor.map_zero]
      have hc₁ : IsColimit (CokernelCofork.ofπ p₁ hp₁comm) :=
        P₁.cokernelCofork.mapIsColimit P₁.isColimitCokernelCofork (res₁L k A₁)
      have hc₂ : IsColimit (CokernelCofork.ofπ p₂ hp₂comm) :=
        P₂.cokernelCofork.mapIsColimit P₂.isColimitCokernelCofork (res₂L k A₂)
      have h₀ : ComplexShape.π (ComplexShape.down ℕ) (ComplexShape.down ℕ)
          (ComplexShape.down ℕ) (0, 0) = 0 := rfl
      have hgapA : HomologicalComplex.ιTensorObj (res₁ComplexL P₁) (res₂ComplexL P₂) 0 0 0 rfl ≫
          Φ.f 0 = MonoidalCategory.tensorHom p₁ p₂ := by
        have hs0 : sIso.inv.f 0 = (extRestrictComplexXIsoL P₁ P₂ 0).inv := by rw [hsIso]; rfl
        have hmid0 : (((resExtL k A₁ A₂).mapHomologicalComplex (ComplexShape.down ℕ)).map
            (extTensorπL P₁ P₂)).f 0 = (resExtL k A₁ A₂).map (extTensorAug₀L P₁ P₂) := by
          change (resExtL k A₁ A₂).map ((extTensorπL P₁ P₂).f 0) = _
          congr 1
        have ht0 : tIso.hom.f 0 = (extRestrictObjIsoL M₁ M₂).hom := by
          rw [htIso, Iso.trans_hom, HomologicalComplex.comp_f, Iso.app_hom,
            HomologicalComplex.singleMapHomologicalComplex_hom_app_self]
          simp only [ChainComplex.single₀ObjXSelf, Iso.refl_hom, CategoryTheory.Functor.map_id,
            Iso.refl_inv, Category.id_comp,
            CategoryTheory.Functor.mapIso_hom, ChainComplex.single₀_map_f_zero]
          exact Category.id_comp _
        rw [hΦ]
        simp only [HomologicalComplex.comp_f]
        rw [hs0, hmid0, ht0, ← Category.assoc,
          ι_extRestrictComplexXIsoL_inv (k := k) P₁ P₂ 0 0 0 h₀, Category.assoc,
          ι_extRestrictComplexXIsoL_aug₀ (k := k) P₁ P₂ h₀, Iso.inv_hom_id_assoc]
      have hΦcomm : (HomologicalComplex.tensorObj (res₁ComplexL P₁) (res₂ComplexL P₂)).d 1 0 ≫
          Φ.f 0 = 0 := by
        rw [← Φ.comm 1 0, HomologicalComplex.single_obj_d, comp_zero]
      exact isColimitCokernelCofork_tensorObj_augmentation hp₁comm hp₂comm hc₁ hc₂ hΦcomm hgapA
    · -- positive degrees: source is acyclic, target is `single₀`.
      rw [quasiIsoAt_iff_exactAt' _ _ (ChainComplex.exactAt_succ_single_obj _ _),
        HomologicalComplex.exactAt_iff_isZero_homology]
      exact homology_tensorObj_resL_isZero_succ P₁ P₂ n

end Etingof
