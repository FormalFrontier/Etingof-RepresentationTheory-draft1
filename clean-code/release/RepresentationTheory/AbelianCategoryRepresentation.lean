/-
Copyright (c) 2026 mathlib-initiative. All rights reserved.
Released under Apache 2.0 license as described in the file LICENCE.
Authors: mathlib-initiative
-/
import Mathlib.CategoryTheory.Abelian.FreydMitchell
import Mathlib.CategoryTheory.Abelian.Subcategory
import Mathlib.CategoryTheory.Abelian.Images
import RepresentationTheory.Alignment.Attribute

/-!
# Abelian category representations

This module records constructions that realize abelian categories as full subcategories of module
categories and closure properties of essential images.
-/

universe v u

namespace RepresentationTheory.AbelianCategoryRepresentation

open CategoryTheory Limits ZeroObject

/-- A type-valued construction on categories. -/
abbrev CategoryData (C : Type*) [CategoryTheory.Category C] :=
  CategoryTheory.Abelian C

section EssentialImage

variable {C D : Type*} [Category* C] [Category* D] (F : C ⥤ D) [F.Full] [F.Faithful]

/-- The apex of a limit cone lies in the essential image when every object in its diagram does. -/
lemma essImage_mem_of_isLimit {J : Type*} [Category* J] [HasLimitsOfShape J C]
    [PreservesLimitsOfShape J F] {G : J ⥤ D} (hG : ∀ j, F.essImage (G.obj j)) {c : Cone G}
    (hc : IsLimit c) : F.essImage c.pt :=
  ⟨limit (Functor.essImage.liftFunctor G F hG),
    ⟨IsLimit.conePointUniqueUpToIso
      ((IsLimit.postcomposeHomEquiv (Functor.essImage.liftFunctorCompIso G F hG) _).symm
        (isLimitOfPreserves F (limit.isLimit _))) hc⟩⟩

/-- The apex of a colimit cocone lies in the essential image when every object in its diagram
does. -/
lemma essImage_mem_of_isColimit {J : Type*} [Category* J] [HasColimitsOfShape J C]
    [PreservesColimitsOfShape J F] {G : J ⥤ D} (hG : ∀ j, F.essImage (G.obj j)) {c : Cocone G}
    (hc : IsColimit c) : F.essImage c.pt :=
  ⟨colimit (Functor.essImage.liftFunctor G F hG),
    ⟨IsColimit.coconePointUniqueUpToIso
      ((IsColimit.precomposeInvEquiv (Functor.essImage.liftFunctorCompIso G F hG) _).symm
        (isColimitOfPreserves F (colimit.isColimit _))) hc⟩⟩

/-- The essential image of a full faithful functor is closed under limits of a shape that exist in
the source and are preserved by the functor. -/
instance essImage_closedUnderLimitsOfShape (J : Type*) [Category* J] [HasLimitsOfShape J C]
    [PreservesLimitsOfShape J F] : F.essImage.IsClosedUnderLimitsOfShape J :=
  ObjectProperty.IsClosedUnderLimitsOfShape.mk' (by
    rintro _ ⟨G, hG⟩
    exact essImage_mem_of_isLimit F hG (limit.isLimit G))

/-- The essential image of a full faithful functor is closed under colimits of a shape that exist in
the source and are preserved by the functor. -/
instance essImage_closedUnderColimitsOfShape (J : Type*) [Category* J] [HasColimitsOfShape J C]
    [PreservesColimitsOfShape J F] : F.essImage.IsClosedUnderColimitsOfShape J :=
  ObjectProperty.IsClosedUnderColimitsOfShape.mk' (by
    rintro _ ⟨G, hG⟩
    exact essImage_mem_of_isColimit F hG (colimit.isColimit G))

/-- The essential image of a full faithful functor is closed under finite products when they exist
in the source and are preserved by the functor. -/
instance essImage_closedUnderFiniteProducts [HasFiniteProducts C]
    [PreservesFiniteProducts F] : F.essImage.IsClosedUnderFiniteProducts :=
  ObjectProperty.IsClosedUnderFiniteProducts.of_isClosedUnderLimitsOfShape
    (fun (_ : Type) _ => inferInstance)

/-- The essential image of a full faithful functor is closed under finite coproducts when they exist
in the source and are preserved by the functor. -/
instance essImage_closedUnderFiniteCoproducts [HasFiniteCoproducts C]
    [PreservesFiniteCoproducts F] : F.essImage.IsClosedUnderFiniteCoproducts :=
  ObjectProperty.IsClosedUnderFiniteCoproducts.of_isClosedUnderColimitsOfShape
    (fun (_ : Type) _ => inferInstance)

/-- The essential image contains a zero object when the functor preserves the empty limit. -/
instance essImage_containsZero [HasZeroObject C] [HasZeroObject D]
    [PreservesLimitsOfShape (Discrete.{0} PEmpty) F] : F.essImage.ContainsZero :=
  ⟨F.obj 0,
    (isZero_zero D).of_iso
      (IsTerminal.uniqueUpToIso (IsTerminal.isTerminalObj F 0 (isZero_zero C).isTerminal)
        (isZero_zero D).isTerminal),
    F.obj_mem_essImage 0⟩

variable [HasZeroMorphisms C] [HasZeroMorphisms D]

/-- The essential image of a full faithful functor is closed under kernels when the source has
equalizers and the functor preserves parallel-pair limits. -/
instance essImage_closedUnderKernels [HasEqualizers C]
    [PreservesLimitsOfShape WalkingParallelPair F] : F.essImage.IsClosedUnderKernels where
  kernels_le := by
    rintro _ ⟨f, k, hk, hf⟩
    exact F.essImage.prop_of_isLimit hk (by rintro (_ | _) <;> [exact hf.1; exact hf.2])

/-- The essential image of a full faithful functor is closed under cokernels when the source has
coequalizers and the functor preserves parallel-pair colimits. -/
instance essImage_closedUnderCokernels [HasCoequalizers C]
    [PreservesColimitsOfShape WalkingParallelPair F] : F.essImage.IsClosedUnderCokernels where
  cokernels_le := by
    rintro _ ⟨f, k, hk, hf⟩
    exact F.essImage.prop_of_isColimit hk (by rintro (_ | _) <;> [exact hf.1; exact hf.2])

end EssentialImage

section Image

variable {C D : Type*} [Category* C] [Category* D] [CategoryTheory.Abelian C]
  [CategoryTheory.Abelian D] (F : C ⥤ D) [F.Full] [F.Faithful] [PreservesFiniteLimits F]
  [PreservesFiniteColimits F]

/-- The essential image of a full faithful functor between abelian categories is closed under
images when the functor preserves finite limits and finite colimits. -/
lemma essImage_closedUnderImages {X Y : D} (f : X ⟶ Y) (hX : F.essImage X)
    (hY : F.essImage Y) : F.essImage (image f) :=
  F.essImage.prop_of_iso (CategoryTheory.Abelian.imageIsoImage f)
    (F.essImage.prop_kernel (cokernel.π f) hY (F.essImage.prop_cokernel f hX hY))

end Image

section FreydMitchell

variable (C : Type u) [Category.{v} C] [CategoryTheory.Abelian C]

/-- The coefficient type used for the module category associated to an abelian category. -/
abbrev coefficientRing : Type (max u v) :=
  CategoryTheory.Abelian.FreydMitchell.EmbeddingRing C

/-- A functor from an abelian category to modules over its associated coefficient ring. -/
noncomputable abbrev embeddingFunctor : C ⥤ ModuleCat.{max u v} (coefficientRing C) :=
  CategoryTheory.Abelian.FreydMitchell.functor C

/-- An object property on modules over the coefficient ring associated to an abelian category. -/
abbrev moduleProperty : ObjectProperty (ModuleCat.{max u v} (coefficientRing C)) :=
  (embeddingFunctor C).essImage

/-- An equivalence from an abelian category to the full subcategory selected by its module object
property. -/
noncomputable def moduleEquivalence : C ≌ (moduleProperty C).FullSubcategory :=
  (embeddingFunctor C).toEssImage.asEquivalence

/-- A natural isomorphism from the module equivalence followed by the full-subcategory inclusion
to the embedding functor. -/
noncomputable def moduleEquivalenceCompInclusionIso :
    (moduleEquivalence C).functor ⋙ (moduleProperty C).ι ≅ embeddingFunctor C :=
  (embeddingFunctor C).toEssImageCompι

/-- The associated module object property is closed under images of morphisms between objects
satisfying it. -/
lemma moduleProperty_closedUnderImages {X Y : ModuleCat.{max u v} (coefficientRing C)}
    (f : X ⟶ Y) (hX : moduleProperty C X) (hY : moduleProperty C Y) :
    moduleProperty C (image f) :=
  essImage_closedUnderImages _ f hX hY

/-- Every abelian category is equivalent to a full subcategory of modules selected by an object
property containing zero and closed under isomorphisms, finite products, finite coproducts,
kernels, cokernels, and images. -/
@[source_ref "Chapter7/Introduction_7.7" (role := primary),
  source_ref "Chapter7/Definition7.7.1" (role := primary)]
theorem exists_moduleCatFullSubcategoryEquivalence :
    ∃ (A : Type (max u v)) (_ : Ring A) (P : ObjectProperty (ModuleCat.{max u v} A)),
      P.ContainsZero ∧ P.IsClosedUnderIsomorphisms ∧
      P.IsClosedUnderFiniteProducts ∧ P.IsClosedUnderFiniteCoproducts ∧
      P.IsClosedUnderKernels ∧ P.IsClosedUnderCokernels ∧
      (∀ (X Y : ModuleCat.{max u v} A) (f : X ⟶ Y), P X → P Y → P (image f)) ∧
      Nonempty (C ≌ P.FullSubcategory) :=
  ⟨coefficientRing C, inferInstance, moduleProperty C, inferInstance, inferInstance,
    inferInstance, inferInstance, inferInstance, inferInstance,
    fun _ _ f hX hY => moduleProperty_closedUnderImages C f hX hY, ⟨moduleEquivalence C⟩⟩

end FreydMitchell

/-- Produces category data for the full subcategory of modules selected by an object property
containing zero and closed under kernels, cokernels, and finite products. -/
@[source_ref "Chapter7/Definition7.7.1" (role := primary)]
noncomputable abbrev categoryDataOfObjectProperty {A : Type u} [Ring A]
    (P : ObjectProperty (ModuleCat.{v} A)) [P.ContainsZero] [P.IsClosedUnderKernels]
    [P.IsClosedUnderCokernels] [P.IsClosedUnderFiniteProducts] :
    CategoryData P.FullSubcategory :=
  inferInstance

end RepresentationTheory.AbelianCategoryRepresentation
