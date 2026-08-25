import Mathlib.CategoryTheory.Abelian.FreydMitchell
import Mathlib.CategoryTheory.Abelian.Subcategory
import Mathlib.CategoryTheory.Abelian.Images

/-!
# Definition 7.7.1: Abelian Category

An **abelian category** is a category (enriched over the category of abelian groups)
which is equivalent to a full subcategory C of the category A-mod of left modules
over a ring A, closed under taking finite direct sums, as well as kernels, cokernels,
and images of morphisms.

`Etingof.Abelian` is Mathlib's intrinsic axiomatisation `CategoryTheory.Abelian`. The two
descriptions agree, and both implications are available here.

* `Etingof.exists_equiv_moduleCat_fullSubcategory`: an intrinsically abelian `C` is equivalent
  to a full subcategory of `A`-mod, for a ring `A`, closed under finite direct sums, kernels,
  cokernels and images. The subcategory is the essential image of the Freyd-Mitchell embedding
  `Etingof.moduleEmbedding`, and the equivalence is `Etingof.moduleRealizationEquiv`.
* `Etingof.abelianOfClosedFullSubcategory`: conversely, a full subcategory of `A`-mod which
  contains a zero object and is closed under kernels, cokernels and finite products is abelian.

The closure properties are proved in the generality in which they hold: the essential image of
a fully faithful functor is closed under limits and colimits of every shape the functor
preserves (`Etingof.essImage_prop_of_isLimit`, `Etingof.essImage_prop_of_isColimit`).
-/

universe v u

namespace Etingof

open CategoryTheory Limits ZeroObject

/-- An abelian category in the sense of Etingof Definition 7.7.1.
This is `CategoryTheory.Abelian` in Mathlib. -/
abbrev Abelian (C : Type*) [CategoryTheory.Category C] :=
  CategoryTheory.Abelian C

section EssentialImage

variable {C D : Type*} [Category* C] [Category* D] (F : C ⥤ D) [F.Full] [F.Faithful]

/-- A limit of a diagram whose values lie in the essential image of a fully faithful functor `F`
again lies in the essential image, provided `F` preserves limits of that shape. -/
lemma essImage_prop_of_isLimit {J : Type*} [Category* J] [HasLimitsOfShape J C]
    [PreservesLimitsOfShape J F] {G : J ⥤ D} (hG : ∀ j, F.essImage (G.obj j)) {c : Cone G}
    (hc : IsLimit c) : F.essImage c.pt :=
  ⟨limit (Functor.essImage.liftFunctor G F hG),
    ⟨IsLimit.conePointUniqueUpToIso
      ((IsLimit.postcomposeHomEquiv (Functor.essImage.liftFunctorCompIso G F hG) _).symm
        (isLimitOfPreserves F (limit.isLimit _))) hc⟩⟩

/-- A colimit of a diagram whose values lie in the essential image of a fully faithful functor
`F` again lies in the essential image, provided `F` preserves colimits of that shape. -/
lemma essImage_prop_of_isColimit {J : Type*} [Category* J] [HasColimitsOfShape J C]
    [PreservesColimitsOfShape J F] {G : J ⥤ D} (hG : ∀ j, F.essImage (G.obj j)) {c : Cocone G}
    (hc : IsColimit c) : F.essImage c.pt :=
  ⟨colimit (Functor.essImage.liftFunctor G F hG),
    ⟨IsColimit.coconePointUniqueUpToIso
      ((IsColimit.precomposeInvEquiv (Functor.essImage.liftFunctorCompIso G F hG) _).symm
        (isColimitOfPreserves F (colimit.isColimit _))) hc⟩⟩

instance essImage_isClosedUnderLimitsOfShape (J : Type*) [Category* J] [HasLimitsOfShape J C]
    [PreservesLimitsOfShape J F] : F.essImage.IsClosedUnderLimitsOfShape J :=
  ObjectProperty.IsClosedUnderLimitsOfShape.mk' (by
    rintro _ ⟨G, hG⟩
    exact essImage_prop_of_isLimit F hG (limit.isLimit G))

instance essImage_isClosedUnderColimitsOfShape (J : Type*) [Category* J] [HasColimitsOfShape J C]
    [PreservesColimitsOfShape J F] : F.essImage.IsClosedUnderColimitsOfShape J :=
  ObjectProperty.IsClosedUnderColimitsOfShape.mk' (by
    rintro _ ⟨G, hG⟩
    exact essImage_prop_of_isColimit F hG (colimit.isColimit G))

instance essImage_isClosedUnderFiniteProducts [HasFiniteProducts C]
    [PreservesFiniteProducts F] : F.essImage.IsClosedUnderFiniteProducts :=
  ObjectProperty.IsClosedUnderFiniteProducts.of_isClosedUnderLimitsOfShape
    (fun (_ : Type) _ => inferInstance)

instance essImage_isClosedUnderFiniteCoproducts [HasFiniteCoproducts C]
    [PreservesFiniteCoproducts F] : F.essImage.IsClosedUnderFiniteCoproducts :=
  ObjectProperty.IsClosedUnderFiniteCoproducts.of_isClosedUnderColimitsOfShape
    (fun (_ : Type) _ => inferInstance)

instance essImage_containsZero [HasZeroObject C] [HasZeroObject D]
    [PreservesLimitsOfShape (Discrete.{0} PEmpty) F] : F.essImage.ContainsZero :=
  ⟨F.obj 0,
    (isZero_zero D).of_iso
      (IsTerminal.uniqueUpToIso (IsTerminal.isTerminalObj F 0 (isZero_zero C).isTerminal)
        (isZero_zero D).isTerminal),
    F.obj_mem_essImage 0⟩

variable [HasZeroMorphisms C] [HasZeroMorphisms D]

instance essImage_isClosedUnderKernels [HasEqualizers C]
    [PreservesLimitsOfShape WalkingParallelPair F] : F.essImage.IsClosedUnderKernels where
  kernels_le := by
    rintro _ ⟨f, k, hk, hf⟩
    exact F.essImage.prop_of_isLimit hk (by rintro (_ | _) <;> [exact hf.1; exact hf.2])

instance essImage_isClosedUnderCokernels [HasCoequalizers C]
    [PreservesColimitsOfShape WalkingParallelPair F] : F.essImage.IsClosedUnderCokernels where
  cokernels_le := by
    rintro _ ⟨f, k, hk, hf⟩
    exact F.essImage.prop_of_isColimit hk (by rintro (_ | _) <;> [exact hf.1; exact hf.2])

end EssentialImage

section Image

variable {C D : Type*} [Category* C] [Category* D] [CategoryTheory.Abelian C]
  [CategoryTheory.Abelian D] (F : C ⥤ D) [F.Full] [F.Faithful] [PreservesFiniteLimits F]
  [PreservesFiniteColimits F]

/-- The essential image of a fully faithful exact functor between abelian categories is closed
under images of morphisms. -/
lemma essImage_image {X Y : D} (f : X ⟶ Y) (hX : F.essImage X) (hY : F.essImage Y) :
    F.essImage (image f) :=
  F.essImage.prop_of_iso (CategoryTheory.Abelian.imageIsoImage f)
    (F.essImage.prop_kernel (cokernel.π f) hY (F.essImage.prop_cokernel f hX hY))

end Image

section FreydMitchell

variable (C : Type u) [Category.{v} C] [CategoryTheory.Abelian C]

/-- The ring over which Definition 7.7.1 realizes the abelian category `C` as a category of
modules. -/
abbrev moduleEmbeddingRing : Type (max u v) :=
  CategoryTheory.Abelian.FreydMitchell.EmbeddingRing C

/-- The full, faithful, exact embedding of an abelian category `C` into a category of modules
supplied by the Freyd-Mitchell theorem. -/
noncomputable abbrev moduleEmbedding : C ⥤ ModuleCat.{max u v} (moduleEmbeddingRing C) :=
  CategoryTheory.Abelian.FreydMitchell.functor C

/-- The full subcategory of `A`-mod appearing in Definition 7.7.1: the essential image of the
Freyd-Mitchell embedding of `C`. -/
abbrev moduleRealization : ObjectProperty (ModuleCat.{max u v} (moduleEmbeddingRing C)) :=
  (moduleEmbedding C).essImage

/-- Definition 7.7.1's equivalence: an abelian category is equivalent to a full subcategory of a
category of modules. -/
noncomputable def moduleRealizationEquiv : C ≌ (moduleRealization C).FullSubcategory :=
  (moduleEmbedding C).toEssImage.asEquivalence

/-- The equivalence of Definition 7.7.1 followed by the inclusion of the full subcategory is the
Freyd-Mitchell embedding. -/
noncomputable def moduleRealizationEquivCompι :
    (moduleRealizationEquiv C).functor ⋙ (moduleRealization C).ι ≅ moduleEmbedding C :=
  (moduleEmbedding C).toEssImageCompι

lemma moduleRealization_image {X Y : ModuleCat.{max u v} (moduleEmbeddingRing C)} (f : X ⟶ Y)
    (hX : moduleRealization C X) (hY : moduleRealization C Y) :
    moduleRealization C (image f) :=
  essImage_image _ f hX hY

/-- **Definition 7.7.1.** Every abelian category is equivalent to a full subcategory of the
category of left modules over a ring, closed under finite direct sums, kernels, cokernels and
images of morphisms. -/
theorem exists_equiv_moduleCat_fullSubcategory :
    ∃ (A : Type (max u v)) (_ : Ring A) (P : ObjectProperty (ModuleCat.{max u v} A)),
      P.ContainsZero ∧ P.IsClosedUnderIsomorphisms ∧
      P.IsClosedUnderFiniteProducts ∧ P.IsClosedUnderFiniteCoproducts ∧
      P.IsClosedUnderKernels ∧ P.IsClosedUnderCokernels ∧
      (∀ (X Y : ModuleCat.{max u v} A) (f : X ⟶ Y), P X → P Y → P (image f)) ∧
      Nonempty (C ≌ P.FullSubcategory) :=
  ⟨moduleEmbeddingRing C, inferInstance, moduleRealization C, inferInstance, inferInstance,
    inferInstance, inferInstance, inferInstance, inferInstance,
    fun _ _ f hX hY => moduleRealization_image C f hX hY, ⟨moduleRealizationEquiv C⟩⟩

end FreydMitchell

/-- The converse to Definition 7.7.1: a full subcategory of `A`-mod which contains a zero object
and is closed under kernels, cokernels and finite direct sums is an abelian category. -/
noncomputable abbrev abelianOfClosedFullSubcategory {A : Type u} [Ring A]
    (P : ObjectProperty (ModuleCat.{v} A)) [P.ContainsZero] [P.IsClosedUnderKernels]
    [P.IsClosedUnderCokernels] [P.IsClosedUnderFiniteProducts] :
    Etingof.Abelian P.FullSubcategory :=
  inferInstance

end Etingof
