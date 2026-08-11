import EtingofRepresentationTheory.Infrastructure.MoritaFGRestriction
import Mathlib.Algebra.Category.FGModuleCat.Abelian
import Mathlib.Algebra.Category.ModuleCat.Projective
import Mathlib.CategoryTheory.Preadditive.Projective.Preserves
import Mathlib.RingTheory.Noetherian.Basic

/-!
# The progenerator extracted from an equivalence of finitely generated module categories

The converse in Definition 9.7.1 extends an equivalence
`FGModuleCat A ≌ FGModuleCat B` to all modules. The algebraic starting point of every such
reconstruction is the image of the regular `A`-module: it is a finitely generated projective
generator on the `B` side.

This file packages and proves that starting point. It does not assume an extension to
`ModuleCat`, so it is genuine infrastructure on the book-faithful `fmod` equivalence itself.
The successor passage from this finite progenerator to an equivalence on arbitrary modules is
proved in `Infrastructure/MoritaFiniteProgenerator.lean` and assembled in
`Chapter9/Introduction_9_7_Morita.lean`.
-/

universe u

open CategoryTheory

namespace Etingof

/-- A categorical finitely generated progenerator: a projective separator in `FGModuleCat R`.
For a finite-dimensional algebra this is the categorical form of a finitely generated
projective generator module. -/
structure IsFmodProgenerator {R : Type u} [Ring R] (P : FGModuleCat.{u} R) : Prop where
  projective : Projective P
  separator : IsSeparator P

/-- The regular module is a separator already inside the finitely generated subcategory. -/
theorem isSeparator_regular_fmod (R : Type u) [Ring R] :
    IsSeparator (FGModuleCat.of.{u} R R) := fun X Y f g h => by
  simp only [ObjectProperty.singleton_iff, FGModuleCat.hom_ext_iff,
    FGModuleCat.hom_hom_comp, LinearMap.ext_iff, LinearMap.coe_comp, Function.comp_apply,
    forall_eq'] at h
  apply FGModuleCat.hom_ext
  ext x
  have hx := h (FGModuleCat.ofHom (LinearMap.toSpanSingleton R X x)) 1
  change f.hom.hom ((LinearMap.toSpanSingleton R X x) 1) =
    g.hom.hom ((LinearMap.toSpanSingleton R X x) 1) at hx
  simpa [LinearMap.toSpanSingleton_apply] using hx

/-- Over a left-Noetherian ring, the regular object is projective in `FGModuleCat`.

The Noetherian hypothesis ensures that `FGModuleCat R` is abelian and that its inclusion into
`ModuleCat R` preserves epimorphisms. Projectivity then descends from the free rank-one regular
module in the full module category. -/
theorem projective_regular_fmod (R : Type u) [Ring R] [IsNoetherianRing R] :
    Projective (FGModuleCat.of.{u} R R) := by
  let ι : FGModuleCat.{u} R ⥤ ModuleCat.{u} R :=
    forget₂ (FGModuleCat.{u} R) (ModuleCat.{u} R)
  haveI : ι.PreservesEpimorphisms := by infer_instance
  refine Projective.mk (fun {X Y} f e _ => ?_)
  haveI : Epi (ι.map e) := inferInstance
  have he : Function.Surjective e.hom.hom :=
    (ModuleCat.epi_iff_surjective (ι.map e)).mp inferInstance
  obtain ⟨y, hy⟩ := he (f.hom.hom 1)
  let l : FGModuleCat.of.{u} R R ⟶ X :=
    FGModuleCat.ofHom (LinearMap.toSpanSingleton R X y)
  refine ⟨l, ?_⟩
  apply FGModuleCat.hom_ext
  apply LinearMap.ext
  intro r
  change e.hom.hom (r • y) = f.hom.hom r
  rw [map_smul, hy]
  have hf := map_smul f.hom.hom r (1 : R)
  simpa using hf.symm

/-- The regular object is a finitely generated progenerator. -/
theorem regular_isFmodProgenerator (R : Type u) [Ring R] [IsNoetherianRing R] :
    IsFmodProgenerator (FGModuleCat.of.{u} R R) :=
  ⟨projective_regular_fmod R, isSeparator_regular_fmod R⟩

/-- **Progenerator extraction from an `fmod` equivalence.** The image of the regular module
under any equivalence of finitely generated module categories is a finitely generated
projective generator.

This is the first algebraic half of the converse Morita bridge; its full-module successor is
`IsProgenerator.moduleCatEquivEndOp`. -/
theorem fmodEquiv_regular_isFmodProgenerator {A B : Type u}
    [Ring A] [IsNoetherianRing A] [Ring B]
    (E : FGModuleCat.{u} A ≌ FGModuleCat.{u} B) :
    IsFmodProgenerator (E.functor.obj (FGModuleCat.of.{u} A A)) := by
  haveI : E.functor.IsEquivalence := E.isEquivalence_functor
  refine ⟨?_, ?_⟩
  · exact E.map_projective_iff (FGModuleCat.of.{u} A A) |>.mpr (projective_regular_fmod A)
  · exact (isSeparator_regular_fmod A).of_equivalence E

/-- Existential form directly consumable from the book-faithful Morita predicate. -/
theorem MoritaEquivalentFmod.exists_isFmodProgenerator {A B : Type u}
    [Ring A] [IsNoetherianRing A] [Ring B]
    (h : MoritaEquivalentFmod A B) :
    ∃ P : FGModuleCat.{u} B, IsFmodProgenerator P := by
  obtain ⟨E⟩ := h
  exact ⟨E.functor.obj (FGModuleCat.of.{u} A A), fmodEquiv_regular_isFmodProgenerator E⟩

/-- Finite-dimensional-algebra specialization matching Definition 9.7.1 exactly. The
Noetherian hypothesis required above is automatic for a module-finite algebra over a field. -/
theorem MoritaEquivalentFmod.exists_isFmodProgenerator_of_finiteDimensional
    {k A B : Type u} [Field k]
    [Ring A] [Algebra k A] [Module.Finite k A]
    [Ring B] [Algebra k B] [Module.Finite k B]
    (h : MoritaEquivalentFmod A B) :
    ∃ P : FGModuleCat.{u} B, IsFmodProgenerator P := by
  letI : IsNoetherianRing A := IsNoetherianRing.of_finite k A
  exact h.exists_isFmodProgenerator

end Etingof
