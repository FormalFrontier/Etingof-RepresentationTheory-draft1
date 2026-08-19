/-
Copyright (c) 2026 mathlib-initiative. All rights reserved.
Released under Apache 2.0 license as described in the file LICENCE.
Authors: mathlib-initiative
-/

import RepresentationTheory.ModuleCat.FiniteUnderEquivalence
import Mathlib.Algebra.Category.FGModuleCat.Abelian
import Mathlib.Algebra.Category.ModuleCat.Projective
import Mathlib.CategoryTheory.Preadditive.Projective.Preserves
import Mathlib.RingTheory.Noetherian.Basic

universe u

open CategoryTheory

namespace RepresentationTheory.FGModuleCat.ProjectiveSeparators

/-- A property of a finitely generated module that entails projectivity and separator behavior. -/
structure IsProjectiveSeparator {R : Type u} [Ring R] (P : FGModuleCat.{u} R) : Prop where
  /-- A finitely generated module with the designated projective-separator property is projective. -/
  projective : Projective P
  /-- A finitely generated module with the designated projective-separator property is a separator. -/
  isSeparator : IsSeparator P

/-- A ring regarded as a finitely generated module over itself is a separator. -/
theorem isSeparator_regularModule (R : Type u) [Ring R] :
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

/-- A Noetherian ring regarded as a finitely generated module over itself is projective. -/
theorem projective_regularModule (R : Type u) [Ring R] [IsNoetherianRing R] :
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

/-- The regular module over a Noetherian ring has the projective-separator property. -/
theorem isProjectiveSeparator_regularModule (R : Type u) [Ring R] [IsNoetherianRing R] :
    IsProjectiveSeparator (FGModuleCat.of.{u} R R) :=
  ⟨projective_regularModule R, isSeparator_regularModule R⟩

/-- An equivalence of finitely generated module categories sends the regular module over a Noetherian ring to a module with the projective-separator property. -/
theorem isProjectiveSeparator_equivalence_obj_regular {A B : Type u}
    [Ring A] [IsNoetherianRing A] [Ring B]
    (E : FGModuleCat.{u} A ≌ FGModuleCat.{u} B) :
    IsProjectiveSeparator (E.functor.obj (FGModuleCat.of.{u} A A)) := by
  haveI : E.functor.IsEquivalence := E.isEquivalence_functor
  refine ⟨?_, ?_⟩
  · exact E.map_projective_iff (FGModuleCat.of.{u} A A) |>.mpr (projective_regularModule A)
  · exact (isSeparator_regularModule A).of_equivalence E

end RepresentationTheory.FGModuleCat.ProjectiveSeparators

namespace RepresentationTheory.RingAuxiliary

/-- For the designated relation from a Noetherian ring to another ring, there exists a finitely generated module with the projective-separator property. -/
theorem RingAuxiliary'.exists_isProjectiveSeparator_of_isNoetherianRing {A B : Type u}
    [Ring A] [IsNoetherianRing A] [Ring B]
    (h : RingAuxiliary' A B) :
    ∃ P : FGModuleCat.{u} B,
      RepresentationTheory.FGModuleCat.ProjectiveSeparators.IsProjectiveSeparator P := by
  obtain ⟨E⟩ := h
  exact ⟨E.functor.obj (FGModuleCat.of.{u} A A),
    RepresentationTheory.FGModuleCat.ProjectiveSeparators.isProjectiveSeparator_equivalence_obj_regular E⟩

/-- For the designated relation between finite algebras, there exists a finitely generated module with the projective-separator property. -/
theorem RingAuxiliary'.exists_isProjectiveSeparator_of_finiteAlgebras
    {k A B : Type u} [Field k]
    [Ring A] [Algebra k A] [Module.Finite k A]
    [Ring B] [Algebra k B] [Module.Finite k B]
    (h : RingAuxiliary' A B) :
    ∃ P : FGModuleCat.{u} B,
      RepresentationTheory.FGModuleCat.ProjectiveSeparators.IsProjectiveSeparator P := by
  letI : IsNoetherianRing A := IsNoetherianRing.of_finite k A
  exact h.exists_isProjectiveSeparator_of_isNoetherianRing

end RepresentationTheory.RingAuxiliary

/-- A ring regarded as a finitely generated module over itself is a separator. -/
alias _root_.RepresentationTheory.FGModuleCat.ProjectiveSeparators.FGModuleCat.isSeparator_regularModule := _root_.RepresentationTheory.FGModuleCat.ProjectiveSeparators.isSeparator_regularModule
