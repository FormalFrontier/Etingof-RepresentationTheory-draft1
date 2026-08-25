/-
Copyright (c) 2026 mathlib-initiative. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: mathlib-initiative
-/
import Mathlib.RepresentationTheory.Maschke
import Mathlib.Algebra.Category.ModuleCat.Abelian
import Mathlib.Algebra.Category.ModuleCat.EpiMono
import Mathlib.Algebra.Homology.ShortComplex.Exact
import Mathlib.LinearAlgebra.Projection
import Mathlib.RingTheory.SimpleModule.Basic
import RepresentationTheory.CategoryTheory.Abelian.CategoryProperties
import RepresentationTheory.Alignment.Attribute

/-!
# Semisimplicity

This module records semisimplicity results for monoid algebras and their module categories.
-/

open CategoryTheory

namespace RepresentationTheory.Semisimplicity

/-- The monoid algebra of a finite group over a field is a semisimple ring when the group cardinality is invertible in the field. -/
theorem monoidAlgebra_isSemisimpleRing_of_isUnit_card
    (k : Type*) (G : Type*) [Field k] [Group G] [Fintype G]
    (h : IsUnit (Fintype.card G : k)) :
    IsSemisimpleRing (MonoidAlgebra k G) := by
  classical
  haveI : NeZero (Nat.card G : k) := by
    rw [neZero_iff]
    rw [Fintype.card_eq_nat_card] at h
    exact h.ne_zero
  infer_instance

/-- The module category of a semisimple ring satisfies the displayed auxiliary category property. -/
theorem moduleCat_auxiliaryProperty_of_isSemisimpleRing
    (R : Type*) [Ring R] [IsSemisimpleRing R] :
    RepresentationTheory.CategoryTheory.Abelian.CategoryProperties.AbelianCategoryProperty
      (ModuleCat R) := by
  intro S hS
  have hf : Function.Injective S.f.hom :=
    LinearMap.ker_eq_bot.mp ((ModuleCat.mono_iff_ker_eq_bot S.f).mp hS.mono_f)
  obtain ⟨q, hq⟩ := exists_isCompl (LinearMap.range S.f.hom)
  let r : S.X₂ ⟶ S.X₁ := ModuleCat.ofHom (LinearMap.linearProjOfIsCompl q S.f.hom hf hq)
  have f_r : S.f ≫ r = 𝟙 S.X₁ := by
    apply ModuleCat.hom_ext
    ext x
    simp [r]
  exact ⟨ShortComplex.Splitting.ofExactOfRetraction S hS.exact r f_r hS.epi_g⟩

/-- When a finite group's cardinality is invertible in the field, the module category over its monoid algebra satisfies the displayed auxiliary category property. -/
@[source_ref "Chapter7/Example7.9.5" (role := primary)]
theorem monoidAlgebra_moduleCat_auxiliaryProperty_of_isUnit_card
    (k : Type*) (G : Type*) [Field k] [Group G] [Fintype G]
    (h : IsUnit (Fintype.card G : k)) :
    RepresentationTheory.CategoryTheory.Abelian.CategoryProperties.AbelianCategoryProperty
      (ModuleCat (MonoidAlgebra k G)) :=
  haveI : IsSemisimpleRing (MonoidAlgebra k G) :=
    monoidAlgebra_isSemisimpleRing_of_isUnit_card k G h
  moduleCat_auxiliaryProperty_of_isSemisimpleRing _

end RepresentationTheory.Semisimplicity
