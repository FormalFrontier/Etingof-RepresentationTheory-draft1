/-
Copyright (c) 2026 mathlib-initiative. All rights reserved.
Released under Apache 2.0 license as described in the file LICENCE.
Authors: mathlib-initiative
-/

import Mathlib.Algebra.Category.ModuleCat.Projective
import Mathlib.Algebra.Category.ModuleCat.Abelian
import Mathlib.CategoryTheory.Abelian.Projective.Resolution
import Mathlib.LinearAlgebra.Finsupp.VectorSpace
import Mathlib.LinearAlgebra.Finsupp.LinearCombination
import Mathlib.LinearAlgebra.Basis.Defs
import Mathlib.LinearAlgebra.FreeModule.Basic
import RepresentationTheory.CategoryTheory.Abelian.ObjectData
import RepresentationTheory.Alignment.Attribute

/-!
# Projective resolutions in abelian categories
-/

namespace RepresentationTheory.CategoryTheory.Abelian.ProjectiveResolution

open _root_.CategoryTheory
open _root_.CategoryTheory.Category _root_.CategoryTheory.Limits _root_.CategoryTheory.Projective

universe v u

/-- States that a projective resolution of a module exists. -/
@[source_ref "Chapter8/Exercise8.2.2" (role := primary)]
theorem nonempty_projectiveResolution (A : Type u) [Ring A] (M : ModuleCat.{u} A) :
    Nonempty
      (RepresentationTheory.CategoryTheory.Abelian.ObjectData.AbelianCategoryObjectData M) :=
  ⟨CategoryTheory.ProjectiveResolution.of M⟩

variable {C : Type u} [Category.{v} C] [Abelian C]
variable (over : C → C) (π : (X : C) → over X ⟶ X)

/-- Constructs a morphism from the object assigned to a kernel into the source of the original
morphism. -/
@[reducible] noncomputable def assignedKernelToSource {X Y : C} (f : X ⟶ Y) :
    over (kernel f) ⟶ X :=
  π (kernel f) ≫ kernel.ι f

/-- Composing the morphism from the assigned kernel object with the original morphism yields
zero. -/
lemma assignedKernelToSource_comp {X Y : C} (f : X ⟶ Y) :
    assignedKernelToSource over π f ≫ f = 0 := by
  simp [assignedKernelToSource]

/-- The morphism from the assigned kernel object and the original morphism form an exact short
complex. -/
theorem assignedKernelToSource_exact [∀ X, Epi (π X)] {X Y : C} (f : X ⟶ Y) :
    (ShortComplex.mk (assignedKernelToSource over π f) f
      (assignedKernelToSource_comp over π f)).Exact := by
  let α : ShortComplex.mk (assignedKernelToSource over π f) f
      (assignedKernelToSource_comp over π f) ⟶
      ShortComplex.mk (kernel.ι f) f (by simp) :=
    { τ₁ := π _
      τ₂ := 𝟙 _
      τ₃ := 𝟙 _ }
  rw [ShortComplex.exact_iff_of_epi_of_isIso_of_mono α]
  apply ShortComplex.exact_of_f_is_kernel
  apply kernelIsKernel

/-- Builds a chain complex from an object assignment, morphisms from assigned objects to the
original objects, and a chosen object. -/
noncomputable def iteratedKernelComplex (Z : C) : ChainComplex C ℕ :=
  ChainComplex.mk' (over Z) (over (kernel (π Z))) (assignedKernelToSource over π (π Z))
    (fun f => ⟨over (kernel f), assignedKernelToSource over π f,
      assignedKernelToSource_comp over π f⟩)

/-- The differential from degree one to degree zero is the morphism from the object assigned to
the kernel of the comparison map at the chosen object into that map's source. -/
lemma iteratedKernelComplex_d_one_zero (Z : C) :
    (iteratedKernelComplex over π Z).d 1 0 = assignedKernelToSource over π (π Z) := by
  simp [iteratedKernelComplex]

/-- The constructed complex is exact at every positive successor degree. -/
lemma iteratedKernelComplex_exactAt_succ [∀ X, Epi (π X)] (Z : C) (n : ℕ) :
    (iteratedKernelComplex over π Z).ExactAt (n + 1) := by
  rw [HomologicalComplex.exactAt_iff' _ (n + 1 + 1) (n + 1) n (by simp) (by simp)]
  simp only [HomologicalComplex.sc', HomologicalComplex.shortComplexFunctor',
    iteratedKernelComplex, ChainComplex.mk', ChainComplex.mk, ChainComplex.of_d]
  match n with
  | 0 => apply assignedKernelToSource_exact
  | n + 1 => apply assignedKernelToSource_exact

/-- Every degree of the constructed complex is projective. -/
lemma iteratedKernelComplex_projective [∀ X, Projective (over X)] (Z : C) (n : ℕ) :
    Projective ((iteratedKernelComplex over π Z).X n) := by
  obtain (_ | _ | _ | n) := n <;> exact (inferInstance : Projective (over _))

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-- Constructs a projective resolution from an object assignment with projective values and
epimorphisms to the original objects. -/
noncomputable def projectiveResolutionOf [∀ X, Projective (over X)] [∀ X, Epi (π X)] (Z : C) :
    ProjectiveResolution Z where
  complex := iteratedKernelComplex over π Z
  projective := iteratedKernelComplex_projective over π Z
  π := (ChainComplex.toSingle₀Equiv _ _).symm ⟨π Z, by
    rw [iteratedKernelComplex_d_one_zero, assoc, kernel.condition, comp_zero]⟩
  quasiIso := ⟨fun n => by
    cases n
    · rw [ChainComplex.quasiIsoAt₀_iff, ShortComplex.quasiIso_iff_of_zeros']
      · dsimp
        refine (ShortComplex.exact_and_epi_g_iff_of_iso ?_).2
          ⟨assignedKernelToSource_exact over π (π Z), by dsimp; infer_instance⟩
        exact ShortComplex.isoMk (Iso.refl _) (Iso.refl _) (Iso.refl _)
          (by simp [iteratedKernelComplex]) (by simp)
      all_goals rfl
    · rw [quasiIsoAt_iff_exactAt']
      · apply iteratedKernelComplex_exactAt_succ
      · apply ChainComplex.exactAt_succ_single_obj⟩

/-- In every degree, the constructed projective resolution has a term equal to the object
assigned to some object. -/
lemma projectiveResolutionOf_exists_term_eq_assignedObject
    [∀ X, Projective (over X)] [∀ X, Epi (π X)] (Z : C) (n : ℕ) :
    ∃ Y : C, (projectiveResolutionOf over π Z).complex.X n = over Y := by
  obtain (_ | _ | _ | n) := n
  · exact ⟨Z, rfl⟩
  · exact ⟨kernel (π Z), rfl⟩
  · exact ⟨_, rfl⟩
  · exact ⟨_, rfl⟩

variable {A : Type u} [Ring A]

/-- Assigns a module object to each module. -/
noncomputable def freeCover (M : ModuleCat.{u} A) : ModuleCat.{u} A :=
  ModuleCat.of A (M →₀ A)

/-- Provides a basis for the underlying module of the associated module object. -/
noncomputable def freeCoverBasis (M : ModuleCat.{u} A) : Module.Basis M A (freeCover M) :=
  Finsupp.basisSingleOne

/-- The underlying module of the associated module object is free. -/
instance freeCover_free (M : ModuleCat.{u} A) : Module.Free A (freeCover M) :=
  Module.Free.of_basis (freeCoverBasis M)

/-- The associated module object is projective. -/
instance freeCover_projective (M : ModuleCat.{u} A) : Projective (freeCover M) :=
  ModuleCat.projective_of_free (freeCoverBasis M)

/-- The morphism from the associated module object to the given module. -/
noncomputable def freeCoverTo (M : ModuleCat.{u} A) : freeCover M ⟶ M :=
  ModuleCat.ofHom (Finsupp.linearCombination A id)

/-- The morphism from the associated module object to the given module is an epimorphism. -/
instance freeCoverTo_epi (M : ModuleCat.{u} A) : Epi (freeCoverTo M) := by
  rw [ModuleCat.epi_iff_surjective]
  intro m
  refine ⟨Finsupp.single m 1, ?_⟩
  change (Finsupp.linearCombination A id) (Finsupp.single m 1) = m
  rw [Finsupp.linearCombination_single, one_smul, id_eq]

/-- Assigns a projective resolution to a module. -/
@[source_ref "Chapter8/Exercise8.2.2" (role := supporting)]
noncomputable def freeProjectiveResolution (M : ModuleCat.{u} A) :
    RepresentationTheory.CategoryTheory.Abelian.ObjectData.AbelianCategoryObjectData M :=
  projectiveResolutionOf freeCover freeCoverTo M

/-- Every degree of this projective resolution has a free underlying module. -/
instance freeProjectiveResolution_free (M : ModuleCat.{u} A) (n : ℕ) :
    Module.Free A ((freeProjectiveResolution M).complex.X n) := by
  obtain ⟨Y, hY⟩ :=
    projectiveResolutionOf_exists_term_eq_assignedObject freeCover freeCoverTo M n
  rw [freeProjectiveResolution, hY]
  infer_instance

/-- Shows that a module has a projective resolution with free underlying modules in every
degree. -/
@[source_ref "Chapter8/Exercise8.2.2" (role := supporting)]
theorem exists_free_projectiveResolution (A : Type u) [Ring A] (M : ModuleCat.{u} A) :
    ∃ P : RepresentationTheory.CategoryTheory.Abelian.ObjectData.AbelianCategoryObjectData M,
      ∀ n, Module.Free A (P.complex.X n) :=
  ⟨freeProjectiveResolution M, fun n => freeProjectiveResolution_free M n⟩

end RepresentationTheory.CategoryTheory.Abelian.ProjectiveResolution
