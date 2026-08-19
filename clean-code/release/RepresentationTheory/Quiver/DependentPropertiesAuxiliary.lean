/-
Copyright (c) 2026 mathlib-initiative. All rights reserved.
Released under Apache 2.0 license as described in the file LICENCE.
Authors: Kim Morrison
-/

import RepresentationTheory.Alignment.Attribute
import RepresentationTheory.CategoryTheory.QuiverAuxiliary
import RepresentationTheory.CategoryTheory.QuiverLinearMaps
import RepresentationTheory.Algebra.Quiver.AuxiliaryConstructions

/-! # Auxiliary dependent properties for quiver-indexed objects -/

namespace RepresentationTheory.CategoryTheory.QuiverAuxiliary.AuxiliaryType

open RepresentationTheory.CategoryTheory.QuiverLinearDiagrams

universe u v w q

variable {k : Type u} {Q : Type v} [CommSemiring k] [Quiver.{w} Q]
variable {ρ : AuxiliaryQuiverModuleData.{u, v, q, w} k Q}

/-- Selects an element of the displayed dependent type for each quiver-dependent object. -/
noncomputable def elementAux (ρ : AuxiliaryQuiverModuleData.{u, v, q, w} k Q) :
    AuxiliaryType k Q ρ where
  carrier := fun _ => ⊥
  map_mem := by simp

/-- Selects a second element of the displayed dependent type for each quiver-dependent object. -/
noncomputable def elementAux' (ρ : AuxiliaryQuiverModuleData.{u, v, q, w} k Q) :
    AuxiliaryType k Q ρ where
  carrier := fun _ => ⊤
  map_mem := by simp

/-- The second auxiliary predicate on an element of the displayed dependent type. -/
def predicateAux' (S : AuxiliaryType k Q ρ) : Prop :=
  ∀ i, S.carrier i = ⊥

/-- The first auxiliary predicate on an element of the displayed dependent type. -/
def predicateAux (S : AuxiliaryType k Q ρ) : Prop :=
  ∀ i, S.carrier i = ⊤

/-- The first auxiliary selection satisfies the second auxiliary predicate. -/
theorem predicateAux'_elementAux : predicateAux' (elementAux ρ) := fun _ => rfl

/-- The second auxiliary selection satisfies the first auxiliary predicate. -/
theorem predicateAux_elementAux' : predicateAux (elementAux' ρ) := fun _ => rfl

end RepresentationTheory.CategoryTheory.QuiverAuxiliary.AuxiliaryType

namespace RepresentationTheory.CategoryTheory.QuiverLinearDiagrams.AuxiliaryQuiverModuleData

open RepresentationTheory.CategoryTheory.QuiverLinearMaps
open RepresentationTheory.CategoryTheory.QuiverAuxiliary

universe u v w q

variable {k : Type u} {Q : Type v} [CommSemiring k] [Quiver.{w} Q]

/-- The fourth auxiliary predicate on the displayed quiver-dependent object. -/
@[source_ref "Chapter2/Discussion_quiver_irreducible_indecomposable" (role := supporting)]
def predicateAux''' (ρ : AuxiliaryQuiverModuleData.{u, v, q, w} k Q) : Prop :=
  ∀ (i : Q) (x : ρ.obj i), x = 0

/-- The third auxiliary predicate on the displayed quiver-dependent object. -/
@[source_ref "Chapter2/Discussion_quiver_irreducible_indecomposable" (role := supporting)]
def predicateAux'' (ρ : AuxiliaryQuiverModuleData.{u, v, q, w} k Q) : Prop :=
  ¬predicateAux''' ρ

/-- The second auxiliary predicate on the displayed quiver-dependent object. -/
@[source_ref "Chapter2/Discussion_quiver_irreducible_indecomposable" (role := supporting)]
def predicateAux' (ρ : AuxiliaryQuiverModuleData.{u, v, q, w} k Q) : Prop :=
  predicateAux'' ρ ∧ ∀ S : AuxiliaryType k Q ρ,
    S.predicateAux' ∨ S.predicateAux

/-- The first auxiliary predicate on the displayed quiver-dependent object. -/
@[source_ref "Chapter2/Discussion_quiver_irreducible_indecomposable" (role := supporting)]
def predicateAux (ρ : AuxiliaryQuiverModuleData.{u, v, q, w} k Q) : Prop :=
  predicateAux'' ρ ∧ ∀ (ρ₁ ρ₂ : AuxiliaryQuiverModuleData.{u, v, q, w} k Q),
    AuxiliaryQuiverEquivData k Q ρ (auxiliaryBinaryConstruction k Q ρ₁ ρ₂) →
      predicateAux''' ρ₁ ∨ predicateAux''' ρ₂

end RepresentationTheory.CategoryTheory.QuiverLinearDiagrams.AuxiliaryQuiverModuleData
