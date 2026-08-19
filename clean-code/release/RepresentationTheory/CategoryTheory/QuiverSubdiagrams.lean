/-
Copyright (c) 2026 mathlib-initiative. All rights reserved.
Released under Apache 2.0 license as described in the file LICENCE.
Authors: Kim Morrison
-/

import RepresentationTheory.CategoryTheory.QuiverLinearDiagrams
import RepresentationTheory.Alignment.Attribute
import Mathlib.Algebra.Module.Submodule.LinearMap

/-! # Quiver subdiagrams -/

namespace RepresentationTheory.CategoryTheory.QuiverSubdiagrams

open RepresentationTheory.CategoryTheory.QuiverLinearDiagrams

/-- A family of submodules of a quiver linear diagram compatible with its arrow maps. -/
@[source_ref "Chapter2/Definition2.8.8" (role := supporting)]
structure QuiverSubdiagram (k : Type*) (Q : Type*) [CommSemiring k]
    [Quiver Q] (ρ : AuxiliaryQuiverModuleData k Q) where
  /-- Returns the submodule selected at a vertex. -/
  carrier : ∀ v, Submodule k (ρ.obj v)
  /-- An arrow map sends an element of the source submodule into the target submodule. -/
  map_mem : ∀ {v w : Q} (e : v ⟶ w) (x : ρ.obj v),
    x ∈ carrier v → ρ.map e x ∈ carrier w

namespace QuiverSubdiagram

variable {k Q : Type*} [CommSemiring k] [Quiver Q]
variable {ρ : AuxiliaryQuiverModuleData k Q}

/-- Converts a quiver subdiagram into a quiver linear diagram. -/
@[source_ref "Chapter2/Definition2.8.8" (role := supporting)]
noncomputable def toDiagram (S : QuiverSubdiagram k Q ρ) :
    AuxiliaryQuiverModuleData k Q where
  obj i := S.carrier i
  map e := LinearMap.restrict (ρ.map e) (fun x hx => S.map_mem e x hx)

/-- The vertex type of the converted diagram is the subtype of the corresponding carrier submodule. -/
@[simp] theorem obj_toDiagram (S : QuiverSubdiagram k Q ρ) (i : Q) :
    S.toDiagram.obj i = S.carrier i :=
  rfl

end QuiverSubdiagram

end RepresentationTheory.CategoryTheory.QuiverSubdiagrams
