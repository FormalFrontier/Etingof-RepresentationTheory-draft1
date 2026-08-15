/-
Copyright (c) 2026 mathlib-initiative. All rights reserved.
Released under Apache 2.0 license as described in the file LICENCE.
Authors: Kim Morrison
-/

import RepresentationTheory.CategoryTheory.QuiverLinearDiagrams
import RepresentationTheory.Alignment.Attribute
import Mathlib.LinearAlgebra.Prod

/-! # Quiver linear diagram constructions -/

namespace RepresentationTheory.CategoryTheory.QuiverLinearDiagrams.QuiverLinearDiagram

/-- Combines two quiver-indexed objects over a commutative semiring into one object. -/
@[source_ref "Chapter2/Definition2.8.9" (role := supporting)]
noncomputable def binaryConstruction (k : Type*) (Q : Type*)
    [CommSemiring k] [Quiver Q]
    (ρ₁ ρ₂ : QuiverLinearDiagram k Q) : QuiverLinearDiagram k Q where
  obj := fun v => ρ₁.obj v × ρ₂.obj v
  map := fun h => (ρ₁.map h).prodMap (ρ₂.map h)

end RepresentationTheory.CategoryTheory.QuiverLinearDiagrams.QuiverLinearDiagram
