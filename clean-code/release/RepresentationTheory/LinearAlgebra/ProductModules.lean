/-
Copyright (c) 2026 mathlib-initiative. All rights reserved.
Released under Apache 2.0 license as described in the file LICENCE.
Authors: Kim Morrison
-/

import Mathlib.LinearAlgebra.DirectSum.Finite
import RepresentationTheory.Alignment.Attribute

/-! # Product modules -/

namespace RepresentationTheory.LinearAlgebra.ProductModules

/-- A type constructor taking two type arguments. -/
@[source_ref "Chapter2/Definition2.3.7" (role := supporting),
  source_ref "Chapter2/Discussion_2.1_overview/Derived7" (role := primary)]
abbrev BinaryTypeConstructor (V₁ V₂ : Type*) := V₁ × V₂

/-- Scalar multiplication on a pair acts componentwise. -/
@[source_ref "Chapter2/Definition2.3.7" (role := primary)]
theorem smul_prod_mk
    (A : Type*) (V₁ V₂ : Type*) [Ring A]
    [AddCommGroup V₁] [AddCommGroup V₂] [Module A V₁] [Module A V₂]
    (a : A) (v₁ : V₁) (v₂ : V₂) :
    a • ((v₁, v₂) : BinaryTypeConstructor V₁ V₂) =
      (a • v₁, a • v₂) :=
  rfl

end RepresentationTheory.LinearAlgebra.ProductModules
