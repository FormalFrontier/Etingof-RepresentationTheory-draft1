/-
Copyright (c) 2026 FormalFrontier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENCE.
Authors: FormalFrontier
-/

import Mathlib.CategoryTheory.Adjunction.Basic
import RepresentationTheory.Alignment.Attribute

/-!
# Data associated with pairs of functors

This module provides a type-valued construction associated with oppositely directed functors.
-/

namespace RepresentationTheory.FunctorPair

/-- A type-valued construction associated with a functor from `C` to `D` and a functor from `D` to `C`. -/
@[source_ref "Chapter7/Definition7.6.1" (role := supporting)]
abbrev Data {C : Type*} {D : Type*} [CategoryTheory.Category C]
    [CategoryTheory.Category D] (F : CategoryTheory.Functor C D)
    (G : CategoryTheory.Functor D C) := CategoryTheory.Adjunction F G

end RepresentationTheory.FunctorPair
