/-
Copyright (c) 2026 FormalFrontier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENCE.
Authors: FormalFrontier
-/
import Mathlib.Algebra.Module.Projective
import RepresentationTheory.Alignment.Attribute

namespace RepresentationTheory.Algebra.Module.Property

/-- A proposition associated with a module over a ring. -/
@[source_ref "Chapter8/Definition8.1.2" (role := supporting)]
abbrev ModuleProperty (R : Type*) (M : Type*) [Ring R] [AddCommGroup M]
    [Module R M] :=
  Module.Projective R M

end RepresentationTheory.Algebra.Module.Property
