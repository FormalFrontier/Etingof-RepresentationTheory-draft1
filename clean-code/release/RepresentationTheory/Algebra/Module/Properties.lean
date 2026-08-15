/-
Copyright (c) 2026 mathlib-initiative. All rights reserved.
Released under Apache 2.0 license as described in the file LICENCE.
Authors: mathlib-initiative
-/
import Mathlib.Algebra.Module.Injective
import RepresentationTheory.Alignment.Attribute

namespace RepresentationTheory.Algebra.Module.Properties

/-- A proposition concerning a ring and an additive commutative group carrying a module structure over it. -/
@[source_ref "Chapter8/Definition8.1.6" (role := supporting)]
abbrev RingModuleProperty (R : Type*) (M : Type*) [Ring R] [AddCommGroup M]
    [Module R M] :=
  Module.Injective R M

end RepresentationTheory.Algebra.Module.Properties
