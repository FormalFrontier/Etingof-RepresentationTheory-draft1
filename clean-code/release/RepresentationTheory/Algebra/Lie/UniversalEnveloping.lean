/-
Copyright (c) 2026 mathlib-initiative. All rights reserved.
Released under Apache 2.0 license as described in the file LICENCE.
Authors: Kim Morrison
-/
import Mathlib.Algebra.Lie.UniversalEnveloping
import RepresentationTheory.Alignment.Attribute

/-! # Representations of universal enveloping algebras -/

namespace RepresentationTheory.Algebra.Lie.UniversalEnveloping

attribute [local instance 100] LieRing.ofAssociativeRing

variable (k : Type*) [Field k]
variable (L : Type*) [LieRing L] [LieAlgebra k L]
variable (V : Type*) [AddCommGroup V] [Module k V]

/-- Equivalence between Lie actions on a module and algebra homomorphisms from the universal enveloping algebra to its endomorphisms. -/
@[source_ref "Chapter2/Example2.9.8/Derived5" (role := primary),
  source_ref "Chapter2/Exercise2.9.11" (role := supporting),
  source_ref "Chapter2/Problem2.14.3/Derived2" (role := supporting)]
noncomputable def representationAlgHomEquiv :
    (L →ₗ⁅k⁆ Module.End k V) ≃
      (UniversalEnvelopingAlgebra k L →ₐ[k] Module.End k V) :=
  UniversalEnvelopingAlgebra.lift k

end RepresentationTheory.Algebra.Lie.UniversalEnveloping
