/-
Copyright (c) 2026 mathlib-initiative. All rights reserved.
Released under Apache 2.0 license as described in the file LICENCE.
Authors: Kim Morrison
-/
import Mathlib.Algebra.Lie.Abelian
import Mathlib.Algebra.Lie.OfAssociative
import RepresentationTheory.Algebra.Lie.Module.Predicates
import RepresentationTheory.Alignment.Attribute

/-! # Basic Lie module constructions -/

set_option linter.style.whitespace false

namespace RepresentationTheory.Algebra.Lie.Module.Examples

open RepresentationTheory.Algebra.Lie.Module.Predicates

attribute [local instance 100] LieRing.ofAssociativeRing

variable (k : Type*) [CommRing k] (L : Type*) [LieRing L] [LieAlgebra k L]

/-- A property of the singleton trivial Lie module. -/
@[source_ref "Chapter2/Example2.9.8" (role := primary)]
theorem punitTrivialModuleProperty :
    LieModule.AuxiliaryPredicate k L (TrivialLieModule k L PUnit) := inferInstance

omit [CommRing k] [LieRing L] [LieAlgebra k L] in
/-- The singleton trivial Lie module is a subsingleton. -/
@[source_ref "Chapter2/Example2.9.8" (role := primary)]
theorem punitTrivialModule_subsingleton :
    Subsingleton (TrivialLieModule k L PUnit) := inferInstanceAs (Subsingleton PUnit)

variable (V : Type*) [AddCommGroup V] [Module k V]

/-- A property of the trivial Lie module. -/
@[source_ref "Chapter2/Example2.9.8" (role := primary)]
theorem trivialModuleProperty :
    LieModule.AuxiliaryPredicate k L (TrivialLieModule k L V) := inferInstance

omit [CommRing k] [LieAlgebra k L] [Module k V] in
/-- The action bracket on a trivial Lie module is zero. -/
@[source_ref "Chapter2/Example2.9.8" (role := primary)]
theorem trivialModule_bracket_eq_zero
    (a : L) (v : TrivialLieModule k L V) : ⁅a, v⁆ = 0 := rfl

/-- A property associated with a Lie algebra used as both displayed type parameters. -/
@[source_ref "Chapter2/Example2.9.8" (role := supporting)]
theorem selfProperty : LieModule.AuxiliaryPredicate k L L := inferInstance

/-- The Lie homomorphism from a Lie algebra to its linear endomorphisms induced by the bracket. -/
@[source_ref "Chapter2/Example2.9.8" (role := supporting)]
noncomputable def adjointRepresentation : L →ₗ⁅k⁆ Module.End k L :=
  LieAlgebra.ad k L

/-- The adjoint representation evaluated on two elements is their bracket. -/
@[source_ref "Chapter2/Example2.9.8" (role := primary)]
theorem adjointRepresentation_apply (a b : L) :
    LieAlgebra.ad k L a b = ⁅a, b⁆ := LieAlgebra.ad_apply k L a b

/-- The adjoint map preserves brackets. -/
@[source_ref "Chapter2/Example2.9.8" (role := primary)]
theorem adjointRepresentation_bracket (a b : L) :
    LieAlgebra.ad k L ⁅a, b⁆ = ⁅LieAlgebra.ad k L a, LieAlgebra.ad k L b⁆ :=
  LieHom.map_lie (LieAlgebra.ad k L) a b

end RepresentationTheory.Algebra.Lie.Module.Examples
