/-
Copyright (c) 2026 mathlib-initiative. All rights reserved.
Released under Apache 2.0 license as described in the file LICENCE.
Authors: Kim Morrison
-/
import Mathlib.Algebra.Lie.Basic
import Mathlib.LinearAlgebra.Dual.Defs
import RepresentationTheory.Alignment.Attribute

/-!
# Duals of Lie modules

The dual-module type and its contragredient Lie action.
-/

set_option linter.style.whitespace false

namespace RepresentationTheory.Algebra.Lie.Dual

/-- The dual-module type for a module of a Lie algebra over a commutative ring. -/
@[nolint unusedArguments, source_ref "Chapter2/Definition2.14.2" (role := supporting)]
abbrev LieModuleDual (k : Type*) (L : Type*) (V : Type*)
    [CommRing k] [LieRing L] [LieAlgebra k L]
    [AddCommGroup V] [Module k V] [LieRingModule L V] [LieModule k L V] :=
  Module.Dual k V

variable {k L V : Type*}
    [CommRing k] [LieRing L] [LieAlgebra k L]
    [AddCommGroup V] [Module k V] [LieRingModule L V] [LieModule k L V]

/-- Evaluating the Lie action on a dual element at a vector gives the negated evaluation on the
Lie action of that vector. -/
@[simp, source_ref "Chapter2/Definition2.14.2" (role := primary)]
theorem lie_bracket_dual_apply (x : L) (f : LieModuleDual k L V) (v : V) :
    (⁅x, f⁆ : LieModuleDual k L V) v = -f ⁅x, v⁆ :=
  Module.Dual.lie_apply x v f

end RepresentationTheory.Algebra.Lie.Dual
