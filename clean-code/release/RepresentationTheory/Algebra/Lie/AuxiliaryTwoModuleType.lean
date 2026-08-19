/-
Copyright (c) 2026 mathlib-initiative. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
import Mathlib.Algebra.Lie.TensorProduct
import RepresentationTheory.Alignment.Attribute

/-!
# Tensor products of Lie modules

Types and action formulas for tensor products of modules over a Lie algebra.
-/

set_option linter.style.whitespace false

open scoped TensorProduct

namespace RepresentationTheory.Algebra.Lie.AuxiliaryTwoModuleType

/-- An auxiliary type depending on a Lie algebra and two of its modules. -/
@[nolint unusedArguments, source_ref "Chapter2/Definition2.14.1" (role := supporting)]
abbrev AuxiliaryLieModuleType (k : Type*) (L : Type*) (V : Type*) (W : Type*)
    [CommRing k] [LieRing L] [LieAlgebra k L]
    [AddCommGroup V] [Module k V] [LieRingModule L V] [LieModule k L V]
    [AddCommGroup W] [Module k W] [LieRingModule L W] [LieModule k L W] :=
  TensorProduct k V W

variable {k L V W : Type*}
    [CommRing k] [LieRing L] [LieAlgebra k L]
    [AddCommGroup V] [Module k V] [LieRingModule L V] [LieModule k L V]
    [AddCommGroup W] [Module k W] [LieRingModule L W] [LieModule k L W]

/-- The Lie action on a pure tensor is the sum of the actions on its two factors. -/
@[source_ref "Chapter2/Definition2.14.1" (role := primary)]
theorem AuxiliaryLieModuleType.lie_bracket_tmul (x : L) (v : V) (w : W) :
    ⁅x, (v ⊗ₜ[k] w : AuxiliaryLieModuleType k L V W)⁆ =
      ⁅x, v⁆ ⊗ₜ[k] w + v ⊗ₜ[k] ⁅x, w⁆ :=
  TensorProduct.LieModule.lie_tmul_right x v w

end RepresentationTheory.Algebra.Lie.AuxiliaryTwoModuleType
