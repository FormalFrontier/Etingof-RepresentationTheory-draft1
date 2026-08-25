/-
Copyright (c) 2026 mathlib-initiative. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

import Mathlib.LinearAlgebra.Dual.Defs
import Mathlib.Algebra.Algebra.Defs
import RepresentationTheory.Alignment.Attribute

/-! # Dual action on a linear dual -/

namespace RepresentationTheory.Module.DualOppositeAction

section DualRepresentation

variable (k A V : Type*)
    [CommRing k] [Ring A] [Algebra k A]
    [AddCommGroup V] [Module k V] [Module A V] [SMulCommClass A k V]

/-- An auxiliary type-valued construction depending on a commutative ring, another type, and a
module over the ring. -/
@[source_ref "Chapter3/Definition3.3.2" (role := supporting)]
abbrev AuxiliaryModuleType (k _A V : Type*)
    [CommRing k] [AddCommGroup V] [Module k V] : Type _ :=
  Module.Dual k V

/-- The scalar action of the opposite ring on the linear dual induced by precomposition with the
action on the original module. -/
@[source_ref "Chapter3/Definition3.3.2" (role := supporting)]
instance dualMulOppositeSMul : SMul Aᵐᵒᵖ (Module.Dual k V) where
  smul a f := f.comp (DistribSMul.toLinearMap k V a.unop)

variable {k A V}

omit [Algebra k A] in
/-- The action of an element of the opposite ring on a linear dual evaluates by applying the
functional after the corresponding action on the vector. -/
@[simp, source_ref "Chapter3/Definition3.3.2" (role := primary)]
theorem dualMulOpposite_smul_apply (a : Aᵐᵒᵖ) (f : Module.Dual k V) (v : V) :
    (a • f) v = f (a.unop • v) :=
  rfl

variable (k A V)

/-- The module structure of the linear dual over the opposite ring induced by a compatible action
on the original module. -/
@[source_ref "Chapter3/Definition3.3.2" (role := primary)]
instance dualMulOppositeModule : Module Aᵐᵒᵖ (Module.Dual k V) where
  one_smul f := by ext v; simp
  mul_smul a b f := by ext v; simp [mul_smul]
  smul_zero a := by ext v; simp
  smul_add a f g := by ext v; simp
  add_smul a b f := by ext v; simp [add_smul]
  zero_smul f := by ext v; simp

example : Module Aᵐᵒᵖ (AuxiliaryModuleType k A V) := inferInstance

end DualRepresentation

end RepresentationTheory.Module.DualOppositeAction

attribute [nolint unusedArguments]
  RepresentationTheory.Module.DualOppositeAction.AuxiliaryModuleType
