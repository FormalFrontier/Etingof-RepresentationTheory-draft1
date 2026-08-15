/-
Copyright (c) 2026 mathlib-initiative. All rights reserved.
Released under Apache 2.0 license as described in the file LICENCE.
Authors: Kim Morrison
-/

import Mathlib.Algebra.FreeAlgebra
import RepresentationTheory.Alignment.Attribute

/-! # Module structures associated to rings -/

namespace RepresentationTheory.Algebra.Ring.ModuleStructures

/-- The canonical module structure on the singleton additive type. -/
@[source_ref "Chapter2/Example2.3.3" (role := primary)]
abbrev punitModule (A : Type*) [Ring A] : Module A PUnit :=
  inferInstance

/-- The canonical module structure of a ring over itself. -/
@[source_ref "Chapter2/Example2.3.3" (role := primary)]
abbrev selfModule (A : Type*) [Ring A] : Module A A :=
  inferInstance

/-- The module structure in which an opposite-ring scalar acts by right multiplication. -/
@[source_ref "Chapter2/Example2.3.3" (role := supporting)]
abbrev oppositeSelfModule (A : Type*) [Ring A] : Module Aᵐᵒᵖ A :=
  inferInstance

/-- Scalar multiplication by an opposite-ring element is multiplication in reverse order. -/
@[source_ref "Chapter2/Example2.3.3" (role := primary)]
theorem op_smul_eq_mul (A : Type*) [Ring A] (a b : A) :
    MulOpposite.op a • b = b * a :=
  rfl

example (k : Type*) [Field k] (V : Type*) [AddCommGroup V] [Module k V] :
    Module k V := inferInstance

example (k : Type*) [CommRing k] (V : Type*) [AddCommGroup V] [Module k V] (n : ℕ) :
    (Fin n → Module.End k V) ≃ (FreeAlgebra k (Fin n) →ₐ[k] Module.End k V) :=
  FreeAlgebra.lift k

example (k : Type*) [CommRing k] (V : Type*) [AddCommGroup V] [Module k V] (n : ℕ)
    (ρ : FreeAlgebra k (Fin n) →ₐ[k] Module.End k V) (i : Fin n) :
    (FreeAlgebra.lift k).symm ρ i = ρ (FreeAlgebra.ι k i) :=
  congrFun (FreeAlgebra.lift_symm_apply k ρ) i

example (k : Type*) [CommRing k] (V : Type*) [AddCommGroup V] [Module k V] (n : ℕ)
    (f : Fin n → Module.End k V) (i : Fin n) :
    FreeAlgebra.lift k f (FreeAlgebra.ι k i) = f i :=
  FreeAlgebra.lift_ι_apply f i

end RepresentationTheory.Algebra.Ring.ModuleStructures
