/-
Copyright (c) 2026 mathlib-initiative. All rights reserved.
Released under Apache 2.0 license as described in the file LICENCE.
Authors: Kim Morrison
-/
import Mathlib.LinearAlgebra.TensorProduct.Basic
import RepresentationTheory.Alignment.Attribute

/-!
# Tensor products of modules

Basic names for tensor products of modules over commutative rings.
-/

set_option linter.style.whitespace false

open scoped TensorProduct

namespace RepresentationTheory.Algebra.Module.TensorProduct

/-- The tensor-product type associated to two modules over a commutative ring. -/
@[source_ref "Chapter2/Definition2.11.1" (role := primary)]
abbrev ModuleTensorProduct (k : Type*) (V W : Type*) [CommRing k]
    [AddCommGroup V] [AddCommGroup W] [Module k V] [Module k W] :=
  V ⊗[k] W

end RepresentationTheory.Algebra.Module.TensorProduct
