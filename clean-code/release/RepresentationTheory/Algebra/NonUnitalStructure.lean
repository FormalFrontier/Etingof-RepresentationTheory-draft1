/-
Copyright (c) 2026 mathlib-initiative. All rights reserved.
Released under Apache 2.0 license as described in the file LICENCE.
Authors: Kim Morrison
-/
import Mathlib.Algebra.Algebra.Basic
import RepresentationTheory.Alignment.Attribute

/-!
# Non-unital algebra structures

Associative bilinear multiplication on a vector space, without a distinguished identity element.
-/

set_option linter.style.whitespace false

namespace RepresentationTheory.Algebra.NonUnitalStructure

/-- Associative bilinear multiplication data on a vector space over a field. -/
@[source_ref "Chapter2/Definition2.2.1" (role := supporting),
  source_ref "Chapter2/Discussion_2.1_overview/Derived2" (role := supporting)]
class NonUnitalAlgebraStructure (k A : Type*) [Field k] [AddCommGroup A] [Module k A] where
  /-- The multiplication supplied by an associative bilinear multiplication structure. -/
  mul : A → A → A
  /-- The multiplication supplied by the structure is associative. -/
  mul_assoc : ∀ a b c : A, mul (mul a b) c = mul a (mul b c)
  /-- Multiplication is additive in its first argument. -/
  add_mul : ∀ a b c : A, mul (a + b) c = mul a c + mul b c
  /-- Multiplication is additive in its second argument. -/
  mul_add : ∀ a b c : A, mul a (b + c) = mul a b + mul a c
  /-- Multiplication commutes with scalar multiplication in its first argument. -/
  smul_mul : ∀ (r : k) (a b : A), mul (r • a) b = r • mul a b
  /-- Multiplication commutes with scalar multiplication in its second argument. -/
  mul_smul : ∀ (r : k) (a b : A), mul a (r • b) = r • mul a b

namespace NonUnitalAlgebraStructure

/-- Constructs associative bilinear multiplication data from an algebra over a field. -/
instance nonUnitalAlgebraStructureOfAlgebra (k A : Type*) [Field k] [Ring A] [Algebra k A] :
    NonUnitalAlgebraStructure k A where
  mul := ( · * · )
  mul_assoc := _root_.mul_assoc
  add_mul := _root_.add_mul
  mul_add := _root_.mul_add
  smul_mul r a b := smul_mul_assoc r a b
  mul_smul r a b := mul_smul_comm r a b

end NonUnitalAlgebraStructure
end RepresentationTheory.Algebra.NonUnitalStructure
