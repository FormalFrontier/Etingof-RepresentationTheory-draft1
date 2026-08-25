/-
Copyright (c) 2026 mathlib-initiative. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
import Mathlib.Algebra.Algebra.Basic
import RepresentationTheory.Alignment.Attribute

/-!
# Non-unital algebra structures

Associative bilinear multiplication on a vector space, without a distinguished identity element.
-/

set_option linter.style.whitespace false

namespace RepresentationTheory.Algebra.AuxiliaryStructure

/-- An auxiliary structure associated with a field and one of its modules. -/
@[source_ref "Chapter2/Definition2.2.1" (role := supporting),
  source_ref "Chapter2/Discussion_2.1_overview/Derived2" (role := supporting)]
class AuxiliaryStructure (k A : Type*) [Field k] [AddCommGroup A] [Module k A] where
  /-- The binary operation supplied by the auxiliary structure. -/
  op : A → A → A
  /-- The associated binary operation is associative. -/
  op_assoc : ∀ a b c : A, op (op a b) c = op a (op b c)
  /-- The associated binary operation is additive in its first argument. -/
  op_add_left : ∀ a b c : A, op (a + b) c = op a c + op b c
  /-- The associated binary operation is additive in its second argument. -/
  op_add_right : ∀ a b c : A, op a (b + c) = op a b + op a c
  /-- The associated binary operation commutes with scalar multiplication in its first argument. -/
  smul_op_left : ∀ (r : k) (a b : A), op (r • a) b = r • op a b
  /-- The associated binary operation commutes with scalar multiplication in its second argument. -/
  op_smul_right : ∀ (r : k) (a b : A), op a (r • b) = r • op a b

namespace AuxiliaryStructure

/-- Constructs the auxiliary structure from a ring that is an algebra over the field. -/
instance of_algebra (k A : Type*) [Field k] [Ring A] [Algebra k A] :
    AuxiliaryStructure k A where
  op := ( · * · )
  op_assoc := _root_.mul_assoc
  op_add_left := _root_.add_mul
  op_add_right := _root_.mul_add
  smul_op_left r a b := smul_mul_assoc r a b
  op_smul_right r a b := mul_smul_comm r a b

end AuxiliaryStructure
end RepresentationTheory.Algebra.AuxiliaryStructure
