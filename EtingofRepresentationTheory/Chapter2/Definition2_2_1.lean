import Mathlib.Algebra.Algebra.Basic

/-!
# Definition 2.2.1: Associative Algebra

An **associative algebra** over `k` is a vector space `A` over `k` together with a bilinear map
`A × A → A`, `(a, b) ↦ ab`, such that `(ab)c = a(bc)`.

## Faithfulness note

The book's Definition 2.2.1 is **non-unital**: it asks only for a `k`-vector space with an
associative bilinear multiplication. The multiplicative unit is *not* part of this definition —
it is introduced separately in Definition 2.2.2. We therefore encode the definition directly as a
mixin class carrying the bilinear associative multiplication on a `k`-vector space, rather than
aliasing Mathlib's `Algebra k A` (which is unital, i.e. strictly stronger than the book asks).

Every unital algebra is in particular such an algebra: the instance
`Algebra k A → Etingof.AssociativeAlgebra k A` below witnesses that `Algebra k A` is a special
case, so all unital examples still fit.
-/

/-- **Definition 2.2.1** (Etingof). A (non-unital) associative algebra over a field `k` is a
`k`-vector space `A` equipped with a bilinear multiplication `A × A → A`, `(a, b) ↦ mul a b`,
that is associative. The unit is deliberately omitted (see Definition 2.2.2). -/
class Etingof.AssociativeAlgebra (k A : Type*) [Field k] [AddCommGroup A] [Module k A] where
  /-- The multiplication `A × A → A`, `(a, b) ↦ ab`. -/
  mul : A → A → A
  /-- Associativity: `(ab)c = a(bc)`. -/
  mul_assoc' : ∀ a b c : A, mul (mul a b) c = mul a (mul b c)
  /-- Additivity in the left argument (one half of bilinearity). -/
  add_mul' : ∀ a b c : A, mul (a + b) c = mul a c + mul b c
  /-- Additivity in the right argument (other half of bilinearity). -/
  mul_add' : ∀ a b c : A, mul a (b + c) = mul a b + mul a c
  /-- Scalar compatibility on the left: `(r • a)b = r • (ab)`. -/
  smul_mul' : ∀ (r : k) (a b : A), mul (r • a) b = r • mul a b
  /-- Scalar compatibility on the right: `a(r • b) = r • (ab)`. -/
  mul_smul' : ∀ (r : k) (a b : A), mul a (r • b) = r • mul a b

namespace Etingof.AssociativeAlgebra

/-- Every unital `k`-algebra (in the Mathlib sense) is in particular an associative algebra in the
sense of Definition 2.2.1: take the ring multiplication, which is associative and bilinear. This
shows the book's (non-unital) notion is a faithful generalization of Mathlib's unital one. -/
instance (k A : Type*) [Field k] [Ring A] [Algebra k A] : Etingof.AssociativeAlgebra k A where
  mul := (· * ·)
  mul_assoc' := mul_assoc
  add_mul' := add_mul
  mul_add' := mul_add
  smul_mul' r a b := smul_mul_assoc r a b
  mul_smul' r a b := mul_smul_comm r a b

end Etingof.AssociativeAlgebra
