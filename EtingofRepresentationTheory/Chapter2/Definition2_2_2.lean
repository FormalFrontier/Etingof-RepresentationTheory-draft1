import Mathlib.Algebra.Algebra.Basic

/-!
# Definition 2.2.2: Unit in an Associative Algebra

A **unit** in an associative algebra A is an element 1 ∈ A such that 1a = a1 = a.

## Mathlib correspondence

Mathlib algebras are unital by default — `Ring A` includes `One A` and the unit laws.
The unit element is `(1 : A)`, and its defining property is captured by the two-sided
identity laws `one_mul` and `mul_one`.
-/

namespace EtingofRepresentationTheory.Chapter2

/-- **Definition 2.2.2.** The element `(1 : A)` is a *unit* in the associative algebra `A`:
it satisfies the two-sided identity property `1 * a = a` and `a * 1 = a` for every `a ∈ A`.
This is the defining content of Etingof Definition 2.2.2; in Mathlib it is provided by
`Ring A` (more precisely by `MulOneClass A`) through `one_mul` and `mul_one`. -/
theorem one_isUnit (A : Type*) [Ring A] (a : A) : 1 * a = a ∧ a * 1 = a :=
  ⟨one_mul a, mul_one a⟩

end EtingofRepresentationTheory.Chapter2
