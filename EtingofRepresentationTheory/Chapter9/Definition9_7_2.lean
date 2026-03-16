import Mathlib.RingTheory.Jacobson.Radical
import Mathlib.RingTheory.Artinian.Ring

/-!
# Definition 9.7.2: Basic algebra

A finite dimensional algebra B is called **basic** if B/Rad(B) is a commutative algebra
(i.e., a direct sum of copies of the ground field k).

Equivalently, B is basic if and only if all simple B-modules are one-dimensional.

## Mathlib correspondence

Not directly in Mathlib. Uses the Jacobson radical `Ideal.jacobson` and commutativity
of the quotient.
-/

/-- A basic algebra in the sense of Etingof Definition 9.7.2.
A finite dimensional algebra whose quotient by the Jacobson radical is commutative. -/
def Etingof.BasicAlgebra : (sorry : Prop) := sorry
