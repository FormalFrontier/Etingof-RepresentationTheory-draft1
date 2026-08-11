import Mathlib.RingTheory.Jacobson.Radical
import Mathlib.RingTheory.Ideal.Quotient.Defs
import Mathlib.RingTheory.Artinian.Ring
import Mathlib.RingTheory.SimpleModule.Basic
import Mathlib.LinearAlgebra.Dimension.Finrank

/-!
# Definition 9.7.2: Basic algebra

A finite dimensional algebra `B` is called **basic** if `B/Rad(B)` is a commutative
algebra.

This file gives the faithful formalization of the book's literal condition as
`Etingof.IsBasicAlgebra`, together with the stronger "splitting" condition
`Etingof.IsBasicAlgebraSplit` (every simple module is one-dimensional) that the
project uses over algebraically closed fields.

## Why two predicates

The book's condition is `B/Rad(B)` commutative. Over a field `k`, the semisimple
quotient `B/Rad(B)` decomposes (Wedderburn–Artin) as a product `∏ᵢ Mat_{nᵢ}(Dᵢ)`
for division algebras `Dᵢ`; it is commutative exactly when every `nᵢ = 1` and every
`Dᵢ` is a field. The condition "every simple module is one-dimensional over `k`" is
*strictly stronger*: it forces `B/Rad(B) ≅ ∏ k` (each `nᵢ = 1` **and** each `Dᵢ = k`).
The two coincide precisely over an algebraically closed field, where every finite
division algebra is `k` itself.

`IsBasicAlgebra` (this file's `Etingof.IsBasicAlgebra`) asserts the book's literal
condition. `IsBasicAlgebraSplit` captures the algebraically-closed reading and is the
hypothesis used throughout the Morita-theoretic development in
`Chapter9/MoritaStructural.lean` and `Infrastructure/BasicAlgebraExistence.lean`,
where the standing assumption is `IsAlgClosed k` (so the two agree).
-/

/-- A basic algebra in the sense of Etingof Definition 9.7.2: a `k`-algebra `A`
whose quotient `A / Rad(A)` by the Jacobson radical is commutative. -/
def Etingof.IsBasicAlgebra (k : Type*) [Field k]
    (A : Type*) [Ring A] [Algebra k A] : Prop :=
  ∀ x y : A ⧸ Ring.jacobson A, x * y = y * x

/-- The "split" basic condition: every simple `A`-module is one-dimensional over `k`.
Over an algebraically closed field this is equivalent to `IsBasicAlgebra` (the book's
`A / Rad(A)` commutative condition); in general it is strictly stronger. -/
def Etingof.IsBasicAlgebraSplit (k : Type*) [Field k]
    (A : Type*) [Ring A] [Algebra k A] : Prop :=
  ∀ (M : Type*) [AddCommGroup M] [Module A M] [IsSimpleModule A M] [Module k M]
    [IsScalarTower k A M], Module.finrank k M = 1

/-- Any commutative `k`-algebra is basic: its radical quotient is again commutative,
so the defining condition holds trivially.  In particular a field is basic over
itself (Definition 9.7.2). -/
theorem Etingof.IsBasicAlgebra.of_commutative (k : Type*) [Field k]
    (A : Type*) [CommRing A] [Algebra k A] : Etingof.IsBasicAlgebra k A :=
  fun x y => mul_comm x y
