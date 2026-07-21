import Mathlib

/-!
# Exercise 2.9.11: Lie algebra representations vs. enveloping algebra representations

The exercise asks to explain why a representation of a Lie algebra `𝔤` is the same thing as a
representation of its universal enveloping algebra `U(𝔤)`.

## Formalization

A representation of `𝔤` on `V` is a Lie algebra homomorphism `𝔤 →ₗ⁅k⁆ End_k(V)` (Definition
2.9.7), where the associative algebra `End_k(V)` is viewed as a Lie algebra via its commutator. A
representation of `U(𝔤)` on `V` is an associative algebra homomorphism `U(𝔤) →ₐ[k] End_k(V)`.

The universal property of the universal enveloping algebra (Mathlib's
`UniversalEnvelopingAlgebra.lift`) gives a natural bijection between these two sets, which is
exactly the content of the exercise.
-/

namespace Etingof.Exercise2_9_11

attribute [local instance 100] LieRing.ofAssociativeRing

variable (k : Type*) [Field k]
variable (L : Type*) [LieRing L] [LieAlgebra k L]
variable (V : Type*) [AddCommGroup V] [Module k V]

/-- **Exercise 2.9.11.** A representation of the Lie algebra `L` on `V` (a Lie homomorphism
`L →ₗ⁅k⁆ End_k(V)`) is the same thing as a representation of its universal enveloping algebra
(an algebra homomorphism `U(L) →ₐ[k] End_k(V)`). The bijection is the universal property of
`U(L)`. -/
noncomputable def repEquiv :
    (L →ₗ⁅k⁆ Module.End k V) ≃ (UniversalEnvelopingAlgebra k L →ₐ[k] Module.End k V) :=
  UniversalEnvelopingAlgebra.lift k

end Etingof.Exercise2_9_11
