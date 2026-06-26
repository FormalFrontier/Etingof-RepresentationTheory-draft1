import Mathlib.Algebra.Module.Basic
import Mathlib.Algebra.FreeAlgebra
import Mathlib.Algebra.Algebra.Bilinear

/-!
# Example 2.3.3: Examples of Representations

1. V = 0 (the zero representation).
2. V = A with ρ(a) = left multiplication by a (the regular representation).
3. A = k: a representation of k is simply a vector space over k.
4. A = k⟨x₁, …, xₙ⟩: a representation is a vector space with n arbitrary linear operators.

## Mathlib correspondence

Exact match. The regular representation is the canonical `Module A A` instance.
-/

/-- The zero module is a representation of any algebra. (Etingof Example 2.3.3(1)) -/
example (A : Type*) [Ring A] : Module A PUnit := inferInstance

/-- The regular representation: A is a left module over itself. (Etingof Example 2.3.3(2)) -/
example (A : Type*) [Ring A] : Module A A := inferInstance

/-- A representation of k is simply a vector space over k. (Etingof Example 2.3.3(3)) -/
example (k : Type*) [Field k] (V : Type*) [AddCommGroup V] [Module k V] :
    Module k V := inferInstance

/-- A representation of an algebra `A` on `V` is precisely an algebra homomorphism
`A →ₐ[k] Module.End k V`.

For the free algebra `A = k⟨x₁, …, xₙ⟩`, the universal property says such a homomorphism
is determined by, and freely choosable as, an arbitrary `n`-tuple of linear operators
`(ρ(x₁), …, ρ(xₙ)) : Fin n → Module.End k V`. The bijection `ρ ↔ (ρ(xᵢ))ᵢ` is exactly
`FreeAlgebra.lift`. (Etingof Example 2.3.3(4)) -/
example (k : Type*) [CommRing k] (V : Type*) [AddCommGroup V] [Module k V] (n : ℕ) :
    (Fin n → Module.End k V) ≃ (FreeAlgebra k (Fin n) →ₐ[k] Module.End k V) :=
  FreeAlgebra.lift k

/-- Unfolding the bijection in one direction: the operators recovered from a representation
`ρ` are its values `ρ(xᵢ)` on the generators `xᵢ = FreeAlgebra.ι k i`. -/
example (k : Type*) [CommRing k] (V : Type*) [AddCommGroup V] [Module k V] (n : ℕ)
    (ρ : FreeAlgebra k (Fin n) →ₐ[k] Module.End k V) (i : Fin n) :
    (FreeAlgebra.lift k).symm ρ i = ρ (FreeAlgebra.ι k i) :=
  congrFun (FreeAlgebra.lift_symm_apply k ρ) i

/-- Unfolding the bijection in the other direction: from any tuple of operators `f`,
the resulting representation sends the generator `xᵢ` to `f i`. -/
example (k : Type*) [CommRing k] (V : Type*) [AddCommGroup V] [Module k V] (n : ℕ)
    (f : Fin n → Module.End k V) (i : Fin n) :
    FreeAlgebra.lift k f (FreeAlgebra.ι k i) = f i :=
  FreeAlgebra.lift_ι_apply f i
