import Mathlib.LinearAlgebra.TensorProduct.Basic

/-!
# Exercise 2.11.7: Tensor product of modules over a commutative ring

> **Exercise 2.11.7.** Show that if `M` and `N` are modules over a commutative ring
> `A`, then `M ⊗_A N` has a natural structure of an `A`-module.

## Mathlib correspondence

Exact match. For a commutative (semi)ring `A` and `A`-modules `M`, `N`, Mathlib's
`TensorProduct A M N` carries a canonical `Module A` structure
(`TensorProduct.instModule`), with scalar multiplication acting on either factor:
`a • (m ⊗ₜ n) = (a • m) ⊗ₜ n = m ⊗ₜ (a • n)`.
-/

namespace Etingof.Exercise2_11_7

open scoped TensorProduct

/-- **Exercise 2.11.7.** For a commutative ring `A` and `A`-modules `M` and `N`, the tensor
product `M ⊗_A N` is naturally an `A`-module. -/
example (A : Type*) [CommRing A]
    (M N : Type*) [AddCommGroup M] [Module A M] [AddCommGroup N] [Module A N] :
    Module A (M ⊗[A] N) := inferInstance

/-- The `A`-action on `M ⊗_A N` is the natural one: `a • (m ⊗ₜ n) = (a • m) ⊗ₜ n`. -/
example (A : Type*) [CommRing A]
    (M N : Type*) [AddCommGroup M] [Module A M] [AddCommGroup N] [Module A N]
    (a : A) (m : M) (n : N) :
    a • (m ⊗ₜ[A] n) = (a • m) ⊗ₜ[A] n :=
  TensorProduct.smul_tmul' a m n

/-- Because `A` is commutative, the action may equivalently be taken on the second factor:
`a • (m ⊗ₜ n) = m ⊗ₜ (a • n)`. -/
example (A : Type*) [CommRing A]
    (M N : Type*) [AddCommGroup M] [Module A M] [AddCommGroup N] [Module A N]
    (a : A) (m : M) (n : N) :
    a • (m ⊗ₜ[A] n) = m ⊗ₜ[A] (a • n) :=
  TensorProduct.tmul_smul a m n |>.symm

end Etingof.Exercise2_11_7
