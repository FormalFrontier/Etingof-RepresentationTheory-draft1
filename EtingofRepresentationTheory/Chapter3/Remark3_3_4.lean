import Mathlib.LinearAlgebra.Basis.Defs
import Mathlib.LinearAlgebra.Quotient.Basic
import Mathlib.LinearAlgebra.FiniteDimensional.Defs
import Mathlib.Algebra.Algebra.Tower

/-!
# Remark 3.3.4: A finite dimensional representation is a quotient of a free module

Let `X` be an `n`-dimensional representation of `A`, with a `k`-basis `{x₁, …, xₙ}`. Then
there is a unique `A`-module homomorphism `ψ : Aⁿ → X` with `ψ(a₁, …, aₙ) = ∑ᵢ aᵢ xᵢ`, and
it is surjective. Hence `X` is a quotient of the free module `Aⁿ`.

We model the free module `Aⁿ` as `ι → A` for a `Fintype` index `ι` (a basis of `X`). The
map `ψ` is `A`-linear and surjective: any element of `X` is a `k`-linear combination of the
basis, and `k` acts through `A` via the scalar tower, so the same element is the image of
the corresponding tuple of scalars from `A`.
-/

open Module

namespace Etingof

variable {k : Type*} (A : Type*) {X : Type*}
  [CommRing k] [Ring A] [Algebra k A]
  [AddCommGroup X] [Module k X] [Module A X] [IsScalarTower k A X]
  {ι : Type*} [Fintype ι]

/-- The `A`-linear map `ψ : Aⁿ → X` from a `k`-basis `b` of `X`, sending the tuple
`(aᵢ)` to `∑ᵢ aᵢ • bᵢ`. The free module `Aⁿ` is realized as `ι → A`. -/
noncomputable def freeCover (b : Basis ι k X) : (ι → A) →ₗ[A] X where
  toFun a := ∑ i, (a i • b i : X)
  map_add' a a' := by
    simp only [Pi.add_apply, add_smul, Finset.sum_add_distrib]
  map_smul' c a := by
    simp only [Pi.smul_apply, smul_eq_mul, mul_smul, RingHom.id_apply, Finset.smul_sum]

@[simp]
theorem freeCover_apply (b : Basis ι k X) (a : ι → A) :
    freeCover A b a = ∑ i, (a i • b i : X) := rfl

/-- The map `ψ : Aⁿ → X` is surjective. Etingof Remark 3.3.4. -/
theorem freeCover_surjective (b : Basis ι k X) :
    Function.Surjective (freeCover A b) := by
  intro x
  -- Use the basis coordinates of `x`, mapped into `A` via the algebra map.
  refine ⟨fun i => algebraMap k A (b.repr x i), ?_⟩
  rw [freeCover_apply]
  rw [show (∑ i, (algebraMap k A (b.repr x i) • b i : X)) = ∑ i, ((b.repr x i) • b i : X) from
    Finset.sum_congr rfl fun i _ => algebraMap_smul A (b.repr x i) (b i)]
  exact b.sum_repr x

/-- `X` is a quotient of the free module `Aⁿ`: the quotient of `Aⁿ` by the kernel of `ψ`
is `A`-linearly isomorphic to `X`. -/
noncomputable def quotientEquivOfFreeCover (b : Basis ι k X) :
    ((ι → A) ⧸ LinearMap.ker (freeCover A b)) ≃ₗ[A] X :=
  (freeCover A b).quotKerEquivOfSurjective (freeCover_surjective A b)

end Etingof
