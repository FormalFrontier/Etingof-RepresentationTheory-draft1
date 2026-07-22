import Mathlib
import EtingofRepresentationTheory.Chapter4.Example4_3_Q8

/-!
# Exercise 4.3.1: the 2-dimensional irreducible representation of `Q₈` on a function space

**Exercise 4.3.1.** Show that the 2-dimensional irreducible representation of `Q₈` can be
realized in the space of functions `f : Q₈ → ℂ` such that `f(g·i) = √(-1)·f(g)` (the action
of `G` is by right multiplication, `g ∘ f(x) = f(x·g)`).

## Formalization

We model `Q₈` by Mathlib's `QuaternionGroup 2` (order `8`), with the element `i` taken to be
`QuaternionGroup.a 1` (an element of order `4`, matching the matrix `rhoI` in
`Example4_3_Q8`), and `√(-1)` by `Complex.I`.

The action of `Q₈` on functions `Q₈ → ℂ` by right translation, `(g ∘ f)(x) = f(x·g)`, is the
**right regular representation** `rightRegular`. The book writes the covariance condition as
`f(g·i) = √(-1)·f(g)`; the subspace invariant under the *right*-translation action is the one
cut out by the *left* covariance `f(i·g) = √(-1)·f(g)` (the two are the standard equivalent
conventions for the induced representation `Ind_{⟨i⟩}^{Q₈} χ`, where `χ(i) = √(-1)`). We call
this invariant subspace `covariantSubspace`.

This is a statement pass. We give faithful signatures with `sorry` proofs for:
* `covariantSubspace_invariant` — the subspace is a subrepresentation of the right regular
  representation;
* `covariantSubspace_finrank` — it is `2`-dimensional;
* `covariantSubspace_irreducible` — it is irreducible (every invariant subspace of it is `⊥`
  or the whole space).

The identification with the concrete 2-dimensional irreducible `Example4_3_Q8.repLin` is
recorded in the docstring and left for a later pass.
-/

open QuaternionGroup

namespace Etingof.Exercise4_3_1

/-- The right regular representation of `Q₈ = QuaternionGroup 2` on functions `Q₈ → ℂ`:
`(rightRegular g) f = fun x => f (x * g)`. This is the action `g ∘ f(x) = f(x·g)` from the
book. -/
noncomputable def rightRegular :
    Representation ℂ (QuaternionGroup 2) (QuaternionGroup 2 → ℂ) where
  toFun g := LinearMap.funLeft ℂ ℂ (· * g)
  map_one' := by
    ext f x
    simp
  map_mul' g h := by
    ext f x
    simp [LinearMap.funLeft_apply, mul_assoc]

@[simp]
theorem rightRegular_apply (g : QuaternionGroup 2) (f : QuaternionGroup 2 → ℂ)
    (x : QuaternionGroup 2) : rightRegular g f x = f (x * g) := rfl

/-- The subspace of functions `f : Q₈ → ℂ` satisfying the covariance condition
`f(i·g) = √(-1)·f(g)` for all `g`, where `i = a 1` and `√(-1) = Complex.I`. This is the space
in which the 2-dimensional irreducible representation of `Q₈` is realized. -/
def covariantSubspace : Submodule ℂ (QuaternionGroup 2 → ℂ) where
  carrier := {f | ∀ g : QuaternionGroup 2, f (a 1 * g) = Complex.I * f g}
  add_mem' {f₁ f₂} hf₁ hf₂ := by
    intro g
    simp only [Pi.add_apply, hf₁ g, hf₂ g]
    ring
  zero_mem' := by
    intro g
    simp
  smul_mem' c f hf := by
    intro g
    simp only [Pi.smul_apply, smul_eq_mul, hf g]
    ring

@[simp]
theorem mem_covariantSubspace {f : QuaternionGroup 2 → ℂ} :
    f ∈ covariantSubspace ↔ ∀ g : QuaternionGroup 2, f (a 1 * g) = Complex.I * f g :=
  Iff.rfl

/-- `covariantSubspace` is a subrepresentation of the right regular representation: it is
invariant under `rightRegular g` for every `g`. -/
theorem covariantSubspace_invariant (g : QuaternionGroup 2)
    (f : QuaternionGroup 2 → ℂ) (hf : f ∈ covariantSubspace) :
    rightRegular g f ∈ covariantSubspace := by
  sorry

/-- The space `covariantSubspace` is `2`-dimensional. -/
theorem covariantSubspace_finrank :
    Module.finrank ℂ covariantSubspace = 2 := by
  sorry

/-- The realized representation is irreducible: every `Q₈`-invariant subspace `U` contained in
`covariantSubspace` is either `⊥` or all of `covariantSubspace`. -/
theorem covariantSubspace_irreducible
    (U : Submodule ℂ (QuaternionGroup 2 → ℂ))
    (hUle : U ≤ covariantSubspace)
    (hUinv : ∀ g : QuaternionGroup 2, ∀ f ∈ U, rightRegular g f ∈ U) :
    U = ⊥ ∨ U = covariantSubspace := by
  sorry

end Etingof.Exercise4_3_1
