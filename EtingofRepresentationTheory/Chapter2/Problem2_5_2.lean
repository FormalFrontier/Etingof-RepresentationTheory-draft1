import Mathlib
import EtingofRepresentationTheory.Chapter2.Definition2_3_8

/-!
# Problem 2.5.2: Cyclic vectors and cyclic representations

Let `V ≠ 0` be a representation of `A`. A vector `v ∈ V` is **cyclic** if it generates `V`, i.e.
`Av = V`. A representation admitting a cyclic vector is **cyclic**. The problem asks to show:

* **(a)** `V` is irreducible if and only if all nonzero vectors of `V` are cyclic.
* **(b)** `V` is cyclic if and only if it is isomorphic to `A/I`, where `I` is a left ideal in `A`.
* **(c)** Give an example of an indecomposable representation which is not cyclic.

## Formalization

A vector `v` is cyclic when `Submodule.span A {v} = ⊤` (the `A`-submodule it generates is all of
`V`). Irreducibility is `IsSimpleModule A V`. Left ideals of `A` are `Submodule A A`, and `A/I` is
the quotient module.

Parts (a) and (b) are recorded here as `sorry` statements. Part (c) — the explicit example
`A = ℂ[x, y]/I₂` acting on `V = A^*` by `(ρ(a)f)(b) = f(ba)` — requires constructing the coregular
module structure and is deferred to a dedicated follow-up item.

This is the **statement pass**.
-/

namespace Etingof.Problem2_5_2

variable {A : Type*} [Ring A]

/-- **Problem 2.5.2(a).** A nonzero representation `V` is irreducible if and only if every nonzero
vector of `V` is cyclic (generates `V`). -/
theorem irreducible_iff_forall_cyclic (V : Type*) [AddCommGroup V] [Module A V] [Nontrivial V] :
    IsSimpleModule A V ↔ ∀ v : V, v ≠ 0 → Submodule.span A {v} = ⊤ := by
  sorry

/-- **Problem 2.5.2(b).** A nonzero representation `V` is cyclic (admits a cyclic vector) if and
only if it is isomorphic to `A/I` for some left ideal `I` of `A`. -/
theorem cyclic_iff_isoQuotient (V : Type*) [AddCommGroup V] [Module A V] [Nontrivial V] :
    (∃ v : V, Submodule.span A {v} = ⊤) ↔
      ∃ I : Submodule A A, Nonempty (V ≃ₗ[A] (A ⧸ I)) := by
  sorry

end Etingof.Problem2_5_2
