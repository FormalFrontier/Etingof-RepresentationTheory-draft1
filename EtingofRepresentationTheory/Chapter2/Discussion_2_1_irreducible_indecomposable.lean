import EtingofRepresentationTheory.Chapter2.Definition2_3_8
import Mathlib.RingTheory.SimpleModule.Basic

/-!
# Discussion 2.1: Irreducible implies indecomposable

Etingof §2.1 defines a nonzero representation `V` of an algebra `A` to be **irreducible**
if its only subrepresentations are `0` and `V`, and **indecomposable** if it cannot be
written as a direct sum of two nonzero subrepresentations. The text then remarks:

> Obviously, irreducible implies indecomposable, but not vice versa.

Irreducibility is Mathlib's `IsSimpleModule A V` (the submodule lattice is a simple order),
and indecomposability is `Etingof.IsIndecomposable A V` (Definition 2.3.8). This file records
the "irreducible ⇒ indecomposable" implication linking the two in-project notions; Mathlib's
`indecomposable_of_simple` is stated for categorical `Simple` objects, not for
`Etingof.IsIndecomposable`.
-/

namespace Etingof

/-- **Irreducible implies indecomposable** (Etingof §2.1). A simple (irreducible) module has
no nontrivial complemented submodule, so it is indecomposable in the sense of
Definition 2.3.8. -/
theorem IsIndecomposable.of_isSimpleModule (A V : Type*) [Ring A] [AddCommGroup V]
    [Module A V] (h : IsSimpleModule A V) : Etingof.IsIndecomposable A V := by
  haveI := h
  refine ⟨IsSimpleModule.nontrivial A V, fun W₁ W₂ hC => ?_⟩
  rcases eq_bot_or_eq_top W₁ with hW₁ | hW₁
  · exact Or.inl hW₁
  · refine Or.inr ?_
    subst hW₁
    exact top_disjoint.mp hC.disjoint

end Etingof
