import Mathlib

/-!
# Problem 5.12.5: the sum of dimensions of the irreducible representations of `S_n`

**Problem 5.12.5.** Find the sum of dimensions of all irreducible representations of the
symmetric group `S_n`.

*Hint.* Show that all irreducible representations of `S_n` are real, i.e., admit a
nondegenerate invariant symmetric form. Then use the Frobenius-Schur theorem.

## Formalization

The Frobenius-Schur theorem gives, for any finite group `G` all of whose irreducibles are of
real type, the identity
`∑_{V irreducible} dim V = #{g ∈ G : g² = 1}`
(the number of elements whose square is the identity — the "square roots of `1`"). For the
symmetric group every irreducible is real, so the sought sum of dimensions is the number of
involutions-or-identity of `S_n`.

We phrase the answer against an arbitrary **complete, irredundant** list of irreducible complex
representations `V : ι → FDRep ℂ (Equiv.Perm (Fin n))`:

* `hsimple` — each `V i` is irreducible (`CategoryTheory.Simple`);
* `hpairwise` — the `V i` are pairwise non-isomorphic;
* `hcomplete` — every irreducible is isomorphic to some `V i`.

Under these hypotheses the sum of dimensions equals `#{g : g * g = 1}`.

Statement pass: the proof is left as `sorry`.
-/

namespace Etingof

open CategoryTheory

/-- Problem 5.12.5. For a complete irredundant family `V` of irreducible complex representations
of `S_n = Equiv.Perm (Fin n)`, the sum of their dimensions equals the number of elements
`g ∈ S_n` with `g² = 1` (the Frobenius-Schur count, valid because every irreducible of `S_n`
is of real type). -/
theorem sum_finrank_irreducible_eq_card_sq_eq_one
    (n : ℕ)
    (ι : Type) [Fintype ι]
    (V : ι → FDRep ℂ (Equiv.Perm (Fin n)))
    (hsimple : ∀ i, Simple (V i))
    (hpairwise : ∀ i j, Nonempty (V i ≅ V j) → i = j)
    (hcomplete : ∀ W : FDRep ℂ (Equiv.Perm (Fin n)), Simple W → ∃ i, Nonempty (W ≅ V i)) :
    ∑ i, Module.finrank ℂ (V i) =
      Fintype.card {g : Equiv.Perm (Fin n) // g * g = 1} := by
  sorry

end Etingof
