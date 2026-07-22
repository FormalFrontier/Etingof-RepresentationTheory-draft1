import Mathlib

/-!
# Problem 4.1.4: Irreducible representations of `p`-groups in characteristic `p`

**Problem 4.1.4.** Let `G` be a group of order `pⁿ`. Show that every irreducible
representation of `G` over a field `k` of characteristic `p` is trivial.

Here "trivial" means that every group element acts as the identity operator. Combined
with irreducibility (simplicity), this forces the representation to be one-dimensional:
if the action is trivial then every `k`-subspace is a subrepresentation, so a simple
module must have no proper nonzero subspaces, i.e. dimension one.

## Formalization

We model an irreducible representation as a `Representation k G V` whose associated
`MonoidAlgebra k G`-module `ρ.asModule` is simple. The faithful statement of "trivial"
is that `ρ g` is the identity linear map for every `g : G`.
-/

/-- **Problem 4.1.4.** If `G` has order `pⁿ` (with `p` prime) and `k` has characteristic
`p`, then every irreducible representation of `G` over `k` is trivial: every group
element acts as the identity. -/
theorem Etingof.Problem4_1_4 {p n : ℕ} [Fact p.Prime]
    {k : Type*} [Field k] [CharP k p]
    {G : Type*} [Group G] [Fintype G] (hG : Fintype.card G = p ^ n)
    {V : Type*} [AddCommGroup V] [Module k V]
    (ρ : Representation k G V)
    (hV : IsSimpleModule (MonoidAlgebra k G) ρ.asModule) :
    ∀ g : G, ρ g = LinearMap.id := by
  sorry
