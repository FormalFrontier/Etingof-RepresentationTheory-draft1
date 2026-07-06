import Mathlib

/-!
# Exercise 4.2.3: fewer irreducibles than conjugacy classes in the modular case

**Exercise 4.2.3.** Show that if `|G| = 0` in `k`, then the number of isomorphism
classes of irreducible representations of `G` over `k` is strictly less than the
number of conjugacy classes in `G`.

*Hint.* Let `P = ∑_{g ∈ G} g ∈ k[G]`. Then `P² = 0`. So `P` has zero trace in every
finite-dimensional representation of `G` over `k`.

## Formalization

The number of conjugacy classes of `G` is `Nat.card (ConjClasses G)`.

The "number of isomorphism classes of irreducible representations of `G` over `k`" is
`Nat.card (IrrepClasses k G)`, where `IrrepClasses k G` is the type of isomorphism
classes of objects of the full subcategory of `FDRep k G` spanned by the simple
(irreducible) representations. This is the genuine set of irreducibles up to
isomorphism, obtained via the isomorphism-class setoid on a category
(`CategoryTheory.isIsomorphicSetoid`).

The hypothesis "`|G| = 0` in `k`" is `(Fintype.card G : k) = 0`, i.e. the characteristic
of `k` divides `|G|`.

This is a statement-pass formalization: the statement is fixed faithfully and the proof
is deferred (`sorry`). The mathematical content is that in the modular case the element
`P = ∑_g g` is nonzero, central, nilpotent (`P² = |G| · P = 0`), and hence lies in the
Jacobson radical of `k[G]`; the group algebra is therefore not semisimple, so the number
of simple modules is strictly smaller than the dimension of its centre, which equals the
number of conjugacy classes.
-/

open CategoryTheory

namespace Etingof

/-- The type of isomorphism classes of irreducible (simple) representations of `G` over
`k`: isomorphism classes of objects in the full subcategory of `FDRep k G` on the simple
objects. -/
def IrrepClasses (k G : Type*) [Field k] [Monoid G] : Type _ :=
  Quotient (isIsomorphicSetoid
    (ObjectProperty.FullSubcategory (fun V : FDRep k G => Simple V)))

/-- **Exercise 4.2.3.** If `|G| = 0` in `k` (the characteristic of `k` divides the order
of the finite group `G`), then the number of isomorphism classes of irreducible
representations of `G` over `k` is strictly less than the number of conjugacy classes of
`G`. -/
theorem Exercise4_2_3 (k G : Type*) [Field k] [Group G] [Fintype G]
    (h : (Fintype.card G : k) = 0) :
    Nat.card (IrrepClasses k G) < Nat.card (ConjClasses G) := by
  sorry

end Etingof
