import EtingofRepresentationTheory.Chapter2.Definition2_2_1

/-!
# Definition 2.2.2: Unit in an Associative Algebra

A **unit** in an associative algebra `A` is an element `e ∈ A` such that `ea = ae = a` for all `a`.

## Faithfulness note

Definition 2.2.1 is non-unital (see `Definition2_2_1.lean`), so a unit is genuinely *extra*
structure introduced here. We define it as the predicate "`e` is a two-sided identity for the
multiplication of `A`", and record that such a unit is unique when it exists — so this is a real
defining property, not a fact that holds automatically for any ring.

(The base field `k` is an explicit argument because, for a non-unital algebra mixin, the carrier
`A` does not determine `k`.)
-/

namespace Etingof.AssociativeAlgebra

variable (k : Type*) {A : Type*} [Field k] [AddCommGroup A] [Module k A]
  [inst : AssociativeAlgebra k A]

/-- **Definition 2.2.2** (Etingof). An element `e : A` is a *unit* (two-sided identity) of the
associative algebra `A` over `k` when `e * a = a` and `a * e = a` for every `a : A`, where `*` is
the multiplication of Definition 2.2.1. Unlike a bare `Ring`, an algebra in the sense of
Definition 2.2.1 need not have such an element. -/
def IsUnit (e : A) : Prop :=
  ∀ a : A, inst.mul e a = a ∧ inst.mul a e = a

/-- A unit, if it exists, is unique: if `e` and `e'` are both two-sided identities then
`e = e * e' = e'`. This is the content that makes "unit" a genuine defining property. -/
theorem isUnit_unique {e e' : A} (he : IsUnit k e) (he' : IsUnit k e') : e = e' := by
  have h1 := (he' e).2   -- `e * e' = e`
  have h2 := (he e').1   -- `e * e' = e'`
  exact h1.symm.trans h2

end Etingof.AssociativeAlgebra
