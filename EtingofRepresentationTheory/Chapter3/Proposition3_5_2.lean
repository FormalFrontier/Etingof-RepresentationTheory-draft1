import Mathlib.RingTheory.Jacobson.Ideal

/-!
# Proposition 3.5.2: Rad(A) is a Two-Sided Ideal

Rad(A), the radical of a finite dimensional algebra `A` — the set of elements acting by
zero in every irreducible representation, equivalently the intersection of the
annihilators of all simple modules — is a *two-sided* ideal of `A`.

In Mathlib the radical is `Ideal.jacobson (⊥ : Ideal A)`. For a general (possibly
noncommutative) ring, `Ideal A` is a *left* ideal (`Submodule A A`), so the left-ideal
property (closure under multiplication on the left) holds by construction. The
mathematical content of Proposition 3.5.2 is the remaining half: closure under
multiplication on the right. Mathlib supplies this as the instance
`Ideal.IsTwoSided` for the Jacobson radical of a two-sided ideal (and `⊥` is two-sided).
-/

/-- The radical `Rad(A) = Ideal.jacobson ⊥` is a two-sided ideal: it is closed under
multiplication on both the left and the right. The left-multiplication closure
(`r * a ∈ Rad(A)`) is the left-ideal structure of `Ideal A`; the right-multiplication
closure (`a * r ∈ Rad(A)`) is the genuine content of Etingof Proposition 3.5.2.

Equivalently, `Ideal.jacobson (⊥ : Ideal A)` carries the `Ideal.IsTwoSided` instance,
see `Etingof.radical_isTwoSided` below. -/
theorem Etingof.radical_is_ideal (A : Type*) [Ring A]
    (a r : A) (ha : a ∈ Ideal.jacobson (⊥ : Ideal A)) :
    r * a ∈ Ideal.jacobson (⊥ : Ideal A) ∧ a * r ∈ Ideal.jacobson (⊥ : Ideal A) :=
  ⟨Ideal.mul_mem_left _ r ha, Ideal.mul_mem_right r _ ha⟩

/-- Proposition 3.5.2, packaged as the Mathlib `Ideal.IsTwoSided` property: the radical
`Ideal.jacobson (⊥ : Ideal A)` is two-sided. This records that the underlying left ideal
is in fact closed under right multiplication. -/
theorem Etingof.radical_isTwoSided (A : Type*) [Ring A] :
    (Ideal.jacobson (⊥ : Ideal A)).IsTwoSided :=
  inferInstance
