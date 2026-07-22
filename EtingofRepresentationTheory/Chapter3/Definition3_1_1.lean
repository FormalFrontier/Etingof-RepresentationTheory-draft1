import Mathlib.RingTheory.SimpleModule.Basic

/-!
# Definition 3.1.1: Semisimple (Completely Reducible) Representation

A **semisimple** (or **completely reducible**) representation of `A` is a direct sum of
irreducible representations.

## Mathlib correspondence

Following the project convention (see `Proposition3_1_4.lean`), a representation of the
algebra `A` is modeled as an `A`-module `V`. The book's notion — `V` is a direct sum of
irreducible (simple) `A`-subrepresentations — is exactly `IsSemisimpleModule A V` in
Mathlib, which asserts that every `A`-submodule has an `A`-module complement (equivalently,
`V` is the direct sum of its simple `A`-submodules).

The semisimplicity is **over the algebra `A`**, not over a base field: a vector space is
always semisimple over a field, so semisimplicity is only meaningful as a property of the
`A`-module structure carrying the representation.
-/

/-- A semisimple representation in the sense of Etingof Definition 3.1.1: a representation
of the algebra `A` (i.e. an `A`-module `V`) that is a direct sum of irreducible
subrepresentations. This is `IsSemisimpleModule A V` in Mathlib — semisimplicity over the
algebra `A`. -/
abbrev Etingof.IsSemisimpleRepresentation (A : Type*) (V : Type*)
    [Ring A] [AddCommGroup V] [Module A V] :=
  IsSemisimpleModule A V
