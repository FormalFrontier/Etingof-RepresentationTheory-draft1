import Mathlib.CategoryTheory.Abelian.Basic
import Mathlib.Algebra.Homology.ShortComplex.ShortExact

/-!
# Definition 7.8.2: Short Exact Sequence

A **short exact sequence** is an exact sequence of the form:
0 → X → Y → Z → 0

This holds iff X → Y is injective, Y → Z is surjective, and the induced map
Y/X → Z is an isomorphism. Short exact sequences correspond to extensions of Z by X.

## Mathlib correspondence

Exact match: `CategoryTheory.ShortComplex` bundled with the defining predicate
`CategoryTheory.ShortComplex.ShortExact`. The latter records that `S.f` is a
mono (injectivity of `X → Y`), `S.g` is an epi (surjectivity of `Y → Z`), and
`S` is exact at `Y` (equivalently the induced `Y/X → Z` is an isomorphism).
-/

/-- A short exact sequence `0 → X → Y → Z → 0` in an abelian category, in the
sense of Etingof Definition 7.8.2. It is a `CategoryTheory.ShortComplex`
together with a proof that it is `ShortComplex.ShortExact`: `X → Y` injective,
`Y → Z` surjective, and exact at `Y`. Bundling the `ShortExact` predicate is
what distinguishes a short *exact* sequence from a bare short complex (which the
zero complex would also satisfy). -/
def Etingof.ShortExactSequence (C : Type*) [CategoryTheory.Category C]
    [CategoryTheory.Limits.HasZeroMorphisms C] :=
  {S : CategoryTheory.ShortComplex C // S.ShortExact}
