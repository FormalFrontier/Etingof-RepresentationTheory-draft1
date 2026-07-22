import Mathlib.Algebra.Homology.ShortComplex.ShortExact
import EtingofRepresentationTheory.Chapter7.Definition7_9_1
import EtingofRepresentationTheory.Chapter7.Definition7_9_4

/-!
# Discussion after Example 7.9.5: additive functors on semisimple categories

The text remarks that in a semisimple category, any additive functor is
automatically exact on both sides.

In a semisimple abelian category (Definition 7.9.4) every short exact sequence
splits, i.e. is isomorphic to `0 → X → X ⊕ Y → Y → 0`. An additive functor
(Definition 7.9.1) preserves finite biproducts, hence sends a splitting to a
splitting; and a split short complex is short exact. So an additive functor out
of a semisimple category carries every short exact sequence to a short exact
sequence — it is exact on both sides.

## Mathlib correspondence

The two ingredients are `CategoryTheory.ShortComplex.Splitting.map` (an additive
functor maps a splitting to a splitting) and
`CategoryTheory.ShortComplex.Splitting.shortExact` (a split short complex is short
exact). "Exact on both sides" is `ShortComplex.ShortExact`, which packages
`Mono` on the left map, `Epi` on the right map, and exactness in the middle.
-/

open CategoryTheory

/-- Discussion after Example 7.9.5: an additive functor `F : C ⥤ D` between abelian
categories, defined on a semisimple category `C`, is exact on both sides — it
carries every short exact sequence to a short exact sequence.

In a semisimple category every short exact sequence `S` splits (Definition 7.9.4);
the additive functor `F` maps that splitting to a splitting of `S.map F`, and a
split short complex is short exact. -/
theorem Etingof.additiveFunctor_shortExact_of_isSemisimpleCategory
    {C D : Type*} [Category C] [Category D] [Abelian C] [Abelian D]
    (hC : Etingof.IsSemisimpleCategory C) (F : C ⥤ D) [F.Additive]
    (S : ShortComplex C) (hS : S.ShortExact) :
    (S.map F).ShortExact :=
  ((hC S hS).some.map F).shortExact
