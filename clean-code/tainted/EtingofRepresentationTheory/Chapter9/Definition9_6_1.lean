import Mathlib.CategoryTheory.Abelian.Basic
import Mathlib.CategoryTheory.Preadditive.Projective.Basic
import Mathlib.CategoryTheory.Simple
import Mathlib.CategoryTheory.Subobject.Basic
import Mathlib.Order.KrullDimension

universe u v

/-!
# Definition 9.6.1: Finite abelian category

A **finite abelian category** over a field k is an abelian category 𝒞 which has enough
projectives, in which there are finitely many simple objects (up to isomorphism), and in
which every object has finite length.

The primary example is the category of finite dimensional modules over a finite
dimensional k-algebra.

## Mathlib correspondence

Mathlib has `CategoryTheory.Abelian` for abelian categories and
`CategoryTheory.EnoughProjectives` for the enough projectives condition. The finiteness
condition on simple objects requires a custom predicate: we ask for a `Fintype` on the
type of isomorphism classes of simple objects.

The **finite-length** standing assumption of §9.6 is recorded order-theoretically, as
`FiniteDimensionalOrder (Subobject X)` for every object `X`: the subobject lattice has a
longest strictly increasing chain, which is exactly "`X` has finite length" (the height of
`⊤ : Subobject X` is the composition length). Recording it in this order-theoretic form
keeps `Definition9_6_1.lean` free of the `HasFiniteLength` inductive predicate
(`Introduction_9_6.lean`, which imports this file), and feeds the composition-length API
`Etingof.clength` directly. Etingof's Definition 9.6.1 proper asks only "enough projectives
+ finitely many simples"; finite length is the standing assumption stated alongside it in
the §9.6 introduction, and is folded into the class here so it is available to every
consumer of the subobject-length API.
-/

open CategoryTheory

/-- A finite abelian category in the sense of Etingof Definition 9.6.1.
An abelian category with enough projectives and finitely many isomorphism classes of
simple objects.

We encode "finitely many simples up to isomorphism" by requiring a finite type `ι`
indexing the simple objects, such that every simple object is isomorphic to one in the
indexed family. -/
class Etingof.IsFiniteAbelianCategory (C : Type u) [Category.{v} C] extends Abelian C,
    EnoughProjectives C where
  /-- An index type for the simple objects. -/
  ι : Type
  /-- The index type is finite. -/
  [finι : Fintype ι]
  /-- A representative simple object for each index. -/
  simpleObj : ι → C
  /-- Each representative is simple. -/
  simple_simpleObj : ∀ i, Simple (simpleObj i)
  /-- Every simple object is isomorphic to some representative. -/
  iso_of_simple : ∀ (X : C), Simple X → ∃ i, Nonempty (X ≅ simpleObj i)
  /-- Every object has finite length: its subobject lattice has a longest strictly
  increasing chain. This is the §9.6 finite-length standing assumption, recorded
  order-theoretically (the height of `⊤ : Subobject X` is the composition length) so that
  the composition-length API `Etingof.clength` can consume it directly. -/
  finiteDimensionalOrder_subobject : ∀ X : C, FiniteDimensionalOrder (Subobject X)

namespace Etingof.IsFiniteAbelianCategory

/-- In a finite abelian category, the subobject lattice of every object is finite
dimensional as an order (the order-theoretic form of "every object has finite length").
Exposed as an instance so that the composition-length API can find it by typeclass
resolution. -/
instance finiteDimensionalOrderSubobject {C : Type u} [Category.{v} C]
    [IsFiniteAbelianCategory C] (X : C) : FiniteDimensionalOrder (Subobject X) :=
  IsFiniteAbelianCategory.finiteDimensionalOrder_subobject X

end Etingof.IsFiniteAbelianCategory
