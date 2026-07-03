import Mathlib.CategoryTheory.Linear.Basic
import Mathlib.CategoryTheory.Linear.LinearFunctor
import Mathlib.CategoryTheory.Preadditive.AdditiveFunctor
import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Biproducts

/-!
# Definition 7.9.1: Additive and k-linear Functor

A functor F between two abelian categories is **additive** if it induces
homomorphisms on Hom groups.

For k-linear categories, F is **k-linear** if it induces k-linear maps
between Hom spaces.

## Mathlib correspondence

Exact match:
- `CategoryTheory.Functor.Additive` for additive functors
- `CategoryTheory.Functor.Linear` for k-linear functors

## Discussion after Definition 7.9.1

The book remarks that "it is easy to show that if `F` is an additive functor,
then `F(X ⊕ Y)` is canonically isomorphic to `F(X) ⊕ F(Y)`". We record this as
`Etingof.AdditiveFunctor.mapBiprod`: for an additive functor `F` between
preadditive categories where the source has binary biproducts, there is a
canonical isomorphism `F(X ⊞ Y) ≅ F(X) ⊞ F(Y)`. This delegates to Mathlib's
`CategoryTheory.Functor.mapBiprod`, available because an additive functor
preserves zero morphisms and finite biproducts.
-/

/-- An additive functor between preadditive categories, in the sense of
Etingof Definition 7.9.1. This is `CategoryTheory.Functor.Additive` in Mathlib. -/
abbrev Etingof.AdditiveFunctor {C : Type*} {D : Type*} [CategoryTheory.Category C]
    [CategoryTheory.Category D] [CategoryTheory.Preadditive C]
    [CategoryTheory.Preadditive D] (F : CategoryTheory.Functor C D) :=
  CategoryTheory.Functor.Additive F

/-- A `k`-linear functor between `k`-linear categories, in the sense of the
second half of Etingof Definition 7.9.1: `F` induces `k`-linear maps between
Hom spaces. This is `CategoryTheory.Functor.Linear` in Mathlib. -/
abbrev Etingof.LinearFunctor (k : Type*) [Semiring k] {C : Type*} {D : Type*}
    [CategoryTheory.Category C] [CategoryTheory.Category D]
    [CategoryTheory.Preadditive C] [CategoryTheory.Preadditive D]
    [CategoryTheory.Linear k C] [CategoryTheory.Linear k D]
    (F : CategoryTheory.Functor C D) :=
  CategoryTheory.Functor.Linear k F
namespace Etingof.AdditiveFunctor

open CategoryTheory CategoryTheory.Limits

variable {C D : Type*} [Category C] [Category D] [Preadditive C] [Preadditive D]
  [HasBinaryBiproducts C] (F : C ⥤ D) [F.Additive] (X Y : C)

/-- An additive functor preserves binary biproducts: this is the finite-biproduct
preservation of an additive functor specialised to a pair. It provides the
`HasBinaryBiproduct (F X) (F Y)` needed to state the comparison isomorphism below. -/
instance preservesBinaryBiproduct : PreservesBinaryBiproduct X Y F :=
  preservesBinaryBiproduct_of_preservesBiproduct F X Y

/-- **Discussion after Definition 7.9.1.** An additive functor `F` between
preadditive categories (with binary biproducts in the source) sends the biproduct
`X ⊞ Y` to a canonically isomorphic copy of `F X ⊞ F Y`. This is the canonical
comparison isomorphism `CategoryTheory.Functor.mapBiprod`, which exists because an
additive functor preserves zero morphisms and finite biproducts. -/
noncomputable def mapBiprod : F.obj (X ⊞ Y) ≅ F.obj X ⊞ F.obj Y :=
  F.mapBiprod X Y

/-- The canonical isomorphism of `mapBiprod` has the expected forward map: it is the
lift of the two functor-images of the biproduct projections. -/
theorem mapBiprod_hom :
    (mapBiprod F X Y).hom = biprod.lift (F.map biprod.fst) (F.map biprod.snd) :=
  F.mapBiprod_hom X Y

end Etingof.AdditiveFunctor
