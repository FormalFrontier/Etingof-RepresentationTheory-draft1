import Mathlib

/-!
# Problem 7.7.3: The category of finitely generated modules is abelian

**Problem 7.7.3.** Let `A` be a finitely generated commutative ring. Show that the
category of finitely generated `A`-modules is an abelian category. (Hint: use the
Hilbert basis theorem.)

## Formalization

A "finitely generated commutative ring" is a commutative ring that is a
finitely-generated `ℤ`-algebra, i.e. `Algebra.FiniteType ℤ A`. By the Hilbert basis
theorem such an `A` is Noetherian, so finitely generated `A`-modules are closed under
subobjects, quotients, kernels and cokernels; the full subcategory they span in
`ModuleCat A` is therefore abelian.

The category of finitely generated `A`-modules is the full subcategory of `ModuleCat A`
on the object property `fun M => Module.Finite A M`, i.e.
`CategoryTheory.ObjectProperty.FullSubcategory (fun M : ModuleCat A => Module.Finite A M)`.
-/

open CategoryTheory

/-- The object property "`M` is a finitely generated `A`-module" on `ModuleCat A`. -/
def Etingof.isFinitelyGenerated (A : Type*) [CommRing A] :
    ObjectProperty (ModuleCat.{0} A) :=
  fun M => Module.Finite A M

/-- Problem 7.7.3: for a finitely generated commutative ring `A` (a finite-type
`ℤ`-algebra), the full subcategory of `ModuleCat A` on the finitely generated modules
is abelian. -/
theorem Etingof.Problem7_7_3 (A : Type) [CommRing A] [Algebra ℤ A]
    [Algebra.FiniteType ℤ A] :
    Nonempty (Abelian (Etingof.isFinitelyGenerated A).FullSubcategory) := by
  sorry
