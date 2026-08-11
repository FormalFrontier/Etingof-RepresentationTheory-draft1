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

open CategoryTheory Limits

/-- The object property "`M` is a finitely generated `A`-module" on `ModuleCat A`. -/
def Etingof.isFinitelyGenerated (A : Type*) [CommRing A] :
    ObjectProperty (ModuleCat.{0} A) :=
  fun M => Module.Finite A M

namespace Etingof.Problem7_7_3

variable {A : Type} [CommRing A]

/-- Over a Noetherian ring, a submodule of a finitely generated module is finitely
generated, so `isFinitelyGenerated A` is closed under subobjects in `ModuleCat A`. -/
instance isClosedUnderSubobjects [IsNoetherianRing A] :
    (Etingof.isFinitelyGenerated A).IsClosedUnderSubobjects where
  prop_of_mono {X Y} f _ hY := by
    haveI : Module.Finite A Y := hY
    haveI : IsNoetherian A Y := isNoetherian_of_isNoetherianRing_of_finite A Y
    exact Module.Finite.of_injective f.hom ((ModuleCat.mono_iff_injective f).mp inferInstance)

/-- A quotient of a finitely generated module is finitely generated, so
`isFinitelyGenerated A` is closed under quotients in `ModuleCat A`. -/
instance isClosedUnderQuotients :
    (Etingof.isFinitelyGenerated A).IsClosedUnderQuotients where
  prop_of_epi {X Y} f _ hX := by
    haveI : Module.Finite A X := hX
    exact Module.Finite.of_surjective f.hom ((ModuleCat.epi_iff_surjective f).mp inferInstance)

/-- The zero module is finitely generated, so `isFinitelyGenerated A` contains a zero
object. -/
instance containsZero : (Etingof.isFinitelyGenerated A).ContainsZero where
  exists_zero :=
    ⟨ModuleCat.of A PUnit, ModuleCat.isZero_of_subsingleton _,
      Module.Finite.of_surjective (0 : A →ₗ[A] PUnit) fun _ => ⟨0, Subsingleton.elim _ _⟩⟩

/-- A finite product of finitely generated modules is finitely generated, so
`isFinitelyGenerated A` is closed under finite products in `ModuleCat A`. -/
instance isClosedUnderFiniteProducts :
    (Etingof.isFinitelyGenerated A).IsClosedUnderFiniteProducts := by
  apply ObjectProperty.IsClosedUnderFiniteProducts.of_isClosedUnderLimitsOfShape.{0}
  intro J _
  apply ObjectProperty.IsClosedUnderLimitsOfShape.mk'
  rintro _ ⟨F, hF⟩
  haveI : ∀ j : J, Module.Finite A (F.obj ⟨j⟩) := fun j => hF ⟨j⟩
  haveI : Module.Finite A (ModuleCat.of A (∀ j : J, (F.obj ⟨j⟩ : Type))) := Module.Finite.pi
  exact (Etingof.isFinitelyGenerated A).prop_of_iso
    (Iso.symm (HasLimit.isoOfNatIso Discrete.natIsoFunctor ≪≫ ModuleCat.piIsoPi _)) this

end Etingof.Problem7_7_3

/-- Problem 7.7.3: for a finitely generated commutative ring `A` (a finite-type
`ℤ`-algebra), the full subcategory of `ModuleCat A` on the finitely generated modules
is abelian. -/
theorem Etingof.Problem7_7_3 (A : Type) [CommRing A] [Algebra ℤ A]
    [Algebra.FiniteType ℤ A] :
    Nonempty (Abelian (Etingof.isFinitelyGenerated A).FullSubcategory) := by
  haveI : IsNoetherianRing A := Algebra.FiniteType.isNoetherianRing ℤ A
  exact ⟨inferInstance⟩
