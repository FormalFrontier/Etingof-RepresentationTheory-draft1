import Mathlib.CategoryTheory.Abelian.Basic
import Mathlib.Algebra.Category.ModuleCat.Abelian
import Mathlib.Algebra.Category.FGModuleCat.Abelian
import Mathlib.RingTheory.Noetherian.Basic
import Mathlib.RingTheory.Finiteness.Basic

/-!
# Example 7.7.2: Module Categories are Abelian

The category of modules over an algebra `A` and the category of finite dimensional
modules over `A` are abelian categories.

## Mathlib correspondence

The book makes two claims, working with a finite dimensional algebra `A` over a field
`k`:
(a) the category of all `A`-modules is abelian, and
(b) the category of finite dimensional `A`-modules is abelian.

Part (a) is an exact match: `ModuleCat A` is an abelian category in Mathlib via
`ModuleCat.instAbelian`.

For part (b) the source category consists of the `A`-modules that are finite
dimensional *over the base field* `k`. Mathlib's `FGModuleCat A` is the category of
`A`-modules that are finitely generated *over* `A`. The point of Example 7.7.2 is that,
in the book's setting where `A` is finite dimensional over `k`, these two conditions
agree, so `FGModuleCat A` is a faithful rendering of the finite dimensional module
category and it is abelian.

The identification of the two categories is the objectwise bridge
`module_finite_iff_finiteDimensional`: for an `A`-module `M` with a compatible
`k`-structure, `M` is finitely generated over `A` iff it is finite dimensional over `k`.
The abelian endpoint `abelian_fgModuleCat_of_finiteDimensional` states part (b) directly
under the book's hypotheses (`A` a finite dimensional `k`-algebra); the required
`IsNoetherianRing A` is *derived* from those hypotheses via
`isNoetherianRing_of_finiteDimensional`, rather than assumed as in the earlier
placeholder.
-/

open CategoryTheory

/-- The category of modules over a ring `A` is an abelian category.
(Etingof Example 7.7.2, part (a)) -/
example (A : Type*) [Ring A] : Abelian (ModuleCat A) := inferInstance

section FiniteDimensionalAlgebra

variable (k A : Type*) [Field k] [Ring A] [Algebra k A]

/-- A finite dimensional algebra over a field is a Noetherian ring.

This is the honest hypothesis behind `Abelian (FGModuleCat A)`: in Etingof's setting `A`
is finite dimensional over the field `k`, hence Artinian and in particular a Noetherian
ring. -/
theorem isNoetherianRing_of_finiteDimensional [FiniteDimensional k A] :
    IsNoetherianRing A :=
  IsNoetherianRing.of_finite k A

/-- Bridge between the two notions of finiteness for a module over a finite dimensional
`k`-algebra `A`.

For an `A`-module `M` carrying a compatible `k`-module structure (an object of the
category the book calls the finite dimensional `A`-modules), `M` is finitely generated
over `A` iff it is finite dimensional over the base field `k`.

The forward direction is `Module.Finite.trans` (`A` is finite over `k` and `M` is finite
over `A`, so `M` is finite over `k`); the reverse is
`Module.Finite.of_restrictScalars_finite` (a `k`-spanning set of `M` also spans over `A`,
since the `k`-action factors through `A`). -/
theorem module_finite_iff_finiteDimensional [FiniteDimensional k A]
    (M : Type*) [AddCommGroup M] [Module A M] [Module k M] [IsScalarTower k A M] :
    Module.Finite A M ↔ FiniteDimensional k M :=
  ⟨fun _ => Module.Finite.trans A M, fun _ => Module.Finite.of_restrictScalars_finite k A M⟩

/-- The category of finite dimensional modules over a finite dimensional `k`-algebra `A`
is abelian.

By `module_finite_iff_finiteDimensional`, `FGModuleCat A` — the finitely generated
`A`-modules — is exactly the category of `A`-modules that are finite dimensional over the
base field `k`, i.e. the finite dimensional module category of Example 7.7.2. It is
abelian because `A` is Noetherian (`isNoetherianRing_of_finiteDimensional`), which here is
derived from the book's hypotheses rather than assumed.
(Etingof Example 7.7.2, part (b)) -/
@[reducible] noncomputable def abelian_fgModuleCat_of_finiteDimensional
    [FiniteDimensional k A] : Abelian (FGModuleCat A) :=
  haveI : IsNoetherianRing A := isNoetherianRing_of_finiteDimensional k A
  inferInstance

end FiniteDimensionalAlgebra

/-- Specializing to the base field `k` itself (`A = k`): the category of finite dimensional
`k`-vector spaces is abelian. -/
noncomputable example (k : Type*) [Field k] : Abelian (FGModuleCat k) :=
  abelian_fgModuleCat_of_finiteDimensional k k
