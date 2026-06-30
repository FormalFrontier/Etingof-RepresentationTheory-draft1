import Mathlib.CategoryTheory.Limits.Yoneda
import Mathlib.CategoryTheory.Limits.Preserves.Finite
import Mathlib.Algebra.Category.ModuleCat.Monoidal.Closed
import Mathlib.Algebra.Category.ModuleCat.ChangeOfRingsExact
import Mathlib.Algebra.Category.ModuleCat.Descent

/-!
# Example 7.9.6: Exactness Properties of Standard Functors

(i) The functors Ind_K^G, Res_K^G are exact.
(ii) The functor Hom(X, ?) is left exact, but not necessarily right exact.
     Counterexample: 0 → ℤ → ℤ → ℤ/2ℤ → 0 with Hom(ℤ/2ℤ, ?).
(iii) The functor X ⊗_A - for a right A-module X is right exact but not
      necessarily left exact. Counterexample: tensor the above sequence by ℤ/2ℤ.

## Mathlib correspondence

In the representation-theoretic setting (group representations over a field `k`,
finite groups) the functors of part (i) are change-of-rings functors along the
inclusion of group algebras `f : k[K] → k[G]`:

* `Res_K^G` is restriction of scalars, `ModuleCat.restrictScalars f`;
* `Ind_K^G` is extension of scalars, `ModuleCat.extendScalars f` (the functor
  `k[G] ⊗_{k[K]} -`).

Restriction of scalars is always exact (parts (i) Res below). Extension of
scalars is always right exact (it is a left adjoint), and it is left exact —
hence exact — exactly when the ring map is flat. For the group-algebra
inclusion `k[K] → k[G]` of a subgroup, `k[G]` is free of rank `[G : K]` as a
`k[K]`-module, hence flat, so `Ind_K^G` is exact. We record the flat hypothesis
explicitly in `Etingof.extendScalars_exact_of_flat`.

Left exactness of `Hom` (part (ii)) is available via the covariant Yoneda functor
`coyoneda.obj (op X)`, which preserves all limits. The negative direction
(failure of right exactness) is a separate computation with the explicit
sequence above and is not formalized here.

For the tensor functor (part (iii)), Mathlib's monoidal closed structure on
`ModuleCat` is defined over a commutative ring, so the categorical statement
`Etingof.tensor_right_exact` below is restricted to `[CommRing R]`. The book's
claim is for `X ⊗_A -` over an arbitrary (possibly noncommutative) ring `A`; the
general noncommutative monoidal statement is not currently expressible through
Mathlib's `ModuleCat` monoidal API. The negative direction (failure of left
exactness) is again a separate computation and is not formalized here.
-/

open CategoryTheory CategoryTheory.Limits

universe u

namespace Etingof

/-! ## Part (i): exactness of `Res` and `Ind` -/

/-- `Res_K^G`, restriction of scalars, preserves finite limits: it is left exact.
For group representations `f` is the inclusion of group algebras `k[K] → k[G]`.
(Etingof Example 7.9.6(i)) -/
instance restrictScalars_preservesFiniteLimits
    {R S : Type u} [CommRing R] [CommRing S] (f : R →+* S) :
    PreservesFiniteLimits (ModuleCat.restrictScalars f) :=
  inferInstance

/-- `Res_K^G`, restriction of scalars, preserves finite colimits: it is right exact.
Together with `restrictScalars_preservesFiniteLimits` this expresses that `Res`
is exact. (Etingof Example 7.9.6(i)) -/
instance restrictScalars_preservesFiniteColimits
    {R S : Type u} [CommRing R] [CommRing S] (f : R →+* S) :
    PreservesFiniteColimits (ModuleCat.restrictScalars f) :=
  inferInstance

/-- `Ind_K^G`, extension of scalars, preserves finite colimits: it is right exact.
This holds unconditionally because `extendScalars f` is a left adjoint (of
`restrictScalars f`). (Etingof Example 7.9.6(i)) -/
instance extendScalars_preservesFiniteColimits
    {R S : Type u} [CommRing R] [CommRing S] (f : R →+* S) :
    PreservesFiniteColimits (ModuleCat.extendScalars.{u, u, u} f) :=
  letI : (ModuleCat.extendScalars.{u, u, u} f).IsLeftAdjoint :=
    (ModuleCat.extendRestrictScalarsAdj.{u, u, u} f).isLeftAdjoint
  inferInstance

/-- `Ind_K^G`, extension of scalars along a flat ring map, preserves finite limits:
it is left exact, hence (with right exactness above) exact.

For group representations the relevant map is the inclusion of group algebras
`k[K] → k[G]`, along which `k[G]` is free, hence flat, so this hypothesis is
satisfied and `Ind_K^G` is exact. (Etingof Example 7.9.6(i)) -/
lemma extendScalars_preservesFiniteLimits_of_flat
    {R S : Type u} [CommRing R] [CommRing S] {f : R →+* S} (hf : f.Flat) :
    PreservesFiniteLimits (ModuleCat.extendScalars.{u, u, u} f) :=
  ModuleCat.preservesFiniteLimits_extendScalars_of_flat hf

/-- `Ind_K^G`, extension of scalars along a flat ring map, is exact: it preserves
finite limits and finite colimits. This is the exactness of `Ind` in Etingof
Example 7.9.6(i), with the flatness hypothesis that holds for the group-algebra
inclusion `k[K] → k[G]`. -/
lemma extendScalars_exact_of_flat
    {R S : Type u} [CommRing R] [CommRing S] {f : R →+* S} (hf : f.Flat) :
    PreservesFiniteLimits (ModuleCat.extendScalars.{u, u, u} f) ∧
      PreservesFiniteColimits (ModuleCat.extendScalars.{u, u, u} f) :=
  ⟨extendScalars_preservesFiniteLimits_of_flat hf, inferInstance⟩

/-! ## Part (ii): left exactness of `Hom` -/

/-- The Hom functor Hom(X, -) is left exact: it preserves finite limits.
This is the covariant Yoneda functor applied to X. (Etingof Example 7.9.6(ii))

In Mathlib, `coyoneda.obj (op X)` is the functor `Hom(X, -)`, and it preserves
all limits (hence in particular finite limits, making it left exact). The book
also notes `Hom(X, -)` need not be right exact, witnessed by applying
`Hom(ℤ/2ℤ, -)` to `0 → ℤ → ℤ → ℤ/2ℤ → 0`; that negative direction is not
formalized here. -/
instance hom_left_exact {C : Type*} [Category C] (X : C) :
    PreservesFiniteLimits (coyoneda.obj (Opposite.op X)) :=
  inferInstance

/-! ## Part (iii): right exactness of the tensor functor -/

/-- The tensor product functor `X ⊗ -` is right exact: it preserves finite colimits.
(Etingof Example 7.9.6(iii))

In Mathlib, `ModuleCat R` is a monoidal closed category, so `tensorLeft X` (the functor
`X ⊗ -`) is a left adjoint of the internal hom functor. Left adjoints preserve all
colimits, hence in particular finite colimits, making the tensor functor right exact.

The `[CommRing R]` hypothesis comes from Mathlib's monoidal closed structure on
`ModuleCat`, which is built over a commutative ring. The book states part (iii) for
`X ⊗_A -` with `X` a right module over an arbitrary (possibly noncommutative) ring
`A`; that general statement is not currently expressible through Mathlib's
`ModuleCat` monoidal API. The book's negative direction (the tensor functor need not
be left exact, witnessed by `ℤ/2ℤ ⊗ -` on `0 → ℤ → ℤ → ℤ/2ℤ → 0`) is also not
formalized here. -/
instance tensor_right_exact {R : Type*} [CommRing R] (X : ModuleCat R) :
    PreservesFiniteColimits (MonoidalCategory.tensorLeft X) :=
  inferInstance

end Etingof
