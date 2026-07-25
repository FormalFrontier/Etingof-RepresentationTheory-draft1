import Mathlib.CategoryTheory.Limits.Yoneda
import Mathlib.CategoryTheory.Limits.Preserves.Finite
import Mathlib.Algebra.Category.ModuleCat.Monoidal.Closed
import Mathlib.Algebra.Category.ModuleCat.ChangeOfRingsExact
import Mathlib.Algebra.Category.ModuleCat.Descent
import Mathlib.LinearAlgebra.TensorProduct.Basic
import Mathlib.Data.ZMod.Basic
import Mathlib.RepresentationTheory.FiniteIndex
import Mathlib.RepresentationTheory.Rep.Res

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
scalars is always right exact (it is a left adjoint), and it is left exact,
hence exact, exactly when the ring map is flat. For the group-algebra
inclusion `k[K] → k[G]` of a subgroup, `k[G]` is free of rank `[G : K]` as a
`k[K]`-module, hence flat, so `Ind_K^G` is exact. We record the flat hypothesis
explicitly in `Etingof.extendScalars_exact_of_flat`.

Left exactness of `Hom` (part (ii)) is available via the covariant Yoneda functor
`coyoneda.obj (op X)`, which preserves all limits. The negative direction
(failure of right exactness) is formalized concretely in
`Etingof.hom_not_right_exact`: applying `Hom(ℤ/2ℤ, -)` to the surjection
`ℤ ↠ ℤ/2ℤ` from the sequence above does not give a surjection, because
`Hom(ℤ/2ℤ, ℤ) = 0` (`Etingof.subsingleton_hom_zmod_int`) while
`Hom(ℤ/2ℤ, ℤ/2ℤ) ≠ 0`.

For the tensor functor (part (iii)), Mathlib's monoidal closed structure on
`ModuleCat` is defined over a commutative ring, so the categorical statement
`Etingof.tensor_right_exact` below is restricted to `[CommRing R]`. The book's
claim is for `X ⊗_A -` over an arbitrary (possibly noncommutative) ring `A`; the
general noncommutative monoidal statement is not currently expressible through
Mathlib's `ModuleCat` monoidal API. The negative direction (failure of left
exactness) is formalized concretely in `Etingof.tensor_not_left_exact`: applying
`ℤ/2ℤ ⊗ -` to the injection `(· * 2) : ℤ ↪ ℤ` gives a non-injective map, because
it kills the nonzero element `1 ⊗ 1` (`Etingof.tmul_one_one_ne_zero`).
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

/-! ### The actual representation-theoretic `Ind` and `Res`

The change-of-rings statements above are the algebraic shadow of Example 7.9.6(i).
The book's functors are `Res_K^G : Rep k G ⥤ Rep k K` and `Ind_K^G : Rep k K ⥤ Rep k G`
for a subgroup `K ≤ G`, which in Mathlib are `Rep.resFunctor K.subtype` and
`Rep.indFunctor k K.subtype` (the same functors used in `Chapter7/Example7_9_2.lean`).

Restriction along *any* group homomorphism is both a right adjoint (of induction,
`Rep.indResAdjunction`) and a left adjoint (of coinduction, `Rep.resCoindAdjunction`),
so `Res` is exact with no hypothesis at all.

For a *finite index* subgroup, induction and coinduction agree (`Rep.indCoindNatIso`),
so `Ind_K^G` is simultaneously a left adjoint of `Res_K^G` (`Rep.indResAdjunction`) and
a right adjoint of it (`Rep.resIndAdjunction`). Hence `Ind` is exact as well, and no
flatness hypothesis has to be supplied from outside. -/

section GroupRepresentations

variable {k : Type u} [CommRing k] {G H : Type u} [Group G] [Group H]

/-- `Res_K^G : Rep k G ⥤ Rep k K` preserves finite limits: it is left exact.
Restriction along a group homomorphism is the right adjoint of induction
(`Rep.indResAdjunction`). (Etingof Example 7.9.6(i)) -/
instance resFunctor_preservesFiniteLimits (φ : G →* H) :
    PreservesFiniteLimits (Rep.resFunctor.{u, u, u} (k := k) φ) :=
  letI : PreservesLimitsOfSize.{0, 0} (Rep.resFunctor.{u, u, u} (k := k) φ) :=
    (Rep.indResAdjunction.{u, u, u} k φ).rightAdjoint_preservesLimits
  inferInstance

/-- `Res_K^G : Rep k G ⥤ Rep k K` preserves finite colimits: it is right exact.
Restriction along a group homomorphism is also a *left* adjoint, namely of coinduction
(`Rep.resCoindAdjunction`). (Etingof Example 7.9.6(i)) -/
instance resFunctor_preservesFiniteColimits (φ : G →* H) :
    PreservesFiniteColimits (Rep.resFunctor.{u, u, u} (k := k) φ) :=
  letI : PreservesColimitsOfSize.{0, 0} (Rep.resFunctor.{u, u, u} (k := k) φ) :=
    (Rep.resCoindAdjunction.{u, u, u} k φ).leftAdjoint_preservesColimits
  inferInstance

/-- **Etingof Example 7.9.6(i)**: `Res_K^G` is exact — it preserves finite limits and
finite colimits. This holds for restriction along an arbitrary group homomorphism; the
subgroup inclusion `K ↪ G` of the book is the case `φ = K.subtype`. -/
theorem resFunctor_exact (φ : G →* H) :
    PreservesFiniteLimits (Rep.resFunctor.{u, u, u} (k := k) φ) ∧
      PreservesFiniteColimits (Rep.resFunctor.{u, u, u} (k := k) φ) :=
  ⟨inferInstance, inferInstance⟩

variable (S : Subgroup G) [S.FiniteIndex]

open scoped Classical in
/-- `Ind_K^G : Rep k K ⥤ Rep k G` preserves finite colimits: it is right exact.
Induction is the left adjoint of restriction (`Rep.indResAdjunction`), and this needs
no finiteness hypothesis. (Etingof Example 7.9.6(i)) -/
instance indFunctor_preservesFiniteColimits :
    PreservesFiniteColimits (Rep.indFunctor.{u, u, u} k S.subtype) :=
  letI : PreservesColimitsOfSize.{0, 0} (Rep.indFunctor.{u, u, u} k S.subtype) :=
    (Rep.indResAdjunction.{u, u, u} k S.subtype).leftAdjoint_preservesColimits
  inferInstance

open scoped Classical in
/-- `Ind_K^G : Rep k K ⥤ Rep k G` preserves finite limits: it is left exact.
For a finite index subgroup `Ind_K^G ≅ Coind_K^G`, so induction is also a *right*
adjoint of restriction (`Rep.resIndAdjunction`). This is where the book's finiteness
assumption on `[G : K]` enters; no flatness hypothesis is needed.
(Etingof Example 7.9.6(i)) -/
instance indFunctor_preservesFiniteLimits :
    PreservesFiniteLimits (Rep.indFunctor.{u, u, u} k S.subtype) :=
  letI : PreservesLimitsOfSize.{0, 0} (Rep.indFunctor.{u, u, u} k S.subtype) :=
    (Rep.resIndAdjunction.{u, u, u} k S).rightAdjoint_preservesLimits
  inferInstance

/-- **Etingof Example 7.9.6(i)**: `Ind_K^G` is exact — it preserves finite limits and
finite colimits — for a finite index subgroup `K ≤ G`. -/
theorem indFunctor_exact :
    PreservesFiniteLimits (Rep.indFunctor.{u, u, u} k S.subtype) ∧
      PreservesFiniteColimits (Rep.indFunctor.{u, u, u} k S.subtype) :=
  ⟨inferInstance, inferInstance⟩

end GroupRepresentations

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

/-- `Hom(ℤ/2ℤ, ℤ) = 0`: every `ℤ`-linear map `ℤ/2ℤ → ℤ` vanishes, because every
element of `ℤ/2ℤ` is 2-torsion while `ℤ` is torsion-free. This is the source of
the failure of right exactness in Etingof Example 7.9.6(ii). -/
theorem subsingleton_hom_zmod_int : Subsingleton (ZMod 2 →ₗ[ℤ] ℤ) := by
  refine ⟨fun φ ψ => ?_⟩
  suffices h : ∀ χ : ZMod 2 →ₗ[ℤ] ℤ, χ = 0 by rw [h φ, h ψ]
  intro χ
  ext x
  rw [LinearMap.zero_apply]
  have h2 : (2 : ℤ) • x = 0 := by
    have : ((2 : ℤ) : ZMod 2) = 0 := by decide
    rw [zsmul_eq_mul, this, zero_mul]
  have hmap := χ.map_smul (2 : ℤ) x
  rw [h2, map_zero, smul_eq_mul] at hmap
  omega

/-- `Hom(ℤ/2ℤ, -)` is not right exact. Concretely, for any surjection
`g : ℤ ↠ ℤ/2ℤ` (in particular the one from `0 → ℤ → ℤ → ℤ/2ℤ → 0`), the induced
post-composition map `Hom(ℤ/2ℤ, ℤ) → Hom(ℤ/2ℤ, ℤ/2ℤ)` is not surjective: the
identity of `ℤ/2ℤ` is not in its image, since the source `Hom(ℤ/2ℤ, ℤ)` is zero
while the target is not. (Etingof Example 7.9.6(ii), negative direction) -/
theorem hom_not_right_exact (g : ℤ →ₗ[ℤ] ZMod 2) :
    ¬ Function.Surjective (fun φ : ZMod 2 →ₗ[ℤ] ℤ => g.comp φ) := by
  haveI := subsingleton_hom_zmod_int
  intro hsurj
  obtain ⟨φ, hφ⟩ := hsurj LinearMap.id
  rw [Subsingleton.elim φ 0] at hφ
  simp only [LinearMap.comp_zero] at hφ
  have h1 : (0 : ZMod 2 →ₗ[ℤ] ZMod 2) (1 : ZMod 2)
      = (LinearMap.id : ZMod 2 →ₗ[ℤ] ZMod 2) (1 : ZMod 2) := by
    rw [hφ]
  simp only [LinearMap.zero_apply, LinearMap.id_coe, id_eq] at h1
  exact absurd h1.symm (by decide)

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

/-- `(1 : ℤ/2ℤ) ⊗ (1 : ℤ) ≠ 0` in `ℤ/2ℤ ⊗_ℤ ℤ`: under the canonical isomorphism
`ℤ/2ℤ ⊗_ℤ ℤ ≃ ℤ/2ℤ` it maps to `1 ≠ 0`. This is the nonzero element killed by the
tensored injection in `Etingof.tensor_not_left_exact`. -/
theorem tmul_one_one_ne_zero : ((1 : ZMod 2) ⊗ₜ[ℤ] (1 : ℤ)) ≠ 0 := by
  intro h
  have himg : (TensorProduct.rid ℤ (ZMod 2)) ((1 : ZMod 2) ⊗ₜ[ℤ] (1 : ℤ)) = 0 := by
    rw [h, map_zero]
  simp only [TensorProduct.rid_tmul, one_smul] at himg
  exact one_ne_zero himg

/-- `ℤ/2ℤ ⊗ -` is not left exact. Applying `lTensor (ℤ/2ℤ)` to the injection
`(· * 2) : ℤ ↪ ℤ` (the map in `0 → ℤ → ℤ → ℤ/2ℤ → 0`) yields a non-injective map:
it sends the nonzero element `1 ⊗ 1` to `1 ⊗ 2 = (2 • 1) ⊗ 1 = 0 ⊗ 1 = 0`.
(Etingof Example 7.9.6(iii), negative direction) -/
theorem tensor_not_left_exact :
    ¬ Function.Injective
      (LinearMap.lTensor (ZMod 2) (LinearMap.lsmul ℤ ℤ (2 : ℤ))) := by
  intro hinj
  apply tmul_one_one_ne_zero
  apply hinj
  rw [map_zero, LinearMap.lTensor_tmul, LinearMap.lsmul_apply,
    ← TensorProduct.smul_tmul]
  have : (2 : ℤ) • (1 : ZMod 2) = 0 := by
    rw [zsmul_eq_mul, show ((2 : ℤ) : ZMod 2) = 0 from by decide, zero_mul]
  rw [this, TensorProduct.zero_tmul]

end Etingof
