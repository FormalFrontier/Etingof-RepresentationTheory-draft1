import Mathlib.RepresentationTheory.Induced
import Mathlib.RepresentationTheory.Rep.Res
import Mathlib.CategoryTheory.Linear.Yoneda
import Mathlib.CategoryTheory.Adjunction.Additive
import Mathlib.Algebra.Category.ModuleCat.ChangeOfRings
import Mathlib.CategoryTheory.Linear.LinearFunctor

/-!
# Example 7.9.2: Additive and k-linear Functors in Representation Theory

> The functors `Ind_K^G`, `Res_K^G`, `Hom_G(V, ?)` in the theory of group
> representations over a field `k` are additive and `k`-linear.

This file records the three statements of the example against the *actual*
group-representation functors on `Rep k G`, not merely the underlying
change-of-rings functor on `ModuleCat`:

* **Restriction** `Res_K^G` is `Rep.resFunctor φ : Rep k G ⥤ Rep k H` for a group
  homomorphism `φ : G →* H` (`Res_K^G` is the case of the inclusion `K ↪ G`).
  Additivity and `k`-linearity are already `Mathlib` instances; we name them here.
* **Induction** `Ind_K^G` is `Rep.indFunctor k φ : Rep k G ⥤ Rep k H`. It is the
  left adjoint of restriction (`Rep.indResAdjunction`), and additivity/linearity
  transfer along the adjunction from restriction. The transfer of additivity is
  `Mathlib`'s `Adjunction.left_adjoint_additive`; the linear companion
  `left_adjoint_linear` is proved below.
* **`Hom_G(V, ?)`** is the covariant hom-functor `Rep k G ⥤ ModuleCat k`,
  i.e. `(linearCoyoneda k (Rep k G)).obj (op V)`. Additivity is a `Mathlib`
  instance; `k`-linearity is proved below.

The `ModuleCat.restrictScalars` instances at the end record the underlying
algebraic change-of-rings statement that the representation-theoretic
restriction is built on.
-/

open CategoryTheory Opposite

namespace Etingof

/-! ## A linear companion to `Adjunction.left_adjoint_additive` -/

/-- If `adj : F ⊣ G` is an adjunction between `R`-linear categories and the right
adjoint `G` is additive and `R`-linear, then the left adjoint `F` is `R`-linear.
This is the `Functor.Linear` companion of
`CategoryTheory.Adjunction.left_adjoint_additive`. -/
lemma left_adjoint_linear {C D : Type*} [Category C] [Category D] [Preadditive C]
    [Preadditive D] (R : Type*) [Semiring R] [Linear R C] [Linear R D]
    {F : C ⥤ D} {G : D ⥤ C} (adj : F ⊣ G) [G.Additive] [G.Linear R] : F.Linear R where
  map_smul {X Y} f r := (adj.homEquiv X (F.obj Y)).injective <| by
    simp only [Adjunction.homEquiv_unit, Functor.map_smul, Linear.comp_smul,
      ← Functor.comp_map, ← adj.unit.naturality, Functor.id_map, Linear.smul_comp]

/-! ## The three functors of Example 7.9.2 -/

section GroupRepresentations

universe u

variable {k G H : Type u} [Field k] [Group G] [Group H] (φ : G →* H)

/-- `Res_K^G` is additive (Etingof Example 7.9.2): the restriction functor
`Rep.resFunctor φ : Rep k H ⥤ Rep k G` along a group homomorphism is additive. -/
theorem resFunctor_additive : (Rep.resFunctor (k := k) φ).Additive := inferInstance

/-- `Res_K^G` is `k`-linear (Etingof Example 7.9.2): the restriction functor
`Rep.resFunctor φ : Rep k H ⥤ Rep k G` along a group homomorphism is `k`-linear. -/
theorem resFunctor_linear : (Rep.resFunctor (k := k) φ).Linear k := inferInstance

/-- `Ind_K^G` is additive (Etingof Example 7.9.2): the induction functor
`Rep.indFunctor k φ : Rep k G ⥤ Rep k H` is additive, since it is left adjoint to
the (additive) restriction functor. -/
theorem indFunctor_additive : (Rep.indFunctor.{u} k φ).Additive :=
  (Rep.indResAdjunction k φ).left_adjoint_additive

/-- `Ind_K^G` is `k`-linear (Etingof Example 7.9.2): the induction functor
`Rep.indFunctor k φ : Rep k G ⥤ Rep k H` is `k`-linear, since it is left adjoint
to the (`k`-linear) restriction functor. -/
theorem indFunctor_linear : (Rep.indFunctor.{u} k φ).Linear k :=
  Etingof.left_adjoint_linear k (Rep.indResAdjunction k φ)

variable (V : Rep k G)

/-- `Hom_G(V, ?)` is additive (Etingof Example 7.9.2): the covariant hom-functor
`(linearCoyoneda k (Rep k G)).obj (op V) : Rep k G ⥤ ModuleCat k` is additive. -/
theorem homGFunctor_additive : ((linearCoyoneda k (Rep k G)).obj (op V)).Additive :=
  inferInstance

/-- `Hom_G(V, ?)` is `k`-linear (Etingof Example 7.9.2): the covariant hom-functor
`(linearCoyoneda k (Rep k G)).obj (op V) : Rep k G ⥤ ModuleCat k` is `k`-linear. -/
theorem homGFunctor_linear : ((linearCoyoneda k (Rep k G)).obj (op V)).Linear k where
  map_smul {X Y} f r := by
    ext g
    exact Linear.comp_smul V X Y g r f

end GroupRepresentations

/-! ## Underlying change-of-rings statement

The representation-theoretic restriction `Rep.resFunctor` is built on the algebraic
restriction of scalars `ModuleCat.restrictScalars`. These instances record that the
underlying change-of-rings functor is additive and linear. -/

open scoped ModuleCat.Algebra

/-- The restriction of scalars functor along a ring homomorphism is additive.
This underlies the fact that `Res_K^G` is additive (Etingof Example 7.9.2). -/
instance restrictScalars_additive
    {R S : Type*} [Ring R] [Ring S] (f : R →+* S) :
    Functor.Additive (ModuleCat.restrictScalars f) :=
  inferInstance

/-- The restriction of scalars functor along an algebra homomorphism is linear.
This underlies the fact that `Res_K^G` is `k`-linear (Etingof Example 7.9.2). -/
instance restrictScalars_linear
    {R₀ R S : Type*} [CommSemiring R₀] [Ring R] [Ring S]
    [Algebra R₀ R] [Algebra R₀ S] (f : R →ₐ[R₀] S) :
    Functor.Linear R₀ (ModuleCat.restrictScalars f.toRingHom) :=
  inferInstance

end Etingof
