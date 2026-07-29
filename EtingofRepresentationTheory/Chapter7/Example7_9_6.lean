import Mathlib.CategoryTheory.Limits.Yoneda
import Mathlib.CategoryTheory.Limits.Preserves.Finite
import Mathlib.Algebra.Category.ModuleCat.Monoidal.Closed
import Mathlib.Algebra.Category.ModuleCat.ChangeOfRingsExact
import Mathlib.Algebra.Category.ModuleCat.Descent
import Mathlib.LinearAlgebra.TensorProduct.Basic
import Mathlib.LinearAlgebra.TensorProduct.RightExactness
import Mathlib.Data.ZMod.Basic
import Mathlib.RepresentationTheory.FiniteIndex
import Mathlib.RepresentationTheory.Rep.Res

set_option backward.isDefEq.respectTransparency false

/-!
# Example 7.9.6: Exactness Properties of Standard Functors

(i) The functors Ind_K^G, Res_K^G are exact.
(ii) The functor Hom(X, ?) is left exact, but not necessarily right exact.
     Counterexample: 0 → ℤ → ℤ → ℤ/2ℤ → 0 with Hom(ℤ/2ℤ, ?).
(iii) The functor X ⊗_A - for a right A-module X is right exact but not
      necessarily left exact. Counterexample: tensor the above sequence by ℤ/2ℤ.

## Mathlib correspondence

### Part (i)

The book's functors are `Res_K^G : Rep k G ⥤ Rep k K` and `Ind_K^G : Rep k K ⥤ Rep k G`.
They are formalized here as the actual representation-theoretic functors
`Rep.resFunctor K.subtype` and `Rep.indFunctor k K.subtype` (the ones used in
`Chapter7/Example7_9_2.lean`), and their exactness is `Etingof.resFunctor_exact` and
`Etingof.indFunctor_exact`:

* restriction along an arbitrary group homomorphism is both a right adjoint (of
  induction, `Rep.indResAdjunction`) and a left adjoint (of coinduction,
  `Rep.resCoindAdjunction`), hence exact with no hypothesis;
* for a *finite index* subgroup induction and coinduction agree
  (`Rep.indCoindNatIso`), so induction is both a left adjoint (`Rep.indResAdjunction`)
  and a right adjoint (`Rep.resIndAdjunction`) of restriction, hence exact.

Neither statement needs a flatness hypothesis supplied from outside.

Underneath, these functors are change-of-rings functors along the inclusion of group
algebras `f : k[K] → k[G]`: `Res_K^G` is `ModuleCat.restrictScalars f` and `Ind_K^G` is
`ModuleCat.extendScalars f`, the functor `k[G] ⊗_{k[K]} -`. That algebraic shadow is
recorded first, with `Etingof.extendScalars_exact_of_flat` carrying the flatness
hypothesis that holds for `k[K] → k[G]` because `k[G]` is `k[K]`-free of rank `[G : K]`.

### Part (ii)

Left exactness of `Hom` is available via the covariant Yoneda functor
`coyoneda.obj (op X)`, which preserves all limits. The negative direction
(failure of right exactness) is formalized concretely in
`Etingof.hom_not_right_exact`: applying `Hom(ℤ/2ℤ, -)` to the surjection
`ℤ ↠ ℤ/2ℤ` from the sequence above does not give a surjection, because
`Hom(ℤ/2ℤ, ℤ) = 0` (`Etingof.subsingleton_hom_zmod_int`) while
`Hom(ℤ/2ℤ, ℤ/2ℤ) ≠ 0`.

### Part (iii)

Mathlib's monoidal closed structure on `ModuleCat` is defined over a commutative ring, so
the categorical statement `Etingof.tensor_right_exact` is restricted to `[CommRing R]`.
The book states part (iii) for a right module `X` over an arbitrary, possibly
noncommutative, ring `A`. Mathlib's `TensorProduct` also requires a commutative base ring
(and `Mathlib/LinearAlgebra/TensorProduct/RightExactness.lean` lists the noncommutative
case as an explicit TODO), so the balanced tensor product `X ⊗_A M` is constructed here as
`Etingof.BalancedTensor`: the quotient of the abelian group `X ⊗_ℤ M` by the balancing
relations `x·a ⊗ m - x ⊗ a·m`. It is functorial in `M` (`Etingof.balancedLTensor`) and
right exact over an arbitrary ring, by `Etingof.balancedLTensor_exact` together with
`Etingof.balancedLTensor_surjective`.

The negative direction (failure of left exactness) is formalized concretely in
`Etingof.tensor_not_left_exact`: applying `ℤ/2ℤ ⊗ -` to the injection `(· * 2) : ℤ ↪ ℤ`
gives a non-injective map, because it kills the nonzero element `1 ⊗ 1`
(`Etingof.tmul_one_one_ne_zero`). `Etingof.balancedLTensor_not_left_exact` transports that
same counterexample to the general construction, instantiated at `A = ℤ`.
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
`Hom(ℤ/2ℤ, -)` to `0 → ℤ → ℤ → ℤ/2ℤ → 0`; that negative direction is
`Etingof.hom_not_right_exact` below. -/
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
`A`; that generality is not expressible through Mathlib's `ModuleCat` monoidal API,
so it is handled separately by the balanced tensor product `Etingof.BalancedTensor`
and `Etingof.balancedLTensor_exact` below. The book's negative direction (the tensor
functor need not be left exact, witnessed by `ℤ/2ℤ ⊗ -` on `0 → ℤ → ℤ → ℤ/2ℤ → 0`)
is `Etingof.tensor_not_left_exact`, transported to the balanced tensor product by
`Etingof.balancedLTensor_not_left_exact`. -/
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

/-! ### Part (iii) over an arbitrary ring

Mathlib's `TensorProduct R M N` requires a commutative base ring `R`, and
`Mathlib/LinearAlgebra/TensorProduct/RightExactness.lean` lists the noncommutative case
as an explicit TODO. The book states part (iii) for a right module `X` over an arbitrary,
possibly noncommutative, ring `A`, so we construct that tensor product here.

For a right `A`-module `X` (encoded, as usual, as a module over `Aᵐᵒᵖ`) and a left
`A`-module `M`, the balanced tensor product `X ⊗_A M` is the quotient of the abelian
group `X ⊗_ℤ M` by the subgroup generated by the balancing relations
`x·a ⊗ m - x ⊗ a·m`. That is `Etingof.BalancedTensor A X M`, and `Etingof.balancedLTensor`
makes it a functor in `M`.

Right exactness (`Etingof.balancedLTensor_exact`, `Etingof.balancedLTensor_surjective`)
is deduced from Mathlib's right exactness over `ℤ` by comparing the balancing submodules:
a surjection `g : N ↠ P` of left `A`-modules carries the balancing submodule of `X ⊗_ℤ N`
*onto* that of `X ⊗_ℤ P` (`Etingof.map_balancingSubmodule`), which is exactly what is
needed to descend exactness to the quotients. -/

section NoncommutativeTensor

-- The `ℤ`-module structure on `X ⊗[ℤ] M` reaches Lean by two routes (`TensorProduct`'s own
-- instance and `AddCommGroup.toIntModule`), so the `Submodule ℤ` bookkeeping below relies on
-- the project-wide `backward.isDefEq.respectTransparency false` option set in `lakefile.toml`.
-- A consequence: `#print axioms` run through a bare `lake env lean` *on this source file*
-- reports a spurious `sorryAx` for the declarations in this section, because `lake env lean`
-- does not apply the library's `leanOptions`. Pass `-D backward.isDefEq.respectTransparency
-- =false`, or audit against the built olean from a scratch file that only `import`s this
-- module.

open TensorProduct

/-- An `A`-linear map between `A`-modules, viewed as a `ℤ`-linear map of the underlying
abelian groups, so that it can be tensored over `ℤ`. -/
abbrev intLinearMap {R M N : Type*} [Ring R] [AddCommGroup M] [Module R M] [AddCommGroup N]
    [Module R N] (g : M →ₗ[R] N) : M →ₗ[ℤ] N := g.toAddMonoidHom.toIntLinearMap

/-- The preimage of the image of a submodule is the submodule joined with the kernel. -/
lemma comap_map_eq_sup_ker {R M N : Type*} [Ring R] [AddCommGroup M] [Module R M]
    [AddCommGroup N] [Module R N] (f : M →ₗ[R] N) (p : Submodule R M) :
    (p.map f).comap f = p ⊔ LinearMap.ker f := by
  refine le_antisymm (fun x hx => ?_)
    (sup_le (fun x hx => Submodule.mem_comap.2 (Submodule.mem_map_of_mem hx))
      (fun x hx => Submodule.mem_comap.2 (by simp [LinearMap.mem_ker.1 hx])))
  obtain ⟨y, hy, hxy⟩ := Submodule.mem_comap.1 hx
  have hker : x - y ∈ LinearMap.ker f := by simp [LinearMap.mem_ker, hxy]
  simpa using Submodule.add_mem _ (Submodule.mem_sup_left hy) (Submodule.mem_sup_right hker)

variable (A : Type*) [Ring A] (X : Type*) [AddCommGroup X] [Module Aᵐᵒᵖ X]
variable (M : Type*) [AddCommGroup M] [Module A M]
variable (N : Type*) [AddCommGroup N] [Module A N]
variable (P : Type*) [AddCommGroup P] [Module A P]

/-- The set of balancing relations `x·a ⊗ m - x ⊗ a·m` inside `X ⊗_ℤ M`, for `X` a right
`A`-module and `M` a left `A`-module over an arbitrary ring `A`. -/
def balancingRel : Set (X ⊗[ℤ] M) :=
  {t | ∃ (a : A) (x : X) (m : M),
    t = (MulOpposite.op a • x) ⊗ₜ[ℤ] m - x ⊗ₜ[ℤ] (a • m)}

/-- The subgroup of `X ⊗_ℤ M` generated by the balancing relations `x·a ⊗ m - x ⊗ a·m`. -/
def balancingSubmodule : Submodule ℤ (X ⊗[ℤ] M) := Submodule.span ℤ (balancingRel A X M)

/-- The tensor product `X ⊗_A M` of a right `A`-module `X` and a left `A`-module `M` over
an arbitrary, possibly noncommutative, ring `A`: the quotient of the abelian group
`X ⊗_ℤ M` by the balancing relations `x·a ⊗ m - x ⊗ a·m`. (Etingof Example 7.9.6(iii)) -/
abbrev BalancedTensor : Type _ := (X ⊗[ℤ] M) ⧸ balancingSubmodule A X M

variable {M N P}

lemma lTensor_balancingRel (g : M →ₗ[A] N) (a : A) (x : X) (m : M) :
    LinearMap.lTensor X (intLinearMap g)
        ((MulOpposite.op a • x) ⊗ₜ[ℤ] m - x ⊗ₜ[ℤ] (a • m)) =
      (MulOpposite.op a • x) ⊗ₜ[ℤ] (g m) - x ⊗ₜ[ℤ] (a • g m) := by
  simp [map_sub, g.map_smul]

lemma balancingSubmodule_le_comap (g : M →ₗ[A] N) :
    balancingSubmodule A X M ≤
      (balancingSubmodule A X N).comap (LinearMap.lTensor X (intLinearMap g)) := by
  refine Submodule.span_le.2 ?_
  rintro t ⟨a, x, m, rfl⟩
  exact Submodule.mem_comap.2
    (lTensor_balancingRel A X g a x m ▸ Submodule.subset_span ⟨a, x, g m, rfl⟩)

/-- The map `X ⊗_A M → X ⊗_A N` induced by an `A`-linear map `M → N`: this is the
functoriality of `X ⊗_A -` over an arbitrary ring `A`. -/
def balancedLTensor (g : M →ₗ[A] N) : BalancedTensor A X M →ₗ[ℤ] BalancedTensor A X N :=
  Submodule.mapQ _ _ (LinearMap.lTensor X (intLinearMap g))
    (balancingSubmodule_le_comap A X g)

@[simp]
lemma balancedLTensor_mk (g : M →ₗ[A] N) (t : X ⊗[ℤ] M) :
    balancedLTensor A X g (Submodule.Quotient.mk t) =
      Submodule.Quotient.mk (LinearMap.lTensor X (intLinearMap g) t) := rfl

/-- A surjection `g : N ↠ P` of left `A`-modules carries the balancing submodule of
`X ⊗_ℤ N` *onto* the balancing submodule of `X ⊗_ℤ P`. This is the one place where
surjectivity of `g` is used, and it is what lets right exactness over `ℤ` descend to the
balanced quotients. -/
lemma map_balancingSubmodule (g : N →ₗ[A] P) (hg : Function.Surjective g) :
    (balancingSubmodule A X N).map (LinearMap.lTensor X (intLinearMap g)) =
      balancingSubmodule A X P := by
  rw [balancingSubmodule, Submodule.map_span, balancingSubmodule]
  congr 1
  ext t
  constructor
  · rintro ⟨s, ⟨a, x, n, rfl⟩, rfl⟩
    exact ⟨a, x, g n, lTensor_balancingRel A X g a x n⟩
  · rintro ⟨a, x, p, rfl⟩
    obtain ⟨n, rfl⟩ := hg p
    exact ⟨_, ⟨a, x, n, rfl⟩, lTensor_balancingRel A X g a x n⟩

/-- **Etingof Example 7.9.6(iii), positive direction, surjectivity half**: for a right
`A`-module `X` over an arbitrary ring `A`, the functor `X ⊗_A -` preserves surjections. -/
theorem balancedLTensor_surjective (g : N →ₗ[A] P) (hg : Function.Surjective g) :
    Function.Surjective (balancedLTensor A X g) := by
  intro y
  obtain ⟨z, rfl⟩ := Submodule.mkQ_surjective _ y
  obtain ⟨w, rfl⟩ := LinearMap.lTensor_surjective (g := intLinearMap g) X hg z
  exact ⟨Submodule.Quotient.mk w, rfl⟩

/-- **Etingof Example 7.9.6(iii), positive direction**: for a right `A`-module `X` over an
arbitrary, possibly noncommutative, ring `A`, the functor `X ⊗_A -` is right exact. Given
an exact sequence `M → N → P → 0` of left `A`-modules, the sequence
`X ⊗_A M → X ⊗_A N → X ⊗_A P → 0` is exact.

Together with `balancedLTensor_surjective` (exactness at `X ⊗_A P`) this is the book's
statement, without any commutativity hypothesis on `A`. -/
theorem balancedLTensor_exact (f : M →ₗ[A] N) (g : N →ₗ[A] P) (hfg : Function.Exact f g)
    (hg : Function.Surjective g) :
    Function.Exact (balancedLTensor A X f) (balancedLTensor A X g) := by
  have hZ : Function.Exact (LinearMap.lTensor X (intLinearMap f))
      (LinearMap.lTensor X (intLinearMap g)) :=
    _root_.lTensor_exact (f := intLinearMap f) (g := intLinearMap g) X hfg hg
  rw [LinearMap.exact_iff, balancedLTensor, balancedLTensor, Submodule.ker_mapQ,
    Submodule.range_mapQ, ← map_balancingSubmodule A X g hg,
    comap_map_eq_sup_ker, ← LinearMap.exact_iff.1 hZ, Submodule.map_sup,
    Submodule.mkQ_map_self, bot_sup_eq]

/-! Over `A = ℤ` the balancing relations are automatic, so `X ⊗_ℤ M` in the sense above is
the ordinary tensor product. This is what connects the general construction to the concrete
`ℤ/2ℤ` counterexample `Etingof.tensor_not_left_exact`: the failure of left exactness there
is a failure of left exactness of `BalancedTensor` as well. -/

/-- Over the commutative ring `ℤ` all balancing relations are trivial, provided the right
action of `ℤᵐᵒᵖ` is the canonical `ℤ`-action. So in that case `BalancedTensor ℤ X M` is the
ordinary tensor product `X ⊗_ℤ M`, up to the quotient by `⊥`. -/
lemma balancingSubmodule_int (X : Type*) [AddCommGroup X] [Module ℤᵐᵒᵖ X]
    (M : Type*) [AddCommGroup M] (h : ∀ (a : ℤ) (x : X), MulOpposite.op a • x = a • x) :
    balancingSubmodule ℤ X M = ⊥ := by
  rw [balancingSubmodule, Submodule.span_eq_bot]
  rintro t ⟨a, x, m, rfl⟩
  rw [h a x, TensorProduct.smul_tmul, sub_self]

/-- Any abelian group is a right `ℤ`-module, through the ring isomorphism `ℤᵐᵒᵖ ≃+* ℤ`.
This is used only to instantiate `BalancedTensor` at `A = ℤ` in
`balancedLTensor_not_left_exact`, so it is deliberately not a global instance: a blanket
`Module ℤᵐᵒᵖ` would collide with the `Semiring.toModule` structure on `ℤᵐᵒᵖ` itself. -/
@[reducible] def intOpModule (X : Type*) [AddCommGroup X] : Module ℤᵐᵒᵖ X :=
  Module.compHom X ((RingEquiv.toOpposite ℤ).symm : ℤᵐᵒᵖ →+* ℤ)

attribute [local instance] intOpModule

lemma op_smul_int (X : Type*) [AddCommGroup X] (a : ℤ) (x : X) :
    MulOpposite.op a • x = a • x := rfl

/-- **Etingof Example 7.9.6(iii), negative direction, for the balanced tensor product**:
`X ⊗_A -` need not be left exact. Instantiating the general construction at `A = ℤ`,
`X = ℤ/2ℤ` and the injection `(· * 2) : ℤ ↪ ℤ` of `0 → ℤ → ℤ → ℤ/2ℤ → 0` gives a
non-injective map, exactly as in `Etingof.tensor_not_left_exact`. -/
theorem balancedLTensor_not_left_exact :
    ¬ Function.Injective (balancedLTensor ℤ (ZMod 2) (LinearMap.lsmul ℤ ℤ (2 : ℤ))) := by
  intro hinj
  refine tensor_not_left_exact fun z w hzw => ?_
  have hbot : balancingSubmodule ℤ (ZMod 2) ℤ = ⊥ :=
    balancingSubmodule_int (ZMod 2) ℤ (op_smul_int (ZMod 2))
  have h := hinj (a₁ := Submodule.Quotient.mk z) (a₂ := Submodule.Quotient.mk w)
    (by rw [balancedLTensor_mk, balancedLTensor_mk]; exact congrArg _ hzw)
  rwa [Submodule.Quotient.eq, hbot, Submodule.mem_bot, sub_eq_zero] at h

end NoncommutativeTensor

end Etingof
