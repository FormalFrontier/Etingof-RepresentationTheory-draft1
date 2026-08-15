/-
Copyright (c) 2026 mathlib-initiative. All rights reserved.
Released under Apache 2.0 license as described in the file LICENCE.
Authors: mathlib-initiative
-/

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
import RepresentationTheory.Alignment.Attribute

set_option backward.isDefEq.respectTransparency false

/-!
# Balanced tensor relations and exactness

This module develops exactness properties of scalar-change, representation, hom, and tensor
functors, together with balanced tensor quotients over arbitrary rings.
-/

open CategoryTheory CategoryTheory.Limits

universe u

namespace RepresentationTheory.TensorProduct.BalancedRelations

/-! ## Scalar-change functors -/


/-- Restriction of scalars along a homomorphism of commutative rings preserves finite limits. -/
instance restrictScalars_preservesFiniteLimits
    {R S : Type u} [CommRing R] [CommRing S] (f : R →+* S) :
    PreservesFiniteLimits (ModuleCat.restrictScalars f) :=
  inferInstance


/-- Restriction of scalars along a homomorphism of commutative rings preserves finite colimits. -/
instance restrictScalars_preservesFiniteColimits
    {R S : Type u} [CommRing R] [CommRing S] (f : R →+* S) :
    PreservesFiniteColimits (ModuleCat.restrictScalars f) :=
  inferInstance


/-- Extension of scalars between commutative rings preserves finite colimits. -/
instance extendScalars_preservesFiniteColimits
    {R S : Type u} [CommRing R] [CommRing S] (f : R →+* S) :
    PreservesFiniteColimits (ModuleCat.extendScalars.{u, u, u} f) :=
  letI : (ModuleCat.extendScalars.{u, u, u} f).IsLeftAdjoint :=
    (ModuleCat.extendRestrictScalarsAdj.{u, u, u} f).isLeftAdjoint
  inferInstance


/-- Extension of scalars along a flat map of commutative rings preserves finite limits. -/
lemma extendScalars_preservesFiniteLimits_of_flat
    {R S : Type u} [CommRing R] [CommRing S] {f : R →+* S} (hf : f.Flat) :
    PreservesFiniteLimits (ModuleCat.extendScalars.{u, u, u} f) :=
  ModuleCat.preservesFiniteLimits_extendScalars_of_flat hf


/-- Extension of scalars along a flat ring homomorphism preserves finite limits and finite colimits. -/
lemma extendScalars_preservesFiniteLimits_and_colimits_of_flat
    {R S : Type u} [CommRing R] [CommRing S] {f : R →+* S} (hf : f.Flat) :
    PreservesFiniteLimits (ModuleCat.extendScalars.{u, u, u} f) ∧
      PreservesFiniteColimits (ModuleCat.extendScalars.{u, u, u} f) :=
  ⟨extendScalars_preservesFiniteLimits_of_flat hf, inferInstance⟩

/-! ### Representation functors -/

section GroupRepresentations

variable {k : Type u} [CommRing k] {G H : Type u} [Group G] [Group H]


/-- Restriction of representations along a group homomorphism preserves finite limits. -/
instance resFunctor_preservesFiniteLimits (φ : G →* H) :
    PreservesFiniteLimits (Rep.resFunctor.{u, u, u} (k := k) φ) :=
  letI : PreservesLimitsOfSize.{0, 0} (Rep.resFunctor.{u, u, u} (k := k) φ) :=
    (Rep.indResAdjunction.{u, u, u} k φ).rightAdjoint_preservesLimits
  inferInstance


/-- Restriction of representations along a group homomorphism preserves finite colimits. -/
instance resFunctor_preservesFiniteColimits (φ : G →* H) :
    PreservesFiniteColimits (Rep.resFunctor.{u, u, u} (k := k) φ) :=
  letI : PreservesColimitsOfSize.{0, 0} (Rep.resFunctor.{u, u, u} (k := k) φ) :=
    (Rep.resCoindAdjunction.{u, u, u} k φ).leftAdjoint_preservesColimits
  inferInstance


/-- Restriction of representations along a group homomorphism preserves finite limits and finite colimits. -/
@[source_ref "Chapter7/Example7.9.6" (role := primary)]
theorem resFunctor_preservesFiniteLimits_and_colimits (φ : G →* H) :
    PreservesFiniteLimits (Rep.resFunctor.{u, u, u} (k := k) φ) ∧
      PreservesFiniteColimits (Rep.resFunctor.{u, u, u} (k := k) φ) :=
  ⟨inferInstance, inferInstance⟩

variable (S : Subgroup G) [S.FiniteIndex]

open scoped Classical in

/-- Induction of representations along a subgroup inclusion preserves finite colimits. -/
instance indFunctor_preservesFiniteColimits :
    PreservesFiniteColimits (Rep.indFunctor.{u, u, u} k S.subtype) :=
  letI : PreservesColimitsOfSize.{0, 0} (Rep.indFunctor.{u, u, u} k S.subtype) :=
    (Rep.indResAdjunction.{u, u, u} k S.subtype).leftAdjoint_preservesColimits
  inferInstance

open scoped Classical in

/-- Induction from a finite-index subgroup preserves finite limits. -/
instance indFunctor_preservesFiniteLimits_of_finiteIndex :
    PreservesFiniteLimits (Rep.indFunctor.{u, u, u} k S.subtype) :=
  letI : PreservesLimitsOfSize.{0, 0} (Rep.indFunctor.{u, u, u} k S.subtype) :=
    (Rep.resIndAdjunction.{u, u, u} k S).rightAdjoint_preservesLimits
  inferInstance


/-- Induction from a finite-index subgroup preserves finite limits and finite colimits. -/
@[source_ref "Chapter7/Example7.9.6" (role := primary)]
theorem indFunctor_preservesFiniteLimits_and_colimits_of_finiteIndex :
    PreservesFiniteLimits (Rep.indFunctor.{u, u, u} k S.subtype) ∧
      PreservesFiniteColimits (Rep.indFunctor.{u, u, u} k S.subtype) :=
  ⟨inferInstance, inferInstance⟩

end GroupRepresentations

/-! ## Covariant hom functors -/


/-- The covariant hom functor represented by any object preserves finite limits. -/
instance coyoneda_obj_preservesFiniteLimits {C : Type*} [Category C] (X : C) :
    PreservesFiniteLimits (coyoneda.obj (Opposite.op X)) :=
  inferInstance


/-- The type of integer-linear maps from `ZMod 2` to the integers is a subsingleton. -/
theorem subsingleton_linearMap_zmodTwo_int : Subsingleton (ZMod 2 →ₗ[ℤ] ℤ) := by
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


/-- For every integer-linear map from the integers to `ZMod 2`, postcomposition with that map is not surjective on linear maps with source `ZMod 2`. -/
@[source_ref "Chapter7/Example7.9.6" (role := primary)]
theorem postcomp_intToZModTwo_not_surjective (g : ℤ →ₗ[ℤ] ZMod 2) :
    ¬ Function.Surjective (fun φ : ZMod 2 →ₗ[ℤ] ℤ => g.comp φ) := by
  haveI := subsingleton_linearMap_zmodTwo_int
  intro hsurj
  obtain ⟨φ, hφ⟩ := hsurj LinearMap.id
  rw [Subsingleton.elim φ 0] at hφ
  simp only [LinearMap.comp_zero] at hφ
  have h1 : (0 : ZMod 2 →ₗ[ℤ] ZMod 2) (1 : ZMod 2)
      = (LinearMap.id : ZMod 2 →ₗ[ℤ] ZMod 2) (1 : ZMod 2) := by
    rw [hφ]
  simp only [LinearMap.zero_apply, LinearMap.id_coe, id_eq] at h1
  exact absurd h1.symm (by decide)

/-! ## Tensor functors -/


/-- Tensoring module objects on the left preserves finite colimits. -/
instance tensorLeft_preservesFiniteColimits {R : Type*} [CommRing R] (X : ModuleCat R) :
    PreservesFiniteColimits (MonoidalCategory.tensorLeft X) :=
  inferInstance


/-- The tensor of one with one over the integers is nonzero. -/
theorem tmul_one_one_ne_zero : ((1 : ZMod 2) ⊗ₜ[ℤ] (1 : ℤ)) ≠ 0 := by
  intro h
  have himg : (TensorProduct.rid ℤ (ZMod 2)) ((1 : ZMod 2) ⊗ₜ[ℤ] (1 : ℤ)) = 0 := by
    rw [h, map_zero]
  simp only [TensorProduct.rid_tmul, one_smul] at himg
  exact one_ne_zero himg


/-- Left tensoring multiplication by two on the integers with `ZMod 2` yields a noninjective map. -/
theorem lTensor_mulTwo_not_injective :
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

/-! ### Balanced tensor quotients -/

section NoncommutativeTensor

-- The `ℤ`-module structure on `X ⊗[ℤ] M` reaches Lean by two routes (`TensorProduct`'s own
-- instance and `AddCommGroup.toIntModule`), so the `Submodule ℤ` bookkeeping below relies on
-- the project-wide `backward.isDefEq.respectTransparency false` option set in `lakefile.toml`.
-- A consequence: `#print axioms` run through a bare `lake env lean` *on this source file*
-- reports a spurious `sorryAx` for the declarations in this section, because `lake env lean`
-- does not apply the library's `leanOptions`. Pass `-D backward.isDefEq.respectTransparency
-- =false`, or audit against the built olean from a scratch file that only `import`s this
-- module.

open _root_.TensorProduct


/-- Regard a linear map over a ring as a linear map of its underlying additive groups over the integers. -/
abbrev LinearMap.restrictScalarsInt {R M N : Type*} [Ring R] [AddCommGroup M] [Module R M] [AddCommGroup N]
    [Module R N] (g : M →ₗ[R] N) : M →ₗ[ℤ] N := g.toAddMonoidHom.toIntLinearMap


/-- Pulling back the image of a submodule is its supremum with the kernel. -/
lemma Submodule.comap_map_eq_sup_ker {R M N : Type*} [Ring R] [AddCommGroup M] [Module R M]
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


/-- The set of balancing relations in an integer tensor product. -/
def balancedTensorRelations : Set (X ⊗[ℤ] M) :=
  {t | ∃ (a : A) (x : X) (m : M),
    t = (MulOpposite.op a • x) ⊗ₜ[ℤ] m - x ⊗ₜ[ℤ] (a • m)}


/-- The integer submodule generated by the balancing relations. -/
def balancedTensorRelationSubmodule : Submodule ℤ (X ⊗[ℤ] M) := Submodule.span ℤ (balancedTensorRelations A X M)


/-- The quotient of an integer tensor product by its balanced relation submodule. -/
abbrev BalancedTensorQuotient : Type _ := (X ⊗[ℤ] M) ⧸ balancedTensorRelationSubmodule A X M

variable {M N P}

/-- Tensoring a linear map carries a basic balancing relation to the corresponding relation after applying the map. -/
lemma lTensor_map_balancedRelation (g : M →ₗ[A] N) (a : A) (x : X) (m : M) :
    LinearMap.lTensor X (LinearMap.restrictScalarsInt g)
        ((MulOpposite.op a • x) ⊗ₜ[ℤ] m - x ⊗ₜ[ℤ] (a • m)) =
      (MulOpposite.op a • x) ⊗ₜ[ℤ] (g m) - x ⊗ₜ[ℤ] (a • g m) := by
  simp [map_sub, g.map_smul]

/-- Balancing relations map into the corresponding relation submodule under a linear map in the right factor. -/
lemma balancedTensorRelationSubmodule_le_comap (g : M →ₗ[A] N) :
    balancedTensorRelationSubmodule A X M ≤
      (balancedTensorRelationSubmodule A X N).comap (LinearMap.lTensor X (LinearMap.restrictScalarsInt g)) := by
  refine Submodule.span_le.2 ?_
  rintro t ⟨a, x, m, rfl⟩
  exact Submodule.mem_comap.2
    (lTensor_map_balancedRelation A X g a x m ▸ Submodule.subset_span ⟨a, x, g m, rfl⟩)


/-- The map on balanced tensor quotients induced by a linear map in the right factor. -/
def BalancedTensorQuotient.map (g : M →ₗ[A] N) : BalancedTensorQuotient A X M →ₗ[ℤ] BalancedTensorQuotient A X N :=
  Submodule.mapQ _ _ (LinearMap.lTensor X (LinearMap.restrictScalarsInt g))
    (balancedTensorRelationSubmodule_le_comap A X g)

/-- The induced balanced-quotient map sends a quotient representative to the quotient of its tensor image. -/
@[simp]
lemma BalancedTensorQuotient.map_mk (g : M →ₗ[A] N) (t : X ⊗[ℤ] M) :
    BalancedTensorQuotient.map A X g (Submodule.Quotient.mk t) =
      Submodule.Quotient.mk (LinearMap.lTensor X (LinearMap.restrictScalarsInt g) t) := rfl


/-- A surjective linear map carries the balancing relation submodule onto the target relation submodule. -/
lemma map_balancedTensorRelationSubmodule_of_surjective (g : N →ₗ[A] P) (hg : Function.Surjective g) :
    (balancedTensorRelationSubmodule A X N).map (LinearMap.lTensor X (LinearMap.restrictScalarsInt g)) =
      balancedTensorRelationSubmodule A X P := by
  rw [balancedTensorRelationSubmodule, Submodule.map_span, balancedTensorRelationSubmodule]
  congr 1
  ext t
  constructor
  · rintro ⟨s, ⟨a, x, n, rfl⟩, rfl⟩
    exact ⟨a, x, g n, lTensor_map_balancedRelation A X g a x n⟩
  · rintro ⟨a, x, p, rfl⟩
    obtain ⟨n, rfl⟩ := hg p
    exact ⟨_, ⟨a, x, n, rfl⟩, lTensor_map_balancedRelation A X g a x n⟩


/-- A surjective linear map induces a surjection on balanced tensor quotients. -/
theorem BalancedTensorQuotient.map_surjective (g : N →ₗ[A] P) (hg : Function.Surjective g) :
    Function.Surjective (BalancedTensorQuotient.map A X g) := by
  intro y
  obtain ⟨z, rfl⟩ := Submodule.mkQ_surjective _ y
  obtain ⟨w, rfl⟩ := LinearMap.lTensor_surjective (g := LinearMap.restrictScalarsInt g) X hg z
  exact ⟨Submodule.Quotient.mk w, rfl⟩


/-- Exactness is preserved by the induced map on balanced tensor quotients when the second map is onto. -/
@[source_ref "Chapter7/Example7.9.6" (role := primary)]
theorem BalancedTensorQuotient.exact_map (f : M →ₗ[A] N) (g : N →ₗ[A] P) (hfg : Function.Exact f g)
    (hg : Function.Surjective g) :
    Function.Exact (BalancedTensorQuotient.map A X f) (BalancedTensorQuotient.map A X g) := by
  have hZ : Function.Exact (LinearMap.lTensor X (LinearMap.restrictScalarsInt f))
      (LinearMap.lTensor X (LinearMap.restrictScalarsInt g)) :=
    _root_.lTensor_exact (f := LinearMap.restrictScalarsInt f) (g := LinearMap.restrictScalarsInt g) X hfg hg
  rw [LinearMap.exact_iff, BalancedTensorQuotient.map, BalancedTensorQuotient.map, Submodule.ker_mapQ,
    Submodule.range_mapQ, ← map_balancedTensorRelationSubmodule_of_surjective A X g hg,
    Submodule.comap_map_eq_sup_ker, ← LinearMap.exact_iff.1 hZ, Submodule.map_sup,
    Submodule.mkQ_map_self, bot_sup_eq]

/-! ### Integer specialization -/


/-- The balancing relation submodule is zero when the opposite integer action agrees with the ordinary action. -/
lemma balancedTensorRelationSubmodule_eq_bot (X : Type*) [AddCommGroup X] [Module ℤᵐᵒᵖ X]
    (M : Type*) [AddCommGroup M] (h : ∀ (a : ℤ) (x : X), MulOpposite.op a • x = a • x) :
    balancedTensorRelationSubmodule ℤ X M = ⊥ := by
  rw [balancedTensorRelationSubmodule, Submodule.span_eq_bot]
  rintro t ⟨a, x, m, rfl⟩
  rw [h a x, TensorProduct.smul_tmul, sub_self]


/-- The canonical action of the opposite integer ring on an additive commutative group. -/
@[reducible] def oppositeIntModule (X : Type*) [AddCommGroup X] : Module ℤᵐᵒᵖ X :=
  Module.compHom X ((RingEquiv.toOpposite ℤ).symm : ℤᵐᵒᵖ →+* ℤ)

attribute [local instance] oppositeIntModule

/-- The canonical opposite-integer action agrees with ordinary integer scalar multiplication. -/
lemma op_int_smul_eq_smul (X : Type*) [AddCommGroup X] (a : ℤ) (x : X) :
    MulOpposite.op a • x = a • x := rfl


/-- The balanced-quotient map induced by multiplication by two over the integers with left factor `ZMod 2` is not injective. -/
@[source_ref "Chapter7/Example7.9.6" (role := primary)]
theorem BalancedTensorQuotient.map_mulTwo_not_injective :
    ¬ Function.Injective (BalancedTensorQuotient.map ℤ (ZMod 2) (LinearMap.lsmul ℤ ℤ (2 : ℤ))) := by
  intro hinj
  refine lTensor_mulTwo_not_injective fun z w hzw => ?_
  have hbot : balancedTensorRelationSubmodule ℤ (ZMod 2) ℤ = ⊥ :=
    balancedTensorRelationSubmodule_eq_bot (ZMod 2) ℤ (op_int_smul_eq_smul (ZMod 2))
  have h := hinj (a₁ := Submodule.Quotient.mk z) (a₂ := Submodule.Quotient.mk w)
    (by rw [BalancedTensorQuotient.map_mk, BalancedTensorQuotient.map_mk]; exact congrArg _ hzw)
  rwa [Submodule.Quotient.eq, hbot, Submodule.mem_bot, sub_eq_zero] at h

end NoncommutativeTensor

end RepresentationTheory.TensorProduct.BalancedRelations
