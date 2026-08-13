/-
Copyright (c) 2026 FormalFrontier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: FormalFrontier
-/
import Mathlib.LinearAlgebra.TensorPower.Symmetric
import Mathlib.Algebra.Category.ModuleCat.Basic
import RepresentationTheory.Alignment.Attribute

/-! -/

open scoped TensorProduct

namespace RepresentationTheory.Mathlib.LinearAlgebra.SymmetricPower.Functor

namespace SymmetricPower

universe u v w x

variable {R ι : Type u} [CommSemiring R]
  {M : Type v} [AddCommMonoid M] [Module R M]
  {N : Type w} [AddCommMonoid N] [Module R N]
  {P : Type x} [AddCommMonoid P] [Module R P]

/-- Two linear maps from a symmetric power are equal when they agree on all quotient
constructors. -/
theorem linearMap_ext {Q : Type*} [AddCommMonoid Q] [Module R Q]
    {f g : Sym[R] ι M →ₗ[R] Q}
    (h : ∀ x : ⨂[R] (_ : ι), M,
      f (_root_.SymmetricPower.mk R ι M x) = g (_root_.SymmetricPower.mk R ι M x)) : f = g := by
  ext x
  exact AddCon.induction_on x h

/-- The linear map on symmetric powers induced by a linear map of modules. -/
noncomputable def map (f : M →ₗ[R] N) : Sym[R] ι M →ₗ[R] Sym[R] ι N :=
  let F : (⨂[R] (_ : ι), M) →+ Sym[R] ι N :=
    (AddCon.mk' _).comp (PiTensorProduct.map (fun _ : ι => f)).toAddMonoidHom
  { toFun := AddCon.lift _ F (fun x y h => Quotient.sound (by
      induction h with
      | of x y h => cases h with
        | perm e g =>
          simp only [LinearMap.toAddMonoidHom_coe, PiTensorProduct.map_tprod]
          exact AddConGen.Rel.of _ _ (_root_.SymmetricPower.Rel.perm e (fun i => f (g i)))
      | refl => exact AddCon.refl _ _
      | symm _ ih => exact AddCon.symm _ ih
      | trans _ _ ih₁ ih₂ => exact AddCon.trans _ ih₁ ih₂
      | add _ _ ih₁ ih₂ => simp only [map_add]; exact AddCon.add _ ih₁ ih₂))
    map_add' := fun x y => by
      refine AddCon.induction_on₂ x y (fun a b => ?_)
      change _root_.SymmetricPower.mk R ι N (PiTensorProduct.map (fun _ : ι => f) (a + b))
        = _root_.SymmetricPower.mk R ι N (PiTensorProduct.map (fun _ : ι => f) a)
          + _root_.SymmetricPower.mk R ι N (PiTensorProduct.map (fun _ : ι => f) b)
      rw [map_add, map_add]
    map_smul' := fun r x => by
      refine AddCon.induction_on x (fun a => ?_)
      change _root_.SymmetricPower.mk R ι N (PiTensorProduct.map (fun _ : ι => f) (r • a))
        = r • _root_.SymmetricPower.mk R ι N (PiTensorProduct.map (fun _ : ι => f) a)
      rw [map_smul, map_smul] }

/-- The induced map sends a quotient constructor to the constructor of its mapped tensor. -/
@[simp] theorem map_mk (f : M →ₗ[R] N) (x : ⨂[R] (_ : ι), M) :
    map (ι := ι) f (_root_.SymmetricPower.mk R ι M x) =
      _root_.SymmetricPower.mk R ι N (PiTensorProduct.map (fun _ : ι => f) x) :=
  rfl

/-- The induced map sends a symmetric tensor product to the tensor product of the mapped entries. -/
@[simp] theorem map_tprod (f : M →ₗ[R] N) (g : ι → M) :
    map (ι := ι) f (⨂ₛ[R] i, g i) = ⨂ₛ[R] i, f (g i) := by
  change map (ι := ι) f (_root_.SymmetricPower.mk R ι M (PiTensorProduct.tprod R g)) = _
  rw [map_mk, PiTensorProduct.map_tprod]
  rfl

/-- The map on a symmetric power induced by the identity linear map is the identity. -/
@[simp] theorem map_id : map (ι := ι) (LinearMap.id : M →ₗ[R] M) = LinearMap.id := by
  refine linearMap_ext fun x => ?_
  rw [map_mk, PiTensorProduct.map_id]
  rfl

/-- Mapping a composite linear map on symmetric powers is the composite of the induced maps. -/
theorem map_comp (g : N →ₗ[R] P) (f : M →ₗ[R] N) :
    map (ι := ι) (g ∘ₗ f) = map (ι := ι) g ∘ₗ map (ι := ι) f := by
  refine linearMap_ext fun x => ?_
  rw [map_mk, LinearMap.comp_apply, map_mk, map_mk,
    show (fun _ : ι => g ∘ₗ f) = fun i : ι => (fun _ : ι => g) i ∘ₗ (fun _ : ι => f) i from rfl,
    PiTensorProduct.map_comp]
  rfl

/-- The induced map of a composite agrees pointwise with the composite of the induced maps. -/
@[simp] theorem map_comp_apply (g : N →ₗ[R] P) (f : M →ₗ[R] N) (x : Sym[R] ι M) :
    map (ι := ι) (g ∘ₗ f) x = map (ι := ι) g (map (ι := ι) f x) := by
  rw [map_comp]; rfl

end SymmetricPower

namespace SymmetricPower

open CategoryTheory

universe u v

/-- A type-indexed family of endofunctors on modules over a commutative ring. -/
noncomputable def moduleEndofunctorOfType (R : Type u) [CommRing R] (ι : Type u) :
    ModuleCat.{max u v} R ⥤ ModuleCat.{max u v} R where
  obj M := ModuleCat.of R (Sym[R] ι M)
  map f := ModuleCat.ofHom (SymmetricPower.map (ι := ι) f.hom)
  map_id M := by
    apply ModuleCat.hom_ext
    simp only [ModuleCat.hom_ofHom, ModuleCat.hom_id]
    exact SymmetricPower.map_id
  map_comp f g := by
    apply ModuleCat.hom_ext
    simp only [ModuleCat.hom_ofHom, ModuleCat.hom_comp]
    exact SymmetricPower.map_comp _ _

/-- A natural-number-indexed family of endofunctors on modules over a commutative ring. -/
@[source_ref "Chapter7/Example7.2.2" (role := primary)]
noncomputable abbrev moduleEndofunctorOfNat (R : Type) [CommRing R] (n : ℕ) :
    ModuleCat.{v} R ⥤ ModuleCat.{v} R :=
  moduleEndofunctorOfType R (Fin n)

end SymmetricPower

end RepresentationTheory.Mathlib.LinearAlgebra.SymmetricPower.Functor
