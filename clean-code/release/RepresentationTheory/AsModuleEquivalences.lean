/-
Copyright (c) 2026 FormalFrontier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: FormalFrontier
-/
import Mathlib

/-!
# Equivalences for modules associated to representations

This module gives direct-sum, equivariant-map, and tensor-product equivalences for modules
associated to representations.
-/

open scoped TensorProduct DirectSum

namespace RepresentationTheory.AsModuleEquivalences

section DirectSumAsModule

variable {k G : Type*} [CommSemiring k] [Monoid G]
variable {ι : Type*} {V : ι → Type*}
variable [(i : ι) → AddCommMonoid (V i)] [(i : ι) → Module k (V i)]

/-- Computes the action of a monoid-algebra singleton on a direct sum of associated modules. -/
theorem single_smul_directSumAsModule
    (ρs : (i : ι) → Representation k G (V i)) (g : G) (t : k)
    (y : DirectSum ι (fun i => Representation.asModule (ρs i))) :
    MonoidAlgebra.single g t • y = t • DirectSum.lmap (fun i => ρs i g) y := by
  refine DirectSum.ext (β := fun i => Representation.asModule (ρs i)) fun i => ?_
  rw [DirectSum.smul_apply, Representation.single_smul]
  rfl

/-- Identifies the module underlying a direct-sum representation with the direct sum of the underlying modules. -/
noncomputable def directSumAsModuleEquiv
    (ρs : (i : ι) → Representation k G (V i)) :
    Representation.asModule (Representation.directSum ρs) ≃ₗ[MonoidAlgebra k G]
      DirectSum ι (fun i => Representation.asModule (ρs i)) where
  toFun x := x
  invFun x := x
  map_add' _ _ := rfl
  left_inv _ := rfl
  right_inv _ := rfl
  map_smul' r x := by
    simp only [RingHom.id_apply]
    induction r using MonoidAlgebra.induction_linear with
    | zero => simp only [zero_smul] <;> rfl
    | add a b ha hb => simp only [add_smul, ha, hb] <;> rfl
    | single g t =>
      rw [single_smul_directSumAsModule, Representation.single_smul,
        Representation.directSum_apply]
      rfl

end DirectSumAsModule

section Intertwiner

variable {k G : Type*} [CommSemiring k] [Monoid G]
variable {V W : Type*} [AddCommMonoid V] [Module k V] [AddCommMonoid W] [Module k W]

/-- Turns an equivariant linear map into a map of the associated monoid-algebra modules. -/
def linearMapAsModule {ρ : Representation k G V} {σ : Representation k G W}
    (f : V →ₗ[k] W) (hf : ∀ (g : G) (x : V), f (ρ g x) = σ g (f x)) :
    Representation.asModule ρ →ₗ[MonoidAlgebra k G] Representation.asModule σ where
  toFun := f
  map_add' := map_add f
  map_smul' r x := by
    simp only [RingHom.id_apply]
    induction r using MonoidAlgebra.induction_linear with
    | zero => simp only [zero_smul]; exact map_zero f
    | add a b ha hb =>
      rw [add_smul, add_smul,
        show f (a • x + b • x) = f (a • x) + f (b • x) from map_add f _ _, ha, hb] <;> rfl
    | single g t =>
      rw [Representation.single_smul, Representation.single_smul, map_smul]
      simp only [Representation.asModuleEquiv]
      congr 1
      exact hf g _

/-- The induced module map evaluates as the given equivariant linear map. -/
@[simp] theorem linearMapAsModule_apply {ρ : Representation k G V}
    {σ : Representation k G W} (f : V →ₗ[k] W)
    (hf : ∀ (g : G) (x : V), f (ρ g x) = σ g (f x)) (x : Representation.asModule ρ) :
    linearMapAsModule f hf x = f x := rfl

/-- Turns an equivariant linear equivalence into an equivalence of the associated monoid-algebra modules. -/
def linearEquivAsModule {ρ : Representation k G V} {σ : Representation k G W}
    (f : V ≃ₗ[k] W) (hf : ∀ (g : G) (x : V), f (ρ g x) = σ g (f x)) :
    Representation.asModule ρ ≃ₗ[MonoidAlgebra k G] Representation.asModule σ where
  toFun := f
  invFun := f.symm
  map_add' := map_add f
  left_inv := f.left_inv
  right_inv := f.right_inv
  map_smul' r x := by
    simp only [RingHom.id_apply]
    induction r using MonoidAlgebra.induction_linear with
    | zero => simp only [zero_smul]; exact map_zero f
    | add a b ha hb =>
      rw [add_smul, add_smul,
        show f (a • x + b • x) = f (a • x) + f (b • x) from map_add f _ _, ha, hb] <;> rfl
    | single g t =>
      rw [Representation.single_smul, Representation.single_smul, map_smul]
      simp only [Representation.asModuleEquiv]
      congr 1
      exact hf g _

/-- The module equivalence induced by an equivariant linear equivalence acts as the original map. -/
@[simp] theorem linearEquivAsModule_apply {ρ : Representation k G V}
    {σ : Representation k G W} (f : V ≃ₗ[k] W)
    (hf : ∀ (g : G) (x : V), f (ρ g x) = σ g (f x)) (x : Representation.asModule ρ) :
    linearEquivAsModule f hf x = f x := rfl

end Intertwiner

section TrivialTprodSplit

open scoped TensorProduct
open TensorProduct

variable {k G S W : Type*} [CommRing k] [Monoid G]
variable [AddCommGroup S] [Module k S] [AddCommGroup W] [Module k W]
variable {β : Type*} [Fintype β] [DecidableEq β]

/-- Provides the basis-indexed linear equivalence from a tensor product to a direct sum. -/
noncomputable def tensorProductToDirectSum (b : Module.Basis β k S) :
    S ⊗[k] W ≃ₗ[k] DirectSum β (fun _ => W) :=
  TensorProduct.congr b.repr (LinearEquiv.refl k W) ≪≫ₗ
    TensorProduct.finsuppScalarLeft k W β ≪≫ₗ
      Finsupp.linearEquivFunOnFinite k W β ≪≫ₗ
        (DirectSum.linearEquivFunOnFintype k β (fun _ => W)).symm

/-- Describes the direct-sum coordinates of a pure tensor using the chosen basis coefficients. -/
theorem tensorProductToDirectSum_tmul (b : Module.Basis β k S) (s : S) (w : W) :
    (DirectSum.linearEquivFunOnFintype k β (fun _ => W))
        (tensorProductToDirectSum (W := W) b (s ⊗ₜ[k] w)) =
      fun i => b.repr s i • w := by
  simp only [tensorProductToDirectSum, LinearEquiv.trans_apply, LinearEquiv.apply_symm_apply,
    TensorProduct.congr_tmul, LinearEquiv.refl_apply]
  funext i
  simp [Finsupp.linearEquivFunOnFinite_apply, TensorProduct.finsuppScalarLeft_apply_tmul_apply]

/-- Evaluating the image of a pure tensor at an index gives the corresponding basis coefficient times its second factor. -/
@[simp] theorem tensorProductToDirectSum_tmul_apply
    (b : Module.Basis β k S) (s : S) (w : W) (i : β) :
    tensorProductToDirectSum (W := W) b (s ⊗ₜ[k] w) i = b.repr s i • w := by
  have := congrFun (tensorProductToDirectSum_tmul b s w) i
  simpa using this

/-- The basis-indexed tensor-product equivalence intertwines the tensor-product and direct-sum representation actions. -/
theorem tensorProductToDirectSum_equivariant
    (b : Module.Basis β k S) (σ : Representation k G W) (g : G) (x : S ⊗[k] W) :
    tensorProductToDirectSum b (((Representation.trivial k G S).tprod σ) g x) =
      (Representation.directSum (V := fun _ => W) (fun _ : β => σ)) g
        (tensorProductToDirectSum b x) := by
  induction x using TensorProduct.induction_on with
  | zero => simp
  | tmul s w =>
    rw [Representation.tprod_apply, TensorProduct.map_tmul, Representation.trivial_apply]
    refine DirectSum.ext (β := fun _ : β => W) fun i => ?_
    rw [tensorProductToDirectSum_tmul_apply, Representation.directSum_apply,
      DirectSum.lmap_apply, tensorProductToDirectSum_tmul_apply, map_smul]
  | add x y hx hy => simp only [map_add, hx, hy]

/-- Identifies the represented tensor product with the direct-sum representation formed from a constant family. -/
noncomputable def trivialTensorAsModuleDirectSumEquiv
    (b : Module.Basis β k S) (σ : Representation k G W) :
    Representation.asModule ((Representation.trivial k G S).tprod σ) ≃ₗ[MonoidAlgebra k G]
      Representation.asModule (Representation.directSum (V := fun _ => W) (fun _ : β => σ)) :=
  linearEquivAsModule (tensorProductToDirectSum b) (tensorProductToDirectSum_equivariant b σ)

/-- Identifies a tensor product with a trivial factor and a representation with a direct sum indexed by a basis. -/
noncomputable def trivialTensorAsModuleEquiv
    (b : Module.Basis β k S) (σ : Representation k G W) :
    Representation.asModule ((Representation.trivial k G S).tprod σ) ≃ₗ[MonoidAlgebra k G]
      DirectSum β (fun _ => Representation.asModule σ) :=
  trivialTensorAsModuleDirectSumEquiv b σ ≪≫ₗ
    directSumAsModuleEquiv (ι := β) (V := fun _ => W) (fun _ : β => σ)

end TrivialTprodSplit

end RepresentationTheory.AsModuleEquivalences
