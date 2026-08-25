/-
Copyright (c) 2026 mathlib-initiative. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: mathlib-initiative
-/
import Mathlib.RepresentationTheory.Invariants
import Mathlib.LinearAlgebra.PiTensorProduct.Basic
import Mathlib.Algebra.Category.ModuleCat.Basic
import RepresentationTheory.Alignment.Attribute

/-!
# Equivariant maps into Pi tensor products

This module constructs the permutation action on Pi tensor products and the functor of equivariant
linear maps from a fixed representation into those tensor products.
-/

open CategoryTheory
open scoped TensorProduct

namespace RepresentationTheory.Mathlib.RepresentationTheory.PiTensorProduct.Equivariant

universe u

section PermAction

variable (k : Type u) [CommRing k] (n : ℕ)
  (V : Type u) [AddCommGroup V] [Module k V]
  (W : Type u) [AddCommGroup W] [Module k W]

/-- Two linear maps out of a Pi tensor product are equal when they agree on all pure tensors. -/
theorem linearMap_ext_tprod {E : Type*} [AddCommMonoid E] [Module k E]
    {φ₁ φ₂ : (⨂[k] (_ : Fin n), V) →ₗ[k] E}
    (h : ∀ v : Fin n → V, φ₁ (PiTensorProduct.tprod k v) = φ₂ (PiTensorProduct.tprod k v)) :
    φ₁ = φ₂ :=
  PiTensorProduct.ext (MultilinearMap.ext h)

/-- The representation of finite permutations on a Pi tensor product obtained by permuting tensor
factors. -/
noncomputable def permRepresentation :
    Representation k (Equiv.Perm (Fin n)) (⨂[k] (_ : Fin n), V) where
  toFun σ := (PiTensorProduct.reindex k (fun _ : Fin n => V) σ).toLinearMap
  map_one' := by
    refine linearMap_ext_tprod k n V fun v => ?_
    simp only [LinearEquiv.coe_coe, PiTensorProduct.reindex_tprod, Module.End.one_apply]
    rfl
  map_mul' σ τ := by
    refine linearMap_ext_tprod k n V fun v => ?_
    simp only [LinearEquiv.coe_coe, PiTensorProduct.reindex_tprod, Module.End.mul_apply]
    rfl

variable {k n V}

/-- A permutation acts on a pure tensor by reindexing its factors using the inverse permutation. -/
@[simp] theorem permRepresentation_apply_tprod (σ : Equiv.Perm (Fin n))
    (v : Fin n → V) :
    permRepresentation k n V σ (PiTensorProduct.tprod k v) =
      PiTensorProduct.tprod k fun i => v (σ.symm i) :=
  PiTensorProduct.reindex_tprod (s := fun _ : Fin n => V) σ v

variable {W}

/-- Mapping every tensor factor by a linear map commutes with the permutation representation on
tensor products. -/
theorem permRepresentation_map_comm (f : V →ₗ[k] W) (σ : Equiv.Perm (Fin n)) :
    (PiTensorProduct.map fun _ : Fin n => f) ∘ₗ (permRepresentation k n V σ) =
      (permRepresentation k n W σ) ∘ₗ (PiTensorProduct.map fun _ : Fin n => f) := by
  refine linearMap_ext_tprod k n V fun v => ?_
  simp

end PermAction

section Schur

variable {k : Type u} [CommRing k] {n : ℕ}
  {W : Type u} [AddCommGroup W] [Module k W]
  (π : Representation k (Equiv.Perm (Fin n)) W)

/-- The submodule of linear maps that intertwine a permutation-group representation with its
action on a Pi tensor product. -/
noncomputable def equivariantLinearMaps (V : Type u) [AddCommGroup V] [Module k V] :
    Submodule k (W →ₗ[k] ⨂[k] (_ : Fin n), V) :=
  (Representation.linHom π (permRepresentation k n V)).invariants

variable {V : Type u} [AddCommGroup V] [Module k V]
  {V' : Type u} [AddCommGroup V'] [Module k V']

private theorem rep_inv_apply (σ : Equiv.Perm (Fin n)) (w : W) : π σ⁻¹ (π σ w) = w := by
  rw [← Module.End.mul_apply, ← map_mul, inv_mul_cancel, map_one, Module.End.one_apply]

private theorem rep_apply_inv (σ : Equiv.Perm (Fin n)) (w : W) : π σ (π σ⁻¹ w) = w := by
  rw [← Module.End.mul_apply, ← map_mul, mul_inv_cancel, map_one, Module.End.one_apply]

/-- Characterizes the linear maps in the equivariant submodule by commutation with every
permutation action. -/
theorem mem_equivariantLinearMaps_iff (φ : W →ₗ[k] ⨂[k] (_ : Fin n), V) :
    φ ∈ equivariantLinearMaps π V ↔
      ∀ σ : Equiv.Perm (Fin n), (permRepresentation k n V σ) ∘ₗ φ = φ ∘ₗ (π σ) := by
  simp only [equivariantLinearMaps, Representation.mem_invariants,
    Representation.linHom_apply]
  constructor
  · intro h σ
    ext w
    have := congrArg (fun ψ : W →ₗ[k] ⨂[k] (_ : Fin n), V => ψ (π σ w)) (h σ)
    simpa [rep_inv_apply π σ w] using this
  · intro h σ
    ext w
    have := congrArg (fun ψ : W →ₗ[k] ⨂[k] (_ : Fin n), V => ψ (π σ⁻¹ w)) (h σ)
    simpa [rep_apply_inv π σ w] using this

/-- Lifts a linear map between modules to a map between the corresponding equivariant-map
submodules. -/
noncomputable def equivariantLinearMapsMap
    (f : V →ₗ[k] V') : equivariantLinearMaps π V →ₗ[k] equivariantLinearMaps π V' :=
  (LinearMap.llcomp k W _ _ (PiTensorProduct.map fun _ : Fin n => f)).restrict
    (fun φ hφ => by
      rw [mem_equivariantLinearMaps_iff] at hφ ⊢
      intro σ
      change (permRepresentation k n V' σ) ∘ₗ
        ((PiTensorProduct.map fun _ : Fin n => f) ∘ₗ φ) = _
      rw [← LinearMap.comp_assoc, ← permRepresentation_map_comm f σ, LinearMap.comp_assoc,
        hφ σ, ← LinearMap.comp_assoc]
      rfl)

/-- The lifted map acts on an equivariant linear map by postcomposition with the factorwise tensor
map. -/
@[simp] theorem equivariantLinearMapsMap_apply (f : V →ₗ[k] V')
    (φ : equivariantLinearMaps π V) :
    (equivariantLinearMapsMap π f φ : W →ₗ[k] ⨂[k] (_ : Fin n), V') =
      (PiTensorProduct.map fun _ : Fin n => f) ∘ₗ
        (φ : W →ₗ[k] ⨂[k] (_ : Fin n), V) :=
  rfl

/-- Lifting the identity linear map gives the identity on equivariant linear maps. -/
theorem equivariantLinearMapsMap_id :
    equivariantLinearMapsMap π (LinearMap.id : V →ₗ[k] V) = LinearMap.id := by
  ext φ
  simp [PiTensorProduct.map_id]

/-- The lift of a composite linear map is the composite of the lifted maps. -/
theorem equivariantLinearMapsMap_comp {V'' : Type u} [AddCommGroup V''] [Module k V'']
    (g : V' →ₗ[k] V'') (f : V →ₗ[k] V') :
    equivariantLinearMapsMap π (g ∘ₗ f) =
      (equivariantLinearMapsMap π g) ∘ₗ (equivariantLinearMapsMap π f) := by
  ext φ
  change ((PiTensorProduct.map fun _ : Fin n => g ∘ₗ f) ∘ₗ (φ : W →ₗ[k] _)) _ = _
  rw [show (fun _ : Fin n => g ∘ₗ f) =
      fun i : Fin n => (fun _ : Fin n => g) i ∘ₗ (fun _ : Fin n => f) i from rfl,
    PiTensorProduct.map_comp]
  rfl

/-- The functor sending a module to the module of equivariant maps into its Pi tensor product. -/
@[source_ref "Chapter7/Example7.2.2" (role := supporting)]
noncomputable def equivariantLinearMapsFunctor : ModuleCat.{u} k ⥤ ModuleCat.{u} k where
  obj V := ModuleCat.of k (equivariantLinearMaps π V)
  map f := ModuleCat.ofHom (equivariantLinearMapsMap π f.hom)
  map_id V := by
    apply ModuleCat.hom_ext
    simp only [ModuleCat.hom_ofHom, ModuleCat.hom_id]
    exact equivariantLinearMapsMap_id π
  map_comp f g := by
    apply ModuleCat.hom_ext
    simp only [ModuleCat.hom_ofHom, ModuleCat.hom_comp]
    exact equivariantLinearMapsMap_comp π _ _

/-- Identifies the object of the equivariant-linear-maps functor with its defining subtype. -/
@[simp] theorem equivariantLinearMapsFunctor_obj (V : ModuleCat.{u} k) :
    (equivariantLinearMapsFunctor π).obj V =
      ModuleCat.of k (equivariantLinearMaps π V) := rfl

end Schur

section Trivial

variable {k : Type u} [CommRing k] {n : ℕ}
  {V : Type u} [AddCommGroup V] [Module k V]

/-- The equivariant maps from the trivial representation to a Pi tensor product are linearly
equivalent to its invariant tensors. -/
noncomputable def equivariantLinearMapsTrivialEquivInvariants :
    equivariantLinearMaps (Representation.trivial k (Equiv.Perm (Fin n)) k) V ≃ₗ[k]
      (permRepresentation k n V).invariants where
  toFun φ := ⟨(φ : k →ₗ[k] ⨂[k] (_ : Fin n), V) 1, fun σ => by
    have := (mem_equivariantLinearMaps_iff _ _).mp φ.2 σ
    have h := congrArg (fun ψ : k →ₗ[k] ⨂[k] (_ : Fin n), V => ψ 1) this
    simpa [Representation.trivial_apply] using h⟩
  map_add' _ _ := rfl
  map_smul' _ _ := rfl
  invFun t := ⟨LinearMap.toSpanSingleton k _ (t : ⨂[k] (_ : Fin n), V), by
    rw [mem_equivariantLinearMaps_iff]
    intro σ
    ext
    simpa [LinearMap.toSpanSingleton_apply, Representation.trivial_apply] using t.2 σ⟩
  left_inv φ := by
    refine Subtype.ext (LinearMap.ext_ring ?_)
    simp [LinearMap.toSpanSingleton_apply]
  right_inv t := by
    refine Subtype.ext ?_
    simp [LinearMap.toSpanSingleton_apply]

end Trivial

end RepresentationTheory.Mathlib.RepresentationTheory.PiTensorProduct.Equivariant
