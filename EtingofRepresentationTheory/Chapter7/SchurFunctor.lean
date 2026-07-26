import Mathlib.RepresentationTheory.Invariants
import Mathlib.LinearAlgebra.PiTensorProduct.Basic
import Mathlib.Algebra.Category.ModuleCat.Basic

/-!
# Schur functors

Etingof's Example 7.2.2(8) closes with: *"More generally, if `π` is a representation of `Sₙ`,
we have functors `V ↦ Hom_{Sₙ}(π, V^{⊗n})`. Such functors are called the Schur functors."*

This file constructs those functors. The two ingredients are

* `Etingof.tensorPowerPermRep k n V` — the permutation action of `Sₙ` on `V^{⊗n}`, sending
  `v₁ ⊗ ⋯ ⊗ vₙ` to `v_{σ⁻¹(1)} ⊗ ⋯ ⊗ v_{σ⁻¹(n)}`, packaged as a `Representation`;
* `Etingof.piTensorMap_comm_perm` — the diagonal map `f ⊗ ⋯ ⊗ f` induced by `f : V →ₗ W`
  is `Sₙ`-equivariant, which is what makes the construction functorial at all.

The functor itself is `Etingof.schurFunctor π`, with underlying object assignment
`Etingof.schurObj π V = Hom_{Sₙ}(π, V^{⊗n})`, realised as the invariants of
`Representation.linHom` — i.e. the submodule of `W →ₗ[k] V^{⊗n}` consisting of the
intertwiners. `Etingof.mem_schurObj_iff` restates membership as the usual intertwining
identity `ρ σ ∘ₗ φ = φ ∘ₗ π σ`.

Neither the `Sₙ`-action on a tensor power nor the equivariant Hom is packaged as a functor
in Mathlib, so this is new API rather than a wrapper.
-/

open CategoryTheory
open scoped TensorProduct

namespace Etingof

universe u

section PermAction

variable (k : Type u) [CommRing k] (n : ℕ)
  (V : Type u) [AddCommGroup V] [Module k V]
  (W : Type u) [AddCommGroup W] [Module k W]

/-- Extensionality for linear maps out of a tensor power: it suffices to check pure tensors.
Mathlib's `PiTensorProduct.ext` is only a local `ext` lemma, so we re-expose it here in
applied form. -/
theorem piTensor_ext {E : Type*} [AddCommMonoid E] [Module k E]
    {φ₁ φ₂ : (⨂[k] (_ : Fin n), V) →ₗ[k] E}
    (h : ∀ v : Fin n → V, φ₁ (PiTensorProduct.tprod k v) = φ₂ (PiTensorProduct.tprod k v)) :
    φ₁ = φ₂ :=
  PiTensorProduct.ext (MultilinearMap.ext h)

/-- The permutation action of the symmetric group `Sₙ` on the tensor power `V^{⊗n}`:
`σ` sends `v₁ ⊗ ⋯ ⊗ vₙ` to `v_{σ⁻¹(1)} ⊗ ⋯ ⊗ v_{σ⁻¹(n)}`. -/
noncomputable def tensorPowerPermRep :
    Representation k (Equiv.Perm (Fin n)) (⨂[k] (_ : Fin n), V) where
  toFun σ := (PiTensorProduct.reindex k (fun _ : Fin n => V) σ).toLinearMap
  map_one' := by
    refine piTensor_ext k n V fun v => ?_
    simp only [LinearEquiv.coe_coe, PiTensorProduct.reindex_tprod, Module.End.one_apply]
    rfl
  map_mul' σ τ := by
    refine piTensor_ext k n V fun v => ?_
    simp only [LinearEquiv.coe_coe, PiTensorProduct.reindex_tprod, Module.End.mul_apply]
    rfl

variable {k n V}

@[simp] theorem tensorPowerPermRep_tprod (σ : Equiv.Perm (Fin n)) (v : Fin n → V) :
    tensorPowerPermRep k n V σ (PiTensorProduct.tprod k v) =
      PiTensorProduct.tprod k fun i => v (σ.symm i) :=
  PiTensorProduct.reindex_tprod (s := fun _ : Fin n => V) σ v

variable {W}

/-- The diagonal map `f ⊗ ⋯ ⊗ f : V^{⊗n} → W^{⊗n}` is `Sₙ`-equivariant for the permutation
actions. This is the functoriality input for the Schur functors: both operations act on
disjoint data (`f` on the entries, `σ` on the slots), so they commute. -/
theorem piTensorMap_comm_perm (f : V →ₗ[k] W) (σ : Equiv.Perm (Fin n)) :
    (PiTensorProduct.map fun _ : Fin n => f) ∘ₗ (tensorPowerPermRep k n V σ) =
      (tensorPowerPermRep k n W σ) ∘ₗ (PiTensorProduct.map fun _ : Fin n => f) := by
  refine piTensor_ext k n V fun v => ?_
  simp

end PermAction

section Schur

variable {k : Type u} [CommRing k] {n : ℕ}
  {W : Type u} [AddCommGroup W] [Module k W]
  (π : Representation k (Equiv.Perm (Fin n)) W)

/-- `Hom_{Sₙ}(π, V^{⊗n})`, the value of the Schur functor attached to the `Sₙ`-representation
`π` at the vector space `V`. It is the space of `Sₙ`-intertwiners from `π` to the tensor
power `V^{⊗n}` with its permutation action, realised as the invariants of the representation
`Representation.linHom` on `W →ₗ[k] V^{⊗n}`. -/
noncomputable def schurObj (V : Type u) [AddCommGroup V] [Module k V] :
    Submodule k (W →ₗ[k] ⨂[k] (_ : Fin n), V) :=
  (Representation.linHom π (tensorPowerPermRep k n V)).invariants

variable {V : Type u} [AddCommGroup V] [Module k V]
  {V' : Type u} [AddCommGroup V'] [Module k V']

private theorem rep_inv_apply (σ : Equiv.Perm (Fin n)) (w : W) : π σ⁻¹ (π σ w) = w := by
  rw [← Module.End.mul_apply, ← map_mul, inv_mul_cancel, map_one, Module.End.one_apply]

private theorem rep_apply_inv (σ : Equiv.Perm (Fin n)) (w : W) : π σ (π σ⁻¹ w) = w := by
  rw [← Module.End.mul_apply, ← map_mul, mul_inv_cancel, map_one, Module.End.one_apply]

/-- Membership in `schurObj` is the usual intertwining identity: `φ` commutes with the two
`Sₙ`-actions. -/
theorem mem_schurObj_iff (φ : W →ₗ[k] ⨂[k] (_ : Fin n), V) :
    φ ∈ schurObj π V ↔
      ∀ σ : Equiv.Perm (Fin n), (tensorPowerPermRep k n V σ) ∘ₗ φ = φ ∘ₗ (π σ) := by
  simp only [schurObj, Representation.mem_invariants, Representation.linHom_apply]
  constructor
  · intro h σ
    ext w
    have := congrArg (fun ψ : W →ₗ[k] ⨂[k] (_ : Fin n), V => ψ (π σ w)) (h σ)
    simpa [rep_inv_apply π σ w] using this
  · intro h σ
    ext w
    have := congrArg (fun ψ : W →ₗ[k] ⨂[k] (_ : Fin n), V => ψ (π σ⁻¹ w)) (h σ)
    simpa [rep_apply_inv π σ w] using this

/-- The action of the Schur functor on morphisms: postcomposition with the diagonal map
`f ⊗ ⋯ ⊗ f`, which lands in the intertwiners because that map is `Sₙ`-equivariant. -/
noncomputable def schurMap (f : V →ₗ[k] V') : schurObj π V →ₗ[k] schurObj π V' :=
  (LinearMap.llcomp k W _ _ (PiTensorProduct.map fun _ : Fin n => f)).restrict
    (fun φ hφ => by
      rw [mem_schurObj_iff] at hφ ⊢
      intro σ
      change (tensorPowerPermRep k n V' σ) ∘ₗ
        ((PiTensorProduct.map fun _ : Fin n => f) ∘ₗ φ) = _
      rw [← LinearMap.comp_assoc, ← piTensorMap_comm_perm f σ, LinearMap.comp_assoc, hφ σ,
        ← LinearMap.comp_assoc]
      rfl)

@[simp] theorem schurMap_coe (f : V →ₗ[k] V') (φ : schurObj π V) :
    (schurMap π f φ : W →ₗ[k] ⨂[k] (_ : Fin n), V') =
      (PiTensorProduct.map fun _ : Fin n => f) ∘ₗ (φ : W →ₗ[k] ⨂[k] (_ : Fin n), V) :=
  rfl

theorem schurMap_id : schurMap π (LinearMap.id : V →ₗ[k] V) = LinearMap.id := by
  ext φ
  simp [PiTensorProduct.map_id]

theorem schurMap_comp {V'' : Type u} [AddCommGroup V''] [Module k V'']
    (g : V' →ₗ[k] V'') (f : V →ₗ[k] V') :
    schurMap π (g ∘ₗ f) = (schurMap π g) ∘ₗ (schurMap π f) := by
  ext φ
  change ((PiTensorProduct.map fun _ : Fin n => g ∘ₗ f) ∘ₗ (φ : W →ₗ[k] _)) _ = _
  rw [show (fun _ : Fin n => g ∘ₗ f) =
      fun i : Fin n => (fun _ : Fin n => g) i ∘ₗ (fun _ : Fin n => f) i from rfl,
    PiTensorProduct.map_comp]
  rfl

/-- **The Schur functor** attached to a representation `π` of `Sₙ`:
`V ↦ Hom_{Sₙ}(π, V^{⊗n})`. (Etingof, Example 7.2.2(8).)

Taking `π` to run over the irreducible representations of `Sₙ` — which by Chapter 5 are
labelled by Young diagrams with `n` boxes — gives the irreducible Schur functors. -/
noncomputable def schurFunctor : ModuleCat.{u} k ⥤ ModuleCat.{u} k where
  obj V := ModuleCat.of k (schurObj π V)
  map f := ModuleCat.ofHom (schurMap π f.hom)
  map_id V := by
    apply ModuleCat.hom_ext
    simp only [ModuleCat.hom_ofHom, ModuleCat.hom_id]
    exact schurMap_id π
  map_comp f g := by
    apply ModuleCat.hom_ext
    simp only [ModuleCat.hom_ofHom, ModuleCat.hom_comp]
    exact schurMap_comp π _ _

@[simp] theorem schurFunctor_obj (V : ModuleCat.{u} k) :
    (schurFunctor π).obj V = ModuleCat.of k (schurObj π V) := rfl

end Schur

section Trivial

variable {k : Type u} [CommRing k] {n : ℕ}
  {V : Type u} [AddCommGroup V] [Module k V]

/-- The Schur functor of the trivial `Sₙ`-representation on `k` is the space of symmetric
tensors: `Hom_{Sₙ}(k, V^{⊗n}) ≃ (V^{⊗n})^{Sₙ}`, by evaluation at `1`.

This pins down the construction: the invariants submodule `schurObj` really is the
equivariant Hom the book asks for, and in the simplest case it is visibly nonzero
whenever `V` is (for `n = 0`, or for `n ≥ 1` and `v : V`, the symmetrised pure tensor
lies in it). -/
noncomputable def schurObjTrivialEquiv :
    schurObj (Representation.trivial k (Equiv.Perm (Fin n)) k) V ≃ₗ[k]
      (tensorPowerPermRep k n V).invariants where
  toFun φ := ⟨(φ : k →ₗ[k] ⨂[k] (_ : Fin n), V) 1, fun σ => by
    have := (mem_schurObj_iff _ _).mp φ.2 σ
    have h := congrArg (fun ψ : k →ₗ[k] ⨂[k] (_ : Fin n), V => ψ 1) this
    simpa [Representation.trivial_apply] using h⟩
  map_add' _ _ := rfl
  map_smul' _ _ := rfl
  invFun t := ⟨LinearMap.toSpanSingleton k _ (t : ⨂[k] (_ : Fin n), V), by
    rw [mem_schurObj_iff]
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

end Etingof
