/-
Copyright (c) 2026 mathlib-initiative. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: mathlib-initiative
-/

import RepresentationTheory.TensorPowerRepresentations
import RepresentationTheory.Algebra.ExteriorSymmetricAuxiliary




































namespace RepresentationTheory.SymmetricPowerRepresentations

open scoped TensorProduct

set_option linter.unusedFintypeInType false

noncomputable section



variable {k : Type} [Field k] {G : Type*} [Monoid G]
  {V : Type} [AddCommGroup V] [Module k V] [Module.Finite k V]

omit [Module.Finite k V] in

/-- The induced symmetric-power map preserves the identity map. -/
lemma symmetricPowerMap_id {n : ℕ} :
    RepresentationTheory.Algebra.ExteriorSymmetricAuxiliary.symmetricPowerMap (n := n) (LinearMap.id : V →ₗ[k] V) = LinearMap.id := by
  apply LinearMap.ext
  intro x
  obtain ⟨t, rfl⟩ := LinearMap.range_eq_top.mp (SymmetricPower.range_mk k (Fin n) V) x
  simp only [RepresentationTheory.Algebra.ExteriorSymmetricAuxiliary.symmetricPowerMap_mk, PiTensorProduct.map_id, LinearMap.id_coe, id_eq]

omit [Module.Finite k V] in

/-- The induced symmetric-power map preserves composition. -/
lemma symmetricPowerMap_comp {n : ℕ} (a b : V →ₗ[k] V) :
    RepresentationTheory.Algebra.ExteriorSymmetricAuxiliary.symmetricPowerMap (n := n) (a ∘ₗ b) =
      RepresentationTheory.Algebra.ExteriorSymmetricAuxiliary.symmetricPowerMap a ∘ₗ RepresentationTheory.Algebra.ExteriorSymmetricAuxiliary.symmetricPowerMap b := by
  apply LinearMap.ext
  intro x
  obtain ⟨t, rfl⟩ := LinearMap.range_eq_top.mp (SymmetricPower.range_mk k (Fin n) V) x
  simp only [RepresentationTheory.Algebra.ExteriorSymmetricAuxiliary.symmetricPowerMap_mk, LinearMap.comp_apply]
  congr 1
  exact LinearMap.congr_fun
    (PiTensorProduct.map_comp (g := fun _ : Fin n => a) (f := fun _ : Fin n => b)) t




/-- Defines the representation induced on a symmetric power. -/
def symmetricPowerRepresentation (ρ : Representation k G V) (n : ℕ) :
    Representation k G (Sym[k]^n V) where
  toFun g := RepresentationTheory.Algebra.ExteriorSymmetricAuxiliary.symmetricPowerMap (ρ g)
  map_one' := by
    simp only [map_one]
    exact symmetricPowerMap_id
  map_mul' g h := by
    simp only [map_mul, Module.End.mul_eq_comp]
    exact symmetricPowerMap_comp _ _

omit [Module.Finite k V] in
/-- Computes the action of the induced representation at a monoid element. -/
@[simp]
theorem symmetricPowerRepresentation_apply (ρ : Representation k G V) (n : ℕ) (g : G) :
    symmetricPowerRepresentation ρ n g = RepresentationTheory.Algebra.ExteriorSymmetricAuxiliary.symmetricPowerMap (ρ g) := rfl



end

section Embedding

open scoped TensorProduct
open RepresentationTheory.SymmetricPowerRepresentations

noncomputable section

variable {k : Type} [Field k] [CharZero k] {G : Type*} [Monoid G]
  {V : Type} [AddCommGroup V] [Module k V] [Module.Finite k V]





/-- Constructs a linear map from a symmetric power to the corresponding tensor power. -/
def symmetricPowerLift (n : ℕ) :
    Sym[k]^n V →ₗ[k] (⨂[k]^n V) :=
  (RepresentationTheory.Algebra.ExteriorSymmetricAuxiliary.auxiliarySubmodule' k V n).subtype ∘ₗ
    (RepresentationTheory.Algebra.ExteriorSymmetricAuxiliary.auxiliarySubmoduleEquivSymmetricPower n).symm.toLinearMap

/-- The symmetric-power lift is injective. -/
theorem symmetricPowerLift_injective (n : ℕ) :
    Function.Injective (symmetricPowerLift (k := k) (V := V) n) :=
  (Subtype.val_injective).comp (RepresentationTheory.Algebra.ExteriorSymmetricAuxiliary.auxiliarySubmoduleEquivSymmetricPower n).symm.injective





/-- The symmetric-power lift intertwines the displayed representation actions. -/
theorem symmetricPowerLift_intertwines (ρ : Representation k G V) (n : ℕ) (g : G) :
    symmetricPowerLift (k := k) (V := V) n ∘ₗ symmetricPowerRepresentation ρ n g =
      RepresentationTheory.TensorPowerRepresentations.tensorPowerRepresentation ρ n g ∘ₗ symmetricPowerLift n := by
  apply LinearMap.ext
  intro y
  set x := (RepresentationTheory.Algebra.ExteriorSymmetricAuxiliary.auxiliarySubmoduleEquivSymmetricPower n).symm y with hx
  have hy : y = RepresentationTheory.Algebra.ExteriorSymmetricAuxiliary.auxiliarySubmoduleEquivSymmetricPower n x := by
    rw [hx, LinearEquiv.apply_symm_apply]
  simp only [LinearMap.comp_apply, symmetricPowerRepresentation_apply, RepresentationTheory.TensorPowerRepresentations.tensorPowerRepresentation_apply,
    symmetricPowerLift, LinearEquiv.coe_coe, Submodule.subtype_apply]

  rw [hy, LinearEquiv.symm_apply_apply,
    ← RepresentationTheory.Algebra.ExteriorSymmetricAuxiliary.auxiliarySubmoduleEquivSymmetricPower_map n (ρ g) x,
    LinearEquiv.symm_apply_apply]

  rfl

end

end Embedding

section Covector

open scoped TensorProduct

variable {G : Type*} [Group G]
  {V : Type} [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V]




/-- A faithful representation has no nonidentity element acting trivially on its dual. -/
theorem eq_one_of_dual_action_eq_one {ρ : Representation ℂ G V} (hρ : Function.Injective ρ)
    {g : G} (hg : (Representation.dual ρ) g = 1) : g = 1 := by
  have hfix : ρ g⁻¹ = ρ (1 : G) := by
    apply LinearMap.ext
    intro v
    rw [map_one, Module.End.one_apply]

    have hsub : ∀ f : Module.Dual ℂ V, f (ρ g⁻¹ v - v) = 0 := by
      intro f
      have hf : (Representation.dual ρ) g f = f := by rw [hg]; rfl
      have : f ∘ₗ ρ g⁻¹ = f := hf
      have := LinearMap.congr_fun this v
      simp only [LinearMap.comp_apply, map_sub] at this ⊢
      rw [this, sub_self]
    exact sub_eq_zero.mp ((Module.forall_dual_apply_eq_zero_iff ℂ (ρ g⁻¹ v - v)).mp hsub)
  have : g⁻¹ = 1 := hρ hfix
  rwa [inv_eq_one] at this










/-- Provides a dual vector whose stabilizer is trivial for a faithful finite group action. -/
theorem exists_dual_vector_trivial_stabilizer [Finite G]
    (ρ : Representation ℂ G V) (hρ : Function.Injective ρ) :
    ∃ u : Module.Dual ℂ V, ∀ g : G, (Representation.dual ρ) g u = u → g = 1 := by
  classical

  set Fix : {g : G // g ≠ 1} → Submodule ℂ (Module.Dual ℂ V) :=
    fun g => LinearMap.ker ((Representation.dual ρ) g.1 - 1) with hFix

  have hproper : ∀ g, Fix g ≠ ⊤ := by
    intro g hg
    rw [hFix, LinearMap.ker_eq_top, sub_eq_zero] at hg
    exact g.2 (eq_one_of_dual_action_eq_one hρ hg)

  have hcover : ⋃ g, (Fix g : Set (Module.Dual ℂ V)) ≠ Set.univ := by
    intro huniv
    obtain ⟨g, hg⟩ := Subspace.exists_eq_top_of_iUnion_eq_univ huniv
    exact hproper g hg

  obtain ⟨u, hu⟩ := Set.ne_univ_iff_exists_notMem _ |>.mp hcover
  refine ⟨u, fun g hgu => ?_⟩
  by_contra hg1
  refine hu (Set.mem_iUnion.mpr ⟨⟨g, hg1⟩, ?_⟩)
  simp only [hFix, SetLike.mem_coe, LinearMap.mem_ker, LinearMap.sub_apply,
    Module.End.one_apply, sub_eq_zero]
  exact hgu

end Covector

section DirectSumExtract

open scoped DirectSum

variable {k G : Type*} [CommSemiring k] [Monoid G]
  {ι : Type*} {V : ι → Type*}
  [(i : ι) → AddCommMonoid (V i)] [(i : ι) → Module k (V i)]
  {W : Type*} [AddCommMonoid W] [Module k W]



/-- Computes a component after the action on a direct-sum representation. -/
theorem directSumRepresentation_component
    (ρs : (i : ι) → Representation k G (V i)) (i : ι) (g : G) :
    DirectSum.component k ι V i ∘ₗ (Representation.directSum ρs) g =
      ρs i g ∘ₗ DirectSum.component k ι V i := by
  ext y
  simp only [LinearMap.comp_apply, Representation.directSum_apply,
    ← DirectSum.apply_eq_component, DirectSum.lmap_apply]





/-- Extracts a nonzero equivariant map to one direct-sum component. -/
theorem exists_nonzero_component_intertwiner
    (ρs : (i : ι) → Representation k G (V i)) (σ : Representation k G W)
    (φ : W →ₗ[k] (⨁ i, V i)) (hφ : φ ≠ 0)
    (hφ_int : ∀ g, φ ∘ₗ σ g = (Representation.directSum ρs) g ∘ₗ φ) :
    ∃ (i : ι) (ψ : W →ₗ[k] V i), ψ ≠ 0 ∧ ∀ g, ψ ∘ₗ σ g = ρs i g ∘ₗ ψ := by
  obtain ⟨w, hw⟩ := DFunLike.ne_iff.mp hφ
  have hcomp : ∃ i, DirectSum.component k ι V i (φ w) ≠ 0 := by
    by_contra h
    simp only [not_exists, ne_eq, not_not] at h
    exact hw (DirectSum.ext_component k fun i => by simp [h i])
  obtain ⟨i, hi⟩ := hcomp
  refine ⟨i, DirectSum.component k ι V i ∘ₗ φ, ?_, fun g => ?_⟩
  · exact fun hzero => hi (by simpa using LinearMap.congr_fun hzero w)
  · rw [LinearMap.comp_assoc, hφ_int g, ← LinearMap.comp_assoc,
      directSumRepresentation_component, LinearMap.comp_assoc]

end DirectSumExtract

section AsModuleHom

open scoped MonoidAlgebra



variable {k G V W : Type*} [CommSemiring k] [Monoid G]
  [AddCommMonoid V] [Module k V] [AddCommMonoid W] [Module k W]
  {ρ : Representation k G V} {σ : Representation k G W}




/-- Converts a homomorphism between representation modules into a linear map. -/
noncomputable def asModuleHomToLinearMap
    (h : ρ.asModule →ₗ[MonoidAlgebra k G] σ.asModule) : V →ₗ[k] W :=
  σ.asModuleEquiv.toLinearMap ∘ₗ h.restrictScalars k ∘ₗ ρ.asModuleEquiv.symm.toLinearMap

/-- Computes the linear map obtained from a representation-module homomorphism. -/
@[simp] theorem asModuleHomToLinearMap_apply
    (h : ρ.asModule →ₗ[MonoidAlgebra k G] σ.asModule) (x : V) :
    asModuleHomToLinearMap h x = σ.asModuleEquiv (h (ρ.asModuleEquiv.symm x)) := rfl

/-- The converted linear map commutes with the two representation actions. -/
theorem asModuleHomToLinearMap_commutes
    (h : ρ.asModule →ₗ[MonoidAlgebra k G] σ.asModule) (g : G) (x : V) :
    asModuleHomToLinearMap h (ρ g x) = σ g (asModuleHomToLinearMap h x) := by
  have key : h (MonoidAlgebra.single g (1 : k) • ρ.asModuleEquiv.symm x)
      = MonoidAlgebra.single g (1 : k) • h (ρ.asModuleEquiv.symm x) := map_smul h _ _
  rw [Representation.single_smul, Representation.single_smul, one_smul, one_smul] at key
  exact key

/-- Injectivity is preserved by converting a representation-module homomorphism to a linear map. -/
theorem asModuleHomToLinearMap_injective
    {h : ρ.asModule →ₗ[MonoidAlgebra k G] σ.asModule} (hh : Function.Injective h) :
    Function.Injective (asModuleHomToLinearMap h) := by
  intro a b hab
  simp only [asModuleHomToLinearMap_apply] at hab
  exact ρ.asModuleEquiv.symm.injective (hh (σ.asModuleEquiv.injective hab))



end AsModuleHom

section SimpleEmbedsRegular

open scoped MonoidAlgebra
open Representation










/-- Produces an injective equivariant map into the regular action from a simple representation. -/
theorem exists_injective_regular_intertwiner
    {k G : Type*} [Field k] [Group G] [Fintype G] [NeZero (Nat.card G : k)]
    {W : Type*} [AddCommGroup W] [Module k W]
    (σ : Representation k G W)
    (hσ : IsSimpleModule (MonoidAlgebra k G) σ.asModule) :
    ∃ φ : W →ₗ[k] MonoidAlgebra k G, Function.Injective φ ∧
      ∀ g : G, φ ∘ₗ σ g = (Representation.ofMulAction k G G) g ∘ₗ φ := by
  classical
  obtain ⟨I, _hI, ⟨e⟩⟩ := isSimpleModule_iff_quot_maximal.mp hσ
  set reg := Representation.ofMulActionSelfAsModuleEquiv (k := k) (G := G) with hreg

  let f : (Representation.ofMulAction k G G).asModule →ₗ[MonoidAlgebra k G] σ.asModule :=
    e.symm.toLinearMap ∘ₗ I.mkQ ∘ₗ reg.toLinearMap
  have hf : Function.Surjective f :=
    e.symm.surjective.comp ((Submodule.mkQ_surjective I).comp reg.surjective)

  obtain ⟨h, hfh⟩ := IsSemisimpleModule.lifting_property (R := MonoidAlgebra k G)
    (M := (Representation.ofMulAction k G G).asModule) (N := σ.asModule)
    (P := σ.asModule) f hf (LinearMap.id)
  have hlinv : Function.LeftInverse f h := fun x => by
    simpa using LinearMap.congr_fun hfh x
  refine ⟨asModuleHomToLinearMap h,
    asModuleHomToLinearMap_injective hlinv.injective, fun g => ?_⟩
  exact LinearMap.ext fun x => asModuleHomToLinearMap_commutes h g x

end SimpleEmbedsRegular









end RepresentationTheory.SymmetricPowerRepresentations
