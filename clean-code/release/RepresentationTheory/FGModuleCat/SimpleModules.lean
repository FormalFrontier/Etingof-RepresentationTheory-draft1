/-
Copyright (c) 2026 FormalFrontier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENCE.
Authors: FormalFrontier
-/
import Mathlib

/-!
# Simple finitely generated modules

This module relates simple modules to simple objects of `FGModuleCat` and constructs a complete
finite family of simple modules over a finite-dimensional algebra.
-/

open CategoryTheory Limits

namespace RepresentationTheory.FGModuleCat.SimpleModules

universe u

noncomputable section

section Bridges

variable {A : Type u} [Ring A] [IsNoetherianRing A]

/-- A fully faithful, monomorphism-preserving functor reflects simple objects: if `F.obj X` is
simple then so is `X`. -/
private lemma simple_of_fullyFaithful_preservesMono {C D : Type*} [Category C] [Category D]
    [HasZeroMorphisms C] [HasZeroMorphisms D]
    (F : C ⥤ D) [F.Full] [F.Faithful] [F.PreservesMonomorphisms] (X : C)
    [Simple (F.obj X)] : Simple X where
  mono_isIso_iff_nonzero {Y} f := by
    intro
    refine ⟨fun hiso h => ?_, fun hne => ?_⟩
    · haveI : IsIso (F.map f) := Functor.map_isIso F f
      exact (Simple.mono_isIso_iff_nonzero (F.map f)).mp inferInstance (by rw [h]; simp)
    · haveI : Mono (F.map f) := inferInstance
      haveI : IsIso (F.map f) := (Simple.mono_isIso_iff_nonzero (F.map f)).mpr
        (fun h => hne (F.map_injective (by rwa [F.map_zero])))
      exact isIso_of_fully_faithful F f

/-- A finite simple module over a Noetherian ring defines a simple object in the category of finitely generated modules. -/
lemma simple_of_isSimpleModule
    (N : Type u) [AddCommGroup N] [Module A N] [Module.Finite A N] [IsSimpleModule A N] :
    Simple (FGModuleCat.of A N) := by
  haveI : Simple ((forget₂ (FGModuleCat.{u} A) (ModuleCat.{u} A)).obj (FGModuleCat.of A N)) := by
    change Simple (ModuleCat.of A N); infer_instance
  exact simple_of_fullyFaithful_preservesMono (forget₂ (FGModuleCat.{u} A) (ModuleCat.{u} A))
    (FGModuleCat.of A N)

/-- The carrier of a simple finitely generated module over a Noetherian ring is a simple module. -/
lemma isSimpleModule_carrier_of_simple (X : FGModuleCat.{u} A) [Simple X] :
    IsSimpleModule A X := by
  haveI hXnt : Nontrivial X := by
    by_contra h
    rw [not_nontrivial_iff_subsingleton] at h
    exact id_nonzero X (by ext x; exact Subsingleton.elim _ _)
  haveI : Nontrivial (Submodule A X) := ⟨⊥, ⊤, bot_ne_top⟩
  rw [isSimpleModule_iff]
  refine IsSimpleOrder.mk fun P => ?_
  let ιP : FGModuleCat.of A ↥P ⟶ X := FGModuleCat.ofHom P.subtype
  haveI : Mono ((forget₂ (FGModuleCat.{u} A) (ModuleCat.{u} A)).map ιP) := by
    rw [ModuleCat.mono_iff_injective]; exact P.injective_subtype
  haveI : Mono ιP := (forget₂ (FGModuleCat.{u} A) (ModuleCat.{u} A)).mono_of_mono_map this
  by_cases hz : ιP = 0
  · left
    have key : ∀ y : ↥P, (y : X) = 0 := fun y => by
      have h0 : ιP.hom.hom y = 0 := by rw [hz]; simp
      exact h0
    rw [eq_bot_iff]; intro x hx; rw [Submodule.mem_bot]; exact key ⟨x, hx⟩
  · right
    haveI : IsIso ιP := (Simple.mono_isIso_iff_nonzero ιP).mpr hz
    let e := FGModuleCat.isoToLinearEquiv (asIso ιP)
    have he : ∀ y : ↥P, e y = (y : X) := fun y => rfl
    rw [eq_top_iff]; intro x _
    exact (he (e.symm x)).symm.trans (e.apply_symm_apply x) ▸ (e.symm x).2

end Bridges

variable (k : Type u) [instField : Field k] (A : Type u) [Ring A] [instAlg : Algebra k A]
  [instFin : Module.Finite k A]

include instField instAlg instFin

/-- For a finite algebra over a field, there is a finite family of finite simple submodules such that every simple module is equivalent to a member. -/
theorem exists_completeSimpleSubmoduleFamily :
    ∃ (n : ℕ) (S : Fin n → Submodule A (A ⧸ Ring.jacobson A)),
      (∀ i, Module.Finite k ↥(S i)) ∧ (∀ i, IsSimpleModule A ↥(S i)) ∧
      ∀ (M : Type u) [AddCommGroup M] [Module A M] [IsSimpleModule A M],
        ∃ i, Nonempty (M ≃ₗ[A] ↥(S i)) := by
  classical
  haveI : IsArtinianRing A := IsArtinianRing.of_finite k A
  haveI : IsSemiprimaryRing A := inferInstance
  haveI : IsSemisimpleRing (A ⧸ Ring.jacobson A) := IsSemiprimaryRing.isSemisimpleRing
  haveI : Module.Finite A (A ⧸ Ring.jacobson A) := inferInstance
  haveI : Module.Finite k (A ⧸ Ring.jacobson A) :=
    Module.Finite.of_surjective (Ideal.Quotient.mkₐ k (Ring.jacobson A)).toLinearMap
      (Ideal.Quotient.mkₐ_surjective k (Ring.jacobson A))
  haveI hss : IsSemisimpleModule A (A ⧸ Ring.jacobson A) := by
    let l : (A ⧸ Ring.jacobson A) →ₛₗ[Ideal.Quotient.mk (Ring.jacobson A)]
        (A ⧸ Ring.jacobson A) :=
      { toFun := id, map_add' := fun _ _ => rfl, map_smul' := fun _ _ => rfl }
    exact (LinearMap.isSemisimpleModule_iff_of_bijective l Function.bijective_id).mpr inferInstance
  obtain ⟨n, S, e, hSsimple⟩ :=
    IsSemisimpleModule.exists_linearEquiv_fin_dfinsupp A (A ⧸ Ring.jacobson A)
  have hfin : ∀ i, Module.Finite k ↥(S i) := fun i =>
    Module.Finite.of_injective ((S i).subtype.restrictScalars k) (S i).injective_subtype
  refine ⟨n, S, hfin, hSsimple, ?_⟩
  intro M _ _ _
  have hann : Ring.jacobson A ≤ Module.annihilator A M :=
    IsSemisimpleModule.jacobson_le_annihilator A M
  haveI : Nontrivial M := IsSimpleModule.nontrivial (R := A) (M := M)
  obtain ⟨m₀, hm₀⟩ := exists_ne (0 : M)
  set g : A →ₗ[A] M := LinearMap.toSpanSingleton A M m₀ with hg
  have hg_surj : Function.Surjective g := by
    rw [← LinearMap.range_eq_top, hg, ← LinearMap.span_singleton_eq_range]
    exact (IsSimpleOrder.eq_bot_or_eq_top (Submodule.span A {m₀})).resolve_left
      (fun h => hm₀ (Submodule.span_singleton_eq_bot.mp h))
  have hker : Ring.jacobson A ≤ LinearMap.ker g := fun a ha => by
    rw [LinearMap.mem_ker, hg, LinearMap.toSpanSingleton_apply]
    exact Module.mem_annihilator.mp (hann ha) m₀
  set g' : (A ⧸ Ring.jacobson A) →ₗ[A] M := Submodule.liftQ (Ring.jacobson A) g hker with hg'
  have hg'_surj : Function.Surjective g' := by
    rw [← LinearMap.range_eq_top, Submodule.range_liftQ, LinearMap.range_eq_top]; exact hg_surj
  set F : (Π₀ i, ↥(S i)) →ₗ[A] M := g'.comp e.symm.toLinearMap with hF
  have hF_surj : Function.Surjective F := hg'_surj.comp e.symm.surjective
  have hF_ne : F ≠ 0 := by
    intro h; obtain ⟨y, hy⟩ := hF_surj m₀; rw [h] at hy; simp at hy; exact hm₀ hy.symm
  have hcomp : ∃ i, F.comp (DFinsupp.lsingle i) ≠ 0 := by
    by_contra hcon
    refine hF_ne (DFinsupp.lhom_ext' (fun i => ?_))
    have hi : F.comp (DFinsupp.lsingle i) = 0 := not_not.mp (fun h => hcon ⟨i, h⟩)
    rw [hi]; simp
  obtain ⟨i₀, hi₀⟩ := hcomp
  haveI := hSsimple i₀
  exact ⟨i₀, ⟨(LinearEquiv.ofBijective _ (LinearMap.bijective_of_ne_zero hi₀)).symm⟩⟩

/-- For a finite algebra over a field, there is an indexed family of simple finitely generated modules containing every simple object up to isomorphism. -/
theorem exists_completeSimpleObjectFamily :
    ∃ (ι : Type) (_ : Fintype ι) (V : ι → FGModuleCat.{u} A),
      (∀ i, Simple (V i)) ∧
      ∀ (X : FGModuleCat.{u} A), Simple X → ∃ i, Nonempty (X ≅ V i) := by
  haveI : IsArtinianRing A := IsArtinianRing.of_finite k A
  haveI : IsNoetherianRing A := inferInstance
  obtain ⟨n, S, _hfin, hSsimple, hcomplete⟩ := exists_completeSimpleSubmoduleFamily k A
  refine ⟨Fin n, inferInstance, fun i => FGModuleCat.of A ↥(S i), fun i => ?_, ?_⟩
  · haveI := hSsimple i
    exact simple_of_isSimpleModule ↥(S i)
  · intro X hX
    haveI := hX
    haveI : IsSimpleModule A X := isSimpleModule_carrier_of_simple X
    obtain ⟨i, ⟨φ⟩⟩ := hcomplete X
    exact ⟨i, ⟨φ.toFGModuleCatIso⟩⟩

end

end RepresentationTheory.FGModuleCat.SimpleModules
