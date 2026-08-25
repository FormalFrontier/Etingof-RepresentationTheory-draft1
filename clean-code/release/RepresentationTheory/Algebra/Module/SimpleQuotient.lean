/-
Copyright (c) 2026 mathlib-initiative. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: mathlib-initiative
-/
import Mathlib.RingTheory.FiniteLength
import RepresentationTheory.ModuleCat.Auxiliary

/-!
# Simple quotients of submodules

This module characterizes and transports an auxiliary relation selecting simple subquotients of
modules over a ring.
-/

universe v u

open CategoryTheory
open RepresentationTheory.ModuleCat.Auxiliary

section CompositionFactor

variable {R : Type u} [Ring R]

namespace RepresentationTheory.Algebra.Module.SimpleQuotient

/-- Characterizes the condition using a simple target together with a surjective witness. -/
theorem simple_target_iff {M S : ModuleCat.{v} R} :
    auxiliaryModuleRelationOverRing R M S ↔
      IsSimpleModule R S ∧ ∃ (P : Submodule R M) (g : P →ₗ[R] S), Function.Surjective g := by
  constructor
  · rintro ⟨hS, N₁, N₂, hle, ⟨e⟩⟩
    refine ⟨hS, N₂, e.toLinearMap ∘ₗ (N₁.comap N₂.subtype).mkQ, ?_⟩
    exact e.surjective.comp (Submodule.mkQ_surjective _)
  · rintro ⟨hS, P, g, hg⟩
    refine ⟨hS, (LinearMap.ker g).map P.subtype, P, Submodule.map_subtype_le _ _, ?_⟩
    have hcomap : ((LinearMap.ker g).map P.subtype).comap P.subtype = LinearMap.ker g :=
      Submodule.comap_map_eq_of_injective P.subtype_injective _
    rw [hcomap]
    exact ⟨g.quotKerEquivOfSurjective hg⟩

end RepresentationTheory.Algebra.Module.SimpleQuotient

open RepresentationTheory.Algebra.Module.SimpleQuotient

namespace RepresentationTheory.ModuleCat.Auxiliary

/-- Extends the selected-target condition from a submodule to its ambient module. -/
theorem auxiliaryModuleRelationOverRing.of_submodule
    {M S : ModuleCat.{v} R} (P : Submodule R M)
    (h : auxiliaryModuleRelationOverRing R (ModuleCat.of R P) S) :
    auxiliaryModuleRelationOverRing R M S := by
  rw [simple_target_iff] at h ⊢
  obtain ⟨hS, Q, g, hg⟩ := h
  refine ⟨hS, Q.map P.subtype,
    g ∘ₗ (Submodule.equivMapOfInjective P.subtype P.subtype_injective Q).symm.toLinearMap, ?_⟩
  exact hg.comp (Submodule.equivMapOfInjective P.subtype P.subtype_injective Q).symm.surjective

/-- Pulls the selected-target condition back along a surjective linear map. -/
theorem auxiliaryModuleRelationOverRing.of_surjective
    {M : ModuleCat.{v} R} {B : Type v} [AddCommGroup B] [Module R B]
    {S : ModuleCat.{v} R} (q : M →ₗ[R] B) (hq : Function.Surjective q)
    (h : auxiliaryModuleRelationOverRing R (ModuleCat.of R B) S) :
    auxiliaryModuleRelationOverRing R M S := by
  rw [simple_target_iff] at h ⊢
  obtain ⟨hS, P, g, hg⟩ := h
  have hres : ∀ x ∈ P.comap q, q x ∈ P := fun x hx => hx
  refine ⟨hS, P.comap q, g ∘ₗ q.restrict hres, ?_⟩
  apply hg.comp
  rintro ⟨y, hy⟩
  obtain ⟨x, rfl⟩ := hq y
  exact ⟨⟨x, hy⟩, Subtype.ext (by simp)⟩

end RepresentationTheory.ModuleCat.Auxiliary

namespace RepresentationTheory.Algebra.Module.SimpleQuotient

/-- Every small nontrivial module admits a second module satisfying the displayed condition. -/
theorem exists_target {M : ModuleCat.{v} R} [Small.{v} R] [Nontrivial M] :
    ∃ S : ModuleCat.{v} R, auxiliaryModuleRelationOverRing R M S := by
  obtain ⟨m, hm⟩ := exists_ne (0 : M)
  set g : R →ₗ[R] M := LinearMap.toSpanSingleton R M m with hgdef
  have hkerne : LinearMap.ker g ≠ ⊤ := by
    intro htop
    apply hm
    have h1 : (1 : R) ∈ LinearMap.ker g := htop ▸ Submodule.mem_top
    have h2 := LinearMap.mem_ker.mp h1
    simpa [g, LinearMap.toSpanSingleton_apply] using h2
  obtain ⟨𝔪, h𝔪max, hle⟩ := Ideal.exists_le_maximal (LinearMap.ker g) hkerne
  have h𝔪coatom : IsCoatom 𝔪 := Ideal.isMaximal_def.mp h𝔪max
  have hle'' : LinearMap.ker g.rangeRestrict ≤ Submodule.comap LinearMap.id 𝔪 := by
    rw [Submodule.comap_id, LinearMap.ker_rangeRestrict]; exact hle
  set proj : (R ⧸ LinearMap.ker g.rangeRestrict) →ₗ[R] (R ⧸ 𝔪) :=
    Submodule.mapQ _ 𝔪 LinearMap.id hle'' with hprojdef
  have hprojsurj : Function.Surjective proj := by
    intro y
    obtain ⟨r, rfl⟩ := Submodule.Quotient.mk_surjective 𝔪 y
    exact ⟨Submodule.Quotient.mk r, by simp [hprojdef, Submodule.mapQ_apply]⟩
  set e := (g.rangeRestrict.quotKerEquivOfSurjective (LinearMap.surjective_rangeRestrict g)).symm
    with hedef
  set gmap : (LinearMap.range g) →ₗ[R] (R ⧸ 𝔪) := proj ∘ₗ e.toLinearMap with hgmapdef
  have hgmapsurj : Function.Surjective gmap := hprojsurj.comp e.surjective
  have hsimple : IsSimpleModule R (R ⧸ 𝔪) := isSimpleModule_iff_isCoatom.mpr h𝔪coatom
  set sh := Shrink.linearEquiv R (R ⧸ 𝔪) with hshdef
  refine ⟨ModuleCat.of R (Shrink.{v} (R ⧸ 𝔪)), simple_target_iff.mpr
    ⟨sh.isSimpleModule_iff.mpr hsimple, LinearMap.range g, sh.symm.toLinearMap ∘ₗ gmap, ?_⟩⟩
  exact sh.symm.surjective.comp hgmapsurj

end RepresentationTheory.Algebra.Module.SimpleQuotient

namespace RepresentationTheory.ModuleCat.Auxiliary

/-- Shows that the source module of this selected-target condition is nontrivial. -/
theorem auxiliaryModuleRelationOverRing.nontrivial {M U : ModuleCat.{v} R}
    (h : auxiliaryModuleRelationOverRing R M U) : Nontrivial M := by
  rw [simple_target_iff] at h
  obtain ⟨hU, P, g, hg⟩ := h
  haveI : Nontrivial U := hU.nontrivial
  obtain ⟨u, hu⟩ := exists_ne (0 : U)
  obtain ⟨p, rfl⟩ := hg u
  have hp : p ≠ 0 := fun h0 => hu (by rw [h0, map_zero])
  exact ⟨(p : M), 0, fun h0 => hp (Subtype.ext h0)⟩

/-- Transports the selected-target condition across a linear equivalence of source modules. -/
theorem auxiliaryModuleRelationOverRing.of_linearEquiv
    {M M' : Type v} [AddCommGroup M] [Module R M] [AddCommGroup M'] [Module R M']
    {U : ModuleCat.{v} R} (e : M ≃ₗ[R] M')
    (h : auxiliaryModuleRelationOverRing R (ModuleCat.of R M') U) :
    auxiliaryModuleRelationOverRing R (ModuleCat.of R M) U :=
  auxiliaryModuleRelationOverRing.of_surjective e.toLinearMap e.surjective h

/-- A selected target of a simple source is linearly equivalent to that source. -/
theorem auxiliaryModuleRelationOverRing.linearEquiv
    {M U : ModuleCat.{v} R} (hM : IsSimpleModule R M)
    (h : auxiliaryModuleRelationOverRing R M U) : Nonempty (U ≃ₗ[R] M) := by
  rw [simple_target_iff] at h
  obtain ⟨hU, P, g, hg⟩ := h
  haveI : Nontrivial U := hU.nontrivial
  have hPne : P ≠ ⊥ := by
    rintro rfl
    obtain ⟨u, hu⟩ := exists_ne (0 : U)
    obtain ⟨p, rfl⟩ := hg u
    exact hu (by rw [Subsingleton.elim p 0, map_zero])
  have hPtop : P = ⊤ := (hM.eq_bot_or_eq_top P).resolve_left hPne
  set eP : P ≃ₗ[R] M := (LinearEquiv.ofEq P ⊤ hPtop).trans Submodule.topEquiv with heP
  set θ : M →ₗ[R] U := g ∘ₗ eP.symm.toLinearMap with hθ
  have hθsurj : Function.Surjective θ := hg.comp eP.symm.surjective
  have hθinj : Function.Injective θ := by
    rw [← LinearMap.ker_eq_bot]
    refine (hM.eq_bot_or_eq_top (LinearMap.ker θ)).resolve_right (fun htop => ?_)
    obtain ⟨u, hu⟩ := exists_ne (0 : U)
    obtain ⟨m, rfl⟩ := hθsurj u
    exact hu (LinearMap.mem_ker.mp (htop ▸ Submodule.mem_top))
  exact ⟨(LinearEquiv.ofBijective θ ⟨hθinj, hθsurj⟩).symm⟩

/-- Places a selected target on either a chosen submodule or its quotient. -/
theorem auxiliaryModuleRelationOverRing.submodule_or_quotient
    {Y : Type v} [AddCommGroup Y] [Module R Y] (K : Submodule R Y)
    {U : ModuleCat.{v} R} (h : auxiliaryModuleRelationOverRing R (ModuleCat.of R Y) U) :
    auxiliaryModuleRelationOverRing R (ModuleCat.of R K) U ∨
      auxiliaryModuleRelationOverRing R (ModuleCat.of R (Y ⧸ K)) U := by
  rw [simple_target_iff] at h
  obtain ⟨hU, P, g, hg⟩ := h
  set φ : (↥(P ⊓ K)) →ₗ[R] U := g ∘ₗ Submodule.inclusion inf_le_left with hφ
  by_cases hφsurj : Function.Surjective φ
  · left
    have hfac : auxiliaryModuleRelationOverRing R
        (ModuleCat.of R (P ⊓ K : Submodule R Y)) U :=
      simple_target_iff.mpr ⟨hU, ⊤, φ ∘ₗ Submodule.topEquiv.toLinearMap,
        hφsurj.comp Submodule.topEquiv.surjective⟩
    have hfac' : auxiliaryModuleRelationOverRing R
        (ModuleCat.of R (Submodule.comap K.subtype (P ⊓ K))) U :=
      auxiliaryModuleRelationOverRing.of_linearEquiv
        (Submodule.comapSubtypeEquivOfLe inf_le_right) hfac
    exact auxiliaryModuleRelationOverRing.of_submodule
      (Submodule.comap K.subtype (P ⊓ K)) hfac'
  · right
    have hker : LinearMap.range φ = ⊥ := by
      refine (hU.eq_bot_or_eq_top _).resolve_right (fun htop => hφsurj ?_)
      rwa [← LinearMap.range_eq_top]
    set κ : (↥P) →ₗ[R] (Y ⧸ K) := K.mkQ ∘ₗ P.subtype with hκ
    set κ' : (↥P) →ₗ[R] (↥(LinearMap.range κ)) := κ.rangeRestrict with hκ'
    have hκ'surj : Function.Surjective κ' := LinearMap.surjective_rangeRestrict κ
    have hφ0 : φ = 0 := LinearMap.range_eq_bot.mp hker
    have hle : LinearMap.ker κ' ≤ LinearMap.ker g := by
      intro p hp
      have hpκ : κ p = 0 := by
        have := LinearMap.mem_ker.mp hp
        simpa [hκ', LinearMap.rangeRestrict, Subtype.ext_iff] using this
      have hpK : (p : Y) ∈ K := by
        have := hpκ
        rwa [hκ, LinearMap.comp_apply, Submodule.mkQ_apply,
          Submodule.Quotient.mk_eq_zero] at this
      rw [LinearMap.mem_ker]
      have hgp : g p = φ ⟨(p : Y), ⟨p.2, hpK⟩⟩ := rfl
      rw [hgp, hφ0, LinearMap.zero_apply]
    set ĝ : (↥(LinearMap.range κ)) →ₗ[R] U :=
      (Submodule.liftQ (LinearMap.ker κ') g hle) ∘ₗ
        (κ'.quotKerEquivOfSurjective hκ'surj).symm.toLinearMap with hĝ
    have hĝsurj : Function.Surjective ĝ := by
      rw [hĝ, LinearMap.coe_comp]
      apply Function.Surjective.comp _ (κ'.quotKerEquivOfSurjective hκ'surj).symm.surjective
      intro u
      obtain ⟨p, rfl⟩ := hg u
      exact ⟨Submodule.Quotient.mk p, by rw [Submodule.liftQ_apply]⟩
    exact simple_target_iff.mpr ⟨hU, LinearMap.range κ, ĝ, hĝsurj⟩

end RepresentationTheory.ModuleCat.Auxiliary

end CompositionFactor
