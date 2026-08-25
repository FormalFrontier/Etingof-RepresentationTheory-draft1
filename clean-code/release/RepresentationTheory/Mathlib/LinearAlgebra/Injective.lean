/-
Copyright (c) 2026 mathlib-initiative. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: mathlib-initiative
-/

import Mathlib.Algebra.Module.Injective
import Mathlib.LinearAlgebra.Quotient.Defs
import Mathlib.LinearAlgebra.Isomorphisms
import RepresentationTheory.Alignment.Attribute

namespace RepresentationTheory.Mathlib.LinearAlgebra.Injective

universe u v

/-- An injective module is exactly one for which every injective linear map from it has a retraction. -/
@[source_ref "Chapter8/Discussion_after_Exercise8.1.4" (role := supporting),
  source_ref "Chapter8/Theorem8.1.5" (role := primary)]
theorem Module.injective_iff_every_injective_map_from_splits
    (R : Type u) [Ring R]
    (I : Type v) [AddCommGroup I] [Module R I] [Small.{v} R] :
    Module.Injective R I ↔
      (∀ {M : Type v} [AddCommGroup M] [Module R M]
        (f : I →ₗ[R] M), Function.Injective f →
          ∃ g : M →ₗ[R] I, g.comp f = LinearMap.id) := by
  constructor
  · intro hI M _ _ f hf
    obtain ⟨g, hg⟩ := hI.out f hf LinearMap.id
    exact ⟨g, LinearMap.ext hg⟩
  · intro h
    constructor
    intro X Y _ _ _ _ α hα g
    set K : Submodule R (I × Y) := LinearMap.range (g.prod (-α))
    set j := K.mkQ ∘ₗ LinearMap.inl R I Y with j_def
    set k := K.mkQ ∘ₗ LinearMap.inr R I Y with k_def
    have hj : Function.Injective j := by
      intro a b hab
      simp only [j_def, LinearMap.coe_comp, Function.comp_apply, LinearMap.inl_apply] at hab
      rw [Submodule.mkQ_apply, Submodule.mkQ_apply, Submodule.Quotient.eq] at hab
      simp only [Prod.mk_sub_mk, sub_zero] at hab
      obtain ⟨x, hx⟩ := hab
      have h2 : (-α) x = 0 := congr_arg Prod.snd hx
      simp only [LinearMap.neg_apply, neg_eq_zero] at h2
      have h3 : x = 0 := hα (by rw [h2, map_zero])
      have h1 : g x = a - b := congr_arg Prod.fst hx
      rw [h3, map_zero] at h1
      exact sub_eq_zero.mp h1.symm
    obtain ⟨r, hr⟩ := h j hj
    have key : ∀ x, j (g x) = k (α x) := by
      intro x
      simp only [j_def, k_def, LinearMap.coe_comp, Function.comp_apply,
        LinearMap.inl_apply, LinearMap.inr_apply, Submodule.mkQ_apply]
      rw [Submodule.Quotient.eq]
      change (g x, (0 : Y)) - ((0 : I), α x) ∈ K
      simp only [Prod.mk_sub_mk, sub_zero, zero_sub]
      exact ⟨x, rfl⟩
    refine ⟨r.comp k, fun x => ?_⟩
    simp only [LinearMap.comp_apply]
    rw [← key x]
    exact congr_fun (congr_arg DFunLike.coe hr) (g x)

/-- Characterizes injectivity by exactness of the maps into the module associated with every short exact sequence. -/
@[source_ref "Chapter8/Discussion_after_Exercise8.1.4" (role := supporting),
  source_ref "Chapter8/Theorem8.1.5" (role := primary)]
theorem Module.injective_iff_hom_exact_on_short_exact
    (R : Type u) [Ring R]
    (I : Type v) [AddCommGroup I] [Module R I] [Small.{v} R] :
    Module.Injective R I ↔
      (∀ {K M N : Type v} [AddCommGroup K] [AddCommGroup M] [AddCommGroup N]
        [Module R K] [Module R M] [Module R N]
        (ι : K →ₗ[R] M) (π : M →ₗ[R] N),
        Function.Injective ι → Function.Surjective π →
        LinearMap.range ι = LinearMap.ker π →
        Function.Injective (fun g : N →ₗ[R] I => g ∘ₗ π) ∧
        (∀ h : M →ₗ[R] I, h ∘ₗ ι = 0 ↔ ∃ g : N →ₗ[R] I, g ∘ₗ π = h) ∧
        Function.Surjective (fun h : M →ₗ[R] I => h ∘ₗ ι)) := by
  constructor
  · intro hI K M N _ _ _ _ _ _ ι π hι hπ hexact
    have hπι : π ∘ₗ ι = 0 := by
      ext k
      have hk : ι k ∈ LinearMap.ker π := hexact ▸ LinearMap.mem_range_self ι k
      simpa [LinearMap.mem_ker] using hk
    refine ⟨?_, ?_, ?_⟩
    · intro a b hab
      ext n
      obtain ⟨m, rfl⟩ := hπ n
      simpa using LinearMap.congr_fun hab m
    · intro h
      constructor
      · intro hπh
        have hrk : LinearMap.range ι ≤ LinearMap.ker h := by
          rintro _ ⟨k, rfl⟩
          simpa [LinearMap.mem_ker] using LinearMap.congr_fun hπh k
        have hkh : LinearMap.ker π ≤ LinearMap.ker h := hexact ▸ hrk
        refine ⟨(LinearMap.ker π).liftQ h hkh ∘ₗ
          (π.quotKerEquivOfSurjective hπ).symm.toLinearMap, ?_⟩
        ext m
        simp only [LinearMap.comp_apply, LinearEquiv.coe_coe,
          LinearMap.quotKerEquivOfSurjective_symm_apply, Submodule.liftQ_apply]
      · rintro ⟨g, rfl⟩
        rw [LinearMap.comp_assoc, hπι, LinearMap.comp_zero]
    · intro f
      obtain ⟨g, hg⟩ := hI.out ι hι f
      exact ⟨g, LinearMap.ext hg⟩
  · intro hex
    constructor
    intro N M _ _ _ _ α hα ν
    obtain ⟨-, -, hsurj⟩ := hex α (LinearMap.range α).mkQ hα
      (Submodule.mkQ_surjective _) (Submodule.ker_mkQ _).symm
    obtain ⟨g, hg⟩ := hsurj ν
    exact ⟨g, fun x => by simpa using LinearMap.congr_fun hg x⟩

/-- Characterizes injective modules by Baer's condition. -/
theorem Module.injective_iff_baer
    (R : Type u) [Ring R]
    (I : Type v) [AddCommGroup I] [Module R I] [Small.{v} R] :
    Module.Injective R I ↔ Module.Baer R I := by
  exact Module.Baer.iff_injective.symm

end RepresentationTheory.Mathlib.LinearAlgebra.Injective
