/-
Copyright (c) 2026 mathlib-initiative. All rights reserved.
Released under Apache 2.0 license as described in the file LICENCE.
Authors: mathlib-initiative
-/

import Mathlib.Algebra.Module.Projective
import Mathlib.RingTheory.Flat.Basic
import Mathlib.LinearAlgebra.FreeModule.Basic
import RepresentationTheory.Alignment.Attribute

namespace RepresentationTheory.Mathlib.LinearAlgebra.Projective

universe u v

/-- A module is projective exactly when every surjective linear map onto it has a linear section. -/
@[source_ref "Chapter8/Theorem8.1.1" (role := primary)]
theorem Module.Projective.iff_surjective_has_section
    (R : Type u) [Ring R]
    (P : Type v) [AddCommGroup P] [Module R P] [Small.{v} R] :
    Module.Projective R P ↔
      (∀ {M : Type v} [AddCommGroup M] [Module R M]
        (f : M →ₗ[R] P), Function.Surjective f →
          ∃ g : P →ₗ[R] M, f.comp g = LinearMap.id) := by
  constructor
  · intro hP M _ _ f hf
    exact LinearMap.exists_rightInverse_of_surjective f (LinearMap.range_eq_top.mpr hf)
  · intro h
    refine Module.Projective.of_lifting_property'' (fun p hp ↦ ?_)
    let e := Finsupp.mapRange.linearEquiv (α := P) (Shrink.linearEquiv R R)
    obtain ⟨g, hg⟩ := h (p ∘ₗ e.toLinearMap) (hp.comp e.surjective)
    exact ⟨e.toLinearMap ∘ₗ g, hg⟩

/-- A module is projective exactly when it is a retract of a suitable module. -/
@[source_ref "Chapter8/Theorem8.1.1" (role := primary)]
theorem Module.Projective.iff_exists_retract
    (R : Type u) [Ring R]
    (P : Type v) [AddCommGroup P] [Module R P] :
    Module.Projective R P ↔
      (∃ (Q : Type (max u v)) (_ : AddCommGroup Q) (_ : Module R Q)
        (_ : Module.Free R Q) (i : P →ₗ[R] Q) (s : Q →ₗ[R] P),
          s.comp i = LinearMap.id) := by
  constructor
  · intro hP
    obtain ⟨s, hs⟩ := hP.out
    exact ⟨P →₀ R, inferInstance, inferInstance, inferInstance, s,
      Finsupp.linearCombination R id, LinearMap.ext hs⟩
  · intro ⟨_, _, _, _, i, s, his⟩
    exact Module.Projective.of_split i s his

/-- A module is projective exactly when applying linear maps from it preserves the displayed short exact sequence conditions. -/
@[source_ref "Chapter8/Theorem8.1.1" (role := primary)]
theorem Module.Projective.iff_hom_preserves_short_exact
    (R : Type u) [Ring R]
    (P : Type v) [AddCommGroup P] [Module R P] [Small.{v} R] :
    Module.Projective R P ↔
      (∀ {K M N : Type v} [AddCommGroup K] [AddCommGroup M] [AddCommGroup N]
        [Module R K] [Module R M] [Module R N]
        (ι : K →ₗ[R] M) (π : M →ₗ[R] N),
        Function.Injective ι → Function.Surjective π →
        LinearMap.range ι = LinearMap.ker π →
        Function.Injective (fun g : P →ₗ[R] K => ι ∘ₗ g) ∧
        (∀ h : P →ₗ[R] M, π ∘ₗ h = 0 ↔ ∃ g : P →ₗ[R] K, ι ∘ₗ g = h) ∧
        Function.Surjective (fun h : P →ₗ[R] M => π ∘ₗ h)) := by
  constructor
  · intro hP K M N _ _ _ _ _ _ ι π hι hπ hexact
    haveI := hP
    have hπι : π ∘ₗ ι = 0 := by
      ext k
      have hk : ι k ∈ LinearMap.ker π := hexact ▸ LinearMap.mem_range_self ι k
      simpa [LinearMap.mem_ker] using hk
    refine ⟨?_, ?_, ?_⟩
    · intro g g' hgg'
      ext p
      exact hι (LinearMap.congr_fun hgg' p)
    · intro h
      constructor
      · intro hπh
        have hpf : ∀ p, h p ∈ LinearMap.range ι := by
          intro p
          rw [hexact, LinearMap.mem_ker]
          simpa using LinearMap.congr_fun hπh p
        refine ⟨(LinearEquiv.ofInjective ι hι).symm.toLinearMap ∘ₗ
          LinearMap.codRestrict (LinearMap.range ι) h hpf, ?_⟩
        ext p
        simp
      · rintro ⟨g, rfl⟩
        rw [← LinearMap.comp_assoc, hπι, LinearMap.zero_comp]
    · intro h'
      exact Module.projective_lifting_property π h' hπ
  · intro hex
    refine Module.Projective.of_lifting_property'' (fun p hp ↦ ?_)
    let e := Finsupp.mapRange.linearEquiv (α := P) (Shrink.linearEquiv R R)
    let f := p ∘ₗ e.toLinearMap
    let ι : ↥(LinearMap.ker f) →ₗ[R] (P →₀ Shrink.{v} R) := (LinearMap.ker f).subtype
    have hfsurj : Function.Surjective f := hp.comp e.surjective
    have hι : Function.Injective ι := Subtype.coe_injective
    have hexact : LinearMap.range ι = LinearMap.ker f := Submodule.range_subtype _
    obtain ⟨-, -, hsurj⟩ :=
      hex (K := ↥(LinearMap.ker f)) (M := P →₀ Shrink.{v} R) (N := P) ι f hι hfsurj hexact
    obtain ⟨h, hh⟩ := hsurj LinearMap.id
    refine ⟨e.toLinearMap ∘ₗ h, ?_⟩
    rw [← LinearMap.comp_assoc]
    exact hh

end RepresentationTheory.Mathlib.LinearAlgebra.Projective
