/-
Copyright (c) 2026 mathlib-initiative. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: mathlib-initiative
-/

import Mathlib
import RepresentationTheory.OneDimensionalSubmoduleComplements
import RepresentationTheory.FiniteDimensionalLinearChainRepresentations
import RepresentationTheory.Alignment.Attribute

/-!
# Finite-dimensional linear-cospan representations

This module classifies indecomposable finite-dimensional representations of the
three-vertex linear cospan.
-/

namespace RepresentationTheory.FiniteDimensionalLinearCospanRepresentations

/-- A finite-dimensional representation consisting of left, center, and right vector spaces with linear maps from both outer spaces into the center. -/
structure LinearCospanRepresentation (k : Type*) [Field k] where
  /-- The left vector space of a linear-cospan representation. -/
  left : Type*
  /-- The center vector space of a linear-cospan representation. -/
  center : Type*
  /-- The right vector space of a linear-cospan representation. -/
  right : Type*
  /-- The additive commutative group structure on the left space. -/
  [leftAddCommGroup : AddCommGroup left]
  /-- The scalar module structure on the left space. -/
  [leftModule : Module k left]
  /-- The left space of a linear-cospan representation is finite-dimensional. -/
  [finiteDimensional_left : FiniteDimensional k left]
  /-- The additive commutative group structure on the center space. -/
  [centerAddCommGroup : AddCommGroup center]
  /-- The scalar module structure on the center space. -/
  [centerModule : Module k center]
  /-- The center space of a linear-cospan representation is finite-dimensional. -/
  [finiteDimensional_center : FiniteDimensional k center]
  /-- The additive commutative group structure on the right space. -/
  [rightAddCommGroup : AddCommGroup right]
  /-- The scalar module structure on the right space. -/
  [rightModule : Module k right]
  /-- The right space of a linear-cospan representation is finite-dimensional. -/
  [finiteDimensional_right : FiniteDimensional k right]
  /-- The structure map from the left space to the center space. -/
  leftToCenter : left →ₗ[k] center
  /-- The structure map from the right space to the center space. -/
  rightToCenter : right →ₗ[k] center

attribute [instance] LinearCospanRepresentation.leftAddCommGroup LinearCospanRepresentation.leftModule LinearCospanRepresentation.finiteDimensional_left
  LinearCospanRepresentation.centerAddCommGroup LinearCospanRepresentation.centerModule LinearCospanRepresentation.finiteDimensional_center
  LinearCospanRepresentation.rightAddCommGroup LinearCospanRepresentation.rightModule LinearCospanRepresentation.finiteDimensional_right

/-- The predicate that a finite-dimensional linear-cospan representation is indecomposable. -/
def LinearCospanRepresentation.IsIndecomposable {k : Type*} [Field k] (ρ : LinearCospanRepresentation k) : Prop :=
  (0 < Module.finrank k ρ.left ∨ 0 < Module.finrank k ρ.center ∨
   0 < Module.finrank k ρ.right) ∧
  ∀ (p₁ q₁ : Submodule k ρ.left) (p₂ q₂ : Submodule k ρ.center)
    (p₃ q₃ : Submodule k ρ.right),
    IsCompl p₁ q₁ → IsCompl p₂ q₂ → IsCompl p₃ q₃ →
    (∀ x ∈ p₁, ρ.leftToCenter x ∈ p₂) → (∀ x ∈ q₁, ρ.leftToCenter x ∈ q₂) →
    (∀ z ∈ p₃, ρ.rightToCenter z ∈ p₂) → (∀ z ∈ q₃, ρ.rightToCenter z ∈ q₂) →
    (p₁ = ⊥ ∧ p₂ = ⊥ ∧ p₃ = ⊥) ∨ (q₁ = ⊥ ∧ q₂ = ⊥ ∧ q₃ = ⊥)

/-- The inverse images of complementary submodules under a bijective linear map are complementary. -/
lemma isCompl_comap_of_bijective {k : Type*} [Field k]
    {V W : Type*} [AddCommGroup V] [Module k V] [AddCommGroup W] [Module k W]
    (h : V →ₗ[k] W) (hh : Function.Bijective h)
    (p q : Submodule k W) (hpq : IsCompl p q) :
    IsCompl (Submodule.comap h p) (Submodule.comap h q) := by
  constructor
  · rw [Submodule.disjoint_def]
    intro x hxp hxq
    have hmem : h x ∈ p ⊓ q := ⟨hxp, hxq⟩
    rw [hpq.1.eq_bot, Submodule.mem_bot] at hmem
    exact hh.1 (by rw [hmem, map_zero])
  · rw [codisjoint_iff]
    ext x
    simp only [Submodule.mem_sup, Submodule.mem_top, iff_true]
    have hx : h x ∈ (⊤ : Submodule k W) := Submodule.mem_top
    rw [← hpq.2.eq_top] at hx
    obtain ⟨a, ha, b, hb, hab⟩ := Submodule.mem_sup.mp hx
    obtain ⟨a', rfl⟩ := hh.2 a
    obtain ⟨b', rfl⟩ := hh.2 b
    refine ⟨a', ha, b', hb, hh.1 ?_⟩
    rw [map_add, hab]

namespace LinearCospanRepresentation

variable {k : Type*} [Field k]

private lemma top_eq_bot_of_finrank_zero {V : Type*} [AddCommGroup V] [Module k V]
    [FiniteDimensional k V] (h : Module.finrank k V = 0) : (⊤ : Submodule k V) = ⊥ :=
  Submodule.finrank_eq_zero.mp (by rw [finrank_top]; exact h)

private lemma finrank_zero_of_top_eq_bot {V : Type*} [AddCommGroup V] [Module k V]
    [FiniteDimensional k V] (h : (⊤ : Submodule k V) = ⊥) : Module.finrank k V = 0 := by
  rw [← finrank_top (R := k) (M := V), h, finrank_bot]

private lemma ker_f_or (ρ : LinearCospanRepresentation k) (hind : ρ.IsIndecomposable) :
    LinearMap.ker ρ.leftToCenter = ⊥ ∨
      (Module.finrank k ρ.center = 0 ∧ Module.finrank k ρ.right = 0) := by
  by_contra h
  push Not at h
  obtain ⟨hker, hrest⟩ := h
  obtain ⟨q₁, hq₁⟩ := Submodule.exists_isCompl (LinearMap.ker ρ.leftToCenter)
  have hres := hind.2 (LinearMap.ker ρ.leftToCenter) q₁ ⊥ ⊤ ⊥ ⊤ hq₁ isCompl_bot_top isCompl_bot_top
    (fun x hx => by simp [LinearMap.mem_ker.mp hx])
    (fun _ _ => Submodule.mem_top)
    (fun z hz => by rw [(Submodule.mem_bot (R := k)).mp hz, map_zero]; exact Submodule.zero_mem _)
    (fun _ _ => Submodule.mem_top)
  rcases hres with ⟨hk, _, _⟩ | ⟨_, h2, h3⟩
  · exact hker hk
  · exact hrest (finrank_zero_of_top_eq_bot h2) (finrank_zero_of_top_eq_bot h3)

private lemma ker_g_or (ρ : LinearCospanRepresentation k) (hind : ρ.IsIndecomposable) :
    LinearMap.ker ρ.rightToCenter = ⊥ ∨
      (Module.finrank k ρ.center = 0 ∧ Module.finrank k ρ.left = 0) := by
  by_contra h
  push Not at h
  obtain ⟨hker, hrest⟩ := h
  obtain ⟨q₃, hq₃⟩ := Submodule.exists_isCompl (LinearMap.ker ρ.rightToCenter)
  have hres := hind.2 ⊥ ⊤ ⊥ ⊤ (LinearMap.ker ρ.rightToCenter) q₃ isCompl_bot_top isCompl_bot_top hq₃
    (fun x hx => by rw [(Submodule.mem_bot (R := k)).mp hx, map_zero]; exact Submodule.zero_mem _)
    (fun _ _ => Submodule.mem_top)
    (fun z hz => by simp [LinearMap.mem_ker.mp hz])
    (fun _ _ => Submodule.mem_top)
  rcases hres with ⟨_, _, hk⟩ | ⟨h1, h2, _⟩
  · exact hker hk
  · exact hrest (finrank_zero_of_top_eq_bot h2) (finrank_zero_of_top_eq_bot h1)

private lemma range_sup_or (ρ : LinearCospanRepresentation k) (hind : ρ.IsIndecomposable) :
    LinearMap.range ρ.leftToCenter ⊔ LinearMap.range ρ.rightToCenter = ⊤ ∨
      (Module.finrank k ρ.left = 0 ∧ Module.finrank k ρ.right = 0) := by
  by_contra h
  push Not at h
  obtain ⟨hsup, hrest⟩ := h
  obtain ⟨T, hT⟩ := Submodule.exists_isCompl (LinearMap.range ρ.leftToCenter ⊔ LinearMap.range ρ.rightToCenter)
  have hres := hind.2 ⊤ ⊥ (LinearMap.range ρ.leftToCenter ⊔ LinearMap.range ρ.rightToCenter) T ⊤ ⊥
    isCompl_top_bot hT isCompl_top_bot
    (fun x _ => Submodule.mem_sup_left (LinearMap.mem_range_self ρ.leftToCenter x))
    (fun x hx => by rw [(Submodule.mem_bot (R := k)).mp hx, map_zero]; exact Submodule.zero_mem _)
    (fun z _ => Submodule.mem_sup_right (LinearMap.mem_range_self ρ.rightToCenter z))
    (fun z hz => by rw [(Submodule.mem_bot (R := k)).mp hz, map_zero]; exact Submodule.zero_mem _)
  rcases hres with ⟨h1, _, h3⟩ | ⟨_, hTbot, _⟩
  · exact hrest (finrank_zero_of_top_eq_bot h1) (finrank_zero_of_top_eq_bot h3)
  · exact hsup (eq_top_of_isCompl_bot (hTbot ▸ hT))

private lemma V₂_zero_cases (ρ : LinearCospanRepresentation k) (hind : ρ.IsIndecomposable)
    (h₂ : Module.finrank k ρ.center = 0) :
    (Module.finrank k ρ.left = 1 ∧ Module.finrank k ρ.right = 0) ∨
    (Module.finrank k ρ.left = 0 ∧ Module.finrank k ρ.right = 1) := by
  obtain ⟨hnt, hind_cond⟩ := hind
  have hV₂zero : ∀ y : ρ.center, y = 0 :=
    RepresentationTheory.FiniteDimensionalLinearChainRepresentations.eq_zero_of_finrank_eq_zero
      ρ.center h₂
  -- One of the outer vertices is zero.
  have houter : Module.finrank k ρ.left = 0 ∨ Module.finrank k ρ.right = 0 := by
    have hres := hind_cond ⊤ ⊥ ⊥ ⊤ ⊥ ⊤ isCompl_top_bot isCompl_bot_top isCompl_bot_top
      (fun x _ => by rw [hV₂zero (ρ.leftToCenter x)]; exact Submodule.zero_mem _)
      (fun _ _ => Submodule.mem_top)
      (fun z _ => by rw [hV₂zero (ρ.rightToCenter z)]; exact Submodule.zero_mem _)
      (fun _ _ => Submodule.mem_top)
    rcases hres with ⟨h1, _, _⟩ | ⟨_, _, h3⟩
    · exact Or.inl (finrank_zero_of_top_eq_bot h1)
    · exact Or.inr (finrank_zero_of_top_eq_bot h3)
  rcases houter with h₁ | h₃
  · -- `left = 0`, so `right` carries the whole representation.
    have hV₁zero : ∀ x : ρ.left, x = 0 :=
      RepresentationTheory.FiniteDimensionalLinearChainRepresentations.eq_zero_of_finrank_eq_zero
        ρ.left h₁
    have h₃pos : 0 < Module.finrank k ρ.right := by omega
    refine Or.inr ⟨h₁, ?_⟩
    rw [← RepresentationTheory.OneDimensionalSubmoduleComplements.nontrivial_and_isCompl_eq_bot_iff_finrank_eq_one]
    refine ⟨Module.nontrivial_of_finrank_pos h₃pos, fun p₃ q₃ hpq₃ => ?_⟩
    have hres := hind_cond ⊥ ⊤ ⊥ ⊤ p₃ q₃ isCompl_bot_top isCompl_bot_top hpq₃
      (fun x _ => by rw [hV₂zero (ρ.leftToCenter x)]; exact Submodule.zero_mem _)
      (fun _ _ => Submodule.mem_top)
      (fun z _ => by rw [hV₂zero (ρ.rightToCenter z)]; exact Submodule.zero_mem _)
      (fun _ _ => Submodule.mem_top)
    rcases hres with ⟨_, _, hp⟩ | ⟨_, _, hq⟩
    · exact Or.inl hp
    · exact Or.inr hq
  · -- `right = 0`, so `left` carries the whole representation.
    have hV₃zero : ∀ z : ρ.right, z = 0 :=
      RepresentationTheory.FiniteDimensionalLinearChainRepresentations.eq_zero_of_finrank_eq_zero
        ρ.right h₃
    have h₁pos : 0 < Module.finrank k ρ.left := by omega
    refine Or.inl ⟨?_, h₃⟩
    rw [← RepresentationTheory.OneDimensionalSubmoduleComplements.nontrivial_and_isCompl_eq_bot_iff_finrank_eq_one]
    refine ⟨Module.nontrivial_of_finrank_pos h₁pos, fun p₁ q₁ hpq₁ => ?_⟩
    have hres := hind_cond p₁ q₁ ⊥ ⊤ ⊥ ⊤ hpq₁ isCompl_bot_top isCompl_bot_top
      (fun x _ => by rw [hV₂zero (ρ.leftToCenter x)]; exact Submodule.zero_mem _)
      (fun _ _ => Submodule.mem_top)
      (fun z _ => by rw [hV₂zero (ρ.rightToCenter z)]; exact Submodule.zero_mem _)
      (fun _ _ => Submodule.mem_top)
    rcases hres with ⟨hp, _, _⟩ | ⟨hq, _, _⟩
    · exact Or.inl hp
    · exact Or.inr hq

private lemma V₂_dim_one_of_outer_zero (ρ : LinearCospanRepresentation k) (hind : ρ.IsIndecomposable)
    (h₁ : Module.finrank k ρ.left = 0) (h₃ : Module.finrank k ρ.right = 0)
    (h₂ : 0 < Module.finrank k ρ.center) : Module.finrank k ρ.center = 1 := by
  obtain ⟨_, hind_cond⟩ := hind
  have hV₁zero : ∀ x : ρ.left, x = 0 :=
    RepresentationTheory.FiniteDimensionalLinearChainRepresentations.eq_zero_of_finrank_eq_zero
      ρ.left h₁
  have hV₃zero : ∀ z : ρ.right, z = 0 :=
    RepresentationTheory.FiniteDimensionalLinearChainRepresentations.eq_zero_of_finrank_eq_zero
      ρ.right h₃
  rw [← RepresentationTheory.OneDimensionalSubmoduleComplements.nontrivial_and_isCompl_eq_bot_iff_finrank_eq_one]
  refine ⟨Module.nontrivial_of_finrank_pos h₂, fun p₂ q₂ hpq₂ => ?_⟩
  have hres := hind_cond ⊥ ⊤ p₂ q₂ ⊥ ⊤ isCompl_bot_top hpq₂ isCompl_bot_top
    (fun x _ => by rw [hV₁zero x, map_zero]; exact Submodule.zero_mem _)
    (fun x _ => by rw [hV₁zero x, map_zero]; exact Submodule.zero_mem _)
    (fun z _ => by rw [hV₃zero z, map_zero]; exact Submodule.zero_mem _)
    (fun z _ => by rw [hV₃zero z, map_zero]; exact Submodule.zero_mem _)
  rcases hres with ⟨_, hp, _⟩ | ⟨_, hq, _⟩
  · exact Or.inl hp
  · exact Or.inr hq

/--
An indecomposable linear-cospan representation has one of six displayed zero-one dimension
triples; whenever an outer space and the center are both one-dimensional, the corresponding
outer-to-center map is bijective.
-/
theorem _root_.RepresentationTheory.FiniteDimensionalLinearCospanRepresentations.isIndecomposable_dimension_cases (k : Type*) [Field k] (ρ : LinearCospanRepresentation k)
    (hind : ρ.IsIndecomposable) :
    (Module.finrank k ρ.left = 1 ∧ Module.finrank k ρ.center = 0 ∧
      Module.finrank k ρ.right = 0) ∨
    (Module.finrank k ρ.left = 0 ∧ Module.finrank k ρ.center = 1 ∧
      Module.finrank k ρ.right = 0) ∨
    (Module.finrank k ρ.left = 0 ∧ Module.finrank k ρ.center = 0 ∧
      Module.finrank k ρ.right = 1) ∨
    (Module.finrank k ρ.left = 1 ∧ Module.finrank k ρ.center = 1 ∧
      Module.finrank k ρ.right = 0 ∧ Function.Bijective ρ.leftToCenter) ∨
    (Module.finrank k ρ.left = 0 ∧ Module.finrank k ρ.center = 1 ∧
      Module.finrank k ρ.right = 1 ∧ Function.Bijective ρ.rightToCenter) ∨
    (Module.finrank k ρ.left = 1 ∧ Module.finrank k ρ.center = 1 ∧
      Module.finrank k ρ.right = 1 ∧ Function.Bijective ρ.leftToCenter ∧
      Function.Bijective ρ.rightToCenter) := by
  have hkerf := ker_f_or ρ hind
  have hkerg := ker_g_or ρ hind
  have hsup := range_sup_or ρ hind
  obtain ⟨hnt, hind_cond⟩ := hind
  have hind' : ρ.IsIndecomposable := ⟨hnt, hind_cond⟩
  rcases Nat.eq_zero_or_pos (Module.finrank k ρ.center) with h₂ | h₂
  · -- The middle space vanishes.
    rcases V₂_zero_cases ρ hind' h₂ with ⟨h1, h3⟩ | ⟨h1, h3⟩
    · exact Or.inl ⟨h1, h₂, h3⟩
    · exact Or.inr (Or.inr (Or.inl ⟨h1, h₂, h3⟩))
  · -- The middle space is nonzero, so both maps are injective.
    have hf_inj : Function.Injective ρ.leftToCenter :=
      LinearMap.ker_eq_bot.mp (hkerf.resolve_right (fun h => absurd h.1 h₂.ne'))
    have hg_inj : Function.Injective ρ.rightToCenter :=
      LinearMap.ker_eq_bot.mp (hkerg.resolve_right (fun h => absurd h.1 h₂.ne'))
    rcases hsup with hsup | ⟨h₁, h₃⟩
    swap
    · -- Both outer spaces vanish: the middle vertex simple.
      exact Or.inr (Or.inl ⟨h₁, V₂_dim_one_of_outer_zero ρ hind' h₁ h₃ h₂, h₃⟩)
    -- The images of `f` and `g` span `center`.
    by_cases hD : LinearMap.range ρ.leftToCenter ⊓ LinearMap.range ρ.rightToCenter = ⊥
    · -- The two subspaces are complementary: the representation splits off one outer vertex.
      have hUW : IsCompl (LinearMap.range ρ.leftToCenter) (LinearMap.range ρ.rightToCenter) :=
        ⟨disjoint_iff.mpr hD, codisjoint_iff.mpr hsup⟩
      have hres := hind_cond ⊤ ⊥ (LinearMap.range ρ.leftToCenter) (LinearMap.range ρ.rightToCenter) ⊥ ⊤
        isCompl_top_bot hUW isCompl_bot_top
        (fun x _ => LinearMap.mem_range_self ρ.leftToCenter x)
        (fun x hx => by
          rw [(Submodule.mem_bot (R := k)).mp hx, map_zero]; exact Submodule.zero_mem _)
        (fun z hz => by
          rw [(Submodule.mem_bot (R := k)).mp hz, map_zero]; exact Submodule.zero_mem _)
        (fun z _ => LinearMap.mem_range_self ρ.rightToCenter z)
      rcases hres with ⟨h1, hU, _⟩ | ⟨_, hW, h3⟩
      · -- `left = 0` and `range f = ⊥`, so `g` is bijective.
        have h₁ : Module.finrank k ρ.left = 0 := finrank_zero_of_top_eq_bot h1
        have hgtop : LinearMap.range ρ.rightToCenter = ⊤ := by
          rw [← hsup, hU, bot_sup_eq]
        have hg_bij : Function.Bijective ρ.rightToCenter := ⟨hg_inj, LinearMap.range_eq_top.mp hgtop⟩
        have hdim : Module.finrank k ρ.right = Module.finrank k ρ.center :=
          (LinearEquiv.ofBijective ρ.rightToCenter hg_bij).finrank_eq
        -- `center` is one-dimensional, transporting decompositions along `g`.
        have hV₂dim1 : Module.finrank k ρ.center = 1 := by
          rw [← RepresentationTheory.OneDimensionalSubmoduleComplements.nontrivial_and_isCompl_eq_bot_iff_finrank_eq_one]
          refine ⟨Module.nontrivial_of_finrank_pos h₂, fun p₂ q₂ hpq₂ => ?_⟩
          have hV₁zero : ∀ x : ρ.left, x = 0 :=
            RepresentationTheory.FiniteDimensionalLinearChainRepresentations.eq_zero_of_finrank_eq_zero
              ρ.left h₁
          have hpq₃ := isCompl_comap_of_bijective ρ.rightToCenter hg_bij p₂ q₂ hpq₂
          have h := hind_cond ⊥ ⊤ p₂ q₂ (Submodule.comap ρ.rightToCenter p₂) (Submodule.comap ρ.rightToCenter q₂)
            isCompl_bot_top hpq₂ hpq₃
            (fun x _ => by rw [hV₁zero x, map_zero]; exact Submodule.zero_mem _)
            (fun x _ => by rw [hV₁zero x, map_zero]; exact Submodule.zero_mem _)
            (fun z hz => hz) (fun z hz => hz)
          rcases h with ⟨_, hp, _⟩ | ⟨_, hq, _⟩
          · exact Or.inl hp
          · exact Or.inr hq
        exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨h₁, hV₂dim1, by omega, hg_bij⟩))))
      · -- `right = 0` and `range g = ⊥`, so `f` is bijective.
        have h₃ : Module.finrank k ρ.right = 0 := finrank_zero_of_top_eq_bot h3
        have hftop : LinearMap.range ρ.leftToCenter = ⊤ := by
          rw [← hsup, hW, sup_bot_eq]
        have hf_bij : Function.Bijective ρ.leftToCenter := ⟨hf_inj, LinearMap.range_eq_top.mp hftop⟩
        have hdim : Module.finrank k ρ.left = Module.finrank k ρ.center :=
          (LinearEquiv.ofBijective ρ.leftToCenter hf_bij).finrank_eq
        have hV₂dim1 : Module.finrank k ρ.center = 1 := by
          rw [← RepresentationTheory.OneDimensionalSubmoduleComplements.nontrivial_and_isCompl_eq_bot_iff_finrank_eq_one]
          refine ⟨Module.nontrivial_of_finrank_pos h₂, fun p₂ q₂ hpq₂ => ?_⟩
          have hV₃zero : ∀ z : ρ.right, z = 0 :=
            RepresentationTheory.FiniteDimensionalLinearChainRepresentations.eq_zero_of_finrank_eq_zero
              ρ.right h₃
          have hpq₁ := isCompl_comap_of_bijective ρ.leftToCenter hf_bij p₂ q₂ hpq₂
          have h := hind_cond (Submodule.comap ρ.leftToCenter p₂) (Submodule.comap ρ.leftToCenter q₂) p₂ q₂ ⊥ ⊤
            hpq₁ hpq₂ isCompl_bot_top
            (fun x hx => hx) (fun x hx => hx)
            (fun z _ => by rw [hV₃zero z, map_zero]; exact Submodule.zero_mem _)
            (fun z _ => by rw [hV₃zero z, map_zero]; exact Submodule.zero_mem _)
          rcases h with ⟨_, hp, _⟩ | ⟨_, hq, _⟩
          · exact Or.inl hp
          · exact Or.inr hq
        exact Or.inr (Or.inr (Or.inr (Or.inl ⟨by omega, hV₂dim1, h₃, hf_bij⟩)))
    · -- The two subspaces meet: the representation is the `(1,1,1)` one.
      -- Split `center` as `(range f ⊓ range g) ⊕ (f Q₁ ⊔ g Q₃)`.
      obtain ⟨Q₁, hQ₁⟩ :=
        Submodule.exists_isCompl (Submodule.comap ρ.leftToCenter (LinearMap.range ρ.leftToCenter ⊓ LinearMap.range ρ.rightToCenter))
      obtain ⟨Q₃, hQ₃⟩ :=
        Submodule.exists_isCompl (Submodule.comap ρ.rightToCenter (LinearMap.range ρ.leftToCenter ⊓ LinearMap.range ρ.rightToCenter))
      set D := LinearMap.range ρ.leftToCenter ⊓ LinearMap.range ρ.rightToCenter with hDdef
      set Q₂ := Submodule.map ρ.leftToCenter Q₁ ⊔ Submodule.map ρ.rightToCenter Q₃ with hQ₂def
      have hDQ₂ : IsCompl D Q₂ := by
        constructor
        · rw [Submodule.disjoint_def]
          intro z hzD hzQ₂
          obtain ⟨a, ha, b, hb, hab⟩ := Submodule.mem_sup.mp hzQ₂
          obtain ⟨x, hx, rfl⟩ := Submodule.mem_map.mp ha
          obtain ⟨y, hy, rfl⟩ := Submodule.mem_map.mp hb
          -- `f x` lies in both images, hence in `D`, forcing `x = 0`.
          have hfxW : ρ.leftToCenter x ∈ LinearMap.range ρ.rightToCenter := by
            have hsubs : ρ.leftToCenter x = z - ρ.rightToCenter y := eq_sub_of_add_eq hab
            rw [hsubs]
            exact Submodule.sub_mem _ hzD.2 (LinearMap.mem_range_self ρ.rightToCenter y)
          have hxmem : x ∈ Submodule.comap ρ.leftToCenter D ⊓ Q₁ :=
            ⟨⟨LinearMap.mem_range_self ρ.leftToCenter x, hfxW⟩, hx⟩
          rw [hQ₁.1.eq_bot, Submodule.mem_bot] at hxmem
          rw [hxmem, map_zero, zero_add] at hab
          -- Now `z = g y` lies in `D`, forcing `y = 0`.
          have hyD : ρ.rightToCenter y ∈ D := by rw [hab]; exact hzD
          have hymem : y ∈ Submodule.comap ρ.rightToCenter D ⊓ Q₃ := ⟨hyD, hy⟩
          rw [hQ₃.1.eq_bot, Submodule.mem_bot] at hymem
          rw [hymem, map_zero] at hab
          exact hab.symm
        · rw [codisjoint_iff]
          have hUle : LinearMap.range ρ.leftToCenter ≤ D ⊔ Q₂ := by
            rintro _ ⟨x, rfl⟩
            have hx : x ∈ (⊤ : Submodule k ρ.left) := Submodule.mem_top
            rw [← hQ₁.2.eq_top] at hx
            obtain ⟨u, hu, v, hv, huv⟩ := Submodule.mem_sup.mp hx
            rw [← huv, map_add]
            exact Submodule.add_mem _ (Submodule.mem_sup_left hu)
              (Submodule.mem_sup_right (Submodule.mem_sup_left (Submodule.mem_map_of_mem hv)))
          have hWle : LinearMap.range ρ.rightToCenter ≤ D ⊔ Q₂ := by
            rintro _ ⟨z, rfl⟩
            have hz : z ∈ (⊤ : Submodule k ρ.right) := Submodule.mem_top
            rw [← hQ₃.2.eq_top] at hz
            obtain ⟨u, hu, v, hv, huv⟩ := Submodule.mem_sup.mp hz
            rw [← huv, map_add]
            exact Submodule.add_mem _ (Submodule.mem_sup_left hu)
              (Submodule.mem_sup_right (Submodule.mem_sup_right (Submodule.mem_map_of_mem hv)))
          exact top_le_iff.mp (hsup ▸ sup_le hUle hWle)
      have hres := hind_cond (Submodule.comap ρ.leftToCenter D) Q₁ D Q₂ (Submodule.comap ρ.rightToCenter D) Q₃
        hQ₁ hDQ₂ hQ₃
        (fun x hx => hx) (fun x hx => Submodule.mem_sup_left (Submodule.mem_map_of_mem hx))
        (fun z hz => hz) (fun z hz => Submodule.mem_sup_right (Submodule.mem_map_of_mem hz))
      rcases hres with ⟨_, hDbot, _⟩ | ⟨_, hQ₂bot, _⟩
      · exact absurd hDbot hD
      · -- `D = ⊤`, so both maps are surjective.
        have hDtop : D = ⊤ := eq_top_of_isCompl_bot (hQ₂bot ▸ hDQ₂)
        have hftop : LinearMap.range ρ.leftToCenter = ⊤ :=
          top_le_iff.mp (hDtop ▸ (inf_le_left : D ≤ LinearMap.range ρ.leftToCenter))
        have hgtop : LinearMap.range ρ.rightToCenter = ⊤ :=
          top_le_iff.mp (hDtop ▸ (inf_le_right : D ≤ LinearMap.range ρ.rightToCenter))
        have hf_bij : Function.Bijective ρ.leftToCenter := ⟨hf_inj, LinearMap.range_eq_top.mp hftop⟩
        have hg_bij : Function.Bijective ρ.rightToCenter := ⟨hg_inj, LinearMap.range_eq_top.mp hgtop⟩
        have hdim₁ : Module.finrank k ρ.left = Module.finrank k ρ.center :=
          (LinearEquiv.ofBijective ρ.leftToCenter hf_bij).finrank_eq
        have hdim₃ : Module.finrank k ρ.right = Module.finrank k ρ.center :=
          (LinearEquiv.ofBijective ρ.rightToCenter hg_bij).finrank_eq
        have hV₂ : Module.finrank k ρ.center = 1 := by
          rw [← RepresentationTheory.OneDimensionalSubmoduleComplements.nontrivial_and_isCompl_eq_bot_iff_finrank_eq_one]
          refine ⟨Module.nontrivial_of_finrank_pos h₂, fun p₂ q₂ hpq₂ => ?_⟩
          have hpq₁ := isCompl_comap_of_bijective ρ.leftToCenter hf_bij p₂ q₂ hpq₂
          have hpq₃ := isCompl_comap_of_bijective ρ.rightToCenter hg_bij p₂ q₂ hpq₂
          have h := hind_cond (Submodule.comap ρ.leftToCenter p₂) (Submodule.comap ρ.leftToCenter q₂) p₂ q₂
            (Submodule.comap ρ.rightToCenter p₂) (Submodule.comap ρ.rightToCenter q₂) hpq₁ hpq₂ hpq₃
            (fun x hx => hx) (fun x hx => hx) (fun z hz => hz) (fun z hz => hz)
          rcases h with ⟨_, hp, _⟩ | ⟨_, hq, _⟩
          · exact Or.inl hp
          · exact Or.inr hq
        exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr
          ⟨by omega, hV₂, by omega, hf_bij, hg_bij⟩))))

end LinearCospanRepresentation

open Module

/-- An equivalence between two finite-dimensional linear-cospan representations. -/
structure LinearCospanRepresentation.Equiv {k : Type*} [Field k] (ρ σ : LinearCospanRepresentation k) where
  /-- The linear equivalence between the left spaces of two equivalent representations. -/
  leftLinearEquiv : ρ.left ≃ₗ[k] σ.left
  /-- The linear equivalence between the center spaces of two equivalent representations. -/
  centerLinearEquiv : ρ.center ≃ₗ[k] σ.center
  /-- The linear equivalence between the right spaces of two equivalent representations. -/
  rightLinearEquiv : ρ.right ≃ₗ[k] σ.right
  /-- The left and center equivalences intertwine the left-to-center structure maps. -/
  leftToCenter_comm_apply : ∀ x, centerLinearEquiv (ρ.leftToCenter x) = σ.leftToCenter (leftLinearEquiv x)
  /-- The right and center equivalences intertwine the right-to-center structure maps. -/
  rightToCenter_comm_apply : ∀ z, centerLinearEquiv (ρ.rightToCenter z) = σ.rightToCenter (rightLinearEquiv z)

namespace LinearCospanRepresentation.Equiv

/-- The identity equivalence of a linear-cospan representation. -/
def refl {k : Type*} [Field k] (ρ : LinearCospanRepresentation k) : ρ.Equiv ρ where
  leftLinearEquiv := LinearEquiv.refl k ρ.left
  centerLinearEquiv := LinearEquiv.refl k ρ.center
  rightLinearEquiv := LinearEquiv.refl k ρ.right
  leftToCenter_comm_apply := fun _ => rfl
  rightToCenter_comm_apply := fun _ => rfl

/-- Reverses an equivalence of linear-cospan representations. -/
def symm {k : Type*} [Field k] {ρ σ : LinearCospanRepresentation k} (e : ρ.Equiv σ) : σ.Equiv ρ where
  leftLinearEquiv := e.leftLinearEquiv.symm
  centerLinearEquiv := e.centerLinearEquiv.symm
  rightLinearEquiv := e.rightLinearEquiv.symm
  leftToCenter_comm_apply := fun y => by
    apply e.centerLinearEquiv.injective
    rw [e.centerLinearEquiv.apply_symm_apply, e.leftToCenter_comm_apply, e.leftLinearEquiv.apply_symm_apply]
  rightToCenter_comm_apply := fun y => by
    apply e.centerLinearEquiv.injective
    rw [e.centerLinearEquiv.apply_symm_apply, e.rightToCenter_comm_apply, e.rightLinearEquiv.apply_symm_apply]

/-- Composes two equivalences of linear-cospan representations. -/
def trans {k : Type*} [Field k] {ρ σ τ : LinearCospanRepresentation k} (e : ρ.Equiv σ) (e' : σ.Equiv τ) :
    ρ.Equiv τ where
  leftLinearEquiv := e.leftLinearEquiv.trans e'.leftLinearEquiv
  centerLinearEquiv := e.centerLinearEquiv.trans e'.centerLinearEquiv
  rightLinearEquiv := e.rightLinearEquiv.trans e'.rightLinearEquiv
  leftToCenter_comm_apply := fun x => by
    simp only [LinearEquiv.trans_apply]
    rw [e.leftToCenter_comm_apply, e'.leftToCenter_comm_apply]
  rightToCenter_comm_apply := fun z => by
    simp only [LinearEquiv.trans_apply]
    rw [e.rightToCenter_comm_apply, e'.rightToCenter_comm_apply]

/-- A representation equivalence preserves the finranks of the left, center, and right spaces. -/
lemma finrank_eq {k : Type*} [Field k] {ρ σ : LinearCospanRepresentation k} (e : ρ.Equiv σ) :
    Module.finrank k ρ.left = Module.finrank k σ.left ∧
    Module.finrank k ρ.center = Module.finrank k σ.center ∧
    Module.finrank k ρ.right = Module.finrank k σ.right :=
  ⟨e.leftLinearEquiv.finrank_eq, e.centerLinearEquiv.finrank_eq, e.rightLinearEquiv.finrank_eq⟩

end LinearCospanRepresentation.Equiv

/-- A standard linear-cospan representation of dimension triple `(1, 0, 0)`. -/
abbrev LinearCospanRepresentation.oneZeroZeroModel (k : Type*) [Field k] : LinearCospanRepresentation k where
  left := k
  center := PUnit
  right := PUnit
  leftToCenter := 0
  rightToCenter := 0

/-- A standard linear-cospan representation of dimension triple `(0, 1, 0)`. -/
abbrev LinearCospanRepresentation.zeroOneZeroModel (k : Type*) [Field k] : LinearCospanRepresentation k where
  left := PUnit
  center := k
  right := PUnit
  leftToCenter := 0
  rightToCenter := 0

/-- A standard linear-cospan representation of dimension triple `(0, 0, 1)`. -/
abbrev LinearCospanRepresentation.zeroZeroOneModel (k : Type*) [Field k] : LinearCospanRepresentation k where
  left := PUnit
  center := PUnit
  right := k
  leftToCenter := 0
  rightToCenter := 0

/-- A standard linear-cospan representation of dimension triple `(1, 1, 0)`. -/
abbrev LinearCospanRepresentation.oneOneZeroModel (k : Type*) [Field k] : LinearCospanRepresentation k where
  left := k
  center := k
  right := PUnit
  leftToCenter := LinearMap.id
  rightToCenter := 0

/-- A standard linear-cospan representation of dimension triple `(0, 1, 1)`. -/
abbrev LinearCospanRepresentation.zeroOneOneModel (k : Type*) [Field k] : LinearCospanRepresentation k where
  left := PUnit
  center := k
  right := k
  leftToCenter := 0
  rightToCenter := LinearMap.id

/-- A standard linear-cospan representation of dimension triple `(1, 1, 1)`. -/
abbrev LinearCospanRepresentation.oneOneOneModel (k : Type*) [Field k] : LinearCospanRepresentation k where
  left := k
  center := k
  right := k
  leftToCenter := LinearMap.id
  rightToCenter := LinearMap.id

namespace LinearCospanRepresentation

/-- Every submodule of a subsingleton module is the bottom submodule. -/
theorem submodule_eq_bot_of_subsingleton {k M : Type*} [Field k] [AddCommGroup M] [Module k M]
    [Subsingleton M] (p : Submodule k M) : p = ⊥ := by
  rw [eq_bot_iff]; intro x _; rw [Submodule.mem_bot]; exact Subsingleton.elim _ _

/-- The standard model of dimension triple `(1, 0, 0)` is indecomposable. -/
theorem oneZeroZeroModel_isIndecomposable (k : Type*) [Field k] : (oneZeroZeroModel k).IsIndecomposable := by
  refine ⟨Or.inl Module.finrank_pos, ?_⟩
  intro p₁ q₁ p₂ q₂ p₃ q₃ hpq₁ _ _ _ _ _ _
  have hsum : Module.finrank k p₁ + Module.finrank k q₁ = 1 := by
    rw [Submodule.finrank_add_eq_of_isCompl hpq₁]; exact finrank_self k
  rcases Nat.eq_zero_or_pos (Module.finrank k p₁) with h0 | hpos
  · exact Or.inl ⟨Submodule.finrank_eq_zero.mp h0, submodule_eq_bot_of_subsingleton p₂,
      submodule_eq_bot_of_subsingleton p₃⟩
  · exact Or.inr ⟨Submodule.finrank_eq_zero.mp (by omega), submodule_eq_bot_of_subsingleton q₂,
      submodule_eq_bot_of_subsingleton q₃⟩

/-- The standard model of dimension triple `(0, 1, 0)` is indecomposable. -/
theorem zeroOneZeroModel_isIndecomposable (k : Type*) [Field k] : (zeroOneZeroModel k).IsIndecomposable := by
  refine ⟨Or.inr (Or.inl Module.finrank_pos), ?_⟩
  intro p₁ q₁ p₂ q₂ p₃ q₃ _ hpq₂ _ _ _ _ _
  have hsum : Module.finrank k p₂ + Module.finrank k q₂ = 1 := by
    rw [Submodule.finrank_add_eq_of_isCompl hpq₂]; exact finrank_self k
  rcases Nat.eq_zero_or_pos (Module.finrank k p₂) with h0 | hpos
  · exact Or.inl ⟨submodule_eq_bot_of_subsingleton p₁, Submodule.finrank_eq_zero.mp h0,
      submodule_eq_bot_of_subsingleton p₃⟩
  · exact Or.inr ⟨submodule_eq_bot_of_subsingleton q₁, Submodule.finrank_eq_zero.mp (by omega),
      submodule_eq_bot_of_subsingleton q₃⟩

/-- The standard model of dimension triple `(0, 0, 1)` is indecomposable. -/
theorem zeroZeroOneModel_isIndecomposable (k : Type*) [Field k] : (zeroZeroOneModel k).IsIndecomposable := by
  refine ⟨Or.inr (Or.inr Module.finrank_pos), ?_⟩
  intro p₁ q₁ p₂ q₂ p₃ q₃ _ _ hpq₃ _ _ _ _
  have hsum : Module.finrank k p₃ + Module.finrank k q₃ = 1 := by
    rw [Submodule.finrank_add_eq_of_isCompl hpq₃]; exact finrank_self k
  rcases Nat.eq_zero_or_pos (Module.finrank k p₃) with h0 | hpos
  · exact Or.inl ⟨submodule_eq_bot_of_subsingleton p₁, submodule_eq_bot_of_subsingleton p₂,
      Submodule.finrank_eq_zero.mp h0⟩
  · exact Or.inr ⟨submodule_eq_bot_of_subsingleton q₁, submodule_eq_bot_of_subsingleton q₂,
      Submodule.finrank_eq_zero.mp (by omega)⟩

/-- The standard model of dimension triple `(1, 1, 0)` is indecomposable. -/
theorem oneOneZeroModel_isIndecomposable (k : Type*) [Field k] : (oneOneZeroModel k).IsIndecomposable := by
  refine ⟨Or.inl Module.finrank_pos, ?_⟩
  intro p₁ q₁ p₂ q₂ p₃ q₃ hpq₁ hpq₂ _ hfp hfq _ _
  have hsum₁ : Module.finrank k p₁ + Module.finrank k q₁ = 1 := by
    rw [Submodule.finrank_add_eq_of_isCompl hpq₁]; exact finrank_self k
  have hsum₂ : Module.finrank k p₂ + Module.finrank k q₂ = 1 := by
    rw [Submodule.finrank_add_eq_of_isCompl hpq₂]; exact finrank_self k
  have hfp' : Module.finrank k p₁ ≤ Module.finrank k p₂ :=
    Submodule.finrank_mono (fun x hx => by simpa using hfp x hx)
  have hfq' : Module.finrank k q₁ ≤ Module.finrank k q₂ :=
    Submodule.finrank_mono (fun x hx => by simpa using hfq x hx)
  rcases Nat.eq_zero_or_pos (Module.finrank k p₁) with h0 | hpos
  · exact Or.inl ⟨Submodule.finrank_eq_zero.mp h0, Submodule.finrank_eq_zero.mp (by omega),
      submodule_eq_bot_of_subsingleton p₃⟩
  · exact Or.inr ⟨Submodule.finrank_eq_zero.mp (by omega),
      Submodule.finrank_eq_zero.mp (by omega), submodule_eq_bot_of_subsingleton q₃⟩

/-- The standard model of dimension triple `(0, 1, 1)` is indecomposable. -/
theorem zeroOneOneModel_isIndecomposable (k : Type*) [Field k] : (zeroOneOneModel k).IsIndecomposable := by
  refine ⟨Or.inr (Or.inl Module.finrank_pos), ?_⟩
  intro p₁ q₁ p₂ q₂ p₃ q₃ _ hpq₂ hpq₃ _ _ hgp hgq
  have hsum₂ : Module.finrank k p₂ + Module.finrank k q₂ = 1 := by
    rw [Submodule.finrank_add_eq_of_isCompl hpq₂]; exact finrank_self k
  have hsum₃ : Module.finrank k p₃ + Module.finrank k q₃ = 1 := by
    rw [Submodule.finrank_add_eq_of_isCompl hpq₃]; exact finrank_self k
  have hgp' : Module.finrank k p₃ ≤ Module.finrank k p₂ :=
    Submodule.finrank_mono (fun z hz => by simpa using hgp z hz)
  have hgq' : Module.finrank k q₃ ≤ Module.finrank k q₂ :=
    Submodule.finrank_mono (fun z hz => by simpa using hgq z hz)
  rcases Nat.eq_zero_or_pos (Module.finrank k p₃) with h0 | hpos
  · exact Or.inl ⟨submodule_eq_bot_of_subsingleton p₁,
      Submodule.finrank_eq_zero.mp (by omega), Submodule.finrank_eq_zero.mp h0⟩
  · exact Or.inr ⟨submodule_eq_bot_of_subsingleton q₁,
      Submodule.finrank_eq_zero.mp (by omega), Submodule.finrank_eq_zero.mp (by omega)⟩

/-- The standard model of dimension triple `(1, 1, 1)` is indecomposable. -/
theorem oneOneOneModel_isIndecomposable (k : Type*) [Field k] : (oneOneOneModel k).IsIndecomposable := by
  refine ⟨Or.inl Module.finrank_pos, ?_⟩
  intro p₁ q₁ p₂ q₂ p₃ q₃ hpq₁ hpq₂ hpq₃ hfp hfq hgp hgq
  have hsum₁ : Module.finrank k p₁ + Module.finrank k q₁ = 1 := by
    rw [Submodule.finrank_add_eq_of_isCompl hpq₁]; exact finrank_self k
  have hsum₂ : Module.finrank k p₂ + Module.finrank k q₂ = 1 := by
    rw [Submodule.finrank_add_eq_of_isCompl hpq₂]; exact finrank_self k
  have hsum₃ : Module.finrank k p₃ + Module.finrank k q₃ = 1 := by
    rw [Submodule.finrank_add_eq_of_isCompl hpq₃]; exact finrank_self k
  have hfp' : Module.finrank k p₁ ≤ Module.finrank k p₂ :=
    Submodule.finrank_mono (fun x hx => by simpa using hfp x hx)
  have hfq' : Module.finrank k q₁ ≤ Module.finrank k q₂ :=
    Submodule.finrank_mono (fun x hx => by simpa using hfq x hx)
  have hgp' : Module.finrank k p₃ ≤ Module.finrank k p₂ :=
    Submodule.finrank_mono (fun z hz => by simpa using hgp z hz)
  have hgq' : Module.finrank k q₃ ≤ Module.finrank k q₂ :=
    Submodule.finrank_mono (fun z hz => by simpa using hgq z hz)
  rcases Nat.eq_zero_or_pos (Module.finrank k p₁) with h0 | hpos
  · exact Or.inl ⟨Submodule.finrank_eq_zero.mp h0, Submodule.finrank_eq_zero.mp (by omega),
      Submodule.finrank_eq_zero.mp (by omega)⟩
  · exact Or.inr ⟨Submodule.finrank_eq_zero.mp (by omega),
      Submodule.finrank_eq_zero.mp (by omega), Submodule.finrank_eq_zero.mp (by omega)⟩

/-- The six-element indexed family of standard linear-cospan representations. -/
def standardModel (k : Type*) [Field k] : Fin 6 → LinearCospanRepresentation k
  | 0 => oneZeroZeroModel k
  | 1 => zeroOneZeroModel k
  | 2 => zeroZeroOneModel k
  | 3 => oneOneZeroModel k
  | 4 => zeroOneOneModel k
  | 5 => oneOneOneModel k

/-- Every member of the six-element family of standard models is indecomposable. -/
@[source_ref "Chapter6/Example6.2.4" (role := primary)]
theorem standardModel_isIndecomposable (k : Type*) [Field k] (i : Fin 6) : (standardModel k i).IsIndecomposable := by
  fin_cases i
  · exact oneZeroZeroModel_isIndecomposable k
  · exact zeroOneZeroModel_isIndecomposable k
  · exact zeroZeroOneModel_isIndecomposable k
  · exact oneOneZeroModel_isIndecomposable k
  · exact zeroOneOneModel_isIndecomposable k
  · exact oneOneOneModel_isIndecomposable k

/-- The ordered triple of left, center, and right dimensions of a linear-cospan representation. -/
noncomputable def dimension (k : Type*) [Field k] (σ : LinearCospanRepresentation k) : ℕ × ℕ × ℕ :=
  (Module.finrank k σ.left, Module.finrank k σ.center, Module.finrank k σ.right)

/-- Equivalent linear-cospan representations have the same ordered triple of dimensions. -/
theorem Equiv.dimension_eq {k : Type*} [Field k] {ρ σ : LinearCospanRepresentation k} (e : ρ.Equiv σ) :
    dimension k ρ = dimension k σ := by
  obtain ⟨h₁, h₂, h₃⟩ := e.finrank_eq
  simp [dimension, h₁, h₂, h₃]

/-- The corresponding standard model has dimension triple `(1, 0, 0)`. -/
theorem oneZeroZeroModel_dimension (k : Type*) [Field k] : dimension k (oneZeroZeroModel k) = (1, 0, 0) := by
  simp [dimension, finrank_self, finrank_zero_of_subsingleton]

/-- The corresponding standard model has dimension triple `(0, 1, 0)`. -/
theorem zeroOneZeroModel_dimension (k : Type*) [Field k] : dimension k (zeroOneZeroModel k) = (0, 1, 0) := by
  simp [dimension, finrank_self, finrank_zero_of_subsingleton]

/-- The corresponding standard model has dimension triple `(0, 0, 1)`. -/
theorem zeroZeroOneModel_dimension (k : Type*) [Field k] : dimension k (zeroZeroOneModel k) = (0, 0, 1) := by
  simp [dimension, finrank_self, finrank_zero_of_subsingleton]

/-- The corresponding standard model has dimension triple `(1, 1, 0)`. -/
theorem oneOneZeroModel_dimension (k : Type*) [Field k] : dimension k (oneOneZeroModel k) = (1, 1, 0) := by
  simp [dimension, finrank_self, finrank_zero_of_subsingleton]

/-- The corresponding standard model has dimension triple `(0, 1, 1)`. -/
theorem zeroOneOneModel_dimension (k : Type*) [Field k] : dimension k (zeroOneOneModel k) = (0, 1, 1) := by
  simp [dimension, finrank_self, finrank_zero_of_subsingleton]

/-- The corresponding standard model has dimension triple `(1, 1, 1)`. -/
theorem oneOneOneModel_dimension (k : Type*) [Field k] : dimension k (oneOneOneModel k) = (1, 1, 1) := by
  simp [dimension, finrank_self]

/-- Every indecomposable linear-cospan representation is equivalent to a unique member of the six-element family of standard models. -/
@[source_ref "Chapter6/Example6.2.4" (role := supporting)]
theorem existsUnique_equiv_standardModel_of_isIndecomposable (k : Type*) [Field k] (ρ : LinearCospanRepresentation k)
    (hind : ρ.IsIndecomposable) : ∃! i : Fin 6, Nonempty (ρ.Equiv (standardModel k i)) := by
  have hexists : ∃ i : Fin 6, Nonempty (ρ.Equiv (standardModel k i)) := by
    rcases _root_.RepresentationTheory.FiniteDimensionalLinearCospanRepresentations.isIndecomposable_dimension_cases k ρ hind with
      ⟨h1, h2, h3⟩ | ⟨h1, h2, h3⟩ | ⟨h1, h2, h3⟩ | ⟨h1, h2, h3, hf⟩ | ⟨h1, h2, h3, hg⟩ |
        ⟨h1, h2, h3, hf, hg⟩
    · refine ⟨0, ?_⟩
      change Nonempty (ρ.Equiv (oneZeroZeroModel k))
      exact ⟨{ leftLinearEquiv := (FiniteDimensional.nonempty_linearEquiv_of_finrank_eq
                  (by rw [h1]; exact (finrank_self k).symm)).some
               centerLinearEquiv := (FiniteDimensional.nonempty_linearEquiv_of_finrank_eq
                  (by rw [h2]; exact finrank_zero_of_subsingleton.symm)).some
               rightLinearEquiv := (FiniteDimensional.nonempty_linearEquiv_of_finrank_eq
                  (by rw [h3]; exact finrank_zero_of_subsingleton.symm)).some
               leftToCenter_comm_apply := fun _ => Subsingleton.elim _ _
               rightToCenter_comm_apply := fun _ => Subsingleton.elim _ _ }⟩
    · refine ⟨1, ?_⟩
      change Nonempty (ρ.Equiv (zeroOneZeroModel k))
      haveI hs₁ : Subsingleton ρ.left := Module.finrank_zero_iff.mp h1
      haveI hs₃ : Subsingleton ρ.right := Module.finrank_zero_iff.mp h3
      exact ⟨{ leftLinearEquiv := (FiniteDimensional.nonempty_linearEquiv_of_finrank_eq
                  (by rw [h1]; exact finrank_zero_of_subsingleton.symm)).some
               centerLinearEquiv := (FiniteDimensional.nonempty_linearEquiv_of_finrank_eq
                  (by rw [h2]; exact (finrank_self k).symm)).some
               rightLinearEquiv := (FiniteDimensional.nonempty_linearEquiv_of_finrank_eq
                  (by rw [h3]; exact finrank_zero_of_subsingleton.symm)).some
               leftToCenter_comm_apply := fun x => by rw [Subsingleton.elim x 0]; simp
               rightToCenter_comm_apply := fun z => by rw [Subsingleton.elim z 0]; simp }⟩
    · refine ⟨2, ?_⟩
      change Nonempty (ρ.Equiv (zeroZeroOneModel k))
      exact ⟨{ leftLinearEquiv := (FiniteDimensional.nonempty_linearEquiv_of_finrank_eq
                  (by rw [h1]; exact finrank_zero_of_subsingleton.symm)).some
               centerLinearEquiv := (FiniteDimensional.nonempty_linearEquiv_of_finrank_eq
                  (by rw [h2]; exact finrank_zero_of_subsingleton.symm)).some
               rightLinearEquiv := (FiniteDimensional.nonempty_linearEquiv_of_finrank_eq
                  (by rw [h3]; exact (finrank_self k).symm)).some
               leftToCenter_comm_apply := fun _ => Subsingleton.elim _ _
               rightToCenter_comm_apply := fun _ => Subsingleton.elim _ _ }⟩
    · refine ⟨3, ?_⟩
      change Nonempty (ρ.Equiv (oneOneZeroModel k))
      haveI hs₃ : Subsingleton ρ.right := Module.finrank_zero_iff.mp h3
      obtain ⟨leftLinearEquiv⟩ := FiniteDimensional.nonempty_linearEquiv_of_finrank_eq
        (R := k) (M := ρ.left) (M' := k) (by rw [h1]; exact (finrank_self k).symm)
      let fEq : ρ.left ≃ₗ[k] ρ.center := LinearEquiv.ofBijective ρ.leftToCenter hf
      refine ⟨{ leftLinearEquiv := leftLinearEquiv, centerLinearEquiv := fEq.symm.trans leftLinearEquiv, rightLinearEquiv := ?_
                leftToCenter_comm_apply := fun x => ?_
                rightToCenter_comm_apply := fun z => by rw [Subsingleton.elim z 0]; simp }⟩
      · exact (FiniteDimensional.nonempty_linearEquiv_of_finrank_eq
          (by rw [h3]; exact finrank_zero_of_subsingleton.symm)).some
      · have hfx : fEq.symm (ρ.leftToCenter x) = x := fEq.symm_apply_apply x
        simp only [LinearEquiv.trans_apply, hfx]
        rfl
    · refine ⟨4, ?_⟩
      change Nonempty (ρ.Equiv (zeroOneOneModel k))
      haveI hs₁ : Subsingleton ρ.left := Module.finrank_zero_iff.mp h1
      obtain ⟨rightLinearEquiv⟩ := FiniteDimensional.nonempty_linearEquiv_of_finrank_eq
        (R := k) (M := ρ.right) (M' := k) (by rw [h3]; exact (finrank_self k).symm)
      let gEq : ρ.right ≃ₗ[k] ρ.center := LinearEquiv.ofBijective ρ.rightToCenter hg
      refine ⟨{ leftLinearEquiv := ?_, centerLinearEquiv := gEq.symm.trans rightLinearEquiv, rightLinearEquiv := rightLinearEquiv
                leftToCenter_comm_apply := fun x => by rw [Subsingleton.elim x 0]; simp
                rightToCenter_comm_apply := fun z => ?_ }⟩
      · exact (FiniteDimensional.nonempty_linearEquiv_of_finrank_eq
          (by rw [h1]; exact finrank_zero_of_subsingleton.symm)).some
      · have hgz : gEq.symm (ρ.rightToCenter z) = z := gEq.symm_apply_apply z
        simp only [LinearEquiv.trans_apply, hgz]
        rfl
    · refine ⟨5, ?_⟩
      change Nonempty (ρ.Equiv (oneOneOneModel k))
      obtain ⟨centerLinearEquiv⟩ := FiniteDimensional.nonempty_linearEquiv_of_finrank_eq
        (R := k) (M := ρ.center) (M' := (oneOneOneModel k).center) (by rw [h2]; exact (finrank_self k).symm)
      let fEq : ρ.left ≃ₗ[k] ρ.center := LinearEquiv.ofBijective ρ.leftToCenter hf
      let gEq : ρ.right ≃ₗ[k] ρ.center := LinearEquiv.ofBijective ρ.rightToCenter hg
      exact ⟨{ leftLinearEquiv := fEq.trans centerLinearEquiv, centerLinearEquiv := centerLinearEquiv, rightLinearEquiv := gEq.trans centerLinearEquiv
               leftToCenter_comm_apply := fun x => by simp only [LinearEquiv.trans_apply]; rfl
               rightToCenter_comm_apply := fun z => by simp only [LinearEquiv.trans_apply]; rfl }⟩
  obtain ⟨i, hi⟩ := hexists
  refine ⟨i, hi, fun j hj => ?_⟩
  obtain ⟨ei⟩ := hi
  obtain ⟨ej⟩ := hj
  have hdv : dimension k (standardModel k j) = dimension k (standardModel k i) := (ej.symm.trans ei).dimension_eq
  fin_cases i <;> fin_cases j <;>
    simp_all [standardModel, oneZeroZeroModel_dimension, zeroOneZeroModel_dimension, zeroZeroOneModel_dimension, oneOneZeroModel_dimension,
      zeroOneOneModel_dimension, oneOneOneModel_dimension]

end LinearCospanRepresentation

end RepresentationTheory.FiniteDimensionalLinearCospanRepresentations
