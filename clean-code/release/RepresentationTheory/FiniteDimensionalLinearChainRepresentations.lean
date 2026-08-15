/-
Copyright (c) 2026 mathlib-initiative. All rights reserved.
Released under Apache 2.0 license as described in the file LICENCE.
Authors: mathlib-initiative
-/

import Mathlib
import RepresentationTheory.OneDimensionalSubmoduleComplements
import RepresentationTheory.FiniteDimensionalLinearMapRepresentations

/-!
# Finite-dimensional linear-chain representations

This module defines finite-dimensional representations consisting of three vector spaces and two
successive linear maps, and classifies their possible dimensions when they are indecomposable.
-/

namespace RepresentationTheory.FiniteDimensionalLinearChainRepresentations

/-- A finite-dimensional representation consisting of three vector spaces over a field and two successive linear maps. -/
structure LinearChainRepresentation (k : Type*) [Field k] where
  /-- The left vector space of a linear-chain representation. -/
  left : Type*
  /-- The middle vector space of a linear-chain representation. -/
  middle : Type*
  /-- The right vector space of a linear-chain representation. -/
  right : Type*
  /-- The additive commutative group structure on the left space. -/
  [leftAddCommGroup : AddCommGroup left]
  /-- The scalar module structure on the left space. -/
  [leftModule : Module k left]
  /-- The left space of a linear-chain representation is finite-dimensional. -/
  [finiteDimensional_left : FiniteDimensional k left]
  /-- The additive commutative group structure on the middle space. -/
  [middleAddCommGroup : AddCommGroup middle]
  /-- The scalar module structure on the middle space. -/
  [middleModule : Module k middle]
  /-- The middle space of a linear-chain representation is finite-dimensional. -/
  [finiteDimensional_middle : FiniteDimensional k middle]
  /-- The additive commutative group structure on the right space. -/
  [rightAddCommGroup : AddCommGroup right]
  /-- The scalar module structure on the right space. -/
  [rightModule : Module k right]
  /-- The right space of a linear-chain representation is finite-dimensional. -/
  [finiteDimensional_right : FiniteDimensional k right]
  /-- The linear map from the left space to the middle space. -/
  leftToMiddle : left →ₗ[k] middle
  /-- The linear map from the middle space to the right space. -/
  middleToRight : middle →ₗ[k] right

attribute [instance] LinearChainRepresentation.leftAddCommGroup
  LinearChainRepresentation.leftModule LinearChainRepresentation.finiteDimensional_left
  LinearChainRepresentation.middleAddCommGroup LinearChainRepresentation.middleModule
  LinearChainRepresentation.finiteDimensional_middle LinearChainRepresentation.rightAddCommGroup
  LinearChainRepresentation.rightModule LinearChainRepresentation.finiteDimensional_right

/-- The predicate that a finite-dimensional linear-chain representation is indecomposable. -/
def LinearChainRepresentation.IsIndecomposable {k : Type*} [Field k]
    (ρ : LinearChainRepresentation k) : Prop :=
  (0 < Module.finrank k ρ.left ∨ 0 < Module.finrank k ρ.middle ∨
   0 < Module.finrank k ρ.right) ∧
  ∀ (p₁ q₁ : Submodule k ρ.left) (p₂ q₂ : Submodule k ρ.middle)
    (p₃ q₃ : Submodule k ρ.right),
    IsCompl p₁ q₁ → IsCompl p₂ q₂ → IsCompl p₃ q₃ →
    (∀ x ∈ p₁, ρ.leftToMiddle x ∈ p₂) → (∀ x ∈ q₁, ρ.leftToMiddle x ∈ q₂) →
    (∀ x ∈ p₂, ρ.middleToRight x ∈ p₃) → (∀ x ∈ q₂, ρ.middleToRight x ∈ q₃) →
    (p₁ = ⊥ ∧ p₂ = ⊥ ∧ p₃ = ⊥) ∨ (q₁ = ⊥ ∧ q₂ = ⊥ ∧ q₃ = ⊥)

/-- Every element of a finite-dimensional vector space of dimension zero is zero. -/
lemma eq_zero_of_finrank_eq_zero {k : Type*} [Field k]
    (V : Type*) [AddCommGroup V] [Module k V] [FiniteDimensional k V]
    (h : Module.finrank k V = 0) (x : V) : x = 0 := by
  have htop : (⊤ : Submodule k V) = ⊥ :=
    Submodule.finrank_eq_zero.mp (by rw [finrank_top]; exact h)
  have hx : x ∈ (⊤ : Submodule k V) := Submodule.mem_top
  rwa [htop, Submodule.mem_bot] at hx

private lemma exists_isCompl_containing {k : Type*} [Field k]
    {V : Type*} [AddCommGroup V] [Module k V] [FiniteDimensional k V]
    (A B : Submodule k V) (h : Disjoint A B) :
    ∃ C : Submodule k V, IsCompl A C ∧ B ≤ C := by
  obtain ⟨C₀, hC₀⟩ := Submodule.exists_isCompl (A ⊔ B)
  refine ⟨B ⊔ C₀, ?_, le_sup_left⟩
  constructor
  · rw [Submodule.disjoint_def]
    intro x hxA hxBC
    obtain ⟨b, hb, c, hc, hbc⟩ := Submodule.mem_sup.mp hxBC
    -- x = b + c, so c = x - b ∈ A ⊔ B
    have hc_AB : c ∈ A ⊔ B := by
      have hceq : c = x - b := eq_sub_of_add_eq' hbc
      rw [hceq]; exact (A ⊔ B).sub_mem (Submodule.mem_sup_left hxA) (Submodule.mem_sup_right hb)
    have : c ∈ (A ⊔ B) ⊓ C₀ := ⟨hc_AB, hc⟩
    rw [hC₀.1.eq_bot, Submodule.mem_bot] at this
    rw [this, add_zero] at hbc
    have : x ∈ A ⊓ B := ⟨hxA, hbc ▸ hb⟩
    rw [h.eq_bot, Submodule.mem_bot] at this
    exact this
  · rw [codisjoint_iff]
    calc A ⊔ (B ⊔ C₀) = (A ⊔ B) ⊔ C₀ := by rw [sup_assoc]
    _ = ⊤ := hC₀.2.eq_top

/-- A bijective linear map sends complementary submodules to complementary submodules. -/
lemma isCompl_map_of_bijective {k : Type*} [Field k]
    {V W : Type*} [AddCommGroup V] [Module k V] [AddCommGroup W] [Module k W]
    (g : V →ₗ[k] W) (hg : Function.Bijective g)
    (p q : Submodule k V) (hpq : IsCompl p q) :
    IsCompl (Submodule.map g p) (Submodule.map g q) := by
  constructor
  · rw [Submodule.disjoint_def]
    intro z hz₁ hz₂
    obtain ⟨y₁, hy₁, rfl⟩ := Submodule.mem_map.mp hz₁
    obtain ⟨y₂, hy₂, h_eq⟩ := Submodule.mem_map.mp hz₂
    have heq : y₁ = y₂ := hg.1 h_eq.symm
    rw [heq] at hy₁
    have hmem : y₂ ∈ p ⊓ q := ⟨hy₁, hy₂⟩
    rw [hpq.1.eq_bot, Submodule.mem_bot] at hmem
    rw [heq, hmem, map_zero]
  · rw [codisjoint_iff]; ext z
    simp only [Submodule.mem_sup, Submodule.mem_top, iff_true]
    obtain ⟨y, rfl⟩ := hg.2 z
    have : y ∈ (⊤ : Submodule k V) := Submodule.mem_top
    rw [← hpq.2.eq_top] at this
    obtain ⟨a, ha, b, hb, hab⟩ := Submodule.mem_sup.mp this
    exact ⟨g a, Submodule.mem_map.mpr ⟨a, ha, rfl⟩,
           g b, Submodule.mem_map.mpr ⟨b, hb, rfl⟩,
           by rw [← map_add, hab]⟩

private lemma a3_V₂_zero {k : Type*} [Field k] (ρ : LinearChainRepresentation k)
    (hind : ρ.IsIndecomposable) (h₂ : Module.finrank k ρ.middle = 0) :
    (Module.finrank k ρ.left = 1 ∧ Module.finrank k ρ.right = 0) ∨
    (Module.finrank k ρ.left = 0 ∧ Module.finrank k ρ.right = 1) := by
  obtain ⟨hnt, hind_cond⟩ := hind
  have hV₂z : ∀ y : ρ.middle, y = 0 := eq_zero_of_finrank_eq_zero ρ.middle h₂
  rcases Nat.eq_zero_or_pos (Module.finrank k ρ.left) with h₁ | h₁ <;>
    rcases Nat.eq_zero_or_pos (Module.finrank k ρ.right) with h₃ | h₃
  · exfalso; omega
  · right; refine ⟨h₁, ?_⟩
    rw [← RepresentationTheory.OneDimensionalSubmoduleComplements.nontrivial_and_isCompl_eq_bot_iff_finrank_eq_one]
    refine ⟨Module.nontrivial_of_finrank_pos h₃, fun p₃ q₃ hpq₃ => ?_⟩
    have := hind_cond ⊥ ⊤ ⊥ ⊤ p₃ q₃ isCompl_bot_top isCompl_bot_top hpq₃
      (fun x hx => by rw [(Submodule.mem_bot (R := k)).mp hx, map_zero]; exact Submodule.zero_mem _)
      (fun _ _ => Submodule.mem_top)
      (fun x _ => by rw [hV₂z x, map_zero]; exact p₃.zero_mem)
      (fun x _ => by rw [hV₂z x, map_zero]; exact q₃.zero_mem)
    rcases this with ⟨_, _, h⟩ | ⟨_, _, h⟩
    · left; exact h
    · right; exact h
  · left; refine ⟨?_, h₃⟩
    rw [← RepresentationTheory.OneDimensionalSubmoduleComplements.nontrivial_and_isCompl_eq_bot_iff_finrank_eq_one]
    refine ⟨Module.nontrivial_of_finrank_pos h₁, fun p₁ q₁ hpq₁ => ?_⟩
    have := hind_cond p₁ q₁ ⊥ ⊤ ⊥ ⊤ hpq₁ isCompl_bot_top isCompl_bot_top
      (fun x _ => by rw [hV₂z (ρ.leftToMiddle x)]; exact Submodule.zero_mem _)
      (fun _ _ => Submodule.mem_top)
      (fun x hx => by rw [(Submodule.mem_bot (R := k)).mp hx, map_zero]; exact Submodule.zero_mem _)
      (fun _ _ => Submodule.mem_top)
    rcases this with ⟨h, _, _⟩ | ⟨h, _, _⟩
    · left; exact h
    · right; exact h
  · exfalso
    have := hind_cond ⊤ ⊥ ⊥ ⊤ ⊥ ⊤ isCompl_top_bot isCompl_bot_top isCompl_bot_top
      (fun x _ => by rw [hV₂z (ρ.leftToMiddle x)]; exact Submodule.zero_mem _)
      (fun x hx => by rw [(Submodule.mem_bot (R := k)).mp hx, map_zero]; exact Submodule.mem_top)
      (fun x hx => by rw [(Submodule.mem_bot (R := k)).mp hx, map_zero]; exact Submodule.zero_mem _)
      (fun _ _ => Submodule.mem_top)
    rcases this with ⟨htop, _, _⟩ | ⟨_, _, htop⟩
    · rw [← finrank_top (R := k) (M := ρ.left), htop, finrank_bot] at h₁; omega
    · rw [← finrank_top (R := k) (M := ρ.right), htop, finrank_bot] at h₃; omega

private lemma a3_V₁_zero {k : Type*} [Field k] (ρ : LinearChainRepresentation k)
    (hind : ρ.IsIndecomposable) (h₁ : Module.finrank k ρ.left = 0) :
    (Module.finrank k ρ.middle = 1 ∧ Module.finrank k ρ.right = 0) ∨
    (Module.finrank k ρ.middle = 0 ∧ Module.finrank k ρ.right = 1) ∨
    (Module.finrank k ρ.middle = 1 ∧ Module.finrank k ρ.right = 1 ∧
      Function.Injective ρ.middleToRight) := by
  obtain ⟨hnt, hind_cond⟩ := hind
  have hV₁z : ∀ x : ρ.left, x = 0 := eq_zero_of_finrank_eq_zero ρ.left h₁
  have hA₂ : (RepresentationTheory.FiniteDimensionalLinearMapRepresentations.LinearMapRepresentation.mk
      ρ.middle ρ.right ρ.middleToRight).IsIndecomposable := by
    refine ⟨?_, fun p₂ q₂ p₃ q₃ hpq₂ hpq₃ hfp hfq => ?_⟩
    · rcases hnt with h | h | h
      · omega
      · left; exact h
      · right; exact h
    · have := hind_cond ⊥ ⊤ p₂ q₂ p₃ q₃ isCompl_bot_top hpq₂ hpq₃
        (fun x hx => by rw [(Submodule.mem_bot (R := k)).mp hx, map_zero]; exact p₂.zero_mem)
        (fun x _ => by rw [hV₁z x, map_zero]; exact q₂.zero_mem)
        hfp hfq
      rcases this with ⟨_, h₂, h₃⟩ | ⟨_, h₂, h₃⟩
      · left; exact ⟨h₂, h₃⟩
      · right; exact ⟨h₂, h₃⟩
  exact RepresentationTheory.FiniteDimensionalLinearMapRepresentations.isIndecomposable_dimension_cases
    k (RepresentationTheory.FiniteDimensionalLinearMapRepresentations.LinearMapRepresentation.mk
      ρ.middle ρ.right ρ.middleToRight) hA₂

private lemma a3_V₃_zero {k : Type*} [Field k] (ρ : LinearChainRepresentation k)
    (hind : ρ.IsIndecomposable) (h₃ : Module.finrank k ρ.right = 0) :
    (Module.finrank k ρ.left = 1 ∧ Module.finrank k ρ.middle = 0) ∨
    (Module.finrank k ρ.left = 0 ∧ Module.finrank k ρ.middle = 1) ∨
    (Module.finrank k ρ.left = 1 ∧ Module.finrank k ρ.middle = 1 ∧
      Function.Injective ρ.leftToMiddle) := by
  obtain ⟨hnt, hind_cond⟩ := hind
  have hV₃z : ∀ x : ρ.right, x = 0 := eq_zero_of_finrank_eq_zero ρ.right h₃
  have hA₂ : (RepresentationTheory.FiniteDimensionalLinearMapRepresentations.LinearMapRepresentation.mk
      ρ.left ρ.middle ρ.leftToMiddle).IsIndecomposable := by
    refine ⟨?_, fun p₁ q₁ p₂ q₂ hpq₁ hpq₂ hfp hfq => ?_⟩
    · rcases hnt with h | h | h
      · left; exact h
      · right; exact h
      · omega
    · have := hind_cond p₁ q₁ p₂ q₂ ⊥ ⊤ hpq₁ hpq₂ isCompl_bot_top
        hfp hfq
        (fun x _ => by rw [hV₃z (ρ.middleToRight x)]; exact Submodule.zero_mem _)
        (fun _ _ => Submodule.mem_top)
      rcases this with ⟨h₁, h₂, _⟩ | ⟨h₁, h₂, _⟩
      · left; exact ⟨h₁, h₂⟩
      · right; exact ⟨h₁, h₂⟩
  exact RepresentationTheory.FiniteDimensionalLinearMapRepresentations.isIndecomposable_dimension_cases
    k (RepresentationTheory.FiniteDimensionalLinearMapRepresentations.LinearMapRepresentation.mk
      ρ.left ρ.middle ρ.leftToMiddle) hA₂

private lemma a3_ker_f {k : Type*} [Field k] (ρ : LinearChainRepresentation k)
    (hind : ρ.IsIndecomposable) :
    LinearMap.ker ρ.leftToMiddle = ⊥ ∨
    (Module.finrank k ρ.middle = 0 ∧ Module.finrank k ρ.right = 0) := by
  by_contra h; push Not at h; obtain ⟨hker, hV₂₃⟩ := h
  obtain ⟨_, hind_cond⟩ := hind
  obtain ⟨q₁, hq₁⟩ := Submodule.exists_isCompl (LinearMap.ker ρ.leftToMiddle)
  have := hind_cond (LinearMap.ker ρ.leftToMiddle) q₁ ⊥ ⊤ ⊥ ⊤ hq₁ isCompl_bot_top isCompl_bot_top
    (fun x hx => by rw [LinearMap.mem_ker.mp hx]; exact Submodule.zero_mem _)
    (fun _ _ => Submodule.mem_top)
    (fun x hx => by rw [(Submodule.mem_bot (R := k)).mp hx, map_zero]; exact Submodule.zero_mem _)
    (fun _ _ => Submodule.mem_top)
  rcases this with ⟨hk, _, _⟩ | ⟨_, htop₂, htop₃⟩
  · exact hker hk
  · have h₂ : Module.finrank k ρ.middle = 0 := by
      rw [← finrank_top (R := k) (M := ρ.middle), htop₂, finrank_bot]
    have h₃ : Module.finrank k ρ.right = 0 := by
      rw [← finrank_top (R := k) (M := ρ.right), htop₃, finrank_bot]
    exact hV₂₃ h₂ h₃

private lemma a3_range_g {k : Type*} [Field k] (ρ : LinearChainRepresentation k)
    (hind : ρ.IsIndecomposable) :
    LinearMap.range ρ.middleToRight = ⊤ ∨
    (Module.finrank k ρ.left = 0 ∧ Module.finrank k ρ.middle = 0) := by
  by_contra h; push Not at h; obtain ⟨hrange, hV₁₂⟩ := h
  obtain ⟨_, hind_cond⟩ := hind
  obtain ⟨q₃, hq₃⟩ := Submodule.exists_isCompl (LinearMap.range ρ.middleToRight)
  have := hind_cond ⊤ ⊥ ⊤ ⊥ (LinearMap.range ρ.middleToRight) q₃
    isCompl_top_bot isCompl_top_bot hq₃
    (fun _ _ => Submodule.mem_top)
    (fun x hx => by rw [(Submodule.mem_bot (R := k)).mp hx, map_zero]; exact Submodule.zero_mem _)
    (fun x _ => LinearMap.mem_range_self ρ.middleToRight x)
    (fun x hx => by rw [(Submodule.mem_bot (R := k)).mp hx, map_zero]; exact q₃.zero_mem)
  rcases this with ⟨htop₁, htop₂, _⟩ | ⟨_, _, hq₃'⟩
  · have h₁ : Module.finrank k ρ.left = 0 := by
      rw [← finrank_top (R := k) (M := ρ.left), htop₁, finrank_bot]
    have h₂ : Module.finrank k ρ.middle = 0 := by
      rw [← finrank_top (R := k) (M := ρ.middle), htop₂, finrank_bot]
    exact hV₁₂ h₁ h₂
  · exact hrange (eq_top_of_isCompl_bot (hq₃' ▸ hq₃))

private lemma a3_gf_injective {k : Type*} [Field k] (ρ : LinearChainRepresentation k)
    (hind : ρ.IsIndecomposable)
    (hf_inj : Function.Injective ρ.leftToMiddle)
    (h₃ : 0 < Module.finrank k ρ.right) :
    Function.Injective (ρ.middleToRight.comp ρ.leftToMiddle) := by
  rw [← LinearMap.ker_eq_bot]
  by_contra hker
  obtain ⟨_, hind_cond⟩ := hind
  set K := LinearMap.ker (ρ.middleToRight.comp ρ.leftToMiddle)
  have hfK_le_kerg : Submodule.map ρ.leftToMiddle K ≤ LinearMap.ker ρ.middleToRight := by
    intro y hy
    obtain ⟨x, hx, rfl⟩ := Submodule.mem_map.mp hy
    exact LinearMap.mem_ker.mpr (LinearMap.mem_ker.mp hx)
  obtain ⟨q₁, hq₁⟩ := Submodule.exists_isCompl K
  have hf_disj : Disjoint (Submodule.map ρ.leftToMiddle K) (Submodule.map ρ.leftToMiddle q₁) := by
    rw [Submodule.disjoint_def]
    intro y hy₁ hy₂
    obtain ⟨x₁, hx₁, rfl⟩ := Submodule.mem_map.mp hy₁
    obtain ⟨x₂, hx₂, h_eq⟩ := Submodule.mem_map.mp hy₂
    have heq : x₁ = x₂ := hf_inj h_eq.symm
    rw [heq] at hx₁
    have hmem : x₂ ∈ K ⊓ q₁ := ⟨hx₁, hx₂⟩
    rw [hq₁.1.eq_bot, Submodule.mem_bot] at hmem
    rw [heq, hmem, map_zero]
  obtain ⟨q₂, hpq₂, hfq₁_le_q₂⟩ := exists_isCompl_containing
    (Submodule.map ρ.leftToMiddle K) (Submodule.map ρ.leftToMiddle q₁) hf_disj
  have := hind_cond K q₁ (Submodule.map ρ.leftToMiddle K) q₂ ⊥ ⊤
    hq₁ hpq₂ isCompl_bot_top
    (fun x hx => Submodule.mem_map.mpr ⟨x, hx, rfl⟩)
    (fun x hx => hfq₁_le_q₂ (Submodule.mem_map.mpr ⟨x, hx, rfl⟩))
    (fun x hx => by
      have := hfK_le_kerg hx
      rw [LinearMap.mem_ker] at this
      rw [this]; exact Submodule.zero_mem _)
    (fun _ _ => Submodule.mem_top)
  rcases this with ⟨hK_bot, _, _⟩ | ⟨_, _, htop⟩
  · exact hker hK_bot
  · rw [← finrank_top (R := k) (M := ρ.right), htop, finrank_bot] at h₃; omega

/-- An indecomposable linear-chain representation has dimension triple (1, 0, 0), (0, 1, 0), (0, 0, 1), (1, 1, 0), (0, 1, 1), or (1, 1, 1), with the corresponding chain maps injective. -/
theorem isIndecomposable_dimension_cases (k : Type*) [Field k]
    (ρ : LinearChainRepresentation k) (hind : ρ.IsIndecomposable) :
    (Module.finrank k ρ.left = 1 ∧ Module.finrank k ρ.middle = 0 ∧
      Module.finrank k ρ.right = 0) ∨
    (Module.finrank k ρ.left = 0 ∧ Module.finrank k ρ.middle = 1 ∧
      Module.finrank k ρ.right = 0) ∨
    (Module.finrank k ρ.left = 0 ∧ Module.finrank k ρ.middle = 0 ∧
      Module.finrank k ρ.right = 1) ∨
    (Module.finrank k ρ.left = 1 ∧ Module.finrank k ρ.middle = 1 ∧
      Module.finrank k ρ.right = 0 ∧ Function.Injective ρ.leftToMiddle) ∨
    (Module.finrank k ρ.left = 0 ∧ Module.finrank k ρ.middle = 1 ∧
      Module.finrank k ρ.right = 1 ∧ Function.Injective ρ.middleToRight) ∨
    (Module.finrank k ρ.left = 1 ∧ Module.finrank k ρ.middle = 1 ∧
      Module.finrank k ρ.right = 1 ∧ Function.Injective ρ.leftToMiddle ∧
      Function.Injective ρ.middleToRight) := by
  obtain ⟨hnt, hind_cond⟩ := hind
  have hind : ρ.IsIndecomposable := ⟨hnt, hind_cond⟩
  rcases Nat.eq_zero_or_pos (Module.finrank k ρ.middle) with h₂ | h₂
  · rcases a3_V₂_zero ρ hind h₂ with ⟨h₁, h₃⟩ | ⟨h₁, h₃⟩
    · left; exact ⟨h₁, h₂, h₃⟩
    · right; right; left; exact ⟨h₁, h₂, h₃⟩
  · rcases Nat.eq_zero_or_pos (Module.finrank k ρ.left) with h₁ | h₁
    · rcases a3_V₁_zero ρ hind h₁ with ⟨h₂', h₃⟩ | ⟨h₂', h₃⟩ | ⟨h₂', h₃, hinj⟩
      · right; left; exact ⟨h₁, h₂', h₃⟩
      · right; right; left; exact ⟨h₁, h₂', h₃⟩
      · right; right; right; right; left; exact ⟨h₁, h₂', h₃, hinj⟩
    · rcases Nat.eq_zero_or_pos (Module.finrank k ρ.right) with h₃ | h₃
      · rcases a3_V₃_zero ρ hind h₃ with ⟨h₁', h₂'⟩ | ⟨h₁', h₂'⟩ | ⟨h₁', h₂', hinj⟩
        · left; exact ⟨h₁', h₂', h₃⟩
        · right; left; exact ⟨h₁', h₂', h₃⟩
        · right; right; right; left; exact ⟨h₁', h₂', h₃, hinj⟩
      · -- ALL THREE NONZERO
        have hf_inj : Function.Injective ρ.leftToMiddle :=
          LinearMap.ker_eq_bot.mp ((a3_ker_f ρ hind).resolve_right (by omega))
        have hg_surj : LinearMap.range ρ.middleToRight = ⊤ :=
          (a3_range_g ρ hind).resolve_right (by omega)
        have hgf_inj := a3_gf_injective ρ hind hf_inj h₃
        -- ker g ∩ range f = ⊥
        have hkerg_rangef : Disjoint (LinearMap.ker ρ.middleToRight) (LinearMap.range ρ.leftToMiddle) := by
          rw [Submodule.disjoint_def]
          intro y hyk hyf
          obtain ⟨x, rfl⟩ := LinearMap.mem_range.mp hyf
          have : x ∈ LinearMap.ker (ρ.middleToRight.comp ρ.leftToMiddle) := by
            rw [LinearMap.mem_ker, LinearMap.comp_apply]
            exact LinearMap.mem_ker.mp hyk
          rw [LinearMap.ker_eq_bot.mpr hgf_inj, Submodule.mem_bot] at this
          rw [this, map_zero]
        -- Get complement of ker g containing range f
        obtain ⟨C, hC, hrf_le_C⟩ := exists_isCompl_containing
          (LinearMap.ker ρ.middleToRight) (LinearMap.range ρ.leftToMiddle) hkerg_rangef
        -- Use indecomposability: (⊥, ker g, ⊥) ⊕ (V₁, C, V₃)
        have hkerg_bot : LinearMap.ker ρ.middleToRight = ⊥ := by
          have := hind_cond ⊥ ⊤ (LinearMap.ker ρ.middleToRight) C ⊥ ⊤
            isCompl_bot_top hC isCompl_bot_top
            (fun x hx => by
              rw [(Submodule.mem_bot (R := k)).mp hx, map_zero]
              exact (LinearMap.ker ρ.middleToRight).zero_mem)
            (fun x _ => hrf_le_C (LinearMap.mem_range_self ρ.leftToMiddle x))
            (fun x hx => by
              rw [LinearMap.mem_ker.mp hx]; exact Submodule.zero_mem _)
            (fun _ _ => Submodule.mem_top)
          rcases this with ⟨_, hkg, _⟩ | ⟨_, _, htop⟩
          · exact hkg
          · rw [← finrank_top (R := k) (M := ρ.right), htop, finrank_bot] at h₃; omega
        -- g is bijective
        have hg_inj : Function.Injective ρ.middleToRight := LinearMap.ker_eq_bot.mp hkerg_bot
        have hg_bij : Function.Bijective ρ.middleToRight :=
          ⟨hg_inj, LinearMap.range_eq_top.mp hg_surj⟩
        -- Show dim V₁ = 1: V₁ is indecomposable
        -- Any decomp p₁ ⊕ q₁ lifts through f, then use exists_isCompl_containing for V₂
        have hV₁_dim1 : Module.finrank k ρ.left = 1 := by
          rw [← RepresentationTheory.OneDimensionalSubmoduleComplements.nontrivial_and_isCompl_eq_bot_iff_finrank_eq_one]
          refine ⟨Module.nontrivial_of_finrank_pos h₁, fun p₁ q₁ hpq₁ => ?_⟩
          have hfp_fq_disj : Disjoint (Submodule.map ρ.leftToMiddle p₁) (Submodule.map ρ.leftToMiddle q₁) := by
            rw [Submodule.disjoint_def]
            intro y hy₁ hy₂
            obtain ⟨x₁, hx₁, rfl⟩ := Submodule.mem_map.mp hy₁
            obtain ⟨x₂, hx₂, h_eq⟩ := Submodule.mem_map.mp hy₂
            have heq : x₁ = x₂ := hf_inj h_eq.symm
            rw [heq] at hx₁
            have hmem : x₂ ∈ p₁ ⊓ q₁ := ⟨hx₁, hx₂⟩
            rw [hpq₁.1.eq_bot, Submodule.mem_bot] at hmem
            rw [heq, hmem, map_zero]
          obtain ⟨q₂, hpq₂, hfq₁_le_q₂⟩ := exists_isCompl_containing
            (Submodule.map ρ.leftToMiddle p₁) (Submodule.map ρ.leftToMiddle q₁) hfp_fq_disj
          have hpq₃ := isCompl_map_of_bijective ρ.middleToRight hg_bij _ _ hpq₂
          have := hind_cond p₁ q₁ (Submodule.map ρ.leftToMiddle p₁) q₂
            (Submodule.map ρ.middleToRight (Submodule.map ρ.leftToMiddle p₁)) (Submodule.map ρ.middleToRight q₂)
            hpq₁ hpq₂ hpq₃
            (fun x hx => Submodule.mem_map.mpr ⟨x, hx, rfl⟩)
            (fun x hx => hfq₁_le_q₂ (Submodule.mem_map.mpr ⟨x, hx, rfl⟩))
            (fun x hx => Submodule.mem_map.mpr ⟨x, hx, rfl⟩)
            (fun x hx => Submodule.mem_map.mpr ⟨x, hx, rfl⟩)
          rcases this with ⟨hp₁, _, _⟩ | ⟨hq₁, _, _⟩
          · left; exact hp₁
          · right; exact hq₁
        -- Show dim V₂ = 1: decompose V₂ = range f ⊕ W, then A₃ indecomp forces W = ⊥
        have hV₂_dim1 : Module.finrank k ρ.middle = 1 := by
          obtain ⟨W, hW⟩ := Submodule.exists_isCompl (LinearMap.range ρ.leftToMiddle)
          have hpq₃ := isCompl_map_of_bijective ρ.middleToRight hg_bij _ _ hW
          have := hind_cond ⊤ ⊥ (LinearMap.range ρ.leftToMiddle) W
            (Submodule.map ρ.middleToRight (LinearMap.range ρ.leftToMiddle)) (Submodule.map ρ.middleToRight W)
            isCompl_top_bot hW hpq₃
            (fun x _ => LinearMap.mem_range_self ρ.leftToMiddle x)
            (fun x hx => by
              rw [(Submodule.mem_bot (R := k)).mp hx, map_zero]; exact W.zero_mem)
            (fun x hx => Submodule.mem_map.mpr ⟨x, hx, rfl⟩)
            (fun x hx => Submodule.mem_map.mpr ⟨x, hx, rfl⟩)
          rcases this with ⟨htop, _, _⟩ | ⟨_, hW_bot, _⟩
          · -- ⊤ = ⊥ contradicts dim V₁ > 0
            rw [← finrank_top (R := k) (M := ρ.left), htop, finrank_bot] at h₁; omega
          · -- W = ⊥ means range f = V₂, so dim V₂ = dim(range f) = dim V₁ = 1
            have hf_surj : LinearMap.range ρ.leftToMiddle = ⊤ :=
              eq_top_of_isCompl_bot (hW_bot ▸ hW)
            have h := ρ.leftToMiddle.finrank_range_add_finrank_ker
            rw [LinearMap.ker_eq_bot.mpr hf_inj, finrank_bot, add_zero,
                hf_surj, finrank_top] at h
            omega
        -- dim V₃ = dim V₂ = 1 (g bijective)
        have hV₃_dim1 : Module.finrank k ρ.right = 1 := by
          have h := ρ.middleToRight.finrank_range_add_finrank_ker
          rw [hkerg_bot, finrank_bot, add_zero, hg_surj, finrank_top] at h
          omega
        right; right; right; right; right
        exact ⟨hV₁_dim1, hV₂_dim1, hV₃_dim1, hf_inj, hg_inj⟩

end RepresentationTheory.FiniteDimensionalLinearChainRepresentations
