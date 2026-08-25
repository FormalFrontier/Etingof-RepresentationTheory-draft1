/-
Copyright (c) 2026 mathlib-initiative. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: mathlib-initiative
-/

import Mathlib
import RepresentationTheory.OneDimensionalSubmoduleComplements
import RepresentationTheory.Alignment.Attribute

/-!
# Finite-dimensional linear-map representations

This module defines finite-dimensional representations consisting of two vector spaces and a
linear map between them. It classifies the indecomposable representations up to equivalence.
-/

namespace RepresentationTheory.FiniteDimensionalLinearMapRepresentations

/-- A finite-dimensional representation consisting of two vector spaces over a field and a linear map between them. -/
structure LinearMapRepresentation (k : Type*) [Field k] where
  /-- The domain vector space of a linear-map representation. -/
  domain : Type*
  /-- The codomain vector space of a linear-map representation. -/
  codomain : Type*
  /-- The additive commutative group structure on the domain space of a representation. -/
  [domainAddCommGroup : AddCommGroup domain]
  /-- The scalar module structure on the domain space of a representation. -/
  [domainModule : Module k domain]
  /-- The domain space of a linear-map representation is finite-dimensional. -/
  [finiteDimensional_domain : FiniteDimensional k domain]
  /-- The additive commutative group structure on the codomain space of a representation. -/
  [codomainAddCommGroup : AddCommGroup codomain]
  /-- The scalar module structure on the codomain space of a representation. -/
  [codomainModule : Module k codomain]
  /-- The codomain space of a linear-map representation is finite-dimensional. -/
  [finiteDimensional_codomain : FiniteDimensional k codomain]
  /-- The structure map from the domain space to the codomain space of a representation. -/
  linearMap : domain →ₗ[k] codomain

attribute [instance] LinearMapRepresentation.domainAddCommGroup
  LinearMapRepresentation.domainModule LinearMapRepresentation.finiteDimensional_domain
  LinearMapRepresentation.codomainAddCommGroup LinearMapRepresentation.codomainModule
  LinearMapRepresentation.finiteDimensional_codomain

/-- The predicate that a finite-dimensional linear-map representation is indecomposable. -/
def LinearMapRepresentation.IsIndecomposable {k : Type*} [Field k]
    (ρ : LinearMapRepresentation k) : Prop :=
  (0 < Module.finrank k ρ.domain ∨ 0 < Module.finrank k ρ.codomain) ∧
  ∀ (p₁ q₁ : Submodule k ρ.domain) (p₂ q₂ : Submodule k ρ.codomain),
    IsCompl p₁ q₁ → IsCompl p₂ q₂ →
    (∀ x ∈ p₁, ρ.linearMap x ∈ p₂) → (∀ x ∈ q₁, ρ.linearMap x ∈ q₂) →
    (p₁ = ⊥ ∧ p₂ = ⊥) ∨ (q₁ = ⊥ ∧ q₂ = ⊥)

private lemma ker_or_codomain_zero {k : Type*} [Field k] (ρ : LinearMapRepresentation k)
    (hind : ρ.IsIndecomposable) :
    LinearMap.ker ρ.linearMap = ⊥ ∨ Module.finrank k ρ.codomain = 0 := by
  by_contra h
  push Not at h
  obtain ⟨hker, hcodomain⟩ := h
  obtain ⟨q₁, hq₁⟩ := Submodule.exists_isCompl (LinearMap.ker ρ.linearMap)
  have hres := hind.2 (LinearMap.ker ρ.linearMap) q₁ ⊥ ⊤ hq₁ isCompl_bot_top
    (fun x hx => by simp [LinearMap.mem_ker.mp hx])
    (fun _ _ => Submodule.mem_top)
  rcases hres with ⟨hk, _⟩ | ⟨_, htop⟩
  · exact hker hk
  · rw [← finrank_top (R := k) (M := ρ.codomain), htop, finrank_bot] at hcodomain
    exact hcodomain rfl

private lemma range_or_domain_zero {k : Type*} [Field k] (ρ : LinearMapRepresentation k)
    (hind : ρ.IsIndecomposable) :
    LinearMap.range ρ.linearMap = ⊤ ∨ Module.finrank k ρ.domain = 0 := by
  by_contra h
  push Not at h
  obtain ⟨hrange, hdomain⟩ := h
  obtain ⟨q₂, hq₂⟩ := Submodule.exists_isCompl (LinearMap.range ρ.linearMap)
  have hind_cond := hind.2 ⊤ ⊥ (LinearMap.range ρ.linearMap) q₂ isCompl_top_bot hq₂
    (fun x _ => LinearMap.mem_range_self ρ.linearMap x)
    (fun x hx => by rw [(Submodule.mem_bot (R := k)).mp hx, map_zero]; exact q₂.zero_mem)
  rcases hind_cond with ⟨htop, _⟩ | ⟨_, hq₂'⟩
  · rw [← finrank_top (R := k) (M := ρ.domain), htop, finrank_bot] at hdomain
    exact hdomain rfl
  · exact hrange (eq_top_of_isCompl_bot (hq₂' ▸ hq₂))

/-- An indecomposable representation has dimension pair `(1, 0)`, `(0, 1)`, or `(1, 1)`, with an injective structure map in the last case. -/
@[source_ref "Chapter6/Example6.2.3" (role := supporting)]
theorem isIndecomposable_dimension_cases (k : Type*) [Field k]
    (ρ : LinearMapRepresentation k) (hind : ρ.IsIndecomposable) :
    (Module.finrank k ρ.domain = 1 ∧ Module.finrank k ρ.codomain = 0) ∨
    (Module.finrank k ρ.domain = 0 ∧ Module.finrank k ρ.codomain = 1) ∨
    (Module.finrank k ρ.domain = 1 ∧ Module.finrank k ρ.codomain = 1 ∧
      Function.Injective ρ.linearMap) := by
  have hker := ker_or_codomain_zero ρ hind
  have hrange := range_or_domain_zero ρ hind
  obtain ⟨hnt, hind_cond⟩ := hind
  rcases Nat.eq_zero_or_pos (Module.finrank k ρ.domain) with h₁ | h₁ <;>
    rcases Nat.eq_zero_or_pos (Module.finrank k ρ.codomain) with h₂ | h₂
  · omega
  · right; left; refine ⟨h₁, ?_⟩
    rw [← RepresentationTheory.OneDimensionalSubmoduleComplements.nontrivial_and_isCompl_eq_bot_iff_finrank_eq_one
      k ρ.codomain]
    refine ⟨Module.nontrivial_of_finrank_pos h₂, fun p₂ q₂ hpq₂ => ?_⟩
    have hdomain_zero : ∀ (x : ρ.domain), x = 0 := fun x => by
      have htop₁ : (⊤ : Submodule k ρ.domain) = ⊥ :=
        Submodule.finrank_eq_zero.mp (by rw [finrank_top]; exact h₁)
      have : x ∈ (⊤ : Submodule k ρ.domain) := Submodule.mem_top
      rwa [htop₁, Submodule.mem_bot] at this
    specialize hind_cond ⊥ ⊤ p₂ q₂ isCompl_bot_top hpq₂
      (fun x _ => by rw [hdomain_zero x, map_zero]; exact p₂.zero_mem)
      (fun x _ => by rw [hdomain_zero x, map_zero]; exact q₂.zero_mem)
    rcases hind_cond with ⟨_, h⟩ | ⟨_, h⟩
    · left; exact h
    · right; exact h
  · left; refine ⟨?_, h₂⟩
    rw [← RepresentationTheory.OneDimensionalSubmoduleComplements.nontrivial_and_isCompl_eq_bot_iff_finrank_eq_one
      k ρ.domain]
    refine ⟨Module.nontrivial_of_finrank_pos h₁, fun p₁ q₁ hpq₁ => ?_⟩
    have htop₂ : (⊤ : Submodule k ρ.codomain) = ⊥ :=
      Submodule.finrank_eq_zero.mp (by rw [finrank_top]; exact h₂)
    have hcodomain_zero : ∀ (y : ρ.codomain), y = 0 := fun y => by
      have : y ∈ (⊤ : Submodule k ρ.codomain) := Submodule.mem_top
      rwa [htop₂, Submodule.mem_bot] at this
    specialize hind_cond p₁ q₁ ⊥ ⊤ hpq₁ isCompl_bot_top
      (fun x _ => by rw [hcodomain_zero (ρ.linearMap x)]; exact Submodule.zero_mem _)
      (fun _ _ => Submodule.mem_top)
    rcases hind_cond with ⟨h, _⟩ | ⟨h, _⟩
    · left; exact h
    · right; exact h
  · have hf_inj : Function.Injective ρ.linearMap :=
      LinearMap.ker_eq_bot.mp (hker.resolve_right (by omega))
    have hf_surj : LinearMap.range ρ.linearMap = ⊤ := hrange.resolve_right (by omega)
    have hdim_eq : Module.finrank k ρ.codomain = Module.finrank k ρ.domain := by
      have h := ρ.linearMap.finrank_range_add_finrank_ker
      rw [LinearMap.ker_eq_bot.mpr hf_inj, finrank_bot, add_zero] at h
      rw [hf_surj, finrank_top] at h
      omega
    have hdomain_dim1 : Module.finrank k ρ.domain = 1 := by
      rw [← RepresentationTheory.OneDimensionalSubmoduleComplements.nontrivial_and_isCompl_eq_bot_iff_finrank_eq_one
        k ρ.domain]
      refine ⟨Module.nontrivial_of_finrank_pos h₁, fun p₁ q₁ hpq₁ => ?_⟩
      set p₂ := Submodule.map ρ.linearMap p₁
      set q₂ := Submodule.map ρ.linearMap q₁
      have hpq₂ : IsCompl p₂ q₂ := by
        constructor
        · rw [Submodule.disjoint_def]
          intro y hy₁ hy₂
          obtain ⟨x₁, hx₁, rfl⟩ := Submodule.mem_map.mp hy₁
          obtain ⟨x₂, hx₂, h_eq⟩ := Submodule.mem_map.mp hy₂
          have heq : x₁ = x₂ := hf_inj h_eq.symm
          rw [heq] at hx₁
          have hmem : x₂ ∈ p₁ ⊓ q₁ := ⟨hx₁, hx₂⟩
          rw [hpq₁.1.eq_bot, Submodule.mem_bot] at hmem
          rw [heq, hmem, map_zero]
        · rw [codisjoint_iff]
          ext y
          simp only [Submodule.mem_sup, Submodule.mem_top, iff_true]
          obtain ⟨x, rfl⟩ := LinearMap.range_eq_top.mp hf_surj y
          have : x ∈ (⊤ : Submodule k ρ.domain) := Submodule.mem_top
          rw [← hpq₁.2.eq_top] at this
          obtain ⟨a, ha, b, hb, hab⟩ := Submodule.mem_sup.mp this
          exact ⟨ρ.linearMap a, ⟨a, ha, rfl⟩, ρ.linearMap b, ⟨b, hb, rfl⟩,
            by rw [← map_add, hab]⟩
      specialize hind_cond p₁ q₁ p₂ q₂ hpq₁ hpq₂
        (fun x hx => Submodule.mem_map.mpr ⟨x, hx, rfl⟩)
        (fun x hx => Submodule.mem_map.mpr ⟨x, hx, rfl⟩)
      rcases hind_cond with ⟨hp₁, _⟩ | ⟨hq₁, _⟩
      · left; exact hp₁
      · right; exact hq₁
    right; right; exact ⟨hdomain_dim1, hdim_eq ▸ hdomain_dim1, hf_inj⟩

open Module

/-- An equivalence between two finite-dimensional linear-map representations. -/
structure LinearMapRepresentation.Equiv {k : Type*} [Field k]
    (ρ σ : LinearMapRepresentation k) where
  /-- The linear equivalence between the domain spaces of two equivalent representations. -/
  domainLinearEquiv : ρ.domain ≃ₗ[k] σ.domain
  /-- The linear equivalence between the codomain spaces of two equivalent representations. -/
  codomainLinearEquiv : ρ.codomain ≃ₗ[k] σ.codomain
  /-- The domain and codomain linear equivalences of a representation equivalence intertwine the two structure maps. -/
  map_comm_apply : ∀ x, codomainLinearEquiv (ρ.linearMap x) =
    σ.linearMap (domainLinearEquiv x)

namespace LinearMapRepresentation.Equiv

/-- The identity equivalence of a linear-map representation. -/
def refl {k : Type*} [Field k] (ρ : LinearMapRepresentation k) : ρ.Equiv ρ where
  domainLinearEquiv := LinearEquiv.refl k ρ.domain
  codomainLinearEquiv := LinearEquiv.refl k ρ.codomain
  map_comm_apply := fun _ => rfl

/-- Reverses an equivalence of linear-map representations. -/
def symm {k : Type*} [Field k] {ρ σ : LinearMapRepresentation k}
    (e : ρ.Equiv σ) : σ.Equiv ρ where
  domainLinearEquiv := e.domainLinearEquiv.symm
  codomainLinearEquiv := e.codomainLinearEquiv.symm
  map_comm_apply := fun y => by
    apply e.codomainLinearEquiv.injective
    rw [e.codomainLinearEquiv.apply_symm_apply, e.map_comm_apply,
      e.domainLinearEquiv.apply_symm_apply]

/-- Composes two equivalences of linear-map representations. -/
def trans {k : Type*} [Field k] {ρ σ τ : LinearMapRepresentation k}
    (e : ρ.Equiv σ) (e' : σ.Equiv τ) : ρ.Equiv τ where
  domainLinearEquiv := e.domainLinearEquiv.trans e'.domainLinearEquiv
  codomainLinearEquiv := e.codomainLinearEquiv.trans e'.codomainLinearEquiv
  map_comm_apply := fun x => by
    simp only [LinearEquiv.trans_apply]
    rw [e.map_comm_apply, e'.map_comm_apply]

/-- A representation equivalence preserves the finranks of both its domain and codomain spaces. -/
lemma finrank_eq {k : Type*} [Field k] {ρ σ : LinearMapRepresentation k} (e : ρ.Equiv σ) :
    Module.finrank k ρ.domain = Module.finrank k σ.domain ∧
    Module.finrank k ρ.codomain = Module.finrank k σ.codomain :=
  ⟨e.domainLinearEquiv.finrank_eq, e.codomainLinearEquiv.finrank_eq⟩

end LinearMapRepresentation.Equiv

/-- A standard linear-map representation whose domain and codomain dimensions are one and zero. -/
abbrev LinearMapRepresentation.oneZeroModel (k : Type*) [Field k] :
    LinearMapRepresentation k where
  domain := k
  codomain := PUnit
  linearMap := 0

/-- A standard linear-map representation whose domain and codomain dimensions are zero and one. -/
abbrev LinearMapRepresentation.zeroOneModel (k : Type*) [Field k] :
    LinearMapRepresentation k where
  domain := PUnit
  codomain := k
  linearMap := 0

/-- A standard linear-map representation whose domain and codomain dimensions are both one. -/
abbrev LinearMapRepresentation.oneOneModel (k : Type*) [Field k] :
    LinearMapRepresentation k where
  domain := k
  codomain := k
  linearMap := LinearMap.id

namespace LinearMapRepresentation

/-- Every submodule of a subsingleton module is the bottom submodule. -/
theorem submodule_eq_bot_of_subsingleton {k M : Type*} [Field k] [AddCommGroup M]
    [Module k M] [Subsingleton M] (p : Submodule k M) : p = ⊥ := by
  rw [eq_bot_iff]
  intro x _
  rw [Submodule.mem_bot]
  exact Subsingleton.elim _ _

/-- The standard model of dimension pair `(1, 0)` is indecomposable. -/
theorem oneZeroModel_isIndecomposable (k : Type*) [Field k] :
    (oneZeroModel k).IsIndecomposable := by
  refine ⟨Or.inl Module.finrank_pos, ?_⟩
  intro p₁ q₁ p₂ q₂ hpq₁ _ _ _
  have hp₂ : p₂ = ⊥ := submodule_eq_bot_of_subsingleton p₂
  have hq₂ : q₂ = ⊥ := submodule_eq_bot_of_subsingleton q₂
  have hsum : Module.finrank k p₁ + Module.finrank k q₁ = 1 := by
    rw [Submodule.finrank_add_eq_of_isCompl hpq₁]
    exact finrank_self k
  rcases Nat.eq_zero_or_pos (Module.finrank k p₁) with h0 | hpos
  · exact Or.inl ⟨Submodule.finrank_eq_zero.mp h0, hp₂⟩
  · exact Or.inr ⟨Submodule.finrank_eq_zero.mp (by omega), hq₂⟩

/-- The standard model of dimension pair `(0, 1)` is indecomposable. -/
theorem zeroOneModel_isIndecomposable (k : Type*) [Field k] :
    (zeroOneModel k).IsIndecomposable := by
  refine ⟨Or.inr Module.finrank_pos, ?_⟩
  intro p₁ q₁ p₂ q₂ _ hpq₂ _ _
  have hp₁ : p₁ = ⊥ := submodule_eq_bot_of_subsingleton p₁
  have hq₁ : q₁ = ⊥ := submodule_eq_bot_of_subsingleton q₁
  have hsum : Module.finrank k p₂ + Module.finrank k q₂ = 1 := by
    rw [Submodule.finrank_add_eq_of_isCompl hpq₂]
    exact finrank_self k
  rcases Nat.eq_zero_or_pos (Module.finrank k p₂) with h0 | hpos
  · exact Or.inl ⟨hp₁, Submodule.finrank_eq_zero.mp h0⟩
  · exact Or.inr ⟨hq₁, Submodule.finrank_eq_zero.mp (by omega)⟩

/-- The standard model of dimension pair `(1, 1)` is indecomposable. -/
theorem oneOneModel_isIndecomposable (k : Type*) [Field k] :
    (oneOneModel k).IsIndecomposable := by
  refine ⟨Or.inl Module.finrank_pos, ?_⟩
  intro p₁ q₁ p₂ q₂ hpq₁ hpq₂ hp hq
  have hsum₁ : Module.finrank k p₁ + Module.finrank k q₁ = 1 := by
    rw [Submodule.finrank_add_eq_of_isCompl hpq₁]
    exact finrank_self k
  have hsum₂ : Module.finrank k p₂ + Module.finrank k q₂ = 1 := by
    rw [Submodule.finrank_add_eq_of_isCompl hpq₂]
    exact finrank_self k
  have hp₁₂ : p₁ ≤ p₂ := fun x hx => by simpa using hp x hx
  have hq₁₂ : q₁ ≤ q₂ := fun x hx => by simpa using hq x hx
  have hfp : Module.finrank k p₁ ≤ Module.finrank k p₂ := Submodule.finrank_mono hp₁₂
  have hfq : Module.finrank k q₁ ≤ Module.finrank k q₂ := Submodule.finrank_mono hq₁₂
  rcases Nat.eq_zero_or_pos (Module.finrank k p₁) with h0 | hpos
  · refine Or.inl ⟨Submodule.finrank_eq_zero.mp h0,
      Submodule.finrank_eq_zero.mp (by omega)⟩
  · refine Or.inr ⟨Submodule.finrank_eq_zero.mp (by omega),
      Submodule.finrank_eq_zero.mp (by omega)⟩

/-- The three-element indexed family of standard linear-map representations. -/
@[source_ref "Chapter6/Example6.2.3" (role := supporting)]
def standardModel (k : Type*) [Field k] : Fin 3 → LinearMapRepresentation k
  | 0 => oneZeroModel k
  | 1 => zeroOneModel k
  | 2 => oneOneModel k

/-- The ordered pair of domain and codomain dimensions of a linear-map representation. -/
noncomputable def dimension (k : Type*) [Field k] (σ : LinearMapRepresentation k) : ℕ × ℕ :=
  (Module.finrank k σ.domain, Module.finrank k σ.codomain)

/-- Equivalent linear-map representations have the same ordered pair of dimensions. -/
theorem Equiv.dimension_eq {k : Type*} [Field k] {ρ σ : LinearMapRepresentation k}
    (e : ρ.Equiv σ) : dimension k ρ = dimension k σ := by
  obtain ⟨h₁, h₂⟩ := e.finrank_eq
  simp [dimension, h₁, h₂]

/-- The standard one-to-zero model has dimension pair `(1, 0)`. -/
theorem oneZeroModel_dimension (k : Type*) [Field k] :
    dimension k (oneZeroModel k) = (1, 0) := by
  simp [dimension, finrank_self, finrank_zero_of_subsingleton]

/-- The standard zero-to-one model has dimension pair `(0, 1)`. -/
theorem zeroOneModel_dimension (k : Type*) [Field k] :
    dimension k (zeroOneModel k) = (0, 1) := by
  simp [dimension, finrank_self, finrank_zero_of_subsingleton]

/-- The standard one-to-one model has dimension pair `(1, 1)`. -/
theorem oneOneModel_dimension (k : Type*) [Field k] :
    dimension k (oneOneModel k) = (1, 1) := by
  simp [dimension, finrank_self]

/-- Every member of the three-element family of standard models is indecomposable. -/
@[source_ref "Chapter6/Example6.2.3" (role := supporting)]
theorem standardModel_isIndecomposable (k : Type*) [Field k] (i : Fin 3) :
    (standardModel k i).IsIndecomposable := by
  fin_cases i
  · exact oneZeroModel_isIndecomposable k
  · exact zeroOneModel_isIndecomposable k
  · exact oneOneModel_isIndecomposable k

/-- Every indecomposable linear-map representation is equivalent to a unique member of the three-element family of standard models. -/
@[source_ref "Chapter6/Example6.2.3" (role := primary)]
theorem existsUnique_equiv_standardModel_of_isIndecomposable (k : Type*) [Field k]
    (ρ : LinearMapRepresentation k) (hind : ρ.IsIndecomposable) :
    ∃! i : Fin 3, Nonempty (ρ.Equiv (standardModel k i)) := by
  have hexists : ∃ i : Fin 3, Nonempty (ρ.Equiv (standardModel k i)) := by
    rcases isIndecomposable_dimension_cases k ρ hind with
      ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2, hinj⟩
    · refine ⟨0, ?_⟩
      change Nonempty (ρ.Equiv (oneZeroModel k))
      exact ⟨{ domainLinearEquiv := (FiniteDimensional.nonempty_linearEquiv_of_finrank_eq
                  (by rw [h1]; exact (finrank_self k).symm)).some,
               codomainLinearEquiv := (FiniteDimensional.nonempty_linearEquiv_of_finrank_eq
                  (by rw [h2]; exact finrank_zero_of_subsingleton.symm)).some,
               map_comm_apply := fun _ => Subsingleton.elim _ _ }⟩
    · refine ⟨1, ?_⟩
      change Nonempty (ρ.Equiv (zeroOneModel k))
      haveI hsub : Subsingleton ρ.domain := Module.finrank_zero_iff.mp h1
      exact ⟨{ domainLinearEquiv := (FiniteDimensional.nonempty_linearEquiv_of_finrank_eq
                  (by rw [h1]; exact finrank_zero_of_subsingleton.symm)).some,
               codomainLinearEquiv := (FiniteDimensional.nonempty_linearEquiv_of_finrank_eq
                  (by rw [h2]; exact (finrank_self k).symm)).some,
               map_comm_apply := fun x => by rw [Subsingleton.elim x 0]; simp }⟩
    · refine ⟨2, ?_⟩
      change Nonempty (ρ.Equiv (oneOneModel k))
      obtain ⟨e₁⟩ := FiniteDimensional.nonempty_linearEquiv_of_finrank_eq
        (R := k) (M := ρ.domain) (M' := (oneOneModel k).domain)
        (by rw [h1]; exact (finrank_self k).symm)
      have hsurj := (LinearMap.injective_iff_surjective_of_finrank_eq_finrank
        (by rw [h1, h2])).mp hinj
      let fEq : ρ.domain ≃ₗ[k] ρ.codomain :=
        LinearEquiv.ofBijective ρ.linearMap ⟨hinj, hsurj⟩
      refine ⟨{ domainLinearEquiv := e₁, codomainLinearEquiv := fEq.symm.trans e₁,
                map_comm_apply := fun x => ?_ }⟩
      have hfx : fEq.symm (ρ.linearMap x) = x := fEq.symm_apply_apply x
      simp only [LinearEquiv.trans_apply, hfx]
      rfl
  obtain ⟨i, hi⟩ := hexists
  refine ⟨i, hi, fun j hj => ?_⟩
  obtain ⟨ei⟩ := hi
  obtain ⟨ej⟩ := hj
  have hdv : dimension k (standardModel k j) = dimension k (standardModel k i) :=
    (ej.symm.trans ei).dimension_eq
  fin_cases i <;> fin_cases j <;>
    simp_all [standardModel, oneZeroModel_dimension, zeroOneModel_dimension,
      oneOneModel_dimension]

end LinearMapRepresentation

end RepresentationTheory.FiniteDimensionalLinearMapRepresentations
