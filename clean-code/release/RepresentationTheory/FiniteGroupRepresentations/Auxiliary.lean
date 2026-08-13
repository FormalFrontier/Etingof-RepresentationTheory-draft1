/-
Copyright (c) 2026 FormalFrontier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENCE.
Authors: Kim Morrison
-/

import Mathlib
import RepresentationTheory.Alignment.Attribute

/-! Auxiliary structures for finite-group representations. -/

namespace RepresentationTheory.FiniteGroupRepresentations.Auxiliary

/-- An auxiliary type of labels. -/
inductive AuxiliaryLabel where
  | complex
  | real
  | quaternionic

/-- A second auxiliary condition on finite-dimensional complex representations of finite groups. -/
@[source_ref "Chapter5/Definition5.1.1" (role := supporting),
  source_ref "Chapter5/Introduction" (role := supporting)]
def auxiliaryRepresentationConditionTwo
    {G : Type*} [Group G] [Fintype G]
    {V : Type*} [AddCommGroup V] [Module ℂ V] [Module.Finite ℂ V]
    (ρ : Representation ℂ G V) : Prop :=
  ∃ B : V →ₗ[ℂ] V →ₗ[ℂ] ℂ,
    (∀ v w, B v w = B w v) ∧
    (∀ v, (∀ w, B v w = 0) → v = 0) ∧
    (∀ g v w, B (ρ g v) (ρ g w) = B v w)

/-- A first auxiliary condition on finite-dimensional complex representations of finite groups. -/
@[source_ref "Chapter5/Definition5.1.1" (role := supporting),
  source_ref "Chapter5/Introduction" (role := supporting)]
def auxiliaryRepresentationConditionOne
    {G : Type*} [Group G] [Fintype G]
    {V : Type*} [AddCommGroup V] [Module ℂ V] [Module.Finite ℂ V]
    (ρ : Representation ℂ G V) : Prop :=
  ∃ B : V →ₗ[ℂ] V →ₗ[ℂ] ℂ,
    (∀ v w, B v w = -(B w v)) ∧
    (∀ v, (∀ w, B v w = 0) → v = 0) ∧
    (∀ g v w, B (ρ g v) (ρ g w) = B v w)

/-- An auxiliary predicate on finite-dimensional complex representations of finite groups. -/
@[source_ref "Chapter5/Definition5.1.1" (role := supporting),
  source_ref "Chapter5/Introduction" (role := supporting)]
def auxiliaryRepresentationProperty
    {G : Type*} [Group G] [Fintype G]
    {V : Type*} [AddCommGroup V] [Module ℂ V] [Module.Finite ℂ V]
    (ρ : Representation ℂ G V) : Prop :=
  ¬ ∃ e : V ≃ₗ[ℂ] Module.Dual ℂ V, ∀ g v, e (ρ g v) = ρ.dual g (e v)

/-- A nondegenerate invariant complex bilinear form yields a map intertwining a representation
with its dual. -/
theorem exists_intertwiner_to_dual_of_nondegenerate_invariant_form
    {G : Type*} [Group G]
    {V : Type*} [AddCommGroup V] [Module ℂ V] [Module.Finite ℂ V]
    (ρ : Representation ℂ G V) (B : V →ₗ[ℂ] V →ₗ[ℂ] ℂ)
    (hnd : ∀ v, (∀ w, B v w = 0) → v = 0)
    (hinv : ∀ g v w, B (ρ g v) (ρ g w) = B v w) :
    ∃ e : V ≃ₗ[ℂ] Module.Dual ℂ V, ∀ g v, e (ρ g v) = ρ.dual g (e v) := by
  have hinj : Function.Injective B := by
    rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    intro v hv
    exact hnd v fun w => by rw [hv]; rfl
  have hdim : Module.finrank ℂ V = Module.finrank ℂ (Module.Dual ℂ V) :=
    (Subspace.dual_finrank_eq (K := ℂ) (V := V)).symm
  refine ⟨B.linearEquivOfInjective hinj hdim, ?_⟩
  intro g v
  apply LinearMap.ext
  intro w
  rw [LinearMap.linearEquivOfInjective_apply, LinearMap.linearEquivOfInjective_apply,
    Representation.dual_apply, Module.Dual.transpose_apply, LinearMap.comp_apply]
  have hgg : (ρ g) ((ρ g⁻¹) w) = w := by
    rw [← Module.End.mul_apply, ← map_mul, mul_inv_cancel, map_one, Module.End.one_apply]
  have := hinv g v (ρ g⁻¹ w)
  rwa [hgg] at this

/-- The second auxiliary representation condition excludes the auxiliary representation property. -/
theorem not_auxiliaryRepresentationProperty_of_conditionTwo
    {G : Type*} [Group G] [Fintype G]
    {V : Type*} [AddCommGroup V] [Module ℂ V] [Module.Finite ℂ V]
    {ρ : Representation ℂ G V} (h : auxiliaryRepresentationConditionTwo ρ) :
    ¬ auxiliaryRepresentationProperty ρ := by
  obtain ⟨B, _, hnd, hinv⟩ := h
  exact fun hc => hc (exists_intertwiner_to_dual_of_nondegenerate_invariant_form ρ B hnd hinv)

/-- The first auxiliary representation condition excludes the auxiliary representation property. -/
theorem not_auxiliaryRepresentationProperty_of_conditionOne
    {G : Type*} [Group G] [Fintype G]
    {V : Type*} [AddCommGroup V] [Module ℂ V] [Module.Finite ℂ V]
    {ρ : Representation ℂ G V} (h : auxiliaryRepresentationConditionOne ρ) :
    ¬ auxiliaryRepresentationProperty ρ := by
  obtain ⟨B, _, hnd, hinv⟩ := h
  exact fun hc => hc (exists_intertwiner_to_dual_of_nondegenerate_invariant_form ρ B hnd hinv)

end RepresentationTheory.FiniteGroupRepresentations.Auxiliary
