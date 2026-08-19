/-
Copyright (c) 2026 mathlib-initiative. All rights reserved.
Released under Apache 2.0 license as described in the file LICENCE.
Authors: Kim Morrison
-/

import Mathlib.LinearAlgebra.Projection
import RepresentationTheory.Alignment.Attribute

/-! # Module decompositions -/

namespace RepresentationTheory.LinearAlgebra.ModuleDecompositions

/-- An auxiliary predicate on a module over a ring. -/
@[source_ref "Chapter2/Discussion_2.1_irreducible_indecomposable/Derived2" (role := supporting)]
def AuxiliaryDecompositionPredicate (A : Type*) (V : Type*) [Ring A] [AddCommGroup V]
    [Module A V] : Prop :=
  Nontrivial V ∧ ∀ (W₁ W₂ : Submodule A V),
    IsCompl W₁ W₂ → W₁ = ⊥ ∨ W₂ = ⊥

universe u v

/-- An auxiliary inductive type associated with a module over a ring. -/
structure AuxiliaryModuleData
    (A : Type u) (V : Type v) [Ring A] [AddCommGroup V] [Module A V] where
  /-- The first auxiliary type associated with the module data. -/
  firstAuxiliaryType : Type v
  /-- The second auxiliary type associated with the module data. -/
  secondAuxiliaryType : Type v
  /-- Gives the additive commutative group structure on the first auxiliary type. -/
  [firstAddCommGroup : AddCommGroup firstAuxiliaryType]
  /-- Gives the additive commutative group structure on the second auxiliary type. -/
  [secondAddCommGroup : AddCommGroup secondAuxiliaryType]
  /-- Supplies the module structure on the first auxiliary type. -/
  [firstModule : Module A firstAuxiliaryType]
  /-- Supplies the module structure on the second auxiliary type. -/
  [secondModule : Module A secondAuxiliaryType]
  /-- The first auxiliary type is nontrivial. -/
  [firstNontrivial : Nontrivial firstAuxiliaryType]
  /-- The second auxiliary type is nontrivial. -/
  [secondNontrivial : Nontrivial secondAuxiliaryType]
  /-- Identifies the ambient module linearly with the product of the two auxiliary types. -/
  linearEquivProd : V ≃ₗ[A] firstAuxiliaryType × secondAuxiliaryType

/-- A second auxiliary predicate on a module over a ring. -/
@[source_ref "Chapter2/Definition2.3.8" (role := supporting)]
def AuxiliaryDecompositionPredicate'
    (A : Type u) (V : Type v) [Ring A] [AddCommGroup V] [Module A V] : Prop :=
  Nontrivial V ∧ IsEmpty (AuxiliaryModuleData A V)

/-- The two auxiliary predicates on a module are logically equivalent. -/
@[source_ref "Chapter2/Definition2.3.8" (role := primary)]
theorem auxiliaryDecompositionPredicate_iff_auxiliaryDecompositionPredicate'
    (A : Type u) (V : Type v) [Ring A] [AddCommGroup V] [Module A V] :
    AuxiliaryDecompositionPredicate A V ↔ AuxiliaryDecompositionPredicate' A V := by
  constructor
  · rintro h
    refine ⟨h.1, ?_⟩
    constructor
    intro d
    letI : AddCommGroup d.firstAuxiliaryType := d.firstAddCommGroup
    letI : AddCommGroup d.secondAuxiliaryType := d.secondAddCommGroup
    letI : Module A d.firstAuxiliaryType := d.firstModule
    letI : Module A d.secondAuxiliaryType := d.secondModule
    let W₁ : Submodule A V :=
      LinearMap.ker (LinearMap.snd A d.firstAuxiliaryType d.secondAuxiliaryType ∘ₗ d.linearEquivProd.toLinearMap)
    let W₂ : Submodule A V :=
      LinearMap.ker (LinearMap.fst A d.firstAuxiliaryType d.secondAuxiliaryType ∘ₗ d.linearEquivProd.toLinearMap)
    have hcompl : IsCompl W₁ W₂ := by
      constructor
      · apply disjoint_iff.mpr
        rw [Submodule.eq_bot_iff]
        intro x hx
        rcases hx with ⟨hx₁, hx₂⟩
        have hfst : (d.linearEquivProd x).1 = 0 := by
          exact LinearMap.mem_ker.mp hx₂
        have hsnd : (d.linearEquivProd x).2 = 0 := by
          exact LinearMap.mem_ker.mp hx₁
        apply d.linearEquivProd.injective
        simpa only [map_zero] using Prod.ext hfst hsnd
      · rw [codisjoint_iff]
        apply top_unique
        intro x hx
        let x₁ : V := d.linearEquivProd.symm ((d.linearEquivProd x).1, 0)
        let x₂ : V := d.linearEquivProd.symm (0, (d.linearEquivProd x).2)
        have hx₁ : x₁ ∈ W₁ := by
          change (LinearMap.snd A d.firstAuxiliaryType d.secondAuxiliaryType ∘ₗ d.linearEquivProd.toLinearMap) x₁ = 0
          simp [x₁]
        have hx₂ : x₂ ∈ W₂ := by
          change (LinearMap.fst A d.firstAuxiliaryType d.secondAuxiliaryType ∘ₗ d.linearEquivProd.toLinearMap) x₂ = 0
          simp [x₂]
        have hsum : x₁ + x₂ = x := by
          apply d.linearEquivProd.injective
          simp [x₁, x₂]
        rw [← hsum]
        exact Submodule.add_mem_sup hx₁ hx₂
    rcases h.2 W₁ W₂ hcompl with hW₁ | hW₂
    · letI := d.firstNontrivial
      obtain ⟨v₁, hv₁⟩ := exists_ne (0 : d.firstAuxiliaryType)
      let x : V := d.linearEquivProd.symm (v₁, 0)
      have hx : x ∈ W₁ := by
        change (LinearMap.snd A d.firstAuxiliaryType d.secondAuxiliaryType ∘ₗ d.linearEquivProd.toLinearMap) x = 0
        simp [x]
      have hx0 : x = 0 := by simpa [hW₁] using hx
      apply hv₁
      have := congrArg (fun y => (d.linearEquivProd y).1) hx0
      simpa [x] using this
    · letI := d.secondNontrivial
      obtain ⟨v₂, hv₂⟩ := exists_ne (0 : d.secondAuxiliaryType)
      let x : V := d.linearEquivProd.symm (0, v₂)
      have hx : x ∈ W₂ := by
        change (LinearMap.fst A d.firstAuxiliaryType d.secondAuxiliaryType ∘ₗ d.linearEquivProd.toLinearMap) x = 0
        simp [x]
      have hx0 : x = 0 := by simpa [hW₂] using hx
      apply hv₂
      have := congrArg (fun y => (d.linearEquivProd y).2) hx0
      simpa [x] using this
  · rintro h
    refine ⟨h.1, ?_⟩
    intro W₁ W₂ hcompl
    by_cases hW₁ : W₁ = ⊥
    · exact Or.inl hW₁
    by_cases hW₂ : W₂ = ⊥
    · exact Or.inr hW₂
    letI : Nontrivial W₁ := Submodule.nontrivial_iff_ne_bot.mpr hW₁
    letI : Nontrivial W₂ := Submodule.nontrivial_iff_ne_bot.mpr hW₂
    let d : AuxiliaryModuleData A V := {
      firstAuxiliaryType := W₁
      secondAuxiliaryType := W₂
      linearEquivProd := (W₁.prodEquivOfIsCompl W₂ hcompl).symm }
    letI : IsEmpty (AuxiliaryModuleData A V) := h.2
    exact isEmptyElim d

/-- The auxiliary predicate excludes two nonbottom objects whose supremum is top and infimum is bottom. -/
@[source_ref "Chapter2/Discussion_2.1_irreducible_indecomposable/Derived2" (role := primary)]
theorem AuxiliaryDecompositionPredicate.not_exists_auxiliary_pair {A : Type*} {V : Type*}
    [Ring A] [AddCommGroup V] [Module A V]
    (h : AuxiliaryDecompositionPredicate A V) :
    ¬ ∃ (M N : Submodule A V), M ≠ ⊥ ∧ N ≠ ⊥ ∧ M ⊔ N = ⊤ ∧ M ⊓ N = ⊥ := by
  rintro ⟨M, N, hM, hN, hSup, hInf⟩
  have hC : IsCompl M N :=
    ⟨disjoint_iff.mpr hInf, codisjoint_iff.mpr (top_le_iff.mp (hSup ▸ le_rfl))⟩
  rcases h.2 M N hC with rfl | rfl
  · exact hM rfl
  · exact hN rfl

end RepresentationTheory.LinearAlgebra.ModuleDecompositions
