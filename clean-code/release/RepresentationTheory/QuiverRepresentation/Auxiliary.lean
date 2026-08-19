/-
Copyright (c) 2026 mathlib-initiative. All rights reserved.
Released under Apache 2.0 license as described in the file LICENCE.
Authors: mathlib-initiative
-/

import RepresentationTheory.CategoryTheory.QuiverLinearDiagrams
import RepresentationTheory.QuiverVertexPredicates
import RepresentationTheory.AuxiliaryQuiverRepresentationTransform
import RepresentationTheory.QuiverRepresentationQuotientTransform
import Mathlib.Algebra.DirectSum.Module
import Mathlib.LinearAlgebra.Dimension.Finrank
import Mathlib.LinearAlgebra.Basis.VectorSpace
import RepresentationTheory.Alignment.Attribute

/-- An auxiliary predicate for the displayed quiver-indexed object over a commutative semiring. -/
def RepresentationTheory.CategoryTheory.QuiverLinearDiagrams.AuxiliaryQuiverModuleData.AuxiliaryCondition
    {k : Type*} [CommSemiring k] {Q : Type*} [Quiver Q]
    (ρ : RepresentationTheory.CategoryTheory.QuiverLinearDiagrams.AuxiliaryQuiverModuleData k Q) : Prop :=
  (∃ v, Nontrivial (ρ.obj v)) ∧
  ∀ (W₁ W₂ : ∀ v, Submodule k (ρ.obj v)),
    (∀ {a b : Q} (e : a ⟶ b), ∀ x ∈ W₁ a, ρ.map e x ∈ W₁ b) →
    (∀ {a b : Q} (e : a ⟶ b), ∀ x ∈ W₂ a, ρ.map e x ∈ W₂ b) →
    (∀ v, IsCompl (W₁ v) (W₂ v)) →
    (∀ v, W₁ v = ⊥) ∨ (∀ v, W₂ v = ⊥)

/-- An auxiliary predicate at a vertex for a quiver-indexed object with finite free component modules. -/
def RepresentationTheory.CategoryTheory.QuiverLinearDiagrams.AuxiliaryQuiverModuleData.AuxiliaryVertexCondition
    {k : Type*} [CommSemiring k] {Q : Type*} [DecidableEq Q] [Quiver Q]
    (ρ : RepresentationTheory.CategoryTheory.QuiverLinearDiagrams.AuxiliaryQuiverModuleData k Q) (i : Q)
    [∀ v, Module.Free k (ρ.obj v)] [∀ v, Module.Finite k (ρ.obj v)] : Prop :=
  Module.finrank k (ρ.obj i) = 1 ∧ ∀ j, j ≠ i → Module.finrank k (ρ.obj j) = 0

/-- Given the displayed auxiliary hypothesis, the auxiliary condition implies either the auxiliary vertex condition or surjectivity of the associated map. -/
@[source_ref "Chapter6/Proposition6.6.5" (role := supporting)]
theorem RepresentationTheory.QuiverRepresentation.Auxiliary.QuiverRepresentation.Auxiliary.vertexConditionOrSurjective
    {k : Type*} [Field k] {Q : Type*} [DecidableEq Q] [Quiver Q]
    {ρ : RepresentationTheory.CategoryTheory.QuiverLinearDiagrams.AuxiliaryQuiverModuleData k Q} {i : Q}
    [∀ v, Module.Free k (ρ.obj v)] [∀ v, Module.Finite k (ρ.obj v)]
    (hi : RepresentationTheory.QuiverVertexPredicates.vertexProperty Q i)
    (hρ : ρ.AuxiliaryCondition) :
    ρ.AuxiliaryVertexCondition i ∨ Function.Surjective (ρ.auxiliaryDirectSumMap i) := by
  
  letI : ∀ v, AddCommGroup (ρ.obj v) := fun v => RepresentationTheory.QuiverRepresentationQuotientTransform.moduleAddCommGroupOfCommRing (k := k)
  
  have sink_no_out : ∀ {a b : Q} (_ : a ⟶ b), a ≠ i :=
    fun {_ b} e h => (hi b).false (h ▸ e)
  
  by_cases hsurj : Function.Surjective (ρ.auxiliaryDirectSumMap i)
  · exact Or.inr hsurj
  · 
    left
    
    obtain ⟨W, hW⟩ := Submodule.exists_isCompl (LinearMap.range (ρ.auxiliaryDirectSumMap i))

    set W₁ : ∀ v, Submodule k (ρ.obj v) := fun v =>
      if hv : v = i then hv ▸ LinearMap.range (ρ.auxiliaryDirectSumMap i) else ⊤
    set W₂ : ∀ v, Submodule k (ρ.obj v) := fun v =>
      if hv : v = i then hv ▸ W else ⊥
    
    have hW₁_sub : ∀ {a b : Q} (e : a ⟶ b), ∀ x ∈ W₁ a, ρ.map e x ∈ W₁ b := by
      intro a b e x _
      by_cases hb : b = i
      · 
        classical
        simp only [W₁, dif_pos hb]
        rw [show hb ▸ LinearMap.range (ρ.auxiliaryDirectSumMap i) = LinearMap.range (ρ.auxiliaryDirectSumMap b)
            from by subst hb; rfl]
        refine ⟨DirectSum.lof k (RepresentationTheory.AuxiliaryQuiverRepresentationTransform.auxiliaryTypeAt Q b)
          (fun j => ρ.obj j.1) ⟨a, e⟩ x, ?_⟩
        simp [RepresentationTheory.CategoryTheory.QuiverLinearDiagrams.AuxiliaryQuiverModuleData.auxiliaryDirectSumMap]
      · simp only [W₁, hb, dite_false]; exact Submodule.mem_top
    
    have hW₂_sub : ∀ {a b : Q} (e : a ⟶ b), ∀ x ∈ W₂ a, ρ.map e x ∈ W₂ b := by
      intro a b e x hx
      simp only [W₂, sink_no_out e, dite_false, Submodule.mem_bot] at hx
      rw [hx, map_zero]; exact Submodule.zero_mem _
    
    have hcompl : ∀ v, IsCompl (W₁ v) (W₂ v) := by
      intro v; by_cases hv : v = i
      · subst hv; simp only [W₁, W₂, dite_true]; exact hW
      · simp only [W₁, W₂, hv, dite_false]; exact isCompl_top_bot
    
    rcases hρ.2 W₁ W₂ hW₁_sub hW₂_sub hcompl with h1 | h2
    · 
      have hj_triv : ∀ j, j ≠ i → Subsingleton (ρ.obj j) := by
        intro j hj
        have h_top_eq_bot : (⊤ : Submodule k (ρ.obj j)) = ⊥ := by
          have := h1 j; simp only [W₁, hj, dite_false] at this; exact this
        exact subsingleton_of_forall_eq 0 fun x => by
          have hx : x ∈ (⊥ : Submodule k (ρ.obj j)) := h_top_eq_bot ▸ Submodule.mem_top
          rwa [Submodule.mem_bot] at hx
      
      have hi_nt : Nontrivial (ρ.obj i) := by
        obtain ⟨v, hv_nt⟩ := hρ.1
        by_cases hvi : v = i
        · exact hvi ▸ hv_nt
        · exact absurd (hj_triv v hvi) (not_subsingleton (α := ρ.obj v))
      haveI := hi_nt

      have h_simple : IsSimpleModule k (ρ.obj i) :=
        { eq_bot_or_eq_top := fun P => by
            obtain ⟨P', hP'⟩ := Submodule.exists_isCompl P
            set U₁ : ∀ v, Submodule k (ρ.obj v) := fun v =>
              if hv : v = i then hv ▸ P else ⊤
            set U₂ : ∀ v, Submodule k (ρ.obj v) := fun v =>
              if hv : v = i then hv ▸ P' else ⊥
            have hU₁_sub : ∀ {a b : Q} (e : a ⟶ b),
                ∀ x ∈ U₁ a, ρ.map e x ∈ U₁ b := by
              intro a b e x _
              haveI := hj_triv a (sink_no_out e)
              rw [Subsingleton.eq_zero x, map_zero]; exact Submodule.zero_mem _
            have hU₂_sub : ∀ {a b : Q} (e : a ⟶ b),
                ∀ x ∈ U₂ a, ρ.map e x ∈ U₂ b := by
              intro a b e x hx
              simp only [U₂, sink_no_out e, dite_false, Submodule.mem_bot] at hx
              rw [hx, map_zero]; exact Submodule.zero_mem _
            have hUcompl : ∀ v, IsCompl (U₁ v) (U₂ v) := by
              intro v; by_cases hv : v = i
              · subst hv; simp only [U₁, U₂, dite_true]; exact hP'
              · simp only [U₁, U₂, hv, dite_false]; exact isCompl_top_bot
            rcases hρ.2 U₁ U₂ hU₁_sub hU₂_sub hUcompl with hU1 | hU2
            · left; have := hU1 i; simp only [U₁, dite_true] at this; exact this
            · right
              have := hU2 i; simp only [U₂, dite_true] at this
              exact eq_top_of_isCompl_bot (this ▸ hP') }
      exact ⟨isSimpleModule_iff_finrank_eq_one.mp h_simple,
             fun j hj => by haveI := hj_triv j hj; exact Module.finrank_zero_of_subsingleton⟩
    · 
      have hW_bot : W = ⊥ := by
        have := h2 i; simp only [W₂, dite_true] at this; exact this
      exact absurd (LinearMap.range_eq_top.mp (eq_top_of_isCompl_bot (hW_bot ▸ hW))) hsurj

/-- Given the displayed auxiliary hypothesis, the auxiliary condition implies either the auxiliary vertex condition or injectivity of the associated map. -/
@[source_ref "Chapter6/Proposition6.6.5" (role := supporting)]
theorem RepresentationTheory.QuiverRepresentation.Auxiliary.QuiverRepresentation.Auxiliary.vertexConditionOrInjective
    {k : Type*} [Field k] {Q : Type*} [DecidableEq Q] [Quiver Q]
    {ρ : RepresentationTheory.CategoryTheory.QuiverLinearDiagrams.AuxiliaryQuiverModuleData k Q} {i : Q}
    [∀ v, Module.Free k (ρ.obj v)] [∀ v, Module.Finite k (ρ.obj v)]
    [Fintype (RepresentationTheory.QuiverRepresentationQuotientTransform.OutgoingArrow Q i)]
    (hi : RepresentationTheory.QuiverVertexPredicates.vertexCondition Q i)
    (hρ : ρ.AuxiliaryCondition) :
    ρ.AuxiliaryVertexCondition i ∨ Function.Injective (ρ.outgoingDirectSumMap i) := by
  
  letI : ∀ v, AddCommGroup (ρ.obj v) := fun v => RepresentationTheory.QuiverRepresentationQuotientTransform.moduleAddCommGroupOfCommRing (k := k)
  
  have source_no_in : ∀ {a b : Q} (_ : a ⟶ b), b ≠ i :=
    fun {a _} e h => (hi a).false (h ▸ e)
  
  by_cases hinj : Function.Injective (ρ.outgoingDirectSumMap i)
  · exact Or.inr hinj
  · 
    left
    
    have hker_ne_bot : LinearMap.ker (ρ.outgoingDirectSumMap i) ≠ ⊥ := by
      intro heq; exact hinj (LinearMap.ker_eq_bot.mp heq)
    
    obtain ⟨W, hW⟩ := Submodule.exists_isCompl (LinearMap.ker (ρ.outgoingDirectSumMap i))

    set W₁ : ∀ v, Submodule k (ρ.obj v) := fun v =>
      if hv : v = i then hv ▸ LinearMap.ker (ρ.outgoingDirectSumMap i) else ⊥
    set W₂ : ∀ v, Submodule k (ρ.obj v) := fun v =>
      if hv : v = i then hv ▸ W else ⊤

    have hW₁_sub : ∀ {a b : Q} (e : a ⟶ b), ∀ x ∈ W₁ a, ρ.map e x ∈ W₁ b := by
      intro a b e x hx
      have hb : b ≠ i := source_no_in e
      simp only [W₁, hb, dite_false]; simp only [Submodule.mem_bot]
      by_cases ha : a = i
      · 
        
        suffices ∀ (e' : i ⟶ b) (x' : ρ.obj i),
            x' ∈ LinearMap.ker (ρ.outgoingDirectSumMap i) → ρ.map e' x' = 0 by
          subst ha; exact this e x (by simpa [W₁, dif_pos rfl] using hx)
        intro e' x' hx'
        rw [LinearMap.mem_ker] at hx'

        suffices h_eval : (ρ.outgoingDirectSumMap i x') ⟨b, e'⟩ = ρ.map e' x' by
          rw [← h_eval, hx']; rfl

        classical
        
        change (DirectSum.component k (RepresentationTheory.QuiverRepresentationQuotientTransform.OutgoingArrow Q i)
          (fun s => ρ.obj s.1) ⟨b, e'⟩) (ρ.outgoingDirectSumMap i x') = ρ.map e' x'
        unfold RepresentationTheory.CategoryTheory.QuiverLinearDiagrams.AuxiliaryQuiverModuleData.outgoingDirectSumMap
        simp only [LinearMap.sum_apply, LinearMap.coe_comp, Function.comp_apply,
          map_sum, DirectSum.component.of, Finset.sum_dite_eq', Finset.mem_univ, ite_true]
      · 
        simp only [W₁, ha, dite_false, Submodule.mem_bot] at hx
        rw [hx, map_zero]
    
    have hW₂_sub : ∀ {a b : Q} (e : a ⟶ b), ∀ x ∈ W₂ a, ρ.map e x ∈ W₂ b := by
      intro a b e x _
      simp only [W₂, source_no_in e, dite_false]; exact Submodule.mem_top
    
    have hcompl : ∀ v, IsCompl (W₁ v) (W₂ v) := by
      intro v; by_cases hv : v = i
      · subst hv; simp only [W₁, W₂, dite_true]; exact hW
      · simp only [W₁, W₂, hv, dite_false]; exact isCompl_bot_top
    
    rcases hρ.2 W₁ W₂ hW₁_sub hW₂_sub hcompl with h1 | h2
    · 
      have hker_bot : LinearMap.ker (ρ.outgoingDirectSumMap i) = ⊥ := by
        have := h1 i; simp only [W₁, dite_true] at this; exact this
      exact absurd (LinearMap.ker_eq_bot.mp hker_bot) hinj
    · 
      have hj_triv : ∀ j, j ≠ i → Subsingleton (ρ.obj j) := by
        intro j hj
        have h_top_eq_bot : (⊤ : Submodule k (ρ.obj j)) = ⊥ := by
          have := h2 j; simp only [W₂, hj, dite_false] at this; exact this
        exact subsingleton_of_forall_eq 0 fun x => by
          have hx : x ∈ (⊥ : Submodule k (ρ.obj j)) := h_top_eq_bot ▸ Submodule.mem_top
          rwa [Submodule.mem_bot] at hx
      
      have hi_nt : Nontrivial (ρ.obj i) := by
        obtain ⟨v, hv_nt⟩ := hρ.1
        by_cases hvi : v = i
        · exact hvi ▸ hv_nt
        · exact absurd (hj_triv v hvi) (not_subsingleton (α := ρ.obj v))
      haveI := hi_nt
      
      have h_simple : IsSimpleModule k (ρ.obj i) :=
        { eq_bot_or_eq_top := fun P => by
            obtain ⟨P', hP'⟩ := Submodule.exists_isCompl P
            set U₁ : ∀ v, Submodule k (ρ.obj v) := fun v =>
              if hv : v = i then hv ▸ P else ⊥
            set U₂ : ∀ v, Submodule k (ρ.obj v) := fun v =>
              if hv : v = i then hv ▸ P' else ⊤
            have hU₁_sub : ∀ {a b : Q} (e : a ⟶ b),
                ∀ x ∈ U₁ a, ρ.map e x ∈ U₁ b := by
              intro a b e x hx
              simp only [U₁, source_no_in e, dite_false, Submodule.mem_bot]
              by_cases ha : a = i
              · simp only [U₁, ha, dite_true] at hx
                haveI := hj_triv b (source_no_in e)
                exact Subsingleton.eq_zero _
              · simp only [U₁, ha, dite_false, Submodule.mem_bot] at hx
                rw [hx, map_zero]
            have hU₂_sub : ∀ {a b : Q} (e : a ⟶ b),
                ∀ x ∈ U₂ a, ρ.map e x ∈ U₂ b := by
              intro a b e x _
              simp only [U₂, source_no_in e, dite_false]; exact Submodule.mem_top
            have hUcompl : ∀ v, IsCompl (U₁ v) (U₂ v) := by
              intro v; by_cases hv : v = i
              · subst hv; simp only [U₁, U₂, dite_true]; exact hP'
              · simp only [U₁, U₂, hv, dite_false]; exact isCompl_bot_top
            rcases hρ.2 U₁ U₂ hU₁_sub hU₂_sub hUcompl with hU1 | hU2
            · left; have := hU1 i; simp only [U₁, dite_true] at this; exact this
            · right
              have hP'_bot := hU2 i; simp only [U₂, dite_true] at hP'_bot
              exact eq_top_of_isCompl_bot (hP'_bot ▸ hP') }
      exact ⟨isSimpleModule_iff_finrank_eq_one.mp h_simple,
             fun j hj => by haveI := hj_triv j hj; exact Module.finrank_zero_of_subsingleton⟩
