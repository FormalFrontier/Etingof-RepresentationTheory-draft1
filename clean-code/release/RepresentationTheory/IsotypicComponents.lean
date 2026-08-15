/-
Copyright (c) 2026 FormalFrontier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENCE.
Authors: FormalFrontier
-/

import RepresentationTheory.CentralizerDecomposition

/-!
# Representatives of isotypic components

This module constructs complete irredundant families of simple submodules for semisimple algebra
actions and for their centralizers.
-/

open scoped TensorProduct

universe u v w

namespace RepresentationTheory.IsotypicComponents

variable (k : Type u) [Field k]
  (E : Type v) [AddCommGroup E] [Module k E] [Module.Finite k E]

omit [Module.Finite k E] in
/-- In a semisimple algebra action, every simple module occurs as a simple submodule. -/
theorem exists_simpleSubmodule_equiv_of_isSemisimple
    (C : Subalgebra k (Module.End k E)) [IsSemisimpleRing C]
    (S : Type w) [AddCommGroup S] [Module C S] [IsSimpleModule C S] :
    ∃ W : Submodule C E, IsSimpleModule C W ∧ Nonempty (S ≃ₗ[C] W) := by
  classical
  haveI : Nontrivial S := IsSimpleModule.nontrivial C S
  obtain ⟨s₀, hs₀⟩ := exists_ne (0 : S)
  set g : (↥C) →ₗ[↥C] S := LinearMap.toSpanSingleton (↥C) S s₀ with hg
  have hg_surj : Function.Surjective g := by
    intro x
    have hspan : Submodule.span (↥C) {s₀} = ⊤ := by
      rcases eq_bot_or_eq_top (Submodule.span (↥C) {s₀}) with h | h
      · exact absurd (by simpa [h] using Submodule.mem_span_singleton_self (R := ↥C) s₀) hs₀
      · exact h
    have hx : x ∈ Submodule.span (↥C) {s₀} := by
      rw [hspan]
      trivial
    rw [Submodule.mem_span_singleton] at hx
    obtain ⟨a, ha⟩ := hx
    exact ⟨a, by simp only [hg, LinearMap.toSpanSingleton_apply]; exact ha⟩
  let equivS : ((↥C) ⧸ LinearMap.ker g) ≃ₗ[↥C] S := g.quotKerEquivOfSurjective hg_surj
  obtain ⟨P, ⟨eP⟩⟩ :=
    IsSemisimpleModule.exists_submodule_linearEquiv_quotient (LinearMap.ker g)
  let ιSC : S →ₗ[↥C] (↥C) := P.subtype ∘ₗ (equivS.symm.trans eP.symm).toLinearMap
  have hι_inj : Function.Injective ιSC :=
    Subtype.val_injective.comp (equivS.symm.trans eP.symm).injective
  let ψ : (↥C) →ₗ[↥C] (E → E) :=
    { toFun := fun c e => c.val e
      map_add' := fun c c' => by ext e; simp
      map_smul' := fun a c => by ext e; rfl }
  have hψ_inj : Function.Injective ψ := by
    rw [injective_iff_map_eq_zero]
    intro c hc
    have hval : (c : Module.End k E) = 0 := by
      ext e
      exact congr_fun hc e
    exact Subtype.ext (by simpa using hval)
  let emb : S →ₗ[↥C] (E → E) := ψ ∘ₗ ιSC
  have hemb_inj : Function.Injective emb := hψ_inj.comp hι_inj
  have hemb_s₀ : emb s₀ ≠ 0 := fun h => hs₀ (hemb_inj (by rw [h, map_zero]))
  have hcoord : ∃ e : E, (emb s₀) e ≠ 0 := by
    by_contra hh
    apply hemb_s₀
    funext e
    by_contra hne
    exact hh ⟨e, hne⟩
  obtain ⟨e, he⟩ := hcoord
  let f : S →ₗ[↥C] E := (LinearMap.proj e) ∘ₗ emb
  have hf_ne : f ≠ 0 := fun h => he (by
    have : f s₀ = 0 := by rw [h]; rfl
    exact this)
  have hker : LinearMap.ker f = ⊥ := by
    rcases eq_bot_or_eq_top (LinearMap.ker f) with h | h
    · exact h
    · exact absurd (LinearMap.ker_eq_top.mp h) hf_ne
  have hf_inj : Function.Injective f := LinearMap.ker_eq_bot.mp hker
  refine ⟨LinearMap.range f, ?_, ⟨LinearEquiv.ofInjective f hf_inj⟩⟩
  exact IsSimpleModule.congr (LinearEquiv.ofInjective f hf_inj).symm

omit [Module.Finite k E] in
/-- For a semisimple algebra action, selects a submodule inside each isotypic component so that
distinct selections are nonisomorphic and every simple module is represented. -/
theorem exists_isotypicComponent_representatives_of_isSemisimple
    (C : Subalgebra k (Module.End k E)) [IsSemisimpleRing C] :
    ∃ (V : isotypicComponents C E → Submodule C E) (_ : ∀ c, IsSimpleModule C (V c)),
      (∀ c, (V c : Submodule C E) ≤ (c : Submodule C E)) ∧
      (∀ c c', Nonempty (↥(V c) ≃ₗ[C] ↥(V c')) → c = c') ∧
      ∀ (S : Type w) [AddCommGroup S] [Module C S] [IsSimpleModule C S],
        ∃ c, Nonempty (S ≃ₗ[C] ↥(V c)) := by
  classical
  haveI : IsSemisimpleModule C E := IsSemisimpleRing.isSemisimpleModule
  let V : isotypicComponents C E → Submodule C E := fun c =>
    ((IsSemisimpleModule.eq_bot_or_exists_simple_le (c.1 : Submodule C E)).resolve_left
      (bot_lt_isotypicComponents c.2).ne').choose
  have V_le : ∀ c, V c ≤ c.1 := fun c =>
    ((IsSemisimpleModule.eq_bot_or_exists_simple_le (c.1 : Submodule C E)).resolve_left
      (bot_lt_isotypicComponents c.2).ne').choose_spec.1
  have V_simple : ∀ c, IsSimpleModule C (V c) := fun c =>
    ((IsSemisimpleModule.eq_bot_or_exists_simple_le (c.1 : Submodule C E)).resolve_left
      (bot_lt_isotypicComponents c.2).ne').choose_spec.2
  have V_spec : ∀ c, (c.1 : Submodule C E) = isotypicComponent C E (V c) := by
    intro c
    haveI := V_simple c
    exact eq_isotypicComponent_of_le c.2 (V_le c)
  refine ⟨V, V_simple, V_le, ?_, ?_⟩
  · rintro c c' ⟨e⟩
    have h_eq : isotypicComponent C E (V c) = isotypicComponent C E (V c') :=
      e.isotypicComponent_eq
    have hc : (c.1 : Submodule C E) = c'.1 := by
      rw [V_spec c, V_spec c']
      exact h_eq
    exact Subtype.ext hc
  · intro S _ _ _
    obtain ⟨W, hW_simple, ⟨eSW⟩⟩ := exists_simpleSubmodule_equiv_of_isSemisimple k E C S
    haveI := hW_simple
    set c : isotypicComponents C E := ⟨isotypicComponent C E W, ⟨W, hW_simple, rfl⟩⟩ with hc
    haveI := V_simple c
    have hcomp : isotypicComponent C E (V c) = isotypicComponent C E W := (V_spec c).symm
    have hWle : W ≤ isotypicComponent C E (V c) := by
      rw [hcomp]
      exact Submodule.le_isotypicComponent W
    obtain ⟨eWV⟩ :=
      isIsotypicOfType_submodule_iff.mp
        (IsIsotypicOfType.isotypicComponent C E (V c)) W hWle
    exact ⟨c, ⟨eSW.trans eWV⟩⟩

omit [Module.Finite k E] in
/-- A simple module is linearly equivalent to a simple submodule of the ambient module. -/
theorem exists_simpleSubmodule_equiv
    (A : Subalgebra k (Module.End k E)) [IsSemisimpleRing A] [FaithfulSMul A E]
    (S : Type w) [AddCommGroup S] [Module A S] [IsSimpleModule A S] :
    ∃ W : Submodule A E, IsSimpleModule A W ∧ Nonempty (S ≃ₗ[A] W) :=
  exists_simpleSubmodule_equiv_of_isSemisimple k E A S

/-- A simple module for the centralizer is linearly equivalent to one of its simple submodules. -/
theorem exists_centralizer_simpleSubmodule_equiv
    (A : Subalgebra k (Module.End k E)) [IsSemisimpleRing A] [FaithfulSMul A E]
    (T : Type w)
    [AddCommGroup T]
    [Module (↥(Subalgebra.centralizer k (A : Set (Module.End k E)))) T]
    [IsSimpleModule (↥(Subalgebra.centralizer k (A : Set (Module.End k E)))) T] :
    ∃ W : Submodule (↥(Subalgebra.centralizer k (A : Set (Module.End k E)))) E,
      IsSimpleModule (↥(Subalgebra.centralizer k (A : Set (Module.End k E)))) W ∧
      Nonempty (T ≃ₗ[↥(Subalgebra.centralizer k (A : Set (Module.End k E)))] W) := by
  haveI : IsSemisimpleRing (↥(Subalgebra.centralizer k (A : Set (Module.End k E)))) :=
    RepresentationTheory.CentralizerDecomposition.isSemisimpleRing_centralizer k E A
  exact exists_simpleSubmodule_equiv_of_isSemisimple k E
    (Subalgebra.centralizer k (A : Set (Module.End k E))) T

omit [Module.Finite k E] in
/-- Constructs one submodule from each isomorphism class of simple constituents in the isotypic
decomposition. -/
theorem exists_isotypicComponent_representatives
    (A : Subalgebra k (Module.End k E)) [IsSemisimpleRing A] [FaithfulSMul A E] :
    ∃ (V : isotypicComponents A E → Submodule A E) (_ : ∀ c, IsSimpleModule A (V c)),
      (∀ c, (V c : Submodule A E) ≤ (c : Submodule A E)) ∧
      (∀ c c', Nonempty (↥(V c) ≃ₗ[A] ↥(V c')) → c = c') ∧
      ∀ (S : Type w) [AddCommGroup S] [Module A S] [IsSimpleModule A S],
        ∃ c, Nonempty (S ≃ₗ[A] ↥(V c)) :=
  exists_isotypicComponent_representatives_of_isSemisimple k E A

/-- Constructs representatives for the centralizer's isotypic components, one for every simple
module class. -/
theorem exists_centralizer_isotypicComponent_representatives
    (A : Subalgebra k (Module.End k E)) [IsSemisimpleRing A] [FaithfulSMul A E] :
    ∃ (W : isotypicComponents (Subalgebra.centralizer k (A : Set (Module.End k E))) E →
          Submodule (↥(Subalgebra.centralizer k (A : Set (Module.End k E)))) E)
        (_ : ∀ c, IsSimpleModule
          (↥(Subalgebra.centralizer k (A : Set (Module.End k E)))) (W c)),
      (∀ c, (W c : Submodule (↥(Subalgebra.centralizer k (A : Set (Module.End k E)))) E) ≤
          (c : Submodule (↥(Subalgebra.centralizer k (A : Set (Module.End k E)))) E)) ∧
      (∀ c c', Nonempty
          (↥(W c) ≃ₗ[↥(Subalgebra.centralizer k (A : Set (Module.End k E)))] ↥(W c')) → c = c') ∧
      ∀ (T : Type w) [AddCommGroup T]
        [Module (↥(Subalgebra.centralizer k (A : Set (Module.End k E)))) T]
        [IsSimpleModule (↥(Subalgebra.centralizer k (A : Set (Module.End k E)))) T],
        ∃ c, Nonempty
          (T ≃ₗ[↥(Subalgebra.centralizer k (A : Set (Module.End k E)))] ↥(W c)) := by
  haveI : IsSemisimpleRing (↥(Subalgebra.centralizer k (A : Set (Module.End k E)))) :=
    RepresentationTheory.CentralizerDecomposition.isSemisimpleRing_centralizer k E A
  exact exists_isotypicComponent_representatives_of_isSemisimple k E
    (Subalgebra.centralizer k (A : Set (Module.End k E)))

end RepresentationTheory.IsotypicComponents
