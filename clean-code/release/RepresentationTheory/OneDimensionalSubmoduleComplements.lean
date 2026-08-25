/-
Copyright (c) 2026 mathlib-initiative. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: mathlib-initiative
-/

import Mathlib
import RepresentationTheory.Alignment.Attribute

/-!
# One-Dimensional Submodule Complements

A characterization of one-dimensional vector spaces using complementary submodules.
-/

/-- A finite-dimensional vector space is nontrivial and every pair of complementary submodules has one member equal to the zero submodule if and only if its dimension is one. -/
@[source_ref "Chapter6/Example6.2.2" (role := supporting)]
theorem RepresentationTheory.OneDimensionalSubmoduleComplements.nontrivial_and_isCompl_eq_bot_iff_finrank_eq_one
    (k : Type*) [Field k]
    (V : Type*) [AddCommGroup V] [Module k V] [FiniteDimensional k V] :
    (Nontrivial V ∧ ∀ (p q : Submodule k V), IsCompl p q → p = ⊥ ∨ q = ⊥) ↔
    Module.finrank k V = 1 := by
  constructor
  · intro ⟨hnt, hind⟩
    by_contra h
    have hpos : 0 < Module.finrank k V := Module.finrank_pos (R := k) (M := V)
    have hge2 : 2 ≤ Module.finrank k V := by omega
    obtain ⟨v, hv⟩ := exists_ne (0 : V)
    set p := Submodule.span k {v}
    have hp_rank : Module.finrank k p = 1 := finrank_span_singleton hv
    obtain ⟨q, hpq⟩ := Submodule.exists_isCompl p
    have hq_rank : Module.finrank k q = Module.finrank k V - 1 := by
      have := Submodule.finrank_add_eq_of_isCompl hpq
      omega
    rcases hind p q hpq with hp_bot | hq_bot
    · have : v ∈ (⊥ : Submodule k V) := hp_bot ▸ Submodule.subset_span (Set.mem_singleton v)
      simp only [Submodule.mem_bot] at this
      exact hv this
    · have : Module.finrank k q = 0 := by rw [hq_bot]; exact finrank_bot k V
      omega
  · intro h1
    refine ⟨Module.nontrivial_of_finrank_eq_succ (n := 0) (by omega), fun p q hpq => ?_⟩
    have hdim : Module.finrank k p + Module.finrank k q = 1 := by
      rw [Submodule.finrank_add_eq_of_isCompl hpq, h1]
    rcases Nat.eq_zero_or_pos (Module.finrank k p) with hp | hp
    · left; rwa [Submodule.finrank_eq_zero] at hp
    · right; have : Module.finrank k q = 0 := by omega
      rwa [Submodule.finrank_eq_zero] at this
