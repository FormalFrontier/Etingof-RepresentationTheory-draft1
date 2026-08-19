/-
Copyright (c) 2026 mathlib-initiative. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

import Mathlib.Order.Zorn
import Mathlib.RingTheory.Ideal.Maximal
import Mathlib.RingTheory.TwoSidedIdeal.Lattice
import RepresentationTheory.Alignment.Attribute

/-! # Existence of coatoms in subobject lattices -/

namespace RepresentationTheory.Ring.CoatomExistence

variable (A : Type*) [Ring A] [Nontrivial A]

/-- A nontrivial ring admits a coatom among the displayed subobjects. -/
@[source_ref "Chapter2/Problem2.4.1" (role := supporting)]
theorem exists_coatom_subobject : ∃ I : Submodule A A, IsCoatom I :=
  let ⟨I, hI⟩ := Ideal.exists_maximal A
  ⟨I, Ideal.isMaximal_def.mp hI⟩

/-- A nontrivial ring admits a coatom among the displayed subobjects. -/
@[source_ref "Chapter2/Problem2.4.1" (role := supporting)]
theorem exists_coatom_subobject_aux1 : ∃ I : Submodule Aᵐᵒᵖ Aᵐᵒᵖ, IsCoatom I :=
  let ⟨I, hI⟩ := Ideal.exists_maximal Aᵐᵒᵖ
  ⟨I, Ideal.isMaximal_def.mp hI⟩

/-- A nontrivial ring admits a coatom among the displayed subobjects. -/
@[source_ref "Chapter2/Problem2.4.1" (role := supporting)]
theorem exists_coatom_subobject_aux2 : ∃ I : TwoSidedIdeal A, IsCoatom I := by
  have bot_ne_top : (⊥ : TwoSidedIdeal A) ≠ ⊤ := by
    intro h
    have one_mem : (1 : A) ∈ (⊥ : TwoSidedIdeal A) := by
      rw [h]
      trivial
    simp only [TwoSidedIdeal.mem_bot] at one_mem
    exact one_ne_zero one_mem
  have chain_upper_bound : ∀ c ⊆ {I : TwoSidedIdeal A | I ≠ ⊤}, IsChain (· ≤ ·) c →
      ∃ ub ∈ {I : TwoSidedIdeal A | I ≠ ⊤}, ∀ z ∈ c, z ≤ ub := by
    intro c hc chain
    rcases c.eq_empty_or_nonempty with rfl | ⟨I₀, hI₀⟩
    · exact ⟨⊥, bot_ne_top, by simp⟩
    · refine ⟨TwoSidedIdeal.mk' {x | ∃ I ∈ c, x ∈ I}
        ⟨I₀, hI₀, I₀.zero_mem⟩ ?_ ?_ ?_ ?_, ?_, ?_⟩
      · rintro x y ⟨I, hI, hx⟩ ⟨J, hJ, hy⟩
        rcases chain.total hI hJ with h | h
        · exact ⟨J, hJ, J.add_mem (h hx) hy⟩
        · exact ⟨I, hI, I.add_mem hx (h hy)⟩
      · rintro x ⟨I, hI, hx⟩
        exact ⟨I, hI, I.neg_mem hx⟩
      · rintro x y ⟨I, hI, hy⟩
        exact ⟨I, hI, I.mul_mem_left x y hy⟩
      · rintro x y ⟨I, hI, hx⟩
        exact ⟨I, hI, I.mul_mem_right x y hx⟩
      · intro union_eq_top
        have one_mem := (TwoSidedIdeal.one_mem_iff _).mpr union_eq_top
        rw [TwoSidedIdeal.mem_mk'] at one_mem
        obtain ⟨I, hI, one_mem⟩ := one_mem
        exact (hc hI) ((TwoSidedIdeal.one_mem_iff I).mp one_mem)
      · intro z hz x hx
        exact (TwoSidedIdeal.mem_mk' _ _ _ _ _ _ x).mpr ⟨z, hz, hx⟩
  obtain ⟨m, hm⟩ := zorn_le₀ {I : TwoSidedIdeal A | I ≠ ⊤} chain_upper_bound
  refine ⟨m, hm.1, fun b hb ↦ ?_⟩
  by_contra hbne
  exact absurd (lt_of_le_of_lt (hm.2 hbne hb.le) hb) (lt_irrefl b)

end RepresentationTheory.Ring.CoatomExistence
