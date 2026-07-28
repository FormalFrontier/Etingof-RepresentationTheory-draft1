import Mathlib.Order.Zorn
import Mathlib.RingTheory.Ideal.Maximal
import Mathlib.RingTheory.TwoSidedIdeal.Lattice

/-!
# Problem 2.4.1: Existence of maximal ideals

A **maximal** ideal in a ring `A` is an ideal `I ≠ A` such that any strictly larger ideal
coincides with `A`. (The definition is made for left, right, or two-sided ideals.) The problem
asks to show that any unital ring has a maximal left, right, and two-sided ideal, using Zorn's
lemma.

## Formalization

"Maximal ideal" in Etingof's sense (proper, and any strictly larger ideal is the whole ring) is
exactly `IsCoatom` in the corresponding lattice of ideals:

* **left ideals** of `A` are `Submodule A A` (the left `A`-module structure on `A`);
* **right ideals** of `A` are `Submodule Aᵐᵒᵖ Aᵐᵒᵖ`: a submodule for the left action of the
  opposite ring is precisely a subset closed under right multiplication by `A`;
* **two-sided ideals** are `TwoSidedIdeal A`.

`IsCoatom I` says `I ≠ ⊤` and any ideal strictly containing `I` equals `⊤`, i.e. `I` is maximal.

The left and right cases follow directly from Mathlib's Krull theorem `Ideal.exists_maximal`
(the right case is the left case for `Aᵐᵒᵖ`). The two-sided case is proved by Zorn's lemma: the
union of a chain of proper two-sided ideals is again a proper two-sided ideal, because `1` lies in
none of them.
-/

namespace Etingof.Problem2_4_1

variable (A : Type*) [Ring A] [Nontrivial A]

/-- Every nontrivial unital ring has a maximal left ideal. (Etingof Problem 2.4.1) -/
theorem exists_maximal_left_ideal : ∃ I : Submodule A A, IsCoatom I :=
  let ⟨I, hI⟩ := Ideal.exists_maximal A
  ⟨I, Ideal.isMaximal_def.mp hI⟩

/-- Every nontrivial unital ring has a maximal right ideal, modelled as a maximal left ideal
of the opposite ring `Aᵐᵒᵖ`. (Etingof Problem 2.4.1) -/
theorem exists_maximal_right_ideal : ∃ I : Submodule Aᵐᵒᵖ Aᵐᵒᵖ, IsCoatom I :=
  let ⟨I, hI⟩ := Ideal.exists_maximal Aᵐᵒᵖ
  ⟨I, Ideal.isMaximal_def.mp hI⟩

/-- Every nontrivial unital ring has a maximal two-sided ideal. (Etingof Problem 2.4.1) -/
theorem exists_maximal_twoSided_ideal : ∃ I : TwoSidedIdeal A, IsCoatom I := by
  -- `⊥ ≠ ⊤` since `1 ≠ 0`.
  have hbot : (⊥ : TwoSidedIdeal A) ≠ ⊤ := by
    intro h
    have h1 : (1 : A) ∈ (⊥ : TwoSidedIdeal A) := by rw [h]; trivial
    simp only [TwoSidedIdeal.mem_bot] at h1
    exact one_ne_zero h1
  -- Every chain of proper ideals has a proper upper bound (its union).
  have hbound : ∀ c ⊆ {I : TwoSidedIdeal A | I ≠ ⊤}, IsChain (· ≤ ·) c →
      ∃ ub ∈ {I : TwoSidedIdeal A | I ≠ ⊤}, ∀ z ∈ c, z ≤ ub := by
    intro c hcs hchain
    rcases c.eq_empty_or_nonempty with rfl | ⟨I₀, hI₀⟩
    · exact ⟨⊥, hbot, by simp⟩
    · -- The union of the chain, as a two-sided ideal.
      refine ⟨TwoSidedIdeal.mk' {x | ∃ I ∈ c, x ∈ I}
        ⟨I₀, hI₀, I₀.zero_mem⟩ ?_ ?_ ?_ ?_, ?_, ?_⟩
      · rintro x y ⟨I, hI, hx⟩ ⟨J, hJ, hy⟩
        rcases hchain.total hI hJ with h | h
        · exact ⟨J, hJ, J.add_mem (h hx) hy⟩
        · exact ⟨I, hI, I.add_mem hx (h hy)⟩
      · rintro x ⟨I, hI, hx⟩
        exact ⟨I, hI, I.neg_mem hx⟩
      · rintro x y ⟨I, hI, hy⟩
        exact ⟨I, hI, I.mul_mem_left x y hy⟩
      · rintro x y ⟨I, hI, hx⟩
        exact ⟨I, hI, I.mul_mem_right x y hx⟩
      · -- The union is proper: `1` is in it iff it is in some member of the chain.
        intro hUtop
        have h1 := (TwoSidedIdeal.one_mem_iff _).mpr hUtop
        rw [TwoSidedIdeal.mem_mk'] at h1
        obtain ⟨I, hI, h1⟩ := h1
        exact (hcs hI) ((TwoSidedIdeal.one_mem_iff I).mp h1)
      · -- The union is an upper bound of the chain.
        intro z hz x hx
        exact (TwoSidedIdeal.mem_mk' _ _ _ _ _ _ x).mpr ⟨z, hz, hx⟩
  -- Zorn's lemma yields a maximal proper ideal, which is a coatom.
  obtain ⟨m, hm⟩ := zorn_le₀ {I : TwoSidedIdeal A | I ≠ ⊤} hbound
  refine ⟨m, hm.1, fun b hb => ?_⟩
  by_contra hbne
  exact absurd (lt_of_le_of_lt (hm.2 hbne hb.le) hb) (lt_irrefl b)

end Etingof.Problem2_4_1
