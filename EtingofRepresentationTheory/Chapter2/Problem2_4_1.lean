import Mathlib

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
* **right ideals** of `A` are `Submodule Aᵐᵒᵖ Aᵐᵒᵖ` — a submodule for the left action of the
  opposite ring is precisely a subset closed under right multiplication by `A`;
* **two-sided ideals** are `TwoSidedIdeal A`.

`IsCoatom I` says `I ≠ ⊤` and any ideal strictly containing `I` equals `⊤`, i.e. `I` is maximal.

This is the **statement pass**: the three existence statements are recorded with `sorry` proofs
(each is proved by Zorn's lemma in the proof phase).
-/

namespace Etingof.Problem2_4_1

variable (A : Type*) [Ring A] [Nontrivial A]

/-- Every nontrivial unital ring has a maximal **left** ideal. (Etingof Problem 2.4.1) -/
theorem exists_maximal_left_ideal : ∃ I : Submodule A A, IsCoatom I := by
  sorry

/-- Every nontrivial unital ring has a maximal **right** ideal, modelled as a maximal left ideal
of the opposite ring `Aᵐᵒᵖ`. (Etingof Problem 2.4.1) -/
theorem exists_maximal_right_ideal : ∃ I : Submodule Aᵐᵒᵖ Aᵐᵒᵖ, IsCoatom I := by
  sorry

/-- Every nontrivial unital ring has a maximal **two-sided** ideal. (Etingof Problem 2.4.1) -/
theorem exists_maximal_twoSided_ideal : ∃ I : TwoSidedIdeal A, IsCoatom I := by
  sorry

end Etingof.Problem2_4_1
