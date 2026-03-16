import Mathlib

/-!
# Example 4.8.1: Character Tables

Character tables for Q₈, S₄, and A₅.

**Q₈**: 5 conjugacy classes, 5 irreducible representations (four 1-dim, one 2-dim).
The 2D representation has χ(1) = 2, χ(-1) = -2, χ(±i) = χ(±j) = χ(±k) = 0.

**S₄**: 5 conjugacy classes, representations of dimensions 1, 1, 2, 3, 3.
Key values computed from cube rotation geometry (trace = 1 + 2cos φ).

**A₅**: 5 conjugacy classes, representations of dimensions 1, 3, 3, 4, 5.
The two 3-dimensional representations have characters involving the golden ratio
φ = (1+√5)/2.

## Mathlib correspondence

Character tables are not systematically formalized in Mathlib. This is primarily
a computational example.
-/

set_option linter.style.nativeDecide false in
/-- Q₈ has exactly 5 conjugacy classes, hence 5 irreducible representations.
(Etingof Example 4.8.1) -/
theorem Etingof.Example4_8_1_Q8_conj_classes :
    Fintype.card (ConjClasses (QuaternionGroup 2)) = 5 := by
  native_decide

set_option linter.style.nativeDecide false in
/-- Q₈ has order 8. Combined with 5 conjugacy classes and the sum-of-squares formula
∑ dᵢ² = |G|, the only solution is dimensions 1,1,1,1,2. (Etingof Example 4.8.1) -/
theorem Etingof.Example4_8_1_Q8_card :
    Fintype.card (QuaternionGroup 2) = 8 := by
  native_decide

set_option linter.style.nativeDecide false in
/-- A₅ has exactly 5 conjugacy classes. (Etingof Example 4.8.1) -/
theorem Etingof.Example4_8_1_A5_conj_classes :
    Fintype.card (ConjClasses (alternatingGroup (Fin 5))) = 5 := by
  native_decide
