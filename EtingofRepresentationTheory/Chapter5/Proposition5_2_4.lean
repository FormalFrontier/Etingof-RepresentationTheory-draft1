import Mathlib

/-!
# Proposition 5.2.4: Ring and Field Properties of Algebraic Numbers/Integers

(i) The set of algebraic integers `ℤ̄` is a ring.

(ii) The set of algebraic numbers `ℚ̄` is a field. Namely, it is an algebraic closure of the
field of rational numbers.

## Formalization

Rather than only recording elementwise closure of `IsAlgebraic ℚ` / `IsIntegral ℤ` under the
ring operations, we bundle the algebraic integers and the algebraic numbers as the honest
subobjects of `ℂ` that the book names, and expose the proposition's final, strongest claim:
the algebraic numbers form *an algebraic closure of `ℚ`*.

* `Etingof.algebraicIntegers` is `integralClosure ℤ ℂ`, the subring `ℤ̄ ⊆ ℂ` of algebraic
  integers (Proposition 5.2.4(i)).
* `Etingof.algebraicNumbers` is `algebraicClosure ℚ ℂ`, the subfield `ℚ̄ ⊆ ℂ` of algebraic
  numbers, packaged as an `IntermediateField ℚ ℂ` (Proposition 5.2.4(ii)).
* `Etingof.Proposition5_2_4_isAlgClosure` records that `ℚ̄` is an algebraic closure of `ℚ`:
  it is algebraically closed and algebraic over `ℚ`. This is the proposition's headline
  statement.

The elementwise operation-closure statements `Proposition5_2_4_ring` and
`Proposition5_2_4_field` are retained, now proved as corollaries of membership in the bundled
subobjects.

## Mathlib correspondence

* `integralClosure R A : Subalgebra R A` bundles the integral elements; `mem_integralClosure_iff`
  identifies its members with `IsIntegral R`.
* `algebraicClosure F E : IntermediateField F E` (the relative algebraic closure) bundles the
  algebraic elements as a subfield; `mem_algebraicClosure_iff` identifies its members with
  `IsAlgebraic F`.
* When `E` is algebraically closed, `algebraicClosure.isAlgClosure` provides
  `IsAlgClosure F (algebraicClosure F E)`. Since `ℂ` is algebraically closed
  (`Complex.isAlgClosed`), this specializes to `IsAlgClosure ℚ (algebraicClosure ℚ ℂ)`.
-/

namespace Etingof

/-- The ring `ℤ̄` of algebraic integers, bundled as the subring `integralClosure ℤ ℂ` of `ℂ`.
(Etingof Proposition 5.2.4(i)) -/
noncomputable abbrev algebraicIntegers : Subalgebra ℤ ℂ := integralClosure ℤ ℂ

/-- An element of `ℂ` is an algebraic integer (lies in `ℤ̄`) iff it is integral over `ℤ`. -/
theorem mem_algebraicIntegers {x : ℂ} : x ∈ algebraicIntegers ↔ IsIntegral ℤ x :=
  mem_integralClosure_iff ℤ ℂ

/-- The subfield `ℚ̄` of algebraic numbers, bundled as the relative algebraic closure of `ℚ`
in `ℂ`, an `IntermediateField ℚ ℂ`. (Etingof Proposition 5.2.4(ii)) -/
noncomputable abbrev algebraicNumbers : IntermediateField ℚ ℂ := algebraicClosure ℚ ℂ

/-- An element of `ℂ` is an algebraic number (lies in `ℚ̄`) iff it is algebraic over `ℚ`. -/
theorem mem_algebraicNumbers {x : ℂ} : x ∈ algebraicNumbers ↔ IsAlgebraic ℚ x :=
  mem_algebraicClosure_iff

/-- **The headline statement of Proposition 5.2.4(ii):** the field `ℚ̄` of algebraic numbers is
an algebraic closure of `ℚ`. Concretely (unfolding `IsAlgClosure`) it is algebraically closed
and algebraic over `ℚ`. -/
theorem Proposition5_2_4_isAlgClosure : IsAlgClosure ℚ algebraicNumbers :=
  inferInstance

/-- `ℚ̄` is algebraic over `ℚ`: every algebraic number is (as expected) algebraic over `ℚ`. -/
theorem Proposition5_2_4_isAlgebraic : Algebra.IsAlgebraic ℚ algebraicNumbers :=
  inferInstance

/-- `ℚ̄` is algebraically closed: this is the substantive half of "algebraic closure". -/
theorem Proposition5_2_4_isAlgClosed : IsAlgClosed algebraicNumbers :=
  IsAlgClosure.isAlgClosed (R := ℚ)

/-- The set of algebraic integers in ℂ forms a subring: it is closed under addition and
multiplication. Now a corollary of the bundled subring `algebraicIntegers`.
(Etingof Proposition 5.2.4(i)) -/
theorem Proposition5_2_4_ring :
    ∀ x y : ℂ, IsIntegral ℤ x → IsIntegral ℤ y →
      IsIntegral ℤ (x + y) ∧ IsIntegral ℤ (x * y) := by
  intro x y hx hy
  rw [← mem_algebraicIntegers] at hx hy
  exact ⟨mem_algebraicIntegers.mp (add_mem hx hy), mem_algebraicIntegers.mp (mul_mem hx hy)⟩

/-- The set of algebraic numbers forms a subfield of ℂ (the algebraic closure of ℚ): it is
closed under addition, multiplication, and under taking inverses of nonzero elements. Now a
corollary of the bundled subfield `algebraicNumbers`: an `IntermediateField` is closed under
all field operations. The book proves inverse-closure by noting that if `α ≠ 0` is a root of a
degree-`d` polynomial `p(x)`, then `α⁻¹` is a root of `xᵈ p(1/x)`.
(Etingof Proposition 5.2.4(ii)) -/
theorem Proposition5_2_4_field :
    ∀ x y : ℂ, IsAlgebraic ℚ x → IsAlgebraic ℚ y →
      IsAlgebraic ℚ (x + y) ∧ IsAlgebraic ℚ (x * y) ∧
        (x ≠ 0 → IsAlgebraic ℚ x⁻¹) := by
  intro x y hx hy
  rw [← mem_algebraicNumbers] at hx hy
  exact ⟨mem_algebraicNumbers.mp (add_mem hx hy),
    mem_algebraicNumbers.mp (mul_mem hx hy),
    fun _ => mem_algebraicNumbers.mp (algebraicNumbers.inv_mem hx)⟩

end Etingof
