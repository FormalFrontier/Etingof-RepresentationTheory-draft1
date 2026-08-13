import Mathlib
import RepresentationTheory.Alignment.Attribute

namespace RepresentationTheory.NumberTheory.AlgebraicNumber.Complex

/-- A distinguished integer subalgebra of the complex numbers. -/
@[source_ref "Chapter5/Discussion_after_Proposition5.2.3" (role := primary),
  source_ref "Chapter5/Proposition5.2.4" (role := primary)]
noncomputable abbrev distinguishedIntSubalgebra : Subalgebra ℤ ℂ := integralClosure ℤ ℂ

/-- Membership in the distinguished integer subalgebra is equivalent to integrality over the
integers. -/
@[source_ref "Chapter5/Discussion_after_Proposition5.2.3" (role := supporting)]
theorem mem_distinguishedIntSubalgebra_iff {x : ℂ} :
    x ∈ distinguishedIntSubalgebra ↔ IsIntegral ℤ x :=
  mem_integralClosure_iff ℤ ℂ

/-- A distinguished rational intermediate field in the complex numbers. -/
@[source_ref "Chapter5/Discussion_after_Proposition5.2.3" (role := primary),
  source_ref "Chapter5/Proposition5.2.4" (role := primary)]
noncomputable abbrev distinguishedRatIntermediateField : IntermediateField ℚ ℂ :=
  algebraicClosure ℚ ℂ

/-- Membership in the distinguished rational intermediate field is equivalent to algebraicity
over the rationals. -/
@[source_ref "Chapter5/Discussion_after_Proposition5.2.3" (role := supporting)]
theorem mem_distinguishedRatIntermediateField_iff {x : ℂ} :
    x ∈ distinguishedRatIntermediateField ↔ IsAlgebraic ℚ x :=
  mem_algebraicClosure_iff

/-- The distinguished rational intermediate field in the complex numbers is an algebraic closure
of the rationals. -/
@[source_ref "Chapter5/Proposition5.2.4" (role := primary)]
theorem isAlgClosure_rat_distinguishedRatIntermediateField :
    IsAlgClosure ℚ distinguishedRatIntermediateField :=
  algebraicClosure.isAlgClosure ℚ ℂ

/-- Every element of the distinguished rational intermediate field in the complex numbers is
algebraic over the rationals. -/
@[source_ref "Chapter5/Proposition5.2.4" (role := supporting)]
theorem algebra_isAlgebraic_rat_distinguishedRatIntermediateField :
    Algebra.IsAlgebraic ℚ distinguishedRatIntermediateField :=
  algebraicClosure.isAlgebraic ℚ ℂ

/-- The complex subtype underlying the distinguished rational intermediate field is algebraically
closed. -/
@[source_ref "Chapter5/Proposition5.2.4" (role := supporting)]
theorem isAlgClosed_distinguishedRatIntermediateField :
    IsAlgClosed distinguishedRatIntermediateField := by
  letI : IsAlgClosure ℚ distinguishedRatIntermediateField :=
    algebraicClosure.isAlgClosure ℚ ℂ
  exact IsAlgClosure.isAlgClosed (R := ℚ)

/-- Integral complex numbers over the integers are closed under addition and multiplication. -/
@[source_ref "Chapter5/Proposition5.2.4" (role := supporting)]
theorem isIntegral_int_complex_add_mul :
    ∀ x y : ℂ, IsIntegral ℤ x → IsIntegral ℤ y →
      IsIntegral ℤ (x + y) ∧ IsIntegral ℤ (x * y) := by
  intro x y hx hy
  rw [← mem_distinguishedIntSubalgebra_iff] at hx hy
  exact
    ⟨mem_distinguishedIntSubalgebra_iff.mp (add_mem hx hy),
      mem_distinguishedIntSubalgebra_iff.mp (mul_mem hx hy)⟩

/-- Rational algebraicity of complex numbers is preserved by addition and multiplication, and by
inversion of a nonzero number. -/
@[source_ref "Chapter5/Proposition5.2.4" (role := supporting)]
theorem isAlgebraic_rat_complex_add_mul_inv :
    ∀ x y : ℂ, IsAlgebraic ℚ x → IsAlgebraic ℚ y →
      IsAlgebraic ℚ (x + y) ∧ IsAlgebraic ℚ (x * y) ∧
        (x ≠ 0 → IsAlgebraic ℚ x⁻¹) := by
  intro x y hx hy
  rw [← mem_distinguishedRatIntermediateField_iff] at hx hy
  exact
    ⟨mem_distinguishedRatIntermediateField_iff.mp (add_mem hx hy),
      mem_distinguishedRatIntermediateField_iff.mp (mul_mem hx hy),
      fun _ =>
        mem_distinguishedRatIntermediateField_iff.mp
          (distinguishedRatIntermediateField.inv_mem hx)⟩

end RepresentationTheory.NumberTheory.AlgebraicNumber.Complex
