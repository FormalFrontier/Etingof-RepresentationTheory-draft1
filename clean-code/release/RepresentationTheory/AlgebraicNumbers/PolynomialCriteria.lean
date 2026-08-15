/-
Copyright (c) 2026 mathlib-initiative. All rights reserved.
Released under Apache 2.0 license as described in the file LICENCE.
Authors: Kim Morrison
-/

import Mathlib
import RepresentationTheory.Alignment.Attribute

namespace RepresentationTheory.AlgebraicNumbers.PolynomialCriteria

/-- A complex number is algebraic over the rationals exactly when it is a zero of a nonzero rational polynomial. -/
@[source_ref "Chapter5/Introduction_5.2" (role := supporting),
  source_ref "Chapter5/Definition5.2.1" (role := supporting)]
theorem isAlgebraic_iff_exists_ne_zero_aeval_eq_zero (z : ℂ) :
    IsAlgebraic ℚ z ↔ ∃ p : Polynomial ℚ, p ≠ 0 ∧ (Polynomial.aeval (R := ℚ) z) p = 0 :=
  Iff.rfl

/-- A complex number is integral over the integers exactly when it is a zero of a monic integer polynomial. -/
@[source_ref "Chapter5/Introduction_5.2" (role := supporting),
  source_ref "Chapter5/Definition5.2.1" (role := primary)]
theorem isIntegral_iff_exists_monic_aeval_eq_zero (z : ℂ) :
    IsIntegral ℤ z ↔ ∃ p : Polynomial ℤ, p.Monic ∧ (Polynomial.aeval (R := ℤ) z) p = 0 := by
  simp [IsIntegral, RingHom.IsIntegralElem, Polynomial.aeval_def]

end RepresentationTheory.AlgebraicNumbers.PolynomialCriteria
