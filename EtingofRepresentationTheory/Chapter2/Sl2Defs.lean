import Mathlib.Algebra.Lie.Classical
import Mathlib.Data.Complex.Basic

/-!
# Shared definitions for sl(2, ℂ) representation theory

This file provides the basic abbreviation for sl(2, ℂ) used across Chapter 2.
-/

open scoped Matrix

namespace Etingof

/-- The Lie algebra sl(2, ℂ), the traceless 2×2 complex matrices. -/
abbrev sl2 : LieSubalgebra ℂ (Matrix (Fin 2) (Fin 2) ℂ) := LieAlgebra.SpecialLinear.sl (Fin 2) ℂ

end Etingof
