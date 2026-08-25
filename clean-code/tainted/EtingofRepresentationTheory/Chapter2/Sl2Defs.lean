import Mathlib.Algebra.Lie.Classical
import Mathlib.Data.Complex.Basic

/-!
# Shared definitions for sl(2, ℂ) representation theory

This file provides the basic abbreviation for sl(2, ℂ) used across Chapter 2.
-/

open scoped Matrix

-- Mathlib's `LieRing.ofAssociativeRing` (the Lie ring structure on an
-- associative ring) is only a *local* instance from v4.31 onward, to avoid a
-- bracket diamond when the ring acts on itself. Re-enable it locally so the
-- `LieSubalgebra ℂ (Matrix (Fin 2) (Fin 2) ℂ)` type below elaborates. On
-- v4.28.1 it is already a global instance and this attribute is harmless.
attribute [local instance 100] LieRing.ofAssociativeRing

namespace Etingof

/-- The Lie algebra sl(2, ℂ), the traceless 2×2 complex matrices. -/
abbrev sl2 : LieSubalgebra ℂ (Matrix (Fin 2) (Fin 2) ℂ) := LieAlgebra.SpecialLinear.sl (Fin 2) ℂ

end Etingof
