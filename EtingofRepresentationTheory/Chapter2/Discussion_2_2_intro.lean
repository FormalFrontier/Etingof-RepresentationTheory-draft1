import Mathlib.Analysis.Complex.Polynomial.Basic
import Mathlib.Algebra.Field.ZMod
import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure

/-!
# Section 2.2: Algebras

Throughout the book, `k` denotes a field and is assumed algebraically closed unless stated
otherwise. Algebraic closedness means that every nonconstant polynomial over `k` has a root.
The main example is `ℂ`; in positive characteristic, an example is the algebraic closure of the
finite field `𝔽ₚ`.

## Mathlib correspondence

Mathlib's class `IsAlgClosed k` is phrased by saying that every polynomial over `k` splits. The
theorem `isAlgClosed_iff_nonconstant_polynomial_has_root` below records the equivalence with the
book's root-based wording. The types `ℂ` and `AlgebraicClosure (ZMod p)` provide the two examples.
-/

open Polynomial

/-- The book's root-based description of an algebraically closed field is equivalent to Mathlib's
splitting-based `IsAlgClosed` class. -/
theorem Etingof.isAlgClosed_iff_nonconstant_polynomial_has_root (k : Type*) [Field k] :
    IsAlgClosed k ↔ ∀ p : k[X], p.degree ≠ 0 → ∃ x : k, p.IsRoot x := by
  constructor
  · intro _ p hp
    exact IsAlgClosed.exists_root p hp
  · intro h
    exact IsAlgClosed.of_exists_root k fun p _ hp ↦
      h p (degree_pos_of_irreducible hp).ne'

/-- The complex numbers are the book's main example of an algebraically closed field. -/
theorem Etingof.complex_isAlgClosed : IsAlgClosed ℂ := inferInstance

/-- For prime `p`, `ZMod p` carries the field structure modeling `𝔽ₚ`. -/
noncomputable abbrev Etingof.zmodField (p : ℕ) [Fact p.Prime] : Field (ZMod p) := inferInstance

/-- The finite field `𝔽ₚ` has exactly `p` elements. -/
theorem Etingof.card_zmod (p : ℕ) [Fact p.Prime] : Fintype.card (ZMod p) = p := ZMod.card p

/-- The algebraic closure of `𝔽ₚ` is algebraically closed. -/
theorem Etingof.algebraicClosure_zmod_isAlgClosed (p : ℕ) [Fact p.Prime] :
    IsAlgClosed (AlgebraicClosure (ZMod p)) := inferInstance

/-- The algebraic closure of `𝔽ₚ` still has characteristic `p`. -/
theorem Etingof.algebraicClosure_zmod_charP (p : ℕ) [Fact p.Prime] :
    CharP (AlgebraicClosure (ZMod p)) p := inferInstance
