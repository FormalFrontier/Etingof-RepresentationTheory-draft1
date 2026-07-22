import Mathlib
import EtingofRepresentationTheory.Chapter2.Definition2_3_8

/-!
# Problem 2.5.1: A quotient of a polynomial ring is indecomposable

Let `A = k[x₁, …, xₙ]` and let `I ≠ A` be any ideal in `A` containing all homogeneous polynomials
of degree `≥ N`. The problem asks to show that `A/I` is an indecomposable representation of `A`.

## Formalization

`A = MvPolynomial (Fin n) k`, `I : Ideal A`, and `A/I` carries its natural `A`-module structure.
"Indecomposable representation" is `Etingof.IsIndecomposable` (Definition 2.3.8). The hypothesis
that `I` contains every homogeneous polynomial of degree `≥ N` is `MvPolynomial.IsHomogeneous`.

This is the **statement pass**: the statement is recorded with a `sorry` proof.
-/

namespace Etingof.Problem2_5_1

open MvPolynomial

variable {k : Type*} [Field k] {n : ℕ}

/-- **Problem 2.5.1.** If `I ≠ A = k[x₁, …, xₙ]` is an ideal containing every homogeneous
polynomial of degree `≥ N`, then `A/I` is an indecomposable representation of `A`. -/
theorem quotient_isIndecomposable (N : ℕ) (I : Ideal (MvPolynomial (Fin n) k))
    (hIne : I ≠ ⊤)
    (hI : ∀ (d : ℕ) (p : MvPolynomial (Fin n) k), N ≤ d → p.IsHomogeneous d → p ∈ I) :
    Etingof.IsIndecomposable (MvPolynomial (Fin n) k) (MvPolynomial (Fin n) k ⧸ I) := by
  sorry

end Etingof.Problem2_5_1
