import Mathlib
import EtingofRepresentationTheory.Chapter5.Definition5_1_1

/-!
# Exercise 5.1.7: an odd-order group has an irreducible not defined over ℝ

**Exercise 5.1.7.** Show that any nontrivial finite group of odd order has an irreducible
representation which is not defined over `ℝ` (i.e., not realizable by real matrices).

## Formalization

A representation "defined over `ℝ`" (realizable by real matrices) admits a `G`-invariant
positive-definite real inner product, hence a nondegenerate symmetric `G`-invariant bilinear
form, so it is of **real type** (`Etingof.IsRealType`, Definition 5.1.1). Therefore "not
defined over `ℝ`" is faithfully captured by `¬ Etingof.IsRealType ρ`.

The statement below asserts the existence of a nontrivial irreducible complex representation
`ρ` (`IsSimpleModule (MonoidAlgebra ℂ G) ρ.asModule`, with `∃ g, ρ g ≠ 1`) that is not of
real type. Exercise 5.3.3 strengthens this to: every nontrivial irreducible is of complex
type.

Statement pass: the proof is left as `sorry`.
-/

namespace Etingof

section Exercise517

variable (G : Type*) [Group G] [Fintype G] [Nontrivial G]

/-- Exercise 5.1.7. A nontrivial finite group of odd order admits a nontrivial irreducible
complex representation that is not of real type — i.e., not realizable by real matrices. -/
theorem exists_irreducible_not_realType_of_odd_order
    (hodd : Odd (Fintype.card G)) :
    ∃ (V : Type) (_ : AddCommGroup V) (_ : Module ℂ V) (_ : Module.Finite ℂ V)
      (ρ : Representation ℂ G V),
      IsSimpleModule (MonoidAlgebra ℂ G) ρ.asModule ∧
      (∃ g, ρ g ≠ 1) ∧
      ¬ Etingof.IsRealType ρ := by
  sorry

end Exercise517

end Etingof
