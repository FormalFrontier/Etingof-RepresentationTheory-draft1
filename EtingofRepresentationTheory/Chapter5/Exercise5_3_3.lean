import Mathlib
import EtingofRepresentationTheory.Chapter5.Definition5_1_1

/-!
# Exercise 5.3.3: nontrivial irreducibles of an odd-order group are of complex type

**Exercise 5.3.3.** Strengthen the result of Exercise 5.1.7: show that all nontrivial
irreducible representations of a group of odd order are of complex type. (Use that any
representation of quaternionic type is even-dimensional.)

## Formalization

We work with the project's type classification (`Etingof.IsComplexType`, Definition 5.1.1):
a complex representation `ρ : Representation ℂ G V` is of *complex type* if it is **not**
isomorphic (equivariantly) to its dual `ρ.dual`. Irreducibility is
`IsSimpleModule (MonoidAlgebra ℂ G) ρ.asModule`, and "nontrivial" is spelled `∃ g, ρ g ≠ 1`
(the action is not the identity on all of `G`).

The mathematical content: for `|G|` odd, a self-dual irreducible carries a nondegenerate
invariant bilinear form, hence is of real or quaternionic type; the Frobenius-Schur indicator
distinguishes these and, by an averaging/counting argument that uses that quaternionic type
forces even dimension while `|G|` odd forces odd-dimensional constituents, the only self-dual
irreducible is the trivial one. So every nontrivial irreducible is of complex type.

Statement pass: the proof is left as `sorry`.
-/

namespace Etingof

section Exercise533

variable {G : Type*} [Group G] [Fintype G]
  {V : Type*} [AddCommGroup V] [Module ℂ V] [Module.Finite ℂ V]

/-- Exercise 5.3.3. Every nontrivial irreducible representation of a finite group of odd
order is of complex type (`V ≇ V*`). -/
theorem isComplexType_of_odd_order_of_nontrivial_irreducible
    (hodd : Odd (Fintype.card G))
    (ρ : Representation ℂ G V)
    (hirr : IsSimpleModule (MonoidAlgebra ℂ G) ρ.asModule)
    (hnontriv : ∃ g, ρ g ≠ 1) :
    Etingof.IsComplexType ρ := by
  sorry

end Exercise533

end Etingof
