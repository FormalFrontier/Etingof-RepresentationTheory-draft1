import Mathlib
import EtingofRepresentationTheory.Chapter5.Definition5_12_1
import EtingofRepresentationTheory.Chapter5.Theorem5_12_2_Irreducible

/-!
# Problem 5.24.1(a): the two orderings of the Young symmetrizer give isomorphic modules

**Problem 5.24.1.** (a) Show that the `S_n`-representation `V'_λ := ℂ[S_n] b_λ a_λ` is
isomorphic to `V_λ`.

*Hint.* Define `S_n`-homomorphisms `f : V_λ → V'_λ` and `g : V'_λ → V_λ` by `f(x) = x a_λ`
and `g(y) = y b_λ`, and show that they are inverse to each other up to a nonzero scalar.

## Formalization

The book's `V_λ = ℂ[S_n] a_λ b_λ` (Young symmetrizer `c_λ = a_λ b_λ`), while the project's
`SpechtModule n la = ℂ[S_n] · (b_λ a_λ)` uses the opposite ordering `c_λ = b_λ a_λ` (see
`Etingof.YoungSymmetrizer`). Part (a) is precisely the statement that these two left ideals —
the two orderings of the row (`a_λ`) and column (`b_λ`) symmetrizers — are isomorphic as
`S_n`-representations.

We write `rowColIdeal la := ℂ[S_n] · (a_λ b_λ)` (the book's `V_λ`) and compare it with
`SpechtModule n la = ℂ[S_n] · (b_λ a_λ)` (the book's `V'_λ`). `S_n` acts on each left ideal by
left multiplication, which is exactly the `ℂ[S_n]`-module scalar action `of(g) • ·`. The claim
is a `ℂ`-linear isomorphism intertwining these actions.

Statement pass: the proof is left as `sorry`.
-/

namespace Etingof

/-- The left ideal `ℂ[S_n] · (a_λ b_λ)`, i.e. the book's `V_λ` (row symmetrizer `a_λ` times
column antisymmetrizer `b_λ`). -/
noncomputable def rowColIdeal (n : ℕ) (la : Nat.Partition n) :
    Submodule (SymGroupAlgebra n) (SymGroupAlgebra n) :=
  Submodule.span (SymGroupAlgebra n)
    {RowSymmetrizer n la * ColumnAntisymmetrizer n la}

/-- Problem 5.24.1(a). The two orderings of the Young symmetrizer generate isomorphic
`S_n`-representations: `ℂ[S_n]·(a_λ b_λ)` (the book's `V_λ`) is isomorphic to
`ℂ[S_n]·(b_λ a_λ) = V'_λ` (the project's `SpechtModule`), via a `ℂ`-linear equivalence
intertwining the left-multiplication (`of(g) • ·`) `S_n`-actions. -/
theorem rowColIdeal_iso_spechtModule (n : ℕ) (la : Nat.Partition n) :
    ∃ e : ↥(rowColIdeal n la) ≃ₗ[ℂ] ↥(SpechtModule n la),
      ∀ (g : Equiv.Perm (Fin n)) (x : ↥(rowColIdeal n la)),
        e ((MonoidAlgebra.of ℂ (Equiv.Perm (Fin n)) g) • x)
          = (MonoidAlgebra.of ℂ (Equiv.Perm (Fin n)) g) • e x := by
  sorry

end Etingof
