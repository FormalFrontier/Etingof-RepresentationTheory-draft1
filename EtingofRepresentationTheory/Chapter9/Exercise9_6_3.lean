import Mathlib.CategoryTheory.Simple
import EtingofRepresentationTheory.Chapter9.Definition9_6_1
import EtingofRepresentationTheory.Chapter9.Definition9_6_2

/-!
# Exercise 9.6.3: Characterization of projective generators

Etingof Exercise 9.6.3. In a finite abelian category, a projective object `P` is a
**projective generator** if and only if for every simple object `L`, one has
`Hom(P, L) ≠ 0`. Deduce that any finite abelian category has a projective generator.

## Statement-pass note

We use `Etingof.IsProgenerator` (Definition 9.6.2) for "projective generator" and
`CategoryTheory.Simple` for simple objects. "`Hom(P, L) ≠ 0`" is rendered as the existence of
a nonzero morphism `∃ f : P ⟶ L, f ≠ 0`. The projectivity hypothesis is carried as an
instance `[Projective P]`, matching the book's "a projective object `P` is a projective
generator iff …". The deduction is the existence statement `∃ P, Nonempty (IsProgenerator P)`;
a witness is the direct sum of the projective covers of the (finitely many) simple objects.
Proofs are deferred (`sorry`).
-/

universe v u

open CategoryTheory

namespace Etingof.Exercise963

/-- **Exercise 9.6.3.** In a finite abelian category, a projective object `P` is a projective
generator (`Etingof.IsProgenerator`) if and only if `Hom(P, L) ≠ 0` for every simple object
`L`. -/
theorem isProgenerator_iff_hom_simple_ne_zero
    {C : Type u} [Category.{v} C] [Etingof.IsFiniteAbelianCategory C]
    (P : C) [Projective P] :
    Nonempty (Etingof.IsProgenerator P) ↔
      ∀ (L : C), Simple L → ∃ f : P ⟶ L, f ≠ 0 := by
  sorry

/-- **Exercise 9.6.3, deduction.** Any finite abelian category has a projective generator. -/
theorem exists_progenerator (C : Type u) [Category.{v} C]
    [Etingof.IsFiniteAbelianCategory C] :
    ∃ P : C, Nonempty (Etingof.IsProgenerator P) := by
  sorry

end Etingof.Exercise963
