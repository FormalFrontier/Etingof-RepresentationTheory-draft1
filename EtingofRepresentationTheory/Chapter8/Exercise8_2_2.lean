import Mathlib.Algebra.Category.ModuleCat.Projective
import Mathlib.Algebra.Category.ModuleCat.Abelian
import Mathlib.CategoryTheory.Abelian.Projective.Resolution
import EtingofRepresentationTheory.Chapter8.Definition8_2_1

/-!
# Exercise 8.2.2: Every module has a projective resolution

Show that any module has a projective resolution (for example, one consisting of free modules).

## Formalization notes

We phrase this for the category `ModuleCat A` of left `A`-modules over a ring `A`. A projective
resolution is `CategoryTheory.ProjectiveResolution` (Definition 8.2.1 in this development,
`Etingof.ProjectiveResolution`). The statement asserts that every module admits one, i.e. the
type of projective resolutions is nonempty.

The parenthetical "consisting of free modules" is the standard construction (repeatedly cover a
module by a free module on its underlying set); Mathlib's `EnoughProjectives (ModuleCat A)`
instance provides projective covers by free modules, from which the resolution is built.

This is a statement-level formalization (spec-first): the proof is deferred (`sorry`).
-/

namespace Etingof

open CategoryTheory

universe u

/-- **Exercise 8.2.2.** Every left `A`-module has a projective resolution. -/
theorem Exercise_8_2_2 (A : Type u) [Ring A] (M : ModuleCat.{u} A) :
    Nonempty (Etingof.ProjectiveResolution M) := by
  sorry

end Etingof
