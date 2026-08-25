import Mathlib.CategoryTheory.Preadditive.Projective.Basic
import Mathlib.CategoryTheory.Generator.Basic
import Mathlib.CategoryTheory.Limits.Shapes.Biproducts

universe u v w

/-!
# Definition 9.6.2: Projective generator (progenerator)

An object `P` in an abelian category is a **projective generator** (or **progenerator**)
if `P` is projective and every object `X` in the category is a quotient of a multiple of `P`
(that is, of a direct sum / coproduct of copies of `P`).

Etingof's motivating example is the regular module `A` (the algebra viewed as a module over
itself) in the category of all modules over a ring `A`: every `A`-module is a quotient of a
free module `A^{(I)}`, and this free module is a coproduct of copies of the regular module.
Producing *arbitrary* modules this way genuinely needs *infinite* coproducts, so the faithful
formalization must allow an unrestricted index set.

## Two notions and how they relate

* `Etingof.IsProjectiveGenerator P` is the **general** notion of Definition 9.6.2: `P` is
  projective and `P` is a separator. In a category with the relevant coproducts,
  being a separator is exactly the condition that every object is the epimorphic image of a
  coproduct of copies of `P` (see `Etingof.IsProjectiveGenerator.epi_coproduct`), i.e. a
  "quotient of a multiple of `P`". This is the notion that covers the source example over an
  arbitrary ring, where infinite coproducts are needed.

* `Etingof.IsProgenerator P` is the **finite** variant used by the finite-abelian-category
  development (Section 9.6 onwards): every object admits an epimorphism from a *finite*
  biproduct `P^n`. This is the correct finitely-generated variant for categories in which every
  object has finite length, but it does **not** formalize the general definition: an arbitrary
  module over an arbitrary ring need not be finitely generated.

The finite variant implies the general one; see `Etingof.IsProgenerator.isProjectiveGenerator`
in `Chapter9.Theorem9_6_4` (it reuses `Etingof.IsProgenerator.isSeparator`).

## Mathlib correspondence

Mathlib has `CategoryTheory.Projective` for projective objects and `CategoryTheory.IsSeparator`
for the separator property, with `CategoryTheory.isSeparator_iff_epi` recording the
"quotient of a coproduct of copies" characterization.
-/

open CategoryTheory CategoryTheory.Limits

/-- A **projective generator** (progenerator) in the sense of Etingof Definition 9.6.2, in full
generality: an object `P` that is projective and is a separator. In a category with the
coproducts `∐ (P ⟶ X)` this says precisely that every object `X` is a quotient (epimorphic image)
of a coproduct of copies of `P`; see `Etingof.IsProjectiveGenerator.epi_coproduct`. Unlike
`Etingof.IsProgenerator`, this allows the arbitrary (possibly infinite) coproducts needed to
realize every object over an arbitrary ring. -/
def Etingof.IsProjectiveGenerator {C : Type u} [Category.{v} C] (P : C) : Prop :=
  Projective P ∧ IsSeparator P

namespace Etingof.IsProjectiveGenerator

variable {C : Type u} [Category.{v} C] {P : C}

/-- A projective generator is in particular projective. -/
theorem projective (h : Etingof.IsProjectiveGenerator P) : Projective P := h.1

/-- A projective generator is in particular a separator. -/
theorem isSeparator (h : Etingof.IsProjectiveGenerator P) : IsSeparator P := h.2

/-- **The book's phrasing.** In a category with the coproducts `∐ (P ⟶ X)`, an object `P` is a
projective generator exactly when it is projective and every object `X` is a quotient
(epimorphic image) of a coproduct of copies of `P`, via the canonical map `Sigma.desc`. -/
theorem epi_coproduct [∀ X : C, HasCoproduct fun _ : P ⟶ X => P] :
    Etingof.IsProjectiveGenerator P ↔
      Projective P ∧ ∀ X : C, Epi (Sigma.desc fun f : P ⟶ X => f) := by
  rw [Etingof.IsProjectiveGenerator, isSeparator_iff_epi]

end Etingof.IsProjectiveGenerator

/-- A projective generator (progenerator) in the **finite** sense of Etingof Definition 9.6.2.
An object `P` is a finite progenerator if it is projective and every object `X` admits an
epimorphism from a *finite* biproduct of copies of `P`.

This is the finitely-generated variant appropriate to the finite-abelian-category development
(every object having finite length), **not** the general Definition 9.6.2: over an arbitrary
ring the source example needs the unbounded coproducts allowed by
`Etingof.IsProjectiveGenerator`. See that definition for the faithful general notion. -/
class Etingof.IsProgenerator {C : Type u} [Category.{v} C] [HasZeroMorphisms C] (P : C)
    extends Projective P where
  /-- Every object admits an epimorphism from a finite biproduct of copies of P. -/
  epiFromBiproduct : ∀ (X : C), ∃ (n : ℕ) (_ : HasBiproduct (fun _ : Fin n => P))
    (f : biproduct (fun _ : Fin n => P) ⟶ X), Epi f
