import EtingofRepresentationTheory.Chapter9.Corollary9_7_3
import EtingofRepresentationTheory.Chapter9.Theorem9_6_4
import EtingofRepresentationTheory.Chapter9.Introduction_9_6
import EtingofRepresentationTheory.Infrastructure.BasicAlgebraExistence

/-!
# Corollary 9.7.3(i), categorical input form

The book's Corollary 9.7.3(i) is stated for an **abstract** `k`-linear finite abelian
category `𝒞`: any such `𝒞` is equivalent to the finite-dimensional modules over a unique
basic algebra `B(𝒞)`. The main development in `Corollary9_7_3.lean` formalizes the
**algebra version** (input = a finite-dimensional algebra `A`). This file records the
**categorical input form**: the input is an abstract `IsFiniteAbelianCategory` together
with a progenerator, and the output packages both the Morita equivalence with a
concrete finite-dimensional algebra and the existence of a basic algebra Morita
equivalent to it.

## What is proved here

`Etingof.Corollary_9_7_3_i_categorical`: for a `k`-linear finite abelian category `𝒞`
over an algebraically closed field `k` with a progenerator `P`, there is a basic
`k`-algebra `B` such that

* `𝒞 ≌ FGModuleCat (End P)ᵐᵒᵖ` (Theorem 9.6.4), and
* `(End P)ᵐᵒᵖ` is Morita equivalent to `B` (Corollary 9.7.3(i), algebra version).

Here `(End P)ᵐᵒᵖ` is the finite-dimensional algebra `A` whose finite-dimensional
modules realize `𝒞`. Because `End P = Hom(P, P)` is finite dimensional over `k` in a
`k`-linear finite abelian category (Etingof §9.6, "check it!"), so is `(End P)ᵐᵒᵖ`.

## The progenerator hypothesis (gap 1 of issue #5738)

The book asserts that *every* finite abelian category has a projective generator. The
project does not (yet) prove existence of a progenerator in an abstract finite abelian
category; matching how Theorem 9.6.4 is stated, the progenerator `P` is carried as an
explicit hypothesis rather than produced.

## Remaining gap: `FGModuleCat` vs. `ModuleCat` (gap 2 of issue #5738)

The book's single conclusion `𝒞 ≌ B-fmod` would combine the two conjuncts above into
one equivalence `𝒞 ≌ FGModuleCat B`. Doing so requires restricting the Morita
equivalence `ModuleCat (End P)ᵐᵒᵖ ≌ ModuleCat B` (which `Etingof.MoritaEquivalent`
records at the level of the *full* module categories) to the finitely generated
subcategories, i.e. proving that a Morita equivalence preserves and reflects finite
generation of modules. Over the finite-dimensional algebras at hand this is the
statement that the equivalence preserves finite `k`-dimension, but the general
categorical fact (a Morita equivalence sends f.g. modules to f.g. modules) is not
available in Mathlib and requires the "finite epi from a generator onto a finitely
generated object" step. That FG-restriction is tracked as a separate formalization
item; once it lands, the two conjuncts here collapse to `𝒞 ≌ FGModuleCat B`.
-/

open CategoryTheory

universe v u

/-- **Corollary 9.7.3(i), categorical input form** (partial: see the module docstring for
the residual `FGModuleCat`-vs-`ModuleCat` gap). Let `𝒞` be a `k`-linear finite abelian
category over an algebraically closed field `k`, and let `P` be a progenerator of `𝒞`.
Then there is a basic `k`-algebra `B` such that `𝒞` is equivalent to the finite-dimensional
`(End P)ᵐᵒᵖ`-modules, and `(End P)ᵐᵒᵖ` — a finite-dimensional `k`-algebra — is Morita
equivalent to `B`.

The finite-dimensional algebra `A = (End P)ᵐᵒᵖ` whose finite-dimensional modules realize
`𝒞` comes from Theorem 9.6.4 (`Etingof.Theorem_9_6_4_corollary`); the basic algebra `B`
Morita equivalent to it comes from the algebra version of Corollary 9.7.3(i)
(`Etingof.exists_basic_morita_equivalent`).
(Etingof Corollary 9.7.3(i), categorical form) -/
theorem Etingof.Corollary_9_7_3_i_categorical
    {k : Type v} [Field k] [IsAlgClosed k]
    (C : Type u) [Category.{v} C]
    [Etingof.IsFiniteAbelianCategory C] [Linear k C]
    [Etingof.IsFiniteAbelianCategoryOverField k C]
    (P : C) [hp : Etingof.IsProgenerator P] :
    ∃ (B : Type v) (_ : Ring B) (_ : Algebra k B) (_ : Module.Finite k B),
      Etingof.IsBasicAlgebra k B ∧
        Nonempty (C ≌ FGModuleCat.{v} (End P)ᵐᵒᵖ) ∧
          Etingof.MoritaEquivalent (End P)ᵐᵒᵖ B := by
  -- `End P = Hom(P, P)` is finite dimensional over `k`, hence so is `(End P)ᵐᵒᵖ`.
  haveI : FiniteDimensional k (End P) :=
    @Etingof.IsFiniteAbelianCategoryOverField.finiteDimensional_hom k _ C _ _ _ _ P P
  haveI : Module.Finite k (End P)ᵐᵒᵖ := inferInstance
  -- Theorem 9.6.4: `𝒞 ≌ FGModuleCat (End P)ᵐᵒᵖ`.
  have hcat : Nonempty (C ≌ FGModuleCat.{v} (End P)ᵐᵒᵖ) :=
    Etingof.Theorem_9_6_4_corollary (k := k) C P
  -- Algebra version of Corollary 9.7.3(i) applied to the finite-dimensional algebra
  -- `A = (End P)ᵐᵒᵖ`: a basic algebra `B` Morita equivalent to it.
  obtain ⟨B, instR, instA, instF, hbasic, hmor⟩ :=
    Etingof.exists_basic_morita_equivalent k (End P)ᵐᵒᵖ
  exact ⟨B, instR, instA, instF, hbasic, hcat, hmor⟩
